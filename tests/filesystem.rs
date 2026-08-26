//! A whole history recorded into a filesystem that is not one.
//!
//! Decision 0025 claims the library reaches the folder only through
//! [`Filesystem`], and that the trait is small enough for somebody who is not
//! `std::fs` to implement. Neither half of that is checkable by reading the
//! source: the `bare` CI job proves the library *compiles* without `std::fs`,
//! and this proves it *works* without one.
//!
//! [`Memory`] below is the whole implementation — nine methods over two
//! `BTreeMap`s, with no path resolution, no links, and no cleverness — and
//! everything after it is a store driven through it end to end: init, record,
//! reopen, bookmark, check, prune. If the trait were the wrong shape, this
//! file is where that would show, because a test that has to reach around the
//! abstraction has found a hole in it.

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};
use std::io;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::{Arc, Mutex};

use historica::core::{FileId, RevisionId};
use historica::format::{LinkTarget, Mode, RevisionDocument};
use historica::fs::{Entry, Filesystem, Kind};
use historica::record::{Clock as _, Platform, Recording, Restriction, record};
use historica::store::{Name, Placement, Severity, Store};
use historica::working::{Rule, Working};

// ---------------------------------------------------------------------------
// A filesystem made of two maps
// ---------------------------------------------------------------------------

/// Files and directories in memory, and nothing else.
///
/// Paths are the keys, exactly as they arrive. Nothing is canonicalised,
/// because nothing in the library asks for that — which is itself part of what
/// this file is checking.
#[derive(Debug, Default)]
struct Memory {
    held: Mutex<Held>,
}

#[derive(Debug, Default)]
struct Held {
    files: BTreeMap<PathBuf, Vec<u8>>,
    directories: BTreeSet<PathBuf>,
}

impl Memory {
    fn new() -> Arc<Self> {
        Arc::new(Self::default())
    }

    /// How many files are held, for the assertions that count them.
    fn count(&self) -> usize {
        self.held.lock().expect("the lock").files.len()
    }
}

fn missing(path: &Path) -> io::Error {
    io::Error::new(io::ErrorKind::NotFound, format!("{}", path.display()))
}

impl Filesystem for Memory {
    fn read(&self, path: &Path) -> io::Result<Vec<u8>> {
        let held = self.held.lock().expect("the lock");
        held.files.get(path).cloned().ok_or_else(|| missing(path))
    }

    fn write(&self, path: &Path, bytes: &[u8]) -> io::Result<()> {
        let mut held = self.held.lock().expect("the lock");
        held.files.insert(path.to_path_buf(), bytes.to_vec());
        Ok(())
    }

    fn create_new(&self, path: &Path, bytes: &[u8]) -> io::Result<()> {
        let mut held = self.held.lock().expect("the lock");
        if held.files.contains_key(path) {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                format!("{}", path.display()),
            ));
        }
        held.files.insert(path.to_path_buf(), bytes.to_vec());
        Ok(())
    }

    fn create_directory(&self, path: &Path) -> io::Result<()> {
        let mut held = self.held.lock().expect("the lock");
        for ancestor in path.ancestors() {
            held.directories.insert(ancestor.to_path_buf());
        }
        Ok(())
    }

    fn entries(&self, path: &Path) -> io::Result<Vec<Entry>> {
        let held = self.held.lock().expect("the lock");
        if !held.directories.contains(path) {
            return Err(missing(path));
        }
        // Whatever sits directly under `path`, however it got there — a file
        // written into a directory nobody declared is still in that directory.
        let mut found = BTreeMap::new();
        let children = held
            .files
            .keys()
            .map(|file| (file, Kind::File))
            .chain(held.directories.iter().map(|dir| (dir, Kind::Directory)));
        for (candidate, kind) in children {
            if candidate == path {
                continue;
            }
            let Ok(relative) = candidate.strip_prefix(path) else {
                continue;
            };
            let mut components = relative.components();
            let Some(first) = components.next() else {
                continue;
            };
            let here = path.join(first);
            // Deeper than one level: the thing directly under `path` is the
            // directory on the way to it.
            let kind = if components.next().is_some() {
                Kind::Directory
            } else {
                kind
            };
            found.insert(here, kind);
        }
        // Returned in reverse, on purpose. The trait promises no order and the
        // library says it sorts what it needs sorted; a memory filesystem that
        // happened to be sorted would let a missing sort pass unnoticed.
        Ok(found
            .into_iter()
            .rev()
            .map(|(path, kind)| Entry { path, kind })
            .collect())
    }

    fn look(&self, path: &Path) -> io::Result<Option<Kind>> {
        let held = self.held.lock().expect("the lock");
        if held.files.contains_key(path) {
            return Ok(Some(Kind::File));
        }
        if held.directories.contains(path) {
            return Ok(Some(Kind::Directory));
        }
        Ok(None)
    }

    fn rename(&self, from: &Path, to: &Path) -> io::Result<()> {
        let mut held = self.held.lock().expect("the lock");
        let bytes = held.files.remove(from).ok_or_else(|| missing(from))?;
        held.files.insert(to.to_path_buf(), bytes);
        Ok(())
    }

    fn remove_file(&self, path: &Path) -> io::Result<()> {
        let mut held = self.held.lock().expect("the lock");
        held.files
            .remove(path)
            .map(|_| ())
            .ok_or_else(|| missing(path))
    }

    fn remove_directory(&self, path: &Path) -> io::Result<()> {
        let mut held = self.held.lock().expect("the lock");
        if !held.directories.contains(path) {
            return Err(missing(path));
        }
        let occupied = held
            .files
            .keys()
            .chain(held.directories.iter())
            .any(|held| held != path && held.starts_with(path));
        if occupied {
            // What `rmdir` says, and what `arrange` and `prune` read as "stop
            // tidying upwards, this one holds something".
            return Err(io::Error::new(
                io::ErrorKind::DirectoryNotEmpty,
                format!("{}", path.display()),
            ));
        }
        held.directories.remove(path);
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// A history, in it
// ---------------------------------------------------------------------------

/// A store over the map. `Arc<Memory>` is a `Filesystem` because a smart
/// pointer to one is — which is also what makes `Store<Arc<dyn Filesystem>>`
/// available to anyone who wants to choose a filesystem at run time.
type MemoryStore = Store<Arc<Memory>>;

const ROOT: &str = "/nowhere";
const AUTHOR: &str = "Adam Harris <adam@example.com>";

/// Put a file in the working copy, which here is just the map.
fn put(memory: &Memory, path: &str, contents: &str) {
    let path = Path::new(ROOT).join(path);
    if let Some(parent) = path.parent() {
        memory.create_directory(parent).expect("a directory");
    }
    memory.write(&path, contents.as_bytes()).expect("a file");
}

fn record_folder(
    memory: &Arc<Memory>,
    store: &mut MemoryStore,
    parents: Vec<RevisionId>,
    message: &str,
) -> RevisionId {
    let mut platform = Platform;
    let working = Working::read_on(memory.clone(), Path::new(ROOT), store.skipped())
        .expect("the folder in memory");
    record(
        store,
        &working,
        &Recording {
            parents,
            author: AUTHOR.to_owned(),
            when: platform.now().expect("a clock"),
            message: message.to_owned(),
            moves: Vec::new(),
            at: Vec::new(),
            accepted: BTreeSet::new(),
            only: Restriction::Everything,
        },
        &mut platform,
    )
    .expect("recording")
    .revision
}

fn history() -> (Arc<Memory>, MemoryStore, RevisionId, RevisionId) {
    let memory = Memory::new();
    memory
        .create_directory(Path::new(ROOT))
        .expect("the working copy");
    let mut store =
        Store::init_on(memory.clone(), Path::new(ROOT).join("history")).expect("a new store");

    put(&memory, "notes.md", "First thought.\n");
    put(&memory, "docs/plan.md", "One: begin.\n");
    let first = record_folder(&memory, &mut store, Vec::new(), "Start a journal");

    put(&memory, "notes.md", "First thought.\nA second one.\n");
    let second = record_folder(&memory, &mut store, vec![first], "A second thought");

    (memory, store, first, second)
}

#[test]
fn a_history_is_recorded_and_read_back_with_no_filesystem_at_all() {
    let (memory, store, first, second) = history();

    assert_eq!(store.len(), 2, "two revisions");
    assert!(store.holds(&first) && store.holds(&second));

    // Every byte of it is in the map and nowhere else — including the header
    // and the note `init` writes into `skipped/`.
    assert!(memory.count() >= 4, "held {} files", memory.count());
    assert!(
        !Path::new(ROOT).exists(),
        "`/nowhere` is not a place on this machine, and nothing created it"
    );

    // Reopening reads the documents back out of the map, by digest, with the
    // graph rebuilt from what the documents themselves say.
    let reopened = Store::open_on(memory.clone(), store.root()).expect("reopening from memory");
    assert_eq!(reopened.len(), 2);
    let history = reopened.history();
    assert_eq!(history.heads(), BTreeSet::from([second]));

    // And the content materialises, which is the whole stack — walk, payload
    // index, replay, merge — over a filesystem that is two maps.
    let tree = reopened.tree(&second).expect("a tree");
    let mut paths: Vec<&str> = tree.files().map(|(_, path)| path).collect();
    paths.sort_unstable();
    assert_eq!(paths, ["docs/plan.md", "notes.md"]);
}

#[test]
fn the_directories_a_path_needs_are_made_in_memory_too() {
    let (memory, _store, _first, _second) = history();
    let held = memory.held.lock().expect("the lock");

    // Decision 0018 files a path as a path, and `create_directory` is what the
    // writer asks for on the way. `docs/plan.md` is filed under `docs/`, in a
    // filesystem that only has directories because it was told to make them.
    let filed: Vec<&PathBuf> = held
        .files
        .keys()
        .filter(|path| path.to_string_lossy().contains("/operations/"))
        .collect();
    assert!(
        filed
            .iter()
            .any(|path| path.to_string_lossy().contains("/docs/")),
        "an operation document should be filed under `docs/`: {filed:?}"
    );
}

#[test]
fn a_bookmark_and_the_skipped_rules_survive_a_reopen() {
    let (memory, mut store, _first, second) = history();

    store
        .set_name("main", Name::Revision(second))
        .expect("a bookmark");
    let rule = Rule::parse("skip build.log").expect("a rule");
    let written = store.add_skipped(&[rule]).expect("a rule");
    assert_eq!(written, vec!["build.log.txt".to_owned()]);

    let reopened = Store::open_on(memory.clone(), store.root()).expect("reopening");
    assert_eq!(reopened.name("main"), Some(Name::Revision(second)));
    assert!(
        reopened.skipped().skips("build.log"),
        "the written rule should be read back"
    );
}

#[test]
fn check_reports_a_healthy_store_it_never_touched_a_disk_to_read() {
    let (memory, store, _first, _second) = history();

    let report = Store::check_on(memory.as_ref(), store.root());
    let errors: Vec<String> = report
        .findings()
        .iter()
        .filter(|finding| finding.severity() == Severity::Error)
        .map(|finding| finding.to_string())
        .collect();
    assert!(errors.is_empty(), "a store recorded cleanly: {errors:?}");
}

#[test]
fn pruning_removes_files_from_the_map_and_tidies_what_it_empties() {
    let (memory, mut store, first, _second) = history();

    // A revision written and then not referenced by anything: prune is
    // decision 0013's, and what it removes here is entries in a `BTreeMap`.
    let orphan = store
        .insert_operation(&historica::format::OperationDocument {
            forgets: None,
            result: None,
            // A document with an operation in it, because a document with
            // none is not one the format parses — and prune reads what the
            // directory holds rather than what this process remembers
            // inserting.
            operations: vec![historica::format::Operation::insert(
                0,
                [historica::format::Item::line("nothing names this")],
            )],
        })
        .expect("an operation document nothing names");
    assert!(store.operation(&orphan).unwrap().is_some());

    let before = memory.count();
    let pruned = store.prune().expect("pruning");
    assert!(
        pruned.operations.contains(&orphan),
        "the unreferenced document should go: {pruned:?}"
    );
    assert!(memory.count() < before, "a file left the map");

    // And the store still reads, with the history untouched.
    let reopened = Store::open_on(memory.clone(), store.root()).expect("reopening after pruning");
    assert_eq!(reopened.len(), 2);
    assert!(reopened.holds(&first));
}

#[test]
fn create_new_is_what_makes_two_writers_of_one_revision_agree() {
    let memory = Memory::new();
    let path = Path::new("/nowhere/once.txt");
    memory
        .create_directory(Path::new("/nowhere"))
        .expect("a directory");

    memory.create_new(path, b"first").expect("the first write");
    let again = memory
        .create_new(path, b"second")
        .expect_err("the second must be refused");
    assert_eq!(again.kind(), io::ErrorKind::AlreadyExists);
    assert_eq!(memory.read(path).expect("the file"), b"first");
}

#[test]
fn arranging_gives_a_folder_readable_names_without_a_folder() {
    let (memory, store, _first, _second) = history();

    // Recording already writes readable names — decision 0019 — so a store
    // this tool wrote has nothing to arrange, and that is the first claim.
    let settled = store.arrangement(Placement::Kept).expect("a plan");
    assert!(
        settled.is_empty(),
        "a store written by `record` is already arranged: {:?}",
        settled.renames
    );

    // Now the digest-named store 0003 says is equally legal. Rewrite every
    // file in `operations/` under its own digest, which is the default writer
    // and the least readable thing a correct store can be.
    let scattered: Vec<PathBuf> = {
        let held = memory.held.lock().expect("the lock");
        held.files
            .keys()
            .filter(|path| path.to_string_lossy().contains("/operations/"))
            .cloned()
            .collect()
    };
    assert!(!scattered.is_empty());
    let operations = Path::new(ROOT).join("history").join("operations");
    for path in &scattered {
        let bytes = memory.read(path).expect("a file");
        let mut digest = format!("{:x?}", bytes.len());
        digest.push_str(&path.to_string_lossy().len().to_string());
        memory.remove_file(path).expect("moving it aside");
        memory
            .write(&operations.join(&digest), &bytes)
            .expect("a digest name");
    }

    let mut store = Store::open_on(memory.clone(), store.root()).expect("reopening the flat store");
    let plan = store.arrangement(Placement::Kept).expect("a plan");
    assert_eq!(
        plan.renames.len(),
        scattered.len(),
        "every flattened file should have somewhere to go"
    );

    let done = store.arrange(Placement::Kept).expect("arranging");
    assert_eq!(done.renames, plan.renames, "the plan is what was done");

    // Decision 0018: the name of a thing is the path, as directories. The
    // entry two revisions down is filed under a folder called `docs`.
    let held = memory.held.lock().expect("the lock");
    let names: Vec<String> = held
        .files
        .keys()
        .filter(|path| path.starts_with(&operations))
        .map(|path| {
            path.strip_prefix(&operations)
                .expect("under operations")
                .to_string_lossy()
                .into_owned()
        })
        .collect();
    assert!(
        names.iter().any(|name| name.contains("docs/plan.md")),
        "the entry belongs under its own path: {names:?}"
    );
    assert!(
        names.iter().all(|name| name.contains('/')),
        "everything is filed under the revision that named it: {names:?}"
    );
    drop(held);

    // And arranging an arranged store moves nothing, in memory as on disk —
    // under either placement, since `operations/` is filed the same way by
    // both and the revisions here never left their month.
    assert!(store.arrange(Placement::Kept).expect("again").is_empty());
    assert!(
        store
            .arrange(Placement::Refiled)
            .expect("and refiling")
            .is_empty()
    );
}

// ---------------------------------------------------------------------------
// The capability the type parameter buys

/// A filesystem with no executable bit must never record one changing.
///
/// Decision 0034's safety property, and the reason `Filesystem::executable`
/// answers `Option<bool>` rather than `bool`. `Memory` models no modes, so it
/// takes the default and says `None`. A recorder that read that as `false`
/// would state `mode <file> plain` for every executable file in the history,
/// and a person's two machines would then take turns flipping the bit off and
/// on, each recording a change the other had to undo.
#[test]
fn a_filesystem_that_models_no_modes_records_none_and_erases_none() {
    let memory = Memory::new();
    memory
        .create_directory(Path::new(ROOT))
        .expect("the working copy");
    let mut store =
        Store::init_on(memory.clone(), Path::new(ROOT).join("history")).expect("a new store");

    put(&memory, "run.sh", "#!/bin/sh\necho hi\n");
    let root = record_folder(&memory, &mut store, Vec::new(), "a script");

    // The map has no such bit, and says so rather than guessing.
    assert_eq!(
        memory
            .executable(&Path::new(ROOT).join("run.sh"))
            .expect("asking is not an error"),
        None
    );

    // Somebody else's machine, which could see the bit, recorded it.
    let held = store
        .get(&root)
        .expect("readable")
        .expect("the root")
        .clone();
    let file = *held.added.keys().next().expect("the script");
    let runnable = RevisionDocument {
        change: "kxryzmorwlvtnsqpkzmuprys".parse().expect("a change ID"),
        parents: BTreeSet::from([root]),
        supersedes: BTreeSet::new(),
        author: AUTHOR.to_owned(),
        when: held.when.clone(),
        revised_by: None,
        revised: None,
        added: BTreeMap::new(),
        moved: BTreeMap::new(),
        modes: BTreeMap::from([(file, Mode::Executable)]),
        links: BTreeMap::new(),
        dropped: BTreeSet::new(),
        edited: BTreeMap::new(),
        text: BTreeMap::new(),
        bytes: BTreeMap::new(),
        extensions: BTreeMap::new(),
        message: "make it runnable".to_owned(),
    };
    let runnable = store.insert(&runnable).expect("writing the revision");
    assert_eq!(
        store.tree(&runnable).expect("the tree").mode(&file),
        Some(Mode::Executable)
    );

    // Now record an ordinary edit here, where the bit cannot be seen. What
    // the folder cannot observe, it must not state.
    put(&memory, "run.sh", "#!/bin/sh\necho there\n");
    let after = record_folder(&memory, &mut store, vec![runnable], "edit the script");
    let document = store.get(&after).expect("readable").expect("the edit");
    assert!(
        document.modes.is_empty(),
        "a folder that cannot see the bit stated one: {:?}",
        document.modes
    );
    assert_eq!(
        store.tree(&after).expect("the tree").mode(&file),
        Some(Mode::Executable),
        "the recorded bit survived a machine that cannot see it"
    );
    assert!(Store::check_on(memory.as_ref(), Path::new(ROOT).join("history")).is_ok());
}

/// A folder with no links refuses the update, naming the links and the reason.
///
/// Decision 0040's other half. `Memory` models no links, so `link_target`
/// takes the default and answers `Ok(None)` — which the contract reserves for
/// exactly that, so one question settles it. Writing a plain file holding the
/// target would invent content no revision stated, which is what git's
/// `core.symlinks=false` does and then explains forever; skipping it silently
/// would leave a folder half-holding a head, which decision 0030 refuses. So
/// it refuses, whole, and says which files and why.
#[test]
fn a_folder_that_models_no_links_refuses_rather_than_inventing_one() {
    let memory = Memory::new();
    memory
        .create_directory(Path::new(ROOT))
        .expect("the working copy");
    let mut store =
        Store::init_on(memory.clone(), Path::new(ROOT).join("history")).expect("a new store");

    put(&memory, "2026/july.md", "July\n");
    let root = record_folder(&memory, &mut store, Vec::new(), "a month");

    // The map has no such thing, and says so rather than guessing.
    assert_eq!(
        memory
            .link_target(&Path::new(ROOT).join("2026/july.md"))
            .expect("asking is not an error"),
        None
    );

    // Somebody else's machine, which has links, recorded one.
    let held = store
        .get(&root)
        .expect("readable")
        .expect("the root")
        .clone();
    let month = *held.added.keys().next().expect("the month");
    let current: FileId = "lqxstvnmpkwyzrolvtsqnkxm".parse().expect("a file ID");
    let linked = RevisionDocument {
        change: "kxryzmorwlvtnsqpkzmuprys".parse().expect("a change ID"),
        parents: BTreeSet::from([root]),
        supersedes: BTreeSet::new(),
        author: AUTHOR.to_owned(),
        when: held.when.clone(),
        revised_by: None,
        revised: None,
        added: BTreeMap::from([(current, "current".to_owned())]),
        moved: BTreeMap::new(),
        modes: BTreeMap::new(),
        links: BTreeMap::from([(current, LinkTarget::Reference(month))]),
        dropped: BTreeSet::new(),
        edited: BTreeMap::new(),
        text: BTreeMap::new(),
        bytes: BTreeMap::new(),
        extensions: BTreeMap::new(),
        message: "point at the month".to_owned(),
    };
    let linked = store.insert(&linked).expect("writing the revision");
    assert_eq!(
        store.tree(&linked).expect("the tree").target(&current),
        Some(&LinkTarget::Reference(month))
    );

    let working = Working::read_on(memory.clone(), Path::new(ROOT), store.skipped())
        .expect("the working copy");
    let refused = historica::update::plan(&store, &working, Path::new(ROOT), &linked)
        .expect_err("a folder with no links cannot hold this tree");
    let said = refused.to_string();
    assert!(said.contains("current"), "{said}: it names the link");
    assert!(
        said.contains("cannot hold a symbolic link"),
        "{said}: and the reason"
    );

    // Nothing was written, and nothing was invented in its place.
    assert_eq!(
        memory
            .look(&Path::new(ROOT).join("current"))
            .expect("asking is not an error"),
        None
    );
}

// ---------------------------------------------------------------------------
// Decision 0043's capability, declined and taken
// ---------------------------------------------------------------------------

/// The same two maps, with a modification time and a read counter.
///
/// `Memory` above models no [`Stamp`], so it takes the default and says
/// `None` — which is the case decision 0043 has to lose nothing on, and the
/// case the tests before this one have been exercising all along. This one
/// models one: a tick that advances on every write, which is what a
/// modification time is for the purpose the catalogue puts it to. Between the
/// two, the same history is recorded and described with the capability and
/// without it, and the reads are counted so that "the folder was not read
/// again" is an assertion rather than a stopwatch.
struct Stamped {
    held: Arc<Memory>,
    /// A tick per write. Nanoseconds, so that the times are far enough apart
    /// for a real filesystem's granularity to be irrelevant to the test.
    ticks: Mutex<u64>,
    times: Mutex<BTreeMap<PathBuf, std::time::SystemTime>>,
    reads: Mutex<BTreeMap<PathBuf, usize>>,
    listings: Mutex<BTreeMap<PathBuf, usize>>,
}

impl Stamped {
    fn new() -> Arc<Self> {
        Arc::new(Self {
            held: Memory::new(),
            ticks: Mutex::new(0),
            times: Mutex::new(BTreeMap::new()),
            reads: Mutex::new(BTreeMap::new()),
            listings: Mutex::new(BTreeMap::new()),
        })
    }

    /// Stamp a path with the next tick, as writing to it does.
    fn touch(&self, path: &Path) {
        let mut ticks = self.ticks.lock().expect("the lock");
        *ticks += 1;
        self.times.lock().expect("the lock").insert(
            path.to_path_buf(),
            std::time::SystemTime::UNIX_EPOCH + std::time::Duration::from_nanos(*ticks),
        );
    }

    /// How many times a directory at or under `path` has been listed.
    fn listings_under(&self, path: &str) -> usize {
        let path = Path::new(ROOT).join(path);
        self.listings
            .lock()
            .expect("the lock")
            .iter()
            .filter(|(listed, _)| listed.starts_with(&path))
            .map(|(_, count)| count)
            .sum()
    }

    /// How many times one path has been read.
    fn reads_of(&self, path: &str) -> usize {
        let path = Path::new(ROOT).join(path);
        *self
            .reads
            .lock()
            .expect("the lock")
            .get(&path)
            .unwrap_or(&0)
    }
}

impl Filesystem for Stamped {
    fn read(&self, path: &Path) -> io::Result<Vec<u8>> {
        *self
            .reads
            .lock()
            .expect("the lock")
            .entry(path.to_path_buf())
            .or_default() += 1;
        self.held.read(path)
    }
    fn write(&self, path: &Path, bytes: &[u8]) -> io::Result<()> {
        self.held.write(path, bytes)?;
        self.touch(path);
        Ok(())
    }
    fn create_new(&self, path: &Path, bytes: &[u8]) -> io::Result<()> {
        self.held.create_new(path, bytes)?;
        self.touch(path);
        Ok(())
    }
    fn create_directory(&self, path: &Path) -> io::Result<()> {
        self.held.create_directory(path)
    }
    fn entries(&self, path: &Path) -> io::Result<Vec<Entry>> {
        *self
            .listings
            .lock()
            .expect("the lock")
            .entry(path.to_path_buf())
            .or_default() += 1;
        self.held.entries(path)
    }
    fn look(&self, path: &Path) -> io::Result<Option<Kind>> {
        self.held.look(path)
    }
    fn rename(&self, from: &Path, to: &Path) -> io::Result<()> {
        self.held.rename(from, to)?;
        self.touch(to);
        Ok(())
    }
    fn remove_file(&self, path: &Path) -> io::Result<()> {
        self.held.remove_file(path)
    }
    fn remove_directory(&self, path: &Path) -> io::Result<()> {
        self.held.remove_directory(path)
    }
    fn stamp(&self, path: &Path) -> io::Result<Option<historica::fs::Stamp>> {
        // Straight out of the map, and deliberately not through `read` above:
        // asking a directory what it already knows is not a read, which is the
        // whole of what this capability is for.
        let Some(modified) = self.times.lock().expect("the lock").get(path).copied() else {
            return Ok(None);
        };
        let size = self.held.read(path).map(|bytes| bytes.len() as u64)?;
        Ok(Some(historica::fs::Stamp { size, modified }))
    }
}

/// Describe the folder, and say what recording it would state.
fn describe<F: Filesystem>(
    store: &Store<F>,
    working: &Working<F>,
    parents: Vec<RevisionId>,
) -> String {
    let surveyed =
        historica::record::survey(store, working, &parents, &[], &[], &Restriction::Everything)
            .expect("surveying the folder");
    format!(
        "added {:?} dropped {:?} edited {:?} modes {:?}",
        surveyed.added,
        surveyed.dropped.values().collect::<Vec<_>>(),
        surveyed.edited.keys().collect::<Vec<_>>(),
        surveyed.modes,
    )
}

/// A folder nobody has touched is described without being read again.
///
/// Decision 0043's whole claim, made countable. The first survey hashes the
/// photograph because nothing has ever said what it holds; the second is
/// answered out of `history/cache/working.txt`, because the directory reports
/// the same size and the same modification time it reported then — and reports
/// them without the file being opened.
#[test]
fn a_folder_nobody_has_touched_is_not_read_a_second_time() {
    let files = Stamped::new();
    files
        .create_directory(Path::new(ROOT))
        .expect("the working copy");
    let mut store =
        Store::init_on(files.clone(), Path::new(ROOT).join("history")).expect("a new store");

    // A file of bytes, which is the case that costs: 0017 stores it whole, so
    // "has it changed" used to be both copies of it read and compared.
    let photograph = Path::new(ROOT).join("photo.png");
    files
        .write(&photograph, &[0u8, 1, 2, 0, 255, 3])
        .expect("a picture");
    let root = record_at(&files, &mut store, Vec::new(), "a picture");

    let working = Working::read_on(files.clone(), Path::new(ROOT), store.skipped())
        .expect("the folder in memory");
    let first = describe(&store, &working, vec![root]);
    let reads = files.reads_of("photo.png");
    assert!(reads > 0, "the first pass has to read it");

    let working = Working::read_on(files.clone(), Path::new(ROOT), store.skipped())
        .expect("the folder again");
    assert_eq!(describe(&store, &working, vec![root]), first);
    assert_eq!(
        files.reads_of("photo.png"),
        reads,
        "the second pass read a file the directory said nobody had written to"
    );

    // And a file somebody *has* written to is read, whatever the catalogue
    // says about it, because the stamp it was catalogued under is gone.
    files
        .write(&photograph, &[0u8, 1, 2, 0, 255, 4])
        .expect("editing the picture");
    let working = Working::read_on(files.clone(), Path::new(ROOT), store.skipped())
        .expect("the folder once more");
    let said = describe(&store, &working, vec![root]);
    assert!(said.contains("edited [\"photo.png\"]"), "{said}");
    assert!(files.reads_of("photo.png") > reads);
}

/// A filesystem that reports no stamp keeps every answer and none of the
/// saving.
///
/// The other half of the same claim, and the reason both new methods are
/// defaulted: `Memory` models neither, so it reads the folder on every command
/// exactly as it did before decision 0043 — and says the same things about it
/// as the filesystem that models both. Nothing about correctness may turn on a
/// capability a host does not have.
#[test]
fn a_filesystem_that_reports_no_stamp_answers_alike_and_writes_no_catalogue() {
    let plain = Memory::new();
    plain
        .create_directory(Path::new(ROOT))
        .expect("the working copy");
    let mut store =
        Store::init_on(plain.clone(), Path::new(ROOT).join("history")).expect("a new store");
    put(&plain, "notes.md", "First thought.\n");
    plain
        .write(&Path::new(ROOT).join("photo.png"), &[0u8, 1, 2, 0, 255, 3])
        .expect("a picture");
    let root = record_folder(&plain, &mut store, Vec::new(), "a journal and a picture");

    assert_eq!(
        plain
            .stamp(&Path::new(ROOT).join("photo.png"))
            .expect("asking is not an error"),
        None,
        "a filesystem with nothing to report must say so rather than guess"
    );

    let working = Working::read_on(plain.clone(), Path::new(ROOT), store.skipped())
        .expect("the folder in memory");
    let said = describe(&store, &working, vec![root]);
    // Twice, because a folder that reads the same twice is the property, and
    // because the second pass is where a catalogue would have been consulted.
    let working = Working::read_on(plain.clone(), Path::new(ROOT), store.skipped())
        .expect("the folder again");
    assert_eq!(describe(&store, &working, vec![root]), said);
    assert!(said.contains("edited []"), "nothing differs: {said}");

    // And nothing was written to `cache/` about a folder nothing can be
    // believed about: a catalogue no reader could ever check is a file with no
    // reason to exist.
    let held = plain.held.lock().expect("the lock");
    assert!(
        !held
            .files
            .contains_key(&Path::new(ROOT).join("history/cache/working.txt")),
        "a filesystem that reports no stamp wrote a catalogue anyway"
    );
}

/// The same as `record_folder`, for a filesystem that is not `Memory`.
fn record_at<F: Filesystem + Clone>(
    files: &F,
    store: &mut Store<F>,
    parents: Vec<RevisionId>,
    message: &str,
) -> RevisionId {
    let mut platform = Platform;
    let working =
        Working::read_on(files.clone(), Path::new(ROOT), store.skipped()).expect("the folder");
    record(
        store,
        &working,
        &Recording {
            parents,
            author: AUTHOR.to_owned(),
            when: platform.now().expect("a clock"),
            message: message.to_owned(),
            moves: Vec::new(),
            at: Vec::new(),
            accepted: BTreeSet::new(),
            only: Restriction::Everything,
        },
        &mut platform,
    )
    .expect("recording")
    .revision
}

// ---------------------------------------------------------------------------

/// A filesystem that is `!Send`, `!Sync`, and not `Debug`.
///
/// This is the shape a host's handle actually arrives in — a Swift object
/// behind an FFI pointer, a `JsValue` on a single-threaded WASM target. Under
/// an `Arc<dyn Filesystem>` the trait would have had to require all three, and
/// a host in this position would have had to write `unsafe impl Send` to be
/// allowed in at all. Here it is an ordinary `F`, and the store it makes has
/// exactly the capabilities it does.
struct Awkward {
    held: Rc<Memory>,
    reads: Cell<usize>,
}

impl Filesystem for Awkward {
    fn read(&self, path: &Path) -> io::Result<Vec<u8>> {
        self.reads.set(self.reads.get() + 1);
        self.held.read(path)
    }
    fn write(&self, path: &Path, bytes: &[u8]) -> io::Result<()> {
        self.held.write(path, bytes)
    }
    fn create_new(&self, path: &Path, bytes: &[u8]) -> io::Result<()> {
        self.held.create_new(path, bytes)
    }
    fn create_directory(&self, path: &Path) -> io::Result<()> {
        self.held.create_directory(path)
    }
    fn entries(&self, path: &Path) -> io::Result<Vec<Entry>> {
        self.held.entries(path)
    }
    fn look(&self, path: &Path) -> io::Result<Option<Kind>> {
        self.held.look(path)
    }
    fn rename(&self, from: &Path, to: &Path) -> io::Result<()> {
        self.held.rename(from, to)
    }
    fn remove_file(&self, path: &Path) -> io::Result<()> {
        self.held.remove_file(path)
    }
    fn remove_directory(&self, path: &Path) -> io::Result<()> {
        self.held.remove_directory(path)
    }
}

#[test]
fn a_filesystem_that_is_neither_send_sync_nor_debug_still_makes_a_store() {
    let files = Awkward {
        held: Rc::new(Memory::default()),
        reads: Cell::new(0),
    };
    files
        .create_directory(Path::new(ROOT))
        .expect("the working copy");

    let store =
        Store::init_on(files, Path::new(ROOT).join("history")).expect("a store over a handle");
    assert!(store.is_empty());

    // It really read through it: `init` opens the store it has just written.
    assert!(store.filesystem().reads.get() > 0);
}

#[test]
fn the_disk_store_keeps_every_capability_it_had() {
    // The derives are conditional on `F`, so this is the assertion that the
    // ordinary case lost nothing when the filesystem became a parameter.
    fn is_send<T: Send>() {}
    fn is_clone<T: Clone>() {}
    fn is_debug<T: std::fmt::Debug>() {}

    is_send::<Store<historica::fs::Disk>>();
    is_clone::<Store<historica::fs::Disk>>();
    is_debug::<Store<historica::fs::Disk>>();

    is_send::<historica::working::Working<historica::fs::Disk>>();
    is_clone::<historica::working::Working<historica::fs::Disk>>();
}

/// Decision 0030 over decision 0025: the folder catches up to a head through
/// the trait, so a host holding its documents in maps — or an iCloud folder —
/// updates them the way a person at a terminal does.
#[test]
fn the_folder_updates_in_memory_too() {
    let (memory, store, _first, second) = history();

    // Stand the folder at the first revision by hand — every byte recorded —
    // and leave a stray beside it that nothing has recorded.
    put(&memory, "notes.md", "First thought.\n");
    put(&memory, "stray.md", "unrecorded\n");

    let working = Working::read_on(memory.clone(), Path::new(ROOT), store.skipped())
        .expect("the folder in memory");
    let plan = historica::update::plan(&store, &working, Path::new(ROOT), &second).expect("a plan");
    assert_eq!(plan.writes.len(), 1, "one file differs");
    let applied = historica::update::apply(&store, &working, Path::new(ROOT), &plan)
        .expect("applying the plan");
    assert_eq!(applied.wrote, ["notes.md"]);
    assert!(applied.left.is_empty() && applied.folded.is_empty());
    assert_eq!(
        memory
            .read(&Path::new(ROOT).join("notes.md"))
            .expect("the file"),
        b"First thought.\nA second one.\n"
    );
    assert_eq!(
        memory
            .read(&Path::new(ROOT).join("stray.md"))
            .expect("still here"),
        b"unrecorded\n",
        "a stray unrecorded file is not update's to touch"
    );

    // Unrecorded bytes at a path the head holds refuse the whole update.
    put(&memory, "notes.md", "an unrecorded edit\n");
    let working = Working::read_on(memory.clone(), Path::new(ROOT), store.skipped())
        .expect("the folder in memory");
    let refused = historica::update::plan(&store, &working, Path::new(ROOT), &second);
    assert!(matches!(
        refused,
        Err(historica::update::UpdateError::Refused { .. })
    ));
}

/// Decision 0025's per-file rule, held through the trait's own guard:
/// `Filesystem::write_if` is handed what the plan saw, and a file that moved
/// between the plan's look and the apply is left where it stands and
/// reported — not written over, and not an error. `Memory` takes the trait's
/// default, so this is the read-compare-write every host that declines the
/// capability performs.
#[test]
fn a_file_that_moved_between_plan_and_apply_is_left_and_reported() {
    let (memory, store, _first, second) = history();

    // The folder stands at the first revision, every byte recorded.
    put(&memory, "notes.md", "First thought.\n");
    let working = Working::read_on(memory.clone(), Path::new(ROOT), store.skipped())
        .expect("the folder in memory");
    let plan = historica::update::plan(&store, &working, Path::new(ROOT), &second).expect("a plan");
    assert_eq!(plan.writes.len(), 1, "one file differs");

    // The race: an edit lands after the plan looked and before apply does.
    put(&memory, "notes.md", "work the plan never saw\n");

    let applied = historica::update::apply(&store, &working, Path::new(ROOT), &plan)
        .expect("applying the plan");
    assert!(applied.wrote.is_empty(), "{applied:?}");
    assert_eq!(
        applied.left,
        [(
            "notes.md".to_owned(),
            "it changed underneath the update".to_owned()
        )]
    );
    assert_eq!(
        memory
            .read(&Path::new(ROOT).join("notes.md"))
            .expect("still here"),
        b"work the plan never saw\n",
        "a raced edit is not update's to clobber"
    );
}

/// A read places a digest without asking what the directory holds.
///
/// Decision 0036 believed a catalogue only once a walk had proved the set of
/// paths it names is the set the directory holds, and every content command
/// paid for that walk. A lookup does not need the proof: the catalogue says
/// where to look, the reader hashes what it finds there, and a catalogue that
/// is wrong costs the pass every reader already falls back to. So the walk is
/// what an *absence* costs, and this is the presence.
#[test]
fn a_content_read_does_not_list_the_directory_the_catalogue_places_it_in() {
    let files = Stamped::new();
    files
        .create_directory(Path::new(ROOT))
        .expect("the working copy");
    let mut store =
        Store::init_on(files.clone(), Path::new(ROOT).join("history")).expect("a new store");
    files
        .write(&Path::new(ROOT).join("notes.md"), b"First thought.\n")
        .expect("a journal");
    let root = record_at(&files, &mut store, Vec::new(), "a journal");
    files
        .write(
            &Path::new(ROOT).join("notes.md"),
            b"First thought.\nSecond thought.\n",
        )
        .expect("a second thought");
    let second = record_at(&files, &mut store, vec![root], "a second thought");
    let file = *store
        .tree(&second)
        .expect("a tree")
        .files()
        .next()
        .expect("the file")
        .0;

    // One read to bring `cache/` up to date with what recording wrote: the
    // pass writes the catalogue before the documents it is about to add, so
    // the first reader after a write is the one that pays for them.
    let opened = Store::open_on(files.clone(), Path::new(ROOT).join("history")).expect("the store");
    let first = opened.content(&second, &file).expect("the content");
    drop(opened);

    let listings = files.listings_under("history/operations");
    let opened = Store::open_on(files.clone(), Path::new(ROOT).join("history")).expect("the store");
    assert_eq!(
        opened.content(&second, &file).expect("the content"),
        first,
        "the same file, read the cheap way"
    );
    assert_eq!(
        files.listings_under("history/operations"),
        listings,
        "a read asked the directory what it holds"
    );

    // And a digest nothing places still costs the pass, because *not here* is
    // the answer a catalogue may not give.
    let absent = historica::format::digest(b"nothing wrote these bytes");
    assert!(opened.operation(&absent).expect("a lookup").is_none());
    assert!(
        files.listings_under("history/operations") > listings,
        "an absence was reported without reading the directory"
    );
}
