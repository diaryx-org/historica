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

use historica::core::RevisionId;
use historica::format::{Mode, RevisionDocument, Version};
use historica::fs::{Entry, Filesystem, Kind};
use historica::record::{Clock as _, Platform, Recording, record};
use historica::store::{Name, Severity, Store};
use historica::working::{Skipped, Working};

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
    assert!(store.get(&first).is_some() && store.get(&second).is_some());

    // Every byte of it is in the map and nowhere else — including the header
    // and the default `skipped.txt` that `init` writes.
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
    let rules: Vec<_> = Skipped::parse("skip build.log\n")
        .expect("a rule")
        .rules()
        .cloned()
        .collect();
    store.append_skipped(&rules).expect("a rule");

    let reopened = Store::open_on(memory.clone(), store.root()).expect("reopening");
    assert_eq!(reopened.name("main"), Some(Name::Revision(second)));
    assert!(
        reopened.skipped().skips("build.log"),
        "the appended rule should be read back"
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
            version: historica::format::Version::V1,
            forgets: None,
            result: None,
            operations: Vec::new(),
        })
        .expect("an operation document nothing names");
    assert!(store.operation(&orphan).is_some());

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
    assert!(reopened.get(&first).is_some());
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
    let settled = store.arrangement().expect("a plan");
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
    let plan = store.arrangement().expect("a plan");
    assert_eq!(
        plan.renames.len(),
        scattered.len(),
        "every flattened file should have somewhere to go"
    );

    let done = store.arrange().expect("arranging");
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

    // And arranging an arranged store moves nothing, in memory as on disk.
    assert!(store.arrange().expect("again").is_empty());
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
    let held = store.get(&root).expect("the root").clone();
    let file = *held.added.keys().next().expect("the script");
    let runnable = RevisionDocument {
        version: Version::V4,
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
    let document = store.get(&after).expect("the edit");
    assert!(
        document.modes.is_empty(),
        "a folder that cannot see the bit stated one: {:?}",
        document.modes
    );
    assert_eq!(
        document.version,
        Version::V1,
        "and claimed a version for it"
    );
    assert_eq!(
        store.tree(&after).expect("the tree").mode(&file),
        Some(Mode::Executable),
        "the recorded bit survived a machine that cannot see it"
    );
    assert!(Store::check_on(memory.as_ref(), Path::new(ROOT).join("history")).is_ok());
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
    let applied =
        historica::update::apply(&working, Path::new(ROOT), &plan).expect("applying the plan");
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
