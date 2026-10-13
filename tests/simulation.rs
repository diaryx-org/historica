//! Replicas that meet only by copying files, simulated.
//!
//! Decision 0003 says a store is synced by anything that copies files, and
//! most of what this format promises is a promise about that sentence: that
//! union by copy converges, that a cache cannot tell a person something the
//! store does not say (0035, 0078), and that a redaction cannot be undone by
//! transport (0014, 0079). Every one of those was argued; two of them were
//! found broken by hand after they were argued, which is what this file is
//! for.
//!
//! Each replica is a folder and a store in a filesystem of its own, held in
//! memory, with a cache outside the store where 0078 says a host keeps one.
//! A round is a list of actions drawn from a seed before it runs: work done
//! at one replica — edit the folder, `record`, `merge`, `amend`, `abandon`,
//! `carry`, `forget`, `prune`, `update`, `export` to a static server and
//! `evict` what it holds — or a sync between two. A sync is nothing
//! historica wrote. It copies some of one store's files into another, in any
//! order, stops wherever it stops, never deletes, and may leave the last file
//! it was writing cut short, as `cp` does when it is killed.
//!
//! After every action, every replica is held to four things:
//!
//! - **`check` passes**, unless the replica holds a file a sync cut short,
//!   in which case every error it reports names that file.
//! - **A cache changes nothing but time** (0035, 0078): a store opened with
//!   its cache answers every question exactly as one opened without.
//! - **Forgotten bytes stay forgotten** (0014, 0079): a replica holding the
//!   documents a `forget` wrote shows none of the items it destroyed, through
//!   any reader, cached or not, whatever else a sync has brought back.
//! - **The same files give the same answers**: two replicas holding the same
//!   documents agree on heads, trees, content, and the merge of their heads,
//!   whatever order the files arrived in.
//!
//! Two of those are broken today in ways the search found and a decision has
//! to settle, each written down as a task: [a merge agrees by
//! text](../docs/tasks/a-merge-agrees-by-text.md) and [a stand-in filed
//! beside another copy](../docs/tasks/a-stand-in-filed-beside-another-copy.md).
//! `agreed_by_text` and `beside_elsewhere` recognise their signatures, so
//! that a run meeting one keeps looking for something else rather than
//! stopping there; `HISTORICA_SIMULATION_STRICT=1` turns them back into
//! failures, and closing either task deletes its function.
//!
//! A failure prints its seed and the round shrunk to the fewest actions that
//! still fail, the convention `tests/conformance.rs` set: `cargo test` runs a
//! fixed seed, `cargo xtask test` rotates it, and `cargo xtask soak` runs
//! many more rounds than either. Beside `HISTORICA_SIMULATION_SEED` and
//! `HISTORICA_SIMULATION_ROUNDS`, `HISTORICA_SIMULATION_DUMP=<dir>` writes
//! the shrunk round's replicas out for the command line to look at, and
//! `HISTORICA_SIMULATION_TALLY=1` prints what each kind of action did, which
//! is how to tell a search that is working from one whose actions are all
//! being refused.
//!
//! What it does not reach yet: renames, links, the executable bit, skip
//! rules, bookmarks beyond copying them, `squash`, `arrange`, and `receive`
//! and `fetch` — the transports historica wrote, as opposed to the one it
//! did not.

use std::collections::{BTreeMap, BTreeSet};
use std::io;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::{Duration, SystemTime};

use historica::core::{FileId, RevisionId};
use historica::format::{Timestamp, digest};
use historica::fs::{Entry, Filesystem, Kind, Stamp};
use historica::record::carry::{Carrying, carry};
use historica::record::{
    Abandoning, Amendment, Entropy, Recording, Restriction, SourceError, abandon, amend, record,
    standing_on,
};
use historica::store::{Extent, Finding, Forgetting, Store};
use historica::tree::{Kind as FileKind, TreeContest};
use historica::working::Working;

// ---------------------------------------------------------------------------
// A filesystem with a clock in it
// ---------------------------------------------------------------------------

/// One machine's disk: files with a modification time, and directories.
///
/// The time is what makes this more than `tests/filesystem.rs`'s `Memory`.
/// Decisions 0043 and 0058 believe a cached answer where a file's size and
/// time say it has not changed, and a filesystem that reports no time is one
/// where nothing cached is ever believed — which is the case those decisions
/// lose nothing on, and the case where none of their bugs can be found.
///
/// The clock ticks once per write and is read through a granularity, because
/// a real one is coarse: two writes within one tick of a two-second FAT
/// clock carry one time, and a rule that compares times has to survive that.
#[derive(Debug)]
struct Disk {
    held: Mutex<Held>,
    /// How many ticks one reported unit of time spans.
    granularity: u64,
}

#[derive(Debug, Default)]
struct Held {
    files: BTreeMap<PathBuf, (Vec<u8>, u64)>,
    directories: BTreeSet<PathBuf>,
    tick: u64,
}

fn missing(path: &Path) -> io::Error {
    io::Error::new(io::ErrorKind::NotFound, format!("{}", path.display()))
}

impl Disk {
    fn new(granularity: u64) -> Arc<Self> {
        Arc::new(Self {
            held: Mutex::new(Held::default()),
            granularity,
        })
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, Held> {
        self.held
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    /// Every file at or below `root`, with its bytes and time.
    fn files_under(&self, root: &Path) -> Vec<(PathBuf, Vec<u8>, u64)> {
        self.lock()
            .files
            .iter()
            .filter(|(path, _)| path.starts_with(root))
            .map(|(path, (bytes, time))| (path.clone(), bytes.clone(), *time))
            .collect()
    }

    fn bytes(&self, path: &Path) -> Option<Vec<u8>> {
        self.lock().files.get(path).map(|(bytes, _)| bytes.clone())
    }

    /// Write as a sync tool does: with the time it chose, or this disk's next.
    fn put(&self, path: &Path, bytes: &[u8], time: Option<u64>) {
        let mut held = self.lock();
        held.tick += 1;
        let time = time.unwrap_or(held.tick);
        if let Some(parent) = path.parent() {
            for ancestor in parent.ancestors() {
                held.directories.insert(ancestor.to_path_buf());
            }
        }
        held.files
            .insert(path.to_path_buf(), (bytes.to_vec(), time));
    }

    fn remove(&self, path: &Path) {
        self.lock().files.remove(path);
    }

    /// A copy of this disk without some of its files.
    fn without(&self, gone: &BTreeSet<PathBuf>) -> Arc<Self> {
        let held = self.lock();
        let copy = Held {
            files: held
                .files
                .iter()
                .filter(|(path, _)| !gone.contains(*path))
                .map(|(path, file)| (path.clone(), file.clone()))
                .collect(),
            directories: held.directories.clone(),
            tick: held.tick,
        };
        Arc::new(Self {
            held: Mutex::new(copy),
            granularity: self.granularity,
        })
    }
}

impl Filesystem for Disk {
    fn read(&self, path: &Path) -> io::Result<Vec<u8>> {
        self.bytes(path).ok_or_else(|| missing(path))
    }

    fn write(&self, path: &Path, bytes: &[u8]) -> io::Result<()> {
        let mut held = self.lock();
        held.tick += 1;
        let tick = held.tick;
        held.files
            .insert(path.to_path_buf(), (bytes.to_vec(), tick));
        Ok(())
    }

    fn create_new(&self, path: &Path, bytes: &[u8]) -> io::Result<()> {
        if self.lock().files.contains_key(path) {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                format!("{}", path.display()),
            ));
        }
        self.write(path, bytes)
    }

    fn create_directory(&self, path: &Path) -> io::Result<()> {
        let mut held = self.lock();
        for ancestor in path.ancestors() {
            held.directories.insert(ancestor.to_path_buf());
        }
        Ok(())
    }

    fn entries(&self, path: &Path) -> io::Result<Vec<Entry>> {
        let held = self.lock();
        if !held.directories.contains(path) {
            return Err(missing(path));
        }
        let mut found = BTreeMap::new();
        let children = held
            .files
            .keys()
            .map(|file| (file, Kind::File))
            .chain(held.directories.iter().map(|dir| (dir, Kind::Directory)));
        for (candidate, kind) in children {
            let Ok(relative) = candidate.strip_prefix(path) else {
                continue;
            };
            let mut components = relative.components();
            let Some(first) = components.next() else {
                continue;
            };
            let kind = match components.next() {
                Some(_) => Kind::Directory,
                None => kind,
            };
            found.insert(path.join(first), kind);
        }
        // Reversed, as `tests/filesystem.rs` does and for its reason: the
        // trait promises no order, and a sorted answer would hide a missing
        // sort.
        Ok(found
            .into_iter()
            .rev()
            .map(|(path, kind)| Entry { path, kind })
            .collect())
    }

    fn look(&self, path: &Path) -> io::Result<Option<Kind>> {
        let held = self.lock();
        if held.files.contains_key(path) {
            return Ok(Some(Kind::File));
        }
        if held.directories.contains(path) {
            return Ok(Some(Kind::Directory));
        }
        Ok(None)
    }

    fn rename(&self, from: &Path, to: &Path) -> io::Result<()> {
        let mut held = self.lock();
        let (bytes, _) = held.files.remove(from).ok_or_else(|| missing(from))?;
        // A rename keeps the file's time on every platform this models.
        held.tick += 1;
        let tick = held.tick;
        held.files.insert(to.to_path_buf(), (bytes, tick));
        Ok(())
    }

    fn remove_file(&self, path: &Path) -> io::Result<()> {
        self.lock()
            .files
            .remove(path)
            .map(|_| ())
            .ok_or_else(|| missing(path))
    }

    fn remove_directory(&self, path: &Path) -> io::Result<()> {
        let mut held = self.lock();
        if !held.directories.contains(path) {
            return Err(missing(path));
        }
        let occupied = held
            .files
            .keys()
            .chain(held.directories.iter())
            .any(|other| other != path && other.starts_with(path));
        if occupied {
            return Err(io::Error::new(
                io::ErrorKind::DirectoryNotEmpty,
                format!("{}", path.display()),
            ));
        }
        held.directories.remove(path);
        Ok(())
    }

    fn stamp(&self, path: &Path) -> io::Result<Option<Stamp>> {
        let held = self.lock();
        if let Some((bytes, time)) = held.files.get(path) {
            let coarse = time / self.granularity * self.granularity;
            return Ok(Some(Stamp {
                size: bytes.len() as u64,
                modified: SystemTime::UNIX_EPOCH + Duration::from_secs(1_700_000_000 + coarse),
            }));
        }
        if held.directories.contains(path) {
            return Ok(None);
        }
        Err(missing(path))
    }
}

// ---------------------------------------------------------------------------
// Randomness, drawn from one seed
// ---------------------------------------------------------------------------

/// The seed `cargo test` searches from, so that two runs are the same run.
const SEED: u64 = 0x0003_5e1e_c7ed_f11e;

/// Rounds per run. Each is a whole history replayed many times over, so this
/// is the number that decides how long `cargo test` spends here.
const ROUNDS: usize = 8;

fn seed() -> u64 {
    match std::env::var("HISTORICA_SIMULATION_SEED") {
        Ok(given) => {
            let parsed = match given.strip_prefix("0x") {
                Some(hex) => u64::from_str_radix(hex, 16),
                None => given.parse(),
            };
            parsed
                .unwrap_or_else(|_| panic!("HISTORICA_SIMULATION_SEED is not a number: {given:?}"))
        }
        Err(_) => SEED,
    }
}

fn rounds() -> usize {
    std::env::var("HISTORICA_SIMULATION_ROUNDS")
        .ok()
        .and_then(|given| given.parse().ok())
        .unwrap_or(ROUNDS)
}

/// splitmix64: small, fast, and the same everywhere.
#[derive(Debug, Clone)]
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, bound: usize) -> usize {
        if bound == 0 {
            return 0;
        }
        (self.next() % bound as u64) as usize
    }

    fn chance(&mut self, percent: u64) -> bool {
        self.next() % 100 < percent
    }
}

/// Identifiers a replica mints, from its own stream.
///
/// Decision 0010 made entropy an input for exactly this: a writer whose
/// identifiers come from a seed writes the same bytes every time the round
/// is replayed.
struct Minting(Rng);

impl Entropy for Minting {
    fn fill(&mut self, bytes: &mut [u8]) -> Result<(), SourceError> {
        for chunk in bytes.chunks_mut(8) {
            let word = self.0.next().to_le_bytes();
            chunk.copy_from_slice(&word[..chunk.len()]);
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// A round, as a value
// ---------------------------------------------------------------------------

/// The files a folder may hold. Three of lines and one of bytes, which is
/// enough to reach a rename-free tree, a contested merge, and both of
/// forgetting's extents.
const FILES: [&str; 4] = ["a.txt", "b.txt", "notes/c.txt", "photo.bin"];

/// One thing that happens. Every parameter is a number taken modulo whatever
/// it indexes when it runs, so that an action means something in any state
/// and removing one from a plan leaves the rest meaning roughly what they
/// meant — which is what lets a failing round be shrunk.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Action {
    /// Change one file in a replica's folder.
    Edit {
        replica: usize,
        file: usize,
        how: u64,
    },
    /// Edit the folder `edits` times, then record it against one current
    /// head. The edits are part of the action because a record with nothing
    /// to record is a refusal, and a round of refusals tests nothing.
    Record {
        replica: usize,
        head: u64,
        edits: u64,
    },
    /// Lay the merge of every current head into the folder and record it.
    Merge { replica: usize },
    /// Amend one current head: with the folder if nothing stands on it, as a
    /// reword if something does.
    Amend { replica: usize, head: u64 },
    /// Abandon a revision, alone or with everything standing on it.
    Abandon {
        replica: usize,
        pick: u64,
        only: bool,
    },
    /// Carry whatever stands on a rewritten revision onto its rewrite.
    Carry { replica: usize },
    /// Forget some lines of a file, or a photograph, at a current head.
    Forget {
        replica: usize,
        head: u64,
        file: usize,
        span: u64,
    },
    /// Delete superseded revisions nothing stands on.
    Prune { replica: usize },
    /// Bring the folder to the one current head.
    Update { replica: usize },
    /// Export the one current head to the server, with a listing beside it,
    /// as a person publishes a copy for others to fetch from (0052).
    Publish { replica: usize },
    /// Let go of the photograph's bytes, where the published copy holds
    /// them (0067).
    Evict { replica: usize },
    /// Copy files from one store into another.
    Sync {
        from: usize,
        to: usize,
        /// Orders the files and decides how many are copied.
        shuffle: u64,
        /// Whether the copy stops partway through its last file.
        torn: bool,
        /// Whether the copy keeps each file's time, as `rsync -t` does.
        keep_times: bool,
    },
}

impl Action {
    fn replicas(&self) -> Vec<usize> {
        match self {
            Action::Sync { from, to, .. } => vec![*from, *to],
            Action::Edit { replica, .. }
            | Action::Record { replica, .. }
            | Action::Merge { replica }
            | Action::Amend { replica, .. }
            | Action::Abandon { replica, .. }
            | Action::Carry { replica }
            | Action::Forget { replica, .. }
            | Action::Prune { replica }
            | Action::Update { replica }
            | Action::Publish { replica }
            | Action::Evict { replica } => vec![*replica],
        }
    }
}

#[derive(Debug, Clone)]
struct Plan {
    replicas: usize,
    /// Coarseness of each replica's clock, in ticks.
    granularity: Vec<u64>,
    actions: Vec<Action>,
}

impl Plan {
    /// The same plan with one replica gone, every other keeping its number.
    fn without(&self, gone: usize) -> Self {
        let actions = self
            .actions
            .iter()
            .filter(|action| !action.replicas().contains(&gone))
            .map(|action| {
                let shift = |at: usize| if at > gone { at - 1 } else { at };
                match action.clone() {
                    Action::Sync {
                        from,
                        to,
                        shuffle,
                        torn,
                        keep_times,
                    } => Action::Sync {
                        from: shift(from),
                        to: shift(to),
                        shuffle,
                        torn,
                        keep_times,
                    },
                    Action::Edit { replica, file, how } => Action::Edit {
                        replica: shift(replica),
                        file,
                        how,
                    },
                    Action::Record {
                        replica,
                        head,
                        edits,
                    } => Action::Record {
                        replica: shift(replica),
                        head,
                        edits,
                    },
                    Action::Merge { replica } => Action::Merge {
                        replica: shift(replica),
                    },
                    Action::Amend { replica, head } => Action::Amend {
                        replica: shift(replica),
                        head,
                    },
                    Action::Abandon {
                        replica,
                        pick,
                        only,
                    } => Action::Abandon {
                        replica: shift(replica),
                        pick,
                        only,
                    },
                    Action::Carry { replica } => Action::Carry {
                        replica: shift(replica),
                    },
                    Action::Forget {
                        replica,
                        head,
                        file,
                        span,
                    } => Action::Forget {
                        replica: shift(replica),
                        head,
                        file,
                        span,
                    },
                    Action::Prune { replica } => Action::Prune {
                        replica: shift(replica),
                    },
                    Action::Update { replica } => Action::Update {
                        replica: shift(replica),
                    },
                    Action::Publish { replica } => Action::Publish {
                        replica: shift(replica),
                    },
                    Action::Evict { replica } => Action::Evict {
                        replica: shift(replica),
                    },
                }
            })
            .collect();
        let mut granularity = self.granularity.clone();
        granularity.remove(gone);
        Plan {
            replicas: self.replicas - 1,
            granularity,
            actions,
        }
    }
}

/// Draw a round. Edits and records dominate, because there has to be work
/// before anything else has anything to act on; syncs are frequent, because
/// they are what is under test.
fn plan(rng: &mut Rng) -> Plan {
    let replicas = 2 + rng.below(2);
    let granularity = (0..replicas)
        .map(|_| if rng.chance(50) { 1 } else { 3 })
        .collect();
    let length = 30 + rng.below(50);
    let mut actions = Vec::with_capacity(length);
    for _ in 0..length {
        let replica = rng.below(replicas);
        let action = match rng.below(100) {
            0..=21 => Action::Edit {
                replica,
                file: rng.below(FILES.len()),
                how: rng.next(),
            },
            22..=39 => Action::Record {
                replica,
                head: rng.next(),
                edits: rng.next(),
            },
            40..=45 => Action::Merge { replica },
            46..=51 => Action::Amend {
                replica,
                head: rng.next(),
            },
            52..=55 => Action::Abandon {
                replica,
                pick: rng.next(),
                only: rng.chance(50),
            },
            56..=58 => Action::Carry { replica },
            59..=66 => Action::Forget {
                replica,
                head: rng.next(),
                file: rng.below(FILES.len()),
                span: rng.next(),
            },
            67..=69 => Action::Prune { replica },
            70..=73 => Action::Update { replica },
            74..=75 => Action::Publish { replica },
            76..=77 => Action::Evict { replica },
            _ => {
                let to = (replica + 1 + rng.below(replicas - 1)) % replicas;
                Action::Sync {
                    from: replica,
                    to,
                    shuffle: rng.next(),
                    torn: rng.chance(8),
                    keep_times: rng.chance(50),
                }
            }
        };
        actions.push(action);
    }
    Plan {
        replicas,
        granularity,
        actions,
    }
}

// ---------------------------------------------------------------------------
// Replicas
// ---------------------------------------------------------------------------

const REPOSITORY: &str = "/folder";
const STORE: &str = "/folder/history";
/// Outside the store and the folder both, where decision 0078 says a host
/// keeps a store's caches.
const CACHE: &str = "/caches/folder";
const AUTHOR: &str = "Sim <sim@example.com>";
/// Where a replica publishes on the server, and the listing beside it.
const PUBLISHED: &str = "/www/published";
const MANIFEST: &str = "/www/offer.txt";

/// The server, as `fetch` and `evict` reach it: a path is a file or nothing.
struct Server(Arc<Disk>);

impl historica::store::Source for Server {
    fn get(&self, path: &str) -> Result<Option<Vec<u8>>, historica::store::Unreachable> {
        Ok(self.0.bytes(&Path::new("/www").join(path)))
    }
}

type SimStore = Store<Arc<Disk>>;

struct Replica {
    disk: Arc<Disk>,
    minting: Minting,
    /// Files a sync cut short and nothing has finished since.
    torn: BTreeSet<PathBuf>,
}

/// What a `forget` destroyed, and what it wrote saying so.
#[derive(Debug, Clone)]
struct Destroyed {
    /// The lines destroyed, by the name decision 0032 gives an item: the
    /// document that minted it and its ordinal there. By name and not by
    /// text, because 0014 forgets items: an amendment or a re-recording
    /// mints a second item with the same text, and that one is not forgotten
    /// by forgetting the first.
    items: BTreeSet<ItemName>,
    /// The photograph destroyed, by the digest of its bytes.
    payload: Option<RevisionId>,
    /// The digests of the forgetting documents it wrote. A replica holding
    /// all of them has been told.
    stand_ins: BTreeSet<RevisionId>,
    /// Where it happened, for the report.
    at: usize,
}

struct World {
    replicas: Vec<Replica>,
    /// A static file server every replica can publish to and read from.
    server: Arc<Disk>,
    destroyed: Vec<Destroyed>,
    /// A counter for the text an edit writes, so that every line is unique.
    written: usize,
    step: usize,
    /// What each kind of action did, for `HISTORICA_SIMULATION_TALLY`.
    tally: BTreeMap<String, usize>,
    /// What each replica said when it was last read, and the documents it
    /// held then.
    seen: Vec<Option<(BTreeSet<RevisionId>, Answers)>>,
}

impl World {
    fn new(plan: &Plan, seed: u64) -> Self {
        let replicas = (0..plan.replicas)
            .map(|at| {
                let disk = Disk::new(plan.granularity[at]);
                disk.create_directory(Path::new(REPOSITORY))
                    .expect("a folder");
                Replica {
                    disk,
                    minting: Minting(Rng(seed ^ (0x5eed_0000 + at as u64))),
                    torn: BTreeSet::new(),
                }
            })
            .collect::<Vec<_>>();
        let first = Store::init_on(replicas[0].disk.clone(), STORE).expect("an empty store");
        drop(first);
        let mut world = Self {
            replicas,
            server: Disk::new(1),
            destroyed: Vec::new(),
            written: 0,
            step: 0,
            tally: BTreeMap::new(),
            seen: vec![None; plan.replicas],
        };
        // One root holding every file, recorded once and copied with its
        // folder to every other replica, as a person copies a store to a
        // second machine. Without it each replica adds its own `a.txt`, and
        // every merge after the first sync meets two files claiming a path.
        for file in 0..FILES.len() {
            world.edit(0, file, file as u64);
        }
        let mut store = world.open(0).expect("the store just made");
        world
            .record_onto(
                0,
                &mut store,
                Vec::new(),
                "root",
                Vec::new(),
                BTreeSet::new(),
            )
            .expect("a root");
        let source = world.replicas[0].disk.clone();
        for (path, bytes, time) in source.files_under(Path::new(REPOSITORY)) {
            for replica in &world.replicas[1..] {
                replica.disk.put(&path, &bytes, Some(time));
            }
        }
        world
    }

    fn open(&self, at: usize) -> Result<SimStore, String> {
        Store::open_caching_on(self.replicas[at].disk.clone(), STORE, CACHE)
            .map_err(|error| format!("open: {error}"))
    }

    fn working(&self, at: usize, store: &SimStore) -> Result<Working<Arc<Disk>>, String> {
        Working::read_caching_on(
            self.replicas[at].disk.clone(),
            Path::new(REPOSITORY),
            store.skipped(),
            CACHE,
        )
        .map_err(|error| format!("working: {error}"))
    }

    /// A moment that only moves forward, and is the same on every replay.
    fn now(&self) -> Timestamp {
        let minutes = self.step;
        format!(
            "2026-01-{:02}T{:02}:{:02}:00+00:00",
            1 + minutes / (24 * 60) % 28,
            minutes / 60 % 24,
            minutes % 60
        )
        .parse()
        .expect("a timestamp")
    }

    fn count<T, E: std::fmt::Debug>(&mut self, what: &str, outcome: &Result<T, E>) {
        let key = match outcome {
            Ok(_) => format!("{what} ok"),
            Err(error) => {
                let said = format!("{error:?}");
                let kind: String = said.chars().take_while(|c| c.is_alphanumeric()).collect();
                format!("{what} refused {kind}")
            }
        };
        *self.tally.entry(key).or_default() += 1;
    }

    /// An action that found nothing to do, counted by why.
    fn skip(&mut self, why: &str) -> Result<(), String> {
        *self.tally.entry(why.to_owned()).or_default() += 1;
        Ok(())
    }

    fn mark(&mut self) -> String {
        self.written += 1;
        format!("w{}s{}", self.written, self.step)
    }

    fn act(&mut self, action: &Action) -> Result<(), String> {
        match *action {
            Action::Edit { replica, file, how } => {
                self.edit(replica, file, how);
                Ok(())
            }
            Action::Record {
                replica,
                head,
                edits,
            } => {
                let mut rng = Rng(edits);
                for _ in 0..1 + rng.below(3) {
                    let file = rng.below(FILES.len());
                    let how = rng.next();
                    self.edit(replica, file, how);
                }
                self.record(replica, head)
            }
            Action::Merge { replica } => self.merge(replica),
            Action::Amend { replica, head } => self.amend(replica, head),
            Action::Abandon {
                replica,
                pick,
                only,
            } => self.abandon(replica, pick, only),
            Action::Carry { replica } => self.carry(replica),
            Action::Forget {
                replica,
                head,
                file,
                span,
            } => self.forget(replica, head, file, span),
            Action::Prune { replica } => self.prune(replica),
            Action::Update { replica } => self.update(replica),
            Action::Publish { replica } => self.publish(replica),
            Action::Evict { replica } => self.evict(replica),
            Action::Sync {
                from,
                to,
                shuffle,
                torn,
                keep_times,
            } => {
                self.sync(from, to, shuffle, torn, keep_times);
                Ok(())
            }
        }
    }

    /// Whether writing to this replica's store is a fair thing to ask. One
    /// holding a file a sync cut short is broken in a way `check` names, and
    /// what a writer does with a broken store is not what is under test.
    fn writable(&self, at: usize) -> bool {
        self.replicas[at].torn.is_empty()
    }

    fn edit(&mut self, at: usize, file: usize, how: u64) {
        let name = FILES[file % FILES.len()];
        let path = Path::new(REPOSITORY).join(name);
        let disk = self.replicas[at].disk.clone();
        let held = disk.bytes(&path);
        let mut rng = Rng(how);
        if name.ends_with(".bin") {
            if held.is_some() && rng.chance(15) {
                disk.remove(&path);
            } else {
                let mark = self.mark();
                // A NUL makes it bytes to the sniff decision 0017 describes.
                let bytes = format!("\0photo {mark}\0").into_bytes();
                disk.put(&path, &bytes, None);
            }
            return;
        }
        let text = held
            .map(|bytes| String::from_utf8_lossy(&bytes).into_owned())
            .unwrap_or_default();
        let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
        match rng.below(10) {
            0 if !lines.is_empty() && rng.chance(25) => {
                disk.remove(&path);
                return;
            }
            1..=3 if !lines.is_empty() => {
                let first = rng.below(lines.len());
                let count = 1 + rng.below(2.min(lines.len() - first));
                lines.drain(first..first + count);
            }
            4..=5 if !lines.is_empty() => {
                let line = rng.below(lines.len());
                lines[line] = self.mark();
            }
            _ => {
                let line = rng.below(lines.len() + 1);
                for offset in 0..1 + rng.below(3) {
                    let mark = self.mark();
                    lines.insert(line + offset, mark);
                }
            }
        }
        let mut text = lines.join("\n");
        if !text.is_empty() {
            text.push('\n');
        }
        disk.put(&path, text.as_bytes(), None);
    }

    fn record(&mut self, at: usize, head: u64) -> Result<(), String> {
        if !self.writable(at) {
            return Ok(());
        }
        let mut store = self.open(at)?;
        let heads: Vec<RevisionId> = current_heads(&store).into_iter().collect();
        let parents = match heads.len() {
            0 => Vec::new(),
            n => vec![heads[head as usize % n]],
        };
        self.record_onto(at, &mut store, parents, "work", Vec::new(), BTreeSet::new())
    }

    fn record_onto(
        &mut self,
        at: usize,
        store: &mut SimStore,
        parents: Vec<RevisionId>,
        message: &str,
        placed: Vec<(FileId, String)>,
        accepted: BTreeSet<String>,
    ) -> Result<(), String> {
        let working = self.working(at, store)?;
        let recording = Recording {
            parents,
            author: AUTHOR.to_owned(),
            when: self.now(),
            message: format!("{message} {}", self.step),
            moves: Vec::new(),
            at: placed,
            accepted,
            only: Restriction::Everything,
            kinds: Default::default(),
            extensions: Default::default(),
        };
        // Refusals are a writer working: nothing to record, a folder that
        // disagrees with a merge. What this round is after is what a refusal
        // or a success leaves behind, which the checks after it look at.
        let outcome = record(store, &working, &recording, &mut self.replicas[at].minting);
        self.count(message, &outcome);
        working.remember();
        Ok(())
    }

    fn merge(&mut self, at: usize) -> Result<(), String> {
        if !self.writable(at) {
            return Ok(());
        }
        let mut store = self.open(at)?;
        let heads: Vec<RevisionId> = current_heads(&store).into_iter().collect();
        if heads.len() < 2 {
            return self.skip("merge: one head");
        }
        let Ok(merged) = store.merged_tree_of(&heads) else {
            return self.skip("merge: no tree");
        };
        // Two files claiming one path is settled by a person with `--at`
        // (decision 0012): one keeps the path, and each other is placed
        // beside it, as the command line's `merge` suggests.
        let mut beside: BTreeMap<FileId, String> = BTreeMap::new();
        for contest in &merged.contested {
            if let TreeContest::Path { path, files } = contest {
                for (index, file) in files.iter().enumerate().skip(1) {
                    beside.insert(*file, format!("{path}.{index}"));
                }
            }
        }
        let disk = self.replicas[at].disk.clone();
        let mut laid = BTreeSet::new();
        // A photograph two sides disagree about is laid down from one side,
        // and a person recording that says so (decision 0028).
        let mut accepted = BTreeSet::new();
        for (file, entry) in merged.tree.entries() {
            let placed = beside.get(file).unwrap_or(&entry.path);
            let path = Path::new(REPOSITORY).join(placed);
            match entry.kind {
                FileKind::Lines => {
                    let Ok(content) = store.merged_content_of(&heads, file) else {
                        return self.skip("merge: no content");
                    };
                    // Every side kept: the union is a resolution a person
                    // may write, and the one that needs no judgement.
                    disk.put(&path, content.state.text().as_bytes(), None);
                }
                FileKind::Whole => {
                    // A contested photograph has no merge to lay down, so
                    // the person takes the side whose bytes sort first.
                    let payload = entry.payload.or_else(|| {
                        merged.contested.iter().find_map(|contest| match contest {
                            TreeContest::Content {
                                file: contested,
                                payloads,
                            } if contested == file => payloads.iter().map(|(_, side)| *side).min(),
                            _ => None,
                        })
                    });
                    let Some(payload) = payload else {
                        return self.skip("merge: contested bytes");
                    };
                    if entry.payload.is_none() {
                        accepted.insert(placed.clone());
                    }
                    let Ok(Some(bytes)) = store.payload(&payload) else {
                        return self.skip("merge: bytes not held");
                    };
                    disk.put(&path, &bytes, None);
                }
                _ => return self.skip("merge: a link"),
            }
            laid.insert(placed.clone());
        }
        // Whatever the merge does not hold leaves the folder, including a
        // file an earlier merge placed beside another.
        for (path, _, _) in disk.files_under(Path::new(REPOSITORY)) {
            let Ok(relative) = path.strip_prefix(REPOSITORY) else {
                continue;
            };
            if relative.starts_with("history") {
                continue;
            }
            if !laid.contains(&*relative.to_string_lossy()) {
                disk.remove(&path);
            }
        }
        let placed = beside.into_iter().collect();
        self.record_onto(at, &mut store, heads, "merge", placed, accepted)
    }

    fn amend(&mut self, at: usize, head: u64) -> Result<(), String> {
        if !self.writable(at) {
            return Ok(());
        }
        let mut store = self.open(at)?;
        let heads: Vec<RevisionId> = current_heads(&store).into_iter().collect();
        if heads.is_empty() {
            return Ok(());
        }
        let revision = heads[head as usize % heads.len()];
        let working = match standing_on(&store, &revision).is_empty() {
            true => self.working(at, &store)?,
            false => Working::unread_on(self.replicas[at].disk.clone(), Path::new(REPOSITORY)),
        };
        let amendment = Amendment {
            revision,
            message: Some(format!("amended {}", self.step)),
            reviser: AUTHOR.to_owned(),
            revised: self.now(),
            moves: Vec::new(),
        };
        let outcome = amend(
            &mut store,
            &working,
            &amendment,
            &mut self.replicas[at].minting,
        );
        self.count("amend", &outcome);
        Ok(())
    }

    fn abandon(&mut self, at: usize, pick: u64, only: bool) -> Result<(), String> {
        if !self.writable(at) {
            return Ok(());
        }
        let mut store = self.open(at)?;
        let revisions: Vec<RevisionId> = store.revisions().map(|(id, _)| *id).collect();
        if revisions.is_empty() {
            return Ok(());
        }
        let abandoning = Abandoning {
            revision: revisions[pick as usize % revisions.len()],
            only,
            author: AUTHOR.to_owned(),
            when: self.now(),
            message: format!("abandoned {}", self.step),
        };
        let outcome = abandon(&mut store, &abandoning, &mut self.replicas[at].minting);
        self.count("abandon", &outcome);
        Ok(())
    }

    fn carry(&mut self, at: usize) -> Result<(), String> {
        if !self.writable(at) {
            return Ok(());
        }
        let mut store = self.open(at)?;
        let outcome = carry(&mut store, &Carrying::Everything).map(|plan| plan.steps.len());
        if !matches!(outcome, Ok(0)) {
            self.count("carry", &outcome);
        }
        Ok(())
    }

    fn forget(&mut self, at: usize, head: u64, file: usize, span: u64) -> Result<(), String> {
        if !self.writable(at) {
            return Ok(());
        }
        let mut store = self.open(at)?;
        let heads: Vec<RevisionId> = current_heads(&store).into_iter().collect();
        if heads.is_empty() {
            return Ok(());
        }
        let revision = heads[head as usize % heads.len()];
        let Ok(tree) = store.tree(&revision) else {
            return Ok(());
        };
        let name = FILES[file % FILES.len()];
        let Some((id, entry)) = tree.entries().find(|(_, entry)| entry.path == name) else {
            return Ok(());
        };
        let id = *id;
        let (extent, items, payload, marks) = match entry.kind {
            FileKind::Lines => {
                let Ok(merged) = store.merged_content_of(&[revision], &id) else {
                    return Ok(());
                };
                let lines = merged.state.items();
                if lines.is_empty() {
                    return Ok(());
                }
                let mut rng = Rng(span);
                let first = rng.below(lines.len());
                let last = first + rng.below(2.min(lines.len() - first));
                let chosen = (first..=last).filter(|at| !lines[*at].forgotten);
                let items = chosen.clone().map(|at| merged.references[at]).collect();
                let marks = chosen.map(|at| lines[at].text.clone()).collect();
                (
                    Extent::Lines {
                        first: first + 1,
                        last: last + 1,
                    },
                    items,
                    None,
                    marks,
                )
            }
            FileKind::Whole => {
                let Some(payload) = entry.payload else {
                    return Ok(());
                };
                let marks = match store.payload(&payload) {
                    Ok(Some(bytes)) => vec![
                        String::from_utf8_lossy(&bytes)
                            .trim_matches('\0')
                            .to_owned(),
                    ],
                    _ => Vec::new(),
                };
                (Extent::Whole, BTreeSet::new(), Some(payload), marks)
            }
            _ => return Ok(()),
        };
        let forgetting = Forgetting {
            revision,
            file: id,
            extent,
        };
        let outcome = store.forget(&forgetting);
        self.count("forget", &outcome);
        let Ok(forgotten) = outcome else {
            return Ok(());
        };
        let stand_ins: BTreeSet<RevisionId> = forgotten
            .writes
            .iter()
            .map(|body| digest(&body.write()))
            .collect();
        // `forget` destroys the store's copies and leaves every folder
        // alone, so a folder still holding the lines records them again the
        // next time anything is recorded there — a person retyping them, as
        // far as the store can tell. The person this round models takes them
        // out of every folder they own, which is the only way the lines are
        // gone everywhere a later `record` can see.
        for replica in &self.replicas {
            scrub(&replica.disk, &marks);
        }
        if (!items.is_empty() || payload.is_some()) && !stand_ins.is_empty() {
            self.destroyed.push(Destroyed {
                items,
                payload,
                stand_ins,
                at: self.step,
            });
        }
        Ok(())
    }

    fn prune(&mut self, at: usize) -> Result<(), String> {
        if !self.writable(at) {
            return Ok(());
        }
        let mut store = self.open(at)?;
        let outcome = store.prune().map(|pruned| pruned.is_empty());
        if !matches!(outcome, Ok(true)) {
            self.count("prune", &outcome);
        }
        Ok(())
    }

    fn update(&mut self, at: usize) -> Result<(), String> {
        if !self.writable(at) {
            return Ok(());
        }
        let store = self.open(at)?;
        let heads: Vec<RevisionId> = current_heads(&store).into_iter().collect();
        let [head] = heads[..] else {
            return Ok(());
        };
        let working = self.working(at, &store)?;
        let repository = Path::new(REPOSITORY);
        // Refusals are the folder protecting work nothing recorded.
        let planned = historica::update::plan(&store, &working, repository, &head);
        self.count("update", &planned);
        if let Ok(update) = planned {
            let applied = historica::update::apply(&store, &working, repository, &update);
            self.count("update applied", &applied);
        }
        Ok(())
    }

    fn publish(&mut self, at: usize) -> Result<(), String> {
        if !self.writable(at) {
            return Ok(());
        }
        let store = self.open(at)?;
        let heads: Vec<RevisionId> = current_heads(&store).into_iter().collect();
        let [head] = heads[..] else {
            return Ok(());
        };
        let outcome = store.export_onto(self.server.clone(), Path::new(PUBLISHED), &head);
        self.count("publish", &outcome);
        if outcome.is_err() {
            return Ok(());
        }
        let copy = Store::open_on(self.server.clone(), Path::new(PUBLISHED).join("history"))
            .map_err(|error| format!("the published copy: {error}"))?;
        let offer = copy
            .offer("published")
            .map_err(|error| format!("offer: {error}"))?;
        self.server
            .put(Path::new(MANIFEST), offer.to_string().as_bytes(), None);
        Ok(())
    }

    fn evict(&mut self, at: usize) -> Result<(), String> {
        if !self.writable(at) || self.server.bytes(Path::new(MANIFEST)).is_none() {
            return Ok(());
        }
        let mut store = self.open(at)?;
        let mut payloads = BTreeSet::new();
        for head in current_heads(&store) {
            let Ok(tree) = store.tree(&head) else {
                return Ok(());
            };
            payloads.extend(tree.entries().filter_map(|(_, entry)| entry.payload));
        }
        // Only what the copy offers: asking to let go of anything else is a
        // refusal, and a round of those tests nothing.
        let listed = self.server.bytes(Path::new(MANIFEST)).unwrap_or_default();
        let Ok(offer) = historica::store::Offer::parse(&String::from_utf8_lossy(&listed)) else {
            return Ok(());
        };
        let offered: BTreeSet<RevisionId> = offer
            .of(historica::store::OfferKind::Payload)
            .map(|entry| entry.digest)
            .collect();
        payloads.retain(|payload| offered.contains(payload));
        if payloads.is_empty() {
            return Ok(());
        }
        let wanted: Vec<RevisionId> = payloads.iter().copied().collect();
        let source = Server(self.server.clone());
        let plan = store.eviction_plan(&source, "offer.txt", &wanted);
        self.count("evict", &plan);
        let Ok(plan) = plan else {
            return Ok(());
        };
        let working = self.working(at, &store)?;
        let Ok(folder) = historica::update::plan_eviction(&store, &working, &payloads) else {
            return Ok(());
        };
        let evicted = store.evict(&plan);
        self.count("evicted", &evicted);
        let _ = historica::update::apply(&store, &working, Path::new(REPOSITORY), &folder);
        Ok(())
    }

    /// Copy some of one store's files into another, as a sync does.
    ///
    /// Never deletes, and never overwrites an immutable file: same name and
    /// different bytes is a conflict a sync tool keeps both sides of, and
    /// this one keeps the receiving side's. The exceptions are the store's
    /// mutable files, which a sync carries like any other, and a file this
    /// sync's predecessor cut short, which a resuming copy finishes.
    fn sync(&mut self, from: usize, to: usize, shuffle: u64, torn: bool, keep_times: bool) {
        if from == to {
            return;
        }
        let mut rng = Rng(shuffle);
        // Whether it stops partway is drawn first, so that a pinned round
        // can say "everything" without depending on how many files there are.
        let partial = rng.below(4) == 0;
        let mut files = self.replicas[from].disk.files_under(Path::new(STORE));
        // Fisher–Yates, from the action's own stream.
        for at in (1..files.len()).rev() {
            files.swap(at, rng.below(at + 1));
        }
        let taken = match partial {
            true => rng.below(files.len() + 1),
            false => files.len(),
        };
        files.truncate(taken);
        *self.tally.entry("sync files".into()).or_default() += taken;
        let target = self.replicas[to].disk.clone();
        let last = files.len().checked_sub(1);
        for (index, (path, bytes, time)) in files.into_iter().enumerate() {
            let held = target.bytes(&path);
            let mutable = path.starts_with(Path::new(STORE).join("names"))
                || self.replicas[to].torn.contains(&path);
            match held {
                Some(held) if held == bytes => continue,
                Some(_) if !mutable => continue,
                _ => {}
            }
            let time = keep_times.then_some(time);
            if torn && Some(index) == last && bytes.len() > 1 {
                let cut = 1 + rng.below(bytes.len() - 1);
                target.put(&path, &bytes[..cut], time);
                self.replicas[to].torn.insert(path);
            } else {
                target.put(&path, &bytes, time);
                // A file cut short is cut short wherever it is copied to.
                match self.replicas[from].torn.contains(&path) {
                    true => self.replicas[to].torn.insert(path),
                    false => self.replicas[to].torn.remove(&path),
                };
            }
        }
    }
}

/// Take every line holding one of `marks` out of a folder, and any file of
/// bytes holding one.
fn scrub(disk: &Disk, marks: &[String]) {
    for name in FILES {
        let path = Path::new(REPOSITORY).join(name);
        let Some(bytes) = disk.bytes(&path) else {
            continue;
        };
        let text = String::from_utf8_lossy(&bytes);
        if !marks.iter().any(|mark| text.contains(mark.as_str())) {
            continue;
        }
        if name.ends_with(".bin") {
            disk.remove(&path);
            continue;
        }
        let kept: String = text
            .split_inclusive('\n')
            .filter(|line| !marks.iter().any(|mark| line.contains(mark.as_str())))
            .collect();
        disk.put(&path, kept.as_bytes(), None);
    }
}

/// Whether this history holds a merge whose agreement about a file is not
/// what its walk says: one that treated its parents as agreeing (stating a
/// delta, or nothing) where the walk does not find that agreed state, or one
/// that stated a resolution where its parents now read alike.
///
/// [The task](../docs/tasks/a-merge-agrees-by-text.md) this is the signature
/// of. Decision 0032's "parents agree" is decided by comparing states, and a
/// state compares by text: two replicas making one edit agree by text and
/// not by identity, and a forgetting makes states that differed compare
/// alike, or alike ones differ, depending on which stand-ins a replica holds.
/// The writer, the reader and `check`'s walk then answer differently, and
/// `check` reports the difference as corruption. Until that task is closed,
/// `ContentDisagrees`, `ResolvedWithoutDisagreement` and their kin in such a
/// history are it, and `HISTORICA_SIMULATION_STRICT` reports them anyway.
fn agreed_by_text(store: &SimStore) -> bool {
    for (_, revision) in store.revisions() {
        let parents: Vec<RevisionId> = revision.parents.iter().copied().collect();
        if parents.len() < 2 {
            continue;
        }
        let Ok(tree) = store.merged_tree_of(&parents) else {
            continue;
        };
        for (file, entry) in tree.tree.entries() {
            if entry.kind != FileKind::Lines {
                continue;
            }
            let states: Vec<_> = parents
                .iter()
                .filter_map(|parent| store.content_of(parent, file).ok().flatten())
                .collect();
            let forgotten = states
                .iter()
                .any(|state| state.items().iter().any(|item| item.forgotten));
            let alike = states.windows(2).all(|pair| pair[0] == pair[1]);
            let walked = store
                .merged_content_of(&parents, file)
                .map(|walked| walked.state);
            if forgotten
                || walked.is_ok_and(|walked| states.iter().any(|state| *state != walked)) && alike
            {
                return true;
            }
        }
    }
    false
}

/// Whether the only thing a cached reading says that a fresh one does not
/// is a photograph whose stand-in this replica holds somewhere other than
/// beside its copy of the bytes.
///
/// [The task](../docs/tasks/a-stand-in-filed-beside-another-copy.md) this is
/// the signature of: decision 0079's look beside a payload finds a stand-in
/// where the replica that forgot it filed it, and the same bytes filed by two
/// revisions sit at two paths, so a replica holding them at the other one
/// keeps handing them over through its cache. `HISTORICA_SIMULATION_STRICT`
/// reports it anyway.
fn beside_elsewhere(disk: &Disk, cached: &Answers, fresh: &Answers) -> bool {
    if strict() {
        return false;
    }
    let handed: BTreeSet<RevisionId> = cached
        .payloads
        .difference(&fresh.payloads)
        .copied()
        .collect();
    if handed.is_empty() || !fresh.payloads.is_subset(&cached.payloads) {
        return false;
    }
    let files = disk.files_under(&Path::new(STORE).join("operations"));
    let stand_ins: BTreeSet<PathBuf> = files
        .iter()
        .filter(|(_, bytes, _)| {
            historica::format::ForgottenPayload::parse(bytes)
                .is_ok_and(|stand_in| handed.contains(&stand_in.forgets))
        })
        .map(|(path, _, _)| path.clone())
        .collect();
    let elsewhere = files
        .iter()
        .filter(|(_, bytes, _)| handed.contains(&digest(bytes)))
        .any(|(path, _, _)| {
            let mut beside = path.clone().into_os_string();
            beside.push(".ops.txt");
            !stand_ins.contains(&PathBuf::from(beside))
        });
    // Everything else the two readings said has to agree.
    let shown_alike = cached.revisions.iter().zip(&fresh.revisions).all(|(a, b)| {
        a.0 == b.0
            && match (a.1, b.1) {
                (Ok(a), Ok(b)) => a.iter().zip(b).all(|(a, b)| {
                    a.0 == b.0 && a.1.0 == b.1.0 && (a.1.1 == b.1.1 || b.1.1.starts_with("absent "))
                }),
                (a, b) => a == b,
            }
    });
    elsewhere
        && shown_alike
        && cached.heads == fresh.heads
        && cached.items == fresh.items
        && cached.merged == fresh.merged
}

fn strict() -> bool {
    STRICT.with(std::cell::Cell::get) || std::env::var_os("HISTORICA_SIMULATION_STRICT").is_some()
}

thread_local! {
    /// Strictness for one test's thread, which a pinned counterexample sets
    /// without making every other test running beside it strict too.
    static STRICT: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// The heads a person works against: superseded ones set aside, unless that
/// leaves none. The command line's rule, restated rather than reached for,
/// since it lives in the binary.
fn current_heads(store: &SimStore) -> BTreeSet<RevisionId> {
    let history = store.history();
    let heads = history.heads();
    let superseded = history.superseded();
    let current: BTreeSet<RevisionId> = heads.difference(&superseded).copied().collect();
    if current.is_empty() { heads } else { current }
}

// ---------------------------------------------------------------------------
// What a replica says
// ---------------------------------------------------------------------------

/// Each file a tree holds, with its path and what a reader shows of it.
type Files = BTreeMap<FileId, (String, String)>;

/// An item's name (decision 0032): the document that minted it, and its
/// ordinal there.
type ItemName = (RevisionId, usize);

/// Everything a reader can be asked, in a form two stores can be compared by.
///
/// Errors are kept as their message: a store that cannot answer is an answer,
/// and two that cannot answer for different reasons disagree.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Answers {
    heads: BTreeSet<RevisionId>,
    /// Every revision's tree, and each file's content in it.
    revisions: BTreeMap<RevisionId, Result<Files, String>>,
    /// The merge of the current heads: each file's path and merged text.
    merged: Result<Files, String>,
    /// Every item of every file of lines at every revision, and at the merge
    /// of the current heads, by name, with whether it reads as forgotten.
    items: BTreeMap<String, Vec<(ItemName, bool)>>,
    /// Every payload whose bytes some reader handed over.
    payloads: BTreeSet<RevisionId>,
}

impl Answers {
    fn of(store: &SimStore) -> Self {
        let mut items = BTreeMap::new();
        let mut payloads = BTreeSet::new();
        let mut named = |label: String, heads: &[RevisionId], file: &FileId| {
            let listed = match store.merged_content_of(heads, file) {
                Ok(merged) => merged
                    .references
                    .iter()
                    .zip(merged.state.items())
                    .map(|(name, item)| (*name, item.forgotten))
                    .collect(),
                Err(_) => Vec::new(),
            };
            items.insert(label, listed);
        };

        let mut revisions = BTreeMap::new();
        for (id, _) in store.revisions() {
            let tree = store.tree(id).map_err(|error| format!("tree: {error}"));
            let tree = tree.map(|tree| {
                tree.entries()
                    .map(|(file, entry)| {
                        if entry.kind == FileKind::Lines {
                            named(format!("{id} {file}"), &[*id], file);
                        }
                        let shown = shown(store, id, file, &mut payloads);
                        (*file, (entry.path.clone(), shown))
                    })
                    .collect()
            });
            revisions.insert(*id, tree);
        }

        let current: Vec<RevisionId> = current_heads(store).into_iter().collect();
        let merged = match current.is_empty() {
            true => Ok(BTreeMap::new()),
            false => store
                .merged_tree_of(&current)
                .map_err(|error| format!("merged tree: {error}"))
                .map(|merged| {
                    merged
                        .tree
                        .entries()
                        .map(|(file, entry)| {
                            let text = match entry.kind {
                                FileKind::Lines => {
                                    named(format!("merged {file}"), &current, file);
                                    match store.merged_content_of(&current, file) {
                                        Ok(merged) => format!(
                                            "{} contested {}",
                                            merged.state.text(),
                                            merged.contested.len()
                                        ),
                                        Err(error) => format!("error: {error}"),
                                    }
                                }
                                _ => format!("{:?}", entry.payload),
                            };
                            (*file, (entry.path.clone(), text))
                        })
                        .collect()
                }),
        };
        Self {
            heads: store.history().heads(),
            revisions,
            merged,
            items,
            payloads,
        }
    }

    /// Whether a reader of this store shows anything `destroyed` destroyed.
    fn shows(&self, destroyed: &Destroyed) -> Option<String> {
        for (label, listed) in &self.items {
            for (name, forgotten) in listed {
                if !forgotten && destroyed.items.contains(name) {
                    return Some(format!("item {name:?} reads in full at {label}"));
                }
            }
        }
        let payload = destroyed.payload?;
        self.payloads
            .contains(&payload)
            .then(|| format!("payload {payload} is handed over"))
    }
}

/// What a reader prints for one file at one revision: its lines, or the
/// bytes of its payload, or why there are none.
fn shown(
    store: &SimStore,
    revision: &RevisionId,
    file: &FileId,
    payloads: &mut BTreeSet<RevisionId>,
) -> String {
    match store.content_at(revision, file) {
        Ok(content) => match (content.lines(), content.payload()) {
            (Some(state), _) => state.text(),
            (None, Some(payload)) => match store.payload(&payload) {
                Ok(Some(bytes)) => {
                    payloads.insert(payload);
                    String::from_utf8_lossy(&bytes).into_owned()
                }
                Ok(None) => format!("absent {payload}"),
                Err(error) => format!("error: {error}"),
            },
            (None, None) => "nothing".to_owned(),
        },
        Err(error) => format!("error: {error}"),
    }
}

/// The documents a replica holds, by digest — what "the same files" means
/// once a sync has had the freedom to put them anywhere.
fn holdings(disk: &Disk) -> BTreeSet<RevisionId> {
    let mut held = BTreeSet::new();
    for directory in ["revisions", "operations"] {
        for (_, bytes, _) in disk.files_under(&Path::new(STORE).join(directory)) {
            held.insert(digest(&bytes));
        }
    }
    held
}

// ---------------------------------------------------------------------------
// The invariants
// ---------------------------------------------------------------------------

impl World {
    /// Hold every replica to the invariants, re-reading only `touched`.
    ///
    /// A replica nothing happened to holds the files it held, so what it
    /// says is what it said; reading it again would only cost time. What it
    /// is compared against can change, so the comparisons run every time.
    fn checked(&mut self, touched: &[usize]) -> Result<(), String> {
        for &at in touched {
            self.seen[at] = self.read(at)?;
        }

        for (at, seen) in self.seen.iter().enumerate() {
            // Forgotten bytes stay forgotten where the forgetting arrived.
            let Some((held, answers)) = seen else {
                continue;
            };
            for destroyed in &self.destroyed {
                if !destroyed.stand_ins.is_subset(held) {
                    continue;
                }
                if let Some(shown) = answers.shows(destroyed) {
                    return Err(format!(
                        "replica {at}: what step {} forgot is shown again: {shown}",
                        destroyed.at
                    ));
                }
            }
        }

        // The same documents give the same answers.
        let seen: Vec<_> = self
            .seen
            .iter()
            .enumerate()
            .filter_map(|(at, seen)| seen.as_ref().map(|(held, answers)| (at, held, answers)))
            .collect();
        for (index, (at, held, answers)) in seen.iter().enumerate() {
            for (other_at, other_held, other) in &seen[index + 1..] {
                if held == other_held && answers != other {
                    return Err(format!(
                        "replicas {at} and {other_at} hold the same documents and disagree\n\
                         {at}: {answers:#?}\n{other_at}: {other:#?}"
                    ));
                }
            }
        }
        Ok(())
    }

    /// Write every replica out under `HISTORICA_SIMULATION_DUMP`, if it is
    /// set, so that a failure can be looked at with the command line.
    fn dump(&self) {
        if !DUMPING.load(std::sync::atomic::Ordering::Relaxed) {
            return;
        }
        let Some(base) = std::env::var_os("HISTORICA_SIMULATION_DUMP") else {
            return;
        };
        let _ = std::fs::remove_dir_all(&base);
        let base = PathBuf::from(base);
        for (at, replica) in self.replicas.iter().enumerate() {
            for (path, bytes, _) in replica.disk.files_under(Path::new("/")) {
                let relative = path.strip_prefix("/").expect("absolute");
                let target = base.join(format!("replica-{at}")).join(relative);
                if let Some(parent) = target.parent() {
                    std::fs::create_dir_all(parent).expect("a directory to dump into");
                }
                std::fs::write(&target, bytes).expect("a dumped file");
            }
            let torn: Vec<String> = replica
                .torn
                .iter()
                .map(|p| p.display().to_string())
                .collect();
            std::fs::write(base.join(format!("replica-{at}/torn.txt")), torn.join("\n"))
                .expect("the torn list");
        }
    }

    /// What one replica says, after holding it to `check` and to its cache.
    /// `None` for a replica holding a file a sync cut short, which `check`
    /// has to name and nothing else has to answer for.
    fn read(&self, at: usize) -> Result<Option<(BTreeSet<RevisionId>, Answers)>, String> {
        let replica = &self.replicas[at];
        let disk = replica.disk.clone();

        // `check`, which takes no cached answer of any kind.
        let report = Store::check_on(&disk, STORE);
        let mut known = None;
        for error in report.errors() {
            let said = error.to_string();
            if matches!(
                error,
                Finding::ContentDisagrees { .. }
                    | Finding::ResolvedWithoutDisagreement { .. }
                    | Finding::UnstatedMerge { .. }
            ) && !strict()
                && *known.get_or_insert_with(|| {
                    // Asked of the replica without the files a sync cut
                    // short, which keep a store from opening at all and
                    // are `check`'s to name, not this question's.
                    let whole = disk.without(&replica.torn);
                    Store::open_on(whole, STORE).is_ok_and(|store| agreed_by_text(&store))
                })
            {
                continue;
            }
            let named = replica.torn.iter().any(|path| {
                said.contains(&*path.file_name().unwrap_or_default().to_string_lossy())
            });
            if !named {
                return Err(format!("replica {at}: check reports {said}"));
            }
        }
        if !replica.torn.is_empty() {
            return Ok(None);
        }

        // A cache changes nothing but time.
        let cached = self.open(at).map(|store| Answers::of(&store))?;
        let fresh = Store::open_on(disk.clone(), STORE)
            .map(|store| Answers::of(&store))
            .map_err(|error| format!("replica {at}: open: {error}"))?;
        if cached != fresh && !beside_elsewhere(&disk, &cached, &fresh) {
            return Err(format!(
                "replica {at}: the cached store and a fresh one disagree\n\
                 cached: {cached:#?}\nfresh:  {fresh:#?}"
            ));
        }
        // And a second cached reading, now that the first has written its
        // catalogues back, says the same again.
        let again = self.open(at).map(|store| Answers::of(&store))?;
        if again != fresh && !beside_elsewhere(&disk, &again, &fresh) {
            return Err(format!(
                "replica {at}: a store read through the cache it just wrote disagrees\n\
                 cached: {again:#?}\nfresh:  {fresh:#?}"
            ));
        }
        Ok(Some((holdings(&disk), fresh)))
    }
}

// ---------------------------------------------------------------------------
// Running, shrinking, reporting
// ---------------------------------------------------------------------------

/// Whether a failing run writes its replicas out: only the last run of a
/// failing round, once shrinking has settled on it.
static DUMPING: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Run a round, checking after every action. The step that failed is part
/// of the failure, so a shrunk round still says where.
fn run(plan: &Plan, seed: u64) -> Result<(), String> {
    let world = play(plan, seed)?;
    if std::env::var_os("HISTORICA_SIMULATION_TALLY").is_some() {
        eprintln!("{:?}", world.tally);
    }
    Ok(())
}

/// Run a round and hand back the world it left, for a test that wants to
/// ask what an action did as well as whether every promise held.
fn play(plan: &Plan, seed: u64) -> Result<World, String> {
    let mut world = World::new(plan, seed);
    let everyone: Vec<usize> = (0..plan.replicas).collect();
    world
        .checked(&everyone)
        .map_err(|failure| format!("before anything: {failure}"))?;
    for (step, action) in plan.actions.iter().enumerate() {
        world.step = step + 1;
        world
            .act(action)
            .map_err(|failure| format!("step {step}, {action:?}: {failure}"))?;
        let touched = match action {
            Action::Sync { to, .. } => vec![*to],
            other => other.replicas(),
        };
        if let Err(failure) = world.checked(&touched) {
            world.dump();
            return Err(format!("after step {step}, {action:?}: {failure}"));
        }
    }
    Ok(world)
}

fn attempt(plan: &Plan, seed: u64) -> Result<(), String> {
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run(plan, seed)));
    outcome.unwrap_or_else(|panic| {
        let said = panic
            .downcast_ref::<&str>()
            .map(|said| (*said).to_owned())
            .or_else(|| panic.downcast_ref::<String>().cloned())
            .unwrap_or_else(|| "a panic that said nothing".to_owned());
        Err(format!("panicked: {said}"))
    })
}

/// Take actions out of a failing round, and replicas, while it still fails.
///
/// By hand, for `tests/conformance.rs`'s reason: removing an action is the
/// only shrink that keeps a round readable, and every action already means
/// something in any state.
fn shrink(plan: Plan, seed: u64) -> Plan {
    const CANDIDATES: usize = 400;
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let mut best = plan;
    let mut spent = 0;
    let mut improved = true;
    while improved && spent < CANDIDATES {
        improved = false;
        if best.replicas > 2 {
            for gone in (0..best.replicas).rev() {
                let candidate = best.without(gone);
                spent += 1;
                if attempt(&candidate, seed).is_err() {
                    best = candidate;
                    improved = true;
                    break;
                }
            }
        }
        let mut at = best.actions.len();
        while at > 0 && spent < CANDIDATES {
            at -= 1;
            let mut candidate = best.clone();
            candidate.actions.remove(at);
            spent += 1;
            if attempt(&candidate, seed).is_err() {
                best = candidate;
                improved = true;
            }
        }
    }
    std::panic::set_hook(hook);
    best
}

fn report(seed: u64, round: usize, plan: &Plan, failure: &str) -> String {
    let mut out =
        String::from("the simulation found a replica saying something it should not.\n\n");
    out.push_str("Reproduce with:\n");
    out.push_str(&format!(
        "    HISTORICA_SIMULATION_SEED=0x{seed:016x} cargo test --test simulation\n\n"
    ));
    out.push_str(&format!(
        "Round {round}, shrunk to {} replicas and {} actions, clocks {:?}:\n",
        plan.replicas,
        plan.actions.len(),
        plan.granularity
    ));
    for (step, action) in plan.actions.iter().enumerate() {
        out.push_str(&format!("  {step:>3}. {action:?}\n"));
    }
    out.push_str(&format!("\n{failure}\n"));
    out
}

/// The rounds of one seed, each drawn from its own stream so that a failing
/// round can be found again without running the ones before it.
#[test]
fn replicas_that_sync_by_copying_files_keep_every_promise() {
    let seed = seed();
    for round in 0..rounds() {
        let round_seed = seed ^ (round as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15);
        let plan = plan(&mut Rng(round_seed));
        if let Err(failure) = attempt(&plan, round_seed) {
            let smaller = shrink(plan, round_seed);
            DUMPING.store(true, std::sync::atomic::Ordering::Relaxed);
            let failure = attempt(&smaller, round_seed).err().unwrap_or(failure);
            panic!("{}", report(seed, round, &smaller, &failure));
        }
    }
}

/// The first thing this search found in `carry`, pinned.
///
/// One replica records work on the root while another amends the root
/// without changing it, so the amendment names the root's documents again,
/// byte for byte. Synced, the work stands on the withdrawn root and a merge
/// joins it to the amendment: every line of the root stands twice in the
/// merge's view, once from each, under one `(document, ordinal)` name, and
/// the resolution keeps both (decision 0032). `carry` then restated the
/// merge onto the amendment verbatim, where its past holds one element under
/// each name and the resolution keeps two — a revision `check` refuses and
/// no reader can materialise. Decision 0059's refusal of a merge above moved
/// content is what has to fire, and nothing moved but identity: the merge's
/// past names the root's documents twice before the carry and once after.
#[test]
fn carrying_a_merge_that_keeps_both_copies_of_a_rewrite_refuses() {
    let plan = Plan {
        replicas: 2,
        granularity: vec![1, 1],
        actions: vec![
            Action::Record {
                replica: 0,
                head: 0,
                edits: 1,
            },
            Action::Amend {
                replica: 1,
                head: 0,
            },
            Action::Sync {
                from: 0,
                to: 1,
                shuffle: 1,
                torn: false,
                keep_times: true,
            },
            Action::Merge { replica: 1 },
            Action::Carry { replica: 1 },
        ],
    };
    let world = play(&plan, SEED).unwrap_or_else(|failure| panic!("{failure}"));
    assert_eq!(world.tally.get("merge ok"), Some(&1), "{:?}", world.tally);
    assert_eq!(
        world.tally.get("carry refused MergeAboveMovedContent"),
        Some(&1),
        "{:?}",
        world.tally
    );
}

/// [A stand-in filed beside another copy](../docs/tasks/a-stand-in-filed-beside-another-copy.md),
/// pinned: the same photograph filed by two revisions, forgotten beside one
/// copy, and handed over through the cache of a replica holding the other.
/// Ignored until that task is done; it is the task's done state.
#[test]
#[ignore = "docs/tasks/a-stand-in-filed-beside-another-copy.md"]
fn a_stand_in_beside_one_copy_is_read_beside_every_other() {
    STRICT.with(|strict| strict.set(true));
    let everything = |from, to| Action::Sync {
        from,
        to,
        shuffle: 1,
        torn: false,
        keep_times: true,
    };
    let plan = Plan {
        replicas: 2,
        granularity: vec![1, 1],
        actions: vec![
            Action::Abandon {
                replica: 0,
                pick: 0,
                only: false,
            },
            Action::Prune { replica: 0 },
            Action::Record {
                replica: 0,
                head: 0,
                edits: 3,
            },
            Action::Forget {
                replica: 0,
                head: 0,
                file: 3,
                span: 0,
            },
            everything(0, 1),
        ],
    };
    if let Err(failure) = play(&plan, SEED) {
        panic!("{failure}");
    }
}
