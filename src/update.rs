//! Making the folder hold the tree at a head.
//!
//! Decision 0030: the store can move ahead of the folder — a receive brings
//! work in, a merge is recorded, a run is abandoned — and the folder catches
//! up. [`plan`] works out what that takes and [`apply`] does it, a pair on
//! decision 0025's promise: the plan is what gets done, so a dry run and the
//! real thing cannot name different files.
//!
//! Two rules carry the whole module. The target is a current head, which is
//! what lets the tool keep needing no stored position: nothing other than a
//! head is ever put in the folder, so the folder as it stands and the store as
//! it stands remain the only two things there are. And an update replaces only
//! bytes some revision records — anywhere in the store, superseded and
//! abandoned revisions included — so it never destroys the only copy of
//! anything. A file holding unrecorded bytes at a path the target holds
//! refuses the whole update; at a path the target does not hold, it is left
//! exactly where it is.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::io;
use std::path::{Path, PathBuf};

use crate::core::{FileId, RevisionId};
use crate::fs::{Filesystem, Kind as OnDisk};
use crate::store::{MaterialiseError, STORE_DIR, Store, StoreError};
use crate::tree::Kind;
use crate::working::{Working, WorkingError};

/// One file the update writes: the bytes the target records for a path, and
/// what the plan saw on disk there, so that applying can look again.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Write {
    /// Where the file sits, relative to the repository root.
    pub path: String,
    /// The bytes the target records — exactly what `cat` prints.
    pub bytes: Vec<u8>,
    /// What the plan found at the path: recorded bytes to replace, or nothing.
    pub replaces: Option<Vec<u8>>,
}

/// One file the update removes: a path the target does not hold, whose bytes
/// some revision records.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Remove {
    /// Where the file sits, relative to the repository root.
    pub path: String,
    /// The recorded bytes the plan saw there, so that applying can look again.
    pub held: Vec<u8>,
}

/// What one update would do, computed before anything is done.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Update {
    /// The files to write, in path order.
    pub writes: Vec<Write>,
    /// The files to remove, in path order.
    pub removes: Vec<Remove>,
    /// Paths already holding exactly what the target records.
    pub kept: Vec<String>,
    /// Paths left alone, with the reason: a tracked file the target does not
    /// hold, whose bytes no revision records. Not a refusal — the file simply
    /// stays, and the next survey reports it as `added`.
    pub leaves: Vec<(String, String)>,
}

impl Update {
    /// Whether there is nothing to do: the folder already holds the target.
    pub fn is_settled(&self) -> bool {
        self.writes.is_empty() && self.removes.is_empty()
    }
}

/// What applying a plan did, which may be less than the plan intended: each
/// destination is looked at once more immediately before it is touched, and a
/// file that changed in between is left alone and reported rather than
/// overwritten.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Applied {
    /// The paths written.
    pub wrote: Vec<String>,
    /// The paths removed.
    pub removed: Vec<String>,
    /// Paths left alone at apply time, with the reason.
    pub left: Vec<(String, String)>,
    /// Paths whose read-back did not hold the bytes just written: the folder
    /// folded two of the tree's paths onto one file, per decision 0027, and
    /// cannot represent this tree.
    pub folded: Vec<String>,
}

/// Why an update could not be planned or performed.
#[derive(Debug)]
#[non_exhaustive]
pub enum UpdateError {
    /// The store holds no revisions, so there is nothing to hold the folder to.
    NothingRecorded,
    /// The target is not a current head, and the folder only ever holds one.
    NotAHead {
        /// The revision that was named.
        target: RevisionId,
        /// The heads the folder could hold instead.
        heads: Vec<RevisionId>,
    },
    /// The folder cannot take the tree whole, so nothing was written.
    ///
    /// Decision 0030 makes an update all or nothing: a folder that half-holds
    /// a head lies to the next `record`, which would observe every missing
    /// file as a fact. Each path is named with what stands in the way.
    Refused {
        /// Every path in the way, with the reason, in path order.
        paths: Vec<(String, String)>,
    },
    /// The target's tree or content could not be materialised.
    Materialise(Box<MaterialiseError>),
    /// The store could not be read.
    Store(StoreError),
    /// The folder could not be read.
    Working(WorkingError),
    /// A file could not be read or written, which is not knowing rather than
    /// a fact about the folder.
    Io {
        /// The path the operation was addressed to.
        path: PathBuf,
        /// What the filesystem said.
        error: io::Error,
    },
}

impl fmt::Display for UpdateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UpdateError::NothingRecorded => {
                write!(
                    f,
                    "nothing is recorded here yet, so there is nothing for the folder to hold"
                )
            }
            UpdateError::NotAHead { target, heads } => {
                write!(
                    f,
                    "{} is not a head, and the folder only ever holds one; \
                     reading the past is `show` and `cat`, and going back is `abandon`",
                    target.abbreviate(12)
                )?;
                for head in heads {
                    write!(f, "\n  {}", head.abbreviate(12))?;
                }
                Ok(())
            }
            UpdateError::Refused { paths } => {
                write!(
                    f,
                    "the folder cannot take this tree whole, so nothing was written:"
                )?;
                for (path, because) in paths {
                    write!(f, "\n  {path}: {because}")?;
                }
                Ok(())
            }
            UpdateError::Materialise(error) => error.fmt(f),
            UpdateError::Store(error) => error.fmt(f),
            UpdateError::Working(error) => error.fmt(f),
            UpdateError::Io { path, error } => write!(f, "{}: {error}", path.display()),
        }
    }
}

impl std::error::Error for UpdateError {}

impl From<StoreError> for UpdateError {
    fn from(error: StoreError) -> Self {
        UpdateError::Store(error)
    }
}

impl From<WorkingError> for UpdateError {
    fn from(error: WorkingError) -> Self {
        UpdateError::Working(error)
    }
}

impl From<MaterialiseError> for UpdateError {
    fn from(error: MaterialiseError) -> Self {
        UpdateError::Materialise(Box::new(error))
    }
}

/// The reason a path in the way refuses, spelled once: `merge` says the same
/// words when it declines to overwrite.
const UNRECORDED: &str = "it holds work nothing has recorded";

/// What one update would do, or why it cannot happen whole.
///
/// `repository` is the directory holding the store — the folder itself. The
/// target must be a current head: decision 0030's position answer is that the
/// folder is only ever given one, which is what keeps `record` and `status`
/// able to derive their positions instead of storing them.
pub fn plan<F: Filesystem>(
    store: &Store<F>,
    working: &Working<F>,
    repository: &Path,
    target: &RevisionId,
) -> Result<Update, UpdateError> {
    if store.is_empty() {
        return Err(UpdateError::NothingRecorded);
    }
    let history = store.history();
    let heads = history.heads();
    let superseded = history.superseded();
    let mut current: BTreeSet<RevisionId> = heads.difference(&superseded).copied().collect();
    if current.is_empty() {
        current = heads;
    }
    if !current.contains(target) {
        return Err(UpdateError::NotAHead {
            target: *target,
            heads: current.into_iter().collect(),
        });
    }

    let tree = store.tree(target)?;

    // The tree by path, with every file that claims each one: a merge can
    // legitimately record two, and a folder's truth can hold at most one.
    let mut placed: BTreeMap<&str, Vec<&FileId>> = BTreeMap::new();
    for (file, entry) in tree.entries() {
        placed.entry(entry.path.as_str()).or_default().push(file);
    }

    let store_prefix = format!("{STORE_DIR}/");
    let mut refused: Vec<(String, String)> = Vec::new();
    let mut refuse = |path: &str, because: String| {
        refused.push((path.to_owned(), because));
    };

    // Refusals the tree itself states, before the folder is consulted.
    let mut directories: BTreeSet<&str> = BTreeSet::new();
    for path in placed.keys() {
        let mut rest = *path;
        while let Some(index) = rest.rfind('/') {
            rest = &rest[..index];
            directories.insert(rest);
        }
    }
    for (path, files) in &placed {
        if files.len() > 1 {
            refuse(
                path,
                "two files hold this path; record the move that settles it first".to_owned(),
            );
        }
        if directories.contains(path) {
            refuse(
                path,
                "it is also a directory of another file here, and a folder cannot hold both"
                    .to_owned(),
            );
        }
        if *path == STORE_DIR || path.starts_with(&store_prefix) {
            refuse(
                path,
                "it would write a working file into the store".to_owned(),
            );
        }
        if store.skipped().skips(path) {
            refuse(
                path,
                "a `skip` rule in history/skipped.txt covers it, so the walk could never offer it back"
                    .to_owned(),
            );
        }
    }

    // A path the walk itself refused — a symlink, a name that is not UTF-8 —
    // is something standing where the tree needs to write, or a directory the
    // tree needs to write beneath.
    for (path, because) in working.refused() {
        let beneath = format!("{path}/");
        for held in placed.keys() {
            if *held == path.as_str() || held.starts_with(&beneath) {
                refuse(
                    held,
                    format!("the folder cannot offer what stands at {path}: {because}"),
                );
            }
        }
    }

    let recorded = RecordedBytes::over(store);
    let mut update = Update::default();

    for (path, files) in &placed {
        let [file] = files.as_slice() else {
            continue; // Already refused above: two files hold the path.
        };
        let entry = tree.entry(file).expect("the tree placed this file");
        let bytes = match entry.kind {
            Kind::Whole => match &entry.payload {
                None => {
                    refuse(
                        path,
                        "concurrent revisions each state its whole content, and neither is a winner"
                            .to_owned(),
                    );
                    continue;
                }
                Some(digest) => match store.payload(digest)? {
                    Some(bytes) => bytes,
                    None if !store.forgetting(digest).is_empty() => {
                        refuse(
                            path,
                            format!(
                                "its content {digest} was forgotten; record the `drop` that makes that true"
                            ),
                        );
                        continue;
                    }
                    None => {
                        refuse(
                            path,
                            format!(
                                "this store does not hold the content {digest}; receive the rest first"
                            ),
                        );
                        continue;
                    }
                },
            },
            Kind::Lines => match store.content(target, file) {
                Ok(state) => state.text().into_bytes(),
                Err(error) => {
                    refuse(path, error.to_string());
                    continue;
                }
            },
        };

        if working.holds(path) {
            let held = working.bytes(path)?;
            if held == bytes {
                update.kept.push((*path).to_owned());
            } else if recorded.holds(path, &held) {
                update.writes.push(Write {
                    path: (*path).to_owned(),
                    bytes,
                    replaces: Some(held),
                });
            } else {
                refuse(path, UNRECORDED.to_owned());
            }
        } else {
            let on_disk = repository.join(path);
            match look(working.filesystem(), &on_disk)? {
                None => update.writes.push(Write {
                    path: (*path).to_owned(),
                    bytes,
                    replaces: None,
                }),
                Some(OnDisk::Directory) => {
                    refuse(path, "a directory stands there".to_owned());
                }
                Some(OnDisk::Symlink) => {
                    refuse(path, "a symbolic link stands there".to_owned());
                }
                Some(_) => {
                    refuse(
                        path,
                        "something stands there the walk did not offer".to_owned(),
                    );
                }
            }
        }
    }

    // What the target does not hold: remove it where its bytes are recorded,
    // leave it where they are not. A tracked file left behind is said out
    // loud; a stray nobody has recorded coexists in silence, exactly as it
    // did before the update.
    let mut tracked: BTreeSet<String> = BTreeSet::new();
    for head in &current {
        for (_, entry) in store.tree(head)?.entries() {
            tracked.insert(entry.path.clone());
        }
    }
    for (path, _) in working.iter() {
        if placed.contains_key(path.as_str()) {
            continue;
        }
        let held = working.bytes(path)?;
        if recorded.holds(path, &held) {
            update.removes.push(Remove {
                path: path.clone(),
                held,
            });
        } else if tracked.contains(path) {
            update.leaves.push((path.clone(), UNRECORDED.to_owned()));
        }
    }

    if refused.is_empty() {
        Ok(update)
    } else {
        refused.sort();
        refused.dedup();
        Err(UpdateError::Refused { paths: refused })
    }
}

/// Perform a plan, looking at each destination once more immediately before
/// touching it. What comes back is what happened: a file that changed between
/// planning and acting is left alone and reported, per decision 0025, and a
/// written path is read back so that a folder folding two paths onto one file
/// — decision 0027's case — is discovered and named rather than silent.
pub fn apply<F: Filesystem>(
    working: &Working<F>,
    repository: &Path,
    update: &Update,
) -> Result<Applied, UpdateError> {
    let filesystem = working.filesystem();
    let mut applied = Applied::default();

    for remove in &update.removes {
        let on_disk = repository.join(&remove.path);
        match read(filesystem, &on_disk)? {
            Some(held) if held == remove.held => {
                filesystem
                    .remove_file(&on_disk)
                    .map_err(|error| UpdateError::Io {
                        path: on_disk.clone(),
                        error,
                    })?;
                applied.removed.push(remove.path.clone());
            }
            Some(_) => {
                applied.left.push((
                    remove.path.clone(),
                    "it changed underneath the update".to_owned(),
                ));
            }
            None => {} // Already gone, which is where a removal was headed.
        }
    }

    for write in &update.writes {
        let on_disk = repository.join(&write.path);
        if read(filesystem, &on_disk)? != write.replaces {
            applied.left.push((
                write.path.clone(),
                "it changed underneath the update".to_owned(),
            ));
            continue;
        }
        if let Some(directory) = on_disk.parent() {
            filesystem
                .create_directory(directory)
                .map_err(|error| UpdateError::Io {
                    path: directory.to_path_buf(),
                    error,
                })?;
        }
        filesystem
            .write(&on_disk, &write.bytes)
            .map_err(|error| UpdateError::Io {
                path: on_disk.clone(),
                error,
            })?;
        applied.wrote.push(write.path.clone());
    }

    // Read each written file back. Bytes that are not what was just written
    // mean the folder folded two of the tree's paths together — case, or
    // normalisation — and cannot represent this tree. Nothing unrecorded was
    // at risk in the discovery: every byte the fold clobbered is one this
    // update had just written from the store.
    for write in &update.writes {
        if !applied.wrote.contains(&write.path) {
            continue;
        }
        let on_disk = repository.join(&write.path);
        if read(filesystem, &on_disk)?.as_deref() != Some(write.bytes.as_slice()) {
            applied.folded.push(write.path.clone());
        }
    }

    // Tidy the directories the removals emptied, upwards until one refuses:
    // `remove_directory` failing on a directory that holds something is the
    // guard, not an error.
    for path in &applied.removed {
        let mut directory = repository.join(path);
        while directory.pop() && directory.as_path() != repository {
            if filesystem.remove_directory(&directory).is_err() {
                break;
            }
        }
    }

    Ok(applied)
}

/// Every byte sequence some revision records, asked path by path.
///
/// Decision 0030's overwrite rule, which is `merge`'s asked of the whole
/// store: what distinguishes "the folder is where I left it" from "the folder
/// holds something nobody has recorded". The candidates for a path are the
/// files any revision ever added or moved there, and a candidate's recorded
/// contents are materialised at each revision that touched it — including
/// merges, whose result is a state no single edit stated. Superseded and
/// abandoned revisions count, because whether bytes are recoverable is a fact
/// about the store's files, not about which tips of the graph are current;
/// after a `prune` deletes the documents, the bytes stop counting, and a
/// folder still holding them holds the last copy.
struct RecordedBytes<'a, F> {
    store: &'a Store<F>,
    ever_at: BTreeMap<&'a str, BTreeSet<FileId>>,
}

impl<'a, F: Filesystem> RecordedBytes<'a, F> {
    fn over(store: &'a Store<F>) -> Self {
        let mut ever_at: BTreeMap<&str, BTreeSet<FileId>> = BTreeMap::new();
        for (_, document) in store.iter() {
            for (file, path) in document.added.iter().chain(document.moved.iter()) {
                ever_at.entry(path.as_str()).or_default().insert(*file);
            }
        }
        Self { store, ever_at }
    }

    /// Whether some revision records exactly these bytes for a file that has
    /// held this path.
    fn holds(&self, path: &str, held: &[u8]) -> bool {
        let Some(files) = self.ever_at.get(path) else {
            return false;
        };
        files.iter().any(|file| {
            self.store.iter().any(|(id, document)| {
                let touches = document.added.contains_key(file)
                    || document.edited.contains_key(file)
                    || document.text.contains_key(file)
                    || document.bytes.contains_key(file)
                    || document.parents.len() > 1;
                touches
                    && self
                        .store
                        .content_at_heads(&[*id], file)
                        .is_ok_and(|content| content.bytes() == held)
            })
        })
    }
}

/// What is at a path, with absence as an answer rather than an error.
fn look<F: Filesystem>(filesystem: &F, path: &Path) -> Result<Option<OnDisk>, UpdateError> {
    filesystem.look(path).map_err(|error| UpdateError::Io {
        path: path.to_path_buf(),
        error,
    })
}

/// Every byte of a file, or `None` where there is none.
fn read<F: Filesystem>(filesystem: &F, path: &Path) -> Result<Option<Vec<u8>>, UpdateError> {
    match filesystem.read(path) {
        Ok(bytes) => Ok(Some(bytes)),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(error) => Err(UpdateError::Io {
            path: path.to_path_buf(),
            error,
        }),
    }
}
