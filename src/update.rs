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
use crate::format::{LinkTarget, Mode};
use crate::fs::{Filesystem, Kind as OnDisk};
use crate::store::{MaterialiseError, STORE_DIR, Store, StoreError};
use crate::tree::{Kind, Tree};
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
    /// The mode the target records.
    ///
    /// Stated by the plan and applied by [`apply`], which is where a
    /// filesystem with no such bit turns setting it into nothing. Asking here
    /// would mean asking about a path that does not exist yet.
    pub mode: Mode,
}

/// One file whose bytes are already what the target records and whose mode is
/// not.
///
/// Decision 0034 puts this inside 0030's promise rather than beside it: the
/// mode of a recorded file is recorded, so a folder holding the right bytes
/// with the wrong bit does not yet hold the head.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Chmod {
    /// Where the file sits, relative to the repository root.
    pub path: String,
    /// What the target records.
    pub mode: Mode,
}

/// One link the update makes: the target the tree records, spelled for a
/// folder, and what the plan found at the path.
///
/// Decision 0040: a `file:` target becomes the relative path from the link's
/// own directory to the target's *current* path, in the host's separators — so
/// the link follows its target through every rename, which is the point — and
/// a verbatim target becomes exactly its bytes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Linking {
    /// Where the link sits, relative to the repository root.
    pub path: String,
    /// What it will point at.
    pub target: String,
    /// What the plan found at the path, so that applying can look again.
    pub replaces: Stood,
}

/// What was at a path when the plan looked.
///
/// A link is not read as bytes and bytes are not read as a link, so what
/// applying compares against has to say which of the two it saw — decision
/// 0025's promise, held for a kind of entry that has no content.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stood {
    /// Nothing at all.
    Nothing,
    /// A link, pointing exactly here.
    Link(String),
    /// A regular file, holding these bytes — which some revision records, or
    /// the plan would have refused rather than planned to replace it.
    File(Vec<u8>),
}

/// One file the update removes: a path the target does not hold, whose bytes
/// some revision records.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Remove {
    /// Where the file sits, relative to the repository root.
    pub path: String,
    /// The recorded bytes the plan saw there, so that applying can look again.
    pub held: Vec<u8>,
    /// The link the plan saw there instead, where the path holds one.
    ///
    /// Decision 0040: what a link holds is a target, so this is what applying
    /// looks at again — reading the path itself would read through it.
    pub link: Option<String>,
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
    /// Files whose bytes are right and whose mode is not, in path order.
    pub modes: Vec<Chmod>,
    /// The links to make, in path order.
    pub links: Vec<Linking>,
    /// Paths left alone, with the reason: a tracked file the target does not
    /// hold, whose bytes no revision records. Not a refusal — the file simply
    /// stays, and the next survey reports it as `added`.
    pub leaves: Vec<(String, String)>,
}

impl Update {
    /// Whether there is nothing to do: the folder already holds the target.
    pub fn is_settled(&self) -> bool {
        self.writes.is_empty()
            && self.removes.is_empty()
            && self.modes.is_empty()
            && self.links.is_empty()
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
    /// Paths whose mode was set, with what it was set to.
    ///
    /// A deletion a person asked for in one word is printed, and so is this:
    /// making a file runnable is a change to a file in their folder.
    pub set: Vec<(String, Mode)>,
    /// The links made, with what each was pointed at.
    pub linked: Vec<(String, String)>,
}

/// Why an update could not be planned or performed.
#[derive(Debug)]
#[non_exhaustive]
pub enum UpdateError {
    /// The store holds no revisions, so there is nothing to hold the folder to.
    NothingRecorded,
    /// The directory a revision was to be laid out in already holds something.
    ///
    /// [`plan_into`]'s whole safety rule. An empty directory cannot afterwards
    /// be asked which of its files the target put there, and one that is not
    /// empty can be asked and cannot answer.
    NotEmpty {
        /// The directory.
        directory: PathBuf,
        /// What it holds.
        holds: Vec<PathBuf>,
    },
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
            UpdateError::NotEmpty { directory, holds } => {
                write!(
                    f,
                    "{} already holds {}; laying a revision out wants a \
                     directory holding nothing, because nothing afterwards \
                     could say which files it put there",
                    directory.display(),
                    holds
                        .iter()
                        .take(3)
                        .map(|path| path
                            .file_name()
                            .unwrap_or(path.as_os_str())
                            .to_string_lossy()
                            .into_owned())
                        .collect::<Vec<_>>()
                        .join(", ")
                )?;
                if holds.len() > 3 {
                    write!(f, " and {} more", holds.len() - 3)?;
                }
                Ok(())
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

/// What a folder with no links is told, and why it is told rather than
/// quietly given something else.
///
/// Decision 0040: writing a plain file holding the target invents content no
/// revision stated, which is what git's `core.symlinks=false` does and then
/// explains forever; skipping it silently leaves a folder half-holding a head,
/// which decision 0030 refuses.
const NO_LINKS: &str = "this folder cannot hold a symbolic link, and a plain file holding the target \
     would be content no revision stated";

/// How a folder spells one link's target, or `None` where the tree does not
/// hold the file a reference names.
///
/// Decision 0040's materialisation, in one place because three callers need
/// exactly it: the update that writes the link, the merge that lays the folder
/// out for `record --merge` to survey, and the check that asks whether a link
/// already on disk is one some revision recorded.
///
/// `at` is where the link sits, since a reference is spelled relative to the
/// link's own directory. The round trip is what this is for: recording what
/// this produced resolves to the same identity, and states nothing.
pub fn materialise(tree: &Tree, at: &str, target: &LinkTarget) -> Option<String> {
    match target {
        // Exactly its bytes: a person who spelled this said something about a
        // machine, and tidying it would change what the folder said.
        LinkTarget::Verbatim(spelling) => Some(spelling.clone()),
        LinkTarget::Reference(named) => Some(host_separators(&relative(
            directory_of(at),
            tree.path(named)?,
        ))),
    }
}

/// The directory part of a store path, empty at the root.
fn directory_of(path: &str) -> &str {
    path.rsplit_once('/').map_or("", |(directory, _)| directory)
}

/// The path from one directory to one file, both spelled as the store spells
/// them.
///
/// Decision 0040: this is what a `file:` target materialises as, so that the
/// link follows its target through every rename — the rename being a fact the
/// store recorded rather than a resemblance anything had to recover.
fn relative(from: &str, to: &str) -> String {
    let from: Vec<&str> = if from.is_empty() {
        Vec::new()
    } else {
        from.split('/').collect()
    };
    let to: Vec<&str> = to.split('/').collect();
    let shared = from
        .iter()
        .zip(&to)
        .take_while(|(here, there)| here == there)
        .count();
    let mut parts: Vec<&str> = vec![".."; from.len() - shared];
    parts.extend(&to[shared..]);
    if parts.is_empty() {
        return ".".to_owned();
    }
    parts.join("/")
}

/// A store path, in the separators the host writes.
///
/// Only a `file:` target passes through here: it is a store path being spelled
/// for a folder. A verbatim target is a string a person chose, and is written
/// as itself.
fn host_separators(spelling: &str) -> String {
    if std::path::MAIN_SEPARATOR == '/' {
        return spelling.to_owned();
    }
    spelling.replace('/', std::path::MAIN_SEPARATOR_STR)
}

/// The bytes of a regular file at a path, where some revision records them.
fn recorded_at<F: Filesystem, G: Filesystem>(
    working: &Working<G>,
    recorded: &RecordedBytes<'_, F>,
    path: &str,
) -> Result<Option<Vec<u8>>, UpdateError> {
    if !working.holds(path) || working.is_link(path) {
        return Ok(None);
    }
    let held = working.bytes(path)?;
    Ok(recorded.holds(path, &held).then_some(held))
}

/// Whether some revision recorded a link at this path pointing exactly here.
///
/// Decision 0030's overwrite rule asked of the one string a link holds instead
/// of bytes. A `file:` target is materialised at the revision that stated it,
/// because that is where the target's path was what it was — the same
/// arithmetic `update` does now, done then.
fn recorded_link<F: Filesystem>(
    store: &Store<F>,
    recorded: &RecordedBytes<'_, F>,
    path: &str,
    held: &str,
) -> Result<bool, UpdateError> {
    for file in recorded.files_at(path) {
        for (id, document) in store.iter() {
            let Some(target) = document.links.get(&file) else {
                continue;
            };
            let tree = store.tree(id)?;
            let Some(at) = tree.path(&file) else { continue };
            let Some(spelled) = materialise(&tree, at, target) else {
                continue;
            };
            if spelled == held {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

/// The heads a person is standing on: every head nothing supersedes, or every
/// head where a successor has not been delivered and filtering leaves nothing.
///
/// Decision 0023's rendering answer, which `plan` needs to say what the folder
/// may be given and `plan_at` needs to say which paths are tracked anywhere.
fn current_heads<F: Filesystem>(store: &Store<F>) -> BTreeSet<RevisionId> {
    let history = store.history();
    let heads = history.heads();
    let superseded = history.superseded();
    let current: BTreeSet<RevisionId> = heads.difference(&superseded).copied().collect();
    if current.is_empty() { heads } else { current }
}

/// What one update would do, or why it cannot happen whole.
///
/// `repository` is the directory holding the store — the folder itself. The
/// target must be a current head: decision 0030's position answer is that the
/// folder is only ever given one, which is what keeps `record` and `status`
/// able to derive their positions instead of storing them.
///
/// The store and the folder are two filesystems rather than one, because
/// decision 0042's export is exactly this pair pointed at a folder somewhere
/// else. `update` passes the same one twice and cannot tell.
pub fn plan<F: Filesystem, G: Filesystem>(
    store: &Store<F>,
    working: &Working<G>,
    repository: &Path,
    target: &RevisionId,
) -> Result<Update, UpdateError> {
    if store.is_empty() {
        return Err(UpdateError::NothingRecorded);
    }
    let current = current_heads(store);
    if !current.contains(target) {
        return Err(UpdateError::NotAHead {
            target: *target,
            heads: current.into_iter().collect(),
        });
    }

    plan_at(store, working, repository, target)
}

/// Lay the tree at any revision out in a directory that holds nothing.
///
/// Decision 0030 deferred this in as many words — "materialising a revision
/// into a directory elsewhere ... needs no position and no safety rule beyond
/// an empty destination, and it is export rather than checkout" — and left it
/// waiting for something to need it. What needs it is a caller building a
/// working tree of its own: `Working::read` takes any root and
/// [`crate::record::record`] takes the working copy as an argument, so a tool
/// can lay a past revision out somewhere, let a person work in it, and record
/// the result against that revision without the folder beside the store ever
/// moving.
///
/// This is not checkout and does not become it. 0030's refusal is about the
/// folder `record` and `status` derive their position from, which still only
/// ever holds a head; nothing here writes a position anywhere, and a caller
/// that keeps one keeps it about a directory it made itself. What makes the
/// difference safe is the emptiness rule: a directory holding nothing cannot
/// afterwards be asked which of its files came from the target and which were
/// already there, because there were none.
///
/// The plan it returns is [`plan`]'s, performed by the same [`apply`], so a
/// payload, a link and a mode are laid down the way `update` lays them down
/// rather than the way each caller would have guessed. Every refusal `plan`
/// states about the tree is stated here too, the `skip` rules included: a
/// caller reading that directory back through the origin's rules would not be
/// offered a file one covers, and would record its absence as a deletion.
pub fn plan_into<F: Filesystem, G: Filesystem>(
    store: &Store<F>,
    into: &Working<G>,
    directory: &Path,
    target: &RevisionId,
) -> Result<Update, UpdateError> {
    let holds = into
        .filesystem()
        .entries(directory)
        .map_err(|error| UpdateError::Io {
            path: directory.to_path_buf(),
            error,
        })?;
    if !holds.is_empty() {
        let mut names: Vec<PathBuf> = holds.into_iter().map(|entry| entry.path).collect();
        names.sort();
        return Err(UpdateError::NotEmpty {
            directory: directory.to_path_buf(),
            holds: names,
        });
    }

    plan_at(store, into, directory, target)
}

/// The plan itself, with no opinion about where the target sits in the history.
///
/// Both entry points above have already had theirs: [`plan`] that the target
/// is a current head, [`plan_into`] that the destination holds nothing.
fn plan_at<F: Filesystem, G: Filesystem>(
    store: &Store<F>,
    working: &Working<G>,
    repository: &Path,
    target: &RevisionId,
) -> Result<Update, UpdateError> {
    if store.is_empty() {
        return Err(UpdateError::NothingRecorded);
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

        // Decision 0040: a link is written as a link, and the two spellings
        // are materialised as themselves. This happens before the content
        // branch below because a link has no content to reach for.
        if entry.kind == Kind::Link {
            let Some(target) = entry.target.as_ref() else {
                refuse(path, "it is a link that names nowhere".to_owned());
                continue;
            };
            let Some(wanted) = materialise(&tree, path, target) else {
                // `tree::apply` and the merge both refuse a reference the tree
                // does not hold, so this is a store contradicting itself
                // rather than a state an update should invent a target for.
                refuse(path, "it names a file this tree does not hold".to_owned());
                continue;
            };
            let on_disk = working
                .get(path)
                .cloned()
                .unwrap_or_else(|| repository.join(path));
            // One question settles whether this folder has links at all, per
            // the contract in `Filesystem::link_target`: only the default
            // answers `Ok(None)`, and it answers it for every path.
            let held = match working.filesystem().link_target(&on_disk) {
                Ok(None) => {
                    refuse(path, NO_LINKS.to_owned());
                    continue;
                }
                Ok(some) => some,
                // Anything else is this filesystem saying the path holds no
                // link, which the look below is what decides what to do about.
                Err(_) => None,
            };
            match (held, look(working.filesystem(), &on_disk)?) {
                (Some(held), _) if held == wanted => update.kept.push((*path).to_owned()),
                (Some(held), _) => update.links.push(Linking {
                    path: (*path).to_owned(),
                    target: wanted,
                    replaces: Stood::Link(held),
                }),
                (None, None) => update.links.push(Linking {
                    path: (*path).to_owned(),
                    target: wanted,
                    replaces: Stood::Nothing,
                }),
                (None, Some(OnDisk::Directory)) => {
                    refuse(path, "a directory stands there".to_owned());
                }
                // A regular file where a link goes: replaced only where its
                // bytes are recorded, which is decision 0030's rule unchanged.
                (None, Some(_)) => match recorded_at(working, &recorded, path)? {
                    Some(bytes) => update.links.push(Linking {
                        path: (*path).to_owned(),
                        target: wanted,
                        replaces: Stood::File(bytes),
                    }),
                    None => refuse(path, UNRECORDED.to_owned()),
                },
            }
            continue;
        }

        // A link where the tree wants a file: nothing recorded the string it
        // holds, and reading it would read through it.
        if working.is_link(path) {
            refuse(path, "a symbolic link stands there".to_owned());
            continue;
        }

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
                    None if !store.forgetting(digest)?.is_empty() => {
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
            Kind::Link => unreachable!("a link was materialised above"),
        };

        if working.holds(path) {
            let held = working.bytes(path)?;
            let held_mode = working.executable(path)?.map(Mode::of);
            if held == bytes {
                match held_mode {
                    Some(mode) if mode != entry.mode => update.modes.push(Chmod {
                        path: (*path).to_owned(),
                        mode: entry.mode,
                    }),
                    _ => update.kept.push((*path).to_owned()),
                }
            } else if recorded.holds(path, &held) {
                update.writes.push(Write {
                    path: (*path).to_owned(),
                    bytes,
                    replaces: Some(held),
                    mode: entry.mode,
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
                    mode: entry.mode,
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
    if working.iter().next().is_some() {
        for head in &current_heads(store) {
            for (_, entry) in store.tree(head)?.entries() {
                tracked.insert(entry.path.clone());
            }
        }
    }
    for (path, _) in working.iter() {
        if placed.contains_key(path.as_str()) {
            continue;
        }
        // Decision 0040: a link the target does not hold goes only where some
        // revision recorded a link at that path pointing exactly there —
        // 0030's rule, asked of the one string a link holds instead of bytes.
        if let Some(held) = working.link_target(path) {
            if recorded_link(store, &recorded, path, held)? {
                update.removes.push(Remove {
                    path: path.clone(),
                    held: Vec::new(),
                    link: Some(held.to_owned()),
                });
            } else if tracked.contains(path) {
                update.leaves.push((path.clone(), UNRECORDED.to_owned()));
            }
            continue;
        }
        // A link this filesystem reports and cannot read is one whose string
        // nothing here can be sure of, so it stays where it is.
        if working.is_link(path) {
            update.leaves.push((path.clone(), UNRECORDED.to_owned()));
            continue;
        }
        let held = working.bytes(path)?;
        if recorded.holds(path, &held) {
            update.removes.push(Remove {
                path: path.clone(),
                held,
                link: None,
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

/// Set one file's mode, and say so only where the filesystem has one to set.
///
/// Decision 0034 asks after rather than before: a filesystem with no
/// executable bit turns the set into nothing, and reading the answer back is
/// how this tells that apart from having set it. Nothing is reported on a
/// filesystem that does not model modes, because nothing happened.
fn set_mode<F: Filesystem + ?Sized>(
    filesystem: &F,
    on_disk: &Path,
    mode: Mode,
    path: &str,
    applied: &mut Applied,
) -> Result<(), UpdateError> {
    let before = filesystem
        .executable(on_disk)
        .map_err(|error| UpdateError::Io {
            path: on_disk.to_path_buf(),
            error,
        })?;
    let Some(before) = before else {
        return Ok(());
    };
    if Mode::of(before) == mode {
        return Ok(());
    }
    filesystem
        .set_executable(on_disk, mode.is_executable())
        .map_err(|error| UpdateError::Io {
            path: on_disk.to_path_buf(),
            error,
        })?;
    applied.set.push((path.to_owned(), mode));
    Ok(())
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
    // Decision 0033: the tree spells a path in normal form C, and a folder may
    // spell the same name decomposed. Where the walk already found the file,
    // it is opened under the spelling the folder actually uses, so an update
    // rewrites that file rather than laying a second one beside it.
    let on_disk = |path: &String| {
        working
            .get(path)
            .cloned()
            .unwrap_or_else(|| repository.join(path))
    };

    for remove in &update.removes {
        let on_disk = on_disk(&remove.path);
        // Decision 0040: a link is looked at again as a link. `read` would
        // open what it points at, and compare the wrong thing about the wrong
        // file.
        if let Some(spelled) = &remove.link {
            match filesystem.link_target(&on_disk) {
                Ok(Some(held)) if &held == spelled => {
                    filesystem
                        .remove_file(&on_disk)
                        .map_err(|error| UpdateError::Io {
                            path: on_disk.clone(),
                            error,
                        })?;
                    applied.removed.push(remove.path.clone());
                }
                Ok(_) => applied.left.push((
                    remove.path.clone(),
                    "it changed underneath the update".to_owned(),
                )),
                // Gone, or no longer a link, which is where a removal was
                // headed or a change to look at again.
                Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                Err(_) => applied.left.push((
                    remove.path.clone(),
                    "it changed underneath the update".to_owned(),
                )),
            }
            continue;
        }
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
        let on_disk = on_disk(&write.path);
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
        set_mode(filesystem, &on_disk, write.mode, &write.path, &mut applied)?;
        applied.wrote.push(write.path.clone());
    }

    // Decision 0040: a link is made, never written through. Whatever stands
    // in the way is removed and the link put in its place, which is what
    // `set_link` promises and what keeps 0026's atomic-replace path — a path
    // that opens the destination — away from an entry whose destination is
    // somebody else's file.
    for link in &update.links {
        let on_disk = on_disk(&link.path);
        let now = match filesystem.link_target(&on_disk) {
            Ok(Some(held)) => Stood::Link(held),
            // Nothing, or something that is not a link: read it as what it is.
            _ => match read(filesystem, &on_disk)? {
                Some(bytes) => Stood::File(bytes),
                None => Stood::Nothing,
            },
        };
        if now != link.replaces {
            applied.left.push((
                link.path.clone(),
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
            .set_link(&on_disk, &link.target)
            .map_err(|error| UpdateError::Io {
                path: on_disk.clone(),
                error,
            })?;
        applied
            .linked
            .push((link.path.clone(), link.target.clone()));
    }

    // Decision 0034: the bytes were already right and the bit was not, so
    // this is the whole of what the folder was missing.
    for chmod in &update.modes {
        let on_disk = on_disk(&chmod.path);
        // A file that changed underneath the update is left alone here for the
        // reason it is left alone above: what comes back is what happened.
        if read(filesystem, &on_disk)?.is_none() {
            applied.left.push((
                chmod.path.clone(),
                "it went away underneath the update".to_owned(),
            ));
            continue;
        }
        set_mode(filesystem, &on_disk, chmod.mode, &chmod.path, &mut applied)?;
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
        let on_disk = on_disk(&write.path);
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

    /// Every file some revision ever put at this path.
    fn files_at(&self, path: &str) -> Vec<FileId> {
        self.ever_at
            .get(path)
            .map(|files| files.iter().copied().collect())
            .unwrap_or_default()
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
