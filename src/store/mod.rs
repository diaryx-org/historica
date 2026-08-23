//! The store: a directory of revision documents.
//!
//! Specified by `docs/decisions/0003-store.md` and completed by
//! `docs/decisions/0006-store-questions.md`. Decision 0025 makes the directory
//! one the caller supplies — a [`Store`] holds a [`crate::fs::Filesystem`] and
//! reads through it, and `std::fs` is what [`crate::fs::Disk`] is. One rule
//! governs everything here:
//!
//! > Identity comes from content. Filenames are presentation.
//!
//! Loading reads files and never their names, so renaming a revision breaks
//! nothing and an arranged store is as valid as a digest-named one. The
//! writer still names files by digest, because that default is self-verifying
//! and cannot conflict under any file sync — but nothing depends on it.
//!
//! ```text
//! history/
//! ├── historica.txt   # the version, and a note saying what this folder is
//! ├── revisions/      # one revision document per file, under any name
//! ├── operations/     # what each revision did, per file — decisions 0007, 0017
//! ├── names/          # bookmarks, `<name>.txt` — the only mutable files
//! ├── cache/          # derived, disposable, deletable without loss
//! └── skipped.txt     # what recording does not take
//! ```
//!
//! `operations/` holds two kinds of file, on the rule `revisions/` already
//! keeps: only a name ending `.ops.txt` is an operation document, and every
//! other file
//! is a payload — decision 0017's content that arrives whole, carrying no
//! format of its own and identified by the digest of its bytes. Payloads are
//! not read when a store is opened. A history with photographs in it must not
//! cost a full hash to run `log`, so the directory is indexed on first need
//! and `check` is where every payload is hashed deliberately.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fmt;
use std::io;
use std::path::{Path, PathBuf};

use crate::core::{ChangeId, FileId, History, RevisionId};
use crate::format::{
    self, Item, OperationDocument, ParseError, ResolutionDocument, RevisionDocument, Version,
    digest,
};
// `fs` here is `crate::fs`, never `std::fs` — this module reaches the folder
// only through the trait, and the qualified form is what keeps that visible.
use crate::fs::{self, Disk, Entry, Filesystem, read_to_string};
use crate::merge::{self, Merged};
use crate::replay::{self, ReplayError, State};
use crate::tree::{self, Kind, MergedTree, Tree, TreeError};
use crate::working::{MalformedSkip, Rule, SKIPPED_FILE, Skipped};

mod arrange;
mod check;
mod forget;
mod prune;
mod receive;

pub use arrange::{ArrangeError, Arranged, Arrangement, Filed, Occupied, Rename, Tally};
pub use check::{Finding, Report, Severity};
pub use forget::{ForgetError, Forgetting, Forgotten};
pub use prune::Pruned;
pub use receive::{MutableConflict, ReceiveError, ReceivePlan, Received};

/// The directory a store lives in, relative to the repository root.
pub const STORE_DIR: &str = "history";
/// The file that marks a directory as a store, and states its format version.
pub const HEADER_FILE: &str = "historica.txt";
/// Revision documents. Only `*.rev` files here are read as revisions.
pub const REVISIONS_DIR: &str = "revisions";
/// Operation documents, per decision 0007.
pub const OPERATIONS_DIR: &str = "operations";
/// Bookmarks: the only mutable files in a store.
pub const NAMES_DIR: &str = "names";
/// Derived, disposable, and deletable without loss.
pub const CACHE_DIR: &str = "cache";
/// The suffix a writer puts on a revision document.
///
/// Decision 0020: the claim that says which kind of document this is comes
/// first, and the claim that says it is text comes last, where an operating
/// system reads it.
pub const REVISION_SUFFIX: &str = ".rev.txt";
/// The suffix a writer puts on an operation document.
pub const OPERATION_SUFFIX: &str = ".ops.txt";
/// The suffix a bookmark file carries, per decision 0021.
///
/// A bookmark's name is its filename, now minus this: `names/main.txt` is the
/// bookmark `main`.
pub const NAME_SUFFIX: &str = ".txt";
/// Every suffix that is a file's claim to be a revision document.
///
/// One entry, which decision 0021 spent the format's one free moment to keep:
/// a payload has only this to avoid, so a repository file called `notes.ops`
/// keeps its own name.
pub const REVISION_SUFFIXES: [&str; 1] = [REVISION_SUFFIX];
/// Every suffix that is a file's claim to be an operation document.
pub const OPERATION_SUFFIXES: [&str; 1] = [OPERATION_SUFFIX];

/// The file `init` writes the readable format into.
///
/// Not hashed and referenced by nothing, exactly as [`HEADER_FILE`] is not.
/// A store whose claim is that it needs no tool should carry the description
/// of itself that makes the claim true, rather than leaving a person to find
/// it in a repository they may not have.
pub const FORMAT_FILE: &str = "format.txt";

/// What `init` writes into [`FORMAT_FILE`]: every grammar in this store, and
/// how to materialise a file from them by hand.
pub const FORMAT_NOTE: &str = include_str!("format.txt");

/// What `init` writes into [`HEADER_FILE`], below the version line.
///
/// Decision 0021: a person who opens `history/` should not have to be told
/// what they are looking at by somebody who already knows. Nothing hashes this
/// file and no document references it, so a reader takes the first line and
/// leaves the rest to whoever is reading.
pub const HEADER_NOTE: &str = "\
This folder is a Historica store: the recorded history of the files beside it.

Everything in it is text you can read, and none of it needs Historica to read.
Identity comes from content — a document is named by the SHA-256 of its own
bytes, which `shasum -a 256` prints — so a filename here is only ever
presentation. Renaming anything in this folder breaks nothing, and filing it
into directories of your own breaks nothing either.

  revisions/      one file per revision: who recorded what, when, and why, and
                  which revisions came before it, named by digest.
  operations/     what each revision did, filed under the revision that did it,
                  at the path the file had. A `.ops.txt` file lists the lines
                  that revision deleted and inserted; every other file there is
                  a file's own content, stored whole.
  names/          bookmarks, one line each. The only files here that change.
  cache/          derived and disposable. Deleting all of it loses nothing.
  skipped.txt     what recording does not take.
  format.txt      every grammar above, spelled out: what each line of each
                  document means, and how to materialise a file from them
                  with an editor and `shasum`. Read that one if you have no
                  Historica and want your files back.

The first line of this file states the format version. A reader that does not
know that version refuses the store rather than guessing at what it would be
leaving out.

`historica help` lists what the tool can do with all of this.
";

/// What `init` puts inside the disposable cache directory.
///
/// Decision 0027 puts the permission to delete a cache at the point where a
/// person is about to do it. The file is itself derived and disposable.
const CACHE_NOTE: &str = "\
Everything in this directory is derived from other files.
You may delete any or all of it; Historica will rebuild what it needs.
";

/// Names the store does not own, matched on a file's last component.
///
/// Decision 0022: 0018 gave payloads the names their files have, and a name is
/// a thing other writers use. A file browser writes `.DS_Store` into every
/// folder it displays and does not ask, which is how one of these overwrote a
/// payload the day the folder was first browsed. Inside the store such a file
/// is somebody else's; on the way in, a payload is never filed under one.
///
/// A blocklist, and it will need adding to. The failure modes are not
/// symmetrical: a name missing from it costs a payload, and a name on it that
/// need not be costs a digest suffix on one filename.
pub const PLATFORM_NAMES: [&str; 5] = [
    ".DS_Store",
    "Thumbs.db",
    "desktop.ini",
    ".localized",
    ".directory",
];
/// The prefix macOS puts on the file it writes beside every other file when a
/// folder is copied to a drive that cannot hold a resource fork.
pub const PLATFORM_PREFIX: &str = "._";

/// Whether a name is one the platform writes rather than one the store owns.
pub fn platform_name(name: &str) -> bool {
    PLATFORM_NAMES.contains(&name) || name.starts_with(PLATFORM_PREFIX)
}

/// Whether a path's last component is a name the store does not own.
fn platform_file(path: &Path) -> bool {
    path.file_name()
        .and_then(|name| name.to_str())
        .is_some_and(platform_name)
}

/// Whether a file's name claims it is one of this format's documents.
pub fn claims(path: &Path, suffixes: &[&str]) -> bool {
    let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
        return false;
    };
    suffixes.iter().any(|suffix| name.ends_with(suffix))
}

/// What a bookmark points at.
///
/// Decision 0006: one line, never two. `change` follows amend and rebase
/// automatically and is the default; `revision` is the exact pin for the rare
/// reference that must not move. Decision 0024 adds `file`, which has no
/// second key to choose between — a file identifier is minted once and
/// survives rename and amendment alike, so there is nothing for a pin to mean.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Name {
    /// Follows the change through every rewrite.
    Change(ChangeId),
    /// Pinned to one revision, which cannot move.
    Revision(RevisionId),
    /// One file, whatever it is called now.
    File(FileId),
}

impl Name {
    /// Parse the single line a bookmark file holds.
    ///
    /// A trailing newline is accepted. Unlike a revision document, a bookmark
    /// is not named by a digest of its bytes, so a second spelling here cannot
    /// create a second identity — the strictness that protects a revision
    /// would only be pedantry.
    pub fn parse(text: &str) -> Result<Self, MalformedName> {
        let line = text.strip_suffix('\n').unwrap_or(text);
        if line.contains('\n') {
            return Err(MalformedName);
        }
        let (key, value) = line.split_once(' ').ok_or(MalformedName)?;
        match key {
            "change" => value.parse().map(Name::Change).map_err(|_| MalformedName),
            "revision" => value.parse().map(Name::Revision).map_err(|_| MalformedName),
            "file" => value.parse().map(Name::File).map_err(|_| MalformedName),
            _ => Err(MalformedName),
        }
    }

    /// What kind of thing this bookmark names, as a person would say it.
    pub fn kind(&self) -> &'static str {
        match self {
            Name::Change(_) => "change",
            Name::Revision(_) => "revision",
            Name::File(_) => "file",
        }
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Name::Change(change) => write!(f, "change {change}"),
            Name::Revision(revision) => write!(f, "revision {revision}"),
            Name::File(file) => write!(f, "file {file}"),
        }
    }
}

/// A bookmark file was not one valid line.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MalformedName;

impl fmt::Display for MalformedName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "a bookmark is one line: `change` and a change ID, `revision` and a \
             digest, or `file` and a file identifier"
        )
    }
}

impl std::error::Error for MalformedName {}

/// What one revision's history says one file holds, under decision 0032's
/// recursive rule.
#[derive(Debug, Clone)]
enum Stated {
    /// The rule does not reach here: a merge whose parents disagree about the
    /// file and which states no resolution. The walk is what answers.
    Unstated,
    /// Nothing in this revision's past mentions the file at all — which is
    /// not the same as holding it empty, because a side that never saw a file
    /// disagrees with nobody about it.
    Absent,
    /// The file, stated.
    Known(State),
}

/// What several parents agree one file holds.
///
/// Decision 0032: "where the parents' states for a file are identical,
/// nothing is stated and the content is that state — the rule a reader can
/// check without any algorithm". A side that never saw the file is not a
/// side that disagrees, so it is dropped rather than counted as empty; if
/// what is left disagrees, the merge owed a resolution and this rule stops.
fn agreed<'a>(parents: impl IntoIterator<Item = &'a Stated>) -> Stated {
    let mut agreed: Option<&State> = None;
    for parent in parents {
        match parent {
            Stated::Unstated => return Stated::Unstated,
            Stated::Absent => continue,
            Stated::Known(state) => match agreed {
                None => agreed = Some(state),
                Some(held) if held == state => {}
                Some(_) => return Stated::Unstated,
            },
        }
    }
    match agreed {
        Some(state) => Stated::Known(state.clone()),
        None => Stated::Absent,
    }
}

/// The items one operation document mints, in document order.
fn minted_by(document: &OperationDocument) -> Vec<Item> {
    document
        .operations
        .iter()
        .filter(|operation| operation.kind == crate::format::OperationKind::Insert)
        .flat_map(|operation| operation.items.iter().cloned())
        .collect()
}

/// What one revision effectively stated about one file, and what named it.
///
/// Effective, in decision 0014's sense: redactions are folded in and a `text`
/// payload has already become the creation document 0017 makes it equivalent
/// to. The digest is the one the revision's own line carries, which is what a
/// `keep` quotes and what a person reads.
#[derive(Debug, Clone)]
pub(crate) enum Held {
    /// Decision 0007's operations, against the state at the parents.
    Operations(RevisionId, OperationDocument),
    /// Decision 0032's resolution: the file at this merge, stated whole.
    Resolution(RevisionId, ResolutionDocument),
}

impl Held {
    /// The event a merge walks, for a revision that stated this.
    pub(crate) fn event(&self, revision: RevisionId, parents: Vec<RevisionId>) -> merge::Event<'_> {
        match self {
            Held::Operations(named, document) => {
                merge::Event::operations(revision, parents, *named, document)
            }
            Held::Resolution(named, document) => {
                merge::Event::resolution(revision, parents, *named, document)
            }
        }
    }

    /// The operations, where that is what was stated.
    pub(crate) fn operations(&self) -> Option<&OperationDocument> {
        match self {
            Held::Operations(_, document) => Some(document),
            Held::Resolution(..) => None,
        }
    }
}

/// What a file holds, which depends on what kind of file it is.
///
/// Decision 0017: lines that merge, or one payload whole.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Content {
    /// A file of lines, as the operation chain leaves it.
    Lines(State),
    /// A file of bytes, exactly as its payload holds them.
    Whole(Vec<u8>),
}

impl Content {
    /// The file's bytes, whichever kind it is.
    pub fn bytes(&self) -> Vec<u8> {
        match self {
            Content::Lines(state) => state.text().into_bytes(),
            Content::Whole(bytes) => bytes.clone(),
        }
    }
}

/// A loaded store.
///
/// Holds documents rather than [`crate::core::Revision`]s, because the
/// documents are the authority and the graph is the projection — the same
/// relationship decision 0003 gives `cache/`.
///
/// The filesystem is a type parameter rather than a bound on the struct, so
/// that `Store` derives exactly what `F` supports: a `Store<Disk>` is `Debug`,
/// `Clone` and `Send` as it always was, and a store over a filesystem that is
/// none of those is none of those, without the trait having had to demand them
/// of anybody. Decision 0025.
#[derive(Debug, Clone)]
pub struct Store<F = Disk> {
    /// Where the folder is asked for. The store never reaches `std::fs`, it
    /// reaches whatever the caller handed it.
    files: F,
    root: PathBuf,
    /// The highest document version this store holds, which is what its
    /// header states and therefore the gate a reader is refused at.
    version: Version,
    documents: BTreeMap<RevisionId, RevisionDocument>,
    operations: BTreeMap<RevisionId, OperationDocument>,
    /// Decision 0032: a merge's file, stated whole by reference. Named by
    /// `edit` lines exactly as operation documents are, and told apart by
    /// their bodies.
    resolutions: BTreeMap<RevisionId, ResolutionDocument>,
    /// Where each payload sits, by digest. Built on first need, never at open.
    payloads: RefCell<Option<BTreeMap<RevisionId, PathBuf>>>,
    names: BTreeMap<String, Name>,
    skipped: Skipped,
}

/// The store's short constructors, which are the long ones on [`Disk`].
///
/// [`Disk`]: crate::fs::Disk
#[cfg(feature = "disk")]
impl Store<Disk> {
    /// Create an empty store at `root`, which must not already be one.
    pub fn init(root: impl AsRef<Path>) -> Result<Self, StoreError> {
        Self::init_on(Disk, root)
    }

    /// Open the store rooted at `root`.
    pub fn open(root: impl AsRef<Path>) -> Result<Self, StoreError> {
        Self::open_on(Disk, root)
    }

    /// Examine a store without loading it, reporting every fault at once.
    pub fn check(root: impl AsRef<Path>) -> Report {
        check::check(&Disk, root.as_ref())
    }

    /// Find the store containing `from`, walking up towards the filesystem root.
    ///
    /// A directory called `history` is not enough: it must hold a `historica`
    /// file, so an unrelated folder of the same name is not mistaken for one.
    ///
    /// Only on disk, and not because of the reading: `from` is canonicalised
    /// first, and "resolve this path against the process's current directory
    /// and the links along it" is a question about the machine the program is
    /// running on rather than about the folder. A host that supplies its own
    /// filesystem already knows where its store is, and calls
    /// [`Store::open_on`].
    pub fn discover(from: impl AsRef<Path>) -> Result<Self, StoreError> {
        let from = from.as_ref();
        let start = from
            .canonicalize()
            .map_err(|error| StoreError::io(from, error))?;
        for directory in start.ancestors() {
            let candidate = directory.join(STORE_DIR);
            if candidate.join(HEADER_FILE).is_file() {
                return Self::open(candidate);
            }
        }
        Err(StoreError::NotAStore { path: start })
    }
}

impl<F: Filesystem> Store<F> {
    /// Create an empty store at `root` on `files`, which must not already be one.
    pub fn init_on(files: F, root: impl AsRef<Path>) -> Result<Self, StoreError> {
        let root = root.as_ref().to_path_buf();
        let header = root.join(HEADER_FILE);
        if crate::fs::exists(&files, &header).map_err(|error| StoreError::io(&header, error))? {
            return Err(StoreError::AlreadyAStore { path: root });
        }
        for directory in [REVISIONS_DIR, OPERATIONS_DIR, NAMES_DIR, CACHE_DIR] {
            let path = root.join(directory);
            files
                .create_directory(&path)
                .map_err(|error| StoreError::io(&path, error))?;
        }
        // Version 1, not the reader's ceiling: the header states the highest
        // document version the store holds, an empty store holds nothing,
        // and version 1's vocabulary is everything short of forgetting.
        // `raise_version` moves it the day a newer document lands.
        files
            .write(
                &header,
                format!("{}\n\n{HEADER_NOTE}", Version::V1.preamble()).as_bytes(),
            )
            .map_err(|error| StoreError::io(&header, error))?;
        // Decision 0027: explain the syntax but state no rules. A host or
        // project that knows what its files mean owns every default.
        let skipped = root.join(SKIPPED_FILE);
        files
            .write(&skipped, crate::working::DEFAULT_SKIPPED.as_bytes())
            .map_err(|error| StoreError::io(&skipped, error))?;
        // A store that says it needs no tool carries the description that
        // makes that true, rather than pointing at a repository.
        let format = root.join(FORMAT_FILE);
        files
            .write(&format, FORMAT_NOTE.as_bytes())
            .map_err(|error| StoreError::io(&format, error))?;
        let cache_note = root.join(CACHE_DIR).join("README.txt");
        files
            .write(&cache_note, CACHE_NOTE.as_bytes())
            .map_err(|error| StoreError::io(&cache_note, error))?;
        Self::open_on(files, root)
    }

    /// Open the store rooted at `root` on `files`.
    ///
    /// A file that does not parse is an error naming the file, never a skip:
    /// strictness where the machine reads, exactly as in decision 0002. Use
    /// [`Store::check_on`] when the point is to enumerate every fault rather
    /// than to stop at the first.
    pub fn open_on(files: F, root: impl AsRef<Path>) -> Result<Self, StoreError> {
        let root = root.as_ref().to_path_buf();
        let version = read_version(&files, &root)?;

        let mut documents = BTreeMap::new();
        for path in files_claiming(&files, &root, REVISIONS_DIR, &REVISION_SUFFIXES)? {
            let bytes = files
                .read(&path)
                .map_err(|error| StoreError::io(&path, error))?;
            let document =
                RevisionDocument::parse(&bytes).map_err(|error| StoreError::Unparsable {
                    file: path.clone(),
                    error,
                })?;
            // Two files with identical bytes are one revision stored twice,
            // which is harmless. Identical digests with differing bytes cannot
            // happen, and if they ever did it would mean a broken read.
            documents.insert(digest(&bytes), document);
        }

        let mut operations = BTreeMap::new();
        let mut resolutions = BTreeMap::new();
        for path in files_claiming(&files, &root, OPERATIONS_DIR, &OPERATION_SUFFIXES)? {
            let bytes = files
                .read(&path)
                .map_err(|error| StoreError::io(&path, error))?;
            // Decision 0032: two content-document grammars share the suffix,
            // and the body says which one the bytes are held to.
            if format::is_resolution(&bytes) {
                let document =
                    ResolutionDocument::parse(&bytes).map_err(|error| StoreError::Unparsable {
                        file: path.clone(),
                        error,
                    })?;
                resolutions.insert(digest(&bytes), document);
            } else {
                let document =
                    OperationDocument::parse(&bytes).map_err(|error| StoreError::Unparsable {
                        file: path.clone(),
                        error,
                    })?;
                operations.insert(digest(&bytes), document);
            }
        }

        let mut names = BTreeMap::new();
        for (name, path) in name_files(&files, &root)? {
            let text =
                read_to_string(&files, &path).map_err(|error| StoreError::io(&path, error))?;
            let target =
                Name::parse(&text).map_err(|_| StoreError::MalformedName { file: path.clone() })?;
            names.insert(name, target);
        }

        let skipped = read_skipped(&files, &root)?;

        Ok(Self {
            files,
            root,
            version,
            documents,
            resolutions,
            operations,
            payloads: RefCell::new(None),
            names,
            skipped,
        })
    }

    /// Examine the store at `root` on `files`, reporting every fault at once.
    ///
    /// Errors mean the store cannot be trusted; notes are observations that
    /// never fail. See `docs/decisions/0006-store-questions.md`.
    pub fn check_on(files: &F, root: impl AsRef<Path>) -> Report {
        check::check(files, root.as_ref())
    }

    /// The directory this store occupies.
    pub fn root(&self) -> &Path {
        &self.root
    }

    /// The filesystem this store was opened on.
    ///
    /// Handed out so that a caller holding a store need not also hold what it
    /// was opened with — reading a payload's neighbours, or writing beside the
    /// folder, is done on the same filesystem or it is done somewhere else.
    pub fn filesystem(&self) -> &F {
        &self.files
    }

    /// How many distinct revisions the store holds.
    pub fn len(&self) -> usize {
        self.documents.len()
    }

    /// Whether the store holds no revisions.
    pub fn is_empty(&self) -> bool {
        self.documents.is_empty()
    }

    /// One document by digest.
    pub fn get(&self, id: &RevisionId) -> Option<&RevisionDocument> {
        self.documents.get(id)
    }

    /// Every document, in digest order.
    pub fn iter(&self) -> impl Iterator<Item = (&RevisionId, &RevisionDocument)> {
        self.documents.iter()
    }

    /// The causal graph these documents describe.
    ///
    /// Derived on demand: the documents are the authority, and this is the
    /// projection of them that answers graph questions.
    pub fn history(&self) -> History {
        let mut history = History::new();
        for document in self.documents.values() {
            // Keyed by digest, so no two documents can collide here.
            let _ = history.insert(document.to_revision());
        }
        history
    }

    /// One operation document by digest.
    pub fn operation(&self, id: &RevisionId) -> Option<&OperationDocument> {
        self.operations.get(id)
    }

    /// Every held forgetting document standing in for `target`.
    ///
    /// Decision 0014: a revision's `edit` line still names the destroyed
    /// digest, and a reader that cannot find it looks for a document that
    /// says it `forgets` it.
    pub fn forgetting(&self, target: &RevisionId) -> Vec<&OperationDocument> {
        self.operations
            .values()
            .filter(|document| document.forgets == Some(*target))
            .collect()
    }

    /// The document a reader consumes for one digest.
    ///
    /// The original where the store holds it, with decision 0014's union rule
    /// folded over every forgetting document that names it: an item is
    /// forgotten if any of them forgets it. `None` when the store holds
    /// neither the document nor anything standing in for it.
    pub fn effective_operation(&self, named: &RevisionId) -> Option<OperationDocument> {
        crate::format::stand_in(self.operations.get(named), &self.forgetting(named))
    }

    /// One resolution document, if the digest names one.
    ///
    /// Decision 0032: an `edit` line names either grammar, and this is how a
    /// caller asks which one it named.
    pub fn resolution(&self, named: &RevisionId) -> Option<&ResolutionDocument> {
        self.resolutions.get(named)
    }

    /// Every resolution document, in digest order.
    pub fn resolutions(&self) -> impl Iterator<Item = (&RevisionId, &ResolutionDocument)> {
        self.resolutions.iter()
    }

    /// Every operation document, in digest order.
    pub fn operations(&self) -> impl Iterator<Item = (&RevisionId, &OperationDocument)> {
        self.operations.iter()
    }

    /// The highest document version this store holds.
    pub fn version(&self) -> Version {
        self.version
    }

    /// One payload's bytes, or `None` if nothing has delivered it.
    ///
    /// Decision 0017: a payload carries no format of its own, so there is
    /// nothing to parse and nothing that can be malformed. The only claim it
    /// makes is its digest, and that claim is what finds it here.
    pub fn payload(&self, id: &RevisionId) -> Result<Option<Vec<u8>>, StoreError> {
        let Some(path) = self.payload_path(id)? else {
            return Ok(None);
        };
        let bytes = self
            .files
            .read(&path)
            .map_err(|error| StoreError::io(&path, error))?;
        Ok(Some(bytes))
    }

    /// Where every payload sits, by digest.
    ///
    /// Hashes the directory the first time it is asked and remembers the
    /// answer, so a command that never reads content never reads a payload.
    pub fn payloads(&self) -> Result<BTreeMap<RevisionId, PathBuf>, StoreError> {
        self.index_payloads()?;
        Ok(self
            .payloads
            .borrow()
            .as_ref()
            .expect("just indexed")
            .clone())
    }

    fn payload_path(&self, id: &RevisionId) -> Result<Option<PathBuf>, StoreError> {
        self.index_payloads()?;
        Ok(self
            .payloads
            .borrow()
            .as_ref()
            .expect("just indexed")
            .get(id)
            .cloned())
    }

    fn index_payloads(&self) -> Result<(), StoreError> {
        if self.payloads.borrow().is_some() {
            return Ok(());
        }
        let mut found: BTreeMap<RevisionId, PathBuf> = BTreeMap::new();
        // Sorted by `walk`, so two copies of one payload resolve to the same
        // path on every replica: the first one found keeps the entry.
        for path in payload_files(&self.files, &self.root)? {
            let bytes = self
                .files
                .read(&path)
                .map_err(|error| StoreError::io(&path, error))?;
            found.entry(digest(&bytes)).or_insert(path);
        }
        *self.payloads.borrow_mut() = Some(found);
        Ok(())
    }

    /// Every revision `head` descends from, itself included, each beside its
    /// digest.
    ///
    /// A DAG rather than a chain: merging is what decides the rest, and it
    /// needs the whole ancestry to know what is concurrent with what.
    ///
    /// The digest comes back with the document because the store already has
    /// it — a document is filed under the digest of the bytes it was read
    /// from, so returning the document alone would make every caller recompute
    /// what the map key already says, and
    /// [`RevisionDocument::id`](crate::format::RevisionDocument::id) costs a
    /// re-serialisation of the whole document.
    pub fn reachable(
        &self,
        head: &RevisionId,
    ) -> Result<Vec<(RevisionId, &RevisionDocument)>, MaterialiseError> {
        self.reachable_from(&[*head])
    }

    /// Every revision several heads descend from, itself included, each beside
    /// its digest.
    ///
    /// What merging two lines of work walks, before any revision joins them:
    /// decision 0012's `merge` asks this of a store to render a conflict that
    /// nothing has recorded yet.
    pub fn reachable_from(
        &self,
        heads: &[RevisionId],
    ) -> Result<Vec<(RevisionId, &RevisionDocument)>, MaterialiseError> {
        let mut seen = BTreeMap::new();
        let mut queue: Vec<RevisionId> = heads.to_vec();
        while let Some(id) = queue.pop() {
            if seen.contains_key(&id) {
                continue;
            }
            let document = self
                .documents
                .get(&id)
                .ok_or(MaterialiseError::Unknown { revision: id })?;
            seen.insert(id, document);
            for parent in &document.parents {
                if !self.documents.contains_key(parent) {
                    return Err(MaterialiseError::MissingParent {
                        parent: *parent,
                        named_by: id,
                    });
                }
                queue.push(*parent);
            }
        }
        Ok(seen.into_iter().collect())
    }

    /// The file set at `head`, and what was decided by rule deciding it.
    ///
    /// Decision 0008's concurrency rules, applied by [`crate::tree::merge`].
    pub fn merged_tree(&self, head: &RevisionId) -> Result<MergedTree, MaterialiseError> {
        self.merged_tree_of(&[*head])
    }

    /// The file set several heads leave between them.
    pub fn merged_tree_of(&self, heads: &[RevisionId]) -> Result<MergedTree, MaterialiseError> {
        let reachable = self.reachable_from(heads)?;
        let head = heads.first().copied().unwrap_or_else(|| {
            // A merge of nothing is the empty tree, and nothing names it.
            RevisionId::from_bytes([0; crate::core::REVISION_ID_LEN])
        });
        tree::merge(
            reachable
                .into_iter()
                .map(|(revision, document)| tree::Event { revision, document }),
        )
        .map_err(|error| MaterialiseError::Tree {
            revision: head,
            error,
        })
    }

    /// The file set at `head`.
    pub fn tree(&self, head: &RevisionId) -> Result<Tree, MaterialiseError> {
        Ok(self.merged_tree(head)?.tree)
    }

    /// One file at `head`, with the spans where concurrent work met.
    ///
    /// Decision 0007's merge, given the events this store holds. A history
    /// with no concurrency in it walks the same path and reports nothing.
    pub fn merged_content(
        &self,
        head: &RevisionId,
        file: &FileId,
    ) -> Result<Merged, MaterialiseError> {
        self.merged_content_of(&[*head], file)
    }

    /// One file as several heads leave it, with the spans where they met.
    pub fn merged_content_of(
        &self,
        heads: &[RevisionId],
        file: &FileId,
    ) -> Result<Merged, MaterialiseError> {
        let reachable = self.reachable_from(heads)?;
        let head = heads
            .first()
            .copied()
            .unwrap_or_else(|| RevisionId::from_bytes([0; crate::core::REVISION_ID_LEN]));

        let held = self.effective_for(&reachable, file)?;
        let mut events = Vec::with_capacity(reachable.len());
        for (revision, document) in reachable {
            let parents = document.parents.iter().copied().collect();
            events.push(match held.get(&revision) {
                Some(stated) => stated.event(revision, parents),
                None => merge::Event::nothing(revision, parents),
            });
        }
        merge::merge(events).map_err(|error| MaterialiseError::Merge {
            revision: head,
            file: *file,
            error: Box::new(error),
        })
    }

    /// The content of one file at `head`.
    ///
    /// A file the tree no longer holds still has content here, because
    /// dropping a file removes it from the file set and history is not a place
    /// things are removed from. Ask [`Store::tree`] whether it exists.
    ///
    /// Decision 0032 makes this one recursive rule with no algorithm in it:
    ///
    /// - a file created here is its payload;
    /// - a file edited on one line of history is the parent's state with the
    ///   document's operations applied — 0007's arithmetic;
    /// - a file at a merge whose parents agree is that agreed state;
    /// - a file at a merge whose parents differ is its resolution.
    ///
    /// Every step is one a person can do by hand and check by hand. The walk
    /// is what answers where the rule does not reach, which is every merge
    /// recorded before version 3: those read exactly as they did, forever.
    pub fn content(&self, head: &RevisionId, file: &FileId) -> Result<State, MaterialiseError> {
        Ok(self.content_of(head, file)?.unwrap_or_else(State::empty))
    }

    /// The content of one file at `head`, or `None` where that history
    /// mentions the file nowhere at all.
    ///
    /// The distinction decision 0032's merge rule turns on: a side that never
    /// saw a file is not a side that disagrees about it, so a merge owes no
    /// resolution for a file only one of its parents has ever heard of.
    pub fn content_of(
        &self,
        head: &RevisionId,
        file: &FileId,
    ) -> Result<Option<State>, MaterialiseError> {
        match self.stated_content(head, file)? {
            Stated::Known(state) => Ok(Some(state)),
            Stated::Absent => Ok(None),
            // Every merge recorded before version 3 lands here, and reads
            // exactly as it always did.
            Stated::Unstated => Ok(Some(self.merged_content(head, file)?.state)),
        }
    }

    /// The items one document mints, in document order.
    ///
    /// The run a `keep` counts into (decision 0032), whichever of the three
    /// things a digest can name here: a resolution's `insert` pieces, an
    /// operation document's inserts, or the lines of the payload a file
    /// arrived whole as. Redactions are folded in, because a `keep` of a
    /// forgotten item is a `keep` of the marker standing where it was.
    pub fn minted(&self, named: &RevisionId) -> Result<Option<Vec<Item>>, MaterialiseError> {
        if let Some(resolution) = self.resolutions.get(named) {
            return Ok(Some(
                resolution
                    .pieces
                    .iter()
                    .filter_map(|piece| match piece {
                        crate::format::Piece::Insert { items } => Some(items.iter().cloned()),
                        crate::format::Piece::Keep { .. } => None,
                    })
                    .flatten()
                    .collect(),
            ));
        }
        if let Some(document) = self.effective_operation(named) {
            return Ok(Some(minted_by(&document)));
        }
        // A digest naming neither is a payload's, or nothing at all.
        match self.creation_for(named, *named) {
            Ok(Some(creation)) => Ok(Some(minted_by(&creation))),
            Ok(None) => Ok(None),
            Err(MaterialiseError::MissingPayload { .. }) => Ok(None),
            Err(error) => Err(error),
        }
    }

    /// One file at `head` by decision 0032's rule, or `None` where the rule
    /// does not reach.
    ///
    /// It does not reach a merge whose parents disagree about the file and
    /// which states no resolution — which is every merge recorded before
    /// version 3, and nothing a version 3 writer produces.
    fn stated_content(&self, head: &RevisionId, file: &FileId) -> Result<Stated, MaterialiseError> {
        let mut known: BTreeMap<RevisionId, Stated> = BTreeMap::new();
        let mut stack = vec![*head];
        while let Some(id) = stack.last().copied() {
            if known.contains_key(&id) {
                stack.pop();
                continue;
            }
            let document = self
                .documents
                .get(&id)
                .ok_or(MaterialiseError::Unknown { revision: id })?;

            // A resolution is the file, stated: nothing before it is read,
            // which is the floor 0032 puts under materialising a long history.
            if let Some(named) = document.edited.get(file)
                && let Some(resolution) = self.resolutions.get(named)
            {
                let assembled = self.assemble(resolution, id, *file)?;
                known.insert(id, Stated::Known(assembled));
                stack.pop();
                continue;
            }

            let unknown: Vec<RevisionId> = document
                .parents
                .iter()
                .copied()
                .filter(|parent| !known.contains_key(parent))
                .collect();
            if !unknown.is_empty() {
                for parent in unknown {
                    if !self.documents.contains_key(&parent) {
                        return Err(MaterialiseError::MissingParent {
                            parent,
                            named_by: id,
                        });
                    }
                    stack.push(parent);
                }
                continue;
            }
            stack.pop();

            // A file created here is its payload, whatever the parents hold:
            // a creation is the first thing said about that identifier.
            if let Some(payload) = document.text.get(file) {
                let created = match self.creation_for(payload, id)? {
                    Some(creation) => State::empty().apply(&creation).map_err(|error| {
                        MaterialiseError::Content {
                            revision: id,
                            file: *file,
                            error,
                        }
                    })?,
                    None => State::empty(),
                };
                known.insert(id, Stated::Known(created));
                continue;
            }

            let base = agreed(document.parents.iter().map(|parent| &known[parent]));
            let stated = match document.edited.get(file) {
                Some(named) => match base {
                    Stated::Unstated => Stated::Unstated,
                    // A file nothing said anything about before is one whose
                    // operations are counted into an empty state.
                    base => {
                        let operations = self.effective_operation(named).ok_or(
                            MaterialiseError::MissingOperations {
                                document: *named,
                                named_by: id,
                            },
                        )?;
                        let before = match base {
                            Stated::Known(state) => state,
                            _ => State::empty(),
                        };
                        Stated::Known(before.apply(&operations).map_err(|error| {
                            MaterialiseError::Content {
                                revision: id,
                                file: *file,
                                error,
                            }
                        })?)
                    }
                },
                // A revision that says nothing about the file says what its
                // parents say, and a merge whose parents disagree says nothing
                // this rule can read.
                None => base,
            };
            known.insert(id, stated);
        }

        Ok(known.remove(head).unwrap_or(Stated::Unstated))
    }

    /// Assemble one resolution, fetching the documents its `keep` lines name.
    fn assemble(
        &self,
        resolution: &crate::format::ResolutionDocument,
        revision: RevisionId,
        file: FileId,
    ) -> Result<State, MaterialiseError> {
        // Gathered first, because the items are owned: a redacted document is
        // not the bytes the store holds, and a payload is not held as items
        // at all.
        let mut held: BTreeMap<RevisionId, Vec<Item>> = BTreeMap::new();
        for piece in &resolution.pieces {
            if let crate::format::Piece::Keep { document, .. } = piece
                && !held.contains_key(document)
                && let Some(items) = self.minted(document)?
            {
                held.insert(*document, items);
            }
        }
        replay::assemble(resolution, |document| held.get(document).map(Vec::as_slice)).map_err(
            |error| MaterialiseError::Content {
                revision,
                file,
                error,
            },
        )
    }

    /// What each of these revisions effectively stated about one file.
    ///
    /// Owned, because the merge may consume documents the store never held
    /// as bytes: a forgetting document changes what a stored document says
    /// (decision 0014), and a `text` payload is exactly the document that
    /// inserts every line at 0 (decision 0017) — and the merge never learns
    /// which spelling it was handed.
    ///
    /// The digest each one was named by travels with it, because decision
    /// 0032 lets a later revision quote an item as `(document, i)` and a
    /// redacted document's bytes are no longer the bytes its `edit` line
    /// named.
    pub(crate) fn effective_for(
        &self,
        documents: &[(RevisionId, &RevisionDocument)],
        file: &FileId,
    ) -> Result<BTreeMap<RevisionId, Held>, MaterialiseError> {
        let mut held: BTreeMap<RevisionId, Held> = BTreeMap::new();
        for &(revision, document) in documents {
            if let Some(named) = document.edited.get(file) {
                // Decision 0032: an `edit` line names either grammar, and
                // which one it named is a fact about the bytes in the store.
                if let Some(resolution) = self.resolutions.get(named) {
                    held.insert(revision, Held::Resolution(*named, resolution.clone()));
                    continue;
                }
                let effective =
                    self.effective_operation(named)
                        .ok_or(MaterialiseError::MissingOperations {
                            document: *named,
                            named_by: revision,
                        })?;
                held.insert(revision, Held::Operations(*named, effective));
            } else if let Some(payload) = document.text.get(file)
                && let Some(creation) = self.creation_for(payload, revision)?
            {
                held.insert(revision, Held::Operations(*payload, creation));
            }
        }
        Ok(held)
    }

    /// The creation document a `text` payload is equivalent to, redactions
    /// folded in.
    ///
    /// Decision 0014 meets 0017 here: a created file's lines are items too,
    /// so forgetting one destroys the payload and leaves a forgetting
    /// document naming its digest — the shape of the creation, minus the
    /// destroyed lines. A payload that is missing with nothing standing in
    /// for it is still [`MaterialiseError::MissingPayload`], because
    /// transport having more to deliver is ordinary and destruction is
    /// recorded.
    fn creation_for(
        &self,
        payload: &RevisionId,
        named_by: RevisionId,
    ) -> Result<Option<OperationDocument>, MaterialiseError> {
        let bytes = self
            .payload(payload)
            .map_err(|error| MaterialiseError::Unreadable {
                payload: *payload,
                because: error.to_string(),
            })?;
        let base = match bytes {
            Some(bytes) => {
                let text =
                    String::from_utf8(bytes).map_err(|_| MaterialiseError::PayloadNotText {
                        payload: *payload,
                        named_by,
                    })?;
                replay::creation(&text)
            }
            None => None,
        };
        let forgetting = self.forgetting(payload);
        if base.is_none() && forgetting.is_empty() {
            // An empty payload is never named (decision 0017), so a named
            // payload with no bytes and no stand-in is one nothing delivered.
            return Err(MaterialiseError::MissingPayload {
                payload: *payload,
                named_by,
            });
        }
        Ok(crate::format::stand_in(base.as_ref(), &forgetting))
    }

    /// What one file holds at `head`, whichever kind of file it is.
    ///
    /// Decision 0017: `cat` and `status` ask this, because the answer for a
    /// photograph is bytes and the answer for prose is lines, and which one it
    /// is was decided when the file was added.
    pub fn content_at(
        &self,
        head: &RevisionId,
        file: &FileId,
    ) -> Result<Content, MaterialiseError> {
        self.content_at_heads(&[*head], file)
    }

    /// What one file holds at several heads, whichever kind of file it is.
    pub fn content_at_heads(
        &self,
        heads: &[RevisionId],
        file: &FileId,
    ) -> Result<Content, MaterialiseError> {
        let merged = self.merged_tree_of(heads)?;
        let entry = merged
            .tree
            .entry(file)
            .ok_or(MaterialiseError::NoSuchFile { file: *file })?;
        match entry.kind {
            Kind::Lines => Ok(Content::Lines(self.merged_content_of(heads, file)?.state)),
            Kind::Whole => {
                let payload = entry
                    .payload
                    .ok_or(MaterialiseError::ContestedContent { file: *file })?;
                let named_by = heads.first().copied().unwrap_or(payload);
                let bytes = self
                    .payload(&payload)
                    .map_err(|error| MaterialiseError::Unreadable {
                        payload,
                        because: error.to_string(),
                    })?
                    .ok_or(MaterialiseError::MissingPayload { payload, named_by })?;
                Ok(Content::Whole(bytes))
            }
        }
    }

    /// What this repository's history does not take.
    ///
    /// Decision 0011: `history/skipped.txt` is a fact about the repository rather
    /// than about the person, so it lives here and travels with the store.
    pub fn skipped(&self) -> &Skipped {
        &self.skipped
    }

    /// Every bookmark, by name.
    pub fn names(&self) -> &BTreeMap<String, Name> {
        &self.names
    }

    /// What one bookmark points at, if it exists.
    pub fn name(&self, name: &str) -> Option<Name> {
        self.names.get(name).copied()
    }

    /// Write a revision into the store, named by its digest.
    ///
    /// Append-only: an existing file is never renamed or overwritten. Writing
    /// a revision the store already holds is therefore not an error but a
    /// no-op, which is what makes two replicas that deterministically produce
    /// one revision produce one file.
    pub fn insert(&mut self, document: &RevisionDocument) -> Result<RevisionId, StoreError> {
        let id = digest(&document.write());
        self.insert_at(document, &format!("{id}{REVISION_SUFFIX}"))
    }

    /// Write a revision into the store under `name`, within `revisions/`.
    ///
    /// Decision 0019: a writer names the file it is creating rather than
    /// renaming it afterwards, so the name comes from the caller — which is
    /// the one place that knows what the store already holds. `name` may
    /// carry `/`, and the directories it names are made.
    pub fn insert_at(
        &mut self,
        document: &RevisionDocument,
        name: &str,
    ) -> Result<RevisionId, StoreError> {
        let bytes = document.write();
        let id = digest(&bytes);
        let path = within(&self.root.join(REVISIONS_DIR), name);

        self.raise_version(document.version)?;
        write_once(&self.files, &path, &bytes)?;
        self.documents.insert(id, document.clone());
        Ok(id)
    }

    /// Write an operation document into the store, named by its digest.
    ///
    /// Append-only on the same terms as [`Store::insert`], and for the extra
    /// reason 0007 gives: two revisions that made byte-identical edits share
    /// one document, so writing one twice is ordinary rather than suspicious.
    pub fn insert_operation(
        &mut self,
        document: &OperationDocument,
    ) -> Result<RevisionId, StoreError> {
        let id = digest(&document.write());
        self.insert_operation_at(document, &format!("{id}{OPERATION_SUFFIX}"))
    }

    /// Write an operation document under `name`, within `operations/`.
    ///
    /// A document the store already holds is not written again, wherever it
    /// sits: 0016's rule that a document two revisions name lives under one of
    /// them, arrived at from the writing side.
    pub fn insert_operation_at(
        &mut self,
        document: &OperationDocument,
        name: &str,
    ) -> Result<RevisionId, StoreError> {
        let bytes = document.write();
        let id = digest(&bytes);
        if self.operations.contains_key(&id) {
            return Ok(id);
        }
        let path = within(&self.root.join(OPERATIONS_DIR), name);
        self.raise_version(document.version)?;
        write_once(&self.files, &path, &bytes)?;
        self.operations.insert(id, document.clone());
        Ok(id)
    }

    /// Write a resolution into the store under `name`, within `operations/`.
    ///
    /// Decision 0032 files a resolution exactly where an operation document
    /// goes and under the same suffix, because an `edit` line names either
    /// and a person reading the store should find the file beside the
    /// revision that wrote it either way.
    pub fn insert_resolution_at(
        &mut self,
        document: &ResolutionDocument,
        name: &str,
    ) -> Result<RevisionId, StoreError> {
        let bytes = document.write();
        let id = digest(&bytes);
        if self.resolutions.contains_key(&id) {
            return Ok(id);
        }
        let path = within(&self.root.join(OPERATIONS_DIR), name);
        self.raise_version(document.version)?;
        write_once(&self.files, &path, &bytes)?;
        self.resolutions.insert(id, document.clone());
        Ok(id)
    }

    /// Write a payload into the store, named by its digest.
    ///
    /// Append-only on [`Store::insert`]'s terms, and with more reason to be:
    /// two revisions that add byte-identical files share one payload, and a
    /// file added, dropped, and added again is the same bytes twice.
    ///
    /// No extension, because a payload's name is the one place the file's own
    /// name belongs and `arrange` is what puts it there.
    pub fn insert_payload(&mut self, bytes: &[u8]) -> Result<RevisionId, StoreError> {
        let id = digest(bytes);
        self.insert_payload_at(bytes, &id.to_string())
    }

    /// Write a payload under `name`, within `operations/`.
    ///
    /// A payload the store already holds is not written again, wherever it
    /// sits — which matters more here than for a document, since the same
    /// photograph added twice is the same megabytes twice.
    pub fn insert_payload_at(
        &mut self,
        bytes: &[u8],
        name: &str,
    ) -> Result<RevisionId, StoreError> {
        let id = digest(bytes);
        if self.payload_path(&id)?.is_some() {
            return Ok(id);
        }
        let path = within(&self.root.join(OPERATIONS_DIR), name);
        write_once(&self.files, &path, bytes)?;
        if let Some(index) = self.payloads.borrow_mut().as_mut() {
            index.entry(id).or_insert(path);
        }
        Ok(id)
    }

    /// State a version the store now holds, rewriting the header if it grew.
    ///
    /// Decision 0017: the header is the reader's gate, so it must never
    /// understate what the directory contains.
    fn raise_version(&mut self, version: Version) -> Result<(), StoreError> {
        if version <= self.version {
            return Ok(());
        }
        let header = self.root.join(HEADER_FILE);
        // Only the first line moves: whatever a person wrote under it is
        // theirs, and a version bump is no reason to take it away.
        let held = read_to_string(&self.files, &header).unwrap_or_default();
        let rest: String = held
            .split_once('\n')
            .map(|(_, rest)| rest.to_owned())
            .unwrap_or_else(|| format!("\n{HEADER_NOTE}"));
        self.files
            .write(
                &header,
                format!("{}\n{rest}", version.preamble()).as_bytes(),
            )
            .map_err(|error| StoreError::io(&header, error))?;
        self.version = version;
        Ok(())
    }

    /// Point a bookmark at something, creating or moving it.
    ///
    /// Bookmarks are the only mutable files in a store, and therefore its
    /// entire conflict surface.
    pub fn set_name(&mut self, name: &str, target: Name) -> Result<(), StoreError> {
        if name.is_empty() || name.contains('/') || name.contains('\\') {
            return Err(StoreError::UnusableName {
                name: name.to_owned(),
            });
        }
        // Decision 0024: every place a bookmark may be typed looks it up before
        // parsing anything, so a name spelled as a full identifier would stop
        // the identifier it spells from naming its own file, and nothing would
        // say so. An abbreviation is untouched: a bookmark called `ba5e` is
        // 0001's own answer, and this is only the full twenty-four characters.
        if name.parse::<FileId>().is_ok() {
            return Err(StoreError::NameIsAnIdentifier {
                name: name.to_owned(),
            });
        }
        let path = self
            .root
            .join(NAMES_DIR)
            .join(format!("{name}{NAME_SUFFIX}"));
        self.files
            .write(&path, format!("{target}\n").as_bytes())
            .map_err(|error| StoreError::io(&path, error))?;
        self.names.insert(name.to_owned(), target);
        Ok(())
    }

    /// Add rules to `history/skipped.txt`, leaving what it already says alone.
    ///
    /// An append rather than a rewrite of the parsed rules, which would render
    /// back a file with every blank line gone. The parser ignores those, but a
    /// person grouping their rules with them meant something by them, and this
    /// is not the command that decides they were noise.
    ///
    /// Decision 0011 puts the file in `names/`'s company — mutable, synced,
    /// and a fact about the repository rather than about the person.
    pub fn append_skipped(&mut self, rules: &[Rule]) -> Result<(), StoreError> {
        if rules.is_empty() {
            return Ok(());
        }
        let path = self.root.join(SKIPPED_FILE);
        let existing = match read_to_string(&self.files, &path) {
            Ok(text) => text,
            Err(error) if error.kind() == io::ErrorKind::NotFound => String::new(),
            Err(error) => return Err(StoreError::io(&path, error)),
        };
        let mut text = existing;
        // A file whose last line was never terminated would otherwise take the
        // first new rule onto the end of it, and the pair would parse as one
        // line neither of them says.
        if !text.is_empty() && !text.ends_with('\n') {
            text.push('\n');
        }
        for rule in rules {
            text.push_str(&format!("{rule}\n"));
        }
        self.files
            .write(&path, text.as_bytes())
            .map_err(|error| StoreError::io(&path, error))?;
        self.skipped = Skipped::parse(&text)
            .map_err(|error| StoreError::MalformedSkipped { file: path, error })?;
        Ok(())
    }
}

/// One of the store's directories, joined with a name that may carry `/`.
fn within(directory: &Path, name: &str) -> PathBuf {
    let mut path = directory.to_path_buf();
    for component in name.split('/') {
        path.push(component);
    }
    path
}

/// Write a digest-named file, never renaming or overwriting one.
///
/// A file that is already there is the same file, because its name is its
/// digest — confirmed rather than assumed.
fn write_once<F: Filesystem + ?Sized>(
    files: &F,
    path: &Path,
    bytes: &[u8],
) -> Result<(), StoreError> {
    // Decision 0018 files a path as a path, so a writer makes the directories
    // the name asks for. `create_directory` is content-free: it makes what the
    // name says and nothing else.
    if let Some(parent) = path.parent() {
        files
            .create_directory(parent)
            .map_err(|error| StoreError::io(parent, error))?;
    }
    // One operation rather than a test and a write, which is the whole reason
    // the trait has it: the window between the two is where a second writer
    // producing the same revision leaves half a document under a name that
    // promises its digest.
    match files.create_new(path, bytes) {
        Ok(()) => {}
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            let existing = files
                .read(path)
                .map_err(|error| StoreError::io(path, error))?;
            if existing != bytes {
                return Err(StoreError::ContentMismatch {
                    file: path.to_path_buf(),
                });
            }
        }
        Err(error) => return Err(StoreError::io(path, error)),
    }
    Ok(())
}

/// Read `history/skipped.txt`, which a store need not have.
fn read_skipped<F: Filesystem + ?Sized>(files: &F, root: &Path) -> Result<Skipped, StoreError> {
    let path = root.join(SKIPPED_FILE);
    match read_to_string(files, &path) {
        Ok(text) => Skipped::parse(&text).map_err(|error| StoreError::MalformedSkipped {
            file: path.clone(),
            error,
        }),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(Skipped::none()),
        Err(error) => Err(StoreError::io(&path, error)),
    }
}

/// Read and validate the store's version header.
///
/// Decision 0017: the header states the highest document version the store
/// holds, which makes it the reader's gate — a reader that knows less refuses
/// the store at the file that says so, rather than reading four fifths of it
/// and calling the result a history.
fn read_version<F: Filesystem + ?Sized>(files: &F, root: &Path) -> Result<Version, StoreError> {
    let header = root.join(HEADER_FILE);
    let text = match read_to_string(files, &header) {
        Ok(text) => text,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return Err(StoreError::NotAStore {
                path: root.to_path_buf(),
            });
        }
        Err(error) => return Err(StoreError::io(&header, error)),
    };
    // Decision 0021: the first line is the version and everything under it is
    // prose for whoever opens the folder. Nothing hashes this file, so a person
    // may write what they like there.
    let line = text.lines().next().unwrap_or_default();
    for version in [Version::V0, Version::V1, Version::V2, Version::V3] {
        if line == version.preamble() {
            return Ok(version);
        }
    }
    Err(StoreError::UnknownVersion {
        found: line.to_owned(),
    })
}

/// What one of the store's directories holds, at any depth.
///
/// Decision 0016: the walk recurses, so a person may arrange `operations/`
/// into whatever directories narrate their history — and a reader that only
/// looked at the top level would read such a store as healthy and incomplete,
/// which is the one failure this format is least willing to produce.
///
/// Held apart rather than filtered on the spot because `check` reports what
/// the loader ignores, and the two describing different directories is how a
/// store passes a check it should not.
#[derive(Debug, Default)]
pub struct Walk {
    /// Every regular file found, sorted, at any depth.
    pub files: Vec<PathBuf>,
    /// Every symbolic link found, sorted, followed by nothing.
    pub links: Vec<PathBuf>,
}

/// Walk one of the store's directories on `files`, at any depth.
///
/// **Symbolic links are found and never followed**, which is what makes an
/// unbounded walk safe: a tree of real directories cannot contain itself, so
/// there is no loop to guard against and no depth to cap. Decision 0011
/// refused a symlink in the working copy on the neighbouring argument — that
/// following one reads somebody else's file under this name — and a store is
/// not the place to change that answer.
pub fn walk<F: Filesystem + ?Sized>(
    files: &F,
    root: &Path,
    directory: &str,
) -> Result<Walk, StoreError> {
    let directory = root.join(directory);
    let mut found = Walk::default();
    let mut pending = vec![directory.clone()];
    while let Some(next) = pending.pop() {
        let entries = match files.entries(&next) {
            Ok(entries) => entries,
            // Absent is empty at the top and impossible below it, since the
            // walk only descends into what it has just seen.
            Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
            Err(error) => return Err(StoreError::io(&next, error)),
        };
        // The trait reports what an entry is without following it, which is
        // where the refusal to follow a link now lives: a reader that resolved
        // one would call the thing at the other end a file of this store.
        for Entry { path, kind } in entries {
            match kind {
                fs::Kind::Symlink => found.links.push(path),
                fs::Kind::Directory => pending.push(path),
                fs::Kind::File => found.files.push(path),
                fs::Kind::Other => {}
            }
        }
    }
    // Sorted at the end rather than per directory: `pending` is a stack, so
    // the order files are found in is not the order they are named in, and
    // two replicas loading one store must agree about both.
    found.files.sort();
    found.links.sort();
    Ok(found)
}

/// Every payload in `operations/`, at any depth.
///
/// Decision 0017: only `*.ops` is an operation document there, and every other
/// file is a payload. The rule is `revisions/`'s — the extension is a file's
/// claim to be a document — read from the other side.
fn payload_files<F: Filesystem + ?Sized>(
    files: &F,
    root: &Path,
) -> Result<Vec<PathBuf>, StoreError> {
    let mut paths = walk(files, root, OPERATIONS_DIR)?.files;
    // Decision 0022: a file the platform wrote into our folder is not content
    // and not a fault. It is somebody else's file, and nothing here reads it.
    paths.retain(|path| !claims(path, &OPERATION_SUFFIXES) && !platform_file(path));
    Ok(paths)
}

/// Every file making one of these claims, at any depth.
///
/// The suffix is the one part of a filename that means anything: it is the
/// file's claim to be a revision or an operation document, and everything else
/// about the name is ignored. Matched as a suffix rather than with
/// `Path::extension`, which sees only the last of a two-part one.
fn files_claiming<F: Filesystem + ?Sized>(
    files: &F,
    root: &Path,
    directory: &str,
    suffixes: &[&str],
) -> Result<Vec<PathBuf>, StoreError> {
    let mut paths = walk(files, root, directory)?.files;
    paths.retain(|path| claims(path, suffixes));
    Ok(paths)
}

/// Every bookmark file under `names/`, by bookmark name.
fn name_files<F: Filesystem + ?Sized>(
    files: &F,
    root: &Path,
) -> Result<Vec<(String, PathBuf)>, StoreError> {
    let directory = root.join(NAMES_DIR);
    let mut found = Vec::new();
    let entries = match files.entries(&directory) {
        Ok(entries) => entries,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(found),
        Err(error) => return Err(StoreError::io(&directory, error)),
    };
    for Entry { path, kind } in entries {
        // Decision 0021: a bookmark is `<name>.txt`, and anything else here is
        // a file nothing reads, which `check` says out loud.
        if kind.is_file()
            && let Some(name) = path.file_name().and_then(|name| name.to_str())
            && let Some(name) = name.strip_suffix(NAME_SUFFIX)
        {
            found.push((name.to_owned(), path));
        }
    }
    // The trait promises no order, and two replicas loading one store must
    // agree about this one.
    found.sort();
    Ok(found)
}

/// Why a store could not produce the tree or the file that was asked for.
///
/// None of these mean the store is broken. Three of them mean transport has
/// more to deliver, one means the history is concurrent and merging is not
/// built, and two mean the store contradicts itself in the way
/// [`crate::replay`] and [`crate::tree`] describe.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum MaterialiseError {
    /// A payload nothing has delivered.
    MissingPayload {
        /// The payload nothing here holds.
        payload: RevisionId,
        /// The revision that names it.
        named_by: RevisionId,
    },
    /// A payload the filesystem would not hand over.
    Unreadable {
        /// The payload.
        payload: RevisionId,
        /// What the filesystem said.
        because: String,
    },
    /// A `text` payload holding bytes no operation document could quote.
    PayloadNotText {
        /// The payload.
        payload: RevisionId,
        /// The revision that names it.
        named_by: RevisionId,
    },
    /// A file the tree does not hold at these heads.
    NoSuchFile {
        /// The file asked for.
        file: FileId,
    },
    /// Concurrent revisions each stated a file's whole content.
    ContestedContent {
        /// The file they disagree about.
        file: FileId,
    },
    /// A revision this store does not hold.
    Unknown {
        /// The revision asked for.
        revision: RevisionId,
    },
    /// A parent this store does not hold.
    MissingParent {
        /// The parent nothing here holds.
        parent: RevisionId,
        /// The revision that names it.
        named_by: RevisionId,
    },
    /// Operations that could not be merged, which means they disagree about
    /// the file they claim to edit rather than about anything concurrent.
    Merge {
        /// The head being materialised.
        revision: RevisionId,
        /// The file.
        file: FileId,
        /// What went wrong. Boxed: it is the largest thing here by far.
        error: Box<crate::merge::MergeError>,
    },
    /// An `edit` naming an operation document this store does not hold.
    MissingOperations {
        /// The document nothing here holds.
        document: RevisionId,
        /// The revision that names it.
        named_by: RevisionId,
    },
    /// A revision that could not be applied to its parent's file set.
    Tree {
        /// The revision that would not apply.
        revision: RevisionId,
        /// What went wrong.
        error: TreeError,
    },
    /// An operation document that disagrees with the file it claims to edit.
    Content {
        /// The revision that names the document.
        revision: RevisionId,
        /// The file it claims to edit.
        file: FileId,
        /// What went wrong.
        error: ReplayError,
    },
}

impl fmt::Display for MaterialiseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MaterialiseError::Unknown { revision } => {
                write!(f, "this store does not hold the revision {revision}")
            }
            MaterialiseError::MissingParent { parent, named_by } => write!(
                f,
                "{named_by} names the parent {parent}, which this store does not hold yet"
            ),
            MaterialiseError::Merge {
                revision,
                file,
                error,
            } => write!(f, "{revision}, file {file}: {error}"),
            MaterialiseError::MissingOperations { document, named_by } => write!(
                f,
                "{named_by} names the operation document {document}, \
                 which this store does not hold yet"
            ),
            MaterialiseError::MissingPayload { payload, named_by } => write!(
                f,
                "{named_by} names the content {payload}, \
                 which this store does not hold yet"
            ),
            MaterialiseError::Unreadable { payload, because } => {
                write!(f, "the content {payload} could not be read: {because}")
            }
            MaterialiseError::PayloadNotText { payload, named_by } => write!(
                f,
                "{named_by} names {payload} as text and it is not UTF-8, \
                 so no operation document could ever quote a line of it; \
                 a file of bytes is named by `bytes`"
            ),
            MaterialiseError::NoSuchFile { file } => {
                write!(f, "no file {file} exists here")
            }
            MaterialiseError::ContestedContent { file } => write!(
                f,
                "concurrent revisions each state the whole content of the file {file}, \
                 and bytes do not merge; \
                 record the version you mean, which is the only thing that can decide it"
            ),
            MaterialiseError::Tree { revision, error } => write!(f, "{revision}: {error}"),
            MaterialiseError::Content {
                revision,
                file,
                error,
            } => write!(f, "{revision}, file {file}: {error}"),
        }
    }
}

impl std::error::Error for MaterialiseError {}

/// Why a store could not be opened or written to.
#[derive(Debug)]
#[non_exhaustive]
pub enum StoreError {
    /// No `historica` file, so this directory is not a store.
    NotAStore {
        /// Where one was looked for.
        path: PathBuf,
    },
    /// `init` was asked to create a store where one already exists.
    AlreadyAStore {
        /// The existing store.
        path: PathBuf,
    },
    /// The store states a version this reader does not have.
    UnknownVersion {
        /// The header line as found.
        found: String,
    },
    /// A revision document did not parse.
    Unparsable {
        /// The file it was read from.
        file: PathBuf,
        /// Why it was refused.
        error: ParseError,
    },
    /// A bookmark was not one valid line.
    MalformedName {
        /// The bookmark file.
        file: PathBuf,
    },
    /// `skipped.txt` was not rules.
    MalformedSkipped {
        /// The file.
        file: PathBuf,
        /// Which line, and what was wanted there.
        error: MalformedSkip,
    },
    /// A digest-named file whose bytes are not what its name claims.
    ContentMismatch {
        /// The offending file.
        file: PathBuf,
    },
    /// A bookmark name that cannot be a filename.
    UnusableName {
        /// The name as given.
        name: String,
    },
    /// A bookmark name spelled as a full change ID or file identifier.
    NameIsAnIdentifier {
        /// The name as given.
        name: String,
    },
    /// The filesystem refused.
    Io {
        /// What was being read or written.
        path: PathBuf,
        /// The underlying failure.
        error: io::Error,
    },
}

impl StoreError {
    fn io(path: impl AsRef<Path>, error: io::Error) -> Self {
        Self::Io {
            path: path.as_ref().to_path_buf(),
            error,
        }
    }
}

impl fmt::Display for StoreError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StoreError::NotAStore { path } => write!(
                f,
                "{} is not a store: no `{HEADER_FILE}` file; `init` makes one",
                path.display()
            ),
            StoreError::AlreadyAStore { path } => {
                write!(f, "{} is already a store", path.display())
            }
            StoreError::UnknownVersion { found } => write!(
                f,
                "this store says `{found}` and this reader knows up to `{}`; upgrade Historica",
                Version::CURRENT
            ),
            StoreError::Unparsable { file, error } => {
                write!(f, "{}: {error}", file.display())
            }
            StoreError::MalformedName { file } => {
                write!(f, "{}: {}", file.display(), MalformedName)
            }
            StoreError::MalformedSkipped { file, error } => {
                write!(f, "{}: {error}", file.display())
            }
            StoreError::ContentMismatch { file } => write!(
                f,
                "{} is named for a digest its bytes do not have",
                file.display()
            ),
            StoreError::UnusableName { name } => {
                write!(
                    f,
                    "`{name}` cannot be a bookmark: a bookmark is one filename"
                )
            }
            StoreError::NameIsAnIdentifier { name } => write!(
                f,
                "`{name}` is spelled as an identifier, and a bookmark that is \
                 one would stop that identifier naming its own file; \
                 give it a name a person would say"
            ),
            StoreError::Io { path, error } => write!(f, "{}: {error}", path.display()),
        }
    }
}

impl std::error::Error for StoreError {}
