//! The store on disk: a directory of revision documents.
//!
//! Specified by `docs/decisions/0003-store.md` and completed by
//! `docs/decisions/0006-store-questions.md`. One rule governs everything here:
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
//! ├── historica       # `historica-v0`
//! ├── revisions/      # one revision document per file, under any name
//! ├── operations/     # what each revision did, per file — decision 0007
//! ├── names/          # bookmarks — the only mutable files
//! └── cache/          # derived, disposable, deletable without loss
//! ```

use std::collections::BTreeMap;
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use crate::core::{ChangeId, History, RevisionId};
use crate::format::{PREAMBLE, ParseError, RevisionDocument, digest};

mod check;

pub use check::{Finding, Report, Severity};

/// The directory a store lives in, relative to the repository root.
pub const STORE_DIR: &str = "history";
/// The file that marks a directory as a store, and states its format version.
pub const HEADER_FILE: &str = "historica";
/// Revision documents. Only `*.rev` files here are read as revisions.
pub const REVISIONS_DIR: &str = "revisions";
/// Operation documents, per decision 0007.
pub const OPERATIONS_DIR: &str = "operations";
/// Bookmarks: the only mutable files in a store.
pub const NAMES_DIR: &str = "names";
/// Derived, disposable, and deletable without loss.
pub const CACHE_DIR: &str = "cache";
/// The extension that is a file's claim to be a revision.
pub const REVISION_EXT: &str = "rev";

/// What a bookmark points at.
///
/// Decision 0006: one line, never two. `change` follows amend and rebase
/// automatically and is the default; `revision` is the exact pin for the rare
/// reference that must not move.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Name {
    /// Follows the change through every rewrite.
    Change(ChangeId),
    /// Pinned to one revision, which cannot move.
    Revision(RevisionId),
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
            _ => Err(MalformedName),
        }
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Name::Change(change) => write!(f, "change {change}"),
            Name::Revision(revision) => write!(f, "revision {revision}"),
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
            "a bookmark is one line: `change` and a change ID, or `revision` and a digest"
        )
    }
}

impl std::error::Error for MalformedName {}

/// A loaded store.
///
/// Holds documents rather than [`crate::core::Revision`]s, because the
/// documents are the authority and the graph is the projection — the same
/// relationship decision 0003 gives `cache/`.
#[derive(Debug, Clone)]
pub struct Store {
    root: PathBuf,
    documents: BTreeMap<RevisionId, RevisionDocument>,
    names: BTreeMap<String, Name>,
}

impl Store {
    /// Create an empty store at `root`, which must not already be one.
    pub fn init(root: impl AsRef<Path>) -> Result<Self, StoreError> {
        let root = root.as_ref().to_path_buf();
        let header = root.join(HEADER_FILE);
        if header.exists() {
            return Err(StoreError::AlreadyAStore { path: root });
        }
        for directory in [REVISIONS_DIR, OPERATIONS_DIR, NAMES_DIR, CACHE_DIR] {
            let path = root.join(directory);
            fs::create_dir_all(&path).map_err(|error| StoreError::io(&path, error))?;
        }
        fs::write(&header, format!("{PREAMBLE}\n"))
            .map_err(|error| StoreError::io(&header, error))?;
        Self::open(root)
    }

    /// Open the store rooted at `root`.
    ///
    /// A file that does not parse is an error naming the file, never a skip:
    /// strictness where the machine reads, exactly as in decision 0002. Use
    /// [`Store::check`] when the point is to enumerate every fault rather than
    /// to stop at the first.
    pub fn open(root: impl AsRef<Path>) -> Result<Self, StoreError> {
        let root = root.as_ref().to_path_buf();
        read_version(&root)?;

        let mut documents = BTreeMap::new();
        for path in revision_files(&root)? {
            let bytes = fs::read(&path).map_err(|error| StoreError::io(&path, error))?;
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

        let mut names = BTreeMap::new();
        for (name, path) in name_files(&root)? {
            let text = fs::read_to_string(&path).map_err(|error| StoreError::io(&path, error))?;
            let target =
                Name::parse(&text).map_err(|_| StoreError::MalformedName { file: path.clone() })?;
            names.insert(name, target);
        }

        Ok(Self {
            root,
            documents,
            names,
        })
    }

    /// Find the store containing `from`, walking up towards the filesystem root.
    ///
    /// A directory called `history` is not enough: it must hold a `historica`
    /// file, so an unrelated folder of the same name is not mistaken for one.
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

    /// Examine a store without loading it, reporting every fault at once.
    ///
    /// Errors mean the store cannot be trusted; notes are observations that
    /// never fail. See `docs/decisions/0006-store-questions.md`.
    pub fn check(root: impl AsRef<Path>) -> Report {
        check::check(root.as_ref())
    }

    /// The directory this store occupies.
    pub fn root(&self) -> &Path {
        &self.root
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
        let bytes = document.write();
        let id = digest(&bytes);
        let path = self
            .root
            .join(REVISIONS_DIR)
            .join(format!("{id}.{REVISION_EXT}"));

        match fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
        {
            Ok(mut file) => {
                use io::Write as _;
                file.write_all(&bytes)
                    .map_err(|error| StoreError::io(&path, error))?;
            }
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                // Same name implies same bytes, so this is the revision we
                // already have. Confirm rather than assume.
                let existing = fs::read(&path).map_err(|error| StoreError::io(&path, error))?;
                if existing != bytes {
                    return Err(StoreError::ContentMismatch { file: path });
                }
            }
            Err(error) => return Err(StoreError::io(&path, error)),
        }

        self.documents.insert(id, document.clone());
        Ok(id)
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
        let path = self.root.join(NAMES_DIR).join(name);
        fs::write(&path, format!("{target}\n")).map_err(|error| StoreError::io(&path, error))?;
        self.names.insert(name.to_owned(), target);
        Ok(())
    }
}

/// Read and validate the store's version header.
fn read_version(root: &Path) -> Result<(), StoreError> {
    let header = root.join(HEADER_FILE);
    let text = match fs::read_to_string(&header) {
        Ok(text) => text,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return Err(StoreError::NotAStore {
                path: root.to_path_buf(),
            });
        }
        Err(error) => return Err(StoreError::io(&header, error)),
    };
    let line = text.trim_end_matches('\n');
    if line != PREAMBLE {
        return Err(StoreError::UnknownVersion {
            found: line.to_owned(),
        });
    }
    Ok(())
}

/// Every `*.rev` file under `revisions/`, in a deterministic order.
///
/// The extension is the one syllable of a filename that means anything: it is
/// the file's claim to be a revision, and everything else is ignored.
fn revision_files(root: &Path) -> Result<Vec<PathBuf>, StoreError> {
    let directory = root.join(REVISIONS_DIR);
    let mut paths = Vec::new();
    let entries = match fs::read_dir(&directory) {
        Ok(entries) => entries,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(paths),
        Err(error) => return Err(StoreError::io(&directory, error)),
    };
    for entry in entries {
        let entry = entry.map_err(|error| StoreError::io(&directory, error))?;
        let path = entry.path();
        if path.is_file() && path.extension().is_some_and(|ext| ext == REVISION_EXT) {
            paths.push(path);
        }
    }
    paths.sort();
    Ok(paths)
}

/// Every bookmark file under `names/`, by bookmark name.
fn name_files(root: &Path) -> Result<Vec<(String, PathBuf)>, StoreError> {
    let directory = root.join(NAMES_DIR);
    let mut found = Vec::new();
    let entries = match fs::read_dir(&directory) {
        Ok(entries) => entries,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(found),
        Err(error) => return Err(StoreError::io(&directory, error)),
    };
    for entry in entries {
        let entry = entry.map_err(|error| StoreError::io(&directory, error))?;
        let path = entry.path();
        if path.is_file()
            && let Some(name) = path.file_name().and_then(|name| name.to_str())
        {
            found.push((name.to_owned(), path));
        }
    }
    found.sort();
    Ok(found)
}

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
                "this store says `{found}` and this reader knows `{PREAMBLE}`; upgrade Historica"
            ),
            StoreError::Unparsable { file, error } => {
                write!(f, "{}: {error}", file.display())
            }
            StoreError::MalformedName { file } => {
                write!(f, "{}: {}", file.display(), MalformedName)
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
            StoreError::Io { path, error } => write!(f, "{}: {error}", path.display()),
        }
    }
}

impl std::error::Error for StoreError {}
