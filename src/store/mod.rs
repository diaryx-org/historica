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
//! ├── historica       # `historica-v1`
//! ├── revisions/      # one revision document per file, under any name
//! ├── operations/     # what each revision did, per file — decisions 0007, 0017
//! ├── names/          # bookmarks — the only mutable files
//! └── cache/          # derived, disposable, deletable without loss
//! ```
//!
//! `operations/` holds two kinds of file, on the rule `revisions/` already
//! keeps: only `*.ops` is read as an operation document, and every other file
//! is a payload — decision 0017's content that arrives whole, carrying no
//! format of its own and identified by the digest of its bytes. Payloads are
//! not read when a store is opened. A history with photographs in it must not
//! cost a full hash to run `log`, so the directory is indexed on first need
//! and `check` is where every payload is hashed deliberately.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use crate::core::{ChangeId, FileId, History, RevisionId};
use crate::format::{OperationDocument, ParseError, RevisionDocument, Version, digest};
use crate::merge::{self, Merged};
use crate::replay::{self, ReplayError, State};
use crate::tree::{self, Kind, MergedTree, Tree, TreeError};
use crate::working::{MalformedSkip, Rule, SKIPPED_FILE, Skipped};

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
/// The suffix a writer puts on a revision document.
///
/// Decision 0020: the claim that says which kind of document this is comes
/// first, and the claim that says it is text comes last, where an operating
/// system reads it.
pub const REVISION_SUFFIX: &str = ".rev.txt";
/// The suffix a writer puts on an operation document.
pub const OPERATION_SUFFIX: &str = ".ops.txt";
/// Every suffix that is a file's claim to be a revision document.
///
/// The older one is read permanently, which is decision 0004's asymmetry
/// applied to a filename rule: a store written before 0020 must not quietly
/// stop having documents in it.
pub const REVISION_SUFFIXES: [&str; 2] = [REVISION_SUFFIX, ".rev"];
/// Every suffix that is a file's claim to be an operation document.
pub const OPERATION_SUFFIXES: [&str; 2] = [OPERATION_SUFFIX, ".ops"];

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
#[derive(Debug, Clone)]
pub struct Store {
    root: PathBuf,
    /// The highest document version this store holds, which is what its
    /// header states and therefore the gate a reader is refused at.
    version: Version,
    documents: BTreeMap<RevisionId, RevisionDocument>,
    operations: BTreeMap<RevisionId, OperationDocument>,
    /// Where each payload sits, by digest. Built on first need, never at open.
    payloads: RefCell<Option<BTreeMap<RevisionId, PathBuf>>>,
    names: BTreeMap<String, Name>,
    skipped: Skipped,
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
        fs::write(&header, format!("{}\n", Version::CURRENT.preamble()))
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
        let version = read_version(&root)?;

        let mut documents = BTreeMap::new();
        for path in files_claiming(&root, REVISIONS_DIR, &REVISION_SUFFIXES)? {
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

        let mut operations = BTreeMap::new();
        for path in files_claiming(&root, OPERATIONS_DIR, &OPERATION_SUFFIXES)? {
            let bytes = fs::read(&path).map_err(|error| StoreError::io(&path, error))?;
            let document =
                OperationDocument::parse(&bytes).map_err(|error| StoreError::Unparsable {
                    file: path.clone(),
                    error,
                })?;
            operations.insert(digest(&bytes), document);
        }

        let mut names = BTreeMap::new();
        for (name, path) in name_files(&root)? {
            let text = fs::read_to_string(&path).map_err(|error| StoreError::io(&path, error))?;
            let target =
                Name::parse(&text).map_err(|_| StoreError::MalformedName { file: path.clone() })?;
            names.insert(name, target);
        }

        let skipped = read_skipped(&root)?;

        Ok(Self {
            root,
            version,
            documents,
            operations,
            payloads: RefCell::new(None),
            names,
            skipped,
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

    /// One operation document by digest.
    pub fn operation(&self, id: &RevisionId) -> Option<&OperationDocument> {
        self.operations.get(id)
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
        let bytes = fs::read(&path).map_err(|error| StoreError::io(&path, error))?;
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
        for path in payload_files(&self.root)? {
            let bytes = fs::read(&path).map_err(|error| StoreError::io(&path, error))?;
            found.entry(digest(&bytes)).or_insert(path);
        }
        *self.payloads.borrow_mut() = Some(found);
        Ok(())
    }

    /// Every revision `head` descends from, itself included.
    ///
    /// A DAG rather than a chain: merging is what decides the rest, and it
    /// needs the whole ancestry to know what is concurrent with what.
    pub fn reachable(&self, head: &RevisionId) -> Result<Vec<&RevisionDocument>, MaterialiseError> {
        self.reachable_from(&[*head])
    }

    /// Every revision several heads descend from, itself included.
    ///
    /// What merging two lines of work walks, before any revision joins them:
    /// decision 0012's `merge` asks this of a store to render a conflict that
    /// nothing has recorded yet.
    pub fn reachable_from(
        &self,
        heads: &[RevisionId],
    ) -> Result<Vec<&RevisionDocument>, MaterialiseError> {
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
        Ok(seen.into_values().collect())
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
        tree::merge(reachable.into_iter().map(|document| tree::Event {
            revision: document.id(),
            document,
        }))
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

        // A `text` payload is exactly the document that inserts every line at
        // 0, so it is turned into one here and the merge never learns that a
        // creation has two spellings. The synthesised documents are collected
        // first because the events borrow them.
        let mut created: BTreeMap<RevisionId, Option<OperationDocument>> = BTreeMap::new();
        for document in &reachable {
            let Some(payload) = document.text.get(file) else {
                continue;
            };
            let revision = document.id();
            let text = self.payload_text(payload, revision)?;
            created.insert(revision, replay::creation(&text));
        }

        let mut events = Vec::with_capacity(reachable.len());
        for document in reachable {
            let revision = document.id();
            let operations = match document.edited.get(file) {
                Some(named) => Some(self.operations.get(named).ok_or(
                    MaterialiseError::MissingOperations {
                        document: *named,
                        named_by: revision,
                    },
                )?),
                None => created.get(&revision).and_then(Option::as_ref),
            };
            events.push(merge::Event {
                revision,
                parents: document.parents.iter().copied().collect(),
                operations,
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
    pub fn content(&self, head: &RevisionId, file: &FileId) -> Result<State, MaterialiseError> {
        Ok(self.merged_content(head, file)?.state)
    }

    /// One payload as text, refusing bytes no operation document could quote.
    fn payload_text(
        &self,
        payload: &RevisionId,
        named_by: RevisionId,
    ) -> Result<String, MaterialiseError> {
        let bytes = self
            .payload(payload)
            .map_err(|error| MaterialiseError::Unreadable {
                payload: *payload,
                because: error.to_string(),
            })?
            .ok_or(MaterialiseError::MissingPayload {
                payload: *payload,
                named_by,
            })?;
        String::from_utf8(bytes).map_err(|_| MaterialiseError::PayloadNotText {
            payload: *payload,
            named_by,
        })
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
    /// Decision 0011: `history/skipped` is a fact about the repository rather
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
        write_once(&path, &bytes)?;
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
        write_once(&path, &bytes)?;
        self.operations.insert(id, document.clone());
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
        write_once(&path, bytes)?;
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
        fs::write(&header, format!("{}\n", version.preamble()))
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
        let path = self.root.join(NAMES_DIR).join(name);
        fs::write(&path, format!("{target}\n")).map_err(|error| StoreError::io(&path, error))?;
        self.names.insert(name.to_owned(), target);
        Ok(())
    }

    /// Add rules to `history/skipped`, leaving what it already says alone.
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
        let existing = match fs::read_to_string(&path) {
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
        fs::write(&path, &text).map_err(|error| StoreError::io(&path, error))?;
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
fn write_once(path: &Path, bytes: &[u8]) -> Result<(), StoreError> {
    // Decision 0018 files a path as a path, so a writer makes the directories
    // the name asks for. `create_dir_all` is content-free: it makes what the
    // name says and nothing else.
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|error| StoreError::io(parent, error))?;
    }
    match fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
    {
        Ok(mut file) => {
            use io::Write as _;
            file.write_all(bytes)
                .map_err(|error| StoreError::io(path, error))?;
        }
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            let existing = fs::read(path).map_err(|error| StoreError::io(path, error))?;
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

/// Read `history/skipped`, which a store need not have.
fn read_skipped(root: &Path) -> Result<Skipped, StoreError> {
    let path = root.join(SKIPPED_FILE);
    match fs::read_to_string(&path) {
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
fn read_version(root: &Path) -> Result<Version, StoreError> {
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
    for version in [Version::V0, Version::V1] {
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

/// Walk one of the store's directories, at any depth.
///
/// **Symbolic links are found and never followed**, which is what makes an
/// unbounded walk safe: a tree of real directories cannot contain itself, so
/// there is no loop to guard against and no depth to cap. Decision 0011
/// refused a symlink in the working copy on the neighbouring argument — that
/// following one reads somebody else's file under this name — and a store is
/// not the place to change that answer.
pub fn walk(root: &Path, directory: &str) -> Result<Walk, StoreError> {
    let directory = root.join(directory);
    let mut found = Walk::default();
    let mut pending = vec![directory.clone()];
    while let Some(next) = pending.pop() {
        let entries = match fs::read_dir(&next) {
            Ok(entries) => entries,
            // Absent is empty at the top and impossible below it, since the
            // walk only descends into what it has just seen.
            Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
            Err(error) => return Err(StoreError::io(&next, error)),
        };
        for entry in entries {
            let entry = entry.map_err(|error| StoreError::io(&next, error))?;
            let path = entry.path();
            // `symlink_metadata` rather than `is_file`, which follows a link
            // and would call the thing at the other end a file of this store.
            let metadata =
                fs::symlink_metadata(&path).map_err(|error| StoreError::io(&path, error))?;
            if metadata.is_symlink() {
                found.links.push(path);
            } else if metadata.is_dir() {
                pending.push(path);
            } else if metadata.is_file() {
                found.files.push(path);
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
fn payload_files(root: &Path) -> Result<Vec<PathBuf>, StoreError> {
    let mut paths = walk(root, OPERATIONS_DIR)?.files;
    paths.retain(|path| !claims(path, &OPERATION_SUFFIXES));
    Ok(paths)
}

/// Every file making one of these claims, at any depth.
///
/// The suffix is the one part of a filename that means anything: it is the
/// file's claim to be a revision or an operation document, and everything else
/// about the name is ignored. Matched as a suffix rather than with
/// `Path::extension`, which sees only the last of a two-part one.
fn files_claiming(
    root: &Path,
    directory: &str,
    suffixes: &[&str],
) -> Result<Vec<PathBuf>, StoreError> {
    let mut paths = walk(root, directory)?.files;
    paths.retain(|path| claims(path, suffixes));
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
    /// `skipped` was not rules.
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
            StoreError::Io { path, error } => write!(f, "{}: {error}", path.display()),
        }
    }
}

impl std::error::Error for StoreError {}
