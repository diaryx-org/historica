//! One kept chain — *somebody else's history, fetched into a directory of
//! yours and kept current by fetching again.*
//!
//! The shape is historica's own, unreshaped: the writer's documents
//! materialised at the head, and the store beside them.
//!
//! ```text
//! <repo>/
//!     <the writer's files, at the head>
//!     history/          the store
//!         remark/       this crate's notes — see NOTES_DIR
//! ```
//!
//! A [`Repo`] is a path and nothing else; constructing one touches no disk.
//!
//! # Where the directory is
//!
//! Wherever the caller's [`Filesystem`] says. Every read and write here goes
//! through one, the same seam historica's own [`Store`] is built on (its
//! decision 0025), and nothing in this crate reaches `std::fs` itself. The
//! filesystem is a type parameter defaulting to [`Disk`], for the reason
//! historica gives for its own: a `Repo` is `Clone`, `Send` or `Debug`
//! exactly when its filesystem is, and nobody's filesystem is asked for more.
//!
//! [`Repo::at`] is a repository on [`Disk`], as it always was. [`Repo::on`]
//! takes any other — an `Arc<`[`Memory`](super::Memory)`>` for a test that
//! should not touch a disk, an `Arc<dyn Filesystem>` for a caller that
//! decides at run time.
//!
//! # What a receive is
//!
//! historica's `fetch` (its decision 0048): the store asks the source for the
//! manifest, takes exactly what it lacks, verifies every file against the
//! digest the manifest names it by, and complies with any forgetting that
//! arrives — so a line the writer withdrew is destroyed here on the next
//! receive, without anybody on this side being asked. The store is then
//! materialised at its head so the files can be read as files.
//!
//! A source that is not a continuation of what this store already holds is
//! refused rather than merged: a single-writer chain that has become another
//! chain is a different history, not a newer one.
//!
//! # What is read out of it
//!
//! Remarks, chiefly — every document at the head that declares a `target` and
//! reads as an [`Annotation`]. A document that declares a target and cannot
//! be read as a remark is passed over rather than reported: it is the
//! writer's mistake, in the writer's chain, and the reader has no way to mend
//! it.

use std::path::{Path, PathBuf};

use historica::core::RevisionId;
use historica::fs::{self as files, Disk, Filesystem};
use historica::store::{HEADER_FILE, STORE_DIR, Source, Store};
use historica::tree::Kind;

use crate::annotation::{Annotation, Fields, Reader, TargetCheck};
use crate::error::{Error, Result, history};

/// The directory under a store where this crate keeps its notes, unless the
/// caller names another.
///
/// Historica's decision 0053 makes this safe to write in: a directory at the
/// store root that historica did not name is somebody else's, and local-only
/// — `check` walks what it named and says nothing about the rest, and nothing
/// here is ever carried. Losing the whole directory costs a display name and
/// the knowledge of where a copy came from, never an answer about what was
/// received.
pub const NOTES_DIR: &str = "remark";

/// Where the sender's display name is noted.
pub const SENDER_NOTE: &str = "sender";

/// Where the name the writer's own chain answers to is noted.
///
/// Distinct from the directory this copy is kept in, which is the *reader's*
/// name for it. A remark's target names a document in the writer's scheme,
/// and this is the other half of resolving one.
pub const ORIGIN_NOTE: &str = "origin";

/// The manifest's name in a fetcher's flat space: what a [`Source`] built
/// over an [`Export`](super::Export) answers with the manifest, and what a
/// sealed transport resolves without consulting it.
pub const MANIFEST_PATH: &str = "offer.txt";

/// What one receive brought in.
#[derive(Debug, Clone)]
pub struct Received {
    /// The label the caller gave this chain.
    pub name: String,
    /// The head after the fetch, or `None` when the source offered nothing
    /// and the store is still empty.
    pub head: Option<String>,
    /// Revision documents taken.
    pub revisions: usize,
    /// Content documents taken.
    pub documents: usize,
    /// Originals destroyed in compliance with forgettings that arrived.
    pub destroyed: usize,
    /// Documents materialised at the head.
    pub files: usize,
}

/// One remark found in a chain, with the document facts around it.
#[derive(Debug, Clone)]
pub struct Remark {
    /// What to call the chain it was found in — the caller's label.
    pub from: String,
    /// Its path in the writer's chain.
    pub path: String,
    /// The remark itself.
    pub annotation: Annotation,
    /// The document's own `id`, when it declares one — with the writer's
    /// namespace, the identity the remark is known by everywhere.
    pub id: Option<String>,
    /// The document's own title, when it declares one.
    pub title: Option<String>,
    /// The `via` a copied remark carries — the identity it had in the chain
    /// that first wrote it. What lets its author, reading somebody else's
    /// copy, recognise their own remark come back.
    pub via: Option<String>,
    /// Who wrote it, as the chain that copied it knew them.
    pub creator: Option<String>,
    /// Everything else the document declared.
    ///
    /// A remark travels through whatever vocabulary its writer's tool
    /// keeps — a disclosure list, a colour scheme, a workflow state — and
    /// this crate has no business naming those. Read them with
    /// [`Fields`](crate::Fields), which [`fig::Value`] implements.
    pub meta: fig::Value,
}

/// One kept chain, at a path, on a filesystem — [`Disk`] unless the caller
/// names another.
#[derive(Debug, Clone)]
pub struct Repo<F = Disk> {
    files: F,
    root: PathBuf,
    notes: String,
}

impl Repo {
    /// A repository at `root` on [`Disk`], keeping its notes under
    /// [`NOTES_DIR`].
    pub fn at(root: impl Into<PathBuf>) -> Self {
        Self::on(Disk, root)
    }

    /// The same, keeping its notes under a directory of the caller's own.
    ///
    /// For a tool that already writes notes into a store somewhere and would
    /// have to migrate every existing copy to adopt this crate's spelling.
    /// The directory must be one historica has not reserved, which is every
    /// name historica does not itself use.
    pub fn with_notes(root: impl Into<PathBuf>, notes: impl Into<String>) -> Self {
        Self::with_notes_on(Disk, root, notes)
    }
}

impl<F> Repo<F> {
    /// A repository at `root` on `files`, keeping its notes under
    /// [`NOTES_DIR`].
    ///
    /// Named after historica's `Store::open_on`, and for the same reason:
    /// the folder is the caller's to supply, and [`Repo::at`] is this with
    /// [`Disk`] and nothing more.
    pub fn on(files: F, root: impl Into<PathBuf>) -> Self {
        Self::with_notes_on(files, root, NOTES_DIR)
    }

    /// [`Repo::with_notes`], on `files`.
    pub fn with_notes_on(files: F, root: impl Into<PathBuf>, notes: impl Into<String>) -> Self {
        Self {
            files,
            root: root.into(),
            notes: notes.into(),
        }
    }

    /// The repository's directory.
    pub fn root(&self) -> &Path {
        &self.root
    }

    /// The filesystem the directory is on.
    pub fn files(&self) -> &F {
        &self.files
    }

    /// The store's directory, inside it.
    pub fn store_dir(&self) -> PathBuf {
        self.root.join(STORE_DIR)
    }
}

impl<F: Filesystem> Repo<F> {
    /// Whether a store is here — the marker file, not the directory: a folder
    /// merely named `history` is ordinary content.
    ///
    /// A filesystem that cannot say is taken to be saying no, which is what
    /// asking `std::fs` the same question always answered.
    pub fn exists(&self) -> bool {
        files::is_file(&self.files, &self.store_dir().join(HEADER_FILE)).unwrap_or(false)
    }

    /// The store, opened on this repository's filesystem. A borrowed
    /// filesystem is a filesystem, so nothing has to be cloned to open one.
    pub(crate) fn store(&self) -> Result<Store<&F>> {
        Store::open_on(&self.files, self.store_dir()).map_err(history)
    }

    /// The current head, as a digest. `None` for a store that holds no
    /// revision, and for one that is not there at all.
    pub fn head(&self) -> Result<Option<String>> {
        if !self.exists() {
            return Ok(None);
        }
        let store = self.store()?;
        Ok(head_of(&store).map(|h| h.to_string()))
    }

    // ── notes ──────────────────────────────────────────────────────────────

    /// Note one fact about this copy. Overwrites; the note is a current
    /// answer rather than a log.
    pub fn note(&self, name: &str, value: &str) -> Result<()> {
        let path = self.note_path(name)?;
        if let Some(parent) = path.parent() {
            self.files.create_directory(parent)?;
        }
        self.files
            .write(&path, format!("{}\n", value.trim()).as_bytes())?;
        Ok(())
    }

    /// One noted fact, or `None` when it was never noted — which is what a
    /// copy fetched before the note existed answers, and re-fetching writes.
    pub fn noted(&self, name: &str) -> Option<String> {
        let text = files::read_to_string(&self.files, &self.note_path(name).ok()?).ok()?;
        let noted = text.trim();
        (!noted.is_empty()).then(|| noted.to_string())
    }

    fn note_path(&self, name: &str) -> Result<PathBuf> {
        check_name(name)?;
        Ok(self
            .store_dir()
            .join(&self.notes)
            .join(format!("{name}.txt")))
    }

    /// The sender's display name, as last noted.
    pub fn sender(&self) -> Option<String> {
        self.noted(SENDER_NOTE)
    }

    /// Note the sender's display name. An empty name notes nothing rather
    /// than noting emptiness.
    pub fn note_sender(&self, who: &str) -> Result<()> {
        match who.trim().is_empty() {
            true => Ok(()),
            false => self.note(SENDER_NOTE, who),
        }
    }

    /// The name the writer's own chain answers to, as last noted.
    pub fn origin(&self) -> Option<String> {
        self.noted(ORIGIN_NOTE)
    }

    /// Note it. The transport is the only party that ever knows this — it
    /// comes off whatever served the chain, not out of anything the chain
    /// carries — so it is recorded at receive time or not at all.
    pub fn note_origin(&self, origin: &str) -> Result<()> {
        match origin.trim().is_empty() {
            true => Ok(()),
            false => self.note(ORIGIN_NOTE, origin),
        }
    }

    // ── receiving ──────────────────────────────────────────────────────────

    /// Fetch what `source` offers under `manifest` into this repository,
    /// creating it on first use, and materialise the result at its head.
    ///
    /// `name` only labels the [`Received`]; where the chain goes is this
    /// repository's own path.
    pub fn receive<S: Source + ?Sized>(
        &self,
        name: &str,
        source: &S,
        manifest: &str,
    ) -> Result<Received> {
        if !self.exists() {
            self.files.create_directory(&self.root)?;
            Store::init_on(&self.files, self.store_dir()).map_err(history)?;
        }
        let mut store = self.store()?;
        // The claims that vouch for what arrives come with it, as `reserved`
        // entries of the offer: historica carries a reserved directory by its
        // class, and its registry says `claims/` travels and `trust/` does
        // not. So there is nothing to do here, and a chain arrives vouched
        // for or not vouched for exactly as it left. See [`super::carry`].
        let fetched = store.fetch(source, manifest, false).map_err(history)?;

        // Reopen: what a fetch destroyed in compliance with a forgetting is
        // best read from a store that has not held the originals in memory.
        let store = self.store()?;
        let head = head_of(&store);
        let files = match &head {
            Some(head) => materialised(&store, head)?,
            None => Vec::new(),
        };
        self.lay_out(&files)?;
        Ok(Received {
            name: name.to_string(),
            head: head.map(|h| h.to_string()),
            revisions: fetched.revisions.len(),
            documents: fetched.documents,
            destroyed: fetched.destroyed,
            files: files.len(),
        })
    }

    // ── reading ────────────────────────────────────────────────────────────

    /// Every document at the head, path and text, in path order — the
    /// writer's chain as this copy last fetched it, which is what a reading
    /// surface renders. Empty for a repository nothing has been received
    /// into.
    pub fn documents(&self) -> Result<Vec<(String, String)>> {
        if !self.exists() {
            return Ok(Vec::new());
        }
        let store = self.store()?;
        let Some(head) = head_of(&store) else {
            return Ok(Vec::new());
        };
        let mut out = materialised(&store, &head)?;
        out.sort_by(|a, b| a.0.cmp(&b.0));
        Ok(out)
    }

    /// Every remark at the head, in path order; narrowed to those of
    /// `target` when one is given, and labelled `from` whatever the caller
    /// calls this chain.
    ///
    /// A document that declares no target is not a remark and is skipped. So
    /// is one that declares a target `reader` refuses, or a motivation it
    /// does not know: the writer's chain is not the reader's to correct, and
    /// one unreadable document must not cost the answer about the other
    /// nine hundred.
    pub fn remarks<C: TargetCheck>(
        &self,
        reader: &Reader<C>,
        from: &str,
        target: Option<&str>,
    ) -> Result<Vec<Remark>> {
        let target = target.map(str::trim);
        let mut out = Vec::new();
        for (path, text) in self.documents()? {
            let Ok(Some((meta, body))) = crate::document::split(&text) else {
                continue;
            };
            let Ok(Some(annotation)) = reader.read(&meta, &body) else {
                continue;
            };
            if !target.is_none_or(|t| t == annotation.target.trim()) {
                continue;
            }
            let owned = |key: &str| meta.text(key).map(str::to_string);
            out.push(Remark {
                from: from.to_string(),
                path,
                annotation,
                id: owned("id"),
                title: owned("title"),
                via: owned(crate::annotation::VIA_FIELD),
                creator: owned(crate::annotation::CREATOR_FIELD),
                meta,
            });
        }
        out.sort_by(|a, b| a.path.cmp(&b.path));
        Ok(out)
    }

    // ── leaving again ──────────────────────────────────────────────────────

    /// This chain, ready to leave — the carriable shape a publish seals and a
    /// local fetch takes from. `None` for a repository holding no revision.
    ///
    /// How one reader's remarks reach every other reader without anybody's
    /// words being copied into a chain their author does not control.
    pub fn export(&self, label: &str) -> Result<Option<super::Export>> {
        match self.exists() {
            true => super::carry::export_at(self, label),
            false => Ok(None),
        }
    }

    /// Write the head's files into the repository, clearing whatever was
    /// there. The store is left alone — it is what says which files these
    /// are.
    fn lay_out(&self, laid: &[(String, String)]) -> Result<()> {
        for entry in self.files.entries(&self.root)? {
            if entry.path.file_name().and_then(|n| n.to_str()) == Some(STORE_DIR) {
                continue;
            }
            match entry.kind.is_directory() {
                true => remove_tree(&self.files, &entry.path)?,
                false => self.files.remove_file(&entry.path)?,
            }
        }
        for (path, text) in laid {
            let full = self.root.join(path);
            if let Some(parent) = full.parent() {
                self.files.create_directory(parent)?;
            }
            self.files.write(&full, text.as_bytes())?;
        }
        Ok(())
    }
}

/// Remove a directory and everything under it.
///
/// The trait removes one empty directory at a time on purpose — historica
/// tidies upwards until a directory refuses, and a recursive remove there
/// would delete a history a level at a time — so the recursion is spelled
/// here, for the one directory this crate means to empty: the head it is
/// about to lay out again. A link is removed as a link, never followed.
fn remove_tree<F: Filesystem + ?Sized>(files: &F, path: &Path) -> Result<()> {
    for entry in files.entries(path)? {
        match entry.kind.is_directory() {
            true => remove_tree(files, &entry.path)?,
            false => files.remove_file(&entry.path)?,
        }
    }
    files.remove_directory(path)?;
    Ok(())
}

/// A name that is about to be a path segment, and nothing else is assumed
/// about it.
pub fn check_name(name: &str) -> Result<()> {
    let bad = name.is_empty()
        || name.starts_with('.')
        || name.contains(['/', '\\'])
        || name.chars().any(char::is_control);
    match bad {
        true => Err(Error::Name(format!("{name:?} cannot name a kept chain"))),
        false => Ok(()),
    }
}

/// The head a single-writer chain is at.
///
/// A superseded head is one an amendment replaced; what is left is the
/// current one. A chain with nothing but superseded heads has been amended
/// down to nothing readable, and the raw heads are better than no answer.
pub(crate) fn current_heads<F: Filesystem>(store: &Store<F>) -> Vec<RevisionId> {
    let history = store.history();
    let heads = history.childless();
    let superseded = history.superseded();
    let current: Vec<RevisionId> = heads.difference(&superseded).copied().collect();
    match current.is_empty() {
        true => heads.into_iter().collect(),
        false => current,
    }
}

pub(crate) fn head_of<F: Filesystem>(store: &Store<F>) -> Option<RevisionId> {
    current_heads(store).first().copied()
}

/// Every text file at one revision, path and text.
///
/// Files of bytes are skipped: a remark is text, and a caller wanting the
/// rest of what a chain holds should ask the store, which is the thing that
/// has it.
pub(crate) fn materialised<F: Filesystem>(
    store: &Store<F>,
    revision: &RevisionId,
) -> Result<Vec<(String, String)>> {
    let tree = store.tree(revision).map_err(history)?;
    let mut out = Vec::new();
    for (file, entry) in tree.entries() {
        if entry.kind != Kind::Lines {
            continue;
        }
        let content = store.content_at(revision, file).map_err(history)?;
        if let Some(state) = content.lines() {
            out.push((entry.path.clone(), state.text()));
        }
    }
    Ok(out)
}
