//! `forget`: destroying an item's payload while preserving its shape.
//!
//! Decision 0014. An operation's arithmetic and an operation's payload are
//! different bytes, and only the payload has to be destroyed: a forgetting
//! document states the same operations, at the same positions, with the same
//! counts, and replaces the items it forgets with a `\ forgotten` marker.
//!
//! An item forgotten once is forgotten everywhere it is quoted — the insert
//! that wrote it, and every delete that quotes it back so replay can check
//! itself — so `forget` is a walk over a file's history rather than an edit
//! to one document. That walk is [`crate::merge::quotes`], and the cost is
//! real: finding the deletes that quote a run means replaying the file.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::PathBuf;

use crate::core::{FileId, RevisionId};
use crate::format::OperationDocument;
use crate::fs::Filesystem;
use crate::merge::{self, MergeError, Quoted};
use crate::tree::Kind;

use super::{
    MaterialiseError, OPERATION_SUFFIXES, OPERATIONS_DIR, Store, StoreError, files_claiming,
    payload_files, prune::remove_empty_directories,
};

/// What a person asks to forget: a span of one file, at one revision.
///
/// Lines rather than items, because a person counts what `cat` shows them;
/// one-based, because every editor they have ever used is.
#[derive(Debug, Clone)]
pub struct Forgetting {
    /// The revision the span is read at.
    pub revision: RevisionId,
    /// The file.
    pub file: FileId,
    /// The first line of the span, one-based.
    pub first: usize,
    /// The last line of the span, inclusive.
    pub last: usize,
}

/// What forgetting destroys, and what stands in for it.
///
/// [`Store::forget`] acts on exactly this, so `--dry-run` and the real thing
/// can never describe different bytes.
#[derive(Debug, Clone, Default)]
pub struct Forgotten {
    /// The digests whose bytes are destroyed.
    pub targets: Vec<RevisionId>,
    /// The forgetting documents written, one per destroyed digest that did
    /// not already have an equally thorough stand-in.
    pub writes: Vec<OperationDocument>,
    /// Every file destroyed, relative to the store root.
    pub destroys: Vec<PathBuf>,
    /// How many of the span's items were already forgotten.
    pub already: usize,
}

impl Forgotten {
    /// Whether forgetting would touch nothing, which forgetting twice does.
    pub fn is_empty(&self) -> bool {
        self.writes.is_empty() && self.destroys.is_empty()
    }
}

impl<F: Filesystem> Store<F> {
    /// What forgetting this span would destroy, without destroying anything.
    pub fn forget_plan(&self, forgetting: &Forgetting) -> Result<Forgotten, ForgetError> {
        if forgetting.first == 0 || forgetting.last < forgetting.first {
            return Err(ForgetError::NotASpan {
                first: forgetting.first,
                last: forgetting.last,
            });
        }

        // Decision 0014 defers binary content: a file of bytes has no items
        // to preserve the shape of.
        let tree = self.tree(&forgetting.revision)?;
        let entry = tree
            .entry(&forgetting.file)
            .ok_or(MaterialiseError::NoSuchFile {
                file: forgetting.file,
            })?;
        if entry.kind != Kind::Lines {
            return Err(ForgetError::NotLines {
                file: forgetting.file,
            });
        }

        // The span, named: the file at that revision, and the identity of
        // each visible item in it — which revision wrote it, and where in
        // that revision's document.
        let reachable = self.reachable(&forgetting.revision)?;
        let at_revision = self.quotes_over(&reachable, &forgetting.file)?;
        let visible: Vec<&Quoted> = at_revision.iter().filter(|quoted| quoted.visible).collect();
        if forgetting.last > visible.len() {
            return Err(ForgetError::PastTheEnd {
                last: forgetting.last,
                lines: visible.len(),
            });
        }
        let span: BTreeSet<(RevisionId, usize, usize)> = visible
            [forgetting.first - 1..forgetting.last]
            .iter()
            .map(|quoted| (quoted.written_by, quoted.write.0, quoted.write.1))
            .collect();

        // Every quote of those items, across the whole history this store
        // holds — the deletes included, which is the walk's whole point.
        let every: Vec<(RevisionId, &crate::format::RevisionDocument)> =
            self.iter().map(|(id, document)| (*id, document)).collect();
        let everywhere = self.quotes_over(&every, &forgetting.file)?;

        // The document each revision names for this file, which is what the
        // quote indices index into.
        let named: BTreeMap<RevisionId, RevisionId> = self
            .iter()
            .filter_map(|(id, document)| {
                document
                    .edited
                    .get(&forgetting.file)
                    .or_else(|| document.text.get(&forgetting.file))
                    .map(|names| (*id, *names))
            })
            .collect();

        let mut items: BTreeMap<RevisionId, BTreeSet<(usize, usize)>> = BTreeMap::new();
        let mut already = 0;
        for quoted in &everywhere {
            if !span.contains(&(quoted.written_by, quoted.write.0, quoted.write.1)) {
                continue;
            }
            if quoted.forgotten {
                already += 1;
            }
            if let Some(target) = named.get(&quoted.written_by) {
                items.entry(*target).or_default().insert(quoted.write);
            }
            for (revision, operation, item) in &quoted.deletes {
                if let Some(target) = named.get(revision) {
                    items
                        .entry(*target)
                        .or_default()
                        .insert((*operation, *item));
                }
            }
        }

        // One forgetting document per destroyed digest, skipped where the
        // stand-ins the store already holds say everything this would.
        let mut plan = Forgotten {
            already,
            ..Forgotten::default()
        };
        for (target, forget) in &items {
            plan.targets.push(*target);
            let base = self
                .effective_operation(target)?
                .or_else(|| self.creation_base(target))
                .ok_or(ForgetError::MissingQuoted { document: *target })?;
            let mut document = base.clone();
            document.forgets = Some(*target);
            // Decision 0031: a forgetting document states no result. The
            // base's result names the destroyed state, and a digest of
            // destroyed content would confirm a guess at it.
            document.result = None;
            for (operation, item) in forget {
                let held = &mut document.operations[*operation].items[*item];
                if !held.forgotten {
                    *held = held.forgetting();
                }
            }
            let mut said = base;
            said.forgets = document.forgets;
            if document != said {
                plan.writes.push(document);
            }
        }

        // Every file whose bytes are a destroyed digest, found by content as
        // everything in a store is.
        let files = self.filesystem();
        for path in files_claiming(files, &self.root, OPERATIONS_DIR, &OPERATION_SUFFIXES)?
            .into_iter()
            .chain(payload_files(files, &self.root)?)
        {
            // Decision 0043: found by content, and content is what it hashes
            // to — so the bytes about to be destroyed are not held in order to
            // decide that they should be.
            let id =
                crate::fs::digest_of(files, &path).map_err(|error| StoreError::io(&path, error))?;
            if plan.targets.contains(&id) {
                plan.destroys.push(self.relative(&path));
            }
        }
        Ok(plan)
    }

    /// Forget a span: write the stand-ins, then destroy the originals.
    ///
    /// In that order, so an interruption leaves a store holding both a
    /// document and a forgetting document naming it — the state `check`
    /// calls resurrection and syncing already produces — rather than a store
    /// that destroyed bytes and recorded nothing about them.
    pub fn forget(&mut self, forgetting: &Forgetting) -> Result<Forgotten, ForgetError> {
        let plan = self.forget_plan(forgetting)?;
        for document in &plan.writes {
            self.insert_operation(document)?;
        }
        for relative in &plan.destroys {
            let path = self.root.join(relative);
            self.filesystem()
                .remove_file(&path)
                .map_err(|error| StoreError::io(&path, error))?;
        }
        for target in &plan.targets {
            self.catalogue_mut()?.remove(target);
        }
        // The payload index maps digests to paths that may just have gone.
        self.forget_catalogue();
        // Decision 0014 destroys bytes, and `cache/` is where copies of them
        // would be. Everything there is replayable, so this loses nothing
        // that forgetting was not meant to take.
        self.clear_cache();
        remove_empty_directories(self.filesystem(), &self.root.join(OPERATIONS_DIR))?;
        Ok(plan)
    }

    /// Every item every revision ever wrote to one file, quotes and all.
    fn quotes_over(
        &self,
        documents: &[(RevisionId, &crate::format::RevisionDocument)],
        file: &FileId,
    ) -> Result<Vec<Quoted>, ForgetError> {
        let held = self.effective_for(documents, file)?;
        let events: Vec<merge::Event<'_>> = documents
            .iter()
            .map(|(revision, document)| {
                let parents = document.parents.iter().copied().collect();
                match held.get(revision) {
                    Some(stated) => stated.event(*revision, parents),
                    None => merge::Event::nothing(*revision, parents),
                }
            })
            .collect();
        Ok(merge::quotes(events)?)
    }

    /// The creation document standing behind a `text` payload digest, if the
    /// digest is one.
    fn creation_base(&self, target: &RevisionId) -> Option<OperationDocument> {
        let named_by = self
            .iter()
            .find(|(_, document)| document.text.values().any(|payload| payload == target))
            .map(|(id, _)| *id)?;
        self.creation_for(target, named_by).ok().flatten()
    }
}

/// Why nothing was forgotten.
#[derive(Debug)]
#[non_exhaustive]
pub enum ForgetError {
    /// A span that names no lines.
    NotASpan {
        /// The first line, as given.
        first: usize,
        /// The last line, as given.
        last: usize,
    },
    /// A span past the end of the file.
    PastTheEnd {
        /// The last line asked for.
        last: usize,
        /// How many lines the file has there.
        lines: usize,
    },
    /// A file of bytes, which decision 0014 defers.
    NotLines {
        /// The file.
        file: FileId,
    },
    /// A quoted document this store holds nothing of, so there is nothing to
    /// preserve the shape of.
    MissingQuoted {
        /// The document.
        document: RevisionId,
    },
    /// The file's history could not be materialised.
    Materialise(Box<MaterialiseError>),
    /// The file's history could not be merged.
    Merge(Box<MergeError>),
    /// The store could not be read or written.
    Store(StoreError),
}

impl From<MaterialiseError> for ForgetError {
    fn from(error: MaterialiseError) -> Self {
        Self::Materialise(Box::new(error))
    }
}

impl From<MergeError> for ForgetError {
    fn from(error: MergeError) -> Self {
        Self::Merge(Box::new(error))
    }
}

impl From<StoreError> for ForgetError {
    fn from(error: StoreError) -> Self {
        Self::Store(error)
    }
}

impl fmt::Display for ForgetError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ForgetError::NotASpan { first, last } => write!(
                f,
                "lines {first}..{last} name no span: lines count from 1, and \
                 the last is not before the first"
            ),
            ForgetError::PastTheEnd { last, lines } => write!(
                f,
                "the file has {lines} lines there, and line {last} is past \
                 the end of it"
            ),
            ForgetError::NotLines { file } => write!(
                f,
                "the file {file} is bytes rather than lines, and forgetting \
                 part of a file that has no items is not built; \
                 decision 0014 defers it"
            ),
            ForgetError::MissingQuoted { document } => write!(
                f,
                "the span is quoted in {document}, which this store does not \
                 hold yet; forgetting preserves a document's shape, and the \
                 shape has not arrived"
            ),
            ForgetError::Materialise(error) => error.fmt(f),
            ForgetError::Merge(error) => error.fmt(f),
            ForgetError::Store(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for ForgetError {}
