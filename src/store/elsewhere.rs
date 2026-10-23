//! Text whose content is held elsewhere.
//!
//! Decision 0089. A copy that fetched the history without the content, or the
//! content of one line, holds every revision and not every document those
//! revisions name. A file of lines is its base payload and every operation
//! document after it, so reading one at a revision needs all of them, and a
//! store missing any is a store that cannot read that file on its own.
//!
//! This answers which files those are and what each lacks, from the store as
//! it stands: nothing is remembered to make it so, as nothing is for bytes
//! held elsewhere. A command that reads a file asks it first, fetches what is
//! missing from the copy it came from, and refuses where it cannot.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::{FileId, RevisionId};
use crate::fs::Filesystem;
use crate::tree::Kind;

use super::{MaterialiseError, Store, StoreError};

/// The files of lines at some revisions whose content this store does not
/// hold whole, by the path each has there, with the digests each lacks.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct TextElsewhere {
    /// Path to the payloads and operation documents it lacks.
    pub files: BTreeMap<String, BTreeSet<RevisionId>>,
}

impl TextElsewhere {
    /// Whether every file asked about is held whole.
    pub fn is_empty(&self) -> bool {
        self.files.is_empty()
    }

    /// Every digest lacked, once.
    pub fn digests(&self) -> BTreeSet<RevisionId> {
        self.files.values().flatten().copied().collect()
    }

    /// The paths, in order.
    pub fn paths(&self) -> impl Iterator<Item = &str> {
        self.files.keys().map(String::as_str)
    }
}

impl<F: Filesystem> Store<F> {
    /// The files of lines at `revisions` this store cannot read on its own,
    /// and the content each lacks.
    ///
    /// `paths`, where given, narrows the question to the files at or beneath
    /// those paths. A file's content is taken to be every payload a `text`
    /// line names for it and every document an `edit` line names for it,
    /// across the whole ancestry of the revision. That is the chain a replay
    /// reads, and, at a merge, every side's: more than the chain of one line,
    /// and never less. A digest something here forgets is not lacked, since
    /// what stands in for it is what a reader reads.
    pub fn text_elsewhere(
        &self,
        revisions: &[RevisionId],
        paths: Option<&[String]>,
    ) -> Result<TextElsewhere, MaterialiseError> {
        let covers = |path: &str| match paths {
            None => true,
            Some(paths) => paths.iter().any(|named| {
                named.is_empty()
                    || path == named
                    || path
                        .strip_prefix(named.as_str())
                        .is_some_and(|rest| rest.starts_with('/'))
            }),
        };
        // Which files to ask about, and the path each has at the revision
        // that names it.
        let mut asked: BTreeMap<FileId, BTreeSet<String>> = BTreeMap::new();
        for revision in revisions {
            let tree = self.tree(revision)?;
            for (file, entry) in tree.entries() {
                if entry.kind == Kind::Lines && covers(&entry.path) {
                    asked.entry(*file).or_default().insert(entry.path.clone());
                }
            }
        }
        let ids: BTreeSet<FileId> = asked.keys().copied().collect();
        let mut elsewhere = TextElsewhere::default();
        for (file, missing) in self.text_lacking(revisions, &ids)? {
            for path in &asked[&file] {
                elsewhere
                    .files
                    .entry(path.clone())
                    .or_default()
                    .extend(missing.iter().copied());
            }
        }
        Ok(elsewhere)
    }

    /// Of `files`, those whose content at `revisions` this store lacks part
    /// of, with the digests each lacks: [`Store::text_elsewhere`] by
    /// identifier rather than by path.
    pub(crate) fn text_lacking(
        &self,
        revisions: &[RevisionId],
        files: &BTreeSet<FileId>,
    ) -> Result<BTreeMap<FileId, BTreeSet<RevisionId>>, MaterialiseError> {
        if files.is_empty() {
            return Ok(BTreeMap::new());
        }
        // One walk down the ancestry of every revision asked about, taking
        // what each names for the files asked about.
        let mut named: BTreeMap<FileId, BTreeSet<RevisionId>> = BTreeMap::new();
        let mut seen: BTreeSet<RevisionId> = BTreeSet::new();
        let mut walking: Vec<RevisionId> = revisions.to_vec();
        while let Some(id) = walking.pop() {
            if !seen.insert(id) {
                continue;
            }
            let Some(document) = self.get(&id).map_err(MaterialiseError::unreadable)? else {
                continue;
            };
            for (file, digest) in document.text.iter().chain(&document.edited) {
                if files.contains(file) {
                    named.entry(*file).or_default().insert(*digest);
                }
            }
            walking.extend(document.parents.iter().copied());
        }

        let mut lacked: BTreeMap<RevisionId, bool> = BTreeMap::new();
        let mut lacking = BTreeMap::new();
        for (file, digests) in named {
            let mut missing = BTreeSet::new();
            for digest in digests {
                let lacks = match lacked.get(&digest) {
                    Some(lacks) => *lacks,
                    None => {
                        let lacks = self
                            .lacks_content(&digest)
                            .map_err(MaterialiseError::unreadable)?;
                        lacked.insert(digest, lacks);
                        lacks
                    }
                };
                if lacks {
                    missing.insert(digest);
                }
            }
            if !missing.is_empty() {
                lacking.insert(file, missing);
            }
        }
        Ok(lacking)
    }

    /// Whether this store lacks one payload or document a revision names for
    /// a file of lines: neither it nor anything standing in for it is here.
    ///
    /// Where the catalogue places it, it is held, and reading it is where a
    /// damaged file is found. Where it does not, a miss proves nothing
    /// (decision 0079), so the slower questions are asked.
    pub(super) fn lacks_content(&self, digest: &RevisionId) -> Result<bool, StoreError> {
        if self.catalogue()?.at(digest).is_some() {
            return Ok(false);
        }
        if self.effective_body(digest)?.is_some() {
            return Ok(false);
        }
        self.held_elsewhere(digest)
    }
}
