//! `prune`: the disk half of decision 0013.
//!
//! Abandoning is a fact recorded in the graph; pruning is disk. Exactly two
//! kinds of file may go: a revision document that is superseded by a revision
//! this store keeps and named as a parent by nothing it keeps, and a content
//! document nothing kept names. Nothing else, ever — a head no bookmark names
//! is work whose author has not given it a name, not garbage.
//!
//! Pruning is local, manual, and printed. It does not propagate, it is not
//! secrecy, and it is the undo history, all three of which decision 0013 says
//! in as many words.

use std::collections::BTreeSet;
use std::io;
use std::path::{Path, PathBuf};

use crate::core::RevisionId;
use crate::fs::{Entry, Filesystem};

use super::{
    OPERATION_SUFFIXES, OPERATIONS_DIR, REVISION_SUFFIXES, REVISIONS_DIR, Store, StoreError,
    files_claiming, payload_files,
};

/// What pruning removed, or would remove.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct Pruned {
    /// Revision documents gone, by digest.
    pub revisions: Vec<RevisionId>,
    /// Operation documents gone, by digest.
    pub operations: Vec<RevisionId>,
    /// Payloads gone, by digest.
    pub payloads: Vec<RevisionId>,
    /// Every file removed, relative to the store root, in removal order.
    pub files: Vec<PathBuf>,
}

impl Pruned {
    /// Whether pruning touched, or would touch, nothing.
    pub fn is_empty(&self) -> bool {
        self.files.is_empty()
    }
}

impl<F: Filesystem> Store<F> {
    /// What `prune` would remove, without removing anything.
    ///
    /// `prune` acts on exactly this, so `--dry-run` and the real thing can
    /// never describe different files.
    pub fn prunable(&self) -> Result<Pruned, StoreError> {
        let deletable = self.deletable_revisions();

        // A reference count over digests, per decision 0013: two revisions
        // with byte-identical edits share one document, so what is kept is
        // whatever any kept revision names, however many name it.
        let mut referenced: BTreeSet<RevisionId> = BTreeSet::new();
        for (id, held) in &self.documents {
            if deletable.contains(id) {
                continue;
            }
            // What a revision named is a tree fact, so this is one of the
            // callers decision 0061 leaves paying for the whole document.
            let document = held.whole()?;
            referenced.extend(document.edited.values().copied());
            referenced.extend(document.text.values().copied());
            referenced.extend(document.bytes.values().copied());
        }
        // A forgetting document is named indirectly: the revision's `edit`
        // line still names the destroyed digest, and the forgetting document
        // is what answers for it (decision 0014). It stays while what it
        // stands in for is named.
        for (id, body) in self.bodies()? {
            if let Some(forgets) = body.forgets()
                && referenced.contains(&forgets)
            {
                referenced.insert(id);
            }
        }

        // Files are found by content, never by name: two copies of one
        // deleted revision are both that revision, wherever they sit and
        // whatever they are called.
        let mut pruned = Pruned::default();
        let files = self.filesystem();
        for path in files_claiming(files, &self.root, REVISIONS_DIR, &REVISION_SUFFIXES)? {
            // Decision 0043: what a file hashes to is what it is, and nothing
            // here wants the file. Every one of these three loops reads every
            // byte of the store and keeps none of it.
            let id =
                crate::fs::digest_of(files, &path).map_err(|error| StoreError::io(&path, error))?;
            if deletable.contains(&id) {
                push_unique(&mut pruned.revisions, id);
                pruned.files.push(self.relative(&path));
            }
        }
        for path in files_claiming(files, &self.root, OPERATIONS_DIR, &OPERATION_SUFFIXES)? {
            let id =
                crate::fs::digest_of(files, &path).map_err(|error| StoreError::io(&path, error))?;
            if !referenced.contains(&id) {
                push_unique(&mut pruned.operations, id);
                pruned.files.push(self.relative(&path));
            }
        }
        for path in payload_files(files, &self.root)? {
            let id =
                crate::fs::digest_of(files, &path).map_err(|error| StoreError::io(&path, error))?;
            if !referenced.contains(&id) {
                push_unique(&mut pruned.payloads, id);
                pruned.files.push(self.relative(&path));
            }
        }
        Ok(pruned)
    }

    /// Remove what decision 0013 says may go, and nothing else.
    ///
    /// `cache/` is not this command's business: it is disposable by decision
    /// 0003 and removable with `rm -r`, and a command that deleted both would
    /// blur the one distinction 0013 exists to keep.
    pub fn prune(&mut self) -> Result<Pruned, StoreError> {
        let pruned = self.prunable()?;
        for relative in &pruned.files {
            let path = self.root.join(relative);
            self.filesystem()
                .remove_file(&path)
                .map_err(|error| StoreError::io(&path, error))?;
        }
        for id in &pruned.revisions {
            self.documents.remove(id);
        }
        for id in &pruned.operations {
            self.catalogue_mut()?.remove(id);
        }
        // The payload index maps digests to paths that may just have gone;
        // it is derived, so it is rebuilt on next need rather than repaired.
        self.forget_catalogue();
        // So is `cache/`, and pruning has just deleted content some of it may
        // hold. Nothing there is reported, because nothing there is lost.
        self.clear_cache();
        for directory in [REVISIONS_DIR, OPERATIONS_DIR] {
            remove_empty_directories(self.filesystem(), &self.root.join(directory))?;
        }
        Ok(pruned)
    }

    /// Revision documents decision 0013 lets go of, to a fixpoint.
    ///
    /// A fixpoint rather than one pass, because deleting one revision can
    /// orphan the next: a superseded run clears in a single pruning, which is
    /// what makes running it twice a no-op. One guard is not in 0013's words
    /// but is in its reasoning: a successor whose `supersedes` names a
    /// revision this store keeps stays, because the evidence of supersession
    /// lives on the successor — 0001 put it there — and deleting it would
    /// resurrect the kept revision as current work.
    fn deletable_revisions(&self) -> BTreeSet<RevisionId> {
        let mut kept: BTreeSet<RevisionId> = self.documents.keys().copied().collect();
        loop {
            let mut shrank = false;
            for id in kept.clone() {
                let revision = self.revision(&id).expect("a revision this store holds");
                let superseded = kept.iter().any(|keeper| {
                    self.revision(keeper)
                        .is_some_and(|keeper| keeper.supersedes.contains(&id))
                });
                let stood_on = kept.iter().any(|keeper| {
                    self.revision(keeper)
                        .is_some_and(|keeper| keeper.parents.contains(&id))
                });
                let evidence = revision.supersedes.iter().any(|named| kept.contains(named));
                if superseded && !stood_on && !evidence {
                    kept.remove(&id);
                    shrank = true;
                }
            }
            if !shrank {
                return self
                    .documents
                    .keys()
                    .filter(|id| !kept.contains(id))
                    .copied()
                    .collect();
            }
        }
    }

    /// One of this store's paths, said as `prune` and `forget` print it.
    pub(super) fn relative(&self, path: &Path) -> PathBuf {
        path.strip_prefix(&self.root)
            .map(Path::to_path_buf)
            .unwrap_or_else(|_| path.to_path_buf())
    }
}

/// The digest, once, however many files hold the same bytes.
fn push_unique(ids: &mut Vec<RevisionId>, id: RevisionId) {
    if !ids.contains(&id) {
        ids.push(id);
    }
}

/// Remove directories pruning emptied, leaving `directory` itself.
///
/// A directory is presentation exactly as a filename is, and one that held
/// only what pruning removed now presents nothing. Symbolic links are not
/// descended into, on `walk`'s reasoning.
pub(super) fn remove_empty_directories<F: Filesystem + ?Sized>(
    files: &F,
    directory: &Path,
) -> Result<bool, StoreError> {
    let entries = match files.entries(directory) {
        Ok(entries) => entries,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(true),
        Err(error) => return Err(StoreError::io(directory, error)),
    };
    let mut empty = true;
    for Entry { path, kind } in entries {
        if kind.is_directory() && remove_empty_directories(files, &path)? {
            files
                .remove_directory(&path)
                .map_err(|error| StoreError::io(&path, error))?;
        } else {
            empty = false;
        }
    }
    Ok(empty)
}
