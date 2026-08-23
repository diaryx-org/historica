//! Receiving immutable history from another store.
//!
//! Decision 0029: copying a store is already transport. Receiving is the
//! narrower operation that plain copying cannot perform safely when both
//! stores changed: union documents by content identity, preserve mutable
//! disagreements, and comply with forgetting documents.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::io;
use std::path::{Path, PathBuf};

use crate::core::RevisionId;
use crate::format::digest;
use crate::fs::{Filesystem, read_to_string};
use crate::working::{DEFAULT_SKIPPED, SKIPPED_FILE, Skipped};

use super::{
    Name, OPERATION_SUFFIX, OPERATION_SUFFIXES, OPERATIONS_DIR, REVISION_SUFFIX, Store, StoreError,
    files_claiming,
};

/// One mutable value two stores disagree about.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MutableConflict {
    /// One bookmark name points at two things.
    Name {
        /// The bookmark.
        name: String,
        /// What the receiving store says.
        here: Name,
        /// What the source store says.
        there: Name,
    },
    /// Both stores carry non-default, differing rule files.
    Skipped,
}

/// A content-identity union worked out before anything is written.
#[derive(Debug, Clone, Default)]
pub struct ReceivePlan {
    revisions: Vec<RevisionId>,
    operations: Vec<RevisionId>,
    payloads: Vec<RevisionId>,
    names: BTreeMap<String, Name>,
    skipped: Option<String>,
    forgotten: BTreeSet<RevisionId>,
    destroys: BTreeSet<RevisionId>,
    conflicts: Vec<MutableConflict>,
}

impl ReceivePlan {
    /// Revision documents the receiver lacks.
    pub fn revisions(&self) -> &[RevisionId] {
        &self.revisions
    }

    /// Operation and forgetting documents the receiver lacks.
    pub fn operations(&self) -> &[RevisionId] {
        &self.operations
    }

    /// Whole-content payloads the receiver lacks.
    pub fn payloads(&self) -> &[RevisionId] {
        &self.payloads
    }

    /// Bookmarks that exist only in the source.
    pub fn names(&self) -> &BTreeMap<String, Name> {
        &self.names
    }

    /// Whether the source rule file will replace an absent or default one.
    pub fn receives_skipped(&self) -> bool {
        self.skipped.is_some()
    }

    /// Forgotten originals that will be destroyed.
    pub fn destroys(&self) -> &BTreeSet<RevisionId> {
        &self.destroys
    }

    /// Mutable disagreements that make applying this plan unsafe.
    pub fn conflicts(&self) -> &[MutableConflict] {
        &self.conflicts
    }

    /// Whether applying this plan would change the receiver.
    pub fn is_empty(&self) -> bool {
        self.revisions.is_empty()
            && self.operations.is_empty()
            && self.payloads.is_empty()
            && self.names.is_empty()
            && self.skipped.is_none()
            && self.destroys.is_empty()
    }
}

/// What one receive changed.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Received {
    /// Revision documents copied.
    pub revisions: usize,
    /// Operation and forgetting documents copied.
    pub operations: usize,
    /// Whole-content payloads copied.
    pub payloads: usize,
    /// Bookmarks copied.
    pub names: usize,
    /// Whether `skipped.txt` was copied.
    pub skipped: bool,
    /// Original operation documents or payloads destroyed in compliance with
    /// received forgetting documents.
    pub destroyed: usize,
}

impl<F: Filesystem> Store<F> {
    /// Work out what receiving `source` would add, without writing anything.
    pub fn receive_plan<G: Filesystem>(
        &self,
        source: &Store<G>,
        join_unrelated: bool,
    ) -> Result<ReceivePlan, ReceiveError> {
        if !Store::check_on(self.filesystem(), self.root()).is_ok() {
            return Err(ReceiveError::BrokenStore { source: false });
        }
        if !Store::check_on(source.filesystem(), source.root()).is_ok() {
            return Err(ReceiveError::BrokenStore { source: true });
        }
        if !join_unrelated && !related(self, source) {
            return Err(ReceiveError::Unrelated);
        }

        // Each store's operation documents, read once: every filter below
        // asks what one of them holds, and none can call `?` inside a closure.
        let held: BTreeSet<RevisionId> = self.operations()?.map(|(id, _)| *id).collect();
        let forgotten: BTreeSet<RevisionId> = self
            .operations()?
            .chain(source.operations()?)
            .filter_map(|(_, document)| document.forgets)
            .collect();
        let mut plan = ReceivePlan {
            forgotten,
            ..ReceivePlan::default()
        };

        plan.revisions = source
            .iter()
            .filter_map(|(id, _)| self.get(id).is_none().then_some(*id))
            .collect();
        plan.operations = source
            .operations()?
            .filter_map(|(id, _)| {
                (!held.contains(id) && !plan.forgotten.contains(id)).then_some(*id)
            })
            .collect();

        let ours = self.payloads()?;
        plan.destroys = plan
            .forgotten
            .iter()
            .filter(|id| held.contains(id) || ours.contains_key(id))
            .copied()
            .collect();
        plan.payloads = source
            .payloads()?
            .into_keys()
            .filter(|id| !ours.contains_key(id) && !plan.forgotten.contains(id))
            .collect();

        for (name, there) in source.names() {
            match self.name(name) {
                None => {
                    plan.names.insert(name.clone(), *there);
                }
                Some(here) if here == *there => {}
                Some(here) => plan.conflicts.push(MutableConflict::Name {
                    name: name.clone(),
                    here,
                    there: *there,
                }),
            }
        }

        let here = optional_read(self.filesystem(), &self.root().join(SKIPPED_FILE))?;
        let there = optional_read(source.filesystem(), &source.root().join(SKIPPED_FILE))?;
        match (here.as_deref(), there.as_deref()) {
            (_, None) => {}
            (Some(here), Some(there)) if here == there => {}
            (None, Some(there)) => plan.skipped = Some(there.to_owned()),
            (Some(here), Some(there)) if here == DEFAULT_SKIPPED => {
                plan.skipped = Some(there.to_owned());
            }
            (Some(_), Some(there)) if there == DEFAULT_SKIPPED => {}
            (Some(_), Some(_)) => plan.conflicts.push(MutableConflict::Skipped),
        }

        Ok(plan)
    }

    /// Receive `source` according to the same plan a dry run can inspect.
    pub fn receive<G: Filesystem>(
        &mut self,
        source: &Store<G>,
        join_unrelated: bool,
    ) -> Result<Received, ReceiveError> {
        let plan = self.receive_plan(source, join_unrelated)?;
        if !plan.conflicts.is_empty() {
            return Err(ReceiveError::Mutable {
                conflicts: plan.conflicts,
            });
        }

        let mut received = Received::default();
        // Content first and revisions last, so an interruption understates what
        // is reachable rather than leaving a new revision naming bytes not yet
        // delivered.
        for id in &plan.payloads {
            let bytes = source
                .payload(id)?
                .expect("a payload named by the plan remains in the open source");
            self.insert_payload_at(&bytes, &id.to_string())?;
            received.payloads += 1;
        }
        for id in &plan.operations {
            let document = source
                .operation(id)?
                .expect("an operation named by the plan remains in the open source")
                .clone();
            self.insert_operation_at(&document, &format!("{id}{OPERATION_SUFFIX}"))?;
            received.operations += 1;
        }
        received.destroyed = self.comply_with_forgetting(&plan.destroys)?;
        for id in &plan.revisions {
            let document = source
                .get(id)
                .expect("a revision named by the plan remains in the open source");
            self.insert_at(document, &format!("{id}{REVISION_SUFFIX}"))?;
            received.revisions += 1;
        }
        for (name, target) in &plan.names {
            self.set_name(name, *target)?;
            received.names += 1;
        }
        if let Some(text) = &plan.skipped {
            let path = self.root.join(SKIPPED_FILE);
            let parsed = Skipped::parse(text).map_err(|error| StoreError::MalformedSkipped {
                file: path.clone(),
                error,
            })?;
            self.files
                .write(&path, text.as_bytes())
                .map_err(|error| StoreError::io(&path, error))?;
            self.skipped = parsed;
            received.skipped = true;
        }
        Ok(received)
    }

    /// Make every forgetting document this store holds effective on disk.
    fn comply_with_forgetting(
        &mut self,
        forgotten: &BTreeSet<RevisionId>,
    ) -> Result<usize, StoreError> {
        let mut destroys: BTreeSet<PathBuf> = BTreeSet::new();
        for path in files_claiming(
            self.filesystem(),
            &self.root,
            OPERATIONS_DIR,
            &OPERATION_SUFFIXES,
        )? {
            let bytes = self
                .files
                .read(&path)
                .map_err(|error| StoreError::io(&path, error))?;
            if forgotten.contains(&digest(&bytes)) {
                destroys.insert(path);
            }
        }
        for target in forgotten {
            if let Some(path) = self.payload_path(target)? {
                destroys.insert(path.to_path_buf());
            }
        }
        for path in &destroys {
            self.files
                .remove_file(path)
                .map_err(|error| StoreError::io(path, error))?;
        }
        for target in forgotten {
            self.bodies_mut()?.operations.remove(target);
        }
        self.forget_payloads();
        super::prune::remove_empty_directories(self.filesystem(), &self.root.join(OPERATIONS_DIR))?;
        Ok(destroys.len())
    }
}

/// Empty stores may be seeded. Otherwise one shared document or direct graph
/// edge is evidence that these are partial views of one history.
fn related<F: Filesystem, G: Filesystem>(here: &Store<F>, there: &Store<G>) -> bool {
    if here.is_empty() || there.is_empty() {
        return true;
    }
    let ours: BTreeSet<RevisionId> = here.iter().map(|(id, _)| *id).collect();
    let theirs: BTreeSet<RevisionId> = there.iter().map(|(id, _)| *id).collect();
    if !ours.is_disjoint(&theirs) {
        return true;
    }
    there.iter().any(|(_, document)| {
        document
            .parents
            .iter()
            .chain(document.supersedes.iter())
            .any(|id| ours.contains(id))
    }) || here.iter().any(|(_, document)| {
        document
            .parents
            .iter()
            .chain(document.supersedes.iter())
            .any(|id| theirs.contains(id))
    })
}

fn optional_read<F: Filesystem>(files: &F, path: &Path) -> Result<Option<String>, StoreError> {
    match read_to_string(files, path) {
        Ok(text) => Ok(Some(text)),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(error) => Err(StoreError::io(path, error)),
    }
}

/// Why one store could not receive another.
#[derive(Debug)]
pub enum ReceiveError {
    /// One side fails `check`.
    BrokenStore {
        /// Whether the broken side is the source rather than the receiver.
        source: bool,
    },
    /// Two nonempty stores share no revision or direct graph edge.
    Unrelated,
    /// Mutable files disagree and were left untouched.
    Mutable {
        /// Every disagreement, in stable order.
        conflicts: Vec<MutableConflict>,
    },
    /// Reading or writing a store failed.
    Store(StoreError),
}

impl From<StoreError> for ReceiveError {
    fn from(error: StoreError) -> Self {
        Self::Store(error)
    }
}

impl fmt::Display for ReceiveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ReceiveError::BrokenStore { source } => write!(
                f,
                "the {} store does not pass `check`; receive writes nothing \
                 until its errors are repaired",
                if *source { "source" } else { "receiving" }
            ),
            ReceiveError::Unrelated => write!(
                f,
                "these nonempty stores share no revision or graph edge; use \
                 `--join-unrelated` only if combining two histories is intended"
            ),
            ReceiveError::Mutable { conflicts } => {
                writeln!(
                    f,
                    "the stores disagree about mutable files; receive writes nothing:"
                )?;
                for conflict in conflicts {
                    match conflict {
                        MutableConflict::Name { name, here, there } => {
                            writeln!(f, "  name {name}: here `{here}`, there `{there}`")?;
                        }
                        MutableConflict::Skipped => {
                            writeln!(f, "  skipped.txt differs")?;
                        }
                    }
                }
                Ok(())
            }
            ReceiveError::Store(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for ReceiveError {}
