//! Receiving immutable history from another store.
//!
//! Decision 0029: copying a store is already transport. Receiving is the
//! narrower operation that plain copying cannot perform safely when both
//! stores changed: union documents by content identity, preserve mutable
//! disagreements, and comply with forgetting documents.
//!
//! Decision 0053 adds the directories this store does not read. A reserved
//! directory travels by its class: `claims/` unions add-only, `trust/` never
//! crosses, and a directory nobody reserved is left alone in both directions.
//! Nothing here opens one of those files, so the union is a union of names —
//! which is exactly what the class promises the names support.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::PathBuf;

use crate::core::RevisionId;
use crate::fs::Filesystem;
use crate::working::Rule;

use super::{
    Body, Name, OPERATION_SUFFIX, OPERATION_SUFFIXES, OPERATIONS_DIR, REVISION_SUFFIX, Store,
    StoreError, files_claiming,
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
}

/// A content-identity union worked out before anything is written.
#[derive(Debug, Clone, Default)]
pub struct ReceivePlan {
    revisions: Vec<RevisionId>,
    documents: Vec<RevisionId>,
    payloads: Vec<RevisionId>,
    names: BTreeMap<String, Name>,
    skipped: Vec<Rule>,
    reserved: Vec<String>,
    forgotten: BTreeSet<RevisionId>,
    destroys: BTreeSet<RevisionId>,
    conflicts: Vec<MutableConflict>,
}

impl ReceivePlan {
    /// Revision documents the receiver lacks.
    pub fn revisions(&self) -> &[RevisionId] {
        &self.revisions
    }

    /// Content documents the receiver lacks, in either grammar.
    ///
    /// Decision 0032: an `edit` line names an operation document or a
    /// resolution, so a transfer that carried only the first grammar would
    /// deliver a merge whose file cannot be read — and then say, correctly,
    /// that there was nothing left to send.
    pub fn documents(&self) -> &[RevisionId] {
        &self.documents
    }

    /// Whole-content payloads the receiver lacks.
    pub fn payloads(&self) -> &[RevisionId] {
        &self.payloads
    }

    /// Bookmarks that exist only in the source.
    pub fn names(&self) -> &BTreeMap<String, Name> {
        &self.names
    }

    /// Rules the source states and the receiver does not.
    ///
    /// Decision 0045: a union, never a conflict. Two replicas that each wrote
    /// a rule were never disagreeing — `skips` asks every rule, so both apply
    /// — and the container that made it look like a disagreement is gone.
    pub fn skipped(&self) -> &[Rule] {
        &self.skipped
    }

    /// Files of another tool's the source holds under a name this store has
    /// no file under, relative to the store root.
    ///
    /// Decision 0053: a reserved directory of the `travels-and-unions` class
    /// unions add-only. A name both stores hold is left as this store has it
    /// and never read, because the rule that named it is a grammar 0046
    /// promised historica would not learn.
    pub fn reserved(&self) -> &[String] {
        &self.reserved
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
            && self.documents.is_empty()
            && self.payloads.is_empty()
            && self.names.is_empty()
            && self.skipped.is_empty()
            && self.reserved.is_empty()
            && self.destroys.is_empty()
    }
}

/// What one receive changed.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Received {
    /// Revision documents copied.
    pub revisions: usize,
    /// Content documents copied, in either grammar.
    pub documents: usize,
    /// Whole-content payloads copied.
    pub payloads: usize,
    /// Bookmarks copied.
    pub names: usize,
    /// Rules copied.
    pub skipped: usize,
    /// Files another tool wrote, unioned by their class (decision 0053).
    pub reserved: usize,
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

        // What each store holds in `operations/`, read once: every filter
        // below asks what one of them holds, and none can call `?` inside a
        // closure. Both grammars, because decision 0032 gave that directory
        // two and a transfer is a question about the directory.
        let held: BTreeSet<RevisionId> = self.bodies()?.into_keys().collect();
        // What either store forgets, in either grammar: decision 0014 reaches
        // a resolution's minted items too, and a stand-in for one is written
        // as a resolution because a stand-in has the shape of what it stands
        // in for.
        let forgotten: BTreeSet<RevisionId> = self
            .bodies()?
            .into_iter()
            .chain(source.bodies()?)
            .filter_map(|(_, body)| body.forgets())
            .collect();
        let mut plan = ReceivePlan {
            forgotten,
            ..ReceivePlan::default()
        };

        plan.revisions = source
            .iter()
            .filter_map(|(id, _)| self.get(id).is_none().then_some(*id))
            .collect();
        plan.documents = source
            .bodies()?
            .into_keys()
            .filter(|id| !held.contains(id) && !plan.forgotten.contains(id))
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

        // Decision 0045: rules union like the documents do, because a set is
        // what the file always held. What replaced three branches guessing
        // whether a rule file was really stated or merely what `init` left is
        // this line, and the guess was only ever a property of the container.
        for rule in source.skipped().rules() {
            if !self.skipped.rules().any(|had| had == rule) {
                plan.skipped.push(rule.clone());
            }
        }

        // Decision 0053: names, compared as names. A file the source holds
        // under a name this store already has is not a disagreement to report
        // and not a file to overwrite — it is what add-only means for a
        // directory whose grammar nothing here reads.
        let ours: BTreeSet<String> = self.travelling_files()?.into_iter().collect();
        plan.reserved = source
            .travelling_files()?
            .into_iter()
            .filter(|label| !ours.contains(label))
            .collect();

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
        for id in &plan.documents {
            // Written back in the grammar it was read in. A resolution
            // rewritten as anything else would be a different digest, and the
            // `edit` line naming it would stop finding it.
            match source
                .body(id)?
                .expect("a document named by the plan remains in the open source")
            {
                Body::Operation(document) => {
                    self.insert_operation_at(&document, &format!("{id}{OPERATION_SUFFIX}"))?;
                }
                Body::Resolution(document) => {
                    self.insert_resolution_at(&document, &format!("{id}{OPERATION_SUFFIX}"))?;
                }
            }
            received.documents += 1;
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
        received.skipped = self.add_skipped(&plan.skipped)?.len();
        // Add-only, and the plan is worked out from a listing rather than
        // held under a lock, so a name that appeared in between is a name
        // this store already has: `carry_travelling` reports it and nothing
        // is overwritten.
        for label in &plan.reserved {
            let bytes = source.travelling_file(label)?;
            if self.carry_travelling(label, &bytes)? {
                received.reserved += 1;
            }
        }
        Ok(received)
    }

    /// Make every forgetting document this store holds effective on disk.
    ///
    /// Shared with `export`, which complies where this does — between the
    /// documents and the revisions — because an assembled copy that kept the
    /// original a stand-in arrived for would be the one copy a redaction never
    /// reached (decisions 0014, 0052).
    pub(super) fn comply_with_forgetting(
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
            // Decision 0043: the question is which digest this file is, and
            // the answer arrives in pieces.
            let id = crate::fs::digest_of(&self.files, &path)
                .map_err(|error| StoreError::io(&path, error))?;
            if forgotten.contains(&id) {
                destroys.insert(path);
            }
        }
        for target in forgotten {
            if let Some(path) = self.catalogue()?.at(target).map(|filed| filed.path.clone()) {
                destroys.insert(self.root.join(path));
            }
        }
        for path in &destroys {
            self.files
                .remove_file(path)
                .map_err(|error| StoreError::io(path, error))?;
        }
        for target in forgotten {
            self.catalogue_mut()?.remove(target);
        }
        self.forget_catalogue();
        super::prune::remove_empty_directories(self.filesystem(), &self.root.join(OPERATIONS_DIR))?;
        Ok(destroys.len())
    }
}

/// Empty stores may be seeded. Otherwise one shared document or direct graph
/// edge is evidence that these are partial views of one history.
///
/// Decision 0052 asks the same question of an export's destination, on the
/// same terms: a directory holding a store this one is unrelated to is not a
/// copy to update.
pub(super) fn related<F: Filesystem, G: Filesystem>(here: &Store<F>, there: &Store<G>) -> bool {
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
                    }
                }
                Ok(())
            }
            ReceiveError::Store(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for ReceiveError {}
