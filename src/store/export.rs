//! `export`: the copy a person takes away.
//!
//! Decision 0042. Copying a store is already transport, and there is no
//! directory on disk whose bytes are *the thing a stranger should have*: the
//! folder holds unrecorded edits and every file a `skip` rule exists to keep
//! private, and `history/` alone holds bookmarks, rules, and a cache that are
//! nobody's but the exporter's. So the sending half is not a protocol. It is
//! a command that **builds that directory**, and then any pipe carries it.
//!
//! What is built is a fresh repository: the folder as the target revision has
//! it, and the target's own ancestry, closed. Both halves are machinery that
//! already exists — [`crate::update`] materialises the folder, and the writing
//! is [`Store::insert_at`] and its neighbours under the names
//! [`crate::naming`] gives them — pointed at a second [`Filesystem`], which is
//! the shape [`Store::receive`] already crosses two filesystems with, run in
//! the other direction. Nothing unrecorded and nothing skipped can appear in
//! the copy, because the copy is assembled rather than mirrored.
//!
//! # What travels, and what does not
//!
//! Every ancestor of the target, every operation document, resolution and
//! payload those revisions name, and every forgetting document that touches
//! any of it — decision 0014 always travels, or a copy would resurrect what a
//! redaction destroyed. Not `names/` and not `cache/`, which are the exporter's
//! bookmarks and nobody's cache. `historica.txt` and `format.txt` are written
//! fresh, because decision 0021 promises the copy explains itself to whoever
//! opens it.
//!
//! Every **shared** rule travels, which is decision 0051 superseding the half
//! of 0042 that called rules the exporter's. A copy that quietly dropped
//! `skip target/` is one whose first `record` offers to record the recipient's
//! build output — the failure 0011 wrote rules to prevent, arriving because
//! the rules did not. A `private` rule stays behind, and the copy is told how
//! many did.
//!
//! A reserved directory travels by its class, which is decision 0053: whole,
//! unread, and without export learning whose it is. `claims/` is carried and
//! `trust/` is not. The directory is carried **whole** rather than filtered to
//! the claims naming exported revisions, because the filter would need a
//! grammar 0046 refused historica, and because a claim covers everything its
//! revision descends from — so the claim worth having is usually one over a
//! later head, which is exactly what such a filter would drop.
//!
//! # The supersession edge
//!
//! Ancestry closes over **parent** edges and nothing else. A revision in the
//! target's ancestry may have been rewritten by a revision that is not — an
//! amendment recorded after the moment being exported — and the export does
//! not chase it, so a copy can hold a revision whose `supersedes` line names a
//! digest it does not hold.
//!
//! That is the ordinary condition rather than a fault, and the format says so
//! from both sides. [`History::superseded`] is explicit that "a superseded
//! revision need not be present locally: the successor carries the evidence";
//! `check` has no finding for the missing predecessor, because there is
//! nothing to find; and head discovery — heads by parent edge, less whatever
//! anything supersedes — reads a dangling edge exactly as it reads a delivered
//! one. `tests/export.rs` pins all three.
//!
//! [`History::superseded`]: crate::core::History::superseded

use std::collections::BTreeSet;
use std::fmt;
use std::io;
use std::path::{Path, PathBuf};

use crate::core::RevisionId;
use crate::format::Piece;
#[cfg(feature = "disk")]
use crate::fs::Disk;
use crate::fs::Filesystem;
use crate::naming;
use crate::update::{self, UpdateError};
use crate::working::Working;

use super::{
    Body, MaterialiseError, OPERATION_SUFFIX, REVISION_SUFFIX, STORE_DIR, Store, StoreError,
};

/// What one export would write, worked out before anything is written.
///
/// [`Store::export_onto`] acts on exactly this, so a dry run and the real
/// thing can never describe different files — the promise `receive_plan`,
/// `prunable` and `forget_plan` already make.
#[derive(Debug, Clone)]
pub struct ExportPlan {
    target: RevisionId,
    revisions: Vec<RevisionId>,
    documents: Vec<RevisionId>,
    payloads: Vec<RevisionId>,
    forgetting: Vec<RevisionId>,
    paths: Vec<String>,
    rules: Vec<crate::working::Rule>,
    withheld: usize,
    reserved: Vec<String>,
}

impl ExportPlan {
    /// The revision the copy ends at, which is its only head.
    pub fn target(&self) -> RevisionId {
        self.target
    }

    /// Every revision document that travels, in digest order.
    pub fn revisions(&self) -> &[RevisionId] {
        &self.revisions
    }

    /// Every operation and resolution document those revisions name.
    pub fn documents(&self) -> &[RevisionId] {
        &self.documents
    }

    /// Every whole-content payload those revisions name.
    pub fn payloads(&self) -> &[RevisionId] {
        &self.payloads
    }

    /// Every forgetting document standing in for any of it.
    pub fn forgetting(&self) -> &[RevisionId] {
        &self.forgetting
    }

    /// Every path the copy's folder will hold, in path order.
    pub fn paths(&self) -> &[String] {
        &self.paths
    }

    /// Every rule the copy will state, which is every shared rule this store
    /// states.
    pub fn rules(&self) -> &[crate::working::Rule] {
        &self.rules
    }

    /// How many private rules stay behind.
    pub fn withheld(&self) -> usize {
        self.withheld
    }

    /// Every file of another tool's that travels, relative to the store root.
    ///
    /// Decision 0053: a reserved directory of the `travels-and-unions` class,
    /// carried whole and unread. `claims/` is the one this store reserves.
    pub fn reserved(&self) -> &[String] {
        &self.reserved
    }
}

/// What one export wrote.
#[derive(Debug, Clone)]
pub struct Exported {
    /// The repository directory that now holds a copy.
    pub root: PathBuf,
    /// The revision it ends at.
    pub target: RevisionId,
    /// Revision documents written.
    pub revisions: usize,
    /// Operation and resolution documents written.
    pub documents: usize,
    /// Payloads written.
    pub payloads: usize,
    /// Forgetting documents written.
    pub forgetting: usize,
    /// Rules carried into the copy.
    pub rules: usize,
    /// Private rules the copy was not given.
    pub withheld: usize,
    /// Files another tool wrote, carried by their class (decision 0053).
    pub reserved: usize,
    /// The paths materialised into the folder, in the order they were written.
    pub files: Vec<String>,
}

impl<F: Filesystem> Store<F> {
    /// What exporting `target` would write, without writing anything.
    pub fn export_plan(&self, target: &RevisionId) -> Result<ExportPlan, ExportError> {
        if !Store::check_on(self.filesystem(), self.root()).is_ok() {
            return Err(ExportError::BrokenStore);
        }

        // Parent edges, and only parent edges. A `supersedes` line naming a
        // revision outside the closure is left dangling on purpose: see the
        // module documentation, and `tests/export.rs`.
        let reachable = self.reachable(target)?;
        // Everything those revisions name, followed through decision 0032's
        // `keep` lines: a resolution is not self-contained prose, and the
        // documents it quotes items of have to travel with it.
        let mut frontier: Vec<RevisionId> = Vec::new();
        for (_, document) in &reachable {
            for named in document
                .edited
                .values()
                .chain(document.text.values())
                .chain(document.bytes.values())
            {
                frontier.push(*named);
            }
        }

        let mut named: BTreeSet<RevisionId> = BTreeSet::new();
        let mut documents: BTreeSet<RevisionId> = BTreeSet::new();
        let mut payloads: BTreeSet<RevisionId> = BTreeSet::new();
        while let Some(id) = frontier.pop() {
            if !named.insert(id) {
                continue;
            }
            if let Some(resolution) = self.resolution(&id)? {
                documents.insert(id);
                for piece in &resolution.pieces {
                    if let Piece::Keep { document, .. } = piece {
                        frontier.push(*document);
                    }
                }
                continue;
            }
            if self.operation(&id)?.is_some() {
                documents.insert(id);
                continue;
            }
            // Neither grammar: a payload, or a digest whose bytes this store
            // does not hold — forgotten, or not yet delivered. Both are left
            // to the stand-ins below and to `check` in the copy, which says
            // the same thing about it that `check` says here.
            if self.payload(&id)?.is_some() {
                payloads.insert(id);
            }
        }

        // Decision 0014 travels, always: a forgetting document is named by
        // nothing, so it is found by asking what each one forgets.
        let mut forgetting: Vec<RevisionId> = Vec::new();
        for (id, body) in self.bodies()? {
            if body.forgets().is_some_and(|target| named.contains(&target))
                && !documents.contains(&id)
            {
                forgetting.push(id);
            }
        }

        // The folder half, said as paths. What writes them is `update`, which
        // materialises from the copy once the copy holds its own history.
        let mut paths: Vec<String> = self
            .tree(target)?
            .entries()
            .map(|(_, entry)| entry.path.clone())
            .collect();
        paths.sort();
        paths.dedup();

        Ok(ExportPlan {
            target: *target,
            revisions: reachable.into_iter().map(|(id, _)| id).collect(),
            documents: documents.into_iter().collect(),
            payloads: payloads.into_iter().collect(),
            forgetting,
            paths,
            rules: self.skipped().travelling().cloned().collect(),
            withheld: self.skipped().withheld(),
            reserved: self.travelling_files()?,
        })
    }

    /// Write a fresh repository at `directory` on `files`, holding the folder
    /// at `target` and the history that leads there.
    ///
    /// `directory` is the repository — the folder — and the store goes in the
    /// `history/` beneath it, exactly as `init` makes one. It must not already
    /// hold anything: seeding an existing store is `receive`'s job, and the
    /// distinction is worth keeping sharp.
    pub fn export_onto<G: Filesystem>(
        &self,
        files: G,
        directory: &Path,
        target: &RevisionId,
    ) -> Result<Exported, ExportError> {
        let plan = self.export_plan(target)?;

        match files.entries(directory) {
            Ok(entries) if entries.is_empty() => {}
            Ok(_) => {
                return Err(ExportError::Occupied {
                    path: directory.to_path_buf(),
                });
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(StoreError::io(directory, error).into()),
        }

        // Decision 0021: `historica.txt` and `format.txt` come from `init`,
        // because a copy that explains itself is the whole claim the format
        // makes. What `init` also writes is a rule file stating no rules and
        // an empty `names/` — which is to say, nothing of the exporter's.
        let mut copy = Store::init_on(files, directory.join(STORE_DIR))?;

        // Decision 0051: the rules that travel, written before the folder is
        // materialised, because the copy's own walk reads them and a rule the
        // copy states is a rule the copy has to be able to honour. None of
        // them can cover a path the target holds — `skip` refuses to write one
        // that does and `check` reports one that arrives — so this cannot take
        // a file out of the folder it was about to write.
        let travelling: Vec<crate::working::Rule> = plan.rules.clone();
        copy.add_skipped(&travelling)?;

        // The names decision 0006 gives a store, computed over what travels
        // rather than over the store it leaves: a collision suffix that
        // depends on a revision the copy does not hold would be a name
        // `arrange` in the copy immediately disagreed with.
        let held: Vec<(RevisionId, &crate::format::RevisionDocument)> = plan
            .revisions
            .iter()
            .map(|id| (*id, self.get(id).expect("a revision the plan named")))
            .collect();
        let stems = naming::stems(held.iter().map(|(id, document)| (id, *document)));
        let filed = self.operation_names(&stems, held.iter().map(|(id, doc)| (id, *doc)))?;
        let name_of = |id: &RevisionId, document: bool| match filed.get(id) {
            Some((stem, name)) => format!("{stem}/{name}"),
            // A forgetting document is named by nothing, so nothing can file
            // it under a path; it keeps the digest name `forget` wrote it
            // under, which is where `arrange` leaves one too.
            None if document => format!("{id}{OPERATION_SUFFIX}"),
            None => id.to_string(),
        };

        // Content first and revisions last, on `receive`'s reasoning: an
        // interruption should understate what is reachable rather than leave
        // a revision naming bytes that never arrived.
        for id in &plan.payloads {
            let bytes = self
                .payload(id)?
                .expect("a payload the plan named is still held");
            copy.insert_payload_at(&bytes, &name_of(id, false))?;
        }
        // Written back in the grammar it was read in, both here and for the
        // stand-ins below: a document rewritten as the other grammar is a
        // different digest, and the line naming it would stop finding it.
        for id in plan.documents.iter().chain(&plan.forgetting) {
            match self
                .body(id)?
                .expect("a document the plan named is still held")
            {
                Body::Resolution(document) => {
                    copy.insert_resolution_at(&document, &name_of(id, true))?;
                }
                Body::Operation(document) => {
                    copy.insert_operation_at(&document, &name_of(id, true))?;
                }
            }
        }
        for (id, document) in &held {
            let stem = stems.get(id).expect("every revision that travels is named");
            copy.insert_at(document, &format!("{stem}{REVISION_SUFFIX}"))?;
        }

        // Decision 0053, after the revisions for the reason the revisions come
        // after the content: an interruption should leave the copy holding
        // less than it will, never a file vouching for a revision that never
        // arrived. The files keep the names they had, which is the whole of
        // what makes the directory union wherever it lands next.
        for label in &plan.reserved {
            let bytes = self.travelling_file(label)?;
            copy.carry_travelling(label, &bytes)?;
        }

        // The folder half is `update`'s, materialised out of the copy's own
        // history — which is the first thing that proves the copy can produce
        // it — and written through the destination filesystem.
        let working = Working::read_on(copy.filesystem(), directory, copy.skipped())
            .map_err(|error| ExportError::Update(Box::new(UpdateError::Working(error))))?;
        let update = update::plan(&copy, &working, directory, target)?;
        let applied = update::apply(&working, directory, &update)?;

        Ok(Exported {
            root: directory.to_path_buf(),
            target: plan.target,
            revisions: plan.revisions.len(),
            documents: plan.documents.len(),
            payloads: plan.payloads.len(),
            forgetting: plan.forgetting.len(),
            rules: travelling.len(),
            withheld: plan.withheld,
            reserved: plan.reserved.len(),
            files: applied.wrote,
        })
    }
}

/// The short form, on the filesystem `std::fs` is.
#[cfg(feature = "disk")]
impl Store<Disk> {
    /// Write a fresh repository at `directory` on disk.
    pub fn export(
        &self,
        directory: impl AsRef<Path>,
        target: &RevisionId,
    ) -> Result<Exported, ExportError> {
        self.export_onto(Disk, directory.as_ref(), target)
    }
}

/// Why nothing was exported.
#[derive(Debug)]
#[non_exhaustive]
pub enum ExportError {
    /// The store `check` calls broken, which a copy would only double.
    BrokenStore,
    /// The destination directory already holds something.
    Occupied {
        /// The directory.
        path: PathBuf,
    },
    /// The target's tree or content could not be materialised.
    Materialise(Box<MaterialiseError>),
    /// The copy's folder could not be written.
    Update(Box<UpdateError>),
    /// A store could not be read or written.
    Store(StoreError),
}

impl From<MaterialiseError> for ExportError {
    fn from(error: MaterialiseError) -> Self {
        Self::Materialise(Box::new(error))
    }
}

impl From<UpdateError> for ExportError {
    fn from(error: UpdateError) -> Self {
        Self::Update(Box::new(error))
    }
}

impl From<StoreError> for ExportError {
    fn from(error: StoreError) -> Self {
        Self::Store(error)
    }
}

impl fmt::Display for ExportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExportError::BrokenStore => write!(
                f,
                "this store does not pass `check`, and a copy of a fault is two \
                 faults; `historica check` says what is wrong"
            ),
            ExportError::Occupied { path } => write!(
                f,
                "{} already holds something, and an export writes a fresh \
                 repository; combining a copy with what is already there is \
                 `receive`",
                path.display()
            ),
            ExportError::Materialise(error) => error.fmt(f),
            ExportError::Update(error) => error.fmt(f),
            ExportError::Store(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for ExportError {}
