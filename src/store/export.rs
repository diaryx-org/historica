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
//! # Exporting onto a copy this store already made
//!
//! Decision 0052. A published export is a directory a stranger fetches from,
//! and re-copying a whole store on every publish is not a thing anybody does
//! on a timer — so a destination that already holds a copy of *this* store is
//! updated in place rather than refused. The set is unchanged: the target's
//! ancestry, closed, exactly as [`Store::export_plan`] states it. What is new
//! is that the copy is **diffed** against that set, so every file has three
//! outcomes rather than one — write it, leave it, or withdraw it.
//!
//! Withdrawal is the point rather than a tidy-up. A `forget` at the origin
//! has to destroy bytes in the published copy or the redaction is defeated by
//! the one copy that is world-readable; so does a `prune`, and so does a
//! target that moves off a branch. An export that only ever added would
//! publish a permanent record of everything the origin ever held, which is
//! the opposite of what decision 0014 promises.
//!
//! Additions ascend — payloads, then documents, then revisions — and
//! withdrawals descend, revisions first. Both keep one invariant at every
//! moment in between: *no revision in the copy names bytes the copy does not
//! hold*. The withdrawals are performed first, so an interruption redacts and
//! then stops rather than stopping before it redacts; an interrupted run
//! understates what is reachable, which is `receive`'s rule and 0048's, and
//! the next run finishes the job.
//!
//! Two of 0052's sentences needed a clause the decision leaves implicit, and
//! both are argued where the code is. The refusal over a revision the origin
//! lacks asks whether the origin *names* it too, or a `prune` — which leaves
//! the successor's `supersedes` line pointing at what it deleted — would
//! refuse the very export 0052 says a prune must propagate through. And the
//! folder is materialised under decision 0055's rule rather than 0030's flat
//! one, because a run that withdraws destroys the record of what the copy's
//! folder holds, and 0030 asked afterwards would call the exporter's own last
//! output somebody's unrecorded work.
//!
//! Three things the copy holds are not the exporter's to touch. `names/` and
//! `cache/` are neither written nor removed, which is 0042 unchanged. Nor is
//! a reserved travelling directory: decision 0054 makes the update add-only
//! there, because `travels-and-unions` is a class whose whole justification
//! is that a name historica cannot read needs no merge rule — and deleting
//! such a file on the strength of its absence somewhere else is a judgement
//! about a grammar 0046 refused historica.
//!
//! [`History::superseded`]: crate::core::History::superseded

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::io;
use std::path::{Path, PathBuf};

use crate::core::RevisionId;
use crate::format::{Mode, Piece, RevisionDocument};
#[cfg(feature = "disk")]
use crate::fs::Disk;
use crate::fs::Filesystem;
use crate::naming;
use crate::update::{self, UpdateError};
use crate::working::{SKIPPED_DIR, Skipped, Working};

use super::{
    Body, HEADER_FILE, MaterialiseError, OPERATION_SUFFIX, OPERATION_SUFFIXES, OPERATIONS_DIR,
    REVISION_SUFFIX, REVISION_SUFFIXES, REVISIONS_DIR, STORE_DIR, Store, StoreError,
    files_claiming, label_of, payload_files, within,
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
    /// Whether a copy of this store is already there to be updated.
    updating: bool,
    /// Every file that leaves the copy, relative to its store root, in the
    /// order they are removed: revisions, then documents, then payloads, then
    /// rule files. Empty for a fresh copy, which has nothing to withdraw.
    withdraws: Vec<PathBuf>,
    /// Where the rule files begin in `withdraws`. They are removed with the
    /// rules that arrive, before the folder is materialised, because the
    /// copy's own walk reads them; everything before this index is store
    /// content and goes after the folder.
    retires_from: usize,
    /// The rules those files state, which is what deletes them.
    retired: Vec<crate::working::Rule>,
    /// Forgotten originals the copy still holds, destroyed where `receive`
    /// destroys them.
    destroys: BTreeSet<RevisionId>,
    /// Everything either side forgets, which is what an export never writes.
    forgotten: BTreeSet<RevisionId>,
    /// What the copy already holds of the set, by digest, so that a second
    /// export writes the difference and leaves the rest where it is.
    holds: BTreeSet<RevisionId>,
    /// What the copy already calls each revision it holds, so that decision
    /// 0052's rule — an existing file is never renamed — can be kept while
    /// the newcomers are named around it.
    stems: BTreeMap<RevisionId, String>,
}

/// How many files one export will write.
///
/// Counted the way [`Exported`] counts what it wrote, which is the whole of
/// what makes a dry run and the real thing describe one copy: for a fresh
/// destination this is the plan's own lengths, and for a copy being updated
/// it is the difference.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Writes {
    /// Revision documents.
    pub revisions: usize,
    /// Operation and resolution documents.
    pub documents: usize,
    /// Whole-content payloads.
    pub payloads: usize,
    /// Forgetting documents.
    pub forgetting: usize,
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

    /// Whether the destination already holds a copy this export will update.
    ///
    /// Decision 0052: false is a fresh repository written into an empty
    /// directory, which is what an export was before.
    pub fn updating(&self) -> bool {
        self.updating
    }

    /// Every file that leaves the copy, relative to its store root, in the
    /// order they are removed.
    ///
    /// Revisions first and payloads last, so that no intermediate moment
    /// leaves a revision in the copy naming bytes the copy does not hold. A
    /// rule file the origin no longer states shares the list, because it is
    /// the same act: something the copy holds and the set no longer names.
    pub fn withdraws(&self) -> &[PathBuf] {
        &self.withdraws
    }

    /// Forgotten originals the copy still holds, which will be destroyed.
    ///
    /// Separate from [`ExportPlan::withdraws`] because it is a different
    /// fact: these bytes are not merely out of the set, they are named by a
    /// forgetting document that says they are gone.
    pub fn destroys(&self) -> &BTreeSet<RevisionId> {
        &self.destroys
    }

    /// How many files this export will write.
    pub fn writes(&self) -> Writes {
        let counted = |ids: &[RevisionId]| {
            ids.iter()
                .filter(|id| !self.holds.contains(id) && !self.forgotten.contains(id))
                .count()
        };
        Writes {
            revisions: counted(&self.revisions),
            documents: counted(&self.documents),
            payloads: counted(&self.payloads),
            forgetting: counted(&self.forgetting),
        }
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
    /// Files withdrawn from a copy this export updated, because the set no
    /// longer names them (decision 0052).
    pub withdrawn: usize,
    /// Forgotten originals destroyed in the copy, in compliance with the
    /// forgetting documents that stand in for them.
    pub destroyed: usize,
    /// Whether a copy already there was updated rather than one written fresh.
    pub updated: bool,
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
            updating: false,
            withdraws: Vec::new(),
            retires_from: 0,
            retired: Vec::new(),
            destroys: BTreeSet::new(),
            forgotten: BTreeSet::new(),
            holds: BTreeSet::new(),
            stems: BTreeMap::new(),
        })
    }

    /// The same plan, diffed against whatever `directory` already holds.
    ///
    /// Decision 0052. The set is [`Store::export_plan`]'s and is not touched
    /// here; what this adds is the other half of an incremental publish — what
    /// the copy already has, what it has that the set no longer names, and
    /// what it calls the revisions it keeps. A destination that is empty or
    /// absent yields exactly the plan a fresh export acts on.
    ///
    /// Every refusal an in-place export can state is stated here, so a dry run
    /// refuses where the real thing would: a directory holding something that
    /// is not this store's copy, a copy `check` calls broken, an unrelated
    /// store, and a copy somebody recorded in.
    pub fn export_plan_onto<G: Filesystem>(
        &self,
        files: &G,
        directory: &Path,
        target: &RevisionId,
    ) -> Result<ExportPlan, ExportError> {
        let mut plan = self.export_plan(target)?;
        let Some(copy) = self.copy_at(files, directory)? else {
            return Ok(plan);
        };
        self.diff_onto(&copy, &mut plan)?;
        plan.updating = true;
        Ok(plan)
    }

    /// The copy at `directory`, or nothing where a fresh export belongs there.
    ///
    /// Decision 0052 narrows the old refusal rather than removing it: a
    /// destination holding a store that is related (0029) and passes `check`
    /// is a copy to update, and unrelated, broken, or simply not a store still
    /// refuses. A copy holding a revision this store neither holds nor names
    /// refuses too, naming `receive` — somebody recorded in the published
    /// copy, and export assembles rather than merges.
    fn copy_at<'a, G: Filesystem>(
        &self,
        files: &'a G,
        directory: &Path,
    ) -> Result<Option<Store<&'a G>>, ExportError> {
        match files.entries(directory) {
            Ok(entries) if entries.is_empty() => return Ok(None),
            Ok(_) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(error) => return Err(StoreError::io(directory, error).into()),
        }

        let path = directory.to_path_buf();
        let root = directory.join(STORE_DIR);
        // The header is the reader's gate everywhere else, and it is the gate
        // here too: a directory with no store under it is a directory holding
        // somebody's files, whatever else it holds.
        let header = root.join(HEADER_FILE);
        if !crate::fs::exists(files, &header).map_err(|error| StoreError::io(&header, error))? {
            return Err(ExportError::Occupied { path });
        }
        if !Store::check_on(files, &root).is_ok() {
            return Err(ExportError::BrokenCopy { path });
        }
        let copy = Store::open_on(files, &root)?;
        if !super::receive::related(self, &copy) {
            return Err(ExportError::Unrelated { path });
        }
        // A revision this store neither holds nor names is one that was
        // recorded in the copy: nothing here has ever heard of it, and
        // withdrawing it would destroy the only copy there is.
        //
        // Named is the part decision 0052 leaves implicit and the prune case
        // needs. `prune` deletes a superseded revision and leaves the
        // successor's `supersedes` line naming it — decision 0001 put the
        // evidence on the successor — so a copy still holding what the origin
        // pruned holds a digest the origin's own graph still points at. That
        // is 0052's other bullet arriving, and the two would contradict each
        // other if the refusal asked only what this store holds.
        let named: BTreeSet<RevisionId> = self
            .revisions()
            .flat_map(|(_, revision)| revision.parents.iter().chain(&revision.supersedes))
            .copied()
            .collect();
        if let Some((revision, _)) = copy
            .revisions()
            .find(|(id, _)| !self.holds(id) && !named.contains(id))
        {
            return Err(ExportError::Recorded {
                path,
                revision: *revision,
            });
        }
        Ok(Some(copy))
    }

    /// Diff the copy against the set, filling in the other half of the plan.
    ///
    /// Files are found by content, never by name, which is `prune`'s rule
    /// arriving at the one other command that destroys bytes: two copies of
    /// one withdrawn document are both that document, wherever they sit and
    /// whatever they are called.
    fn diff_onto<G: Filesystem>(
        &self,
        copy: &Store<G>,
        plan: &mut ExportPlan,
    ) -> Result<(), ExportError> {
        let revisions: BTreeSet<RevisionId> = plan.revisions.iter().copied().collect();
        let documents: BTreeSet<RevisionId> = plan
            .documents
            .iter()
            .chain(&plan.forgetting)
            .copied()
            .collect();
        let payloads: BTreeSet<RevisionId> = plan.payloads.iter().copied().collect();

        // What either side forgets, which is what neither side may hold. The
        // copy's own is asked for on `receive`'s reasoning: a store that
        // destroyed something must not be handed it back, and an export that
        // wrote the original over a stand-in would resurrect exactly what
        // decision 0014 destroyed.
        let mut forgotten: BTreeSet<RevisionId> = BTreeSet::new();
        for (id, body) in self.bodies()? {
            if documents.contains(&id)
                && let Some(target) = body.forgets()
            {
                forgotten.insert(target);
            }
        }
        let theirs = copy.bodies()?;
        for body in theirs.values() {
            if let Some(target) = body.forgets() {
                forgotten.insert(target);
            }
        }

        let files = copy.filesystem();
        let root = copy.root();
        let revisions_dir = root.join(REVISIONS_DIR);
        for path in files_claiming(files, root, REVISIONS_DIR, &REVISION_SUFFIXES)? {
            // Decision 0043: what a file hashes to is what it is, taken in
            // pieces, and nothing here wants the file.
            let id =
                crate::fs::digest_of(files, &path).map_err(|error| StoreError::io(&path, error))?;
            if !revisions.contains(&id) {
                plan.withdraws.push(copy.relative(&path));
                continue;
            }
            plan.holds.insert(id);
            if let Some(stem) = label_of(&revisions_dir, &path)
                .and_then(|label| label.strip_suffix(REVISION_SUFFIX).map(str::to_owned))
            {
                plan.stems.insert(id, stem);
            }
        }

        for path in files_claiming(files, root, OPERATIONS_DIR, &OPERATION_SUFFIXES)? {
            let id =
                crate::fs::digest_of(files, &path).map_err(|error| StoreError::io(&path, error))?;
            if forgotten.contains(&id) {
                plan.destroys.insert(id);
                continue;
            }
            // A stand-in the origin does not have, for a document the set
            // still names: the copy forgot something the origin did not, and
            // withdrawing the stand-in would leave the revision that names it
            // pointing at nothing. Decision 0014 travels one way only.
            let stands_in = theirs
                .get(&id)
                .and_then(|body| body.forgets())
                .is_some_and(|target| documents.contains(&target) || payloads.contains(&target));
            if documents.contains(&id) || stands_in {
                plan.holds.insert(id);
                continue;
            }
            plan.withdraws.push(copy.relative(&path));
        }

        for path in payload_files(files, root)? {
            let id =
                crate::fs::digest_of(files, &path).map_err(|error| StoreError::io(&path, error))?;
            if forgotten.contains(&id) {
                plan.destroys.insert(id);
                continue;
            }
            if payloads.contains(&id) {
                plan.holds.insert(id);
                continue;
            }
            plan.withdraws.push(copy.relative(&path));
        }

        // Decision 0051's travel axis, arriving at the one boundary that can
        // be crossed twice: a shared rule the origin gained is written below,
        // and a rule file the copy holds goes when the origin deleted the rule
        // or made it `private`. It is the only thing an export removes that a
        // recipient might have been relying on.
        plan.retires_from = plan.withdraws.len();
        for (rule, file) in copy.skipped().stating() {
            if plan.rules.iter().any(|travelling| travelling == rule) {
                continue;
            }
            plan.retired.push(rule.clone());
            if let Some(file) = file {
                plan.withdraws.push(within(Path::new(SKIPPED_DIR), file));
            }
        }

        plan.forgotten = forgotten;
        Ok(())
    }

    /// Write a repository at `directory` on `files`, holding the folder at
    /// `target` and the history that leads there.
    ///
    /// `directory` is the repository — the folder — and the store goes in the
    /// `history/` beneath it, exactly as `init` makes one. An empty or absent
    /// directory gets a fresh copy. A directory already holding a copy *this*
    /// store made gets that copy brought up to the target, which is decision
    /// 0052; anything else is refused, because combining two histories is
    /// `receive`'s job and the distinction is worth keeping sharp.
    pub fn export_onto<G: Filesystem>(
        &self,
        files: G,
        directory: &Path,
        target: &RevisionId,
    ) -> Result<Exported, ExportError> {
        let plan = self.export_plan_onto(&files, directory, target)?;
        let root = directory.join(STORE_DIR);

        let mut copy = match plan.updating {
            true => Store::open_on(files, &root)?,
            // Decision 0021: `historica.txt` and `format.txt` come from
            // `init`, because a copy that explains itself is the whole claim
            // the format makes. What `init` also writes is a rule file stating
            // no rules and an empty `names/` — which is to say, nothing of the
            // exporter's.
            false => Store::init_on(files, &root)?,
        };

        // Whether the copy's folder is still exactly what the last export left
        // there, asked *before* this one takes anything away. Decision 0052
        // meets decision 0030 here and the meeting needs saying: a `forget` or
        // a withdrawal at the origin takes with it the record of what the
        // copy's folder holds, so 0030's overwrite rule — asked afterwards, as
        // it would be — calls the exporter's own last output "work nothing has
        // recorded" and refuses to replace it. Asked beforehand it answers the
        // question that was actually meant: has anybody touched this folder
        // since the export wrote it. Nobody has, and it is the export's to
        // rewrite; somebody has, and 0030 refuses exactly as it always did.
        //
        // Only where something is being taken away, because that is the only
        // case where the two rules disagree — and it is the run that is
        // already paying for a pass over the copy.
        let overwrite = match plan.updating
            && (!plan.withdraws.is_empty() || !plan.destroys.is_empty())
            && undisturbed(&copy, directory)?
        {
            true => update::Overwrite::Wholesale,
            false => update::Overwrite::Recorded,
        };

        // Decision 0051, in both directions and before the folder is
        // materialised, because the copy's own walk reads these and a rule the
        // copy states is a rule the copy has to be able to honour. None of
        // them can cover a path the target holds — `skip` refuses to write one
        // that does and `check` reports one that arrives — so this cannot take
        // a file out of the folder it is about to write. The rule that goes is
        // one the origin deleted or made `private`, which decision 0052 makes
        // the only thing an export removes that a recipient might have been
        // relying on.
        copy.remove_skipped(&plan.retired)?;
        let travelling: Vec<crate::working::Rule> = plan.rules.clone();
        copy.add_skipped(&travelling)?;

        // The names decision 0006 gives a store, computed over what travels
        // rather than over the store it leaves: a collision suffix that
        // depends on a revision the copy does not hold would be a name
        // `arrange` in the copy immediately disagreed with.
        let held: Vec<(RevisionId, &RevisionDocument)> = plan
            .revisions
            .iter()
            .map(|id| Ok((*id, self.get(id)?.expect("a revision the plan named"))))
            .collect::<Result<_, StoreError>>()?;
        let stems = match plan.updating {
            false => naming::stems(held.iter().map(|(id, document)| (id, *document))),
            true => stems_around(&plan, &copy.documents()?, &held),
        };
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
        // a revision naming bytes that never arrived. What the copy already
        // holds is left exactly where it is — an existing file is never
        // renamed — and what either side forgot is never written at all.
        let mut wrote = Writes::default();
        for id in &plan.payloads {
            if plan.holds.contains(id) || plan.forgotten.contains(id) {
                continue;
            }
            let bytes = self
                .payload(id)?
                .expect("a payload the plan named is still held");
            copy.insert_payload_at(&bytes, &name_of(id, false))?;
            wrote.payloads += 1;
        }
        // Written back in the grammar it was read in, both here and for the
        // stand-ins below: a document rewritten as the other grammar is a
        // different digest, and the line naming it would stop finding it.
        let naming_documents = plan
            .documents
            .iter()
            .map(|id| (id, false))
            .chain(plan.forgetting.iter().map(|id| (id, true)));
        for (id, forgetting) in naming_documents {
            if plan.holds.contains(id) || plan.forgotten.contains(id) {
                continue;
            }
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
            match forgetting {
                true => wrote.forgetting += 1,
                false => wrote.documents += 1,
            }
        }
        // Decision 0014 is complied with here, between the documents and the
        // revisions, because that is where `receive` complies with it: a
        // forgetting document that has just arrived destroys the original the
        // copy still holds, exactly as it does anywhere else.
        let destroyed = copy.comply_with_forgetting(&plan.destroys)?;
        for (id, document) in &held {
            if plan.holds.contains(id) {
                continue;
            }
            let stem = stems.get(id).expect("every revision that travels is named");
            copy.insert_at(document, &format!("{stem}{REVISION_SUFFIX}"))?;
            wrote.revisions += 1;
        }

        // Decision 0053, after the revisions for the reason the revisions come
        // after the content: an interruption should leave the copy holding
        // less than it will, never a file vouching for a revision that never
        // arrived. The files keep the names they had, which is the whole of
        // what makes the directory union wherever it lands next — and decision
        // 0054 makes the second run union too, adding what the copy lacks and
        // withdrawing nothing.
        let mut reserved = 0;
        for label in &plan.reserved {
            let bytes = self.travelling_file(label)?;
            if copy.carry_travelling(label, &bytes)? {
                reserved += 1;
            }
        }

        // The folder half is `update`'s, materialised out of the copy's own
        // history — which is the first thing that proves the copy can produce
        // it — and written through the destination filesystem. Decision 0030
        // catches a non-empty folder up, which is the whole of what is new
        // here; what the call site loses is the assumption that the folder was
        // empty, and it happens before the withdrawals because 0030's
        // overwrite rule reads the very revisions they remove.
        let working = Working::read_on(copy.filesystem(), directory, copy.skipped())
            .map_err(|error| ExportError::Update(Box::new(UpdateError::Working(error))))?;
        let update = update::plan_at(&copy, &working, directory, target, overwrite)?;
        let applied = update::apply(&working, directory, &update)?;

        // Withdrawals descend: the revisions, then the documents nothing kept
        // names, then the payloads. Every one of them is something no revision
        // the copy keeps names, so the invariant holds at every moment in
        // between — a run cut short here understates what the copy is
        // reachable from, and the next run finishes the job.
        for relative in &plan.withdraws[..plan.retires_from] {
            let path = root.join(relative);
            copy_remove(copy.filesystem(), &path)?;
        }
        for directory in [REVISIONS_DIR, OPERATIONS_DIR] {
            super::prune::remove_empty_directories(copy.filesystem(), &root.join(directory))?;
        }
        // Decision 0014's promise is that bytes are *gone*, so what `cache/`
        // derived from them goes too. `forget` and `prune` clear it for this
        // reason, and an export that destroyed or withdrew anything is the
        // third command with something to destroy.
        if !plan.withdraws.is_empty() || destroyed != 0 {
            copy.clear_cache();
        }

        Ok(Exported {
            root: directory.to_path_buf(),
            target: plan.target,
            revisions: wrote.revisions,
            documents: wrote.documents,
            payloads: wrote.payloads,
            forgetting: wrote.forgetting,
            rules: travelling.len(),
            withheld: plan.withheld,
            reserved,
            withdrawn: plan.withdraws.len(),
            destroyed,
            updated: plan.updating,
            files: applied.wrote,
        })
    }
}

/// Whether the copy's folder still holds what its own history last put there.
///
/// The folder is read through the copy's own filesystem and against the copy's
/// own rules, which is what makes this the question 0030 would ask of it
/// rather than a question about the origin.
fn undisturbed<G: Filesystem>(copy: &Store<G>, directory: &Path) -> Result<bool, ExportError> {
    let working = Working::read_on(copy.filesystem(), directory, copy.skipped())
        .map_err(|error| ExportError::Update(Box::new(UpdateError::Working(error))))?;
    Ok(update::undisturbed(copy, &working, directory)?)
}

/// Remove one file the copy is giving up, tolerating one already gone.
///
/// The plan is worked out from a listing rather than held under a lock, so a
/// file somebody deleted in between is a file that is where the plan wanted it
/// to be. Everything else is reported.
fn copy_remove<F: Filesystem + ?Sized>(files: &F, path: &Path) -> Result<(), ExportError> {
    match files.remove_file(path) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(StoreError::io(path, error).into()),
    }
}

/// The stem each revision takes in a copy that already holds files.
///
/// Decision 0052: an existing file is never renamed, so a revision the copy
/// holds keeps the name it was written under and a newcomer whose readable
/// name meets it takes the collision suffix — even where a fresh export would
/// have given it the plain name. That is [`naming::stem_for`], which is the
/// writer's own answer to the same question (0019, 0041), applied against the
/// set the copy already holds rather than against the whole plan. The names
/// drift from what a fresh export would produce, and nothing reads them but a
/// fetcher, which discards them.
fn stems_around(
    plan: &ExportPlan,
    copy: &[(&RevisionId, &RevisionDocument)],
    held: &[(RevisionId, &RevisionDocument)],
) -> BTreeMap<RevisionId, String> {
    let mut stems = plan.stems.clone();
    let mut existing: Vec<RevisionDocument> = copy
        .iter()
        .map(|(_, document)| (*document).clone())
        .collect();
    // Digest order, which is `held`'s, so two replicas naming one set of
    // newcomers around one copy name them alike.
    for (id, document) in held {
        if stems.contains_key(id) {
            continue;
        }
        stems.insert(
            *id,
            naming::stem_for(
                &document.when,
                &document.message,
                &document.change,
                id,
                existing.iter(),
            ),
        );
        existing.push((*document).clone());
    }
    stems
}

/// The folder a revision has, and nothing else.
///
/// Decision 0042 builds a copy a stranger can *work* in, and pays for it: the
/// target's whole ancestry, every document and payload those revisions name,
/// and the rules and reserved directories that go with them. Exporting the
/// three-hundredth revision of a six-hundred-revision store writes 14 MB and
/// takes a second and a half, of which 13 MB is `history/`.
///
/// Sometimes the ancestry is not what was wanted. A person looking at what a
/// file said last month, a build of an old revision, a tree handed to somebody
/// who does not have historica — each of those wants the folder and nothing
/// underneath it. That is the same command with the store left out, because
/// what it writes is the same folder: the same target, the same
/// materialisation through [`crate::update`], and the same rules a full copy
/// would have carried, so `export --files-only` and `export` write folders
/// that agree byte for byte.
///
/// # What it is not
///
/// **Not a repository.** There is no `history/`, so nothing here can be
/// recorded into, fetched from or received. An export at a past revision is
/// still the way to *work* on one — the copy it writes has that revision as
/// its only head — and this is the way to *look* at one.
///
/// **Not an update in place.** Decision 0052 lets an export be written over a
/// copy of this store because the copy's own `history/` says what the last
/// export put there; a folder with no store beside it cannot answer that
/// question about a single file, so there is nothing to diff and nothing that
/// could be safely withdrawn. The destination is empty or it is refused,
/// which is [`crate::update::plan_into`]'s rule and the reason it has one.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct ExportedFiles {
    /// The directory that now holds the folder.
    pub root: PathBuf,
    /// The revision it holds.
    pub target: RevisionId,
    /// The paths written, in the order they were written.
    pub files: Vec<String>,
    /// The links made, with what each was pointed at.
    pub links: Vec<(String, String)>,
    /// The paths whose mode was set, with what it was set to.
    pub modes: Vec<(String, Mode)>,
    /// Paths left alone, with the reason.
    ///
    /// Empty on every ordinary run, and a fault rather than a note when it is
    /// not: the destination was empty when this began, so there was nothing to
    /// leave alone unless somebody wrote into it while this was working.
    pub left: Vec<(String, String)>,
    /// Paths whose read-back did not hold the bytes just written, because the
    /// destination folds two of the tree's paths onto one file (decision 0027).
    pub folded: Vec<String>,
}

impl<F: Filesystem> Store<F> {
    /// What a files-only export would write, without writing anything.
    ///
    /// The plan is [`crate::update`]'s, so a caller can read it with the same
    /// eyes it reads `update --dry-run` with.
    pub fn export_files_plan_onto<G: Filesystem>(
        &self,
        files: G,
        directory: &Path,
        target: &RevisionId,
    ) -> Result<update::Update, ExportError> {
        // A copy of a fault is two faults, which is `export`'s rule and
        // `prune`'s and `fetch`'s. Nothing about leaving the history behind
        // makes it safe to copy a folder out of a store that contradicts
        // itself.
        if !Store::check_on(self.filesystem(), self.root()).is_ok() {
            return Err(ExportError::BrokenStore);
        }
        let working = self.folder_at(&files, directory)?;
        Ok(update::plan_into(self, &working, directory, target)?)
    }

    /// Lay the folder `target` has out at `directory`, writing no `history/`.
    pub fn export_files_onto<G: Filesystem>(
        &self,
        files: G,
        directory: &Path,
        target: &RevisionId,
    ) -> Result<ExportedFiles, ExportError> {
        if !Store::check_on(self.filesystem(), self.root()).is_ok() {
            return Err(ExportError::BrokenStore);
        }
        let working = self.folder_at(&files, directory)?;
        let update = update::plan_into(self, &working, directory, target)?;
        let applied = update::apply(&working, directory, &update)?;

        // The plan's own and the apply's, together: into a directory that held
        // nothing, both mean the same thing — somebody else is writing here —
        // and a caller has no use for which half noticed.
        let mut left = update.leaves.clone();
        left.extend(applied.left.iter().cloned());

        Ok(ExportedFiles {
            root: directory.to_path_buf(),
            target: *target,
            files: applied.wrote,
            links: applied.linked,
            modes: applied.set,
            left,
            folded: applied.folded,
        })
    }

    /// The destination as a folder, made if it is not there yet.
    ///
    /// Decision 0051's rules, filtered to the ones that travel: the folder a
    /// full export writes is filtered by the rules the copy would have stated,
    /// so a files-only copy filtered by anything else would not be the same
    /// folder. A `private` rule keeps its own text out of a copy and is not a
    /// statement about which files a copy holds.
    fn folder_at<'a, G: Filesystem>(
        &self,
        files: &'a G,
        directory: &Path,
    ) -> Result<Working<&'a G>, ExportError> {
        files.create_directory(directory).map_err(|error| {
            ExportError::Update(Box::new(UpdateError::Io {
                path: directory.to_path_buf(),
                error,
            }))
        })?;
        let skipped = Skipped::from_rules(self.skipped().travelling().cloned());
        Working::read_on(files, directory, &skipped)
            .map_err(|error| ExportError::Update(Box::new(UpdateError::Working(error))))
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

    /// Lay the folder `target` has out at `directory` on disk, with no store.
    pub fn export_files(
        &self,
        directory: impl AsRef<Path>,
        target: &RevisionId,
    ) -> Result<ExportedFiles, ExportError> {
        self.export_files_onto(Disk, directory.as_ref(), target)
    }
}

/// Why nothing was exported.
#[derive(Debug)]
#[non_exhaustive]
pub enum ExportError {
    /// The store `check` calls broken, which a copy would only double.
    BrokenStore,
    /// The destination directory holds something that is not this store's copy.
    Occupied {
        /// The directory.
        path: PathBuf,
    },
    /// The destination holds a copy `check` calls broken.
    BrokenCopy {
        /// The directory.
        path: PathBuf,
    },
    /// The destination holds a store sharing no revision or edge with this one.
    Unrelated {
        /// The directory.
        path: PathBuf,
    },
    /// The destination holds a revision this store does not: somebody recorded
    /// in the published copy, and an export assembles rather than merges.
    Recorded {
        /// The directory.
        path: PathBuf,
        /// One revision the copy holds and this store does not.
        revision: RevisionId,
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
                "{} already holds something that is not a copy of this store; \
                 an export writes a fresh repository into an empty directory \
                 and updates a copy it made, and combining a copy with what is \
                 already there is `receive`",
                path.display()
            ),
            ExportError::BrokenCopy { path } => write!(
                f,
                "{} holds a copy that does not pass `check`, and an export \
                 writes nothing into a store whose faults it would build on; \
                 `historica check` there says what is wrong",
                path.display()
            ),
            ExportError::Unrelated { path } => write!(
                f,
                "{} holds a store that shares no revision or graph edge with \
                 this one; an export updates a copy it made and refuses \
                 anything else",
                path.display()
            ),
            ExportError::Recorded { path, revision } => write!(
                f,
                "{} holds {}, which this store does not: somebody recorded in \
                 the copy, and an export assembles rather than merges; \
                 `historica receive` in this direction first",
                path.display(),
                revision.abbreviate(crate::naming::DIGEST_CHARS)
            ),
            ExportError::Materialise(error) => error.fmt(f),
            ExportError::Update(error) => error.fmt(f),
            ExportError::Store(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for ExportError {}
