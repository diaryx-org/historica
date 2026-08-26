//! Carrying a descendant across a rewrite: decision 0059.
//!
//! Three decisions stopped at one wall and used the same words each time:
//! restating a descendant's operations against a parent whose content moved
//! is 0007's merge under another name. This module is that merge, run under
//! that name. A revision standing on a superseded one — the state 0023's
//! `## Since` taught `check` to note — is restated against the successor:
//! everything that describes the work is copied, `revised` comes from the
//! rewrite that caused it, and a file whose base moved is put through the
//! merge machinery the store already trusts.
//!
//! Nothing here mints, stamps, or reads a clock. A carry is 0010's "carried
//! along by an ancestor" row: every fact derives from what the store holds,
//! so two replicas repairing one history write byte-identical files.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fmt;

use crate::core::{FileId, Revision, RevisionId};
use crate::diff::diff;
use crate::format::{LinkTarget, OperationDocument, RevisionDocument, Timestamp, digest};
use crate::fs::Filesystem;
use crate::merge::{self, Event, MergeError};
use crate::naming;
use crate::replay::{ReplayError, State};
use crate::store::{MaterialiseError, REVISION_SUFFIX, Store, StoreError};

/// One revision the plan would restate, worked out to the last byte.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct CarryStep {
    /// The revision being carried, which the new one supersedes.
    pub predecessor: RevisionId,
    /// The parents the new revision stands on.
    pub onto: Vec<RevisionId>,
    /// The revision that would be written.
    pub revision: RevisionId,
    /// The paths whose operations were restated rather than named unchanged.
    pub restated: Vec<String>,
    /// The finished document.
    document: RevisionDocument,
    /// The restated operation documents to write, with where each file sat.
    writes: Vec<(naming::Filing, OperationDocument)>,
}

/// Which revisions a carry reaches.
///
/// The repair sweeps whatever it finds; an inline act carries what it itself
/// stranded and nothing else, because a rewrite is not entitled to finish a
/// half-delivered one somebody else's transport left behind.
#[derive(Debug, Clone)]
pub enum Carrying {
    /// Every revision standing on a rewritten one — `check`'s note, swept.
    Everything,
    /// One revision standing on a rewritten one, and everything on it.
    One(RevisionId),
    /// Everything stranded by these rewrites, and everything standing on
    /// that. Decision 0059's inline acts: one plan, covering exactly what
    /// the act caused.
    By(BTreeSet<RevisionId>),
    /// Decision 0059's authored move: restate `target` against `onto`, and
    /// carry what stands on it after.
    ///
    /// The same restating as every other variant, with one thing different
    /// and it is the important one — nothing in the store paired these two
    /// revisions. A person did, which is why `revised` is a reading of the
    /// clock here and derived everywhere else. That is 0010's other row, and
    /// the reason a moved revision converges with nothing: it was authored.
    Onto {
        /// The revision to restate.
        target: RevisionId,
        /// The parent to restate it against.
        onto: RevisionId,
        /// When, from the clock, because a person asked for this.
        revised: Timestamp,
        /// Who, which decision 0005 spells `revised-by`.
        reviser: String,
    },
}

/// What carrying would do, before anything is written.
///
/// Every refusal happens while this is being built, so a plan that exists is
/// one the store will take whole — parents first, each step's documents
/// before its revision, exactly as `record` writes.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct CarryPlan {
    /// The steps, parents before children.
    pub steps: Vec<CarryStep>,
}

impl CarryPlan {
    /// Whether there is nothing standing on a rewritten revision.
    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }
}

/// What one file's content is doing across the rewrite, at some point in the
/// carried line: what the old side holds, and what the new side holds.
///
/// Built once per replaced parent by comparing the store's own answers, and
/// updated as each carried revision restates things — so the base a
/// descendant's operations are read against is always the pair, never a walk
/// through revisions that do not exist yet.
#[derive(Debug, Clone, Default)]
struct Moving {
    /// Line files whose content differs, as (old side, new side).
    lines: BTreeMap<FileId, (State, State)>,
    /// Files the old side holds and the new side does not, with their paths.
    lost: BTreeMap<FileId, String>,
    /// Paths the new side holds and the old side does not.
    introduced: BTreeSet<String>,
    /// Whole files whose payloads differ.
    payloads: BTreeSet<FileId>,
}

impl Moving {
    /// Whether any content moved at all — the condition under which a merge
    /// cannot be carried, because its parents' agreement would have to be
    /// recomputed and its resolution renumbered.
    fn moved(&self) -> bool {
        !self.lines.is_empty() || !self.lost.is_empty() || !self.payloads.is_empty()
    }

    /// The union of what several parents hand down.
    fn join(all: Vec<Moving>) -> Moving {
        let mut joined = Moving::default();
        for one in all {
            joined.lines.extend(one.lines);
            joined.lost.extend(one.lost);
            joined.introduced.extend(one.introduced);
            joined.payloads.extend(one.payloads);
        }
        joined
    }

    /// Two rewrites in sequence, read as one: `first` is what moved from the
    /// old side to a middle spelling, `second` from the middle to the new.
    ///
    /// A union would be wrong here in both directions — a file both legs
    /// moved would keep the middle content as one of its ends — so a pair is
    /// composed from `first`'s old side and `second`'s new side, and a file
    /// only one leg moved keeps that leg's pair, because the other leg left
    /// its two ends equal. A composition whose ends come out equal is a file
    /// the second rewrite put back, and it is dropped: nothing is moving.
    fn compose(first: Moving, second: Moving) -> Moving {
        let mut lines = second.lines;
        for (file, (old, middle)) in first.lines {
            let composed = match lines.remove(&file) {
                Some((_, new)) => (old, new),
                None => (old, middle),
            };
            if composed.0 != composed.1 {
                lines.insert(file, composed);
            }
        }
        Moving {
            lines,
            lost: first.lost.into_iter().chain(second.lost).collect(),
            introduced: first
                .introduced
                .into_iter()
                .chain(second.introduced)
                .collect(),
            payloads: first.payloads.into_iter().chain(second.payloads).collect(),
        }
    }
}

/// Work out what carrying would restate, without writing anything.
///
/// With a target, the plan is that revision and everything standing on it.
/// With none, it is every revision `check`'s note would name — one nothing
/// supersedes, standing on one something does — and an empty plan is the
/// ordinary answer in a store with no rewrite half-delivered.
pub fn plan<F: Filesystem>(store: &Store<F>, carrying: &Carrying) -> Result<CarryPlan, CarryError> {
    // What each withdrawn revision was withdrawn by, exactly as `check`
    // builds it: from the documents that state it, so a supersession nobody
    // delivered is not one this store knows about.
    let mut withdrawn: BTreeMap<RevisionId, BTreeSet<RevisionId>> = BTreeMap::new();
    for (id, revision) in store.revisions() {
        for predecessor in &revision.supersedes {
            withdrawn.entry(*predecessor).or_default().insert(*id);
        }
    }

    let stranded = |id: &RevisionId, revision: &Revision| {
        !withdrawn.contains_key(id)
            && revision
                .parents
                .iter()
                .any(|parent| withdrawn.contains_key(parent))
    };

    // The set to carry: the stranded revisions, and everything standing on
    // them — because writing a successor for a revision makes everything on
    // it stranded, and a repair that manufactured the state it repairs would
    // not be one. A withdrawn revision is never carried: a rewrite reaches
    // what it rewrote and nothing built on it, and what it rewrote is done.
    // The authored move's own mapping, and every refusal that belongs to
    // deciding rather than to restating.
    let moved: Option<(RevisionId, RevisionId, RevisionId)> = match carrying {
        Carrying::Onto { target, onto, .. } => {
            let revision = store
                .revision(target)
                .ok_or(CarryError::NotHeld { revision: *target })?
                .clone();
            if store.revision(onto).is_none() {
                return Err(CarryError::NotHeld { revision: *onto });
            }
            // A revision something has already rewritten is a change with
            // two spellings, and moving one of them would be choosing which
            // won. Every act on a divergent change waits for a person.
            if let Some(successors) = withdrawn.get(target) {
                return Err(CarryError::DivergentRewrite {
                    superseded: *target,
                    successors: successors.clone(),
                });
            }
            // A merge's parents' agreement would have to be recomputed
            // against a parent it never met, which is the work `plan`
            // refuses one revision higher up and refuses here for the same
            // reason.
            if revision.parents.len() > 1 {
                return Err(CarryError::MovingAMerge { revision: *target });
            }
            // A revision with no parent is where a history starts, and a
            // history that started somewhere else is a different history.
            let parent = revision
                .parents
                .iter()
                .next()
                .copied()
                .ok_or(CarryError::MovingARoot { revision: *target })?;
            if parent == *onto {
                return Err(CarryError::AlreadyThere {
                    revision: *target,
                    onto: *onto,
                });
            }
            Some((*target, parent, *onto))
        }
        _ => None,
    };

    // The enum under its own name, because the set below takes the other.
    let asked = carrying;
    let mut carrying: BTreeSet<RevisionId> = match carrying {
        Carrying::One(named) => {
            let revision = store
                .revision(named)
                .ok_or(CarryError::NotHeld { revision: *named })?;
            if !stranded(named, revision) {
                return Err(CarryError::NotStranded { revision: *named });
            }
            BTreeSet::from([*named])
        }
        Carrying::Everything => store
            .revisions()
            .filter(|(id, revision)| stranded(id, revision))
            .map(|(id, _)| *id)
            .collect(),
        // Stranded *by these*: a parent one of the causes superseded. The
        // closure below reaches the rest, so what an inline act writes is
        // the stack above its own rewrite and nothing further.
        Carrying::By(causes) => store
            .revisions()
            .filter(|(id, revision)| {
                !withdrawn.contains_key(*id)
                    && revision.parents.iter().any(|parent| {
                        withdrawn
                            .get(parent)
                            .is_some_and(|by| by.iter().any(|one| causes.contains(one)))
                    })
            })
            .map(|(id, _)| *id)
            .collect(),
        // The move starts at the revision named, and the closure below takes
        // the stack above it. Nothing is stranded here — the pairing this
        // carries onto is the person's, not a rewrite's.
        Carrying::Onto { target, .. } => BTreeSet::from([*target]),
    };

    loop {
        let more: BTreeSet<RevisionId> = store
            .revisions()
            .filter(|(id, revision)| {
                !carrying.contains(*id)
                    && !withdrawn.contains_key(*id)
                    && revision
                        .parents
                        .iter()
                        .any(|parent| carrying.contains(parent))
            })
            .map(|(id, _)| *id)
            .collect();
        if more.is_empty() {
            break;
        }
        carrying.extend(more);
    }

    // A destination inside what is moving would stand on a revision this act
    // is about to supersede, by construction — the half-finished shape
    // `carry` exists to repair, manufactured deliberately.
    if let Some((target, _, destination)) = &moved
        && carrying.contains(destination)
    {
        return Err(CarryError::MovingOntoItself {
            revision: *target,
            onto: *destination,
        });
    }

    // The successor a superseded parent resolves to: the head of its own
    // supersession chain, since a rewrite may itself have been rewritten.
    // Two heads is divergence, which a person resolves before anything is
    // carried onto either.
    let successor = |of: &RevisionId| -> Result<RevisionId, CarryError> {
        let mut current = BTreeSet::from([*of]);
        loop {
            let mut next: BTreeSet<RevisionId> = BTreeSet::new();
            let mut heads: BTreeSet<RevisionId> = BTreeSet::new();
            for id in &current {
                match withdrawn.get(id) {
                    Some(successors) => next.extend(successors.iter().copied()),
                    None => {
                        heads.insert(*id);
                    }
                }
            }
            if next.is_empty() {
                return match heads.len() {
                    1 => Ok(heads.into_iter().next().expect("one head")),
                    _ => Err(CarryError::DivergentRewrite {
                        superseded: *of,
                        successors: heads,
                    }),
                };
            }
            next.extend(heads);
            current = next;
        }
    };

    // Parents before children, where a parent is the carried revision itself
    // or the carried head of its supersession chain — an amendment that was
    // itself stranded is carried first, and what stood on it follows onto
    // the revision that carry writes for it.
    let depends = |id: &RevisionId| -> Result<BTreeSet<RevisionId>, CarryError> {
        let revision = store.revision(id).expect("a member of the plan");
        let mut on = BTreeSet::new();
        for parent in &revision.parents {
            if carrying.contains(parent) {
                on.insert(*parent);
            } else if withdrawn.contains_key(parent) {
                let head = successor(parent)?;
                if carrying.contains(&head) {
                    on.insert(head);
                }
            }
        }
        Ok(on)
    };
    let mut order: Vec<RevisionId> = Vec::new();
    let mut placed: BTreeSet<RevisionId> = BTreeSet::new();
    while placed.len() < carrying.len() {
        let mut advanced = false;
        for id in &carrying {
            if placed.contains(id) {
                continue;
            }
            if depends(id)?.iter().all(|on| placed.contains(on)) {
                order.push(*id);
                placed.insert(*id);
                advanced = true;
            }
        }
        debug_assert!(advanced, "a cycle in a Merkle DAG");
        if !advanced {
            break;
        }
    }

    // What the plan has decided so far: each carried revision's new identity
    // and document, and what its content is doing across the rewrite, for
    // the steps standing on it.
    let mut planned: BTreeMap<RevisionId, RevisionId> = BTreeMap::new();
    let mut documents: BTreeMap<RevisionId, RevisionDocument> = BTreeMap::new();
    let mut handed_down: BTreeMap<RevisionId, Moving> = BTreeMap::new();
    let mut compared: BTreeMap<(RevisionId, RevisionId), Moving> = BTreeMap::new();
    let mut steps: Vec<CarryStep> = Vec::new();

    for id in &order {
        // The whole document, because a carry restates every tree fact in it.
        let previous = store.get(id)?.expect("a member of the plan").clone();

        // Each parent, mapped across the rewrite, with what moved between
        // the two spellings of it.
        let mut onto: Vec<(RevisionId, RevisionId)> = Vec::new();
        let mut inherited: Vec<Moving> = Vec::new();
        for parent in &previous.parents {
            // The move's own pairing. Nothing superseded anything, so none
            // of the derived branches below can find it; what it shares with
            // them is everything after — the delta between the two parents
            // replays exactly as a rewrite's would.
            if let Some((moving, from, to)) = &moved
                && id == moving
                && parent == from
            {
                if let std::collections::btree_map::Entry::Vacant(vacant) =
                    compared.entry((*from, *to))
                {
                    vacant.insert(between(store, from, to)?);
                }
                onto.push((*parent, *to));
                inherited.push(compared[&(*from, *to)].clone());
                continue;
            }
            if let Some(new) = planned.get(parent) {
                onto.push((*parent, *new));
                inherited.push(handed_down.get(parent).cloned().unwrap_or_default());
            } else if withdrawn.contains_key(parent) {
                let head = successor(parent)?;
                let new = planned.get(&head).copied().unwrap_or(head);
                if let std::collections::btree_map::Entry::Vacant(vacant) =
                    compared.entry((*parent, new))
                {
                    let delta = if planned.contains_key(&head) {
                        // The successor was itself carried, so the rewrite
                        // reaches here in two legs: what moved from this
                        // parent to the successor, then what the carry moved
                        // restating the successor — read as one, composed.
                        Moving::compose(
                            between(store, parent, &head)?,
                            handed_down.get(&head).cloned().unwrap_or_default(),
                        )
                    } else {
                        between(store, parent, &new)?
                    };
                    vacant.insert(delta);
                }
                onto.push((*parent, new));
                inherited.push(compared[&(*parent, new)].clone());
            } else {
                onto.push((*parent, *parent));
                inherited.push(Moving::default());
            }
        }

        let mut moving = Moving::join(inherited);

        // A merge above moved content would have to have its parents'
        // agreement recomputed and its resolution's references renumbered,
        // which is real work this version refuses rather than guesses at.
        // A merge above a rewrite that only reworded carries like any other
        // revision, verbatim.
        if previous.parents.len() > 1 && moving.moved() {
            return Err(CarryError::MergeAboveMovedContent { revision: *id });
        }

        // The mapped parents, deduplicated by the set the document holds. A
        // rewrite that folded two of them into one revision would quietly
        // turn a merge into a chain, which is not a thing to do on anyone's
        // behalf.
        let parents: BTreeSet<RevisionId> = onto.iter().map(|(_, new)| *new).collect();
        if parents.len() < previous.parents.len() {
            return Err(CarryError::CollapsedParents { revision: *id });
        }

        // The refusals a step meets before any content is read.
        for path in previous.added.values().chain(previous.moved.values()) {
            if moving.introduced.contains(path) {
                return Err(CarryError::PathTaken {
                    revision: *id,
                    path: path.clone(),
                });
            }
        }
        let states: Vec<&FileId> = previous
            .edited
            .keys()
            .chain(previous.text.keys())
            .chain(previous.bytes.keys())
            .chain(previous.moved.keys())
            .chain(previous.modes.keys())
            .chain(previous.links.keys())
            .chain(previous.dropped.iter())
            .collect();
        for file in states {
            if let Some(path) = moving.lost.get(file) {
                return Err(CarryError::LostByRewrite {
                    revision: *id,
                    path: path.clone(),
                });
            }
        }
        for target in previous.links.values() {
            if let LinkTarget::Reference(named) = target
                && let Some(path) = moving.lost.get(named)
            {
                return Err(CarryError::LostByRewrite {
                    revision: *id,
                    path: path.clone(),
                });
            }
        }
        for file in previous.bytes.keys() {
            if moving.payloads.contains(file) {
                return Err(CarryError::ContestedPayload {
                    revision: *id,
                    file: *file,
                });
            }
        }

        // The content. A file whose base did not move is named unchanged —
        // same bytes, same digest, same document on disk. A file whose base
        // moved is restated through 0007's merge: the delta from the old
        // base to the new replays as an operation stream concurrent with
        // this revision's own, and where the two touch one region the carry
        // is contested and refuses.
        let mut edited: BTreeMap<FileId, RevisionId> = BTreeMap::new();
        let mut writes: Vec<(FileId, OperationDocument)> = Vec::new();
        let mut restated: Vec<FileId> = Vec::new();
        for (file, named) in &previous.edited {
            let Some((old_base, new_base)) = moving.lines.get(file).cloned() else {
                edited.insert(*file, *named);
                continue;
            };
            let operations = store
                .effective_operation(named)
                .map_err(CarryError::Store)?
                .ok_or(CarryError::MissingOperations {
                    revision: *id,
                    document: *named,
                })?;
            // A forgotten run has no bytes to restate, and recording the
            // marker's text as content would launder a redaction into
            // authority. Decision 0014 keeps its grip on a verbatim carry,
            // whose documents it already covers; a restated one is refused.
            let forgotten = operations
                .operations
                .iter()
                .flat_map(|operation| &operation.items)
                .any(|item| item.forgotten)
                || old_base.items().iter().any(|item| item.forgotten)
                || new_base.items().iter().any(|item| item.forgotten);
            if forgotten {
                return Err(CarryError::Forgotten {
                    revision: *id,
                    file: *file,
                });
            }

            let old_parent = previous
                .parents
                .iter()
                .next()
                .copied()
                .expect("a restated file has a parent whose content moved");
            let (_, new_parent) = onto
                .iter()
                .find(|(old, _)| *old == old_parent)
                .expect("the parent was mapped above");
            let creation = crate::replay::creation(&old_base.text());
            let delta = diff(&old_base, &new_base)
                .expect("the two bases differ, or the file would not be moving");
            let mut events: Vec<Event<'_>> = Vec::new();
            match &creation {
                Some(document) => events.push(Event::operations(
                    old_parent,
                    Vec::new(),
                    digest(&document.write()),
                    document,
                )),
                None => events.push(Event::nothing(old_parent, Vec::new())),
            }
            events.push(Event::operations(
                *new_parent,
                vec![old_parent],
                digest(&delta.write()),
                &delta,
            ));
            events.push(Event::operations(
                *id,
                vec![old_parent],
                *named,
                &operations,
            ));
            let merged = merge::merge(events).map_err(CarryError::Merge)?;
            if !merged.contested.is_empty() {
                return Err(CarryError::Contested {
                    revision: *id,
                    file: *file,
                    regions: merged.contested.len(),
                });
            }

            let old_after = old_base.apply(&operations).map_err(CarryError::Replay)?;
            let carried = merged.state;
            if let Some(document) = diff(&new_base, &carried) {
                edited.insert(*file, digest(&document.write()));
                writes.push((*file, document));
            }
            restated.push(*file);
            if old_after == carried {
                moving.lines.remove(file);
            } else {
                moving.lines.insert(*file, (old_after, carried));
            }
        }

        // What this revision states whole, it states on both sides now.
        for file in previous.bytes.keys() {
            moving.payloads.remove(file);
        }
        // What it drops is gone from both sides.
        for file in &previous.dropped {
            moving.lines.remove(file);
            moving.payloads.remove(file);
        }

        // A step thinned to nothing has no honest content: everything it
        // said is already what the rewrite says. Abandoning the predecessor
        // is the statement a person can still make about it.
        let empty = edited.is_empty()
            && previous.text.is_empty()
            && previous.bytes.is_empty()
            && previous.added.is_empty()
            && previous.moved.is_empty()
            && previous.modes.is_empty()
            && previous.links.is_empty()
            && previous.dropped.is_empty();
        if empty && parents.len() < 2 {
            return Err(CarryError::CarriedToNothing { revision: *id });
        }

        // Decision 0010's two rows, and which one this is depends on who
        // caused it. The moved revision is the person's act, so it takes a
        // reading of the clock; everything carried after it is derived from
        // the rewrite that caused it, so two replicas repairing one history
        // write byte-identical files. Only the first of a move is authored —
        // the stack above it converges exactly as a repair's does.
        let authored = match (&moved, asked) {
            (
                Some((moving, _, _)),
                Carrying::Onto {
                    revised, reviser, ..
                },
            ) if id == moving => Some((revised.clone(), reviser.clone())),
            _ => None,
        };
        let (revised, revised_by) = match authored {
            Some((revised, reviser)) => {
                let by = (reviser != previous.author).then_some(reviser);
                (revised, by)
            }
            None => {
                // Where more than one parent was rewritten, from the one with
                // the greater digest — the tie every other rule here is
                // broken by, with no clock consulted.
                let cause = onto
                    .iter()
                    .filter(|(old, new)| old != new)
                    .map(|(_, new)| *new)
                    .max()
                    .expect("a carried revision has a parent that moved");
                let held = store.get(&cause)?.cloned();
                let cause = documents
                    .get(&cause)
                    .cloned()
                    .or(held)
                    .expect("the cause is planned or held");
                let revised = cause.revised.clone().ok_or(CarryError::UnstampedCause {
                    revision: *id,
                    cause: cause.id(),
                })?;
                let revised_by = cause
                    .revised_by
                    .clone()
                    .unwrap_or_else(|| cause.author.clone());
                (
                    revised,
                    (revised_by != previous.author).then_some(revised_by),
                )
            }
        };

        let document = RevisionDocument {
            change: previous.change,
            parents,
            supersedes: BTreeSet::from([*id]),
            author: previous.author.clone(),
            when: previous.when.clone(),
            revised_by,
            revised: Some(revised),
            added: previous.added.clone(),
            moved: previous.moved.clone(),
            modes: previous.modes.clone(),
            links: previous.links.clone(),
            dropped: previous.dropped.clone(),
            edited,
            text: previous.text.clone(),
            bytes: previous.bytes.clone(),
            extensions: previous.extensions.clone(),
            message: previous.message.clone(),
        };
        let revision = document.id();

        // Where each restated document is filed: under the carried
        // revision's stem, at the path the file had — which the predecessor
        // can answer, because the predecessor is in the store.
        let mut filings: Vec<(naming::Filing, OperationDocument)> = Vec::new();
        let mut paths: Vec<String> = Vec::new();
        if !writes.is_empty() || !restated.is_empty() {
            let tree = store
                .tree(id)
                .map_err(|error| CarryError::Materialise(Box::new(error)))?;
            for file in &restated {
                if let Some(path) = tree.path(file) {
                    paths.push(path.to_owned());
                }
            }
            for (file, held) in writes {
                let path = tree.path(&file).unwrap_or_default().to_owned();
                filings.push((
                    naming::Filing {
                        held: digest(&held.write()),
                        path,
                        document: true,
                    },
                    held,
                ));
            }
        }

        planned.insert(*id, revision);
        documents.insert(revision, document.clone());
        handed_down.insert(*id, moving);
        steps.push(CarryStep {
            predecessor: *id,
            onto: onto.iter().map(|(_, new)| *new).collect(),
            revision,
            restated: paths,
            document,
            writes: filings,
        });
    }

    Ok(CarryPlan { steps })
}

/// What one file set is doing across one rewrite: the store's answer at the
/// superseded revision, compared with its answer at the successor.
fn between<F: Filesystem>(
    store: &Store<F>,
    superseded: &RevisionId,
    successor: &RevisionId,
) -> Result<Moving, CarryError> {
    let materialise = |error| CarryError::Materialise(Box::new(error));
    let old_tree = store.tree(superseded).map_err(materialise)?;
    let new_tree = store.tree(successor).map_err(materialise)?;

    let mut moving = Moving::default();
    for (file, path) in old_tree.files() {
        let Some(kind) = old_tree.kind(file) else {
            continue;
        };
        if new_tree.path(file).is_none() {
            moving.lost.insert(*file, path.to_owned());
            continue;
        }
        match kind {
            crate::tree::Kind::Lines => {
                let old = store.content_of(superseded, file).map_err(materialise)?;
                let new = store.content_of(successor, file).map_err(materialise)?;
                if old != new {
                    moving.lines.insert(
                        *file,
                        (
                            old.unwrap_or_else(State::empty),
                            new.unwrap_or_else(State::empty),
                        ),
                    );
                }
            }
            crate::tree::Kind::Whole => {
                let old = old_tree.entry(file).and_then(|entry| entry.payload);
                let new = new_tree.entry(file).and_then(|entry| entry.payload);
                if old != new {
                    moving.payloads.insert(*file);
                }
            }
            // A target restated by a carried revision simply stands, exactly
            // as a `mode` does: the carried revision is later than both
            // spellings, so what it says is what the file is.
            crate::tree::Kind::Link => {}
        }
    }
    for (file, path) in new_tree.files() {
        if old_tree.path(file).is_none() {
            moving.introduced.insert(path.to_owned());
        }
    }
    Ok(moving)
}

/// Carry every planned revision across, writing documents before revisions.
///
/// The plan is computed whole before anything is written, so every refusal
/// arrives with the store untouched. An interrupted carry leaves a store
/// `check` still accepts — the carried prefix is a finished rewrite, and the
/// rest is exactly the state `carry` repairs, so running it again resumes.
pub fn carry<F: Filesystem>(
    store: &mut Store<F>,
    carrying: &Carrying,
) -> Result<CarryPlan, CarryError> {
    let planned = plan(store, carrying)?;
    write(store, planned)
}

/// Write a plan already worked out, documents before revisions.
///
/// Split from [`carry`] because decision 0059's inline acts plan their
/// carries against a rewrite the store is only provisionally holding, and
/// then write the rewrite and the carries together — so the plan and the
/// writing of it are two moments there, where the repair has one.
pub(crate) fn write<F: Filesystem>(
    store: &mut Store<F>,
    planned: CarryPlan,
) -> Result<CarryPlan, CarryError> {
    for step in &planned.steps {
        let stem = naming::stem_for(
            &step.document.when,
            &step.document.message,
            &step.document.change,
            &step.revision,
            store.documents()?.into_iter().map(|(_, held)| held),
        );
        let filings: Vec<naming::Filing> = step
            .writes
            .iter()
            .map(|(filing, _)| filing.clone())
            .collect();
        let filed = naming::filed(&filings);
        for (filing, document) in &step.writes {
            let name = match filed.get(&filing.held) {
                Some(name) => format!("{stem}/{name}"),
                None => filing.held.to_string(),
            };
            store
                .insert_operation_at(document, &name)
                .map_err(CarryError::Store)?;
        }
        store
            .insert_at(&step.document, &format!("{stem}{REVISION_SUFFIX}"))
            .map_err(CarryError::Store)?;
    }
    Ok(planned)
}

/// Why nothing was carried.
#[derive(Debug)]
#[non_exhaustive]
pub enum CarryError {
    /// A named revision this store does not hold.
    NotHeld {
        /// The revision as it was named.
        revision: RevisionId,
    },
    /// A named revision that does not stand on a rewritten one.
    NotStranded {
        /// The revision as it was named.
        revision: RevisionId,
    },
    /// A merge named as the thing to move.
    ///
    /// Decision 0059 refuses a merge above moved content because its
    /// parents' agreement would have to be recomputed. A merge asked to
    /// stand somewhere new is the same work, asked directly.
    MovingAMerge {
        /// The revision as it was named.
        revision: RevisionId,
    },
    /// A revision with no parent named as the thing to move.
    ///
    /// Where a history starts is not a thing that stands somewhere; a
    /// history that started somewhere else is a different history.
    MovingARoot {
        /// The revision as it was named.
        revision: RevisionId,
    },
    /// A move onto the parent the revision already has.
    AlreadyThere {
        /// The revision as it was named.
        revision: RevisionId,
        /// The destination, which is where it already stands.
        onto: RevisionId,
    },
    /// A move onto a revision that is itself moving.
    ///
    /// The result would stand on a superseded revision by construction: the
    /// half-finished rewrite `carry` repairs, manufactured deliberately.
    MovingOntoItself {
        /// The revision as it was named.
        revision: RevisionId,
        /// The destination, which is among what would move.
        onto: RevisionId,
    },
    /// A superseded parent whose rewrite has two current revisions.
    DivergentRewrite {
        /// The parent that was withdrawn.
        superseded: RevisionId,
        /// The rewrites, between which nothing here can choose.
        successors: BTreeSet<RevisionId>,
    },
    /// A merge standing above content the rewrite moved.
    ///
    /// Its parents' agreement would have to be recomputed and its
    /// resolution's references renumbered, which is work this version
    /// refuses rather than guesses at.
    MergeAboveMovedContent {
        /// The merge.
        revision: RevisionId,
    },
    /// A rewrite that folded two of a revision's parents into one.
    CollapsedParents {
        /// The revision whose parents collapsed.
        revision: RevisionId,
    },
    /// A path this revision states that the rewrite also introduced.
    PathTaken {
        /// The revision.
        revision: RevisionId,
        /// The path two files would claim.
        path: String,
    },
    /// A fact about a file the rewrite removed.
    LostByRewrite {
        /// The revision stating it.
        revision: RevisionId,
        /// Where the file sat before the rewrite removed it.
        path: String,
    },
    /// A whole payload this revision states where the rewrite states another.
    ContestedPayload {
        /// The revision.
        revision: RevisionId,
        /// The file whose bytes are contested.
        file: FileId,
    },
    /// A restated span the rewrite also touched.
    ///
    /// Decision 0027: contested regions are ephemeral and never recorded, so
    /// a carry that meets one refuses and a person resolves it — by amending
    /// the work onto the successor by hand, or abandoning what stands.
    Contested {
        /// The revision whose operations met the rewrite's.
        revision: RevisionId,
        /// The file they met in.
        file: FileId,
        /// How many regions they met in.
        regions: usize,
    },
    /// A restated file whose history has forgotten something.
    ///
    /// The stand-in has no bytes to re-diff, and recording the marker's text
    /// as content would launder a redaction into authority.
    Forgotten {
        /// The revision.
        revision: RevisionId,
        /// The file a forgetting reaches.
        file: FileId,
    },
    /// A carry that would state nothing at all.
    CarriedToNothing {
        /// The revision whose whole statement the rewrite already makes.
        revision: RevisionId,
    },
    /// An `edit` naming an operation document this store does not hold.
    MissingOperations {
        /// The revision naming it.
        revision: RevisionId,
        /// The document nothing here holds.
        document: RevisionId,
    },
    /// A cause with no `revised` to derive from, which no writer produces.
    UnstampedCause {
        /// The revision being carried.
        revision: RevisionId,
        /// The successor with no stamp on it.
        cause: RevisionId,
    },
    /// The merge machinery refused the synthetic replay.
    Merge(MergeError),
    /// A base state refused the operations recorded against it.
    Replay(ReplayError),
    /// A tree or content could not be produced.
    Materialise(Box<MaterialiseError>),
    /// The store could not be read or written.
    Store(StoreError),
}

impl From<StoreError> for CarryError {
    fn from(error: StoreError) -> Self {
        Self::Store(error)
    }
}

impl From<MaterialiseError> for CarryError {
    fn from(error: MaterialiseError) -> Self {
        Self::Materialise(Box::new(error))
    }
}

impl fmt::Display for CarryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CarryError::NotHeld { revision } => write!(
                f,
                "this store does not hold the revision {revision}, so there is \
                 nothing here to carry"
            ),
            CarryError::MovingAMerge { revision } => write!(
                f,
                "{} is a merge, and standing it somewhere new would mean \
                 working out afresh what its parents agree on — which is \
                 real work rather than something to guess at on anyone's \
                 behalf",
                revision.abbreviate(12)
            ),
            CarryError::MovingARoot { revision } => write!(
                f,
                "{} is where this history starts, and a history that started \
                 somewhere else is a different history",
                revision.abbreviate(12)
            ),
            CarryError::AlreadyThere { revision, onto } => write!(
                f,
                "{} already stands on {}, so there is nothing to restate",
                revision.abbreviate(12),
                onto.abbreviate(12)
            ),
            CarryError::MovingOntoItself { revision, onto } => write!(
                f,
                "{} stands on {}, which is part of what moving {} would \
                 restate — the result would stand on a revision this act \
                 supersedes",
                onto.abbreviate(12),
                revision.abbreviate(12),
                revision.abbreviate(12)
            ),
            CarryError::NotStranded { revision } => write!(
                f,
                "{} does not stand on a rewritten revision, so there is \
                 nothing to carry it across",
                revision.abbreviate(12)
            ),
            CarryError::DivergentRewrite {
                superseded,
                successors,
            } => write!(
                f,
                "{} was rewritten two ways, and nothing here can choose which \
                 rewrite to carry the work onto; abandon one of them \
                 first:{}",
                superseded.abbreviate(12),
                successors
                    .iter()
                    .map(|id| format!("\n  {}", id.abbreviate(12)))
                    .collect::<String>()
            ),
            CarryError::MergeAboveMovedContent { revision } => write!(
                f,
                "{} is a merge, and the rewrite moved content beneath it; \
                 restating a merge means recomputing what its parents agreed \
                 on, which is not built — amend the work onto the rewrite by \
                 hand, tip first",
                revision.abbreviate(12)
            ),
            CarryError::CollapsedParents { revision } => write!(
                f,
                "the rewrite folded two of {}'s parents into one revision, \
                 and carrying it would quietly turn a merge into a chain",
                revision.abbreviate(12)
            ),
            CarryError::PathTaken { revision, path } => write!(
                f,
                "{} puts a file at `{path}`, and the rewrite also put one \
                 there; two files cannot hold one path, so say where each \
                 goes by amending the work onto the rewrite by hand",
                revision.abbreviate(12)
            ),
            CarryError::LostByRewrite { revision, path } => write!(
                f,
                "{} says something about `{path}`, which the rewrite removed; \
                 what stands on the removal has to be restated by hand",
                revision.abbreviate(12)
            ),
            CarryError::ContestedPayload { revision, file } => write!(
                f,
                "{} and the rewrite state different bytes for {file}, and \
                 nothing here can choose between attachments; record the one \
                 that is meant, by hand",
                revision.abbreviate(12)
            ),
            CarryError::Contested {
                revision,
                file,
                regions,
            } => write!(
                f,
                "what {} did and what the rewrite did meet in {} of one \
                 file ({file}); resolving concurrent work is a person's, so \
                 amend it onto the rewrite by hand",
                revision.abbreviate(12),
                if *regions == 1 {
                    "one region".to_owned()
                } else {
                    format!("{regions} regions")
                }
            ),
            CarryError::Forgotten { revision, file } => write!(
                f,
                "restating what {} did to {file} would re-record content a \
                 forgetting destroyed, which no carry may do; amend the work \
                 onto the rewrite by hand",
                revision.abbreviate(12)
            ),
            CarryError::CarriedToNothing { revision } => write!(
                f,
                "everything {} states, the rewrite already states, and a \
                 revision saying nothing would mean nothing; abandon it \
                 instead, with the reason",
                revision.abbreviate(12)
            ),
            CarryError::MissingOperations { revision, document } => write!(
                f,
                "restating {} needs the operation document {}, which is not \
                 here yet",
                revision.abbreviate(12),
                document.abbreviate(12)
            ),
            CarryError::UnstampedCause { revision, cause } => write!(
                f,
                "{} would take its `revised` from {}, which carries none — a \
                 revision that supersedes without a stamp is one no writer \
                 produces",
                revision.abbreviate(12),
                cause.abbreviate(12)
            ),
            CarryError::Merge(error) => error.fmt(f),
            CarryError::Replay(error) => error.fmt(f),
            CarryError::Materialise(error) => error.fmt(f),
            CarryError::Store(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for CarryError {}
