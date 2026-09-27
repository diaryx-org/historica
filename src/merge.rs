//! Merging concurrent branches by replaying their event graph.
//!
//! Decision 0007 chose Eg-walker (Gentle and Kleppmann, EuroSys 2025): the
//! stored artifacts are operations and their causal edges, and the structure
//! that resolves concurrency is built during a walk of that graph and thrown
//! away at the end. Nothing here is written to disk, which is what lets
//! `cache/` be genuinely disposable rather than nominally so.
//!
//! The walk works like this. Every revision is an event, and its operations
//! are stated against the state at its parents — so replaying an event needs
//! the list of items that were *visible to its author*, which is a filter over
//! the transient structure by causal past. Positions are turned into item
//! identities against that view; identities are then integrated into one
//! shared structure whose in-order reading is the merged file.
//!
//! Two things follow from decision 0007 and are load-bearing:
//!
//! - **An item's name is derived, never stored.** Item *i* of revision *R* is
//!   named `(R, i)`, and `R` is a digest of bytes a person can read. Ordering
//!   ties are broken by that name — by digest, then by index — because 0002
//!   refuses to trust a timestamp and 0001 calls a change ID an unverifiable
//!   claim.
//! - **The linear case costs nothing.** A history with no concurrency in it
//!   never reaches this module: [`crate::replay`] applies it directly, and
//!   this returns the same bytes for the same input.
//!
//! The ordering rule is Fugue's (Weidner and Kleppmann), for the reason 0007
//! gives: it carries the strongest published guarantee against interleaving,
//! and interleaved text is the least readable thing a merge can produce. It is
//! implemented as the tree formulation, in `anchor` and `Tree::order`, and
//! kept in one place because 0007 owes it a conformance suite against the
//! reference implementation before any of this is called done.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::ancestry::Ancestry;
use crate::core::RevisionId;
use crate::format::{Item, Operation, OperationDocument, OperationKind, Piece, ResolutionDocument};
use crate::replay::State;

#[cfg(verus_keep_ghost)]
use crate::ancestry;
#[cfg(verus_keep_ghost)]
use crate::format::proof::{ItemS, PieceS};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
pub(crate) mod proof;

/// What one revision stated about one file.
///
/// Two spellings, and decision 0032 is the second: a revision either says what
/// it *did* to the file, against the state at its parents, or — where a merge's
/// parents disagree — says what the file *is*, whole, by reference.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy)]
pub enum Stated<'a> {
    /// Decision 0007's operations, positioned into the state at the parents.
    Operations(&'a OperationDocument),
    /// Decision 0032's resolution: the file at this merge, stated whole.
    Resolution(&'a ResolutionDocument),
}

/// One revision's contribution to one file.
///
/// A revision that changed nothing about the file still appears, because its
/// causal edges are part of the graph the merge walks.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct Event<'a> {
    /// The revision this is.
    pub revision: RevisionId,
    /// Its causal parents.
    pub parents: Vec<RevisionId>,
    /// What it stated about this file, beside the digest naming the document
    /// it stated it in — an operation document's, a resolution's, or the
    /// payload's for a file that arrived whole.
    ///
    /// The digest is the half of an item's name a `keep` line quotes, which is
    /// why it travels with the document rather than being recomputed: a
    /// redacted document's bytes are not the bytes its revision named.
    pub stated: Option<(RevisionId, Stated<'a>)>,
}

impl<'a> Event<'a> {
    /// An event that says nothing about this file.
    pub fn nothing(revision: RevisionId, parents: Vec<RevisionId>) -> Self {
        Self {
            revision,
            parents,
            stated: None,
        }
    }

    /// An event stating operations, named by `document`.
    pub fn operations(
        revision: RevisionId,
        parents: Vec<RevisionId>,
        document: RevisionId,
        operations: &'a OperationDocument,
    ) -> Self {
        Self {
            revision,
            parents,
            stated: Some((document, Stated::Operations(operations))),
        }
    }

    /// An event stating a resolution, named by `document`.
    pub fn resolution(
        revision: RevisionId,
        parents: Vec<RevisionId>,
        document: RevisionId,
        resolution: &'a ResolutionDocument,
    ) -> Self {
        Self {
            revision,
            parents,
            stated: Some((document, Stated::Resolution(resolution))),
        }
    }

    /// The operations this event states, if that is what it states.
    fn operation_document(&self) -> Option<(RevisionId, &'a OperationDocument)> {
        match self.stated {
            Some((named, Stated::Operations(document))) => Some((named, document)),
            _ => None,
        }
    }

    /// Whether this event states its file by reference rather than by delta.
    fn resolves(&self) -> bool {
        matches!(self.stated, Some((_, Stated::Resolution(_))))
    }
}

/// A merged file, and where concurrent work met inside it.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct Merged {
    /// The merged content.
    pub state: State,
    /// Which revision wrote each item, in the same order as the items.
    ///
    /// Derived like everything else a merge produces — item *i* of revision
    /// *R* is named `(R, i)` — and returned because decision 0012's rendering
    /// labels each run inside a contested span with the revision that wrote
    /// it, which is more than a three-way tool can say.
    pub origins: Vec<RevisionId>,
    /// The name a `keep` line quotes for each item, in the same order.
    ///
    /// The document that minted the item, and its ordinal in that document's
    /// order. Decision 0032: this is what turns a proposed merge into a
    /// resolution — the surviving items are named rather than restated, so
    /// they keep the identities a later merge across this one needs.
    pub references: Vec<(RevisionId, usize)>,
    /// Where two branches touched one region. Never written to disk.
    pub contested: Vec<Contested>,
}

/// One region where concurrent revisions met.
///
/// Decision 0007: "Replay therefore returns two things: the merged content,
/// and the spans where concurrent operations touched one region." This is the
/// second, and it is a report rather than a conflict — a tool may decline to
/// record an automatic merge and show a person both versions instead, which is
/// the legitimate divergence 0001 already has vocabulary for.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct Contested {
    /// Where the region begins, as an item index into the merged file.
    pub at: usize,
    /// How many items it covers. Zero for a contest over items that are gone.
    pub len: usize,
    /// The revisions whose concurrent work met here, in digest order.
    pub revisions: Vec<RevisionId>,
    /// What kind of meeting it was.
    pub kind: Contest,
}

/// What made a region contested.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Contest {
    /// Concurrent revisions inserted at one position, and the tie was broken.
    Insertion,
    /// One revision removed an item another concurrently wrote next to.
    Deletion,
    /// Concurrent revisions disagree about the file's last terminator.
    ///
    /// Decision 0007's third open question, arriving where it said it would.
    Terminator,
}

/// Merge every event's contribution to one file.
///
/// The events may arrive in any order and are sorted causally here, ties by
/// digest, so that the result does not depend on the order a store happened to
/// read its files in.
pub fn merge<'a>(events: impl IntoIterator<Item = Event<'a>>) -> Result<Merged, MergeError> {
    let graph = Graph::new(events.into_iter().collect())?;
    // A resolution is a merge's spelling, so a chain holding one is a history
    // nothing here wrote; the walk is what knows how to cross it, and the fast
    // path stays the arithmetic it was.
    if graph.chain() && !graph.events.iter().any(|event| event.resolves()) {
        return linear(&graph);
    }
    let order = graph.order.clone();
    walk(&graph, &order)
}

/// The merged file of a history with nothing concurrent in it.
///
/// Decision 0007 promised this and named the reason:
///
/// > When no two operations in the region are concurrent — one person, one
/// > device, or any history that has already been merged — the internal
/// > structure is never built and replay is application.
///
/// Application is all it is. Positions are stated against the state at the
/// parent, and in a chain that state is simply the file so far, so a
/// revision's operations are read against one frozen view and then applied as
/// arithmetic. No element identities are minted, no tree is built, no ancestry
/// is consulted, and nothing is tombstoned: a deleted item is gone at the end
/// of the revision that deleted it, because in a chain nothing can arrive
/// later that needed to see it.
///
/// This must agree with [`walk`] byte for byte on every history both can
/// express, including `origins` and the terminator report — the tests hold it
/// to that over generated chains rather than trusting the argument.
fn linear(graph: &Graph<'_>) -> Result<Merged, MergeError> {
    let mut items: Vec<Item> = Vec::new();
    let mut origins: Vec<RevisionId> = Vec::new();
    let mut references: Vec<(RevisionId, usize)> = Vec::new();

    for event in &graph.order {
        let Some((named, document)) = graph.events[*event].operation_document() else {
            continue;
        };
        let revision = graph.events[*event].revision;
        let length = items.len();
        let mut removed = vec![false; length];
        let mut added: BTreeMap<usize, Vec<Item>> = BTreeMap::new();

        // Every position is counted into the state at the parent, so all of
        // them are read before any of them moves anything.
        for operation in &document.operations {
            match operation.kind {
                OperationKind::Delete => {
                    let end = operation.at.saturating_add(operation.items.len());
                    if end > length {
                        return Err(MergeError::OutOfRange {
                            revision,
                            position: end,
                            length,
                        });
                    }
                    for (offset, recorded) in operation.items.iter().enumerate() {
                        let position = operation.at + offset;
                        let found = &items[position];
                        // A forgotten item on either side matches, per
                        // decision 0014, exactly as it does in the walk.
                        if !recorded.matches(found) {
                            return Err(MergeError::ItemDisagrees {
                                revision,
                                position,
                                recorded: recorded.text.clone(),
                                found: found.text.clone(),
                            });
                        }
                        removed[position] = true;
                    }
                }
                OperationKind::Insert => {
                    if operation.at > length {
                        return Err(MergeError::OutOfRange {
                            revision,
                            position: operation.at,
                            length,
                        });
                    }
                    added
                        .entry(operation.at)
                        .or_default()
                        .extend(operation.items.iter().cloned());
                }
            }
        }

        // An insert at a position goes before whatever the parent held there,
        // which is where the walk's anchoring puts it too; an insert at the
        // end names the gap past the last item.
        let mut kept: Vec<Item> = Vec::with_capacity(length);
        let mut wrote: Vec<RevisionId> = Vec::with_capacity(length);
        let mut named_by: Vec<(RevisionId, usize)> = Vec::with_capacity(length);
        // How many items this document has minted so far, which is the
        // ordinal half of the name a `keep` quotes.
        let mut minted = 0usize;
        for position in 0..=length {
            if let Some(new) = added.remove(&position) {
                wrote.extend(std::iter::repeat_n(revision, new.len()));
                named_by.extend((minted..minted + new.len()).map(|at| (named, at)));
                minted += new.len();
                kept.extend(new);
            }
            if position < length && !removed[position] {
                kept.push(items[position].clone());
                wrote.push(origins[position]);
                named_by.push(references[position]);
            }
        }
        items = kept;
        origins = wrote;
        references = named_by;
    }

    Ok(Merged {
        contested: terminators(&items),
        origins,
        references,
        state: State::from_items(items),
    })
}

/// One item of one file, and everywhere its bytes are quoted.
///
/// Decision 0014: a paragraph inserted by revision *R* and deleted by
/// revision *S* has its bytes in two documents — *R*'s insert, and *S*'s
/// delete, which quotes it verbatim so replay can check itself. `forget`
/// walks the file's history for every one of those quotes, and this is that
/// walk's result.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct Quoted {
    /// The revision that wrote the item.
    pub written_by: RevisionId,
    /// Which operation and item of that revision's document wrote it.
    pub write: (usize, usize),
    /// The item's text, as the document that wrote it states it. Empty for an
    /// item already forgotten, whose text is what was destroyed.
    pub text: String,
    /// Every deletion quoting it: the deleting revision, and which operation
    /// and item of its document hold the quote.
    pub deletes: Vec<(RevisionId, usize, usize)>,
    /// Every revision that dropped it without quoting it — which is how a
    /// resolution removes an item, decision 0032 stating what survives rather
    /// than what went.
    ///
    /// Separate from `deletes` because there is nothing in such a removal to
    /// redact, and because it is the other half of a fact `forget` needs: a
    /// resolution that drops an item and mints one reading the same has
    /// copied it, which is the only way a merge can restate text that already
    /// had a name.
    pub dropped_by: Vec<RevisionId>,
    /// Whether the item's text is already destroyed where it was written.
    pub forgotten: bool,
    /// Whether the item is in the merged file, or a tombstone.
    pub visible: bool,
}

/// Every item every event ever wrote to one file, in reading order.
///
/// Tombstones included, because a forgotten paragraph is usually one somebody
/// deleted. The visible items, in order, are the merged file — the same one
/// [`merge`] returns.
pub fn quotes<'a>(events: impl IntoIterator<Item = Event<'a>>) -> Result<Vec<Quoted>, MergeError> {
    let graph = Graph::new(events.into_iter().collect())?;
    let tree = built(&graph, &graph.order)?;
    Ok(tree
        .order()
        .into_iter()
        .map(|at| {
            let element = &tree.elements[at];
            // In event order, whatever order the walk met them in.
            let mut deleted_by = element.deleted_by.clone();
            deleted_by.sort_by_key(|(event, _)| *event);
            Quoted {
                written_by: graph.events[element.author].revision,
                write: element.wrote,
                text: element.item.text.clone(),
                deletes: deleted_by
                    .iter()
                    .filter_map(|(event, quote)| {
                        // A resolution drops an item by not keeping it, and a
                        // removal that quotes nothing is nothing to redact.
                        let (operation, item) = (*quote)?;
                        Some((graph.events[*event].revision, operation, item))
                    })
                    .collect(),
                dropped_by: deleted_by
                    .iter()
                    .filter(|(_, quote)| quote.is_none())
                    .map(|(event, _)| graph.events[*event].revision)
                    .collect(),
                forgotten: element.item.forgotten,
                visible: element.deleted_by.is_empty(),
            }
        })
        .collect())
}

/// Every item claiming a terminator the file cannot give it.
///
/// Only a file's last item may lack one. A chain cannot produce a file that
/// breaks that — [`crate::replay`] refuses the document that would — but
/// concurrency can, and decision 0007 left that open; reporting it is what
/// this can honestly do. Shared so the two paths cannot drift.
fn terminators(items: &[Item]) -> Vec<Contested> {
    items
        .iter()
        .enumerate()
        .filter(|(position, item)| !item.terminated && position + 1 != items.len())
        .map(|(position, _)| Contested {
            at: position,
            len: 1,
            revisions: Vec::new(),
            kind: Contest::Terminator,
        })
        .collect()
}

/// Replay a graph in one causal order.
///
/// Which order is a matter of taste and not of result: an element's place in
/// the tree is decided by what its own author had seen, so any order that puts
/// an event after its parents produces the same file. The tests hold that
/// claim to every valid order of a small graph rather than asserting it.
fn walk(graph: &Graph<'_>, order: &[usize]) -> Result<Merged, MergeError> {
    Ok(built(graph, order)?.read(graph))
}

/// Kahn's algorithm: every event once, each after all of its parents, taking
/// the lowest-numbered among those whose parents are all placed. `None`
/// where some event is never placed, which a cycle does.
///
/// Proved: what it returns lists every event once, each after all of its
/// parents. That it refuses only a cycle is argued, not proved.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        forall|e: int, k: int| 0 <= e < parents@.len() && 0 <= k < parents@[e]@.len()
            ==> (#[trigger] parents@[e]@[k] as int) < parents@.len(),
    ensures
        r matches Some(order) ==> ancestry::proof::causal(ancestry::proof::parents_of(parents@), order@),
))]
fn causal_order(parents: &[Vec<usize>]) -> Option<Vec<usize>> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost graph = ancestry::proof::parents_of(parents@);
    }
    let n = parents.len();
    // Which events each event is a parent of: the ones worth looking at
    // again once it is placed.
    let mut children: Vec<Vec<usize>> = Vec::with_capacity(n);
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            children@.len() <= n,
            forall|e: int| 0 <= e < children@.len() ==> (#[trigger] children@[e])@.len() == 0,
        decreases n - children@.len(),
    ))]
    while children.len() < n {
        children.push(Vec::new());
    }
    let mut child: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            child <= n,
            children@.len() == n,
            forall|e: int, k: int| 0 <= e < n && 0 <= k < children@[e]@.len()
                ==> (#[trigger] children@[e]@[k] as int) < n,
        decreases n - child,
    ))]
    while child < n {
        let mut k: usize = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                k <= parents@[child as int]@.len(),
                children@.len() == n,
                forall|e: int, k2: int| 0 <= e < n && 0 <= k2 < children@[e]@.len()
                    ==> (#[trigger] children@[e]@[k2] as int) < n,
            decreases parents@[child as int]@.len() - k,
        ))]
        while k < parents[child].len() {
            let parent = parents[child][k];
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost before = children@; }
            children[parent].push(child);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|e: int, k2: int| 0 <= e < n && 0 <= k2 < children@[e]@.len()
                    implies (#[trigger] children@[e]@[k2] as int) < n by {
                    if e != parent as int {
                        assert(children@[e] == before[e]);
                    } else if k2 < before[e]@.len() {
                        assert(children@[e]@[k2] == before[e]@[k2]);
                    }
                }
            }
            k += 1;
        }
        child += 1;
    }
    let mut placed = vec![false; n];
    // Ready events, highest first, so that the lowest is taken next. Sorting
    // the events by digest makes "lowest index" mean "lowest digest".
    let mut ready: Vec<usize> = Vec::new();
    let mut e = n;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            e <= n,
            placed@.len() == n,
            forall|i: int| 0 <= i < n ==> !#[trigger] placed@[i],
            descending(ready@),
            forall|j: int| 0 <= j < ready@.len() ==> e <= #[trigger] ready@[j] < n,
            forall|j: int| 0 <= j < ready@.len() ==> ready_for(graph, placed@, #[trigger] ready@[j] as int),
        decreases e,
    ))]
    while e > 0 {
        e -= 1;
        if parents[e].is_empty() {
            #[cfg(verus_keep_ghost)]
            proof! { assert(graph[e as int] == parents@[e as int]@); }
            ready.push(e);
        }
    }
    let mut order: Vec<usize> = Vec::with_capacity(n);
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            placed@.len() == n,
            children@.len() == n,
            forall|e: int, k: int| 0 <= e < n && 0 <= k < children@[e]@.len()
                ==> (#[trigger] children@[e]@[k] as int) < n,
            order@.len() <= n,
            forall|i: int| 0 <= i < order@.len() ==> (#[trigger] order@[i] as int) < n,
            forall|i: int, j: int| 0 <= i < j < order@.len() ==> order@[i] != order@[j],
            forall|x: int| 0 <= x < n ==> (#[trigger] placed@[x] <==> order@.contains(x as usize)),
            ancestry::proof::parents_first(graph, order@),
            descending(ready@),
            forall|j: int| 0 <= j < ready@.len() ==> (#[trigger] ready@[j] as int) < n,
            forall|j: int| 0 <= j < ready@.len() ==> ready_for(graph, placed@, #[trigger] ready@[j] as int),
        decreases n - order@.len(),
    ))]
    while let Some(next) = ready.pop() {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(ready_for(graph, placed@, next as int));
            assert forall|i: int| 0 <= i < order@.len() implies #[trigger] order@[i] as int != next as int by {
                if order@[i] == next {
                    assert(order@.contains(next));
                }
            }
            ancestry::proof::lemma_short(order@, n as int, next as int);
            let at = order@.len() as int;
            // Every parent of `next` is placed, so already in the order.
            assert forall|k: int| 0 <= k < graph[next as int].len() implies
                exists|j: int| 0 <= j < at && order@[j] == #[trigger] graph[next as int][k] by {
                let p = graph[next as int][k];
                assert(placed@[p as int]);
                assert(order@.contains(p));
            }
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost was_placed = placed@;
            let ghost was_order = order@;
        }
        placed[next] = true;
        order.push(next);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|x: int| 0 <= x < n implies (#[trigger] placed@[x] <==> order@.contains(x as usize)) by {
                if x != next as int {
                    assert(placed@[x] == was_placed[x]);
                    if order@.contains(x as usize) {
                        let i = choose|i: int| 0 <= i < order@.len() && order@[i] == x as usize;
                        assert(i < order@.len() - 1);
                        assert(was_order[i] == x as usize);
                    }
                    if was_order.contains(x as usize) {
                        let i = choose|i: int| 0 <= i < was_order.len() && was_order[i] == x as usize;
                        assert(order@[i] == x as usize);
                    }
                } else {
                    assert(order@[order@.len() - 1] == next);
                }
            }
            assert forall|j: int| 0 <= j < ready@.len() implies ready_for(graph, placed@, #[trigger] ready@[j] as int) by {
                assert(ready@[j] > next);
                assert forall|k2: int| 0 <= k2 < graph[ready@[j] as int].len()
                    implies #[trigger] placed@[graph[ready@[j] as int][k2] as int] by {
                    assert(was_placed[graph[ready@[j] as int][k2] as int]);
                }
            }
            assert(order@ =~= was_order.push(next));
            assert forall|k2: int| 0 <= k2 < graph[next as int].len()
                implies was_order.contains(#[trigger] graph[next as int][k2]) by {
                let p = graph[next as int][k2];
                assert(was_placed[p as int]);
            }
            ancestry::proof::lemma_parents_first_push(graph, was_order, next);
        }
        let mut c: usize = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                c <= children@[next as int]@.len(),
                descending(ready@),
                forall|j: int| 0 <= j < ready@.len() ==> (#[trigger] ready@[j] as int) < n,
                forall|j: int| 0 <= j < ready@.len() ==> ready_for(graph, placed@, #[trigger] ready@[j] as int),
            decreases children@[next as int]@.len() - c,
        ))]
        while c < children[next].len() {
            let child = children[next][c];
            if !placed[child] && all_placed(&parents[child], &placed) {
                #[cfg(verus_keep_ghost)]
                proof_decl! {
                    assert(graph[child as int] == parents@[child as int]@);
                    let ghost before = ready@;
                }
                add_ready(&mut ready, child);
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert forall|j: int| 0 <= j < ready@.len() implies
                        (#[trigger] ready@[j] as int) < n && ready_for(graph, placed@, ready@[j] as int) by {
                        assert(ready@.contains(ready@[j]));
                        if ready@[j] != child {
                            assert(before.contains(ready@[j]));
                            let i = choose|i: int| 0 <= i < before.len() && before[i] == ready@[j];
                        }
                    }
                }
            }
            c += 1;
        }
    }
    if order.len() == n {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(order@.len() == graph.len());
            assert forall|i: int| 0 <= i < order@.len() implies (#[trigger] order@[i] as int) < graph.len() by {}
            assert forall|i: int, j: int| 0 <= i < j < order@.len() implies order@[i] != order@[j] by {}
        }
        Some(order)
    } else {
        None
    }
}

/// Whether every one of `of` is placed.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        forall|k: int| 0 <= k < of@.len() ==> (#[trigger] of@[k] as int) < placed@.len(),
    ensures
        r == forall|k: int| 0 <= k < of@.len() ==> #[trigger] placed@[of@[k] as int],
))]
fn all_placed(of: &[usize], placed: &[bool]) -> bool {
    let mut k: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            k <= of@.len(),
            forall|k2: int| 0 <= k2 < of@.len() ==> (#[trigger] of@[k2] as int) < placed@.len(),
            forall|k2: int| 0 <= k2 < k ==> #[trigger] placed@[of@[k2] as int],
        decreases of@.len() - k,
    ))]
    while k < of.len() {
        if !placed[of[k]] {
            return false;
        }
        k += 1;
    }
    true
}

/// Put `event` among the ready, highest first, once.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires
        descending(old(ready)@),
    ensures
        descending(final(ready)@),
        forall|x: usize| #[trigger] final(ready)@.contains(x) <==> (old(ready)@.contains(x) || x == event),
))]
fn add_ready(ready: &mut Vec<usize>, event: usize) {
    let mut at: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            at <= ready@.len(),
            ready@ == old(ready)@,
            descending(ready@),
            forall|j: int| 0 <= j < at ==> #[trigger] ready@[j] > event,
        decreases ready@.len() - at,
    ))]
    while at < ready.len() && ready[at] > event {
        at += 1;
    }
    if at < ready.len() && ready[at] == event {
        return;
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before = ready@; }
    ready.insert(at, event);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|i: int, j: int| 0 <= i < j < ready@.len() implies #[trigger] ready@[i] > #[trigger] ready@[j] by {
            if j < at as int {
            } else if i < at as int && j == at as int {
            } else if i < at as int {
                assert(ready@[j] == before[j - 1]);
                assert(before[i] > before[j - 1] || i == j - 1);
            } else if i == at as int {
                assert(ready@[j] == before[j - 1]);
                if at < before.len() {
                    assert(before[at as int] < event);
                    assert(before[at as int] >= before[j - 1]);
                }
            } else {
                assert(ready@[i] == before[i - 1]);
                assert(ready@[j] == before[j - 1]);
            }
        }
        assert forall|x: usize| #[trigger] ready@.contains(x) <==> (before.contains(x) || x == event) by {
            if ready@.contains(x) {
                let i = choose|i: int| 0 <= i < ready@.len() && ready@[i] == x;
                if i < at as int { assert(before[i] == x); }
                else if i > at as int { assert(before[i - 1] == x); }
            }
            if before.contains(x) {
                let i = choose|i: int| 0 <= i < before.len() && before[i] == x;
                if i < at as int { assert(ready@[i] == x); } else { assert(ready@[i + 1] == x); }
            }
            if x == event {
                assert(ready@[at as int] == event);
            }
        }
    }
}

/// Replay a graph in one order, to the tree whose reading is the merged file.
///
/// Proved to build exactly what the model's `walk` builds, and to refuse
/// exactly where it refuses, for any order that names each event once; the
/// model's `theorem_convergence` is that any two causal orders build trees
/// reading the same file.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        graph.holds(),
        forall|k: int| 0 <= k < order@.len() ==> #[trigger] order@[k] < graph.events@.len(),
        forall|i: int, j: int| 0 <= i < order@.len() && 0 <= j < order@.len() && i != j
            ==> order@[i] != order@[j],
    ensures
        (r is Ok <==> proof::walk(graph@, proof::ints(order@), order@.len() as int) is Some),
        r matches Ok(tree) ==> {
            &&& tree@ == proof::walk(graph@, proof::ints(order@), order@.len() as int)->Some_0
            &&& tree.holds(graph.events@.len())
        },
))]
fn built(graph: &Graph<'_>, order: &[usize]) -> Result<Tree, MergeError> {
    let mut tree = Tree {
        elements: Vec::new(),
        root: Vec::new(),
    };
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost g = graph@;
        let ghost walking = proof::ints(order@);
        assert(tree@.nodes =~= Seq::<proof::Node>::empty());
        assert(tree@.children(None, true) == Seq::<int>::empty());
        assert(proof::ints(tree.root@) =~= Seq::<int>::empty());
    }
    let mut k: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            k <= order@.len(),
            graph.holds(),
            g == graph@,
            walking == proof::ints(order@),
            forall|j: int| 0 <= j < order@.len() ==> #[trigger] order@[j] < graph.events@.len(),
            forall|i: int, j: int| 0 <= i < order@.len() && 0 <= j < order@.len() && i != j
                ==> order@[i] != order@[j],
            tree.holds(graph.events@.len()),
            proof::distinct_names(tree@),
            forall|i: int| 0 <= i < tree.elements@.len() ==> exists|j: int| 0 <= j < k
                && order@[j] == (#[trigger] tree.elements@[i]).author,
            proof::walk(g, walking, k as int) == Some(tree@),
        decreases order@.len() - k,
    ))]
    while k < order.len() {
        let event = order[k];
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            // Nothing is by `event` yet: every element is by an event walked
            // already, and the order names each event once.
            assert forall|i: int| tree@.node(i) && (#[trigger] tree@.nodes[i]).author == event as int
                implies tree@.nodes[i].minted < 0 by {
                assert(tree@.nodes[i] == tree.elements@[i]@);
                let j = choose|j: int| 0 <= j < k && order@[j] == tree.elements@[i].author;
            }
            let ghost before = tree.elements@;
            assert(walking[k as int] == event as int);
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost walked = tree@; }
        let replayed = tree.replay(graph, event);
        #[cfg(verus_keep_ghost)]
        proof! {
            // A walk that refuses one event refuses the whole order.
            assert(proof::walk(g, walking, k as int + 1) == proof::replay_event(walked, g, event as int));
            if replayed is Err && proof::walk(g, walking, order@.len() as int) is Some {
                proof::lemma_walk_some_prefix(g, walking, k as int + 1, order@.len() as int);
            }
        }
        replayed?;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|i: int| 0 <= i < tree.elements@.len() implies exists|j: int| 0 <= j < k + 1
                && order@[j] == (#[trigger] tree.elements@[i]).author by {
                if i < before.len() {
                    let j = choose|j: int| 0 <= j < k && order@[j] == before[i].author;
                    assert(order@[j] == tree.elements@[i].author);
                } else {
                    assert(order@[k as int] == tree.elements@[i].author);
                }
            }
        }
        k += 1;
    }
    Ok(tree)
}

/// The event graph, indexed and causally ordered.
#[cfg_attr(verus_keep_ghost, verus_verify)]
struct Graph<'a> {
    events: Vec<Event<'a>>,
    /// Which events each event had seen.
    ancestry: Ancestry,
    /// Causal order, ties broken by digest.
    order: Vec<usize>,
}

impl<'a> Graph<'a> {
    fn new(mut events: Vec<Event<'a>>) -> Result<Self, MergeError> {
        events.sort_by_key(|event| event.revision);
        let index: BTreeMap<RevisionId, usize> = events
            .iter()
            .enumerate()
            .map(|(index, event)| (event.revision, index))
            .collect();

        let mut parents: Vec<Vec<usize>> = Vec::with_capacity(events.len());
        for event in &events {
            let mut of = Vec::new();
            for parent in &event.parents {
                let found = index.get(parent).ok_or(MergeError::MissingParent {
                    parent: *parent,
                    named_by: event.revision,
                })?;
                of.push(*found);
            }
            parents.push(of);
        }

        Self::from(events, parents)
    }

    /// Whether this graph is one chain, so nothing in it is concurrent.
    fn chain(&self) -> bool {
        matches!(self.ancestry, Ancestry::Chain { .. })
    }

    /// Whether neither of these two events had seen the other.
    fn concurrent(&self, one: usize, other: usize) -> bool {
        one != other && !self.ancestry.knows(one, other) && !self.ancestry.knows(other, one)
    }
}

#[cfg_attr(verus_keep_ghost, cfg_eval, verus_verify)]
impl<'a> Graph<'a> {
    /// The graph of `events`, already in digest order, whose parents are
    /// `parents` by index: walked in causal order, and asked what each event
    /// had seen.
    ///
    /// Proved: the ancestry it holds is a partial order and the order it
    /// walks is causal under it, which is what the walk's convergence theorem
    /// asks of a graph. That `Graph::new` indexed the parents right is read,
    /// not proved.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            parents@.len() == events@.len(),
            forall|e: int, k: int| 0 <= e < parents@.len() && 0 <= k < parents@[e]@.len()
                ==> (#[trigger] parents@[e]@[k] as int) < parents@.len(),
            parents@.len() + 63 <= usize::MAX,
            parents@.len() * ((parents@.len() + 63) / 64) <= usize::MAX,
        ensures
            r matches Ok(graph) ==> {
                &&& graph.holds()
                &&& graph.events@ == events@
                &&& graph@.wf()
                &&& proof::valid_order(graph@, proof::ints(graph.order@))
            },
    ))]
    fn from(events: Vec<Event<'a>>, parents: Vec<Vec<usize>>) -> Result<Self, MergeError> {
        let order = match causal_order(&parents) {
            Some(order) => order,
            None => return Err(MergeError::Cycle),
        };
        let ancestry = Ancestry::new(&order, &parents);
        let graph = Graph {
            events,
            ancestry,
            order,
        };
        #[cfg(verus_keep_ghost)]
        proof! { lemma_graph_sound(&graph, ancestry::proof::parents_of(parents@)); }
        Ok(graph)
    }
}

#[cfg_attr(verus_keep_ghost, cfg_eval, verus_verify)]
impl Graph<'_> {
    /// Whether the author of `event` had seen `other`, or is `other`.
    ///
    /// The view an insertion is placed against: an element written earlier by
    /// this same revision is one its author can see, because they wrote it.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.holds(),
            event < self.events@.len(),
            other < self.events@.len(),
        ensures
            r == self@.knows(event as int, other as int),
    ))]
    fn knows(&self, event: usize, other: usize) -> bool {
        self.ancestry.knows(event, other)
    }

    /// Whether `other` is strictly in `event`'s past.
    ///
    /// The view an operation's positions are counted into: what the author had
    /// before they started, which is their parents' state and nothing of their
    /// own.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.holds(),
            event < self.events@.len(),
            other < self.events@.len(),
        ensures
            r == self@.saw(event as int, other as int),
    ))]
    fn saw(&self, event: usize, other: usize) -> bool {
        self.ancestry.saw(event, other)
    }

    /// The events that stated their file in `document`.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            forall|k: int| 0 <= k < r@.len() ==> #[trigger] r@[k] < self.events@.len(),
            forall|a: int| 0 <= a < self.events@.len() ==>
                (proof::states(self@.events[a], document) <==> r@.contains(a as usize)),
    ))]
    fn stating(&self, document: RevisionId) -> Vec<usize> {
        let mut stating: Vec<usize> = Vec::new();
        let mut a: usize = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                a <= self.events@.len(),
                forall|k: int| 0 <= k < stating@.len() ==> #[trigger] stating@[k] < a,
                forall|b: int| 0 <= b < a ==>
                    (proof::states(self@.events[b], document) <==> stating@.contains(b as usize)),
            decreases self.events@.len() - a,
        ))]
        while a < self.events.len() {
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                assert(self@.events[a as int] == self.events@[a as int]@);
                let ghost was = stating@;
            }
            match self.events[a].stated {
                Some((named, _)) if named == document => stating.push(a),
                _ => {}
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|b: int| 0 <= b <= a implies
                    (proof::states(self@.events[b], document) <==> #[trigger] stating@.contains(b as usize)) by {
                    if b < a {
                        if was.contains(b as usize) {
                            let k = choose|k: int| 0 <= k < was.len() && was[k] == b as usize;
                            assert(stating@[k] == b as usize);
                        }
                        if stating@.contains(b as usize) {
                            let k = choose|k: int| 0 <= k < stating@.len() && stating@[k] == b as usize;
                            if k < was.len() {
                                assert(was[k] == b as usize);
                            }
                        }
                    } else if stating@.len() > was.len() {
                        assert(stating@[was.len() as int] == a);
                    }
                }
            }
            a += 1;
        }
        stating
    }
}

/// Which side of its parent an element sits on.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Side {
    Left,
    Right,
}

/// One item in the transient structure, alive or tombstoned.
///
/// Which element it was attached to, and on which side, is written down twice:
/// in `parent` and `side`, and by the child list it was put into, whose
/// in-order reading is the file. The walk reads the lists; the proof reads the
/// fields, and [`Tree::attach`] is the one place either is written.
///
/// Its name is `(author, minted)`: the event that wrote it, and how many items
/// that event had minted before it. Events are indexed in digest order, so the
/// first half compares as decision 0007's digest does, and sibling ties are
/// broken by the name.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug)]
struct Element {
    /// The name a `keep` line quotes: the *document* that minted the item, and
    /// the item's ordinal in that document's order.
    ///
    /// Decision 0032 counts references this way because a person reading a
    /// resolution has the `edit` line in front of them, not the revision's
    /// digest. Its ordinal is the element's `minted`. It is coarser than the
    /// element's name by exactly one case — two concurrent
    /// revisions naming one byte-identical document — where the elements it
    /// cannot tell apart hold the same text but not the same place. A
    /// resolution written against such a view keeps the shared name once per
    /// element, so [`Tree::resolution`] resolves each `keep` to the next
    /// element still standing under the name, in view order — the rule that
    /// makes the walk read the same file the resolution assembles to by hand.
    reference: (RevisionId, usize),
    item: Item,
    /// The event that wrote it.
    author: usize,
    /// Which operation and item of its author's document wrote it.
    ///
    /// `id` cannot say: two operations of one document can spell one index.
    /// `forget` needs the exact line of the exact document, because that is
    /// what it destroys.
    wrote: (usize, usize),
    /// Every event that removed it, and where in that event's document the
    /// removal quotes it. Concurrent deletions agree.
    ///
    /// `None` where the removal quotes nothing: decision 0032's resolution
    /// drops an item by not keeping it, and there is no line of text for a
    /// redaction to chase. In the order the walk met them; one event removes
    /// an element at most once.
    deleted_by: Vec<(usize, Option<(usize, usize)>)>,
    /// The element it was attached to, `None` for the document's top level.
    /// Read only by the proof, which only Verus compiles.
    #[allow(dead_code)]
    parent: Option<usize>,
    /// Which side of `parent` it was attached on. Read only by the proof.
    #[allow(dead_code)]
    side: Side,
    left: Vec<usize>,
    right: Vec<usize>,
}

/// Make room in `slot` for ordinal `minted`, holding nothing new.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures
        final(slot)@.len() > minted,
        final(slot)@.len() >= old(slot)@.len(),
        forall|m: int| 0 <= m < old(slot)@.len() ==> #[trigger] final(slot)@[m] == old(slot)@[m],
        forall|m: int| old(slot)@.len() <= m < final(slot)@.len() ==> #[trigger] final(slot)@[m] is None,
))]
fn pad(slot: &mut Vec<Option<usize>>, minted: usize) {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            slot@.len() >= old(slot)@.len(),
            forall|m: int| 0 <= m < old(slot)@.len() ==> #[trigger] slot@[m] == old(slot)@[m],
            forall|m: int| old(slot)@.len() <= m < slot@.len() ==> #[trigger] slot@[m] is None,
            slot@.len() <= old(slot)@.len() || slot@.len() <= minted + 1,
        decreases minted + 1 - slot@.len(),
    ))]
    while slot.len() <= minted {
        slot.push(None);
    }
}

/// One step of reading the tree out in order: a subtree still to be read, or
/// an element to write down.
#[cfg_attr(verus_keep_ghost, verus_verify)]
enum Work {
    Expand(usize),
    Emit(usize),
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Default)]
struct Tree {
    elements: Vec<Element>,
    /// The document's top level: the root's right children.
    root: Vec<usize>,
}

#[cfg_attr(verus_keep_ghost, cfg_eval, verus_verify)]
impl Tree {
    /// Every element, in the order the document reads.
    ///
    /// Iterative because a file typed from beginning to end is a chain of
    /// right children as deep as the file is long. What the stack holds is
    /// what is still to be read, top first, and it is proved to be read out
    /// in the in-order reading of the tree.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.holds_shape(),
        ensures
            proof::ints(r@) == self@.order(),
    ))]
    fn order(&self) -> Vec<usize> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost t = self@;
            self.lemma_listed(self.root@, None, true);
            reveal(proof::TreeS::order);
            lemma_read_all_reads(t, proof::ints(self.root@), -1);
        }
        let mut out: Vec<usize> = Vec::with_capacity(self.elements.len());
        let mut stack: Vec<Work> = Vec::with_capacity(self.root.len());
        self.push_reversed(&self.root, &mut stack);
        #[cfg(verus_keep_ghost)]
        proof! { assert(pending(t, Seq::<Work>::empty()) == Seq::<int>::empty()); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                proof::ints(out@) + pending(t, stack@) == t.order(),
                forall|k: int| 0 <= k < stack@.len() ==> match #[trigger] stack@[k] {
                    Work::Expand(at) => at < self.elements@.len(),
                    Work::Emit(_) => true,
                },
            decreases pending(t, stack@).len(), pending(t, stack@).len() - emits(stack@),
        ))]
        while let Some(work) = stack.pop() {
            match work {
                Work::Expand(at) => {
                    #[cfg(verus_keep_ghost)]
                    proof_decl! {
                        let ghost rest = stack@;
                        let ghost element = self.elements@[at as int];
                        self.lemma_listed(element.left@, Some(at as int), false);
                        self.lemma_listed(element.right@, Some(at as int), true);
                        lemma_read_all_reads(t, proof::ints(element.left@), at as int);
                        lemma_read_all_reads(t, proof::ints(element.right@), at as int);
                        assert(t.nodes[at as int] == element@);
                    }
                    let element = &self.elements[at];
                    self.push_reversed(&element.right, &mut stack);
                    #[cfg(verus_keep_ghost)]
                    proof! { lemma_push(t, stack@, Work::Emit(at)); }
                    stack.push(Work::Emit(at));
                    self.push_reversed(&element.left, &mut stack);
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        let (left, right) = (reads(t, proof::ints(element.left@)), reads(t, proof::ints(element.right@)));
                        assert(left + (seq![at as int] + (right + pending(t, rest)))
                            =~= t.read(at as int) + pending(t, rest));
                        lemma_emits_bound(t, stack@);
                    }
                }
                Work::Emit(at) => {
                    out.push(at);
                    #[cfg(verus_keep_ghost)]
                    proof! { lemma_emits_bound(t, stack@); }
                }
            }
        }
        out
    }

    /// Push a subtree to read for each of `siblings`, last first, so that
    /// the stack reads them in their order before what it held.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            forall|k: int| 0 <= k < siblings@.len() ==> #[trigger] siblings@[k] < self.elements@.len(),
            forall|k: int| 0 <= k < old(stack)@.len() ==> match #[trigger] old(stack)@[k] {
                Work::Expand(at) => at < self.elements@.len(),
                Work::Emit(_) => true,
            },
        ensures
            pending(self@, final(stack)@) == reads(self@, proof::ints(siblings@)) + pending(self@, old(stack)@),
            emits(final(stack)@) == emits(old(stack)@),
            forall|k: int| 0 <= k < final(stack)@.len() ==> match #[trigger] final(stack)@[k] {
                Work::Expand(at) => at < self.elements@.len(),
                Work::Emit(_) => true,
            },
    ))]
    fn push_reversed(&self, siblings: &[usize], stack: &mut Vec<Work>) {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost t = self@;
            let ghost below = stack@;
            assert(proof::ints(siblings@).skip(siblings@.len() as int) =~= Seq::<int>::empty());
        }
        let mut c = siblings.len();
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                c <= siblings@.len(),
                pending(t, stack@) == reads(t, proof::ints(siblings@).skip(c as int)) + pending(t, below),
                emits(stack@) == emits(below),
                forall|k: int| 0 <= k < stack@.len() ==> match #[trigger] stack@[k] {
                    Work::Expand(at) => at < self.elements@.len(),
                    Work::Emit(_) => true,
                },
            decreases c,
        ))]
        while c > 0 {
            c -= 1;
            #[cfg(verus_keep_ghost)]
            proof! {
                let more = proof::ints(siblings@).skip(c as int);
                assert(more.drop_first() =~= proof::ints(siblings@).skip(c as int + 1));
                assert(more[0] == siblings@[c as int] as int);
                lemma_push(t, stack@, Work::Expand(siblings@[c as int]));
                assert(reads(t, more) == t.read(more[0]) + reads(t, more.drop_first()));
                assert(reads(t, more) + pending(t, below)
                    =~= t.read(more[0]) + (reads(t, more.drop_first()) + pending(t, below)));
            }
            stack.push(Work::Expand(siblings[c]));
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(proof::ints(siblings@).skip(0) =~= proof::ints(siblings@)); }
    }

    /// One event, replayed onto the tree: what it stated, against what its
    /// author saw. Proved to do exactly what the model's `replay_event` says,
    /// refusing exactly where it refuses.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).holds(graph.events@.len()),
            graph.holds(),
            event < graph.events@.len(),
            proof::distinct_names(old(self)@),
            old(self)@.minted_below(event as int, 0),
        ensures
            final(self).holds(graph.events@.len()),
            proof::distinct_names(final(self)@),
            final(self).elements@.len() >= old(self).elements@.len(),
            forall|i: int| 0 <= i < old(self).elements@.len() ==> {
                &&& (#[trigger] final(self).elements@[i]).author == old(self).elements@[i].author
                &&& final(self).elements@[i].reference == old(self).elements@[i].reference
            },
            forall|i: int| old(self).elements@.len() <= i < final(self).elements@.len()
                ==> (#[trigger] final(self).elements@[i]).author == event,
            (r is Ok <==> proof::replay_event(old(self)@, graph@, event as int) is Some),
            r is Ok ==> final(self)@ == proof::replay_event(old(self)@, graph@, event as int)->Some_0,
    ))]
    fn replay(&mut self, graph: &Graph<'_>, event: usize) -> Result<(), MergeError> {
        #[cfg(verus_keep_ghost)]
        proof! { assert(graph@.events[event as int] == graph.events@[event as int]@); }
        match graph.events[event].stated {
            None => Ok(()),
            Some((named, Stated::Operations(document))) => {
                self.operations(graph, event, named, document)
            }
            Some((named, Stated::Resolution(document))) => {
                self.resolution(graph, event, named, document)
            }
        }
    }

    /// The elements still standing, in the order the document reads: the
    /// merged file, element by element. Proved to be the model's `items`,
    /// read by index.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.holds_shape(),
        ensures
            proof::ints(r@) == proof::sel(self@.order(), |i: int| self@.standing(i)),
            forall|k: int| 0 <= k < r@.len() ==> #[trigger] r@[k] < self.elements@.len(),
    ))]
    fn standing(&self) -> Vec<usize> {
        let order = self.order();
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost t = self@;
            let ghost stands = |i: int| t.standing(i);
            reveal(proof::TreeS::order);
            proof::lemma_read_all_nodes(t, t.children(None, true), -1);
            assert(proof::ints(order@).take(0) =~= Seq::<int>::empty());
        }
        let mut standing: Vec<usize> = Vec::new();
        let mut k: usize = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                k <= order@.len(),
                proof::ints(standing@) == proof::sel(proof::ints(order@).take(k as int), stands),
                forall|j: int| 0 <= j < standing@.len() ==> #[trigger] standing@[j] < self.elements@.len(),
            decreases order@.len() - k,
        ))]
        while k < order.len() {
            let at = order[k];
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                assert(proof::ints(order@)[k as int] == at as int);
                assert(t.node(at as int));
                let ghost upto = proof::ints(order@).take(k as int + 1);
                assert(upto.drop_last() =~= proof::ints(order@).take(k as int));
                assert(upto.last() == at as int);
                let ghost before = standing@;
                let ghost element = self.elements@[at as int];
                assert(t.nodes[at as int] == element@);
                let ghost removers = element.deleted_by@.map_values(|by: (usize, Option<(usize, usize)>)| by.0 as int);
                if element.deleted_by@.len() > 0 {
                    assert(removers.to_set().contains(removers[0]));
                    assert(t.nodes[at as int].deleted.contains(removers[0]));
                    assert(!t.standing(at as int));
                } else {
                    assert(removers =~= Seq::<int>::empty());
                    assert forall|d: int| !(#[trigger] element@.deleted.contains(d)) by {
                        if element@.deleted.contains(d) {
                            assert(removers.contains(d));
                        }
                    }
                    assert(t.standing(at as int));
                }
                assert(stands(at as int) == t.standing(at as int));
            }
            if self.elements[at].deleted_by.is_empty() {
                standing.push(at);
                #[cfg(verus_keep_ghost)]
                proof! { assert(proof::ints(standing@) =~= proof::ints(before).push(at as int)); }
            }
            k += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(proof::ints(order@).take(order@.len() as int) =~= proof::ints(order@)); }
        standing
    }

    /// Decision 0007's operations, replayed against what their author saw.
    ///
    /// Every operation of one revision is stated against the state at its
    /// parents, so that view is computed once and never moves under them.
    /// Proved to do exactly what the model's `replay_ops` says, refusing
    /// exactly where it refuses.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).holds(graph.events@.len()),
            graph.holds(),
            event < graph.events@.len(),
            proof::distinct_names(old(self)@),
            old(self)@.minted_below(event as int, 0),
        ensures
            final(self).holds(graph.events@.len()),
            proof::distinct_names(final(self)@),
            final(self).elements@.len() >= old(self).elements@.len(),
            forall|i: int| 0 <= i < old(self).elements@.len() ==> {
                &&& (#[trigger] final(self).elements@[i]).author == old(self).elements@[i].author
                &&& final(self).elements@[i].reference == old(self).elements@[i].reference
            },
            forall|i: int| old(self).elements@.len() <= i < final(self).elements@.len()
                ==> (#[trigger] final(self).elements@[i]).author == event,
            ({
                let t = old(self)@;
                let replayed = proof::replay_ops(
                    t,
                    graph@,
                    event as int,
                    t.visible(graph@, event as int),
                    document.operations.deep_view(),
                    0,
                    0,
                );
                &&& (r is Ok <==> replayed is Some)
                &&& (r is Ok ==> final(self)@ == replayed->Some_0)
            }),
    ))]
    fn operations(
        &mut self,
        graph: &Graph<'_>,
        event: usize,
        named: RevisionId,
        document: &OperationDocument,
    ) -> Result<(), MergeError> {
        let revision = graph.events[event].revision;
        let order = self.order();
        let prepare = self.visible(&order, graph, event);
        // How many items this document has minted so far, which is the ordinal
        // half of the name decision 0032 lets a `keep` quote, is how many
        // elements it has added.
        let base = self.elements.len();
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost t = self@;
            let ghost g = graph@;
            let ghost ops = document.operations.deep_view();
            let ghost view = proof::ints(prepare@);
            let ghost replayed = proof::replay_ops(t, g, event as int, view, ops, 0, 0);
            proof::lemma_visible_ok(t, g, event as int);
            assert forall|q: int| 0 <= q < prepare@.len() implies #[trigger] prepare@[q] < self.elements@.len() by {
                assert(view[q] == prepare@[q] as int);
            }
        }
        let mut index: usize = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                index <= document.operations@.len(),
                self.holds(graph.events@.len()),
                base <= self.elements@.len(),
                base == old(self).elements@.len(),
                prepare@.len() <= usize::MAX,
                forall|q: int| 0 <= q < prepare@.len() ==> #[trigger] prepare@[q] < self.elements@.len(),
                proof::distinct_names(self@),
                self@.minted_below(event as int, self.elements@.len() - base),
                forall|i: int| 0 <= i < old(self).elements@.len() ==> {
                    &&& (#[trigger] self.elements@[i]).author == old(self).elements@[i].author
                    &&& self.elements@[i].reference == old(self).elements@[i].reference
                },
                forall|i: int| old(self).elements@.len() <= i < self.elements@.len()
                    ==> (#[trigger] self.elements@[i]).author == event,
                replayed == proof::replay_ops(self@, g, event as int, view, ops, index as int,
                    self.elements@.len() - base),
            decreases document.operations@.len() - index,
        ))]
        while index < document.operations.len() {
            let operation = &document.operations[index];
            #[cfg(verus_keep_ghost)]
            proof! { assert(ops[index as int] == operation.deep_view()); }
            let at = operation.at;
            match operation.kind {
                OperationKind::Delete => {
                    let count = operation.items.len();
                    if count > prepare.len() || at > prepare.len() - count {
                        return Err(MergeError::OutOfRange {
                            revision,
                            position: at.saturating_add(count),
                            length: prepare.len(),
                        });
                    }
                    #[cfg(verus_keep_ghost)]
                    proof_decl! { let ghost t = self@; }
                    let deleted = self.delete_run(graph, event, &prepare, index, operation);
                    #[cfg(verus_keep_ghost)]
                    proof! { self.lemma_names_alike(t); }
                    deleted?;
                }
                OperationKind::Insert => {
                    if at > prepare.len() {
                        return Err(MergeError::OutOfRange {
                            revision,
                            position: at,
                            length: prepare.len(),
                        });
                    }
                    let left = if at == 0 { None } else { Some(prepare[at - 1]) };
                    self.insert_run(graph, event, named, base, left, index, &operation.items);
                }
            }
            index += 1;
        }
        Ok(())
    }

    /// One `delete`'s items, each held against the item its author saw at
    /// that position and marked removed by `event`.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).holds(graph.events@.len()),
            graph.holds(),
            event < graph.events@.len(),
            operation.at + operation.items@.len() <= prepare@.len(),
            prepare@.len() <= usize::MAX,
            forall|q: int| 0 <= q < prepare@.len() ==> #[trigger] prepare@[q] < old(self).elements@.len(),
        ensures
            final(self).holds(graph.events@.len()),
            final(self).elements@.len() == old(self).elements@.len(),
            forall|i: int| 0 <= i < old(self).elements@.len() ==> {
                &&& (#[trigger] final(self).elements@[i]).author == old(self).elements@[i].author
                &&& final(self).elements@[i].reference == old(self).elements@[i].reference
            },
            match proof::delete_run(
                old(self)@,
                graph@,
                event as int,
                proof::ints(prepare@),
                operation.at as int,
                operation.items.deep_view(),
                0,
            ) {
                None => r is Err,
                Some(next) => r is Ok && final(self)@ == next,
            },
    ))]
    fn delete_run(
        &mut self,
        graph: &Graph<'_>,
        event: usize,
        prepare: &[usize],
        index: usize,
        operation: &Operation,
    ) -> Result<(), MergeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost g = graph@;
            let ghost view = proof::ints(prepare@);
            let ghost items = operation.items.deep_view();
            let ghost ran = proof::delete_run(self@, g, event as int, view, operation.at as int, items, 0);
        }
        let at = operation.at;
        let mut offset: usize = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                offset <= operation.items@.len(),
                self.holds(graph.events@.len()),
                self.elements@.len() == old(self).elements@.len(),
                forall|i: int| 0 <= i < old(self).elements@.len() ==> {
                    &&& (#[trigger] self.elements@[i]).author == old(self).elements@[i].author
                    &&& self.elements@[i].reference == old(self).elements@[i].reference
                },
                ran == proof::delete_run(self@, g, event as int, view, at as int, items, offset as int),
            decreases operation.items@.len() - offset,
        ))]
        while offset < operation.items.len() {
            let recorded = &operation.items[offset];
            let target = prepare[at + offset];
            let found = &self.elements[target].item;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(items[offset as int] == recorded@);
                assert(view[at + offset] == target as int);
                assert(self@.nodes[target as int] == self.elements@[target as int]@);
            }
            // A forgotten item on either side matches, per decision 0014: the
            // redundancy its text paid for is exactly what was destroyed.
            if !recorded.matches(found) {
                return Err(MergeError::ItemDisagrees {
                    revision: graph.events[event].revision,
                    position: at + offset,
                    recorded: recorded.text.clone(),
                    found: found.text.clone(),
                });
            }
            self.mark(target, event, Some((index, offset)));
            offset += 1;
        }
        Ok(())
    }

    /// Record that `event` removed the element at `target`, and where its
    /// document quotes the removal, if it does.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            old(self).holds_shape(),
            target < old(self).elements@.len(),
        ensures
            final(self).holds_shape(),
            final(self)@ == old(self)@.delete(target as int, event as int),
            final(self).elements@.len() == old(self).elements@.len(),
            forall|i: int| 0 <= i < old(self).elements@.len() ==> {
                &&& (#[trigger] final(self).elements@[i]).author == old(self).elements@[i].author
                &&& final(self).elements@[i].reference == old(self).elements@[i].reference
            },
            forall|events: nat| old(self).holds(events) && event < events ==> #[trigger] final(self).holds(events),
    ))]
    fn mark(&mut self, target: usize, event: usize, quote: Option<(usize, usize)>) {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost before = self.elements@;
            let ghost old_view = self@;
            let ghost marked = self@.delete(target as int, event as int);
        }
        self.elements[target].deleted_by.push((event, quote));
        #[cfg(verus_keep_ghost)]
        proof! {
            let was = before[target as int].deleted_by@.map_values(|by: (usize, Option<(usize, usize)>)| by.0 as int);
            let now = self.elements@[target as int].deleted_by@.map_values(|by: (usize, Option<(usize, usize)>)| by.0 as int);
            assert(now =~= was.push(event as int));
            assert forall|d: int| now.to_set().contains(d) == was.to_set().insert(event as int).contains(d) by {
                if now.contains(d) {
                    let q = choose|q: int| 0 <= q < now.len() && now[q] == d;
                    if q < was.len() {
                        assert(was[q] == d);
                    }
                }
                if was.contains(d) {
                    let q = choose|q: int| 0 <= q < was.len() && was[q] == d;
                    assert(now[q] == d);
                }
                if d == event as int {
                    assert(now[was.len() as int] == d);
                }
            }
            assert(now.to_set() =~= was.to_set().insert(event as int));
            assert(self.elements@[target as int]@.deleted == before[target as int]@.deleted.insert(event as int));
            assert(self@.nodes =~= marked.nodes);
            assert forall|parent: Option<int>, right: bool| #[trigger] self@.children(parent, right)
                == old_view.children(parent, right) by {
                assert forall|i: int| 0 <= i < self@.len() implies #[trigger] proof::placed_alike(old_view, self@, i) by {
                    assert(old_view.nodes[i] == before[i]@);
                }
                proof::lemma_children_placed(old_view, self@, parent, right);
            }
            assert forall|i: int| 0 <= i < self.elements@.len() implies {
                &&& proof::ints((#[trigger] self.elements@[i]).left@) == self@.children(Some(i), false)
                &&& proof::ints(self.elements@[i].right@) == self@.children(Some(i), true)
                &&& match self.elements@[i].parent {
                    Some(p) => p < i,
                    None => self.elements@[i].side is Right,
                }
            } by {
                if i != target {
                    assert(self.elements@[i] == before[i]);
                }
            }
            assert forall|events: nat| old(self).holds(events) && event < events implies #[trigger] self.holds(events) by {
                assert forall|i: int| 0 <= i < self.elements@.len() implies {
                    &&& (#[trigger] self.elements@[i]).author < events
                    &&& forall|k: int| 0 <= k < self.elements@[i].deleted_by@.len()
                        ==> #[trigger] self.elements@[i].deleted_by@[k].0 < events
                } by {
                    if i != target {
                        assert(self.elements@[i] == before[i]);
                    } else {
                        assert forall|k: int| 0 <= k < self.elements@[i].deleted_by@.len()
                            implies #[trigger] self.elements@[i].deleted_by@[k].0 < events by {
                            if k < before[i].deleted_by@.len() {
                                assert(self.elements@[i].deleted_by@[k] == before[i].deleted_by@[k]);
                            }
                        }
                    }
                }
            }
        }
    }

    /// Items inserted in order, each anchored after the one before it. The
    /// last of them is what follows the run, or `left` where there are none.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).holds(graph.events@.len()),
            graph.holds(),
            event < graph.events@.len(),
            base <= old(self).elements@.len(),
            left matches Some(l) ==> l < old(self).elements@.len(),
            proof::distinct_names(old(self)@),
            old(self)@.minted_below(event as int, old(self).elements@.len() - base),
        ensures
            final(self).holds(graph.events@.len()),
            ({
                let (next, minted) = proof::insert_run(
                    old(self)@,
                    graph@,
                    event as int,
                    items.deep_view(),
                    proof::opt(left),
                    old(self).elements@.len() - base,
                );
                &&& final(self)@ == next
                &&& final(self).elements@.len() - base == minted
                &&& final(self).elements@.len() >= old(self).elements@.len()
            }),
            proof::distinct_names(final(self)@),
            final(self)@.minted_below(event as int, final(self).elements@.len() - base),
            forall|i: int| 0 <= i < old(self).elements@.len() ==> {
                &&& (#[trigger] final(self).elements@[i]).author == old(self).elements@[i].author
                &&& final(self).elements@[i].reference == old(self).elements@[i].reference
            },
            forall|i: int| old(self).elements@.len() <= i < final(self).elements@.len()
                ==> (#[trigger] final(self).elements@[i]).author == event,
            items@.len() == 0 ==> r == left,
            items@.len() > 0 ==> (r matches Some(l) && l as int == final(self).elements@.len() - 1),
            r matches Some(l) ==> l < final(self).elements@.len(),
    ))]
    #[allow(clippy::too_many_arguments)]
    fn insert_run(
        &mut self,
        graph: &Graph<'_>,
        event: usize,
        named: RevisionId,
        base: usize,
        left: Option<usize>,
        index: usize,
        items: &[Item],
    ) -> Option<usize> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost g = graph@;
            let ghost stated = items.deep_view();
            let ghost start = left;
            let ghost ran = proof::insert_run(self@, g, event as int, stated, proof::opt(left), self.elements@.len() - base);
            assert(stated.skip(0) =~= stated);
        }
        let mut left = left;
        let mut offset: usize = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                offset <= items@.len(),
                self.holds(graph.events@.len()),
                base <= self.elements@.len(),
                self.elements@.len() == old(self).elements@.len() + offset,
                left matches Some(l) ==> l < self.elements@.len(),
                offset == 0 ==> left == start,
                offset > 0 ==> (left matches Some(l) && l as int == self.elements@.len() - 1),
                proof::distinct_names(self@),
                self@.minted_below(event as int, self.elements@.len() - base),
                forall|i: int| 0 <= i < old(self).elements@.len() ==> {
                    &&& (#[trigger] self.elements@[i]).author == old(self).elements@[i].author
                    &&& self.elements@[i].reference == old(self).elements@[i].reference
                },
                forall|i: int| old(self).elements@.len() <= i < self.elements@.len()
                    ==> (#[trigger] self.elements@[i]).author == event,
                ran == proof::insert_run(self@, g, event as int, stated.skip(offset as int), proof::opt(left),
                    self.elements@.len() - base),
            decreases items@.len() - offset,
        ))]
        while offset < items.len() {
            let (parent, side) = self.anchor(left, graph, event);
            let minted = self.elements.len() - base;
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost rest = stated.skip(offset as int);
                assert(rest[0] == items@[offset as int]@);
                assert(rest.drop_first() =~= stated.skip(offset as int + 1));
                let ghost t = self@;
                let ghost place = (proof::opt(parent), side is Right);
                proof::lemma_attach_names(t, event as int, minted as int, items@[offset as int]@, place);
            }
            left = Some(self.attach(
                (named, minted),
                items[offset].copied(),
                event,
                (index, offset),
                parent,
                side,
            ));
            offset += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(stated.skip(offset as int) =~= Seq::<ItemS>::empty()); }
        left
    }

    /// Decision 0032's resolution, crossed.
    ///
    /// The resolution is the recorded truth of this file at this revision, so
    /// the walk takes it as stated rather than deriving anything: an item the
    /// resolution does not keep is dead here, exactly as a delete; the items
    /// it inserts are its own; and the items it keeps survive **under their
    /// own names**, which is what lets a concurrent branch's edits to those
    /// same items merge normally instead of colliding with copies.
    ///
    /// Proved to do exactly what the model's `replay_resolution` says,
    /// refusing exactly where it refuses.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).holds(graph.events@.len()),
            graph.holds(),
            event < graph.events@.len(),
            proof::distinct_names(old(self)@),
            old(self)@.minted_below(event as int, 0),
        ensures
            final(self).holds(graph.events@.len()),
            proof::distinct_names(final(self)@),
            final(self).elements@.len() >= old(self).elements@.len(),
            forall|i: int| 0 <= i < old(self).elements@.len() ==> {
                &&& (#[trigger] final(self).elements@[i]).author == old(self).elements@[i].author
                &&& final(self).elements@[i].reference == old(self).elements@[i].reference
            },
            forall|i: int| old(self).elements@.len() <= i < final(self).elements@.len()
                ==> (#[trigger] final(self).elements@[i]).author == event,
            ({
                let t = old(self)@;
                let replayed = proof::replay_resolution(
                    t,
                    graph@,
                    event as int,
                    t.visible(graph@, event as int),
                    document.pieces.deep_view(),
                );
                &&& (r is Ok <==> replayed is Some)
                &&& (r is Ok ==> final(self)@ == replayed->Some_0)
            }),
    ))]
    fn resolution(
        &mut self,
        graph: &Graph<'_>,
        event: usize,
        named: RevisionId,
        document: &ResolutionDocument,
    ) -> Result<(), MergeError> {
        let order = self.order();
        // The same view an operation document's positions are counted into:
        // what this author had before they started.
        let prepare = self.visible(&order, graph, event);
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost t = self@;
            let ghost g = graph@;
            let ghost view = proof::ints(prepare@);
            let ghost pieces = document.pieces.deep_view();
            proof::lemma_visible_ok(t, g, event as int);
            assert forall|q: int| 0 <= q < prepare@.len() implies #[trigger] prepare@[q] < self.elements@.len() by {
                assert(view[q] == prepare@[q] as int);
            }
            self.lemma_shaped();
            proof::lemma_visible_no_dup(t, g, event as int);
        }
        // Where each name the author could see stands in that view. Two
        // elements share a name only in the byte-identical case
        // `Element::reference` describes, where they belong to different
        // events; each `keep` takes the first position still standing under
        // its name, so the walk keeps as many elements as the resolution
        // assembles items.
        let slots = self.slots(&prepare, graph.events.len());
        let kept = self.pieces(graph, event, named, document, &prepare, &slots)?;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost pieced = self@; }
        // Everything the author could see and the resolution did not keep.
        // Recorded as a removal that quotes nothing, because a resolution
        // states what survives rather than what went.
        self.drop_unkept(event, &prepare, &kept);
        #[cfg(verus_keep_ghost)]
        proof! { self.lemma_names_alike(pieced); }
        Ok(())
    }

    /// A resolution's pieces in order: what each keeps, and what each inserts
    /// after it. Returns which positions of the view were kept.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).holds(graph.events@.len()),
            graph.holds(),
            event < graph.events@.len(),
            forall|q: int| 0 <= q < prepare@.len() ==> #[trigger] prepare@[q] < old(self).elements@.len(),
            slots_hold(old(self).elements@, prepare@, slots@, graph.events@.len()),
            proof::distinct_names(old(self)@),
            old(self)@.minted_below(event as int, 0),
        ensures
            final(self).holds(graph.events@.len()),
            proof::distinct_names(final(self)@),
            final(self).elements@.len() >= old(self).elements@.len(),
            forall|i: int| 0 <= i < old(self).elements@.len() ==> {
                &&& (#[trigger] final(self).elements@[i]).author == old(self).elements@[i].author
                &&& final(self).elements@[i].reference == old(self).elements@[i].reference
            },
            forall|i: int| old(self).elements@.len() <= i < final(self).elements@.len()
                ==> (#[trigger] final(self).elements@[i]).author == event,
            r matches Ok(kept) ==> kept@.len() == prepare@.len(),
            match proof::replay_pieces(
                old(self)@,
                graph@,
                event as int,
                proof::ints(prepare@),
                document.pieces.deep_view(),
                0,
                ISet::empty(),
                None,
                0,
            ) {
                None => r is Err,
                Some((next, now)) => r matches Ok(kept) && final(self)@ == next && kept_set(kept@) == now,
            },
    ))]
    fn pieces(
        &mut self,
        graph: &Graph<'_>,
        event: usize,
        named: RevisionId,
        document: &ResolutionDocument,
        prepare: &[usize],
        slots: &[Vec<Option<usize>>],
    ) -> Result<Vec<bool>, MergeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost g = graph@;
            let ghost view = proof::ints(prepare@);
            let ghost pieces = document.pieces.deep_view();
            let ghost ran = proof::replay_pieces(self@, g, event as int, view, pieces, 0, ISet::empty(), None, 0);
        }
        let base = self.elements.len();
        let mut kept = vec![false; prepare.len()];
        #[cfg(verus_keep_ghost)]
        proof! { assert(kept_set(kept@) =~= ISet::<int>::empty()); }
        // The element the next piece follows, which is what anchors an insert.
        let mut left: Option<usize> = None;
        let mut index: usize = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                index <= document.pieces@.len(),
                graph.holds(),
                event < graph.events@.len(),
                g == graph@,
                view == proof::ints(prepare@),
                pieces == document.pieces.deep_view(),
                ran == proof::replay_pieces(old(self)@, graph@, event as int, proof::ints(prepare@),
                    document.pieces.deep_view(), 0, ISet::empty(), None, 0),
                self.holds(graph.events@.len()),
                base == old(self).elements@.len(),
                base <= self.elements@.len(),
                kept@.len() == prepare@.len(),
                left matches Some(l) ==> l < self.elements@.len(),
                forall|q: int| 0 <= q < prepare@.len() ==> #[trigger] prepare@[q] < self.elements@.len(),
                proof::distinct_names(self@),
                self@.minted_below(event as int, self.elements@.len() - base),
                forall|i: int| 0 <= i < old(self).elements@.len() ==> {
                    &&& (#[trigger] self.elements@[i]).author == old(self).elements@[i].author
                    &&& self.elements@[i].reference == old(self).elements@[i].reference
                },
                forall|i: int| old(self).elements@.len() <= i < self.elements@.len()
                    ==> (#[trigger] self.elements@[i]).author == event,
                slots_hold(self.elements@, prepare@, slots@, graph.events@.len()),
                ran == proof::replay_pieces(self@, g, event as int, view, pieces, index as int,
                    kept_set(kept@), proof::opt(left), self.elements@.len() - base),
            decreases document.pieces@.len() - index,
        ))]
        while index < document.pieces.len() {
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                assert(pieces[index as int] == document.pieces@[index as int].deep_view());
                let ghost before = self.elements@;
            }
            match &document.pieces[index] {
                Piece::Keep {
                    document: from,
                    first,
                    count,
                } => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        assert(pieces[index as int] == PieceS::Keep { document: *from, first: *first as int, count: *count as int });
                    }
                    left = self.keep_run(
                        graph, event, prepare, slots, &mut kept, left, *from, *first, *count,
                    )?;
                }
                Piece::Insert { items } => {
                    #[cfg(verus_keep_ghost)]
                    proof_decl! {
                        assert(pieces[index as int] == PieceS::Insert { items: items.deep_view() });
                        let ghost t = self@;
                        let ghost was = left;
                        let ghost minted = self.elements@.len() - base;
                    }
                    left = self.insert_run(graph, event, named, base, left, index, items);
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        lemma_slots_kept(before, self.elements@, prepare@, slots@, graph.events@.len());
                        let (next, m) = proof::insert_run(t, g, event as int, items.deep_view(), proof::opt(was), minted);
                        assert(self@ == next);
                        assert(items.deep_view().len() == items@.len());
                        assert(proof::opt(left) == if items.deep_view().len() == 0 { proof::opt(was) } else { Some(next.len() - 1) });
                    }
                }
            }
            index += 1;
        }
        Ok(kept)
    }

    /// Each `keep`'s items in turn: the next element still standing under
    /// each name, in the author's view.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            event < graph.events@.len(),
            left matches Some(l) ==> l < self.elements@.len(),
            old(kept)@.len() == prepare@.len(),
            forall|q: int| 0 <= q < prepare@.len() ==> #[trigger] prepare@[q] < self.elements@.len(),
            slots_hold(self.elements@, prepare@, slots@, graph.events@.len()),
        ensures
            final(kept)@.len() == prepare@.len(),
            r matches Ok(Some(l)) ==> l < self.elements@.len(),
            match proof::keep_run(
                self@,
                graph@,
                proof::ints(prepare@),
                kept_set(old(kept)@),
                proof::opt(left),
                from,
                first as int,
                count as int,
                0,
            ) {
                None => r is Err,
                Some((now, last)) => r is Ok && kept_set(final(kept)@) == now && proof::opt(r->Ok_0) == last,
            },
    ))]
    #[allow(clippy::too_many_arguments)]
    fn keep_run(
        &self,
        graph: &Graph<'_>,
        event: usize,
        prepare: &[usize],
        slots: &[Vec<Option<usize>>],
        kept: &mut [bool],
        left: Option<usize>,
        from: RevisionId,
        first: usize,
        count: usize,
    ) -> Result<Option<usize>, MergeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost view = proof::ints(prepare@);
            let ghost ran = proof::keep_run(self@, graph@, view, kept_set(kept@), proof::opt(left), from,
                first as int, count as int, 0);
        }
        // The events that stated the document this `keep` names: one,
        // except where concurrent revisions named one byte-identical
        // document.
        let stating = graph.stating(from);
        let mut left = left;
        let mut offset: usize = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                offset <= count,
                kept@.len() == prepare@.len(),
                left matches Some(l) ==> l < self.elements@.len(),
                ran == proof::keep_run(self@, graph@, view, kept_set(kept@), proof::opt(left), from,
                    first as int, count as int, offset as int),
            decreases count - offset,
        ))]
        while offset < count {
            let found = match first.checked_add(offset) {
                Some(item) => {
                    #[cfg(verus_keep_ghost)]
                    proof_with!(Ghost(graph@), Ghost(prepare@), Ghost(from));
                    self.pick(slots, kept, &stating, item)
                }
                // No element has an ordinal past the last `usize`, and a
                // run reaching one has already met an ordinal nothing holds,
                // so this is never where a refusal comes from.
                None => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        assert forall|q: int| 0 <= q < view.len() implies
                            !(!kept_set(kept@).contains(q) && #[trigger] proof::refers(self@, graph@, view[q], from, first + offset)) by {
                            assert(self@.nodes[view[q]] == self.elements@[prepare@[q] as int]@);
                        }
                        proof::lemma_pick_none(self@, graph@, view, kept_set(kept@), from, first + offset, 0);
                    }
                    None
                }
            };
            match found {
                None => {
                    return Err(MergeError::UnknownReference {
                        revision: graph.events[event].revision,
                        document: from,
                        item: first.saturating_add(offset),
                    });
                }
                Some(position) => {
                    #[cfg(verus_keep_ghost)]
                    proof_decl! { let ghost was = kept@; }
                    kept[position] = true;
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        assert(kept_set(kept@) =~= kept_set(was).insert(position as int));
                        assert(view[position as int] == prepare@[position as int] as int);
                    }
                    left = Some(prepare[position]);
                }
            }
            offset += 1;
        }
        Ok(left)
    }

    /// The first position of the view not yet kept that holds item `item` of
    /// `from`, given the events that stated `from`.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        with
            Ghost(g): Ghost<proof::GraphS>,
            Ghost(prepare): Ghost<Seq<usize>>,
            Ghost(from): Ghost<RevisionId>,
        requires
            kept@.len() == prepare.len(),
            forall|q: int| 0 <= q < prepare.len() ==> #[trigger] prepare[q] < self.elements@.len(),
            slots_hold(self.elements@, prepare, slots@, g.events.len()),
            forall|k: int| 0 <= k < stating@.len() ==> #[trigger] stating@[k] < g.events.len(),
            forall|a: int| 0 <= a < g.events.len() ==>
                (proof::states(g.events[a], from) <==> stating@.contains(a as usize)),
        ensures
            proof::opt(r) == proof::pick(self@, g, proof::ints(prepare), kept_set(kept@), from, item as int, 0),
            r matches Some(q) ==> q < prepare.len(),
    ))]
    fn pick(
        &self,
        slots: &[Vec<Option<usize>>],
        kept: &[bool],
        stating: &[usize],
        item: usize,
    ) -> Option<usize> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost t = self@;
            let ghost view = proof::ints(prepare);
            let ghost unkept = kept_set(kept@);
            // A position qualifies where it is not kept and its element is
            // `item` of `from`: exactly where some stating event's slot for
            // `item` holds it.
            let ghost qualifies = |q: int| 0 <= q < view.len() && !unkept.contains(q)
                && proof::refers(t, g, view[q], from, item as int);
        }
        let mut best: Option<usize> = None;
        let mut c: usize = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                c <= stating@.len(),
                best matches Some(b) ==> qualifies(b as int),
                forall|k: int| 0 <= k < c ==> {
                    let a = #[trigger] stating@[k] as int;
                    (slots@[a]@.len() > item && slots@[a]@[item as int] is Some
                        && !kept@[slots@[a]@[item as int]->Some_0 as int])
                        ==> (best matches Some(b) && b <= slots@[a]@[item as int]->Some_0)
                },
            decreases stating@.len() - c,
        ))]
        while c < stating.len() {
            let author = stating[c];
            let slot = if item < slots[author].len() {
                slots[author][item]
            } else {
                None
            };
            if let Some(q) = slot {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(q < prepare.len() && self.elements@[prepare[q as int] as int].author == author
                        && self.elements@[prepare[q as int] as int].reference.1 == item);
                    assert(t.nodes[view[q as int]] == self.elements@[prepare[q as int] as int]@);
                    assert(stating@.contains(author));
                }
                let better = match best {
                    None => true,
                    Some(b) => q < b,
                };
                if !kept[q] && better {
                    best = Some(q);
                }
            }
            c += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            // Every qualifying position is in some stating event's slot.
            assert forall|q: int| #[trigger] qualifies(q) implies best matches Some(b) && b <= q by {
                assert(view[q] == prepare[q] as int);
                let element = self.elements@[prepare[q] as int];
                assert(t.nodes[view[q]] == element@);
                let author = element.author;
                assert(element.reference.1 == item);
                assert(proof::states(g.events[author as int], from));
                assert(stating@.contains(author));
                let k = choose|k: int| 0 <= k < stating@.len() && stating@[k] == author;
                assert(stating@[k] == author);
                let slot = slots@[stating@[k] as int]@;
                assert(slot.len() > item);
                assert(slot[item as int] == Some(q as usize));
                assert(slot[item as int]->Some_0 == q as usize);
                assert(!kept@[q]);
                assert(best matches Some(b) && b <= q as usize);
            }
            match best {
                Some(b) => {
                    assert forall|r: int| 0 <= r < b implies !(!unkept.contains(r) && #[trigger] proof::refers(t, g, view[r], from, item as int)) by {
                        if 0 <= r < b && !unkept.contains(r) && proof::refers(t, g, view[r], from, item as int) {
                            assert(qualifies(r));
                        }
                    }
                    proof::lemma_pick_first(t, g, view, unkept, from, item as int, 0, b as int);
                }
                None => {
                    assert forall|r: int| 0 <= r < view.len() implies !(!unkept.contains(r) && #[trigger] proof::refers(t, g, view[r], from, item as int)) by {
                        if !unkept.contains(r) && proof::refers(t, g, view[r], from, item as int) {
                            assert(qualifies(r));
                        }
                    }
                    proof::lemma_pick_none(t, g, view, unkept, from, item as int, 0);
                }
            }
        }
        best
    }

    /// Where each element of the view stands in it, by author and ordinal.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            forall|q: int| 0 <= q < prepare@.len() ==> {
                &&& #[trigger] prepare@[q] < self.elements@.len()
                &&& self.elements@[prepare@[q] as int].author < events
            },
            proof::distinct_names(self@),
            proof::ints(prepare@).no_duplicates(),
        ensures
            slots_hold(self.elements@, prepare@, r@, events as nat),
    ))]
    fn slots(&self, prepare: &[usize], events: usize) -> Vec<Vec<Option<usize>>> {
        let mut slots: Vec<Vec<Option<usize>>> = Vec::with_capacity(events);
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                slots@.len() <= events,
                forall|a: int| 0 <= a < slots@.len() ==> #[trigger] slots@[a]@.len() == 0,
            decreases events - slots@.len(),
        ))]
        while slots.len() < events {
            slots.push(Vec::new());
        }
        let mut q: usize = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                q <= prepare@.len(),
                slots@.len() == events,
                forall|a: int, m: int| 0 <= a < events && 0 <= m < slots@[a]@.len()
                    && (#[trigger] slots@[a]@[m]) is Some ==> {
                        let p = slots@[a]@[m]->Some_0 as int;
                        &&& p < q
                        &&& self.elements@[prepare@[p] as int].author == a
                        &&& self.elements@[prepare@[p] as int].reference.1 == m
                    },
                forall|p: int| 0 <= p < q ==> {
                    let element = #[trigger] self.elements@[prepare@[p] as int];
                    &&& element.reference.1 < slots@[element.author as int]@.len()
                    &&& slots@[element.author as int]@[element.reference.1 as int] == Some(p as usize)
                },
            decreases prepare@.len() - q,
        ))]
        while q < prepare.len() {
            let element = &self.elements[prepare[q]];
            let (author, minted) = (element.author, element.reference.1);
            pad(&mut slots[author], minted);
            #[cfg(verus_keep_ghost)]
            proof! {
                // Nothing already recorded is at this name: the view lists
                // each element once, and no two elements share a name.
                if slots@[author as int]@[minted as int] is Some {
                    let p = slots@[author as int]@[minted as int]->Some_0 as int;
                    assert(proof::ints(prepare@)[p] != proof::ints(prepare@)[q as int]);
                    let (i, j) = (prepare@[p] as int, prepare@[q as int] as int);
                    assert(self@.nodes[i] == self.elements@[i]@);
                    assert(self@.nodes[j] == self.elements@[j]@);
                    assert(self@.id(i) == self@.id(j));
                }
            }
            slots[author][minted] = Some(q);
            q += 1;
        }
        slots
    }

    /// Everything the view held and `kept` does not, removed by `event`.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            old(self).holds_shape(),
            kept@.len() == prepare@.len(),
            forall|q: int| 0 <= q < prepare@.len() ==> #[trigger] prepare@[q] < old(self).elements@.len(),
        ensures
            final(self).holds_shape(),
            final(self)@ == proof::drop_unkept(old(self)@, event as int, proof::ints(prepare@), kept_set(kept@), 0),
            final(self).elements@.len() == old(self).elements@.len(),
            forall|i: int| 0 <= i < old(self).elements@.len() ==> {
                &&& (#[trigger] final(self).elements@[i]).author == old(self).elements@[i].author
                &&& final(self).elements@[i].reference == old(self).elements@[i].reference
            },
            forall|events: nat| old(self).holds(events) && event < events ==> #[trigger] final(self).holds(events),
    ))]
    fn drop_unkept(&mut self, event: usize, prepare: &[usize], kept: &[bool]) {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost view = proof::ints(prepare@);
            let ghost ran = proof::drop_unkept(self@, event as int, view, kept_set(kept@), 0);
        }
        let mut q: usize = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                q <= prepare@.len(),
                self.holds_shape(),
                self.elements@.len() == old(self).elements@.len(),
                forall|i: int| 0 <= i < old(self).elements@.len() ==> {
                    &&& (#[trigger] self.elements@[i]).author == old(self).elements@[i].author
                    &&& self.elements@[i].reference == old(self).elements@[i].reference
                },
                forall|events: nat| old(self).holds(events) && event < events ==> #[trigger] self.holds(events),
                ran == proof::drop_unkept(self@, event as int, view, kept_set(kept@), q as int),
            decreases prepare@.len() - q,
        ))]
        while q < prepare.len() {
            #[cfg(verus_keep_ghost)]
            proof! { assert(view[q as int] == prepare@[q as int] as int); }
            if !kept[q] {
                self.mark(prepare[q], event, None);
            }
            q += 1;
        }
    }

    /// The elements one event's author could see, in order.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.holds(graph.events@.len()),
            graph.holds(),
            event < graph.events@.len(),
            proof::ints(order@) == self@.order(),
        ensures
            proof::ints(r@) == self@.visible(graph@, event as int),
    ))]
    fn visible(&self, order: &[usize], graph: &Graph<'_>, event: usize) -> Vec<usize> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost t = self@;
            let ghost seen = |i: int| t.seen(graph@, event as int, i);
            reveal(proof::TreeS::visible);
            reveal(proof::TreeS::order);
            proof::lemma_read_all_nodes(t, t.children(None, true), -1);
            assert(proof::ints(order@).take(0) =~= Seq::<int>::empty());
        }
        let mut visible: Vec<usize> = Vec::new();
        let mut k: usize = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                k <= order@.len(),
                proof::ints(visible@) == proof::sel(proof::ints(order@).take(k as int), seen),
            decreases order@.len() - k,
        ))]
        while k < order.len() {
            let at = order[k];
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                assert(proof::ints(order@)[k as int] == at as int);
                assert(t.node(at as int));
                let ghost upto = proof::ints(order@).take(k as int + 1);
                assert(upto.drop_last() =~= proof::ints(order@).take(k as int));
                assert(upto.last() == at as int);
                let ghost before = visible@;
            }
            if self.seen(at, graph, event) {
                visible.push(at);
                #[cfg(verus_keep_ghost)]
                proof! { assert(proof::ints(visible@) =~= proof::ints(before).push(at as int)); }
            }
            k += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(proof::ints(order@).take(order@.len() as int) =~= proof::ints(order@)); }
        visible
    }

    /// Whether `event`'s author saw the element at `at`: written in their
    /// past, and removed by nothing in it.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.holds(graph.events@.len()),
            graph.holds(),
            event < graph.events@.len(),
            at < self.elements@.len(),
        ensures
            r == self@.seen(graph@, event as int, at as int),
    ))]
    fn seen(&self, at: usize, graph: &Graph<'_>, event: usize) -> bool {
        let element = &self.elements[at];
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost node = self@.nodes[at as int];
            assert(node == element@);
            let ghost removers = element.deleted_by@.map_values(|by: (usize, Option<(usize, usize)>)| by.0 as int);
        }
        if !graph.saw(event, element.author) {
            return false;
        }
        let mut k: usize = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                k <= element.deleted_by@.len(),
                forall|q: int| 0 <= q < k ==> !graph@.saw(event as int, #[trigger] removers[q]),
            decreases element.deleted_by@.len() - k,
        ))]
        while k < element.deleted_by.len() {
            if graph.saw(event, element.deleted_by[k].0) {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(removers[k as int] == element.deleted_by@[k as int].0 as int);
                    assert(removers.to_set().contains(removers[k as int]));
                }
                return false;
            }
            #[cfg(verus_keep_ghost)]
            proof! { assert(removers[k as int] == element.deleted_by@[k as int].0 as int); }
            k += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|d: int| node.deleted.contains(d) implies !graph@.saw(event as int, d) by {
                assert(removers.contains(d));
                let q = choose|q: int| 0 <= q < removers.len() && removers[q] == d;
            }
        }
        true
    }

    /// The first of `children` whose author `event` knows.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.holds(graph.events@.len()),
            graph.holds(),
            event < graph.events@.len(),
            forall|k: int| 0 <= k < children@.len() ==> #[trigger] children@[k] < self.elements@.len(),
        ensures
            proof::opt(r) == self@.first_known(graph@, event as int, proof::ints(children@)),
    ))]
    fn first_known(&self, children: &[usize], graph: &Graph<'_>, event: usize) -> Option<usize> {
        let mut k: usize = 0;
        #[cfg(verus_keep_ghost)]
        proof! { assert(proof::ints(children@).skip(0) =~= proof::ints(children@)); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                k <= children.len(),
                self@.first_known(graph@, event as int, proof::ints(children@))
                    == self@.first_known(graph@, event as int, proof::ints(children@).skip(k as int)),
            decreases children.len() - k,
        ))]
        while k < children.len() {
            let child = children[k];
            #[cfg(verus_keep_ghost)]
            proof! {
                let rest = proof::ints(children@).skip(k as int);
                assert(rest[0] == child as int);
                assert(rest.drop_first() =~= proof::ints(children@).skip(k as int + 1));
                assert(self@.nodes[child as int] == self.elements@[child as int]@);
            }
            if graph.knows(event, self.elements[child].author) {
                return Some(child);
            }
            k += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(proof::ints(children@).skip(k as int) =~= Seq::<int>::empty()); }
        None
    }

    /// Where an element written after `left` belongs in the tree.
    ///
    /// Fugue's rule, in its tree formulation: an element attaches to its left
    /// neighbour when that neighbour has nothing to its right yet, and
    /// otherwise as a left child of the element that follows the left
    /// neighbour in its author's view of the tree — *tombstones included*,
    /// which is why the author's next visible element cannot say where. That
    /// next element is the leftmost known node under the left neighbour's
    /// first known right child, so a run written by one author becomes one
    /// subtree, read out contiguously — the guarantee against interleaving
    /// that decision 0007 chose Fugue for — and two elements only ever become
    /// same-side siblings when their authors had not seen each other, which
    /// is what entitles [`Tree::attach`] to break sibling ties by name.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.holds(graph.events@.len()),
            graph.holds(),
            event < graph.events@.len(),
            left matches Some(at) ==> at < self.elements@.len(),
        ensures
            proof::opt(r.0) == self@.anchor(graph@, event as int, proof::opt(left)).0,
            (r.1 is Right) == self@.anchor(graph@, event as int, proof::opt(left)).1,
            r.0 matches Some(p) ==> p < self.elements@.len(),
            r.0 is None ==> r.1 is Right,
    ))]
    fn anchor(
        &self,
        left: Option<usize>,
        graph: &Graph<'_>,
        event: usize,
    ) -> (Option<usize>, Side) {
        #[cfg(verus_keep_ghost)]
        proof! {
            match left {
                Some(at) => self.lemma_listed(self.elements@[at as int].right@, Some(at as int), true),
                None => self.lemma_listed(self.root@, None, true),
            }
        }
        let found = match left {
            Some(at) => self.first_known(&self.elements[at].right, graph, event),
            None => self.first_known(&self.root, graph, event),
        };
        let first = match found {
            Some(first) => first,
            None => return (left, Side::Right),
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            let above = self@.children(proof::opt(left), true);
            proof::lemma_first_known_known(self@, graph@, event as int, above);
            proof::lemma_children_nodes(self@, proof::opt(left), true);
            assert(self@.hangs(first as int, proof::opt(left), true));
        }
        // Down the known left children, as far as they go.
        let mut at = first;
        let mut descending = true;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                at < self.elements@.len(),
                self@.leftmost_known(graph@, event as int, first as int)
                    == self@.leftmost_known(graph@, event as int, at as int),
                !descending ==> self@.first_known(graph@, event as int, self@.children(Some(at as int), false)) is None,
            decreases self.elements@.len() - at + if descending { 1int } else { 0int },
        ))]
        while descending {
            #[cfg(verus_keep_ghost)]
            proof! { self.lemma_listed(self.elements@[at as int].left@, Some(at as int), false); }
            match self.first_known(&self.elements[at].left, graph, event) {
                Some(next) => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        let below = self@.children(Some(at as int), false);
                        proof::lemma_first_known_known(self@, graph@, event as int, below);
                        let k = choose|k: int| 0 <= k < below.len() && below[k] == next as int;
                        assert(self.elements@[at as int].left@[k] == next);
                        proof::lemma_children_nodes(self@, Some(at as int), false);
                        assert(self@.hangs(next as int, Some(at as int), false));
                        assert(self@.nodes[next as int] == self.elements@[next as int]@);
                    }
                    at = next;
                }
                None => descending = false,
            }
        }
        (Some(at), Side::Left)
    }

    /// Put an element into the tree, among its siblings in name order.
    ///
    /// The place among the siblings is found before the element is added, so
    /// that the list is read and then written rather than taken out and put
    /// back, which is the one shape of this the prover follows.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).holds_shape(),
            parent matches Some(p) ==> p < old(self).elements@.len(),
            parent is None ==> side is Right,
        ensures
            r == old(self).elements@.len(),
            final(self).holds_shape(),
            final(self)@ == old(self)@.attach(
                author as int,
                reference.1 as int,
                item@,
                (proof::opt(parent), side is Right),
            ),
            final(self).elements@.len() == old(self).elements@.len() + 1,
            final(self).elements@[r as int].reference == reference,
            final(self).elements@[r as int].author == author,
            final(self).elements@[r as int].deleted_by@.len() == 0,
            forall|i: int| 0 <= i < old(self).elements@.len() ==> {
                &&& (#[trigger] final(self).elements@[i]).reference == old(self).elements@[i].reference
                &&& final(self).elements@[i].author == old(self).elements@[i].author
                &&& final(self).elements@[i].deleted_by == old(self).elements@[i].deleted_by
            },
            forall|events: nat| old(self).holds(events) && author < events ==> #[trigger] final(self).holds(events),
    ))]
    fn attach(
        &mut self,
        reference: (RevisionId, usize),
        item: Item,
        author: usize,
        wrote: (usize, usize),
        parent: Option<usize>,
        side: Side,
    ) -> usize {
        let at = self.elements.len();
        let minted = reference.1;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost t = self@;
            let ghost before = self.elements@;
            let ghost root = self.root@;
            let ghost place = (proof::opt(parent), side is Right);
            let ghost u = t.attach(author as int, minted as int, item@, place);
        }
        let siblings = match parent {
            None => &self.root,
            Some(p) => match side {
                Side::Left => &self.elements[p].left,
                Side::Right => &self.elements[p].right,
            },
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            self.lemma_listed(siblings@, place.0, place.1);
            assert(proof::ints(siblings@).skip(0) =~= proof::ints(siblings@));
        }
        // Ties between concurrent elements are broken by name: by digest,
        // which is event order, then by how many the event had minted.
        let mut position: usize = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                position <= siblings.len(),
                u.first_greater(proof::ints(siblings@), t.len(), 0)
                    == u.first_greater(proof::ints(siblings@), t.len(), position as int),
            decreases siblings.len() - position,
        ))]
        while position < siblings.len() && {
            let other = &self.elements[siblings[position]];
            !(other.author > author || (other.author == author && other.reference.1 > minted))
        } {
            #[cfg(verus_keep_ghost)]
            proof! {
                let other = siblings@[position as int] as int;
                assert(u.nodes[other] == t.nodes[other]);
                assert(t.nodes[other] == self.elements@[other]@);
            }
            position += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            if position < siblings.len() {
                let other = siblings@[position as int] as int;
                assert(u.nodes[other] == t.nodes[other]);
                assert(t.nodes[other] == self.elements@[other]@);
            }
        }
        self.elements.push(Element {
            reference,
            item,
            author,
            wrote,
            deleted_by: Vec::new(),
            parent,
            side,
            left: Vec::new(),
            right: Vec::new(),
        });
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost pushed = self.elements@;
            assert(pushed[at as int]@.deleted =~= Set::<int>::empty());
            assert(self@.nodes =~= u.nodes);
        }
        match parent {
            None => self.root.insert(position, at),
            Some(p) => match side {
                Side::Left => self.elements[p].left.insert(position, at),
                Side::Right => self.elements[p].right.insert(position, at),
            },
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(self.elements@.len() == pushed.len());
            assert forall|i: int| 0 <= i < pushed.len() implies #[trigger] self.elements@[i]@ == pushed[i]@ by {}
            assert(self@.nodes =~= u.nodes);
            let inserted = proof::ints(siblings@).insert(position as int, at as int);
            proof::lemma_children_attach(t, author as int, minted as int, item@, place, place.0, place.1);
            assert(u.insert_sorted(t.children(place.0, place.1), t.len()) =~= inserted);
            assert(u.children(place.0, place.1) == inserted);

            // The new element has nothing under it yet.
            assert forall|j: int, r: bool| 0 <= j < u.len() implies !u.hangs(j, Some(at as int), r) by {
                if j < at {
                    assert(u.nodes[j] == before[j]@);
                }
            }
            proof::lemma_children_none(u, Some(at as int), false, u.len());
            proof::lemma_children_none(u, Some(at as int), true, u.len());

            // Every other list is the one it was, and so is the model's.
            proof::lemma_children_attach(t, author as int, minted as int, item@, place, None, true);
            if place.0 is None {
                assert(proof::ints(self.root@) =~= inserted);
            } else {
                assert(self.root@ == root);
            }
            assert forall|i: int| 0 <= i < self.elements@.len() implies {
                &&& proof::ints((#[trigger] self.elements@[i]).left@) == u.children(Some(i), false)
                &&& proof::ints(self.elements@[i].right@) == u.children(Some(i), true)
                &&& match self.elements@[i].parent {
                    Some(p) => p < i,
                    None => self.elements@[i].side is Right,
                }
            } by {
                if i < at {
                    proof::lemma_children_attach(t, author as int, minted as int, item@, place, Some(i), false);
                    proof::lemma_children_attach(t, author as int, minted as int, item@, place, Some(i), true);
                    if place == (Some(i), false) {
                        assert(proof::ints(self.elements@[i].left@) =~= inserted);
                    }
                    if place == (Some(i), true) {
                        assert(proof::ints(self.elements@[i].right@) =~= inserted);
                    }
                } else {
                    assert(proof::ints(self.elements@[i].left@) =~= Seq::<int>::empty());
                    assert(proof::ints(self.elements@[i].right@) =~= Seq::<int>::empty());
                }
            }
            assert forall|events: nat| old(self).holds(events) && author < events implies #[trigger] self.holds(events) by {
                assert forall|i: int| 0 <= i < self.elements@.len() implies {
                    &&& (#[trigger] self.elements@[i]).author < events
                    &&& forall|k: int| 0 <= k < self.elements@[i].deleted_by@.len()
                        ==> #[trigger] self.elements@[i].deleted_by@[k].0 < events
                } by {
                    if i < at {
                        assert(self.elements@[i].author == before[i].author);
                        assert(self.elements@[i].deleted_by == before[i].deleted_by);
                    }
                }
            }
        }
        at
    }
}

impl Tree {
    /// Where two revisions that had not seen each other met.
    ///
    /// Computed from the finished structure rather than noticed on the way
    /// past, because what a walk has seen so far depends on the order it walks
    /// in, and a report that changed with the order would be worth nothing.
    fn contests(&self, graph: &Graph<'_>) -> Vec<Option<(Contest, BTreeSet<RevisionId>)>> {
        let mut found: Vec<Option<(Contest, BTreeSet<RevisionId>)>> =
            vec![None; self.elements.len()];
        let mark = |found: &mut Vec<Option<(Contest, BTreeSet<RevisionId>)>>,
                    at: usize,
                    kind: Contest,
                    against: RevisionId| {
            let entry = found[at].get_or_insert((kind, BTreeSet::new()));
            entry.0 = kind;
            entry.1.insert(against);
        };

        // A tie broken between elements written at one place by authors who
        // had not seen each other.
        let mut sibling_lists: Vec<&Vec<usize>> = vec![&self.root];
        for element in &self.elements {
            sibling_lists.push(&element.left);
            sibling_lists.push(&element.right);
        }
        for siblings in sibling_lists {
            for (position, at) in siblings.iter().enumerate() {
                for other in &siblings[position + 1..] {
                    let (mine, theirs) = (self.elements[*at].author, self.elements[*other].author);
                    if !graph.concurrent(mine, theirs) {
                        continue;
                    }
                    mark(
                        &mut found,
                        *at,
                        Contest::Insertion,
                        graph.events[theirs].revision,
                    );
                    mark(
                        &mut found,
                        *other,
                        Contest::Insertion,
                        graph.events[mine].revision,
                    );
                }
            }
        }

        // An element removed by one revision, with something a concurrent
        // revision wrote still standing next to the gap. Adjacency is read off
        // the finished file rather than off the tree: an element attaches
        // wherever the anchoring rule puts it, which is not always beside the
        // thing it was written beside.
        let mut before: Option<usize> = None;
        let mut pending: BTreeSet<usize> = BTreeSet::new();
        for at in self.order() {
            let element = &self.elements[at];
            if element.deleted_by.is_empty() {
                for by in &pending {
                    if graph.concurrent(element.author, *by) {
                        mark(
                            &mut found,
                            at,
                            Contest::Deletion,
                            graph.events[*by].revision,
                        );
                    }
                }
                pending.clear();
                before = Some(at);
                continue;
            }
            if let Some(previous) = before {
                for (by, _) in &element.deleted_by {
                    if graph.concurrent(self.elements[previous].author, *by) {
                        mark(
                            &mut found,
                            previous,
                            Contest::Deletion,
                            graph.events[*by].revision,
                        );
                    }
                }
            }
            pending.extend(element.deleted_by.iter().map(|(by, _)| *by));
        }
        found
    }

    /// The merged file, and the regions where concurrent work met in it.
    fn read(&self, graph: &Graph<'_>) -> Merged {
        let contests = self.contests(graph);
        let mut items: Vec<Item> = Vec::new();
        let mut authors: Vec<usize> = Vec::new();
        let mut references: Vec<(RevisionId, usize)> = Vec::new();
        let mut marked: Vec<Option<(Contest, BTreeSet<RevisionId>)>> = Vec::new();
        for at in self.standing() {
            let element = &self.elements[at];
            items.push(element.item.clone());
            authors.push(element.author);
            references.push(element.reference);
            marked.push(contests[at].clone());
        }

        // A contest is reported over the whole run its author wrote, because
        // half a paragraph is not what a person needs to look at.
        let mut contested: Vec<Contested> = Vec::new();
        let mut position = 0;
        while position < items.len() {
            let author = authors[position];
            let mut end = position;
            while end + 1 < items.len() && authors[end + 1] == author {
                end += 1;
            }
            let mut kind = None;
            let mut revisions: BTreeSet<RevisionId> = BTreeSet::new();
            for found in marked.iter().take(end + 1).skip(position).flatten() {
                kind = Some(found.0);
                revisions.extend(found.1.iter().copied());
            }
            if let Some(kind) = kind {
                contested.push(Contested {
                    at: position,
                    len: end + 1 - position,
                    revisions: revisions.into_iter().collect(),
                    kind,
                });
            }
            position = end + 1;
        }

        contested.extend(terminators(&items));
        contested.sort_by_key(|contest| (contest.at, contest.len));

        Merged {
            origins: authors
                .iter()
                .map(|author| graph.events[*author].revision)
                .collect(),
            references,
            state: State::from_items(items),
            contested,
        }
    }
}

/// Why a set of events could not be merged.
///
/// As everywhere else, none of these mean the algorithm failed. The algorithm
/// never fails; these mean the events handed to it do not describe one history.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum MergeError {
    /// An event names a parent that was not among the events.
    MissingParent {
        /// The parent nothing here holds.
        parent: RevisionId,
        /// The event that names it.
        named_by: RevisionId,
    },
    /// The events name each other in a circle, which a Merkle DAG cannot do.
    Cycle,
    /// An operation names a position the state at its parents does not have.
    OutOfRange {
        /// The revision whose operation it was.
        revision: RevisionId,
        /// The position named.
        position: usize,
        /// How many items its author could see.
        length: usize,
    },
    /// A resolution keeps an item its author could not see.
    ///
    /// Decision 0032: a `keep` names a document and a run of its items, and
    /// this is the run naming something no document in the causal past minted
    /// — or minted and something already removed, or kept more often than the
    /// author's view held elements under the name.
    UnknownReference {
        /// The revision whose resolution it was.
        revision: RevisionId,
        /// The document the `keep` names.
        document: RevisionId,
        /// Which of its items.
        item: usize,
    },
    /// A recorded item is not the item its author was editing.
    ItemDisagrees {
        /// The revision whose operation it was.
        revision: RevisionId,
        /// Where the two disagree, in that author's view.
        position: usize,
        /// What the document recorded.
        recorded: String,
        /// What the author's view actually held.
        found: String,
    },
}

impl fmt::Display for MergeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MergeError::MissingParent { parent, named_by } => write!(
                f,
                "{named_by} names the parent {parent}, which is not among the events to merge; \
                 a merge needs the whole causal past of every head"
            ),
            MergeError::Cycle => write!(
                f,
                "these events name each other in a circle, which a graph of digests cannot do; \
                 one of them has been edited after the fact"
            ),
            MergeError::OutOfRange {
                revision,
                position,
                length,
            } => write!(
                f,
                "{revision} names position {position} of a file its author saw {length} items of; \
                 the document was recorded against a different history"
            ),
            MergeError::UnknownReference {
                revision,
                document,
                item,
            } => write!(
                f,
                "{revision} keeps item {item} of {document}, which its author's view of the \
                 file does not hold; the resolution names a document outside this merge's \
                 past, or a run longer than that document has items"
            ),
            MergeError::ItemDisagrees {
                revision,
                position,
                recorded,
                found,
            } => write!(
                f,
                "{revision} deletes `{recorded}` at position {position}, \
                 where its author's view held `{found}`; \
                 one of the two is corrupt, and the digests say which"
            ),
        }
    }
}

impl std::error::Error for MergeError {}

#[cfg(verus_keep_ghost)]
verus! {

impl View for Element {
    type V = proof::Node;

    closed spec fn view(&self) -> proof::Node {
        proof::Node {
            author: self.author as int,
            minted: self.reference.1 as int,
            item: self.item@,
            parent: proof::opt(self.parent),
            right: self.side is Right,
            deleted: self.deleted_by@.map_values(|by: (usize, Option<(usize, usize)>)| by.0 as int).to_set(),
        }
    }
}

impl View for Tree {
    type V = proof::TreeS;

    closed spec fn view(&self) -> proof::TreeS {
        proof::TreeS { nodes: self.elements@.map_values(|element: Element| element@) }
    }
}

impl Tree {
    /// What the walk keeps true of the tree between steps, for a graph of
    /// `events` events: each child list is the model's, a parent comes before
    /// its child, the top level is all right children, and every author and
    /// remover is an event.
    closed spec fn holds(&self, events: nat) -> bool {
        &&& self.holds_shape()
        &&& forall|i: int| 0 <= i < self.elements@.len() ==> {
            &&& (#[trigger] self.elements@[i]).author < events
            &&& forall|k: int| 0 <= k < self.elements@[i].deleted_by@.len()
                ==> #[trigger] self.elements@[i].deleted_by@[k].0 < events
        }
    }

    /// The tree's shape: each child list is the model's, a parent comes
    /// before its child, and the top level is all right children.
    closed spec fn holds_shape(&self) -> bool {
        let t = self@;
        &&& proof::ints(self.root@) == t.children(None, true)
        &&& forall|i: int| 0 <= i < self.elements@.len() ==> {
            &&& proof::ints((#[trigger] self.elements@[i]).left@) == t.children(Some(i), false)
            &&& proof::ints(self.elements@[i].right@) == t.children(Some(i), true)
            &&& match self.elements@[i].parent {
                Some(p) => p < i,
                None => self.elements@[i].side is Right,
            }
        }
    }
}

/// Highest first, each once.
spec fn descending(s: Seq<usize>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> #[trigger] s[i] > #[trigger] s[j]
}

/// Whether `e` may be placed next: not yet placed, and every parent placed.
spec fn ready_for(graph: Seq<Seq<usize>>, placed: Seq<bool>, e: int) -> bool {
    &&& 0 <= e < placed.len()
    &&& !placed[e]
    &&& forall|k: int| 0 <= k < graph[e].len() ==> #[trigger] placed[graph[e][k] as int]
}

/// A graph whose ancestry is reachability over a causal order is what the
/// convergence theorem asks for: a partial order, walked causally.
proof fn lemma_graph_sound(graph: &Graph<'_>, parents: Seq<Seq<usize>>)
    requires
        graph.holds(),
        parents.len() == graph.events@.len(),
        ancestry::proof::causal(parents, graph.order@),
        forall|e: int, o: int| 0 <= e < parents.len() && 0 <= o < parents.len()
            ==> (#[trigger] graph.ancestry.knows_spec(e, o) <==> ancestry::proof::reaches(parents, e, o)),
    ensures
        graph@.wf(),
        proof::valid_order(graph@, proof::ints(graph.order@)),
{
    let g = graph@;
    let order = graph.order@;
    let n = parents.len() as int;
    assert forall|e: int| g.event(e) implies g.knows(e, e) by {
        ancestry::proof::lemma_reaches_self(parents, e);
    }
    assert forall|a: int, b: int, c: int| g.event(a) && g.event(b) && g.event(c)
        && g.knows(a, b) && g.knows(b, c) implies g.knows(a, c) by {
        ancestry::proof::lemma_reaches_trans(parents, a, b, c);
    }
    assert forall|a: int, b: int| g.event(a) && g.event(b) && g.knows(a, b) && g.knows(b, a) implies a == b by {
        ancestry::proof::lemma_reaches_antisymmetric(parents, order, a, b);
    }
    let walked = proof::ints(order);
    assert forall|i: int, j: int| 0 <= i < walked.len() && 0 <= j < walked.len()
        && g.saw(walked[i], walked[j]) implies j < i by {
        ancestry::proof::lemma_place(parents, order, walked[i]);
        ancestry::proof::lemma_place(parents, order, walked[j]);
        ancestry::proof::lemma_reaches_back(parents, order, walked[i], walked[j]);
    }
    assert forall|e: int| g.event(e) implies exists|q: int| 0 <= q < walked.len() && walked[q] == e by {
        ancestry::proof::lemma_place(parents, order, e);
        assert(walked[ancestry::proof::place(order, e)] == e);
    }
    assert forall|i: int, j: int| 0 <= i < walked.len() && 0 <= j < walked.len() && i != j
        implies walked[i] != walked[j] by {
        if i < j { assert(order[i] != order[j]); } else { assert(order[j] != order[i]); }
    }
}

/// What a stack of work still has to write, top first.
spec fn pending(t: proof::TreeS, stack: Seq<Work>) -> Seq<int>
    decreases stack.len()
{
    if stack.len() == 0 {
        Seq::empty()
    } else {
        let rest = pending(t, stack.drop_last());
        match stack.last() {
            Work::Expand(at) => t.read(at as int) + rest,
            Work::Emit(at) => seq![at as int] + rest,
        }
    }
}

/// How many of the steps on a stack write an element down directly.
spec fn emits(stack: Seq<Work>) -> nat
    decreases stack.len()
{
    if stack.len() == 0 {
        0
    } else {
        emits(stack.drop_last()) + if stack.last() is Emit { 1nat } else { 0nat }
    }
}

/// Pushing a step puts what it writes in front of what was pending.
proof fn lemma_push(t: proof::TreeS, stack: Seq<Work>, work: Work)
    ensures
        pending(t, stack.push(work)) == match work {
            Work::Expand(at) => t.read(at as int) + pending(t, stack),
            Work::Emit(at) => seq![at as int] + pending(t, stack),
        },
        emits(stack.push(work)) == emits(stack) + if work is Emit { 1nat } else { 0nat },
{
    assert(stack.push(work).drop_last() =~= stack);
}

/// Each of a list of siblings read in turn, whatever is above them.
spec fn reads(t: proof::TreeS, siblings: Seq<int>) -> Seq<int>
    decreases siblings.len()
{
    if siblings.len() == 0 {
        Seq::empty()
    } else {
        t.read(siblings[0]) + reads(t, siblings.drop_first())
    }
}

/// Where every sibling is a node below `above`, the model's reading of
/// them is each read in turn.
proof fn lemma_read_all_reads(t: proof::TreeS, siblings: Seq<int>, above: int)
    requires
        forall|k: int| 0 <= k < siblings.len() ==> above < #[trigger] siblings[k] < t.len(),
    ensures
        t.read_all(siblings, above) == reads(t, siblings),
    decreases siblings.len()
{
    if siblings.len() > 0 {
        assert forall|k: int| 0 <= k < siblings.drop_first().len() implies above < #[trigger] siblings.drop_first()[k] < t.len() by {
            assert(siblings.drop_first()[k] == siblings[k + 1]);
        }
        lemma_read_all_reads(t, siblings.drop_first(), above);
    }
}

proof fn lemma_emits_bound(t: proof::TreeS, stack: Seq<Work>)
    ensures
        emits(stack) <= pending(t, stack).len(),
    decreases stack.len()
{
    if stack.len() > 0 {
        lemma_emits_bound(t, stack.drop_last());
    }
}

impl<'a> View for Event<'a> {
    type V = proof::EventS;

    closed spec fn view(&self) -> proof::EventS {
        proof::EventS {
            ops: match self.stated {
                Some((_, Stated::Operations(document))) => Some(document.operations.deep_view()),
                _ => None,
            },
            pieces: match self.stated {
                Some((_, Stated::Resolution(document))) => Some(document.pieces.deep_view()),
                _ => None,
            },
            named: match self.stated {
                Some((named, _)) => named,
                None => arbitrary(),
            },
        }
    }
}

impl<'a> View for Graph<'a> {
    type V = proof::GraphS;

    closed spec fn view(&self) -> proof::GraphS {
        let events = self.events@.len();
        proof::GraphS {
            events: self.events@.map_values(|event: Event<'a>| event@),
            knows: |e: int, o: int| 0 <= e < events && 0 <= o < events && self.ancestry.knows_spec(e, o),
        }
    }
}

impl Tree {
    /// Every index in a child list is an element hanging there, and so a
    /// node after its parent.
    proof fn lemma_listed(&self, listed: Seq<usize>, parent: Option<int>, right: bool)
        requires
            self.holds_shape(),
            proof::ints(listed) == self@.children(parent, right),
        ensures
            forall|k: int| 0 <= k < listed.len() ==> {
                &&& #[trigger] listed[k] < self.elements@.len()
                &&& self@.hangs(listed[k] as int, parent, right)
                &&& (parent matches Some(p) ==> p < listed[k])
            },
    {
        proof::lemma_children_nodes(self@, parent, right);
        assert forall|k: int| 0 <= k < listed.len() implies {
            &&& #[trigger] listed[k] < self.elements@.len()
            &&& self@.hangs(listed[k] as int, parent, right)
            &&& (parent matches Some(p) ==> p < listed[k])
        } by {
            assert(proof::ints(listed)[k] == listed[k] as int);
            let j = listed[k] as int;
            assert(self@.hangs(j, parent, right));
            assert(self@.nodes[j] == self.elements@[j]@);
        }
    }
}

impl Tree {
    /// A tree whose elements have the names they had, in the same number,
    /// has the same names: distinct where they were, and none minted anew.
    proof fn lemma_names_alike(&self, before: proof::TreeS)
        requires
            before.len() == self.elements@.len(),
            forall|i: int| 0 <= i < before.len() ==> {
                &&& (#[trigger] self.elements@[i]).author == before.nodes[i].author
                &&& self.elements@[i].reference.1 == before.nodes[i].minted
            },
        ensures
            proof::distinct_names(before) ==> proof::distinct_names(self@),
            forall|a: int, m: int| #[trigger] before.minted_below(a, m) ==> self@.minted_below(a, m),
    {
        assert forall|i: int| 0 <= i < before.len() implies #[trigger] self@.id(i) == before.id(i) by {
            assert(self@.nodes[i] == self.elements@[i]@);
        }
        assert forall|a: int, m: int| #[trigger] before.minted_below(a, m) implies self@.minted_below(a, m) by {
            assert forall|i: int| self@.node(i) && (#[trigger] self@.nodes[i]).author == a implies self@.nodes[i].minted < m by {
                assert(self@.nodes[i] == self.elements@[i]@);
            }
        }
    }
}

/// The positions of a view a resolution has kept so far.
spec fn kept_set(kept: Seq<bool>) -> ISet<int> {
    ISet::new(|q: int| 0 <= q < kept.len() && kept[q])
}

/// `slots[a][m]` holds the position in `prepare` of the element event `a`
/// minted `m`th, wherever it stands in it, and nothing else.
spec fn slots_hold(elements: Seq<Element>, prepare: Seq<usize>, slots: Seq<Vec<Option<usize>>>, events: nat) -> bool {
    &&& slots.len() == events
    &&& prepare.len() <= usize::MAX
    &&& forall|a: int, m: int| 0 <= a < events && 0 <= m < slots[a]@.len()
        && (#[trigger] slots[a]@[m]) is Some ==> {
            let p = slots[a]@[m]->Some_0 as int;
            &&& 0 <= p < prepare.len()
            &&& elements[prepare[p] as int].author == a
            &&& elements[prepare[p] as int].reference.1 == m
        }
    &&& forall|p: int| 0 <= p < prepare.len() ==> {
        let element = #[trigger] elements[prepare[p] as int];
        &&& element.author < events
        &&& element.reference.1 < slots[element.author as int]@.len()
        &&& slots[element.author as int]@[element.reference.1 as int] == Some(p as usize)
    }
}

/// Slots taken of a view still hold once elements are added or marked,
/// which changes no element's name.
proof fn lemma_slots_kept(before: Seq<Element>, after: Seq<Element>, prepare: Seq<usize>, slots: Seq<Vec<Option<usize>>>, events: nat)
    requires
        slots_hold(before, prepare, slots, events),
        before.len() <= after.len(),
        forall|q: int| 0 <= q < prepare.len() ==> #[trigger] prepare[q] < before.len(),
        forall|i: int| 0 <= i < before.len() ==> {
            &&& (#[trigger] after[i]).author == before[i].author
            &&& after[i].reference == before[i].reference
        },
    ensures
        slots_hold(after, prepare, slots, events),
{
    assert forall|p: int| 0 <= p < prepare.len() implies #[trigger] after[prepare[p] as int] == after[prepare[p] as int]
        && after[prepare[p] as int].author == before[prepare[p] as int].author by {}
}

impl Tree {
    /// Every parent comes before its child.
    proof fn lemma_shaped(&self)
        requires self.holds_shape()
        ensures proof::shaped(self@)
    {
        assert forall|j: int| self@.node(j) implies match (#[trigger] self@.nodes[j]).parent {
            Some(p) => 0 <= p < j,
            None => true,
        } by {
            assert(self@.nodes[j] == self.elements@[j]@);
        }
    }
}

impl Graph<'_> {
    /// The ancestry answers for exactly these events.
    closed spec fn holds(&self) -> bool {
        self.ancestry.holds() && self.ancestry.events() == self.events@.len()
    }
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diff::diff;
    use crate::format::{PREAMBLE, digest};
    use crate::replay::replay;

    /// A history built by hand: documents, and the events that name them.
    #[derive(Default)]
    struct History {
        documents: Vec<OperationDocument>,
        resolutions: Vec<ResolutionDocument>,
        events: Vec<(RevisionId, Vec<RevisionId>, Option<At>)>,
    }

    /// Which of the two content grammars a revision stated its file in.
    #[derive(Debug, Clone, Copy)]
    enum At {
        Operations(usize),
        Resolution(usize),
    }

    impl History {
        /// One revision, named for readability and identified by that name's
        /// digest, which stands in for the digest of a revision document.
        fn revision(
            &mut self,
            name: &str,
            parents: &[&str],
            operations: Option<&[&str]>,
        ) -> &mut Self {
            let document = operations.map(|lines| {
                let mut text = format!("{PREAMBLE}\n\n");
                for line in lines {
                    text.push_str(line);
                    text.push('\n');
                }
                OperationDocument::parse(text.as_bytes()).expect("a document that parses")
            });
            let at = document.map(|document| {
                self.documents.push(document);
                At::Operations(self.documents.len() - 1)
            });
            self.events.push((
                digest(name.as_bytes()),
                parents.iter().map(|name| digest(name.as_bytes())).collect(),
                at,
            ));
            self
        }

        /// A merge stating decision 0032's resolution, whose `result` is the
        /// digest of the file the pieces assemble to.
        fn resolving(
            &mut self,
            name: &str,
            parents: &[&str],
            assembles: &str,
            pieces: &[&str],
        ) -> &mut Self {
            let mut text = format!("{PREAMBLE}\nresult {}\n\n", digest(assembles.as_bytes()));
            for line in pieces {
                text.push_str(line);
                text.push('\n');
            }
            let document =
                ResolutionDocument::parse(text.as_bytes()).expect("a resolution that parses");
            self.resolutions.push(document);
            let at = At::Resolution(self.resolutions.len() - 1);
            self.events.push((
                digest(name.as_bytes()),
                parents.iter().map(|name| digest(name.as_bytes())).collect(),
                Some(at),
            ));
            self
        }

        /// A merge stating a resolution already built, for the randomised
        /// tests that draft one from a proposal.
        fn resolved(
            &mut self,
            name: &str,
            parents: &[&str],
            document: ResolutionDocument,
        ) -> &mut Self {
            self.resolutions.push(document);
            let at = At::Resolution(self.resolutions.len() - 1);
            self.events.push((
                digest(name.as_bytes()),
                parents.iter().map(|name| digest(name.as_bytes())).collect(),
                Some(at),
            ));
            self
        }

        /// The digest naming the document one revision stated its file in,
        /// which is the half of an item's name a `keep` line quotes.
        fn document(&self, name: &str) -> RevisionId {
            let revision = digest(name.as_bytes());
            let (_, _, at) = self
                .events
                .iter()
                .find(|(id, _, _)| *id == revision)
                .expect("a revision by that name");
            match at.expect("a revision that stated something") {
                At::Operations(at) => digest(&self.documents[at].write()),
                At::Resolution(at) => digest(&self.resolutions[at].write()),
            }
        }

        fn events(&self) -> Vec<Event<'_>> {
            self.events
                .iter()
                .map(|(revision, parents, at)| match at {
                    Some(At::Operations(at)) => {
                        let document = &self.documents[*at];
                        Event::operations(
                            *revision,
                            parents.clone(),
                            digest(&document.write()),
                            document,
                        )
                    }
                    Some(At::Resolution(at)) => {
                        let document = &self.resolutions[*at];
                        Event::resolution(
                            *revision,
                            parents.clone(),
                            digest(&document.write()),
                            document,
                        )
                    }
                    None => Event::nothing(*revision, parents.clone()),
                })
                .collect()
        }

        fn merged(&self) -> Merged {
            merge(self.events()).expect("a history that merges")
        }

        fn text(&self) -> String {
            self.merged().state.text()
        }

        /// Every order that puts an event after its parents.
        fn topological_orders(&self) -> Vec<Vec<usize>> {
            let graph = Graph::new(self.events()).expect("a graph");
            let mut orders = Vec::new();
            let mut taken = vec![false; graph.events.len()];
            let mut current = Vec::new();
            fn walk(
                graph: &Graph<'_>,
                taken: &mut Vec<bool>,
                current: &mut Vec<usize>,
                orders: &mut Vec<Vec<usize>>,
            ) {
                if current.len() == graph.events.len() {
                    orders.push(current.clone());
                    return;
                }
                for next in 0..graph.events.len() {
                    if taken[next] {
                        continue;
                    }
                    let ready = (0..graph.events.len())
                        .all(|ancestor| !graph.saw(next, ancestor) || taken[ancestor]);
                    if !ready {
                        continue;
                    }
                    taken[next] = true;
                    current.push(next);
                    walk(graph, taken, current, orders);
                    current.pop();
                    taken[next] = false;
                }
            }
            walk(&graph, &mut taken, &mut current, &mut orders);
            orders
        }
    }

    /// Decision 0032: the walk takes a resolution as the recorded truth of
    /// the file at that revision.
    #[test]
    fn a_resolution_says_what_survived_and_what_did_not() {
        let mut history = History::default();
        history
            .revision("root", &[], Some(&["insert 0", "+a", "+b", "+c"]))
            .revision("left", &["root"], Some(&["insert 1", "+L"]))
            .revision("right", &["root"], Some(&["insert 2", "+R"]));

        // Unresolved, the two branches meet and both lines stand.
        assert_eq!(history.text(), "a\nL\nb\nR\nc\n");

        let (root, left) = (history.document("root"), history.document("left"));
        history.resolving(
            "merge",
            &["left", "right"],
            "a\nL\nb\nc\nX\n",
            &[
                &format!("keep {root} 0 1"),
                &format!("keep {left} 0 1"),
                &format!("keep {root} 1 2"),
                "insert",
                "+X",
            ],
        );

        // What the resolution states, and nothing of the line it dropped.
        assert_eq!(history.text(), "a\nL\nb\nc\nX\n");
        // An item the resolution does not keep is dead there, exactly as a
        // delete: every walk order agrees, because a tombstone is a fact.
        for order in history.topological_orders() {
            let graph = Graph::new(history.events()).expect("a graph");
            assert_eq!(
                walk(&graph, &order).expect("a merge").state.text(),
                "a\nL\nb\nc\nX\n"
            );
        }
    }

    /// The property the decision calls load-bearing: a kept item survives
    /// under its own name, so a branch that edits it merges rather than
    /// colliding with a copy.
    #[test]
    fn a_kept_item_keeps_its_name_and_a_concurrent_edit_still_lands_on_it() {
        let mut history = History::default();
        history
            .revision("root", &[], Some(&["insert 0", "+a", "+b"]))
            .revision("left", &["root"], Some(&["insert 1", "+L"]))
            .revision("right", &["root"], Some(&["insert 2", "+R"]));
        let (root, left) = (history.document("root"), history.document("left"));
        history
            .resolving(
                "merge",
                &["left", "right"],
                "a\nL\nb\n",
                &[
                    &format!("keep {root} 0 1"),
                    &format!("keep {left} 0 1"),
                    &format!("keep {root} 1 1"),
                ],
            )
            // Taken from `left`, concurrently with the merge, and deleting the
            // very line the resolution kept.
            .revision("aside", &["left"], Some(&["delete 1 1", "-L"]))
            .revision("after", &["merge", "aside"], None);

        // One `L`, and it is gone: the delete met the item the resolution
        // kept rather than a restated copy standing beside it.
        assert_eq!(history.text(), "a\nb\n");
    }

    /// A resolution quotes nothing it drops, so a redaction has nothing to
    /// chase there — decision 0032's reason for references over bytes.
    #[test]
    fn dropping_an_item_by_not_keeping_it_quotes_nothing() {
        let mut history = History::default();
        history
            .revision("root", &[], Some(&["insert 0", "+a", "+b"]))
            .revision("left", &["root"], Some(&["insert 2", "+L"]))
            .revision("right", &["root"], Some(&["insert 2", "+R"]));
        let root = history.document("root");
        history.resolving(
            "merge",
            &["left", "right"],
            "a\nb\n",
            &[&format!("keep {root} 0 2")],
        );

        let quoted = quotes(history.events()).expect("a history that merges");
        let dropped: Vec<&Quoted> = quoted.iter().filter(|item| !item.visible).collect();
        assert_eq!(dropped.len(), 2, "both branches' lines are gone");
        for item in dropped {
            assert!(
                item.deletes.is_empty(),
                "a resolution states what survives, so it quotes nothing"
            );
        }
    }

    /// The byte-identical case `Element::reference` describes, resolved: two
    /// concurrent revisions record one document, so two elements stand under
    /// one name, and a resolution keeping both can only spell that as the
    /// same `keep` twice. Each occurrence consumes the next element still
    /// standing under the name, so the walk reads exactly the file the
    /// resolution assembles to by hand — an insert between the two
    /// occurrences included, which is what pins where each one landed.
    #[test]
    fn a_keep_of_a_name_two_concurrent_revisions_share_lands_once_per_element() {
        let mut history = History::default();
        history
            .revision("root", &[], Some(&["insert 0", "+a"]))
            .revision("left", &["root"], Some(&["insert 0", "+x"]))
            .revision("right", &["root"], Some(&["insert 0", "+x"]));
        let (root, shared) = (history.document("root"), history.document("left"));
        assert_eq!(
            shared,
            history.document("right"),
            "the two branches are meant to record one byte-identical document"
        );
        assert_eq!(history.text(), "x\nx\na\n");

        history.resolving(
            "merge",
            &["left", "right"],
            "x\nbetween\nx\na\n",
            &[
                &format!("keep {shared} 0 1"),
                "insert",
                "+between",
                &format!("keep {shared} 0 1"),
                &format!("keep {root} 0 1"),
            ],
        );
        assert_eq!(history.text(), "x\nbetween\nx\na\n");
    }

    /// The same shape, kept once more than the view holds elements under the
    /// name — which no view can satisfy, so it is refused rather than folded
    /// onto an element some other `keep` already consumed.
    #[test]
    fn a_keep_of_a_shared_name_beyond_the_elements_standing_under_it_is_refused() {
        let mut history = History::default();
        history
            .revision("root", &[], Some(&["insert 0", "+a"]))
            .revision("left", &["root"], Some(&["insert 0", "+x"]))
            .revision("right", &["root"], Some(&["insert 0", "+x"]));
        let (root, shared) = (history.document("root"), history.document("left"));
        history.resolving(
            "merge",
            &["left", "right"],
            "x\nx\nx\na\n",
            &[
                &format!("keep {shared} 0 1"),
                &format!("keep {shared} 0 1"),
                &format!("keep {shared} 0 1"),
                &format!("keep {root} 0 1"),
            ],
        );
        assert!(matches!(
            merge(history.events()).expect_err("a third keep of two elements"),
            MergeError::UnknownReference { .. }
        ));
    }

    /// A `keep` naming something the author could not see is the store
    /// contradicting itself, not a merge that failed.
    #[test]
    fn a_keep_of_an_item_nobody_wrote_is_refused() {
        let mut history = History::default();
        history
            .revision("root", &[], Some(&["insert 0", "+a"]))
            .revision("left", &["root"], Some(&["insert 1", "+L"]))
            .revision("right", &["root"], Some(&["insert 1", "+R"]));
        let root = history.document("root");
        history.resolving(
            "merge",
            &["left", "right"],
            "a\n",
            // `root` minted one item, so its item 4 is nothing at all.
            &[&format!("keep {root} 4 1")],
        );
        assert!(matches!(
            merge(history.events()).expect_err("a reference to nothing"),
            MergeError::UnknownReference { .. }
        ));
    }

    /// The walk-order property, over graphs that hold a resolution.
    ///
    /// Decision 0032 leaves the walk in place for merging branches that reach
    /// across a recorded merge, so everything 0007's acceptance test claims
    /// has to keep holding once a resolution is in the graph: an element's
    /// place is decided by what its own author had seen, and any order that
    /// puts an event after its parents produces one file.
    #[test]
    fn a_graph_holding_a_resolution_walks_to_one_file_in_every_order() {
        let mut rng = Rng(0x0032_0007_c0de_f00d);
        let mut resolutions = 0;
        for round in 0..120 {
            let mut history = History::default();
            history.revision("root", &[], Some(&["insert 0", "+a", "+b", "+c", "+d"]));

            // Two hands on the root, neither having seen the other.
            let mut branches = Vec::new();
            for replica in 0..2 {
                let (text, document) = edit(&mut rng, "a\nb\nc\nd\n");
                let Some(document) = document else { continue };
                let name = format!("branch-{replica}");
                history.documents.push(document);
                let at = At::Operations(history.documents.len() - 1);
                history
                    .events
                    .push((digest(name.as_bytes()), vec![digest(b"root")], Some(at)));
                branches.push((name, text));
            }
            if branches.len() < 2 {
                continue;
            }

            // A person reads both sides, edits, and records what the file is.
            let proposed = merge(history.events()).expect("a merge");
            let (text, _) = edit(&mut rng, &proposed.state.text());
            let after = State::from_text(&text);
            let Some(resolution) =
                crate::diff::resolve(&proposed.state, &proposed.references, &after)
            else {
                continue;
            };
            let sides: Vec<&str> = branches.iter().map(|(name, _)| name.as_str()).collect();
            history.resolved("merge", &sides, resolution);
            resolutions += 1;

            // And a third hand, taken from one branch before the merge —
            // counting into *that* branch's file, as its author would — whose
            // edits must land on the items the resolution kept rather than on
            // copies of them.
            let (_, aside) = edit(&mut rng, &branches[0].1);
            if let Some(document) = aside {
                history.documents.push(document);
                let at = At::Operations(history.documents.len() - 1);
                history.events.push((
                    digest(b"aside"),
                    vec![digest(sides[0].as_bytes())],
                    Some(at),
                ));
                history.events.push((
                    digest(b"after"),
                    vec![digest(b"merge"), digest(b"aside")],
                    None,
                ));
            }

            let graph = Graph::new(history.events()).expect("a graph");
            let orders = history.topological_orders();
            let expected =
                walk(&graph, &orders[0]).unwrap_or_else(|error| panic!("round {round}: {error}"));
            for order in &orders {
                assert_eq!(
                    walk(&graph, order).expect("a merge"),
                    expected,
                    "round {round}, order {order:?}"
                );
            }
        }
        assert!(
            resolutions > 40,
            "only {resolutions} rounds actually held a resolution"
        );
    }

    /// A chain is recognised as one, and replays to the file that was edited.
    ///
    /// [`Ancestry::Chain`] is the whole reason a history with no fork in it
    /// costs a position per event rather than a row of bits, so the shape has
    /// to be detected on the histories a person actually records rather than
    /// on the two-revision ones written by hand below.
    #[test]
    fn a_chain_is_stored_as_one_and_replays_to_what_was_edited() {
        struct Rng(u64);
        impl Rng {
            fn below(&mut self, bound: usize) -> usize {
                self.0 ^= self.0 << 13;
                self.0 ^= self.0 >> 7;
                self.0 ^= self.0 << 17;
                (self.0.wrapping_mul(0x2545_f491_4f6c_dd1d) >> 33) as usize % bound.max(1)
            }
        }

        let mut rng = Rng(0x0007_11ea_c4a1_0000);
        for round in 0..400 {
            let mut text = String::from("alpha\nbeta\ngamma\n");
            let mut history = History::default();
            let names: Vec<String> = (0..10).map(|at| format!("r{round}-{at}")).collect();
            history.revision(
                &names[0],
                &[],
                Some(&["insert 0", "+alpha", "+beta", "+gamma"]),
            );

            for step in 1..names.len() {
                let before = State::from_text(&text);
                let mut lines: Vec<String> = text.lines().map(|line| format!("{line}\n")).collect();
                match rng.below(5) {
                    // Append past the end, where a chain of right children forms.
                    0 => lines.push(format!("added {round}-{step}\n")),
                    // Delete a line, leaving a tombstone the tree keeps.
                    1 if !lines.is_empty() => {
                        let at = rng.below(lines.len());
                        lines.remove(at);
                    }
                    // Delete the tail, so the next append sees no visible
                    // right neighbour and anchors to a tombstone.
                    2 if !lines.is_empty() => {
                        lines.pop();
                    }
                    // Insert in the middle, beside whatever is there.
                    3 => {
                        let at = rng.below(lines.len() + 1);
                        lines.insert(at, format!("wedged {round}-{step}\n"));
                    }
                    // Rewrite a run, which is a delete and an insert at once.
                    _ if !lines.is_empty() => {
                        let at = rng.below(lines.len());
                        lines[at] = format!("rewritten {round}-{step}\n");
                    }
                    _ => lines.push(format!("added {round}-{step}\n")),
                }
                text = lines.concat();
                let after = State::from_text(&text);
                let document = diff(&before, &after);
                let written: Option<Vec<String>> = document.as_ref().map(|document| {
                    String::from_utf8(document.write())
                        .expect("a document is text")
                        .lines()
                        .skip_while(|line| !line.is_empty())
                        .skip(1)
                        .map(str::to_owned)
                        .collect()
                });
                let borrowed: Option<Vec<&str>> = written
                    .as_ref()
                    .map(|lines| lines.iter().map(String::as_str).collect());
                history.revision(&names[step], &[&names[step - 1]], borrowed.as_deref());
            }

            let graph = Graph::new(history.events()).expect("a graph");
            assert!(
                matches!(graph.ancestry, Ancestry::Chain { .. }),
                "round {round}: one parent each is a chain, and must be stored as one"
            );

            // The oracle is the edit itself: each revision was recorded from a
            // real before-and-after pair, so the text edited into place is
            // what the history means.
            assert_eq!(
                replay(history.documents.iter()).expect("a replay").text(),
                text,
                "round {round}: the replayer disagrees with the edit"
            );
            // [`merge`] sends a chain to [`linear`]; the walk is held to the
            // same answer directly, item for item, so the two paths cannot
            // drift apart behind the dispatch.
            let merged = merge(history.events()).expect("a merge");
            assert_eq!(
                merged.state.text(),
                text,
                "round {round}: the linear path disagrees with the edit"
            );
            let order = graph.order.clone();
            assert_eq!(
                walk(&graph, &order).expect("a walk"),
                merged,
                "round {round}: the walk disagrees with the linear path"
            );
            assert!(
                merged.contested.is_empty(),
                "round {round}: nothing in a chain is concurrent, so nothing is contested"
            );
            assert_eq!(
                merged.origins.len(),
                merged.state.len(),
                "round {round}: every item has an author"
            );
        }
    }

    /// A defect the tree walk used to have, kept executable rather than in
    /// prose.
    ///
    /// [`Tree::anchor`] once took the author's next *visible* element as the
    /// right origin, where Fugue takes the next element in the traversal,
    /// tombstones included. Whenever an insertion's left neighbour held a
    /// tombstoned right child, that handed two causally ordered elements one
    /// parent and side, and [`Tree::attach`]'s digest tie-break — right
    /// between concurrent elements, wrong between ordered ones — read them
    /// out on a coin flip: 94 of these 200 chains once misordered.
    ///
    /// Below, `d` and `f` sit four revisions apart in one chain with nothing
    /// concurrent anywhere in it, and the file must read `a d f c` on every
    /// digest, as [`crate::replay`] — and so `check` — always said.
    #[test]
    fn the_tree_walk_keeps_a_chain_in_causal_order_around_tombstones() {
        let mut wrong = 0;
        for salt in 0..200 {
            let names: Vec<String> = (1..=7).map(|at| format!("s{salt}-r{at}")).collect();
            let at: Vec<&str> = names.iter().map(String::as_str).collect();
            let mut history = History::default();
            history
                .revision(at[0], &[], Some(&["insert 0", "+a", "+c"]))
                .revision(at[1], &[at[0]], Some(&["insert 1", "+b"]))
                .revision(at[2], &[at[1]], Some(&["delete 1 1", "-b"]))
                .revision(at[3], &[at[2]], Some(&["insert 1", "+d"]))
                .revision(at[4], &[at[3]], Some(&["insert 2", "+e"]))
                .revision(at[5], &[at[4]], Some(&["delete 2 1", "-e"]))
                .revision(at[6], &[at[5]], Some(&["insert 2", "+f"]));

            let graph = Graph::new(history.events()).expect("a graph");
            let order = graph.order.clone();
            if walk(&graph, &order).expect("a walk").state.text() != "a\nd\nf\nc\n" {
                wrong += 1;
            }
        }
        assert_eq!(wrong, 0, "the walk misordered {wrong} of 200 chains");
    }

    /// The same chains, held to the answer [`crate::replay`] gives.
    ///
    /// This is what `check` computes for these histories, and while the walk
    /// carried the defect above it was the account that stayed right: `cat`
    /// returned the walk's bytes in the wrong order, `status` then called the
    /// file edited the moment after it was recorded, and the next `record`
    /// wrote a document saying its author moved a line they never touched.
    #[test]
    fn the_replayer_does_not_reorder_a_chain_around_a_tombstone() {
        for salt in 0..200 {
            let names: Vec<String> = (1..=7).map(|at| format!("s{salt}-r{at}")).collect();
            let at: Vec<&str> = names.iter().map(String::as_str).collect();
            let mut history = History::default();
            history
                .revision(at[0], &[], Some(&["insert 0", "+a", "+c"]))
                .revision(at[1], &[at[0]], Some(&["insert 1", "+b"]))
                .revision(at[2], &[at[1]], Some(&["delete 1 1", "-b"]))
                .revision(at[3], &[at[2]], Some(&["insert 1", "+d"]))
                .revision(at[4], &[at[3]], Some(&["insert 2", "+e"]))
                .revision(at[5], &[at[4]], Some(&["delete 2 1", "-e"]))
                .revision(at[6], &[at[5]], Some(&["insert 2", "+f"]));

            assert_eq!(
                replay(history.documents.iter()).expect("a replay").text(),
                "a\nd\nf\nc\n",
                "salt {salt}: the replayer reordered a chain"
            );
        }
    }

    /// A root that writes three lines, which most of these start from.
    fn abc() -> History {
        let mut history = History::default();
        history.revision("root", &[], Some(&["insert 0", "+a", "+b", "+c"]));
        history
    }

    #[test]
    fn a_linear_history_merges_to_what_replay_produces() {
        // The claim decision 0007 makes about the common case: when nothing is
        // concurrent, this is application and agrees with the simple path.
        let mut history = abc();
        history
            .revision(
                "second",
                &["root"],
                Some(&["delete 1 1", "-b", "insert 1", "+B"]),
            )
            .revision("third", &["second"], Some(&["insert 3", "+d"]));

        let chain: Vec<&OperationDocument> = history.documents.iter().collect();
        assert_eq!(history.text(), replay(chain).expect("a chain").text());
        assert_eq!(history.text(), "a\nB\nc\nd\n");
        assert!(history.merged().contested.is_empty());
    }

    #[test]
    fn concurrent_edits_in_different_places_both_survive() {
        let mut history = abc();
        history
            .revision("left", &["root"], Some(&["insert 0", "+top"]))
            .revision("right", &["root"], Some(&["insert 3", "+bottom"]));
        assert_eq!(history.text(), "top\na\nb\nc\nbottom\n");
        assert!(history.merged().contested.is_empty());
    }

    #[test]
    fn concurrent_runs_at_one_position_do_not_interleave() {
        // The property decision 0007 chose Fugue for. Two people write a
        // paragraph in the same place; each paragraph must come out whole.
        let mut history = abc();
        history
            .revision("left", &["root"], Some(&["insert 1", "+x1", "+x2", "+x3"]))
            .revision("right", &["root"], Some(&["insert 1", "+y1", "+y2", "+y3"]));

        let text = history.text();
        assert!(text.contains("x1\nx2\nx3\n"), "{text}");
        assert!(text.contains("y1\ny2\ny3\n"), "{text}");
        assert!(text.starts_with("a\n"), "{text}");
        assert!(text.ends_with("b\nc\n"), "{text}");

        // And the tie is reported rather than hidden: one span per run, each
        // covering the whole paragraph its author wrote.
        let contested = history.merged().contested;
        assert_eq!(contested.len(), 2, "{contested:?}");
        for contest in &contested {
            assert_eq!(contest.kind, Contest::Insertion);
            assert_eq!(contest.len, 3, "the whole run is shown");
            assert_eq!(contest.revisions.len(), 1);
        }
    }

    #[test]
    fn runs_written_backwards_do_not_interleave_either() {
        // Each line inserted before the one written a moment ago, which is the
        // case a naive rule gets wrong.
        let mut history = abc();
        history
            .revision("left-1", &["root"], Some(&["insert 1", "+x1"]))
            .revision("left-2", &["left-1"], Some(&["insert 1", "+x2"]))
            .revision("right-1", &["root"], Some(&["insert 1", "+y1"]))
            .revision("right-2", &["right-1"], Some(&["insert 1", "+y2"]));

        let text = history.text();
        assert!(text.contains("x2\nx1\n"), "{text}");
        assert!(text.contains("y2\ny1\n"), "{text}");
    }

    #[test]
    fn concurrent_deletions_of_one_line_agree() {
        let mut history = abc();
        history
            .revision("left", &["root"], Some(&["delete 1 1", "-b"]))
            .revision("right", &["root"], Some(&["delete 1 1", "-b"]));
        assert_eq!(history.text(), "a\nc\n");
        assert!(
            history.merged().contested.is_empty(),
            "agreement is not a contest"
        );
    }

    #[test]
    fn a_deletion_beside_a_concurrent_insertion_is_reported() {
        // Nothing is lost: the inserted line stays, and the removal stands.
        // What a person is told is that the two met.
        let mut history = abc();
        history
            .revision("left", &["root"], Some(&["delete 1 1", "-b"]))
            .revision("right", &["root"], Some(&["insert 2", "+new"]));

        let merged = history.merged();
        assert_eq!(merged.state.text(), "a\nnew\nc\n");
        assert_eq!(merged.contested.len(), 1, "{:?}", merged.contested);
        assert_eq!(merged.contested[0].kind, Contest::Deletion);
    }

    #[test]
    fn a_merge_revision_that_records_nothing_changes_nothing() {
        let mut history = abc();
        history
            .revision("left", &["root"], Some(&["insert 0", "+top"]))
            .revision("right", &["root"], Some(&["insert 3", "+bottom"]))
            .revision("merge", &["left", "right"], None);
        assert_eq!(history.text(), "top\na\nb\nc\nbottom\n");
    }

    #[test]
    fn the_result_does_not_depend_on_the_order_the_graph_is_walked() {
        // Decision 0007's second acceptance claim: replaying one graph in
        // different topological orders produces the same bytes.
        let mut history = abc();
        history
            .revision("left", &["root"], Some(&["insert 1", "+x1", "+x2"]))
            .revision(
                "right",
                &["root"],
                Some(&["insert 1", "+y", "delete 2 1", "-c"]),
            )
            .revision("after", &["left"], Some(&["insert 0", "+first"]));

        let orders = history.topological_orders();
        assert!(orders.len() > 1, "the graph has room for several orders");
        let graph = Graph::new(history.events()).expect("a graph");
        let expected = walk(&graph, &orders[0]).expect("a merge");
        for order in &orders {
            assert_eq!(
                walk(&graph, order).expect("a merge"),
                expected,
                "order {order:?} produced a different file"
            );
        }
    }

    #[test]
    fn the_events_may_arrive_in_any_order() {
        let mut history = abc();
        history
            .revision("left", &["root"], Some(&["insert 1", "+x"]))
            .revision("right", &["root"], Some(&["insert 1", "+y"]));

        let forwards = merge(history.events()).expect("a merge");
        let mut backwards = history.events();
        backwards.reverse();
        assert_eq!(merge(backwards).expect("a merge"), forwards);
    }

    #[test]
    fn a_document_that_disagrees_with_its_authors_view_is_refused() {
        let mut history = abc();
        history.revision("wrong", &["root"], Some(&["delete 1 1", "-not-b"]));
        let error = merge(history.events()).expect_err("a disagreement");
        assert!(matches!(error, MergeError::ItemDisagrees { .. }), "{error}");
        assert!(error.to_string().contains("not-b"));
    }

    #[test]
    fn a_head_whose_past_is_incomplete_is_refused() {
        let mut history = History::default();
        history.revision("child", &["absent"], Some(&["insert 0", "+a"]));
        assert!(matches!(
            merge(history.events()).expect_err("an incomplete past"),
            MergeError::MissingParent { .. }
        ));
    }

    /// The generator from `examples/matchers.rs`, again: deterministic, so a
    /// surprising result can be looked at twice.
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            self.0 = x;
            x.wrapping_mul(0x2545_f491_4f6c_dd1d)
        }

        fn below(&mut self, bound: usize) -> usize {
            (self.next() % bound as u64) as usize
        }
    }

    /// Edit a file the way a person does, and record what that did.
    fn edit(rng: &mut Rng, text: &str) -> (String, Option<OperationDocument>) {
        let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
        for _ in 0..1 + rng.below(3) {
            match rng.below(3) {
                0 if !lines.is_empty() => {
                    let at = rng.below(lines.len());
                    lines.remove(at);
                }
                1 if !lines.is_empty() => {
                    let at = rng.below(lines.len());
                    lines[at] = format!("edited {}", rng.below(5));
                }
                _ => {
                    let at = rng.below(lines.len() + 1);
                    for offset in 0..1 + rng.below(3) {
                        lines.insert(at + offset, format!("written {}", rng.below(5)));
                    }
                }
            }
        }
        let mut out = String::new();
        for line in &lines {
            out.push_str(line);
            out.push('\n');
        }
        let document = diff(&State::from_text(text), &State::from_text(&out));
        (out, document)
    }

    #[test]
    fn a_revision_may_be_recorded_against_a_merged_state() {
        // What a tool does when a person merges and keeps working: the merge
        // is materialised, the next edit is recorded against it, and that
        // document's positions mean nothing until the same merge is
        // reconstructed. This is the case a prepare state exists for.
        let mut rng = Rng(0x51de_babe);
        for round in 0..100 {
            let mut history = abc();
            let mut branches = Vec::new();
            for replica in 0..2 {
                let (_, document) = edit(&mut rng, "a\nb\nc\n");
                let Some(document) = document else { continue };
                let name = format!("replica-{replica}");
                history.documents.push(document);
                let at = At::Operations(history.documents.len() - 1);
                history
                    .events
                    .push((digest(name.as_bytes()), vec![digest(b"root")], Some(at)));
                branches.push(name);
            }
            if branches.len() < 2 {
                continue;
            }

            // Merge what exists so far, edit that, and record the difference.
            let merged = merge(history.events()).expect("a merge").state;
            let (_, document) = edit(&mut rng, &merged.text());
            let parents = branches
                .iter()
                .map(|name| digest(name.as_bytes()))
                .collect();
            let at = document.map(|document| {
                history.documents.push(document);
                At::Operations(history.documents.len() - 1)
            });
            history
                .events
                .push((digest(b"after-the-merge"), parents, at));

            let graph = Graph::new(history.events()).expect("a graph");
            let orders = history.topological_orders();
            let expected =
                walk(&graph, &orders[0]).unwrap_or_else(|error| panic!("round {round}: {error}"));
            for order in &orders {
                assert_eq!(
                    walk(&graph, order).expect("a merge"),
                    expected,
                    "round {round}, order {order:?}"
                );
            }
        }
    }

    #[test]
    fn replicas_editing_at_once_converge_whatever_order_they_are_walked_in() {
        // Decision 0007's acceptance test: random operations from several
        // replicas, merged in every order the graph allows, byte-identical.
        let mut rng = Rng(0x00c0_ffee_1234);
        for round in 0..200 {
            let mut history = abc();
            let mut text = "a\nb\nc\n".to_owned();
            let replicas = 2 + rng.below(2);

            for replica in 0..replicas {
                // Each replica edits the root, without seeing the others.
                let (_, document) = edit(&mut rng, &text);
                let name = format!("replica-{replica}");
                match document {
                    Some(document) => {
                        history.documents.push(document);
                        let at = At::Operations(history.documents.len() - 1);
                        history.events.push((
                            digest(name.as_bytes()),
                            vec![digest(b"root")],
                            Some(at),
                        ));
                    }
                    None => continue,
                }
            }
            text.push_str("");

            let orders = history.topological_orders();
            let graph = Graph::new(history.events()).expect("a graph");
            let expected =
                walk(&graph, &orders[0]).unwrap_or_else(|error| panic!("round {round}: {error}"));
            for order in &orders {
                assert_eq!(
                    walk(&graph, order).expect("a merge"),
                    expected,
                    "round {round}, order {order:?}"
                );
            }

            // Every line a replica wrote survives somewhere, because a merge
            // that quietly dropped work would converge just as well. Only the
            // replicas' own lines: a line the root wrote can be deleted, and
            // one of them deleting it is not a loss.
            let merged = expected.state.text();
            for document in history.documents.iter().skip(1) {
                for operation in &document.operations {
                    if operation.kind == OperationKind::Insert {
                        for item in &operation.items {
                            assert!(
                                merged.contains(&item.text),
                                "round {round}: `{}` was lost in {merged:?}",
                                item.text
                            );
                        }
                    }
                }
            }
        }
    }
}
