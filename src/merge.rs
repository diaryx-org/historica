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
//! implemented as the tree formulation, in [`anchor`] and [`Tree::order`], and
//! kept in one place because 0007 owes it a conformance suite against the
//! reference implementation before any of this is called done.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::ancestry::Ancestry;
use crate::core::RevisionId;
use crate::format::{Item, OperationDocument, OperationKind, Piece, ResolutionDocument};
use crate::replay::State;

/// What one revision stated about one file.
///
/// Two spellings, and decision 0032 is the second: a revision either says what
/// it *did* to the file, against the state at its parents, or — where a merge's
/// parents disagree — says what the file *is*, whole, by reference.
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
#[derive(Debug, Clone)]
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
pub struct Quoted {
    /// The revision that wrote the item.
    pub written_by: RevisionId,
    /// Which operation and item of that revision's document wrote it.
    pub write: (usize, usize),
    /// Every deletion quoting it: the deleting revision, and which operation
    /// and item of its document hold the quote.
    pub deletes: Vec<(RevisionId, usize, usize)>,
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
    let order = graph.order.clone();
    let mut tree = Tree::default();
    for event in &order {
        tree.replay(&graph, *event)?;
    }
    Ok(tree
        .order()
        .into_iter()
        .map(|at| {
            let element = &tree.elements[at];
            Quoted {
                written_by: graph.events[element.author].revision,
                write: element.wrote,
                deletes: element
                    .deleted_by
                    .iter()
                    .filter_map(|(event, quote)| {
                        // A resolution drops an item by not keeping it, and a
                        // removal that quotes nothing is nothing to redact.
                        let (operation, item) = (*quote)?;
                        Some((graph.events[*event].revision, operation, item))
                    })
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
    let mut tree = Tree::default();
    for event in order {
        tree.replay(graph, *event)?;
    }
    Ok(tree.read(graph))
}

/// The event graph, indexed and causally ordered.
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

        // Kahn's algorithm, taking the lowest digest among the events whose
        // parents are all placed. Sorting the events by digest above makes
        // "lowest index" mean "lowest digest".
        let mut remaining: Vec<usize> = parents.iter().map(Vec::len).collect();
        let mut children: Vec<Vec<usize>> = vec![Vec::new(); events.len()];
        for (child, of) in parents.iter().enumerate() {
            for parent in of {
                children[*parent].push(child);
            }
        }
        let mut ready: BTreeSet<usize> = remaining
            .iter()
            .enumerate()
            .filter(|(_, count)| **count == 0)
            .map(|(index, _)| index)
            .collect();

        let mut order = Vec::with_capacity(events.len());
        while let Some(next) = ready.iter().next().copied() {
            ready.remove(&next);
            order.push(next);
            for child in &children[next] {
                remaining[*child] -= 1;
                if remaining[*child] == 0 {
                    ready.insert(*child);
                }
            }
        }
        if order.len() != events.len() {
            return Err(MergeError::Cycle);
        }

        Ok(Self {
            events,
            ancestry: Ancestry::new(&order, &parents),
            order,
        })
    }

    /// Whether this graph is one chain, so nothing in it is concurrent.
    fn chain(&self) -> bool {
        matches!(self.ancestry, Ancestry::Chain { .. })
    }

    /// Whether neither of these two events had seen the other.
    fn concurrent(&self, one: usize, other: usize) -> bool {
        one != other && !self.ancestry.knows(one, other) && !self.ancestry.knows(other, one)
    }

    /// Whether the author of `event` had seen `other`, or is `other`.
    ///
    /// The view an insertion is placed against: an element written earlier by
    /// this same revision is one its author can see, because they wrote it.
    fn knows(&self, event: usize, other: usize) -> bool {
        self.ancestry.knows(event, other)
    }

    /// Whether `other` is strictly in `event`'s past.
    ///
    /// The view an operation's positions are counted into: what the author had
    /// before they started, which is their parents' state and nothing of their
    /// own.
    fn saw(&self, event: usize, other: usize) -> bool {
        self.ancestry.saw(event, other)
    }
}

/// Which side of its parent an element sits on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Side {
    Left,
    Right,
}

/// One item in the transient structure, alive or tombstoned.
///
/// Which element it was attached to, and on which side, is not a field: it is
/// recorded by the child list it was put into, and the in-order reading of
/// those lists is the file.
#[derive(Debug, Clone)]
struct Element {
    /// `(R, i)`: the revision that wrote it, and its index within that
    /// revision. Derived, never stored, and unique because a digest is.
    id: (RevisionId, usize),
    /// The name a `keep` line quotes: the *document* that minted the item, and
    /// the item's ordinal in that document's order.
    ///
    /// Decision 0032 counts references this way because a person reading a
    /// resolution has the `edit` line in front of them, not the revision's
    /// digest. It is coarser than `id` by exactly one case — two concurrent
    /// revisions naming one byte-identical document — where the two items it
    /// cannot tell apart hold the same text, so nothing a reference decides
    /// depends on which is taken.
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
    /// redaction to chase.
    deleted_by: BTreeMap<usize, Option<(usize, usize)>>,
    left: Vec<usize>,
    right: Vec<usize>,
}

#[derive(Debug, Default)]
struct Tree {
    elements: Vec<Element>,
    /// The document's top level: the root's right children.
    root: Vec<usize>,
}

impl Tree {
    /// Every element, in the order the document reads.
    ///
    /// Iterative because a file typed from beginning to end is a chain of
    /// right children as deep as the file is long.
    fn order(&self) -> Vec<usize> {
        enum Work {
            Expand(usize),
            Emit(usize),
        }
        let mut out = Vec::with_capacity(self.elements.len());
        let mut stack: Vec<Work> = self.root.iter().rev().map(|at| Work::Expand(*at)).collect();
        while let Some(work) = stack.pop() {
            match work {
                Work::Expand(at) => {
                    let element = &self.elements[at];
                    for child in element.right.iter().rev() {
                        stack.push(Work::Expand(*child));
                    }
                    stack.push(Work::Emit(at));
                    for child in element.left.iter().rev() {
                        stack.push(Work::Expand(*child));
                    }
                }
                Work::Emit(at) => out.push(at),
            }
        }
        out
    }

    /// The elements one event's author could see, in order.
    fn visible(&self, order: &[usize], graph: &Graph<'_>, event: usize) -> Vec<usize> {
        order
            .iter()
            .copied()
            .filter(|at| {
                let element = &self.elements[*at];
                graph.saw(event, element.author)
                    && !element.deleted_by.keys().any(|by| graph.saw(event, *by))
            })
            .collect()
    }

    fn replay(&mut self, graph: &Graph<'_>, event: usize) -> Result<(), MergeError> {
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

    /// Decision 0032's resolution, crossed.
    ///
    /// The resolution is the recorded truth of this file at this revision, so
    /// the walk takes it as stated rather than deriving anything: an item the
    /// resolution does not keep is dead here, exactly as a delete; the items
    /// it inserts are its own; and the items it keeps survive **under their
    /// own names**, which is what lets a concurrent branch's edits to those
    /// same items merge normally instead of colliding with copies.
    fn resolution(
        &mut self,
        graph: &Graph<'_>,
        event: usize,
        named: RevisionId,
        document: &ResolutionDocument,
    ) -> Result<(), MergeError> {
        let revision = graph.events[event].revision;
        let order = self.order();
        // The same view an operation document's positions are counted into:
        // what this author had before they started.
        let prepare = self.visible(&order, graph, event);

        // Where each name the author could see sits in that view. The first
        // wins where two elements share a name, which is the byte-identical
        // case `Element::reference` describes.
        let mut by_reference: BTreeMap<(RevisionId, usize), usize> = BTreeMap::new();
        for (position, at) in prepare.iter().enumerate() {
            by_reference
                .entry(self.elements[*at].reference)
                .or_insert(position);
        }

        let mut kept: BTreeSet<usize> = BTreeSet::new();
        // The element the next piece follows, which is what anchors an insert.
        let mut left: Option<usize> = None;
        let mut minted = 0usize;
        for (index, piece) in document.pieces.iter().enumerate() {
            match piece {
                Piece::Keep {
                    document: from,
                    first,
                    count,
                } => {
                    for offset in 0..*count {
                        let name = (*from, first + offset);
                        let Some(position) = by_reference.get(&name).copied() else {
                            return Err(MergeError::UnknownReference {
                                revision,
                                document: *from,
                                item: first + offset,
                            });
                        };
                        kept.insert(position);
                        left = Some(prepare[position]);
                    }
                }
                Piece::Insert { items } => {
                    for (offset, item) in items.iter().enumerate() {
                        let (parent, side) = self.anchor(left, graph, event);
                        left = Some(self.attach(
                            (revision, minted),
                            (named, minted),
                            item.clone(),
                            event,
                            (index, offset),
                            parent,
                            side,
                        ));
                        minted += 1;
                    }
                }
            }
        }

        // Everything the author could see and the resolution did not keep.
        // Recorded as a removal that quotes nothing, because a resolution
        // states what survives rather than what went.
        for (position, at) in prepare.iter().enumerate() {
            if !kept.contains(&position) {
                self.elements[*at].deleted_by.insert(event, None);
            }
        }
        Ok(())
    }

    fn operations(
        &mut self,
        graph: &Graph<'_>,
        event: usize,
        named: RevisionId,
        document: &OperationDocument,
    ) -> Result<(), MergeError> {
        let revision = graph.events[event].revision;
        let order = self.order();
        // Every operation of one revision is stated against the state at its
        // parents, so this view is computed once and never moves under them.
        let prepare = self.visible(&order, graph, event);
        // How many items this document has minted so far, which is the ordinal
        // half of the name decision 0032 lets a `keep` quote.
        let mut minted = 0usize;

        for (index, operation) in document.operations.iter().enumerate() {
            let at = operation.at;
            match operation.kind {
                OperationKind::Delete => {
                    let end = at.saturating_add(operation.items.len());
                    if end > prepare.len() {
                        return Err(MergeError::OutOfRange {
                            revision,
                            position: end,
                            length: prepare.len(),
                        });
                    }
                    for (offset, recorded) in operation.items.iter().enumerate() {
                        let target = prepare[at + offset];
                        let found = &self.elements[target].item;
                        // A forgotten item on either side matches, per
                        // decision 0014: the redundancy its text paid for is
                        // exactly what was destroyed.
                        if !recorded.matches(found) {
                            return Err(MergeError::ItemDisagrees {
                                revision,
                                position: at + offset,
                                recorded: recorded.text.clone(),
                                found: found.text.clone(),
                            });
                        }
                        self.elements[target]
                            .deleted_by
                            .insert(event, Some((index, offset)));
                    }
                }
                OperationKind::Insert => {
                    if at > prepare.len() {
                        return Err(MergeError::OutOfRange {
                            revision,
                            position: at,
                            length: prepare.len(),
                        });
                    }
                    let mut left = at.checked_sub(1).map(|before| prepare[before]);
                    for (offset, item) in operation.items.iter().enumerate() {
                        let (parent, side) = self.anchor(left, graph, event);
                        left = Some(self.attach(
                            (revision, index + offset),
                            (named, minted),
                            item.clone(),
                            event,
                            (index, offset),
                            parent,
                            side,
                        ));
                        minted += 1;
                    }
                }
            }
        }
        Ok(())
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
    /// is what entitles [`Tree::attach`] to break sibling ties by digest.
    fn anchor(
        &self,
        left: Option<usize>,
        graph: &Graph<'_>,
        event: usize,
    ) -> (Option<usize>, Side) {
        let known = |children: &[usize]| {
            children
                .iter()
                .copied()
                .find(|child| graph.knows(event, self.elements[*child].author))
        };
        let children = match left {
            Some(at) => &self.elements[at].right,
            None => &self.root,
        };
        let Some(mut at) = known(children) else {
            return (left, Side::Right);
        };
        while let Some(next) = known(&self.elements[at].left) {
            at = next;
        }
        (Some(at), Side::Left)
    }

    /// Put an element into the tree, among its siblings in name order.
    #[allow(clippy::too_many_arguments)]
    fn attach(
        &mut self,
        id: (RevisionId, usize),
        reference: (RevisionId, usize),
        item: Item,
        author: usize,
        wrote: (usize, usize),
        parent: Option<usize>,
        side: Side,
    ) -> usize {
        let at = self.elements.len();
        self.elements.push(Element {
            id,
            reference,
            item,
            author,
            wrote,
            deleted_by: BTreeMap::new(),
            left: Vec::new(),
            right: Vec::new(),
        });

        let siblings = match (parent, side) {
            (None, _) => &mut self.root,
            (Some(parent), Side::Left) => &mut self.elements[parent].left,
            (Some(parent), Side::Right) => &mut self.elements[parent].right,
        };
        let siblings = std::mem::take(siblings);
        let mut placed = siblings;
        // Ties between concurrent elements are broken by digest, then by
        // index, which is the name each of them already has.
        let position = placed
            .iter()
            .position(|other| self.elements[*other].id > id)
            .unwrap_or(placed.len());
        placed.insert(position, at);

        let restored = match (parent, side) {
            (None, _) => &mut self.root,
            (Some(parent), Side::Left) => &mut self.elements[parent].left,
            (Some(parent), Side::Right) => &mut self.elements[parent].right,
        };
        *restored = placed;
        at
    }

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
                for by in element.deleted_by.keys() {
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
            pending.extend(element.deleted_by.keys().copied());
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
        for at in self.order() {
            let element = &self.elements[at];
            if !element.deleted_by.is_empty() {
                continue;
            }
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
    /// — or minted and something already removed.
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
