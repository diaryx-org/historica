//! The conformance suite decision 0007 owes.
//!
//! Historica's merge is an event-graph replay: operations and causal edges
//! are stored, and the structure that resolves concurrency is built during a
//! walk and thrown away. The reference here is the other architecture — the
//! one a live CRDT actually runs. Each replica holds a Fugue tree; an insert
//! computes its parent and side **at the source**, from what that replica
//! knows; messages carry placement, not positions; delivery is causal and
//! placement-order-independent.
//!
//! The two share four lines of specification — Fugue's anchoring rule, and
//! ties by digest then index — and nothing else: no event graph, no
//! visibility filtering, no replay. Every history both can express must
//! merge to the same bytes, and the properties below hold them to it, along
//! with the guarantee 0007 chose Fugue for: two concurrently written
//! paragraphs never interleave.
//!
//! The simulated edits are item-shaped rather than text-shaped, and produce
//! the content a line-based model has to answer for: empty lines, lines
//! carrying a carriage return, and files that end without a terminator. The
//! last of those is what lets the search reach the one file shape no single
//! history can state — an item that is neither terminated nor last — which
//! decision 0007 left open and `historica::merge` reports rather than
//! resolves.

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};

use historica::core::RevisionId;
use historica::diff::{diff, resolve};
use historica::format::{
    Item, OperationDocument, OperationKind, Piece, ResolutionDocument, digest,
};
use historica::merge::{Contest, Event, Merged, merge};
use historica::replay::State;

/// The name an element already has: decision 0007's `(R, i)`, and beneath it
/// the operation and offset that spell `i`, which only make a tie between one
/// revision's own elements total.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Key {
    revision: RevisionId,
    index: usize,
    operation: usize,
    offset: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Side {
    Left,
    Right,
}

/// What travels between replicas. Placement is computed once, at the source,
/// which is what makes applying it the same everywhere.
#[derive(Debug, Clone)]
enum Message {
    Insert {
        key: Key,
        /// The name decision 0032 lets a `keep` quote: the document that
        /// minted the item, and its ordinal in that document's order. It
        /// travels with the placement because a resolution arriving later
        /// refers to items by it.
        reference: (RevisionId, usize),
        item: Item,
        parent: Option<Key>,
        side: Side,
    },
    Delete {
        key: Key,
    },
}

#[derive(Debug, Clone)]
struct Node {
    key: Option<Key>,
    item: Option<Item>,
    deleted: bool,
    left: Vec<usize>,
    right: Vec<usize>,
}

/// One replica of the reference CRDT. Node 0 is the root, which is nobody.
#[derive(Debug, Clone)]
struct Replica {
    nodes: Vec<Node>,
    by_key: BTreeMap<Key, usize>,
    by_reference: BTreeMap<(RevisionId, usize), usize>,
}

const ROOT: usize = 0;

impl Replica {
    fn new() -> Self {
        Self {
            nodes: vec![Node {
                key: None,
                item: None,
                deleted: false,
                left: Vec::new(),
                right: Vec::new(),
            }],
            by_key: BTreeMap::new(),
            by_reference: BTreeMap::new(),
        }
    }

    /// Every node, in the order the document reads. Iterative, as the merge's
    /// own traversal is, and for the same reason.
    fn order(&self) -> Vec<usize> {
        enum Work {
            Expand(usize),
            Emit(usize),
        }
        let mut out = Vec::new();
        let mut stack = vec![Work::Expand(ROOT)];
        while let Some(work) = stack.pop() {
            match work {
                Work::Expand(at) => {
                    let node = &self.nodes[at];
                    for child in node.right.iter().rev() {
                        stack.push(Work::Expand(*child));
                    }
                    if at != ROOT {
                        stack.push(Work::Emit(at));
                    }
                    for child in node.left.iter().rev() {
                        stack.push(Work::Expand(*child));
                    }
                }
                Work::Emit(at) => out.push(at),
            }
        }
        out
    }

    fn visible(&self) -> Vec<usize> {
        self.order()
            .into_iter()
            .filter(|at| !self.nodes[*at].deleted)
            .collect()
    }

    fn text(&self) -> String {
        let mut out = String::new();
        for at in self.visible() {
            let item = self.nodes[at].item.as_ref().expect("a non-root node");
            out.push_str(item.shown());
            if item.terminated {
                out.push('\n');
            }
        }
        out
    }

    /// The file this replica holds, as items.
    ///
    /// Not the same thing as reading [`Replica::text`] back with
    /// [`State::from_text`], and that is the point: once a merge has left an
    /// item that is neither terminated nor last, the bytes join it to the
    /// line after it and the boundary is gone. An edit is derived against
    /// what the replica holds, so this is what it is derived against.
    fn state(&self) -> State {
        State::from_items(
            self.visible()
                .into_iter()
                .map(|at| self.nodes[at].item.clone().expect("a non-root node")),
        )
    }

    /// Apply one message. Idempotent, and order-independent under causal
    /// delivery, because placement was already decided.
    fn apply(&mut self, message: &Message) {
        match message {
            Message::Insert {
                key,
                reference,
                item,
                parent,
                side,
            } => {
                if self.by_key.contains_key(key) {
                    return;
                }
                let at = self.nodes.len();
                self.nodes.push(Node {
                    key: Some(*key),
                    item: Some(item.clone()),
                    deleted: false,
                    left: Vec::new(),
                    right: Vec::new(),
                });
                self.by_key.insert(*key, at);
                self.by_reference.entry(*reference).or_insert(at);
                let parent = parent.map_or(ROOT, |key| self.by_key[&key]);
                let siblings = match side {
                    Side::Left => &mut self.nodes[parent].left,
                    Side::Right => &mut self.nodes[parent].right,
                };
                let siblings = std::mem::take(siblings);
                let mut placed = siblings;
                let position = placed
                    .iter()
                    .position(|other| self.nodes[*other].key > Some(*key))
                    .unwrap_or(placed.len());
                placed.insert(position, at);
                let restored = match side {
                    Side::Left => &mut self.nodes[parent].left,
                    Side::Right => &mut self.nodes[parent].right,
                };
                *restored = placed;
            }
            Message::Delete { key } => {
                let at = self.by_key[key];
                self.nodes[at].deleted = true;
            }
        }
    }

    /// Fugue's anchoring rule, at the source: attach to the left neighbour
    /// when it has nothing to its right yet, and otherwise as a left child of
    /// the node that follows the left neighbour in the traversal — tombstones
    /// included, which is the leftmost node under its first right child.
    fn anchor(&self, left: Option<usize>) -> (Option<usize>, Side) {
        let children = match left {
            Some(left) => &self.nodes[left].right,
            None => &self.nodes[ROOT].right,
        };
        let Some(&first) = children.first() else {
            return (left, Side::Right);
        };
        let mut at = first;
        while let Some(&next) = self.nodes[at].left.first() {
            at = next;
        }
        (Some(at), Side::Left)
    }

    /// Turn one revision's document into messages, applying each locally as
    /// it is derived — the source replica *is* the author's view.
    fn derive(&mut self, revision: RevisionId, document: &OperationDocument) -> Vec<Message> {
        // Positions are stated against the state at the parents and never
        // move, so the view is captured once, before anything is applied.
        let prepare = self.visible();
        let named = digest(&document.write());
        let mut minted = 0usize;
        let mut messages = Vec::new();
        for (index, operation) in document.operations.iter().enumerate() {
            match operation.kind {
                OperationKind::Delete => {
                    for (offset, recorded) in operation.items.iter().enumerate() {
                        let target = prepare[operation.at + offset];
                        let held = self.nodes[target].item.as_ref().expect("a non-root node");
                        assert_eq!(
                            recorded.text, held.text,
                            "the harness derived a delete against the wrong state"
                        );
                        let message = Message::Delete {
                            key: self.nodes[target].key.expect("a non-root node"),
                        };
                        self.apply(&message);
                        messages.push(message);
                    }
                }
                OperationKind::Insert => {
                    let mut left = operation.at.checked_sub(1).map(|before| prepare[before]);
                    for (offset, item) in operation.items.iter().enumerate() {
                        let (parent, side) = self.anchor(left);
                        let key = Key {
                            revision,
                            index: index + offset,
                            operation: index,
                            offset,
                        };
                        let message = Message::Insert {
                            key,
                            reference: (named, minted),
                            item: item.clone(),
                            parent: parent.and_then(|node| self.nodes[node].key),
                            side,
                        };
                        self.apply(&message);
                        messages.push(message);
                        minted += 1;
                        left = Some(self.by_key[&key]);
                    }
                }
            }
        }
        messages
    }

    /// Turn one merge's resolution into messages, the same way: at the source,
    /// from what this replica knows.
    ///
    /// Decision 0032 in the live architecture. A resolution states the file
    /// whole, so what travels is what that costs the tree — a delete for
    /// every visible item it does not keep, and an insert for every item it
    /// mints, anchored after the piece before it. Nothing is restated, so a
    /// kept item's node is untouched and keeps its identity.
    fn derive_resolution(
        &mut self,
        revision: RevisionId,
        named: RevisionId,
        resolution: &ResolutionDocument,
    ) -> Vec<Message> {
        let prepare = self.visible();
        let mut kept: BTreeSet<usize> = BTreeSet::new();
        let mut left: Option<usize> = None;
        let mut minted = 0usize;
        let mut messages = Vec::new();

        for (index, piece) in resolution.pieces.iter().enumerate() {
            match piece {
                Piece::Keep {
                    document,
                    first,
                    count,
                } => {
                    for offset in 0..*count {
                        let at = *self
                            .by_reference
                            .get(&(*document, first + offset))
                            .expect("a keep of an item this replica has seen");
                        kept.insert(at);
                        left = Some(at);
                    }
                }
                Piece::Insert { items } => {
                    for (offset, item) in items.iter().enumerate() {
                        let (parent, side) = self.anchor(left);
                        let key = Key {
                            revision,
                            index: minted,
                            operation: index,
                            offset,
                        };
                        let message = Message::Insert {
                            key,
                            reference: (named, minted),
                            item: item.clone(),
                            parent: parent.and_then(|node| self.nodes[node].key),
                            side,
                        };
                        self.apply(&message);
                        messages.push(message);
                        minted += 1;
                        left = Some(self.by_key[&key]);
                    }
                }
            }
        }

        for at in prepare {
            if kept.contains(&at) {
                continue;
            }
            let message = Message::Delete {
                key: self.nodes[at].key.expect("a non-root node"),
            };
            self.apply(&message);
            messages.push(message);
        }
        messages
    }
}

/// The generator `src/merge.rs` uses, again: deterministic, so a surprising
/// round can be looked at twice.
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

/// One line, the way a person's file actually holds one.
///
/// Ordinary text most of the time. The other two are the shapes the first
/// version of this generator could not produce: an empty line, and a line
/// whose text ends in a carriage return — a file written on the other kind of
/// machine, whose `\r` decision 0007's item keeps rather than strips.
fn line(rng: &mut Rng, verb: &str, salt: usize) -> String {
    match rng.below(8) {
        0 => String::new(),
        1 => format!("{verb} {salt}-{}\r", rng.below(100)),
        _ => format!("{verb} {salt}-{}", rng.below(100)),
    }
}

/// Edit a file the way a person does, and record what that did.
///
/// Items rather than text, because the two stop agreeing once a merge has
/// run: a merged file may hold an item that is neither terminated nor last,
/// and reading those bytes back joins it to the line after it. What the
/// replica holds is what an edit is derived against.
///
/// What comes out is always a file a person could have left behind — every
/// item terminated but the last, which is the rule [`State::applied`] holds a
/// recorded document to. Only concurrency may break it, which is exactly why
/// the generator producing files that *end* without a terminator is what
/// reaches the case where something does.
fn edit(rng: &mut Rng, before: &State, salt: usize) -> (State, Option<OperationDocument>) {
    let mut items: Vec<Item> = before.items().to_vec();
    for _ in 0..1 + rng.below(3) {
        match rng.below(3) {
            0 if !items.is_empty() => {
                let at = rng.below(items.len());
                items.remove(at);
            }
            1 if !items.is_empty() => {
                let at = rng.below(items.len());
                items[at] = Item::line(line(rng, "edited", salt));
            }
            _ => {
                let at = rng.below(items.len() + 1);
                for offset in 0..1 + rng.below(3) {
                    items.insert(at + offset, Item::line(line(rng, "written", salt)));
                }
            }
        }
    }
    // Every line but the last carries its terminator, and the last one
    // sometimes does not — a person adding or taking away the trailing
    // newline, which is an ordinary thing to do and an item-shaped change.
    // An empty last line is never unterminated: there would be no bytes left
    // to say that it was, and `State::from_text` cannot produce it either.
    let last = items.len().saturating_sub(1);
    for item in items.iter_mut().take(last) {
        item.terminated = true;
    }
    if let Some(item) = items.last_mut() {
        item.terminated = item.text.is_empty() || rng.below(4) != 0;
    }
    let after = State::from_items(items);
    let document = diff(before, &after);
    (after, document)
}

/// Which of the two content grammars one event stated its file in.
#[derive(Debug, Clone, Copy)]
enum At {
    Operations(usize),
    Resolution(usize),
}

/// The shapes only concurrency can produce, counted while the suite runs.
///
/// The generator was widened to reach them; counting says whether it still
/// does. A later change to the generator that stops producing files ending
/// without a terminator would leave every assertion below passing and quietly
/// stop exercising the branch, which is the failure this catches.
#[derive(Debug, Clone, Copy, Default)]
struct Reached {
    /// Merges reporting [`Contest::Terminator`].
    terminator_contests: usize,
    /// Merged files holding an unterminated item that is not the last.
    unterminated_not_last: usize,
}

/// A whole simulation: several replicas, one shared history, two machines.
struct Sim {
    documents: Vec<OperationDocument>,
    resolutions: Vec<ResolutionDocument>,
    /// `(revision, parents, document, messages)`, in creation order — which
    /// is a causal order, since a parent exists before its child.
    events: Vec<(RevisionId, Vec<RevisionId>, At, Vec<Message>)>,
    replicas: Vec<Replica>,
    known: Vec<BTreeSet<usize>>,
    minted: usize,
    /// Counted through a `Cell` so that asserting agreement stays a read.
    reached: Cell<Reached>,
}

impl Sim {
    fn new(replicas: usize) -> Self {
        Self {
            documents: Vec::new(),
            resolutions: Vec::new(),
            events: Vec::new(),
            replicas: (0..replicas).map(|_| Replica::new()).collect(),
            known: vec![BTreeSet::new(); replicas],
            minted: 0,
            reached: Cell::default(),
        }
    }

    fn mint(&mut self) -> RevisionId {
        self.minted += 1;
        digest(format!("revision {}", self.minted).as_bytes())
    }

    /// The heads of what one replica knows: its next revision's parents.
    fn heads(&self, replica: usize) -> Vec<RevisionId> {
        let known = &self.known[replica];
        let parents: BTreeSet<RevisionId> = known
            .iter()
            .flat_map(|at| self.events[*at].1.iter().copied())
            .collect();
        known
            .iter()
            .map(|at| self.events[*at].0)
            .filter(|revision| !parents.contains(revision))
            .collect()
    }

    /// The historica side of one replica's view: the event-graph merge.
    fn events(&self, replica: usize) -> Vec<Event<'_>> {
        self.known[replica]
            .iter()
            .map(|at| {
                let (revision, parents, stated, _) = &self.events[*at];
                match stated {
                    At::Operations(at) => {
                        let document = &self.documents[*at];
                        Event::operations(
                            *revision,
                            parents.clone(),
                            digest(&document.write()),
                            document,
                        )
                    }
                    At::Resolution(at) => {
                        let document = &self.resolutions[*at];
                        Event::resolution(
                            *revision,
                            parents.clone(),
                            digest(&document.write()),
                            document,
                        )
                    }
                }
            })
            .collect()
    }

    /// The historica side of one replica's view: the event-graph merge.
    fn proposal(&self, replica: usize) -> Option<Merged> {
        let events = self.events(replica);
        if events.is_empty() {
            return None;
        }
        Some(merge(events).expect("a history that merges"))
    }

    /// One replica records one revision holding `document`.
    fn record(&mut self, replica: usize, document: OperationDocument) {
        let revision = self.mint();
        let parents = self.heads(replica);
        let messages = self.replicas[replica].derive(revision, &document);
        self.documents.push(document);
        let at = At::Operations(self.documents.len() - 1);
        self.events.push((revision, parents, at, messages));
        self.known[replica].insert(self.events.len() - 1);
    }

    /// One replica reads both sides and records what the file is.
    ///
    /// Decision 0032's merge, on both architectures at once: the resolution
    /// is written from what the event-graph side proposes, and derived into
    /// messages from what the live tree holds. Nothing forces the two to name
    /// the same items, which is exactly the claim being tested.
    fn merge(&mut self, rng: &mut Rng, replica: usize, salt: usize) -> bool {
        let parents = self.heads(replica);
        if parents.len() < 2 {
            return false;
        }
        let proposed = self.proposal(replica).expect("a history that merges");
        let (after, _) = edit(rng, &proposed.state, salt);
        let Some(resolution) = resolve(&proposed.state, &proposed.references, &after) else {
            return false;
        };

        let revision = self.mint();
        let named = digest(&resolution.write());
        let messages = self.replicas[replica].derive_resolution(revision, named, &resolution);
        self.resolutions.push(resolution);
        let at = At::Resolution(self.resolutions.len() - 1);
        self.events.push((revision, parents, at, messages));
        self.known[replica].insert(self.events.len() - 1);
        true
    }

    /// One replica edits what it currently sees, at random.
    fn edit(&mut self, rng: &mut Rng, replica: usize, salt: usize) {
        let before = self.replicas[replica].state();
        let (_, document) = edit(rng, &before, salt);
        if let Some(document) = document {
            self.record(replica, document);
        }
    }

    /// Deliver everything `from` knows to `into`, causally: creation order.
    fn sync(&mut self, into: usize, from: usize) {
        let arriving: Vec<usize> = self.known[from]
            .difference(&self.known[into])
            .copied()
            .collect();
        for at in arriving {
            let messages = self.events[at].3.clone();
            for message in &messages {
                self.replicas[into].apply(message);
            }
            self.known[into].insert(at);
        }
    }

    /// The claim under test: both architectures read one file.
    fn agree(&self, replica: usize, round: usize) {
        let proposal = self.proposal(replica);
        if let Some(merged) = &proposal {
            self.note(merged);
        }
        let merged = proposal.map_or_else(String::new, |merged| merged.state.text());
        assert_eq!(
            self.replicas[replica].text(),
            merged,
            "round {round}: replica {replica} disagrees with the event-graph replay"
        );
    }

    /// Record which of the widened generator's targets this merge reached.
    fn note(&self, merged: &Merged) {
        let mut reached = self.reached.get();
        if merged
            .contested
            .iter()
            .any(|contest| contest.kind == Contest::Terminator)
        {
            reached.terminator_contests += 1;
        }
        let items = merged.state.items();
        if items
            .iter()
            .take(items.len().saturating_sub(1))
            .any(|item| !item.terminated)
        {
            reached.unterminated_not_last += 1;
        }
        self.reached.set(reached);
    }
}

#[test]
fn the_event_graph_replay_conforms_to_the_reference_crdt() {
    // Random replicas, random edits, random partial syncs — and after every
    // single step, the transient event-graph replay must read the same file
    // the live tree has been maintaining all along.
    let mut rng = Rng(0x0007_c04f_0000_f00d);
    let mut reached = Reached::default();
    for round in 0..150 {
        let replicas = 2 + rng.below(2);
        let mut sim = Sim::new(replicas);

        // A shared root, so concurrent edits have something to disagree on —
        // sometimes holding an empty line, and sometimes ending without a
        // terminator, since a file that arrives that way is one people have.
        let mut items: Vec<Item> = ["alpha", "beta", "gamma", "delta"]
            .into_iter()
            .map(Item::line)
            .collect();
        if rng.below(3) == 0 {
            items.insert(1 + rng.below(3), Item::line(""));
        }
        if rng.below(3) == 0 {
            items.last_mut().expect("a root with lines").terminated = false;
        }
        let root = diff(&State::empty(), &State::from_items(items)).expect("a root document");
        sim.record(0, root);
        for replica in 1..replicas {
            sim.sync(replica, 0);
        }

        for action in 0..12 {
            match rng.below(4) {
                0 | 1 => {
                    let replica = rng.below(replicas);
                    sim.edit(&mut rng, replica, action);
                    sim.agree(replica, round);
                }
                // Decision 0032: a replica holding two heads reads both sides
                // and records what the file is. The history then holds a
                // resolution, and everything downstream of it — every later
                // edit, every later merge, every partial sync — is walked
                // across one.
                2 => {
                    // Whichever replica is holding two heads, since a merge
                    // is not something a replica can do on request.
                    let first = rng.below(replicas);
                    for offset in 0..replicas {
                        let replica = (first + offset) % replicas;
                        if sim.merge(&mut rng, replica, action) {
                            sim.agree(replica, round);
                            break;
                        }
                    }
                }
                _ => {
                    let into = rng.below(replicas);
                    let from = rng.below(replicas);
                    if into != from {
                        sim.sync(into, from);
                        sim.agree(into, round);
                    }
                }
            }
        }

        // Full sync: everyone reads one file, in both architectures.
        for into in 0..replicas {
            for from in 0..replicas {
                if into != from {
                    sim.sync(into, from);
                }
            }
        }
        let first = sim.replicas[0].text();
        for replica in 0..replicas {
            sim.agree(replica, round);
            assert_eq!(
                sim.replicas[replica].text(),
                first,
                "round {round}: the reference replicas did not converge"
            );
        }

        let round = sim.reached.get();
        reached.terminator_contests += round.terminator_contests;
        reached.unterminated_not_last += round.unterminated_not_last;
    }

    // The generator is widened to reach these, and a suite that stops
    // reaching them fails rather than passing quietly on a narrower search.
    assert!(
        reached.unterminated_not_last > 0,
        "no round produced a merged file whose unterminated item was not last: {reached:?}"
    );
    assert!(
        reached.terminator_contests > 0,
        "no round reported a contested terminator: {reached:?}"
    );
}

/// One document from the lines below the separator, as the merge tests do.
fn document(lines: &[&str]) -> OperationDocument {
    let mut text = format!("{}\n\n", historica::format::PREAMBLE);
    for line in lines {
        text.push_str(line);
        text.push('\n');
    }
    OperationDocument::parse(text.as_bytes()).expect("a document that parses")
}

/// A root event and the named events after it, merged to a file.
fn merged(root: &OperationDocument, events: &[(String, Vec<String>, OperationDocument)]) -> String {
    merge(
        std::iter::once(Event::operations(
            digest(b"root"),
            Vec::new(),
            digest(&root.write()),
            root,
        ))
        .chain(events.iter().map(|(name, parents, operations)| {
            Event::operations(
                digest(name.as_bytes()),
                parents.iter().map(|name| digest(name.as_bytes())).collect(),
                digest(&operations.write()),
                operations,
            )
        })),
    )
    .expect("a history that merges")
    .state
    .text()
}

/// Whether every line of `run` appears in `text` as one contiguous block.
fn contiguous(text: &str, run: &[&str]) -> bool {
    let mut joined = String::new();
    for line in run {
        joined.push_str(line);
        joined.push('\n');
    }
    text.contains(&joined)
}

#[test]
fn concurrent_paragraphs_do_not_interleave_however_many_hands_write_them() {
    // The property 0007 chose Fugue over the reference implementation's own
    // Yjs-style rule for. Several replicas each write a paragraph at one
    // position, line by line, across several revisions — the shape a person
    // typing actually produces — and each paragraph must come out whole.
    let mut rng = Rng(0x1e_af_1e_55);
    for round in 0..100 {
        let replicas = 2 + rng.below(2);
        let root = document(&["insert 0", "+a", "+b"]);
        let mut events: Vec<(String, Vec<String>, OperationDocument)> = Vec::new();
        let mut runs: Vec<Vec<String>> = Vec::new();

        for replica in 0..replicas {
            // Each replica types its paragraph at position 1, one line per
            // revision, forward — each line after the one before it.
            let lines = 2 + rng.below(3);
            let mut run = Vec::new();
            let mut parent = "root".to_owned();
            for line in 0..lines {
                let written = format!("r{replica} line {line}");
                let at = 1 + line;
                let name = format!("replica {replica} revision {line}");
                events.push((
                    name.clone(),
                    vec![parent.clone()],
                    document(&[&format!("insert {at}"), &format!("+{written}")]),
                ));
                run.push(written);
                parent = name;
            }
            runs.push(run);
        }

        let text = merged(&root, &events);
        assert!(text.starts_with("a\n"), "round {round}: {text}");
        assert!(text.ends_with("b\n"), "round {round}: {text}");
        for (replica, run) in runs.iter().enumerate() {
            let run: Vec<&str> = run.iter().map(String::as_str).collect();
            assert!(
                contiguous(&text, &run),
                "round {round}: replica {replica}'s paragraph interleaved:\n{text}"
            );
        }
    }
}

#[test]
fn paragraphs_typed_backwards_do_not_interleave_either() {
    // Each line inserted before the one written a moment ago: the case a
    // naive rule breaks, pinned here beyond the two-replica test the merge
    // module already carries.
    let root = document(&["insert 0", "+a", "+b"]);
    let mut events: Vec<(String, Vec<String>, OperationDocument)> = Vec::new();
    for replica in 0..3 {
        let mut parent = "root".to_owned();
        for line in 0..3 {
            let name = format!("replica {replica} revision {line}");
            events.push((
                name.clone(),
                vec![parent.clone()],
                document(&["insert 1", &format!("+r{replica} line {}", 2 - line)]),
            ));
            parent = name;
        }
    }
    let text = merged(&root, &events);

    for replica in 0..3 {
        let run: Vec<String> = (0..3)
            .map(|line| format!("r{replica} line {line}"))
            .collect();
        let run: Vec<&str> = run.iter().map(String::as_str).collect();
        assert!(
            contiguous(&text, &run),
            "replica {replica}'s paragraph interleaved:\n{text}"
        );
    }
}

#[test]
fn a_terminator_two_concurrent_files_disagree_about_is_reported() {
    // The shape a chain cannot produce and `crate::replay` refuses a document
    // for producing: an item that is neither terminated nor last. One replica
    // takes the file's trailing newline away; the other, not having seen
    // that, appends past the line it was on. Neither file is malformed and
    // the merge of them holds an item that is, which is decision 0007's third
    // open question arriving the only way it can.
    //
    // Pinned here rather than left to the search above, so that the branch
    // stays covered whatever the generator is later tuned to.
    let mut sim = Sim::new(2);
    sim.record(
        0,
        diff(&State::empty(), &State::from_text("a\nb\n")).expect("a root document"),
    );
    sim.sync(1, 0);

    let unterminated = diff(
        &State::from_text("a\nb\n"),
        &State::from_items([Item::line("a"), Item::unterminated("b")]),
    )
    .expect("a document taking the terminator away");
    sim.record(0, unterminated);
    let appended = diff(&State::from_text("a\nb\n"), &State::from_text("a\nb\nc\n"))
        .expect("a document appending past it");
    sim.record(1, appended);

    sim.sync(0, 1);
    sim.sync(1, 0);
    sim.agree(0, 0);
    sim.agree(1, 0);

    let merged = sim.proposal(0).expect("a history that merges");
    let items = merged.state.items();
    let unterminated: Vec<usize> = items
        .iter()
        .enumerate()
        .filter(|(_, item)| !item.terminated)
        .map(|(position, _)| position)
        .collect();
    assert_eq!(
        unterminated,
        [1],
        "the item that was last is not last any more: {items:?}"
    );
    assert_eq!(
        merged
            .contested
            .iter()
            .filter(|contest| contest.kind == Contest::Terminator)
            .map(|contest| contest.at)
            .collect::<Vec<usize>>(),
        [1],
        "a merge that cannot give the terminator to both files must say so: {:?}",
        merged.contested
    );
    // Both architectures read the same bytes out of it, joined line and all.
    assert_eq!(sim.replicas[0].text(), "a\nbc\n");
    assert_eq!(sim.replicas[1].text(), "a\nbc\n");
}

#[test]
fn the_reference_and_the_replay_agree_at_the_end_of_a_tombstoned_file() {
    // An append where the file's last items are tombstones, so the right
    // origin is a tombstone rather than anything visible. The least
    // travelled branch in both implementations, held to agreement explicitly.
    let mut sim = Sim::new(2);
    sim.record(0, document(&["insert 0", "+a", "+b", "+c"]));
    sim.sync(1, 0);
    // Replica 0 deletes the tail; replica 1 concurrently appends past it.
    sim.record(0, document(&["delete 1 2", "-b", "-c"]));
    sim.record(1, document(&["insert 3", "+appended"]));
    sim.sync(0, 1);
    sim.sync(1, 0);
    sim.agree(0, 0);
    sim.agree(1, 0);
    assert_eq!(sim.replicas[0].text(), sim.replicas[1].text());
    assert!(sim.replicas[0].text().contains("appended\n"));
}
