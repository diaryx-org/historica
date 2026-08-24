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
//!
//! Each round is drawn as a value before it runs, from a seed the environment
//! may replace. That is what lets CI search somewhere new every run without
//! giving up on reproducing what it finds: a failure prints the seed, and the
//! failing round shrunk to the fewest replicas and actions that still produce
//! it.

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

/// One file, with the bytes that do not print made visible.
///
/// Two files differing only in whether the last line carries its terminator
/// look identical otherwise, and a carriage return looks like nothing at all
/// — which are two of the three shapes this suite searches over, so a failure
/// that shows the bytes plainly would be a failure nobody could read.
fn shown(text: &str) -> String {
    let mut out = String::new();
    for line in text.split_inclusive('\n') {
        out.push_str("    ");
        for character in line.chars() {
            match character {
                '\n' => out.push_str("\\n"),
                '\r' => out.push_str("\\r"),
                '\\' => out.push_str("\\\\"),
                other => out.push(other),
            }
        }
        out.push('\n');
    }
    if out.is_empty() {
        out.push_str("    (the file is empty)\n");
    }
    out.pop();
    out
}

/// The seed the suite searches from, when nothing says otherwise.
const SEED: u64 = 0x0007_c04f_0000_f00d;

/// The seed this run searches from.
///
/// Fixed by default, so that `cargo test` twice is `cargo test` twice, and
/// overridable through `HISTORICA_CONFORMANCE_SEED` so that CI can rotate it.
/// A suite that searches the same hundred and fifty cases forever stops
/// finding anything the day it first passes; one that searches a fresh
/// hundred and fifty every run keeps looking, and is only useful if a failure
/// says which ones it looked at. Every failure below prints the seed, and
/// putting it back in the variable brings the same case out again.
fn seed() -> u64 {
    let Ok(given) = std::env::var("HISTORICA_CONFORMANCE_SEED") else {
        return SEED;
    };
    let given = given.trim();
    let parsed = match given
        .strip_prefix("0x")
        .or_else(|| given.strip_prefix("0X"))
    {
        Some(hexadecimal) => u64::from_str_radix(hexadecimal, 16),
        None => given.parse(),
    };
    parsed.unwrap_or_else(|_| {
        panic!("HISTORICA_CONFORMANCE_SEED is not a number: {given:?}");
    })
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

    /// The claim under test, answered rather than asserted.
    ///
    /// A value, because the search below has to ask a candidate plan whether
    /// it still fails, and it cannot ask that of an assertion.
    fn checked(&self, replica: usize, step: usize) -> Result<(), String> {
        let proposal = self.proposal(replica);
        if let Some(merged) = &proposal {
            self.note(merged);
        }
        let merged = proposal.map_or_else(String::new, |merged| merged.state.text());
        let held = self.replicas[replica].text();
        if held == merged {
            return Ok(());
        }
        Err(format!(
            "at step {step}, replica {replica} disagrees with the event-graph replay\n\
             \x20 the reference tree reads:\n{}\n\
             \x20 the event-graph replay reads:\n{}",
            shown(&held),
            shown(&merged),
        ))
    }

    /// The claim under test: both architectures read one file.
    fn agree(&self, replica: usize, round: usize) {
        if let Err(failure) = self.checked(replica, round) {
            panic!("round {round}: {failure}");
        }
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

/// One thing a round does, drawn before the round runs.
///
/// A plan is a value rather than a path through a generator, which is what
/// makes a failing round shrinkable: the search below takes actions out of it
/// and asks whether it still fails. Each action carries its own seed, so
/// removing one leaves what the others do untouched — the property a
/// generator consulted inline as it goes cannot have.
#[derive(Debug, Clone, Copy)]
enum Action {
    /// One replica edits what it sees.
    Edit { replica: usize, seed: u64 },
    /// Whichever replica from `first` onwards is holding two heads reads both
    /// sides and records what the file is.
    Merge { first: usize, seed: u64 },
    /// Everything one replica knows, delivered to another.
    Sync { into: usize, from: usize },
}

impl std::fmt::Display for Action {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Action::Edit { replica, seed } => {
                write!(out, "replica {replica} edits (seed 0x{seed:016x})")
            }
            Action::Merge { first, seed } => {
                write!(out, "a merge, from replica {first} (seed 0x{seed:016x})")
            }
            Action::Sync { into, from } => write!(out, "replica {into} hears from {from}"),
        }
    }
}

/// One whole round, as a value.
#[derive(Debug, Clone)]
struct Plan {
    replicas: usize,
    /// Where the shared root holds an empty line, if it holds one.
    blank: Option<usize>,
    /// Whether the shared root's last line carries its terminator.
    terminated: bool,
    actions: Vec<Action>,
}

impl Plan {
    /// The shared root, so concurrent edits have something to disagree on —
    /// sometimes holding an empty line, and sometimes ending without a
    /// terminator, since a file that arrives that way is one people have.
    fn root(&self) -> OperationDocument {
        let mut items: Vec<Item> = ["alpha", "beta", "gamma", "delta"]
            .into_iter()
            .map(Item::line)
            .collect();
        if let Some(at) = self.blank {
            items.insert(at, Item::line(""));
        }
        if !self.terminated {
            items.last_mut().expect("a root with lines").terminated = false;
        }
        diff(&State::empty(), &State::from_items(items)).expect("a root document")
    }

    /// The same plan with one replica taken out of it, and every action that
    /// named it dropped. Only ever the last replica, so the others keep the
    /// numbers they had and every remaining action still means what it did.
    fn without(&self, gone: usize) -> Self {
        let replicas = self.replicas - 1;
        let actions = self
            .actions
            .iter()
            .filter_map(|action| match *action {
                Action::Edit { replica, .. } if replica == gone => None,
                Action::Sync { into, from } if into == gone || from == gone => None,
                Action::Merge { first, seed } => Some(Action::Merge {
                    first: first % replicas,
                    seed,
                }),
                other => Some(other),
            })
            .collect();
        Self {
            replicas,
            actions,
            ..self.clone()
        }
    }
}

/// Draw one round.
fn plan(rng: &mut Rng) -> Plan {
    let replicas = 2 + rng.below(2);
    let blank = (rng.below(3) == 0).then(|| 1 + rng.below(3));
    let terminated = rng.below(3) != 0;
    let actions = (0..12)
        .map(|_| match rng.below(4) {
            0 | 1 => Action::Edit {
                replica: rng.below(replicas),
                seed: rng.next() | 1,
            },
            2 => Action::Merge {
                first: rng.below(replicas),
                seed: rng.next() | 1,
            },
            _ => Action::Sync {
                into: rng.below(replicas),
                from: rng.below(replicas),
            },
        })
        .collect();
    Plan {
        replicas,
        blank,
        terminated,
        actions,
    }
}

/// Run one plan, and say what it reached or how it failed.
///
/// Random replicas, random edits, random partial syncs — and after every
/// single step, the transient event-graph replay must read the same file the
/// live tree has been maintaining all along.
fn run(plan: &Plan) -> Result<Reached, String> {
    let mut sim = Sim::new(plan.replicas);
    sim.record(0, plan.root());
    for replica in 1..plan.replicas {
        sim.sync(replica, 0);
    }

    for (step, action) in plan.actions.iter().enumerate() {
        match *action {
            Action::Edit { replica, seed } => {
                sim.edit(&mut Rng(seed), replica, salt(seed));
                sim.checked(replica, step)?;
            }
            // Decision 0032: a replica holding two heads reads both sides and
            // records what the file is. The history then holds a resolution,
            // and everything downstream of it — every later edit, every later
            // merge, every partial sync — is walked across one. Which replica
            // is holding two heads is not something a plan can know in
            // advance, so it names where to start looking.
            Action::Merge { first, seed } => {
                let mut rng = Rng(seed);
                for offset in 0..plan.replicas {
                    let replica = (first + offset) % plan.replicas;
                    if sim.merge(&mut rng, replica, salt(seed)) {
                        sim.checked(replica, step)?;
                        break;
                    }
                }
            }
            Action::Sync { into, from } => {
                if into != from {
                    sim.sync(into, from);
                    sim.checked(into, step)?;
                }
            }
        }
    }

    // Full sync: everyone reads one file, in both architectures.
    for into in 0..plan.replicas {
        for from in 0..plan.replicas {
            if into != from {
                sim.sync(into, from);
            }
        }
    }
    let first = sim.replicas[0].text();
    for replica in 0..plan.replicas {
        sim.checked(replica, plan.actions.len())?;
        let held = sim.replicas[replica].text();
        if held != first {
            return Err(format!(
                "after a full sync the reference replicas did not converge\n\
                 \x20 replica 0 reads:\n{}\n\
                 \x20 replica {replica} reads:\n{}",
                shown(&first),
                shown(&held),
            ));
        }
    }
    Ok(sim.reached.get())
}

/// What the written lines of one action are labelled with, so that two
/// actions do not mint the same text — derived from the action's own seed
/// rather than its position, since shrinking moves positions and a label that
/// moved with them would change what every later action produced.
fn salt(seed: u64) -> usize {
    (seed % 1000) as usize
}

/// Run one plan, catching a panic from anywhere further in.
///
/// A `merge` that returns an error and a merge that disagrees are both this
/// suite finding something, and the search below has to treat them the same
/// way — otherwise it shrinks towards whichever failure it can see and walks
/// away from the other.
fn attempt(plan: &Plan) -> Result<Reached, String> {
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run(plan)));
    outcome.unwrap_or_else(|panic| {
        let said = panic
            .downcast_ref::<&str>()
            .map(|said| (*said).to_owned())
            .or_else(|| panic.downcast_ref::<String>().cloned())
            .unwrap_or_else(|| "a panic that said nothing".to_owned());
        Err(format!("panicked: {said}"))
    })
}

/// Make a failing plan smaller, one candidate at a time.
///
/// Delta debugging at the size this suite needs: take an action out, take a
/// replica out, plainen the root, and keep whatever still fails. Repeat until
/// a pass changes nothing.
///
/// There is no shrinking library here on purpose. A general one shrinks the
/// values a plan is made of; what makes a counterexample readable is knowing
/// that a merge action does nothing unless some replica holds two heads, that
/// a sync to oneself is a no-op, and that dropping the highest-numbered
/// replica leaves every other action meaning what it meant. That is domain
/// knowledge, and it is about thirty lines of it.
///
/// Bounded, because a shrink that runs all afternoon is worse than a
/// counterexample that is a little too big.
fn shrink(plan: Plan) -> Plan {
    /// How many candidate plans the search may run. Each is a whole round, so
    /// this is seconds, not minutes.
    const CANDIDATES: usize = 1_500;

    // The hook, not the panics: a candidate that panics is the search working
    // as intended, and printing fifteen hundred backtraces would bury the one
    // report that matters. The suite is already failing by the time this
    // runs, which is the only reason a global hook is acceptable here.
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));

    let mut best = plan;
    let mut spent = 0usize;
    let mut improved = true;
    while improved && spent < CANDIDATES {
        improved = false;

        // Fewer actions first: the shortest history is the readable one.
        let mut at = best.actions.len();
        while at > 0 && spent < CANDIDATES {
            at -= 1;
            let mut candidate = best.clone();
            candidate.actions.remove(at);
            spent += 1;
            if attempt(&candidate).is_err() {
                best = candidate;
                improved = true;
            }
        }

        // Then fewer hands, then the plainest root the failure survives.
        let mut simpler: Vec<Plan> = Vec::new();
        if best.replicas > 2 {
            simpler.push(best.without(best.replicas - 1));
        }
        if best.blank.is_some() {
            simpler.push(Plan {
                blank: None,
                ..best.clone()
            });
        }
        if !best.terminated {
            simpler.push(Plan {
                terminated: true,
                ..best.clone()
            });
        }
        for candidate in simpler {
            if spent >= CANDIDATES {
                break;
            }
            spent += 1;
            if attempt(&candidate).is_err() {
                best = candidate;
                improved = true;
            }
        }
    }

    std::panic::set_hook(hook);
    best
}

/// What a failing round has to say to be worth being woken up for.
fn report(seed: u64, round: usize, plan: &Plan, failure: &str) -> String {
    let mut out = String::new();
    out.push_str("the conformance suite found a disagreement.\n\n");
    out.push_str(failure);
    out.push_str("\n\nthe whole run repeats with:\n");
    out.push_str(&format!(
        "    HISTORICA_CONFORMANCE_SEED=0x{seed:016x} cargo test --test conformance\n"
    ));
    out.push_str(&format!(
        "\nround {round}, shrunk to {} replicas and {} actions:\n",
        plan.replicas,
        plan.actions.len()
    ));
    out.push_str("    the root is alpha, beta, gamma, delta");
    if let Some(at) = plan.blank {
        out.push_str(&format!(", with an empty line at {at}"));
    }
    if !plan.terminated {
        out.push_str(", ending without a terminator");
    }
    out.push('\n');
    for (step, action) in plan.actions.iter().enumerate() {
        out.push_str(&format!("    {step:2}. {action}\n"));
    }
    out.push_str("\nto pin it as a test of its own, this is the plan:\n    ");
    out.push_str(&format!("{plan:?}\n"));
    out
}

#[test]
fn the_event_graph_replay_conforms_to_the_reference_crdt() {
    let seed = seed();
    let mut rng = Rng(seed);
    let mut reached = Reached::default();
    for round in 0..150 {
        let plan = plan(&mut rng);
        match attempt(&plan) {
            Ok(found) => {
                reached.terminator_contests += found.terminator_contests;
                reached.unterminated_not_last += found.unterminated_not_last;
            }
            Err(_) => {
                // The first failure is not the one to report. Shrink it, then
                // report the failure the smaller plan produces, since that is
                // the one the plan printed underneath it actually reproduces.
                let smaller = shrink(plan);
                let failure = attempt(&smaller).expect_err("a shrunk plan still fails");
                panic!("{}", report(seed, round, &smaller, &failure));
            }
        }
    }

    // The generator is widened to reach these, and a suite that stops
    // reaching them fails rather than passing quietly on a narrower search.
    assert!(
        reached.unterminated_not_last > 0,
        "no round produced a merged file whose unterminated item was not last \
         (seed 0x{seed:016x}): {reached:?}"
    );
    assert!(
        reached.terminator_contests > 0,
        "no round reported a contested terminator (seed 0x{seed:016x}): {reached:?}"
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
    let seed = seed() ^ 0x1e_af_1e_55;
    let mut rng = Rng(seed);
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
        assert!(
            text.starts_with("a\n"),
            "round {round} (seed 0x{seed:016x}): {text}"
        );
        assert!(
            text.ends_with("b\n"),
            "round {round} (seed 0x{seed:016x}): {text}"
        );
        for (replica, run) in runs.iter().enumerate() {
            let run: Vec<&str> = run.iter().map(String::as_str).collect();
            assert!(
                contiguous(&text, &run),
                "round {round} (seed 0x{seed:016x}): replica {replica}'s paragraph \
                 interleaved, and the whole run repeats with \
                 HISTORICA_CONFORMANCE_SEED=0x{:016x}:\n{text}",
                seed ^ 0x1e_af_1e_55,
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
