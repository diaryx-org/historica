//! A mathematical model of `crate::merge`: Eg-walker over Fugue, as Verus
//! specification functions, and the convergence theorem stated against it.
//!
//! Nothing here executes. The point of this file is the *definition* — what
//! `Tree::replay` computes, written so a theorem can quantify over every
//! causal order — and the examples at the end that hold the definition to
//! what the crate's tests expect.
//!
//! Fidelity to `merge.rs`, and the deliberate gaps:
//!
//! - Events are indexed in digest order, as `Graph::new` sorts them, so a
//!   comparison of indices is a comparison of digests.
//! - `knows` is taken as a relation with the properties `Ancestry` provides
//!   (reflexive, transitive, acyclic, containing the parent edges). That
//!   `ancestry.rs` computes exactly this is a separate, executable proof.
//! - An element is named `(author, minted)` — the event and its running
//!   count of items — rather than `(revision, op + offset)`. Sibling ties are
//!   broken by the author half, and two elements of one author are never
//!   same-side siblings, so the second half never decides an order.
//! - Resolutions (decision 0032) are not modelled yet. Every event states an
//!   operation document or nothing.
//! - `contested` is not modelled; the theorem is about the file.

use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Items and operations, as in the replay model.
// ---------------------------------------------------------------------------

pub struct ItemS {
    pub text: Seq<u8>,
    pub terminated: bool,
    pub forgotten: bool,
}

pub open spec fn matches_s(recorded: ItemS, found: ItemS) -> bool {
    recorded.terminated == found.terminated
        && (recorded.forgotten || found.forgotten || recorded.text == found.text)
}

pub struct OperationS {
    pub delete: bool,
    pub at: int,
    pub items: Seq<ItemS>,
}

// ---------------------------------------------------------------------------
// The event graph.
// ---------------------------------------------------------------------------

/// One revision's contribution: what it stated, or nothing.
pub struct EventS {
    pub ops: Option<Seq<OperationS>>,
}

pub struct GraphS {
    /// Indexed in digest order.
    pub events: Seq<EventS>,
    /// `knows(e, o)`: `o` is in `e`'s causal past, `e` itself included.
    pub knows: spec_fn(int, int) -> bool,
}

impl GraphS {
    pub open spec fn n(self) -> int { self.events.len() as int }

    pub open spec fn event(self, e: int) -> bool { 0 <= e < self.n() }

    pub open spec fn knows(self, e: int, o: int) -> bool { (self.knows)(e, o) }

    /// Strictly in the past: the view positions are counted into.
    pub open spec fn saw(self, e: int, o: int) -> bool { e != o && self.knows(e, o) }

    /// What `Ancestry` guarantees of the relation it answers.
    pub open spec fn wf(self) -> bool {
        &&& forall|e: int| self.event(e) ==> self.knows(e, e)
        &&& forall|a: int, b: int, c: int| self.event(a) && self.event(b) && self.event(c)
                && self.knows(a, b) && self.knows(b, c) ==> self.knows(a, c)
        &&& forall|a: int, b: int| self.event(a) && self.event(b)
                && self.knows(a, b) && self.knows(b, a) ==> a == b
    }
}

/// A causal order: every event once, and nothing before what it had seen.
pub open spec fn valid_order(g: GraphS, order: Seq<int>) -> bool {
    &&& order.len() == g.n()
    &&& forall|i: int| 0 <= i < order.len() ==> g.event(#[trigger] order[i])
    &&& forall|i: int, j: int| 0 <= i < order.len() && 0 <= j < order.len() && i != j
            ==> order[i] != order[j]
    &&& forall|i: int, j: int| 0 <= i < order.len() && 0 <= j < order.len()
            && g.saw(order[i], order[j]) ==> j < i
}

// ---------------------------------------------------------------------------
// The transient tree.
// ---------------------------------------------------------------------------

/// One element. Its place is `(parent, right)`: a child of `parent` (or of
/// the root when `None`), on its right side or its left.
pub struct Node {
    pub author: int,
    pub minted: int,
    pub item: ItemS,
    pub parent: Option<int>,
    pub right: bool,
    /// Every event that removed it. Concurrent deletions agree.
    pub deleted: Set<int>,
}

pub struct TreeS {
    /// In attachment order, so a parent's index is below its children's.
    pub nodes: Seq<Node>,
}

impl TreeS {
    pub open spec fn len(self) -> int { self.nodes.len() as int }

    pub open spec fn node(self, i: int) -> bool { 0 <= i < self.len() }

    /// The name sibling ties are broken by: digest, then index.
    pub open spec fn id(self, i: int) -> (int, int) { (self.nodes[i].author, self.nodes[i].minted) }

    pub open spec fn id_lt(a: (int, int), b: (int, int)) -> bool {
        a.0 < b.0 || (a.0 == b.0 && a.1 < b.1)
    }

    /// Whether `j` hangs off `parent` on the side `right`.
    pub open spec fn hangs(self, j: int, parent: Option<int>, right: bool) -> bool {
        self.node(j) && self.nodes[j].parent == parent && self.nodes[j].right == right
    }

    /// `Tree::attach`'s placement: before the first sibling whose name is greater.
    pub open spec fn insert_sorted(self, siblings: Seq<int>, j: int) -> Seq<int> {
        siblings.insert(self.first_greater(siblings, j, 0), j)
    }

    pub open spec fn first_greater(self, siblings: Seq<int>, j: int, k: int) -> int
        decreases siblings.len() - k
    {
        if k < 0 || k >= siblings.len() {
            siblings.len() as int
        } else if Self::id_lt(self.id(j), self.id(siblings[k])) {
            k
        } else {
            self.first_greater(siblings, j, k + 1)
        }
    }

    /// The sibling list under `parent` on side `right`, as `attach` built it:
    /// each node in attachment order, placed among those before it by name.
    pub open spec fn children_upto(self, parent: Option<int>, right: bool, k: int) -> Seq<int>
        decreases k
    {
        if k <= 0 {
            Seq::empty()
        } else {
            let before = self.children_upto(parent, right, k - 1);
            if self.hangs(k - 1, parent, right) { self.insert_sorted(before, k - 1) } else { before }
        }
    }

    pub open spec fn children(self, parent: Option<int>, right: bool) -> Seq<int> {
        self.children_upto(parent, right, self.len())
    }

    /// `Tree::order`: the in-order reading. Left subtrees, the node, right
    /// subtrees. A child's index is above its parent's in any tree `attach`
    /// built, which is what the guards ask so the recursion is total.
    pub open spec fn read(self, i: int) -> Seq<int>
        decreases self.len() - i, 1int, 0int
    {
        if !self.node(i) {
            Seq::empty()
        } else {
            self.read_all(self.children(Some(i), false), i)
                + seq![i]
                + self.read_all(self.children(Some(i), true), i)
        }
    }

    pub open spec fn read_all(self, siblings: Seq<int>, above: int) -> Seq<int>
        decreases self.len() - above, 0int, siblings.len()
    {
        if siblings.len() == 0 {
            Seq::empty()
        } else {
            let first = siblings[0];
            let rest = self.read_all(siblings.drop_first(), above);
            if above < first < self.len() { self.read(first) + rest } else { rest }
        }
    }

    /// The whole document, in order.
    ///
    /// Opaque, with `visible` and `items`: `order` is a sum of `read`s, and
    /// vstd's `filter_distributes_over_add` turns any `filter` over it into
    /// a matching loop unless the definition stays closed until asked for.
    #[verifier::opaque]
    pub open spec fn order(self) -> Seq<int> {
        self.read_all(self.children(None, true), -1)
    }

    /// `Tree::visible`: what `e`'s author could see — written in their past,
    /// and not removed by anything in their past.
    #[verifier::opaque]
    pub open spec fn visible(self, g: GraphS, e: int) -> Seq<int> {
        self.order().filter(|i: int| self.seen(g, e, i))
    }

    pub open spec fn seen(self, g: GraphS, e: int, i: int) -> bool {
        g.saw(e, self.nodes[i].author)
            && !(exists|d: int| self.nodes[i].deleted.contains(d) && g.saw(e, d))
    }

    /// The first sibling whose author `e` knows.
    pub open spec fn first_known(self, g: GraphS, e: int, siblings: Seq<int>) -> Option<int>
        decreases siblings.len()
    {
        if siblings.len() == 0 {
            None
        } else if g.knows(e, self.nodes[siblings[0]].author) {
            Some(siblings[0])
        } else {
            self.first_known(g, e, siblings.drop_first())
        }
    }

    /// Down the known left children, as far as they go.
    pub open spec fn leftmost_known(self, g: GraphS, e: int, at: int) -> int
        decreases self.len() - at
    {
        match self.first_known(g, e, self.children(Some(at), false)) {
            None => at,
            Some(next) => if at < next < self.len() { self.leftmost_known(g, e, next) } else { at },
        }
    }

    /// `Tree::anchor`: Fugue's rule. Attach to the left neighbour's right
    /// when it has no known right child; otherwise as a left child of the
    /// leftmost known node under its first known right child.
    pub open spec fn anchor(self, g: GraphS, e: int, left: Option<int>) -> (Option<int>, bool) {
        let siblings = self.children(left, true);
        match self.first_known(g, e, siblings) {
            None => (left, true),
            Some(first) => (Some(self.leftmost_known(g, e, first)), false),
        }
    }

    pub open spec fn attach(self, author: int, minted: int, item: ItemS, place: (Option<int>, bool)) -> TreeS {
        TreeS {
            nodes: self.nodes.push(Node {
                author, minted, item, parent: place.0, right: place.1, deleted: Set::empty(),
            }),
        }
    }

    pub open spec fn delete(self, i: int, by: int) -> TreeS {
        let node = self.nodes[i];
        TreeS { nodes: self.nodes.update(i, Node { deleted: node.deleted.insert(by), ..node }) }
    }

    /// Nothing has removed it.
    pub open spec fn standing(self, i: int) -> bool {
        forall|d: int| !self.nodes[i].deleted.contains(d)
    }

    /// The merged file: every element still standing, in order.
    #[verifier::opaque]
    pub open spec fn items(self) -> Seq<ItemS> {
        self.order()
            .filter(|i: int| self.standing(i))
            .map(|_k: int, i: int| self.nodes[i].item)
    }
}

// ---------------------------------------------------------------------------
// Replaying one event: `Tree::operations`.
// ---------------------------------------------------------------------------

/// A run of inserted items, each anchored after the one before.
pub open spec fn insert_run(
    t: TreeS, g: GraphS, e: int, items: Seq<ItemS>, left: Option<int>, minted: int,
) -> (TreeS, int)
    decreases items.len()
{
    if items.len() == 0 {
        (t, minted)
    } else {
        let place = t.anchor(g, e, left);
        let next = t.attach(e, minted, items[0], place);
        insert_run(next, g, e, items.drop_first(), Some(t.len()), minted + 1)
    }
}

/// A delete's items, held against the view and marked.
pub open spec fn delete_run(
    t: TreeS, g: GraphS, e: int, prepare: Seq<int>, at: int, items: Seq<ItemS>, k: int,
) -> Option<TreeS>
    decreases items.len() - k
{
    if k < 0 || k >= items.len() {
        Some(t)
    } else {
        let target = prepare[at + k];
        if !matches_s(items[k], t.nodes[target].item) {
            None
        } else {
            delete_run(t.delete(target, e), g, e, prepare, at, items, k + 1)
        }
    }
}

/// `None` where the document contradicts its author's view.
pub open spec fn replay_ops(
    t: TreeS, g: GraphS, e: int, prepare: Seq<int>, ops: Seq<OperationS>, k: int, minted: int,
) -> Option<TreeS>
    decreases ops.len() - k
{
    if k < 0 || k >= ops.len() {
        Some(t)
    } else {
        let op = ops[k];
        if op.delete {
            if op.at < 0 || op.at + op.items.len() > prepare.len() {
                None
            } else {
                match delete_run(t, g, e, prepare, op.at, op.items, 0) {
                    None => None,
                    Some(next) => replay_ops(next, g, e, prepare, ops, k + 1, minted),
                }
            }
        } else {
            if op.at < 0 || op.at > prepare.len() {
                None
            } else {
                let left = if op.at == 0 { None } else { Some(prepare[op.at - 1]) };
                let (next, minted) = insert_run(t, g, e, op.items, left, minted);
                replay_ops(next, g, e, prepare, ops, k + 1, minted)
            }
        }
    }
}

pub open spec fn replay_event(t: TreeS, g: GraphS, e: int) -> Option<TreeS> {
    match g.events[e].ops {
        None => Some(t),
        Some(ops) => replay_ops(t, g, e, t.visible(g, e), ops, 0, 0),
    }
}

/// `walk`: the tree after the first `k` events of `order`.
pub open spec fn walk(g: GraphS, order: Seq<int>, k: int) -> Option<TreeS>
    decreases k
{
    if k <= 0 {
        Some(TreeS { nodes: Seq::empty() })
    } else {
        match walk(g, order, k - 1) {
            None => None,
            Some(t) => replay_event(t, g, order[k - 1]),
        }
    }
}

pub open spec fn merged(g: GraphS, order: Seq<int>) -> Option<Seq<ItemS>> {
    match walk(g, order, order.len() as int) {
        None => None,
        Some(t) => Some(t.items()),
    }
}

// ---------------------------------------------------------------------------
// The theorem. Decision 0007's second acceptance claim.
// ---------------------------------------------------------------------------

/// Replaying one graph in any two causal orders produces the same file, or
/// the same refusal.
///
/// **Not yet proven.** The route: an element's place is a function of its
/// author's causal past alone, because `anchor` reads only siblings whose
/// authors the event knows and `visible` only elements it saw; so the tree
/// after any causally closed prefix is the same abstract tree, and `items`
/// is a function of the abstract tree. See README.
pub proof fn theorem_convergence(g: GraphS, a: Seq<int>, b: Seq<int>)
    requires g.wf(), valid_order(g, a), valid_order(g, b)
    ensures merged(g, a) == merged(g, b)
{
    admit();
}

// ---------------------------------------------------------------------------
// Unfolding lemmas: how each definition moves under `attach` and `delete`.
// ---------------------------------------------------------------------------

/// `children` after an attach: the new node joins its own sibling list by
/// name, and no other list changes.
pub proof fn lemma_children_attach(t: TreeS, author: int, minted: int, item: ItemS, place: (Option<int>, bool), parent: Option<int>, right: bool)
    ensures ({
        let u = t.attach(author, minted, item, place);
        u.children(parent, right) == if place == (parent, right) {
            u.insert_sorted(t.children(parent, right), t.len())
        } else {
            t.children(parent, right)
        }
    })
{
    let u = t.attach(author, minted, item, place);
    lemma_children_upto_same(t, u, parent, right, t.len());
    assert(u.children_upto(parent, right, u.len()) == (
        if u.hangs(t.len(), parent, right) { u.insert_sorted(u.children_upto(parent, right, t.len()), t.len()) }
        else { u.children_upto(parent, right, t.len()) }
    ));
    assert(u.hangs(t.len(), parent, right) == (place == (parent, right)));
}

/// Two trees agreeing on their first `k` nodes list the same children among them.
proof fn lemma_children_upto_same(t: TreeS, u: TreeS, parent: Option<int>, right: bool, k: int)
    requires k <= t.len(), k <= u.len(), forall|i: int| 0 <= i < k ==> t.nodes[i] == u.nodes[i]
    ensures t.children_upto(parent, right, k) == u.children_upto(parent, right, k)
    decreases k
{
    if k > 0 {
        lemma_children_upto_same(t, u, parent, right, k - 1);
        if t.hangs(k - 1, parent, right) {
            lemma_children_upto_hang(t, parent, right, k - 1);
            lemma_insert_sorted_same(t, u, t.children_upto(parent, right, k - 1), k - 1);
        }
    }
}

/// `insert_sorted` reads only the names of the nodes it places among.
proof fn lemma_insert_sorted_same(t: TreeS, u: TreeS, siblings: Seq<int>, j: int)
    requires
        0 <= j < t.len(), 0 <= j < u.len(), t.nodes[j] == u.nodes[j],
        forall|i: int| 0 <= i < siblings.len() ==> 0 <= #[trigger] siblings[i] < t.len() && siblings[i] < u.len() && t.nodes[siblings[i]] == u.nodes[siblings[i]],
    ensures t.insert_sorted(siblings, j) == u.insert_sorted(siblings, j)
{
    lemma_first_greater_same(t, u, siblings, j, 0);
}

proof fn lemma_first_greater_same(t: TreeS, u: TreeS, siblings: Seq<int>, j: int, k: int)
    requires
        0 <= j < t.len(), 0 <= j < u.len(), t.nodes[j] == u.nodes[j],
        forall|i: int| 0 <= i < siblings.len() ==> 0 <= #[trigger] siblings[i] < t.len() && siblings[i] < u.len() && t.nodes[siblings[i]] == u.nodes[siblings[i]],
    ensures t.first_greater(siblings, j, k) == u.first_greater(siblings, j, k)
    decreases siblings.len() - k
{
    if 0 <= k < siblings.len() {
        lemma_first_greater_same(t, u, siblings, j, k + 1);
    }
}

/// Every index a sibling list holds is a node, and hangs where the list says.
pub proof fn lemma_children_upto_hang(t: TreeS, parent: Option<int>, right: bool, k: int)
    requires k <= t.len()
    ensures forall|i: int| 0 <= i < t.children_upto(parent, right, k).len()
        ==> 0 <= #[trigger] t.children_upto(parent, right, k)[i] < k && t.hangs(t.children_upto(parent, right, k)[i], parent, right)
    decreases k
{
    if k > 0 {
        lemma_children_upto_hang(t, parent, right, k - 1);
        let before = t.children_upto(parent, right, k - 1);
        if t.hangs(k - 1, parent, right) {
            let at = t.first_greater(before, k - 1, 0);
            lemma_first_greater_bounds(t, before, k - 1, 0);
            let after = before.insert(at, k - 1);
            assert forall|i: int| 0 <= i < after.len() implies 0 <= #[trigger] after[i] < k && t.hangs(after[i], parent, right) by {
                if i < at { assert(after[i] == before[i]); }
                else if i == at { assert(after[i] == k - 1); }
                else { assert(after[i] == before[i - 1]); }
            }
        }
    }
}

proof fn lemma_first_greater_bounds(t: TreeS, siblings: Seq<int>, j: int, k: int)
    requires 0 <= k <= siblings.len()
    ensures k <= t.first_greater(siblings, j, k) <= siblings.len()
    decreases siblings.len() - k
{
    if k < siblings.len() && !TreeS::id_lt(t.id(j), t.id(siblings[k])) {
        lemma_first_greater_bounds(t, siblings, j, k + 1);
    }
}

// ---------------------------------------------------------------------------
// The model on the crate's own tests, so the definition is not vacuous.
// ---------------------------------------------------------------------------

spec fn line(c: u8) -> ItemS { ItemS { text: seq![c], terminated: true, forgotten: false } }
spec fn ins(at: int, items: Seq<ItemS>) -> OperationS { OperationS { delete: false, at, items } }
spec fn del(at: int, items: Seq<ItemS>) -> OperationS { OperationS { delete: true, at, items } }

/// A node as the examples spell one.
spec fn node(author: int, minted: int, item: ItemS, parent: Option<int>, right: bool) -> Node {
    Node { author, minted, item, parent, right, deleted: Set::empty() }
}

// Generic shapes, so an example never unfolds `children_upto` itself.

proof fn lemma_children_none(t: TreeS, parent: Option<int>, right: bool, k: int)
    requires 0 <= k <= t.len(), forall|j: int| 0 <= j < k ==> !t.hangs(j, parent, right)
    ensures t.children_upto(parent, right, k) == Seq::<int>::empty()
    decreases k
{
    if k > 0 { lemma_children_none(t, parent, right, k - 1); }
}

proof fn lemma_children_one(t: TreeS, parent: Option<int>, right: bool, j: int)
    requires t.hangs(j, parent, right), forall|i: int| 0 <= i < t.len() && i != j ==> !t.hangs(i, parent, right)
    ensures t.children(parent, right) == seq![j]
{
    lemma_children_none(t, parent, right, j);
    lemma_children_upto_after(t, parent, right, j + 1, t.len());
    reveal_with_fuel(TreeS::first_greater, 2);
    assert(t.children_upto(parent, right, j + 1) =~= seq![j]);
}

proof fn lemma_children_two(t: TreeS, parent: Option<int>, right: bool, j1: int, j2: int)
    requires
        j1 < j2, t.hangs(j1, parent, right), t.hangs(j2, parent, right),
        forall|i: int| 0 <= i < t.len() && i != j1 && i != j2 ==> !t.hangs(i, parent, right),
    ensures t.children(parent, right) == if TreeS::id_lt(t.id(j2), t.id(j1)) { seq![j2, j1] } else { seq![j1, j2] }
{
    lemma_children_none(t, parent, right, j1);
    reveal_with_fuel(TreeS::first_greater, 3);
    assert(t.children_upto(parent, right, j1 + 1) =~= seq![j1]);
    lemma_children_upto_after(t, parent, right, j1 + 1, j2);
    assert(t.children_upto(parent, right, j2 + 1) =~= (if TreeS::id_lt(t.id(j2), t.id(j1)) { seq![j2, j1] } else { seq![j1, j2] }));
    lemma_children_upto_after(t, parent, right, j2 + 1, t.len());
}

/// Nothing hangs in `from..to`, so the list does not move across it.
proof fn lemma_children_upto_after(t: TreeS, parent: Option<int>, right: bool, from: int, to: int)
    requires 0 <= from <= to <= t.len(), forall|j: int| from <= j < to ==> !t.hangs(j, parent, right)
    ensures t.children_upto(parent, right, to) == t.children_upto(parent, right, from)
    decreases to - from
{
    if to > from { lemma_children_upto_after(t, parent, right, from, to - 1); }
}

proof fn lemma_read_leaf(t: TreeS, i: int)
    requires t.node(i), t.children(Some(i), false) == Seq::<int>::empty(), t.children(Some(i), true) == Seq::<int>::empty()
    ensures t.read(i) == seq![i]
{
    reveal_with_fuel(TreeS::read_all, 2);
    assert(t.read(i) =~= seq![i]);
}

// The graph: `0 ── 1`, `0 ── 2`. `the_events_may_arrive_in_any_order`, and
// the smallest tie there is: the root writes `a`, one branch inserts `x` at
// 1 and the other `y` at 1. The tie is broken by digest, so `x` (event 1)
// precedes `y` (event 2) whichever branch is walked first.

spec fn fork_knows(e: int, o: int) -> bool { e == o || (o == 0 && (e == 1 || e == 2)) }

spec fn a() -> ItemS { line(b'a') }
spec fn x() -> ItemS { line(b'x') }
spec fn y() -> ItemS { line(b'y') }

spec fn ex_g() -> GraphS {
    GraphS {
        events: seq![
            EventS { ops: Some(seq![ins(0, seq![a()])]) },
            EventS { ops: Some(seq![ins(1, seq![x()])]) },
            EventS { ops: Some(seq![ins(1, seq![y()])]) },
        ],
        knows: |e: int, o: int| fork_knows(e, o),
    }
}

spec fn t0() -> TreeS { TreeS { nodes: Seq::empty() } }
spec fn t1() -> TreeS { TreeS { nodes: seq![node(0, 0, a(), None, true)] } }
// Forwards: `x` then `y`.
spec fn t2() -> TreeS { TreeS { nodes: t1().nodes.push(node(1, 0, x(), Some(0), true)) } }
spec fn t3() -> TreeS { TreeS { nodes: t2().nodes.push(node(2, 0, y(), Some(0), true)) } }
// Backwards: `y` then `x`.
spec fn u2() -> TreeS { TreeS { nodes: t1().nodes.push(node(2, 0, y(), Some(0), true)) } }
spec fn u3() -> TreeS { TreeS { nodes: u2().nodes.push(node(1, 0, x(), Some(0), true)) } }

proof fn ex_graph_wf()
    ensures ex_g().wf(), valid_order(ex_g(), seq![0int, 1, 2]), valid_order(ex_g(), seq![0int, 2, 1])
{
}

proof fn ex_step0()
    ensures replay_event(t0(), ex_g(), 0) == Some(t1())
{
    let (t, g) = (t0(), ex_g());
    lemma_children_none(t, None, true, 0);
    reveal_with_fuel(TreeS::read_all, 2);
    reveal(TreeS::order);
    assert(t.order() == Seq::<int>::empty());
    reveal(TreeS::visible);
    reveal_with_fuel(Seq::filter, 2);
    assert(t.visible(g, 0) == Seq::<int>::empty());
    reveal_with_fuel(TreeS::first_known, 2);
    assert(t.anchor(g, 0, None) == (None::<int>, true));
    reveal_with_fuel(insert_run, 3);
    assert(insert_run(t, g, 0, seq![a()], None, 0) == (t1(), 1));
    reveal_with_fuel(replay_ops, 3);
}

/// `t1` is `a` alone, under the root.
proof fn ex_t1_shape()
    ensures
        t1().children(None, true) == seq![0int],
        t1().children(Some(0), true) == Seq::<int>::empty(),
        t1().children(Some(0), false) == Seq::<int>::empty(),
        t1().order() == seq![0int],
{
    let t = t1();
    lemma_children_one(t, None, true, 0);
    lemma_children_none(t, Some(0), true, 1);
    lemma_children_none(t, Some(0), false, 1);
    lemma_read_leaf(t, 0);
    reveal_with_fuel(TreeS::read_all, 2);
    reveal(TreeS::order);
    assert(t.order() =~= seq![0int]);
}

/// A branch's insert at 1 against `t1`: after `a`, to its right, because
/// `a` has no right child yet, and every event sees `a`.
proof fn ex_step_from_t1(t: TreeS, e: int, item: ItemS)
    requires t == t1(), e == 1 || e == 2, item == (if e == 1 { x() } else { y() })
    ensures replay_event(t, ex_g(), e) == Some(TreeS { nodes: t.nodes.push(node(e, 0, item, Some(0), true)) }),
{
    let g = ex_g();
    ex_t1_shape();
    assert(t.visible(g, e) == seq![0int]) by {
        reveal(TreeS::visible);
        reveal_with_fuel(Seq::filter, 3);
        assert(t.seen(g, e, 0));
        assert(t.visible(g, e) =~= seq![0int]);
    }
    assert(t.anchor(g, e, Some(0)) == (Some(0int), true)) by {
        reveal_with_fuel(TreeS::first_known, 2);
    }
    let after = TreeS { nodes: t.nodes.push(node(e, 0, item, Some(0), true)) };
    assert(t.attach(e, 0, item, (Some(0), true)) == after);
    assert(insert_run(t, g, e, seq![item], Some(0), 0) == (after, 1)) by {
        reveal_with_fuel(insert_run, 3);
    }
    assert(g.events[e].ops == Some(seq![ins(1, seq![item])]));
    assert(replay_ops(t, g, e, seq![0int], seq![ins(1, seq![item])], 0, 0) == Some(after)) by {
        reveal_with_fuel(replay_ops, 3);
    }
    assert(replay_event(t, g, e) == Some(after)) by {
        assert(replay_event(t, g, e) == replay_ops(t, g, e, t.visible(g, e), seq![ins(1, seq![item])], 0, 0));
    }
}

/// A tree of `a` and one branch's element to its right: its shape.
proof fn ex_two_shape(t: TreeS, first: int)
    requires
        first == 1 || first == 2,
        t == (TreeS { nodes: t1().nodes.push(node(first, 0, if first == 1 { x() } else { y() }, Some(0), true)) }),
    ensures
        t.children(None, true) == seq![0int],
        t.children(Some(0), true) == seq![1int],
        t.children(Some(0), false) == Seq::<int>::empty(),
        t.children(Some(1), true) == Seq::<int>::empty(),
        t.children(Some(1), false) == Seq::<int>::empty(),
        t.order() == seq![0int, 1],
{
    lemma_children_one(t, None, true, 0);
    lemma_children_one(t, Some(0), true, 1);
    lemma_children_none(t, Some(0), false, 2);
    lemma_children_none(t, Some(1), true, 2);
    lemma_children_none(t, Some(1), false, 2);
    lemma_read_leaf(t, 1);
    reveal_with_fuel(TreeS::read, 2);
    reveal_with_fuel(TreeS::read_all, 3);
    reveal(TreeS::order);
    assert(t.read(0) =~= seq![0int, 1]);
    assert(t.order() =~= seq![0int, 1]);
}

/// The second branch sees `a` alone: the first branch's element is one its
/// author had not seen, so it neither counts into the view nor anchors.
proof fn ex_second_branch(t: TreeS, first: int, second: int, item: ItemS)
    requires
        (first == 1 && second == 2) || (first == 2 && second == 1),
        t == (TreeS { nodes: t1().nodes.push(node(first, 0, if first == 1 { x() } else { y() }, Some(0), true)) }),
        item == (if second == 1 { x() } else { y() }),
    ensures
        replay_event(t, ex_g(), second) == Some(TreeS { nodes: t.nodes.push(node(second, 0, item, Some(0), true)) }),
{
    let g = ex_g();
    ex_two_shape(t, first);
    assert(t.visible(g, second) == seq![0int]) by {
        reveal(TreeS::visible);
        reveal_with_fuel(Seq::filter, 3);
        assert(t.seen(g, second, 0));
        assert(!t.seen(g, second, 1));
        assert(t.visible(g, second) =~= seq![0int]);
    }
    assert(t.anchor(g, second, Some(0)) == (Some(0int), true)) by {
        reveal_with_fuel(TreeS::first_known, 3);
        assert(!g.knows(second, first));
        assert(t.first_known(g, second, seq![1int]) == None::<int>);
    }
    let after = TreeS { nodes: t.nodes.push(node(second, 0, item, Some(0), true)) };
    assert(t.attach(second, 0, item, (Some(0), true)) == after);
    assert(insert_run(t, g, second, seq![item], Some(0), 0) == (after, 1)) by {
        reveal_with_fuel(insert_run, 3);
    }
    assert(g.events[second].ops == Some(seq![ins(1, seq![item])]));
    assert(replay_ops(t, g, second, seq![0int], seq![ins(1, seq![item])], 0, 0) == Some(after)) by {
        reveal_with_fuel(replay_ops, 3);
    }
}

/// A finished tree's shape: `a` under the root, both branches' elements to
/// its right, ordered by name — event 1's `x` before event 2's `y`, whether
/// `x` was attached first or second.
proof fn ex_three_shape(t: TreeS, xi: int, yi: int)
    requires
        (xi == 1 && yi == 2) || (xi == 2 && yi == 1),
        t.len() == 3,
        t.nodes[0] == node(0, 0, a(), None, true),
        t.nodes[xi] == node(1, 0, x(), Some(0), true),
        t.nodes[yi] == node(2, 0, y(), Some(0), true),
    ensures
        t.children(None, true) == seq![0int],
        t.children(Some(0), true) == seq![xi, yi],
        forall|p: int| 0 <= p < 3 ==> #[trigger] t.children(Some(p), false) == Seq::<int>::empty(),
        forall|p: int| 1 <= p < 3 ==> #[trigger] t.children(Some(p), true) == Seq::<int>::empty(),
{
    lemma_children_one(t, None, true, 0);
    if xi < yi {
        lemma_children_two(t, Some(0), true, xi, yi);
        assert(!TreeS::id_lt(t.id(yi), t.id(xi)));
    } else {
        lemma_children_two(t, Some(0), true, yi, xi);
        assert(TreeS::id_lt(t.id(xi), t.id(yi)));
    }
    assert forall|p: int| 0 <= p < 3 implies #[trigger] t.children(Some(p), false) == Seq::<int>::empty() by {
        lemma_children_none(t, Some(p), false, 3);
    }
    assert forall|p: int| 1 <= p < 3 implies #[trigger] t.children(Some(p), true) == Seq::<int>::empty() by {
        lemma_children_none(t, Some(p), true, 3);
    }
}

proof fn ex_order(t: TreeS, xi: int, yi: int)
    requires
        (xi == 1 && yi == 2) || (xi == 2 && yi == 1),
        t.len() == 3,
        t.nodes[0] == node(0, 0, a(), None, true),
        t.nodes[xi] == node(1, 0, x(), Some(0), true),
        t.nodes[yi] == node(2, 0, y(), Some(0), true),
    ensures t.order() == seq![0int, xi, yi]
{
    ex_three_shape(t, xi, yi);
    lemma_read_leaf(t, 1);
    lemma_read_leaf(t, 2);
    reveal_with_fuel(TreeS::read, 2);
    reveal_with_fuel(TreeS::read_all, 4);
    reveal(TreeS::order);
    assert(t.read_all(seq![xi, yi], 0) =~= seq![xi, yi]);
    assert(t.read(0) =~= seq![0int, xi, yi]);
    assert(t.order() =~= seq![0int, xi, yi]);
}

proof fn ex_read(t: TreeS, xi: int, yi: int)
    requires
        (xi == 1 && yi == 2) || (xi == 2 && yi == 1),
        t.len() == 3,
        t.nodes[0] == node(0, 0, a(), None, true),
        t.nodes[xi] == node(1, 0, x(), Some(0), true),
        t.nodes[yi] == node(2, 0, y(), Some(0), true),
    ensures t.items() == seq![a(), x(), y()]
{
    ex_order(t, xi, yi);
    assert(t.order().filter(|i: int| t.standing(i)) == seq![0int, xi, yi]) by {
        reveal_with_fuel(Seq::filter, 4);
        assert(t.standing(0) && t.standing(1) && t.standing(2));
        assert(t.order().filter(|i: int| t.standing(i)) =~= seq![0int, xi, yi]);
    }
    assert(t.items() == seq![a(), x(), y()]) by {
        reveal(TreeS::items);
        assert(t.items() =~= seq![a(), x(), y()]);
    }
}

/// The claim, on this graph: both walks read `a x y`.
proof fn example_concurrent_inserts_tie_by_digest()
    ensures
        merged(ex_g(), seq![0int, 1, 2]) == Some(seq![a(), x(), y()]),
        merged(ex_g(), seq![0int, 2, 1]) == Some(seq![a(), x(), y()]),
{
    let g = ex_g();
    ex_step0();
    ex_step_from_t1(t1(), 1, x());
    ex_step_from_t1(t1(), 2, y());
    ex_second_branch(t2(), 1, 2, y());
    ex_second_branch(u2(), 2, 1, x());
    reveal_with_fuel(walk, 4);
    assert(walk(g, seq![0int, 1, 2], 3) == Some(t3()));
    assert(walk(g, seq![0int, 2, 1], 3) == Some(u3()));
    ex_read(t3(), 1, 2);
    ex_read(u3(), 2, 1);
}

/// One event applied, for the examples; `replay_event` with the `None` case
/// ruled out by the example itself.
spec fn step(t: TreeS, g: GraphS, e: int) -> TreeS {
    replay_event(t, g, e).unwrap()
}

fn main() {}

} // verus!
