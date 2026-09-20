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
// A filter of our own, so its lemmas are ours.
// ---------------------------------------------------------------------------

/// `Seq::filter`, spelled here so that no broadcast lemma of vstd's fires
/// on it: the lemmas below are the whole interface.
pub open spec fn sel(s: Seq<int>, p: spec_fn(int) -> bool) -> Seq<int>
    decreases s.len()
{
    if s.len() == 0 {
        s
    } else {
        let rest = sel(s.drop_last(), p);
        if p(s.last()) { rest.push(s.last()) } else { rest }
    }
}

pub proof fn lemma_sel_add(a: Seq<int>, b: Seq<int>, p: spec_fn(int) -> bool)
    ensures sel(a + b, p) == sel(a, p) + sel(b, p)
    decreases b.len()
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(sel(a, p) + sel(b, p) =~= sel(a, p));
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
        lemma_sel_add(a, b.drop_last(), p);
        if p(b.last()) {
            assert(sel(a + b, p) =~= sel(a, p) + sel(b, p));
        }
    }
}

pub proof fn lemma_sel_single(x: int, p: spec_fn(int) -> bool)
    ensures sel(seq![x], p) == if p(x) { seq![x] } else { Seq::<int>::empty() }
{
    reveal_with_fuel(sel, 3);
    assert(seq![x].drop_last() =~= Seq::<int>::empty());
    assert(sel(Seq::<int>::empty(), p) == Seq::<int>::empty());
    if p(x) { assert(sel(seq![x], p) =~= seq![x]); }
}

/// Where `sel(s, p)[q]` came from in `s`.
pub open spec fn src(s: Seq<int>, p: spec_fn(int) -> bool, q: int) -> int
    decreases s.len()
{
    if s.len() == 0 {
        -1
    } else {
        let r = sel(s.drop_last(), p);
        if p(s.last()) && q == r.len() { s.len() - 1 } else { src(s.drop_last(), p, q) }
    }
}

/// `sel` is an order-preserving subsequence: `src` names the position each
/// element came from, and positions ascend.
pub proof fn lemma_sel_sub(s: Seq<int>, p: spec_fn(int) -> bool)
    ensures
        sel(s, p).len() <= s.len(),
        forall|q: int| 0 <= q < sel(s, p).len() ==> 0 <= #[trigger] src(s, p, q) < s.len() && s[src(s, p, q)] == sel(s, p)[q] && p(s[src(s, p, q)]),
        forall|a: int, b: int| 0 <= a < b < sel(s, p).len() ==> #[trigger] src(s, p, a) < #[trigger] src(s, p, b),
        forall|i: int| 0 <= i < s.len() && p(#[trigger] s[i]) ==> sel(s, p).contains(s[i]),
    decreases s.len()
{
    if s.len() == 0 {
        assert(sel(s, p) == s);
    } else {
        let d = s.drop_last();
        lemma_sel_sub(d, p);
        let r = sel(d, p);
        assert(sel(s, p) == if p(s.last()) { r.push(s.last()) } else { r });
        assert forall|q: int| 0 <= q < sel(s, p).len()
            implies 0 <= #[trigger] src(s, p, q) < s.len() && s[src(s, p, q)] == sel(s, p)[q] && p(s[src(s, p, q)]) by {
            if p(s.last()) && q == r.len() {
                assert(src(s, p, q) == s.len() - 1);
            } else {
                assert(src(s, p, q) == src(d, p, q));
                assert(sel(s, p)[q] == r[q]);
                assert(s[src(d, p, q)] == d[src(d, p, q)]);
            }
        }
        assert forall|a: int, b: int| 0 <= a < b < sel(s, p).len() implies #[trigger] src(s, p, a) < #[trigger] src(s, p, b) by {
            if p(s.last()) && b == r.len() {
                assert(src(s, p, a) == src(d, p, a));
                assert(src(d, p, a) < d.len());
            } else {
                assert(src(s, p, a) == src(d, p, a));
                assert(src(s, p, b) == src(d, p, b));
            }
        }
        assert forall|i: int| 0 <= i < s.len() && p(#[trigger] s[i]) implies sel(s, p).contains(s[i]) by {
            if i < d.len() {
                assert(r.contains(d[i]));
                let q = choose|q: int| 0 <= q < r.len() && r[q] == d[i];
                assert(sel(s, p)[q] == s[i]);
            } else {
                assert(sel(s, p)[r.len() as int] == s[i]);
            }
        }
    }
}

/// Two lists with the same names, filtered by predicates that agree
/// position by position, have the same names.
pub proof fn lemma_sel_names(t: TreeS, u: TreeS, x: Seq<int>, y: Seq<int>, pt: spec_fn(int) -> bool, pu: spec_fn(int) -> bool)
    requires
        t.names(x) == u.names(y),
        forall|k: int| 0 <= k < x.len() ==> (pt(#[trigger] x[k]) <==> pu(y[k])),
    ensures t.names(sel(x, pt)) == u.names(sel(y, pu))
    decreases x.len()
{
    assert(t.names(x).len() == x.len());
    assert(u.names(y).len() == y.len());
    assert(x.len() == y.len());
    assert forall|k: int| 0 <= k < x.len() implies t.id(#[trigger] x[k]) == u.id(y[k]) by {
        assert(t.names(x)[k] == t.id(x[k]));
        assert(u.names(y)[k] == u.id(y[k]));
    }
    if x.len() > 0 {
        assert(t.names(x.drop_last()) =~= u.names(y.drop_last()));
        lemma_sel_names(t, u, x.drop_last(), y.drop_last(), pt, pu);
        let n = x.len() - 1;
        assert(t.id(x[n]) == u.id(y[n]));
        assert(pt(x[n]) <==> pu(y[n]));
        let (rx, ry) = (sel(x.drop_last(), pt), sel(y.drop_last(), pu));
        assert(t.names(rx).len() == u.names(ry).len());
        if pt(x[n]) {
            assert(sel(x, pt) == rx.push(x[n]));
            assert(sel(y, pu) == ry.push(y[n]));
            let (nx, ny) = (t.names(sel(x, pt)), u.names(sel(y, pu)));
            assert(nx.len() == ny.len());
            assert forall|k: int| 0 <= k < nx.len() implies nx[k] == ny[k] by {
                assert(nx[k] == t.id(rx.push(x[n])[k]));
                assert(ny[k] == u.id(ry.push(y[n])[k]));
                if k < rx.len() {
                    assert(t.names(rx)[k] == t.id(rx[k]));
                    assert(u.names(ry)[k] == u.id(ry[k]));
                }
            }
            assert(nx =~= ny);
        } else {
            assert(sel(x, pt) == rx);
            assert(sel(y, pu) == ry);
        }
    }
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
        sel(self.order(), |i: int| self.seen(g, e, i))
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
        sel(self.order(), |i: int| self.standing(i)).map(|_k: int, i: int| self.nodes[i].item)
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
// Lemma W: the walk builds well-formed trees.
// ---------------------------------------------------------------------------

impl TreeS {
    /// What every tree the walk builds satisfies, and what the later lemmas
    /// rest on: a parent is attached before its child and known by the
    /// child's author; names are unique; a removal was by an event that
    /// saw the element's author.
    pub open spec fn wf(self, g: GraphS) -> bool {
        &&& forall|i: int| self.node(i) ==> g.event(#[trigger] self.nodes[i].author)
        &&& forall|i: int| self.node(i) && (#[trigger] self.nodes[i]).parent is Some
                ==> 0 <= self.nodes[i].parent->Some_0 < i
        &&& forall|i: int| self.node(i) && (#[trigger] self.nodes[i]).parent is Some
                ==> g.knows(self.nodes[i].author, self.nodes[self.nodes[i].parent->Some_0].author)
        &&& forall|i: int, j: int| self.node(i) && self.node(j) && i != j ==> self.id(i) != self.id(j)
        &&& forall|i: int, d: int| self.node(i) && #[trigger] self.nodes[i].deleted.contains(d)
                ==> g.saw(d, self.nodes[i].author)
    }

    /// `u` is `self` with more elements attached and more removals marked:
    /// nothing already there changes name, place or content.
    pub open spec fn extends(self, u: TreeS) -> bool {
        &&& self.len() <= u.len()
        &&& forall|i: int| self.node(i) ==> {
            &&& (#[trigger] u.nodes[i]).author == self.nodes[i].author
            &&& u.nodes[i].minted == self.nodes[i].minted
            &&& u.nodes[i].item == self.nodes[i].item
            &&& u.nodes[i].parent == self.nodes[i].parent
            &&& u.nodes[i].right == self.nodes[i].right
        }
    }

    /// A left neighbour an insertion may anchor after: an element the
    /// event knows, or nothing.
    pub open spec fn known_or_none(self, g: GraphS, e: int, left: Option<int>) -> bool {
        left is Some ==> self.node(left->Some_0) && g.knows(e, self.nodes[left->Some_0].author)
    }

    /// Every index in `prepare` is an element the event saw — the shape
    /// `visible` produces, which `replay_ops` counts positions into.
    pub open spec fn view_ok(self, g: GraphS, e: int, prepare: Seq<int>) -> bool {
        forall|q: int| 0 <= q < prepare.len() ==> self.node(#[trigger] prepare[q]) && g.saw(e, self.nodes[prepare[q]].author)
    }

    /// No element yet minted by `e` at or above `minted`.
    pub open spec fn minted_below(self, e: int, minted: int) -> bool {
        forall|i: int| self.node(i) && (#[trigger] self.nodes[i]).author == e ==> self.nodes[i].minted < minted
    }
}

pub proof fn lemma_extends_trans(t: TreeS, u: TreeS, v: TreeS)
    requires t.extends(u), u.extends(v)
    ensures t.extends(v)
{
}

pub proof fn lemma_first_known_known(t: TreeS, g: GraphS, e: int, siblings: Seq<int>)
    ensures t.first_known(g, e, siblings) matches Some(c) ==> siblings.contains(c) && g.knows(e, t.nodes[c].author)
    decreases siblings.len()
{
    if siblings.len() > 0 && !g.knows(e, t.nodes[siblings[0]].author) {
        lemma_first_known_known(t, g, e, siblings.drop_first());
        if let Some(c) = t.first_known(g, e, siblings.drop_first()) {
            let k = choose|k: int| 0 <= k < siblings.drop_first().len() && siblings.drop_first()[k] == c;
            assert(siblings[k + 1] == c);
        }
    }
}

pub proof fn lemma_children_nodes(t: TreeS, parent: Option<int>, right: bool)
    ensures forall|q: int| 0 <= q < t.children(parent, right).len()
        ==> t.hangs(#[trigger] t.children(parent, right)[q], parent, right)
{
    lemma_children_upto_hang(t, parent, right, t.len());
}

pub proof fn lemma_leftmost_known_known(t: TreeS, g: GraphS, e: int, at: int)
    requires t.node(at), g.knows(e, t.nodes[at].author)
    ensures t.node(t.leftmost_known(g, e, at)), g.knows(e, t.nodes[t.leftmost_known(g, e, at)].author)
    decreases t.len() - at
{
    let siblings = t.children(Some(at), false);
    lemma_first_known_known(t, g, e, siblings);
    lemma_children_nodes(t, Some(at), false);
    if let Some(next) = t.first_known(g, e, siblings) {
        if at < next < t.len() {
            lemma_leftmost_known_known(t, g, e, next);
        }
    }
}

pub proof fn lemma_anchor_known(t: TreeS, g: GraphS, e: int, left: Option<int>)
    requires t.known_or_none(g, e, left)
    ensures t.known_or_none(g, e, t.anchor(g, e, left).0)
{
    let siblings = t.children(left, true);
    lemma_first_known_known(t, g, e, siblings);
    lemma_children_nodes(t, left, true);
    if let Some(first) = t.first_known(g, e, siblings) {
        lemma_leftmost_known_known(t, g, e, first);
    }
}

pub proof fn lemma_attach_wf(t: TreeS, g: GraphS, e: int, minted: int, item: ItemS, place: (Option<int>, bool))
    requires t.wf(g), g.event(e), t.known_or_none(g, e, place.0), t.minted_below(e, minted)
    ensures ({
        let u = t.attach(e, minted, item, place);
        &&& u.wf(g)
        &&& t.extends(u)
        &&& u.len() == t.len() + 1
        &&& u.nodes[t.len()].author == e
        &&& u.minted_below(e, minted + 1)
    })
{
    let u = t.attach(e, minted, item, place);
    assert forall|i: int, j: int| u.node(i) && u.node(j) && i != j implies u.id(i) != u.id(j) by {
        if i < t.len() && j < t.len() {
            assert(t.id(i) != t.id(j));
        }
    }
}

pub proof fn lemma_insert_run_wf(t: TreeS, g: GraphS, e: int, items: Seq<ItemS>, left: Option<int>, minted: int)
    requires t.wf(g), g.wf(), g.event(e), t.known_or_none(g, e, left), t.minted_below(e, minted)
    ensures ({
        let (u, m) = insert_run(t, g, e, items, left, minted);
        &&& u.wf(g)
        &&& t.extends(u)
        &&& m == minted + items.len()
        &&& u.len() == t.len() + items.len()
        &&& u.minted_below(e, m)
        &&& forall|i: int| t.len() <= i < u.len() ==> (#[trigger] u.nodes[i]).author == e
    })
    decreases items.len()
{
    if items.len() > 0 {
        let place = t.anchor(g, e, left);
        lemma_anchor_known(t, g, e, left);
        lemma_attach_wf(t, g, e, minted, items[0], place);
        let next = t.attach(e, minted, items[0], place);
        assert(next.known_or_none(g, e, Some(t.len())));
        lemma_insert_run_wf(next, g, e, items.drop_first(), Some(t.len()), minted + 1);
        let (u, m) = insert_run(next, g, e, items.drop_first(), Some(t.len()), minted + 1);
        lemma_extends_trans(t, next, u);
    }
}

pub proof fn lemma_delete_wf(t: TreeS, g: GraphS, e: int, i: int)
    requires t.wf(g), t.node(i), g.saw(e, t.nodes[i].author)
    ensures t.delete(i, e).wf(g), t.extends(t.delete(i, e)), t.delete(i, e).len() == t.len()
{
    let u = t.delete(i, e);
    assert forall|a: int, b: int| u.node(a) && u.node(b) && a != b implies u.id(a) != u.id(b) by {
        assert(t.id(a) != t.id(b));
    }
}

pub proof fn lemma_delete_run_wf(t: TreeS, g: GraphS, e: int, prepare: Seq<int>, at: int, items: Seq<ItemS>, k: int)
    requires t.wf(g), t.view_ok(g, e, prepare), 0 <= at, at + items.len() <= prepare.len()
    ensures delete_run(t, g, e, prepare, at, items, k) matches Some(u) ==> u.wf(g) && t.extends(u) && u.len() == t.len()
    decreases items.len() - k
{
    if 0 <= k < items.len() {
        let target = prepare[at + k];
        if matches_s(items[k], t.nodes[target].item) {
            lemma_delete_wf(t, g, e, target);
            let next = t.delete(target, e);
            assert(next.view_ok(g, e, prepare));
            lemma_delete_run_wf(next, g, e, prepare, at, items, k + 1);
            if let Some(u) = delete_run(next, g, e, prepare, at, items, k + 1) {
                lemma_extends_trans(t, next, u);
            }
        }
    }
}

pub proof fn lemma_replay_ops_wf(t: TreeS, g: GraphS, e: int, prepare: Seq<int>, ops: Seq<OperationS>, k: int, minted: int)
    requires t.wf(g), g.wf(), g.event(e), t.view_ok(g, e, prepare), t.minted_below(e, minted)
    ensures replay_ops(t, g, e, prepare, ops, k, minted) matches Some(u) ==> u.wf(g) && t.extends(u)
        && forall|i: int| t.len() <= i < u.len() ==> (#[trigger] u.nodes[i]).author == e
    decreases ops.len() - k
{
    if 0 <= k < ops.len() {
        let op = ops[k];
        if op.delete {
            if !(op.at < 0 || op.at + op.items.len() > prepare.len()) {
                lemma_delete_run_wf(t, g, e, prepare, op.at, op.items, 0);
                if let Some(next) = delete_run(t, g, e, prepare, op.at, op.items, 0) {
                    assert(next.view_ok(g, e, prepare));
                    assert(next.minted_below(e, minted));
                    lemma_replay_ops_wf(next, g, e, prepare, ops, k + 1, minted);
                    if let Some(u) = replay_ops(next, g, e, prepare, ops, k + 1, minted) {
                        lemma_extends_trans(t, next, u);
                    }
                }
            }
        } else {
            if !(op.at < 0 || op.at > prepare.len()) {
                let left = if op.at == 0 { None } else { Some(prepare[op.at - 1]) };
                assert(t.known_or_none(g, e, left));
                lemma_insert_run_wf(t, g, e, op.items, left, minted);
                let (next, m) = insert_run(t, g, e, op.items, left, minted);
                assert(next.view_ok(g, e, prepare));
                lemma_replay_ops_wf(next, g, e, prepare, ops, k + 1, m);
                if let Some(u) = replay_ops(next, g, e, prepare, ops, k + 1, m) {
                    lemma_extends_trans(t, next, u);
                }
            }
        }
    }
}

/// Everything `read`/`read_all` emit is a node.
pub proof fn lemma_read_nodes(t: TreeS, i: int)
    ensures forall|q: int| 0 <= q < t.read(i).len() ==> t.node(#[trigger] t.read(i)[q])
    decreases t.len() - i, 1int, 0int
{
    if t.node(i) {
        let left = t.read_all(t.children(Some(i), false), i);
        let right = t.read_all(t.children(Some(i), true), i);
        lemma_read_all_nodes(t, t.children(Some(i), false), i);
        lemma_read_all_nodes(t, t.children(Some(i), true), i);
        assert forall|q: int| 0 <= q < t.read(i).len() implies t.node(#[trigger] t.read(i)[q]) by {
            if q < left.len() {
                assert(t.read(i)[q] == left[q]);
            } else if q == left.len() {
                assert(t.read(i)[q] == i);
            } else {
                assert(t.read(i)[q] == right[q - left.len() - 1]);
            }
        }
    }
}

pub proof fn lemma_read_all_nodes(t: TreeS, siblings: Seq<int>, above: int)
    ensures forall|q: int| 0 <= q < t.read_all(siblings, above).len() ==> t.node(#[trigger] t.read_all(siblings, above)[q])
    decreases t.len() - above, 0int, siblings.len()
{
    if siblings.len() > 0 {
        lemma_read_all_nodes(t, siblings.drop_first(), above);
        let first = siblings[0];
        let rest = t.read_all(siblings.drop_first(), above);
        if above < first < t.len() {
            lemma_read_nodes(t, first);
            let head = t.read(first);
            assert forall|q: int| 0 <= q < t.read_all(siblings, above).len()
                implies t.node(#[trigger] t.read_all(siblings, above)[q]) by {
                if q < head.len() {
                    assert(t.read_all(siblings, above)[q] == head[q]);
                } else {
                    assert(t.read_all(siblings, above)[q] == rest[q - head.len()]);
                }
            }
        }
    }
}

pub proof fn lemma_visible_ok(t: TreeS, g: GraphS, e: int)
    ensures t.view_ok(g, e, t.visible(g, e))
{
    reveal(TreeS::visible);
    reveal(TreeS::order);
    lemma_read_all_nodes(t, t.children(None, true), -1);
    let order = t.order();
    let pred = |i: int| t.seen(g, e, i);
    lemma_sel_sub(order, pred);
    assert forall|q: int| 0 <= q < sel(order, pred).len()
        implies t.node(#[trigger] sel(order, pred)[q]) && g.saw(e, t.nodes[sel(order, pred)[q]].author) by {
        let j = src(order, pred, q);
        assert(t.node(order[j]) && pred(order[j]));
    }
}

pub proof fn lemma_replay_event_wf(t: TreeS, g: GraphS, e: int)
    requires t.wf(g), g.wf(), g.event(e), t.minted_below(e, 0)
    ensures replay_event(t, g, e) matches Some(u) ==> u.wf(g) && t.extends(u)
        && forall|i: int| t.len() <= i < u.len() ==> (#[trigger] u.nodes[i]).author == e
{
    if let Some(ops) = g.events[e].ops {
        lemma_visible_ok(t, g, e);
        lemma_replay_ops_wf(t, g, e, t.visible(g, e), ops, 0, 0);
    }
}

/// Lemma W. Every tree the walk builds is well-formed, and every element
/// in it was written by an event already walked.
pub proof fn lemma_walk_wf(g: GraphS, order: Seq<int>, k: int)
    requires g.wf(), valid_order(g, order), 0 <= k <= order.len()
    ensures walk(g, order, k) matches Some(t) ==> t.wf(g)
        && forall|i: int| t.node(i) ==> exists|j: int| 0 <= j < k && order[j] == (#[trigger] t.nodes[i]).author
    decreases k
{
    if k > 0 {
        lemma_walk_wf(g, order, k - 1);
        if let Some(t) = walk(g, order, k - 1) {
            let e = order[k - 1];
            // `e` has not been walked, so nothing in `t` is its.
            assert(t.minted_below(e, 0)) by {
                assert forall|i: int| t.node(i) && (#[trigger] t.nodes[i]).author == e implies false by {
                    let j = choose|j: int| 0 <= j < k - 1 && order[j] == t.nodes[i].author;
                    assert(order[j] == order[k - 1]);
                }
            }
            lemma_replay_event_wf(t, g, e);
            if let Some(u) = replay_event(t, g, e) {
                assert forall|i: int| u.node(i) implies exists|j: int| 0 <= j < k && order[j] == (#[trigger] u.nodes[i]).author by {
                    if i < t.len() {
                        let j = choose|j: int| 0 <= j < k - 1 && order[j] == t.nodes[i].author;
                        assert(order[j] == u.nodes[i].author);
                    } else {
                        assert(order[k - 1] == u.nodes[i].author);
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Names, and lists sorted by them.
// ---------------------------------------------------------------------------

pub type Name = (int, int);

/// Strictly ascending by name.
pub open spec fn ids_sorted(ns: Seq<Name>) -> bool {
    forall|a: int, b: int| 0 <= a < b < ns.len() ==> TreeS::id_lt(ns[a], ns[b])
}

impl TreeS {
    /// The names along a list of indices.
    pub open spec fn names(self, s: Seq<int>) -> Seq<Name> {
        Seq::new(s.len(), |k: int| self.id(s[k]))
    }

    pub open spec fn sorted(self, s: Seq<int>) -> bool {
        forall|a: int, b: int| 0 <= a < b < s.len() ==> Self::id_lt(self.id(s[a]), self.id(s[b]))
    }
}

pub proof fn lemma_id_lt_total(a: Name, b: Name)
    ensures TreeS::id_lt(a, b) || TreeS::id_lt(b, a) || a == b
{
}

pub proof fn lemma_id_lt_trans(a: Name, b: Name, c: Name)
    requires TreeS::id_lt(a, b), TreeS::id_lt(b, c)
    ensures TreeS::id_lt(a, c)
{
}

/// A sorted list has no name twice.
pub proof fn lemma_sorted_no_dup(ns: Seq<Name>, a: int, b: int)
    requires ids_sorted(ns), 0 <= a < ns.len(), 0 <= b < ns.len(), ns[a] == ns[b]
    ensures a == b
{
    if a < b { assert(TreeS::id_lt(ns[a], ns[b])); }
    if b < a { assert(TreeS::id_lt(ns[b], ns[a])); }
}

/// Two sorted lists with the same members are the same list.
pub proof fn lemma_sorted_same_members(ns1: Seq<Name>, ns2: Seq<Name>)
    requires ids_sorted(ns1), ids_sorted(ns2), forall|n: Name| ns1.contains(n) <==> ns2.contains(n)
    ensures ns1 == ns2
    decreases ns1.len()
{
    if ns1.len() == 0 {
        if ns2.len() > 0 {
            assert(ns2.contains(ns2[0]));
            assert(ns1.contains(ns2[0]));
        }
        assert(ns1 =~= ns2);
    } else {
        assert(ns1.contains(ns1[0]));
        assert(ns2.contains(ns1[0]));
        let q = choose|q: int| 0 <= q < ns2.len() && ns2[q] == ns1[0];
        assert(ns2.contains(ns2[0]));
        assert(ns1.contains(ns2[0]));
        let r = choose|r: int| 0 <= r < ns1.len() && ns1[r] == ns2[0];
        // The heads are each other's minimum.
        if q > 0 { assert(TreeS::id_lt(ns2[0], ns2[q])); }
        if r > 0 { assert(TreeS::id_lt(ns1[0], ns1[r])); }
        assert(ns1[0] == ns2[0]) by {
            if q > 0 && r > 0 {
                lemma_id_lt_trans(ns1[0], ns2[0], ns1[0]);
            }
        }
        let t1 = ns1.drop_first();
        let t2 = ns2.drop_first();
        assert(ids_sorted(t1));
        assert(ids_sorted(t2));
        assert forall|n: Name| t1.contains(n) <==> t2.contains(n) by {
            if t1.contains(n) {
                let a = choose|a: int| 0 <= a < t1.len() && t1[a] == n;
                assert(ns1[a + 1] == n);
                assert(ns1.contains(n));
                assert(ns2.contains(n));
                let b = choose|b: int| 0 <= b < ns2.len() && ns2[b] == n;
                if b == 0 { lemma_sorted_no_dup(ns1, 0, a + 1); }
                assert(t2[b - 1] == n);
            }
            if t2.contains(n) {
                let a = choose|a: int| 0 <= a < t2.len() && t2[a] == n;
                assert(ns2[a + 1] == n);
                assert(ns2.contains(n));
                assert(ns1.contains(n));
                let b = choose|b: int| 0 <= b < ns1.len() && ns1[b] == n;
                if b == 0 { lemma_sorted_no_dup(ns2, 0, a + 1); }
                assert(t1[b - 1] == n);
            }
        }
        lemma_sorted_same_members(t1, t2);
        assert(ns1.len() == ns2.len());
        assert forall|k: int| 0 <= k < ns1.len() implies ns1[k] == ns2[k] by {
            if k > 0 {
                assert(ns1[k] == t1[k - 1]);
                assert(ns2[k] == t2[k - 1]);
            }
        }
        assert(ns1 =~= ns2);
    }
}

/// Where `first_greater` stops: everything before it is below `j`'s name,
/// and what it stops at is above.
proof fn lemma_first_greater_split(t: TreeS, s: Seq<int>, j: int, k: int)
    requires 0 <= k <= s.len(), t.sorted(s), forall|q: int| 0 <= q < s.len() ==> t.id(#[trigger] s[q]) != t.id(j)
    ensures ({
        let pos = t.first_greater(s, j, k);
        &&& k <= pos <= s.len()
        &&& forall|q: int| k <= q < pos ==> TreeS::id_lt(t.id(#[trigger] s[q]), t.id(j))
        &&& pos < s.len() ==> TreeS::id_lt(t.id(j), t.id(s[pos]))
    })
    decreases s.len() - k
{
    if k < s.len() && !TreeS::id_lt(t.id(j), t.id(s[k])) {
        lemma_id_lt_total(t.id(j), t.id(s[k]));
        lemma_first_greater_split(t, s, j, k + 1);
    }
}

pub proof fn lemma_insert_sorted_sorted(t: TreeS, s: Seq<int>, j: int)
    requires t.sorted(s), forall|q: int| 0 <= q < s.len() ==> t.id(#[trigger] s[q]) != t.id(j)
    ensures t.sorted(t.insert_sorted(s, j))
{
    lemma_first_greater_split(t, s, j, 0);
    let pos = t.first_greater(s, j, 0);
    let out = s.insert(pos, j);
    assert forall|a: int, b: int| 0 <= a < b < out.len() implies TreeS::id_lt(t.id(out[a]), t.id(out[b])) by {
        if b < pos {
            assert(out[a] == s[a] && out[b] == s[b]);
        } else if b == pos {
            assert(out[a] == s[a] && out[b] == j);
        } else if a < pos {
            assert(out[a] == s[a] && out[b] == s[b - 1]);
            if pos < s.len() { lemma_id_lt_trans(t.id(s[a]), t.id(j), t.id(s[pos])); }
            assert(TreeS::id_lt(t.id(s[a]), t.id(s[b - 1])));
        } else if a == pos {
            assert(out[a] == j && out[b] == s[b - 1]);
            if b - 1 > pos { lemma_id_lt_trans(t.id(j), t.id(s[pos]), t.id(s[b - 1])); }
        } else {
            assert(out[a] == s[a - 1] && out[b] == s[b - 1]);
        }
    }
}

/// Under unique names, every sibling list `attach` builds is sorted.
pub proof fn lemma_children_upto_sorted(t: TreeS, parent: Option<int>, right: bool, k: int)
    requires 0 <= k <= t.len(), forall|i: int, j: int| t.node(i) && t.node(j) && i != j ==> t.id(i) != t.id(j)
    ensures t.sorted(t.children_upto(parent, right, k))
    decreases k
{
    if k > 0 {
        lemma_children_upto_sorted(t, parent, right, k - 1);
        if t.hangs(k - 1, parent, right) {
            lemma_children_upto_hang(t, parent, right, k - 1);
            lemma_insert_sorted_sorted(t, t.children_upto(parent, right, k - 1), k - 1);
        }
    }
}

pub proof fn lemma_children_sorted(t: TreeS, g: GraphS, parent: Option<int>, right: bool)
    requires t.wf(g)
    ensures t.sorted(t.children(parent, right)), ids_sorted(t.names(t.children(parent, right)))
{
    lemma_children_upto_sorted(t, parent, right, t.len());
}

// ---------------------------------------------------------------------------
// Agreement on a set of events, and the restricted reading.
// ---------------------------------------------------------------------------

/// Closed under causal past.
pub open spec fn closed(g: GraphS, s: Set<int>) -> bool {
    forall|e: int, o: int| s.contains(e) && g.event(e) && g.event(o) && #[trigger] g.knows(e, o) ==> s.contains(o)
}

impl TreeS {
    pub open spec fn parent_name(self, i: int) -> Option<Name> {
        match self.nodes[i].parent {
            None => None,
            Some(p) => Some(self.id(p)),
        }
    }

    /// The indices among `s` whose author is in `set`.
    pub open spec fn in_set(self, set: Set<int>, s: Seq<int>) -> Seq<int> {
        sel(s, |i: int| set.contains(self.nodes[i].author))
    }

    /// `read`, emitting only elements authored in `set`.
    pub open spec fn sub_read(self, set: Set<int>, i: int) -> Seq<int>
        decreases self.len() - i, 1int, 0int
    {
        if !self.node(i) {
            Seq::empty()
        } else {
            self.sub_read_all(set, self.children(Some(i), false), i)
                + (if set.contains(self.nodes[i].author) { seq![i] } else { Seq::<int>::empty() })
                + self.sub_read_all(set, self.children(Some(i), true), i)
        }
    }

    pub open spec fn sub_read_all(self, set: Set<int>, siblings: Seq<int>, above: int) -> Seq<int>
        decreases self.len() - above, 0int, siblings.len()
    {
        if siblings.len() == 0 {
            Seq::empty()
        } else {
            let first = siblings[0];
            let rest = self.sub_read_all(set, siblings.drop_first(), above);
            if above < first < self.len() { self.sub_read(set, first) + rest } else { rest }
        }
    }

    pub open spec fn sub_order(self, set: Set<int>) -> Seq<int> {
        self.sub_read_all(set, self.children(None, true), -1)
    }
}

/// `j` in `u` is `i` in `t`, as far as events in `set` can tell.
pub open spec fn same_node(t: TreeS, u: TreeS, set: Set<int>, i: int, j: int) -> bool {
    &&& u.id(j) == t.id(i)
    &&& u.nodes[j].item == t.nodes[i].item
    &&& u.nodes[j].right == t.nodes[i].right
    &&& u.parent_name(j) == t.parent_name(i)
    &&& forall|d: int| set.contains(d) ==> (u.nodes[j].deleted.contains(d) <==> t.nodes[i].deleted.contains(d))
}

/// `t` and `u` hold the same elements authored in `set`, at the same
/// places, removed by the same events of `set`.
pub open spec fn agree(t: TreeS, u: TreeS, set: Set<int>) -> bool {
    &&& forall|i: int| t.node(i) && set.contains((#[trigger] t.nodes[i]).author)
            ==> exists|j: int| u.node(j) && same_node(t, u, set, i, j)
    &&& forall|j: int| u.node(j) && set.contains((#[trigger] u.nodes[j]).author)
            ==> exists|i: int| t.node(i) && same_node(t, u, set, i, j)
}

/// Under unique names, a name picks out one index.
pub proof fn lemma_named_unique(t: TreeS, g: GraphS, a: int, b: int)
    requires t.wf(g), t.node(a), t.node(b), t.id(a) == t.id(b)
    ensures a == b
{
}

/// Everything that hangs somewhere is in that sibling list.
pub proof fn lemma_children_upto_complete(t: TreeS, parent: Option<int>, right: bool, k: int, c: int)
    requires 0 <= c < k <= t.len(), t.hangs(c, parent, right)
    ensures t.children_upto(parent, right, k).contains(c)
    decreases k
{
    if c == k - 1 {
        let before = t.children_upto(parent, right, k - 1);
        lemma_first_greater_bounds(t, before, c, 0);
        let pos = t.first_greater(before, c, 0);
        assert(before.insert(pos, c)[pos] == c);
    } else {
        lemma_children_upto_complete(t, parent, right, k - 1, c);
        let before = t.children_upto(parent, right, k - 1);
        if t.hangs(k - 1, parent, right) {
            lemma_first_greater_bounds(t, before, k - 1, 0);
            let pos = t.first_greater(before, k - 1, 0);
            let q = choose|q: int| 0 <= q < before.len() && before[q] == c;
            let after = before.insert(pos, k - 1);
            if q < pos { assert(after[q] == c); } else { assert(after[q + 1] == c); }
        }
    }
}

pub proof fn lemma_children_complete(t: TreeS, parent: Option<int>, right: bool, c: int)
    requires t.hangs(c, parent, right)
    ensures t.children(parent, right).contains(c)
{
    lemma_children_upto_complete(t, parent, right, t.len(), c);
}

/// A filter of a sorted list is sorted.
pub proof fn lemma_sel_sorted(t: TreeS, s: Seq<int>, p: spec_fn(int) -> bool)
    requires t.sorted(s)
    ensures t.sorted(sel(s, p))
{
    lemma_sel_sub(s, p);
    assert forall|a: int, b: int| 0 <= a < b < sel(s, p).len() implies TreeS::id_lt(t.id(sel(s, p)[a]), t.id(sel(s, p)[b])) by {
        let (ia, ib) = (src(s, p, a), src(s, p, b));
        assert(s[ia] == sel(s, p)[a] && s[ib] == sel(s, p)[b] && ia < ib);
    }
}

/// Filtering twice is filtering once by both.
pub proof fn lemma_sel_sel(s: Seq<int>, p: spec_fn(int) -> bool, q: spec_fn(int) -> bool)
    ensures sel(sel(s, p), q) == sel(s, |i: int| p(i) && q(i))
    decreases s.len()
{
    if s.len() > 0 {
        lemma_sel_sel(s.drop_last(), p, q);
        let r = sel(s.drop_last(), p);
        if p(s.last()) {
            assert(sel(s, p) == r.push(s.last()));
            assert(r.push(s.last()).drop_last() =~= r);
            assert(r.push(s.last()).last() == s.last());
        }
    }
}

/// Lemma R1: the restricted reading is the reading, restricted.
pub proof fn lemma_sub_read_is_sel(t: TreeS, set: Set<int>, i: int)
    ensures t.in_set(set, t.read(i)) == t.sub_read(set, i)
    decreases t.len() - i, 1int, 0int
{
    if t.node(i) {
        let p = |i: int| set.contains(t.nodes[i].author);
        let (lc, rc) = (t.children(Some(i), false), t.children(Some(i), true));
        lemma_sub_read_all_is_sel(t, set, lc, i);
        lemma_sub_read_all_is_sel(t, set, rc, i);
        lemma_sel_add(t.read_all(lc, i) + seq![i], t.read_all(rc, i), p);
        lemma_sel_add(t.read_all(lc, i), seq![i], p);
        lemma_sel_single(i, p);
    }
}

pub proof fn lemma_sub_read_all_is_sel(t: TreeS, set: Set<int>, siblings: Seq<int>, above: int)
    ensures t.in_set(set, t.read_all(siblings, above)) == t.sub_read_all(set, siblings, above)
    decreases t.len() - above, 0int, siblings.len()
{
    let p = |i: int| set.contains(t.nodes[i].author);
    if siblings.len() == 0 {
        assert(t.read_all(siblings, above) =~= Seq::<int>::empty());
    } else {
        let first = siblings[0];
        lemma_sub_read_all_is_sel(t, set, siblings.drop_first(), above);
        if above < first < t.len() {
            lemma_sub_read_is_sel(t, set, first);
            lemma_sel_add(t.read(first), t.read_all(siblings.drop_first(), above), p);
        }
    }
}

/// Lemma R2: outside the set, a subtree reads as nothing — its elements'
/// authors all know the root's, so none of them is in a closed set that
/// leaves the root out.
pub proof fn lemma_sub_read_outside(t: TreeS, g: GraphS, set: Set<int>, i: int)
    requires t.wf(g), g.wf(), closed(g, set), t.node(i), !set.contains(t.nodes[i].author)
    ensures t.sub_read(set, i) == Seq::<int>::empty()
    decreases t.len() - i, 1int, 0int
{
    lemma_children_nodes(t, Some(i), false);
    lemma_children_nodes(t, Some(i), true);
    lemma_sub_read_all_outside(t, g, set, t.children(Some(i), false), i);
    lemma_sub_read_all_outside(t, g, set, t.children(Some(i), true), i);
    assert(t.sub_read(set, i) =~= Seq::<int>::empty());
}

pub proof fn lemma_sub_read_all_outside(t: TreeS, g: GraphS, set: Set<int>, siblings: Seq<int>, above: int)
    requires
        t.wf(g), g.wf(), closed(g, set), t.node(above), !set.contains(t.nodes[above].author),
        forall|q: int| 0 <= q < siblings.len() ==> t.node(#[trigger] siblings[q]) && t.nodes[siblings[q]].parent == Some(above),
    ensures t.sub_read_all(set, siblings, above) == Seq::<int>::empty()
    decreases t.len() - above, 0int, siblings.len()
{
    if siblings.len() > 0 {
        let first = siblings[0];
        lemma_sub_read_all_outside(t, g, set, siblings.drop_first(), above);
        if above < first < t.len() {
            // `first`'s author knows `above`'s; closed would pull `above`'s in.
            assert(g.knows(t.nodes[first].author, t.nodes[above].author));
            assert(!set.contains(t.nodes[first].author));
            lemma_sub_read_outside(t, g, set, first);
        }
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
    reveal_with_fuel(sel, 2);
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
        reveal_with_fuel(sel, 3);
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
        reveal_with_fuel(sel, 3);
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
    assert(sel(t.order(), |i: int| t.standing(i)) == seq![0int, xi, yi]) by {
        reveal_with_fuel(sel, 4);
        assert(t.standing(0) && t.standing(1) && t.standing(2));
        assert(sel(t.order(), |i: int| t.standing(i)) =~= seq![0int, xi, yi]);
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
