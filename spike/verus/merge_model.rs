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
pub open spec fn closed(g: GraphS, s: ISet<int>) -> bool {
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
    pub open spec fn in_set(self, set: ISet<int>, s: Seq<int>) -> Seq<int> {
        sel(s, |i: int| set.contains(self.nodes[i].author))
    }

    /// `read`, emitting only elements authored in `set`.
    pub open spec fn sub_read(self, set: ISet<int>, i: int) -> Seq<int>
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

    pub open spec fn sub_read_all(self, set: ISet<int>, siblings: Seq<int>, above: int) -> Seq<int>
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

    pub open spec fn sub_order(self, set: ISet<int>) -> Seq<int> {
        self.sub_read_all(set, self.children(None, true), -1)
    }
}

/// Removed by the same events of `set`. Opaque: this quantifier is the
/// one Z3 will instantiate a million times if it is allowed to.
#[verifier::opaque]
pub open spec fn same_deleted(t: TreeS, u: TreeS, set: ISet<int>, i: int, j: int) -> bool {
    forall|d: int| #[trigger] set.contains(d) ==> (u.nodes[j].deleted.contains(d) <==> t.nodes[i].deleted.contains(d))
}

/// `j` in `u` is `i` in `t`, as far as events in `set` can tell.
pub open spec fn same_node(t: TreeS, u: TreeS, set: ISet<int>, i: int, j: int) -> bool {
    &&& u.id(j) == t.id(i)
    &&& u.nodes[j].item == t.nodes[i].item
    &&& u.nodes[j].right == t.nodes[i].right
    &&& u.parent_name(j) == t.parent_name(i)
    &&& same_deleted(t, u, set, i, j)
}

/// Every element of `t` authored in `set` has a twin in `u`.
pub open spec fn half(t: TreeS, u: TreeS, set: ISet<int>) -> bool {
    forall|i: int| t.node(i) && #[trigger] set.contains(t.nodes[i].author)
        ==> exists|j: int| u.node(j) && same_node(t, u, set, i, j)
}

/// `t` and `u` hold the same elements authored in `set`, at the same
/// places, removed by the same events of `set`.
pub open spec fn agree(t: TreeS, u: TreeS, set: ISet<int>) -> bool {
    half(t, u, set) && half(u, t, set)
}

/// Being twins is symmetric.
pub proof fn lemma_same_node_sym(t: TreeS, u: TreeS, set: ISet<int>, i: int, j: int)
    requires same_node(u, t, set, j, i)
    ensures same_node(t, u, set, i, j)
{
    reveal(same_deleted);
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
pub proof fn lemma_sel_sel(s: Seq<int>, p: spec_fn(int) -> bool, q: spec_fn(int) -> bool, r: spec_fn(int) -> bool)
    requires forall|i: int| #[trigger] r(i) <==> p(i) && q(i)
    ensures sel(sel(s, p), q) == sel(s, r)
    decreases s.len()
{
    if s.len() > 0 {
        lemma_sel_sel(s.drop_last(), p, q, r);
        let r = sel(s.drop_last(), p);
        if p(s.last()) {
            assert(sel(s, p) == r.push(s.last()));
            assert(r.push(s.last()).drop_last() =~= r);
            assert(r.push(s.last()).last() == s.last());
        }
    }
}

/// Lemma R1: the restricted reading is the reading, restricted.
pub proof fn lemma_sub_read_is_sel(t: TreeS, set: ISet<int>, i: int)
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

pub proof fn lemma_sub_read_all_is_sel(t: TreeS, set: ISet<int>, siblings: Seq<int>, above: int)
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
pub proof fn lemma_sub_read_outside(t: TreeS, g: GraphS, set: ISet<int>, i: int)
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

pub proof fn lemma_sub_read_all_outside(t: TreeS, g: GraphS, set: ISet<int>, siblings: Seq<int>, above: int)
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
// R3–R5: trees that agree on a closed set read the same names from it.
// ---------------------------------------------------------------------------

pub proof fn lemma_names_add(t: TreeS, a: Seq<int>, b: Seq<int>)
    ensures t.names(a + b) == t.names(a) + t.names(b)
{
    assert(t.names(a + b) =~= t.names(a) + t.names(b));
}

pub proof fn lemma_names_contains(t: TreeS, s: Seq<int>, n: Name)
    ensures t.names(s).contains(n) <==> exists|q: int| 0 <= q < s.len() && t.id(#[trigger] s[q]) == n
{
    if t.names(s).contains(n) {
        let q = choose|q: int| 0 <= q < t.names(s).len() && t.names(s)[q] == n;
        assert(t.id(s[q]) == n);
    }
    if exists|q: int| 0 <= q < s.len() && t.id(#[trigger] s[q]) == n {
        let q = choose|q: int| 0 <= q < s.len() && t.id(#[trigger] s[q]) == n;
        assert(t.names(s)[q] == n);
    }
}

pub proof fn lemma_sorted_names(t: TreeS, s: Seq<int>)
    requires t.sorted(s)
    ensures ids_sorted(t.names(s))
{
    assert forall|a: int, b: int| 0 <= a < b < t.names(s).len() implies TreeS::id_lt(t.names(s)[a], t.names(s)[b]) by {
        assert(t.names(s)[a] == t.id(s[a]));
        assert(t.names(s)[b] == t.id(s[b]));
    }
}

/// The parents a pair of twins may hang from: both the root, or twins.
pub open spec fn twin_parents(t: TreeS, u: TreeS, g: GraphS, pt: Option<int>, pu: Option<int>) -> bool {
    match (pt, pu) {
        (None, None) => true,
        (Some(i), Some(j)) => t.node(i) && u.node(j) && t.id(i) == u.id(j),
        _ => false,
    }
}

/// Lemma R3: under twin parents, the children authored in the set have the
/// same names in the same order.
pub proof fn lemma_children_names_agree(t: TreeS, u: TreeS, g: GraphS, set: ISet<int>, pt: Option<int>, pu: Option<int>, r: bool)
    requires t.wf(g), u.wf(g), g.wf(), closed(g, set), agree(t, u, set), twin_parents(t, u, g, pt, pu)
    ensures t.names(t.in_set(set, t.children(pt, r))) == u.names(u.in_set(set, u.children(pu, r)))
{
    let (ct, cu) = (t.children(pt, r), u.children(pu, r));
    let (xt, xu) = (t.in_set(set, ct), u.in_set(set, cu));
    let (pt_, pu_) = (|i: int| set.contains(t.nodes[i].author), |i: int| set.contains(u.nodes[i].author));
    lemma_children_sorted(t, g, pt, r);
    lemma_children_sorted(u, g, pu, r);
    lemma_sel_sorted(t, ct, pt_);
    lemma_sel_sorted(u, cu, pu_);
    lemma_sorted_names(t, xt);
    lemma_sorted_names(u, xu);
    lemma_children_nodes(t, pt, r);
    lemma_children_nodes(u, pu, r);
    lemma_sel_sub(ct, pt_);
    lemma_sel_sub(cu, pu_);
    assert forall|n: Name| t.names(xt).contains(n) <==> u.names(xu).contains(n) by {
        lemma_names_contains(t, xt, n);
        lemma_names_contains(u, xu, n);
        if t.names(xt).contains(n) {
            let q = choose|q: int| 0 <= q < xt.len() && t.id(#[trigger] xt[q]) == n;
            let c = xt[q];
            let k = src(ct, pt_, q);
            assert(ct[k] == c && pt_(c));
            assert(t.hangs(c, pt, r));
            let c2 = choose|j: int| u.node(j) && same_node(t, u, set, c, j);
            assert(u.hangs(c2, pu, r)) by {
                match (pt, pu) {
                    (None, None) => {}
                    (Some(i), Some(j)) => {
                        let p2 = u.nodes[c2].parent->Some_0;
                        lemma_named_unique(u, g, p2, j);
                    }
                    _ => {}
                }
            }
            lemma_children_complete(u, pu, r, c2);
            assert(pu_(c2));
            assert(xu.contains(c2));
            let q2 = choose|q2: int| 0 <= q2 < xu.len() && xu[q2] == c2;
            assert(u.id(xu[q2]) == n);
        }
        if u.names(xu).contains(n) {
            let q = choose|q: int| 0 <= q < xu.len() && u.id(#[trigger] xu[q]) == n;
            let c = xu[q];
            let k = src(cu, pu_, q);
            assert(cu[k] == c && pu_(c));
            assert(u.hangs(c, pu, r));
            let c2 = choose|i: int| t.node(i) && same_node(u, t, set, c, i);
            lemma_same_node_sym(t, u, set, c2, c);
            assert(t.hangs(c2, pt, r)) by {
                match (pt, pu) {
                    (None, None) => {}
                    (Some(i), Some(j)) => {
                        let p2 = t.nodes[c2].parent->Some_0;
                        lemma_named_unique(t, g, p2, i);
                    }
                    _ => {}
                }
            }
            lemma_children_complete(t, pt, r, c2);
            assert(pt_(c2));
            assert(xt.contains(c2));
            let q2 = choose|q2: int| 0 <= q2 < xt.len() && xt[q2] == c2;
            assert(t.id(xt[q2]) == n);
        }
    }
    lemma_sorted_same_members(t.names(xt), u.names(xu));
}

/// Siblings outside the set read as nothing, so a list reads as its
/// in-set part does.
pub proof fn lemma_sub_read_all_restrict(t: TreeS, g: GraphS, set: ISet<int>, siblings: Seq<int>, above: int)
    requires
        t.wf(g), g.wf(), closed(g, set),
        forall|q: int| 0 <= q < siblings.len() ==> t.node(#[trigger] siblings[q]) && above < siblings[q],
    ensures t.sub_read_all(set, siblings, above) == t.sub_read_all(set, t.in_set(set, siblings), above)
    decreases siblings.len()
{
    let p = |i: int| set.contains(t.nodes[i].author);
    if siblings.len() == 0 {
        assert(t.in_set(set, siblings) == siblings);
    } else {
        let first = siblings[0];
        let rest = siblings.drop_first();
        lemma_sub_read_all_restrict(t, g, set, rest, above);
        assert(siblings =~= seq![first] + rest);
        lemma_sel_add(seq![first], rest, p);
        lemma_sel_single(first, p);
        if p(first) {
            assert(t.in_set(set, siblings) == seq![first] + t.in_set(set, rest));
            assert((seq![first] + t.in_set(set, rest))[0] == first);
            assert((seq![first] + t.in_set(set, rest)).drop_first() =~= t.in_set(set, rest));
        } else {
            assert(t.in_set(set, siblings) =~= t.in_set(set, rest));
            lemma_sub_read_outside(t, g, set, first);
            assert(t.sub_read_all(set, siblings, above) =~= t.sub_read_all(set, rest, above));
        }
    }
}

/// The in-set children of a node are nodes attached after it.
pub proof fn lemma_in_set_children(t: TreeS, g: GraphS, set: ISet<int>, parent: Option<int>, r: bool, above: int)
    requires t.wf(g), match parent { Some(i) => i == above, None => above == -1 }
    ensures forall|q: int| 0 <= q < t.in_set(set, t.children(parent, r)).len()
        ==> t.node(#[trigger] t.in_set(set, t.children(parent, r))[q]) && above < t.in_set(set, t.children(parent, r))[q]
{
    let c = t.children(parent, r);
    let p = |i: int| set.contains(t.nodes[i].author);
    lemma_children_nodes(t, parent, r);
    lemma_sel_sub(c, p);
    assert forall|q: int| 0 <= q < sel(c, p).len() implies t.node(#[trigger] sel(c, p)[q]) && above < sel(c, p)[q] by {
        let k = src(c, p, q);
        assert(t.hangs(c[k], parent, r));
    }
}

/// Lemma R4: twins read the same names from the set.
pub proof fn lemma_sub_read_agree(t: TreeS, u: TreeS, g: GraphS, set: ISet<int>, i: int, j: int)
    requires t.wf(g), u.wf(g), g.wf(), closed(g, set), agree(t, u, set), t.node(i), u.node(j), t.id(i) == u.id(j)
    ensures t.names(t.sub_read(set, i)) == u.names(u.sub_read(set, j))
    decreases t.len() - i, 1int, 0int
{
    let (lt, rt) = (t.children(Some(i), false), t.children(Some(i), true));
    let (lu, ru) = (u.children(Some(j), false), u.children(Some(j), true));
    lemma_children_nodes(t, Some(i), false);
    lemma_children_nodes(t, Some(i), true);
    lemma_children_nodes(u, Some(j), false);
    lemma_children_nodes(u, Some(j), true);
    lemma_sub_read_all_restrict(t, g, set, lt, i);
    lemma_sub_read_all_restrict(t, g, set, rt, i);
    lemma_sub_read_all_restrict(u, g, set, lu, j);
    lemma_sub_read_all_restrict(u, g, set, ru, j);
    lemma_children_names_agree(t, u, g, set, Some(i), Some(j), false);
    lemma_children_names_agree(t, u, g, set, Some(i), Some(j), true);
    lemma_in_set_children(t, g, set, Some(i), false, i);
    lemma_in_set_children(t, g, set, Some(i), true, i);
    lemma_in_set_children(u, g, set, Some(j), false, j);
    lemma_in_set_children(u, g, set, Some(j), true, j);
    lemma_sub_read_all_agree(t, u, g, set, t.in_set(set, lt), u.in_set(set, lu), i, j);
    lemma_sub_read_all_agree(t, u, g, set, t.in_set(set, rt), u.in_set(set, ru), i, j);
    let mid_t: Seq<int> = if set.contains(t.nodes[i].author) { seq![i] } else { Seq::<int>::empty() };
    let mid_u: Seq<int> = if set.contains(u.nodes[j].author) { seq![j] } else { Seq::<int>::empty() };
    assert(t.names(mid_t) =~= u.names(mid_u));
    lemma_names_add(t, t.sub_read_all(set, lt, i), mid_t);
    lemma_names_add(t, t.sub_read_all(set, lt, i) + mid_t, t.sub_read_all(set, rt, i));
    lemma_names_add(u, u.sub_read_all(set, lu, j), mid_u);
    lemma_names_add(u, u.sub_read_all(set, lu, j) + mid_u, u.sub_read_all(set, ru, j));
}

/// Two same-named lists of in-set children read the same names.
pub proof fn lemma_sub_read_all_agree(t: TreeS, u: TreeS, g: GraphS, set: ISet<int>, ct: Seq<int>, cu: Seq<int>, above_t: int, above_u: int)
    requires
        t.wf(g), u.wf(g), g.wf(), closed(g, set), agree(t, u, set),
        t.names(ct) == u.names(cu),
        forall|q: int| 0 <= q < ct.len() ==> t.node(#[trigger] ct[q]) && above_t < ct[q],
        forall|q: int| 0 <= q < cu.len() ==> u.node(#[trigger] cu[q]) && above_u < cu[q],
    ensures t.names(t.sub_read_all(set, ct, above_t)) == u.names(u.sub_read_all(set, cu, above_u))
    decreases t.len() - above_t, 0int, ct.len()
{
    assert(t.names(ct).len() == ct.len());
    assert(u.names(cu).len() == cu.len());
    if ct.len() > 0 {
        assert(t.names(ct)[0] == t.id(ct[0]));
        assert(u.names(cu)[0] == u.id(cu[0]));
        assert forall|k: int| 0 <= k < ct.len() implies t.id(#[trigger] ct[k]) == u.id(cu[k]) by {
            assert(t.names(ct)[k] == t.id(ct[k]));
            assert(u.names(cu)[k] == u.id(cu[k]));
        }
        assert(t.names(ct.drop_first()) =~= u.names(cu.drop_first()));
        lemma_sub_read_agree(t, u, g, set, ct[0], cu[0]);
        lemma_sub_read_all_agree(t, u, g, set, ct.drop_first(), cu.drop_first(), above_t, above_u);
        lemma_names_add(t, t.sub_read(set, ct[0]), t.sub_read_all(set, ct.drop_first(), above_t));
        lemma_names_add(u, u.sub_read(set, cu[0]), u.sub_read_all(set, cu.drop_first(), above_u));
    }
}

/// Lemma R5: the whole restricted reading agrees.
pub proof fn lemma_sub_order_agree(t: TreeS, u: TreeS, g: GraphS, set: ISet<int>)
    requires t.wf(g), u.wf(g), g.wf(), closed(g, set), agree(t, u, set)
    ensures t.names(t.sub_order(set)) == u.names(u.sub_order(set))
{
    let (ct, cu) = (t.children(None, true), u.children(None, true));
    lemma_children_nodes(t, None, true);
    lemma_children_nodes(u, None, true);
    lemma_sub_read_all_restrict(t, g, set, ct, -1);
    lemma_sub_read_all_restrict(u, g, set, cu, -1);
    lemma_children_names_agree(t, u, g, set, None, None, true);
    lemma_in_set_children(t, g, set, None, true, -1);
    lemma_in_set_children(u, g, set, None, true, -1);
    lemma_sub_read_all_agree(t, u, g, set, t.in_set(set, ct), u.in_set(set, cu), -1, -1);
}

/// The events strictly in `e`'s past: what `visible` counts into.
pub open spec fn past(g: GraphS, e: int) -> ISet<int> {
    ISet::new(|o: int| g.saw(e, o))
}

pub proof fn lemma_past_closed(g: GraphS, e: int)
    requires g.wf(), g.event(e)
    ensures closed(g, past(g, e))
{
    assert forall|a: int, o: int| past(g, e).contains(a) && g.event(a) && g.event(o) && #[trigger] g.knows(a, o)
        implies past(g, e).contains(o) by {
        assert(g.knows(e, o));
        if o == e { assert(g.knows(a, e) && g.knows(e, a)); }
    }
}

/// The twin of `i` is the one index of `u` carrying its name.
pub proof fn lemma_twin(t: TreeS, u: TreeS, g: GraphS, set: ISet<int>, i: int, j: int)
    requires u.wf(g), agree(t, u, set), t.node(i), set.contains(t.nodes[i].author), u.node(j), u.id(j) == t.id(i)
    ensures same_node(t, u, set, i, j)
{
    let j2 = choose|j2: int| u.node(j2) && same_node(t, u, set, i, j2);
    lemma_named_unique(u, g, j, j2);
}

/// Lemma R: trees that agree on an event's past show it the same view.
pub proof fn lemma_visible_agree(t: TreeS, u: TreeS, g: GraphS, e: int)
    requires t.wf(g), u.wf(g), g.wf(), g.event(e), agree(t, u, past(g, e))
    ensures t.names(t.visible(g, e)) == u.names(u.visible(g, e))
{
    reveal(TreeS::visible);
    reveal(TreeS::order);
    let set = past(g, e);
    lemma_past_closed(g, e);
    let (seen_t, seen_u) = (|i: int| t.seen(g, e, i), |i: int| u.seen(g, e, i));
    let (in_t, in_u) = (|i: int| set.contains(t.nodes[i].author), |i: int| set.contains(u.nodes[i].author));
    let kept_t = |i: int| forall|d: int| set.contains(d) ==> !t.nodes[i].deleted.contains(d);
    let kept_u = |i: int| forall|d: int| set.contains(d) ==> !u.nodes[i].deleted.contains(d);
    // `seen` is "in the past, and nothing in the past removed it".
    assert forall|i: int| #[trigger] seen_t(i) <==> in_t(i) && kept_t(i) by {
        if in_t(i) && kept_t(i) {
            assert forall|d: int| t.nodes[i].deleted.contains(d) implies !g.saw(e, d) by {
                if g.saw(e, d) { assert(set.contains(d)); }
            }
        }
        if seen_t(i) {
            assert forall|d: int| set.contains(d) implies !t.nodes[i].deleted.contains(d) by {
                assert(g.saw(e, d));
            }
        }
    }
    assert forall|i: int| #[trigger] seen_u(i) <==> in_u(i) && kept_u(i) by {
        if in_u(i) && kept_u(i) {
            assert forall|d: int| u.nodes[i].deleted.contains(d) implies !g.saw(e, d) by {
                if g.saw(e, d) { assert(set.contains(d)); }
            }
        }
        if seen_u(i) {
            assert forall|d: int| set.contains(d) implies !u.nodes[i].deleted.contains(d) by {
                assert(g.saw(e, d));
            }
        }
    }
    lemma_sel_sel(t.order(), in_t, kept_t, seen_t);
    lemma_sel_sel(u.order(), in_u, kept_u, seen_u);
    lemma_sub_read_all_is_sel(t, set, t.children(None, true), -1);
    lemma_sub_read_all_is_sel(u, set, u.children(None, true), -1);
    assert(sel(t.order(), in_t) == t.sub_order(set));
    assert(sel(u.order(), in_u) == u.sub_order(set));
    lemma_sub_order_agree(t, u, g, set);
    let (x, y) = (t.sub_order(set), u.sub_order(set));
    assert(t.names(x).len() == x.len());
    assert(u.names(y).len() == y.len());
    assert(x.len() == y.len());
    lemma_read_all_nodes(t, t.children(None, true), -1);
    lemma_read_all_nodes(u, u.children(None, true), -1);
    lemma_sel_sub(t.order(), in_t);
    lemma_sel_sub(u.order(), in_u);
    assert forall|k: int| 0 <= k < x.len() implies (kept_t(#[trigger] x[k]) <==> kept_u(y[k])) by {
        assert(t.names(x)[k] == t.id(x[k]));
        assert(u.names(y)[k] == u.id(y[k]));
        let (a, b) = (src(t.order(), in_t, k), src(u.order(), in_u, k));
        assert(t.node(x[k]) && in_t(x[k]));
        assert(u.node(y[k]));
        lemma_twin(t, u, g, set, x[k], y[k]);
        reveal(same_deleted);
        assert forall|d: int| #[trigger] set.contains(d) implies (u.nodes[y[k]].deleted.contains(d) <==> t.nodes[x[k]].deleted.contains(d)) by {}
    }
    lemma_sel_names(t, u, x, y, kept_t, kept_u);
}

// ---------------------------------------------------------------------------
// Lemma A: `anchor` reads only what the event knows.
// ---------------------------------------------------------------------------

/// What `e` knows: its past and itself. The set an insertion is placed
/// against.
pub open spec fn known(g: GraphS, e: int) -> ISet<int> {
    ISet::new(|o: int| g.knows(e, o))
}

pub proof fn lemma_known_closed(g: GraphS, e: int)
    requires g.wf(), g.event(e)
    ensures closed(g, known(g, e))
{
    assert forall|a: int, o: int| known(g, e).contains(a) && g.event(a) && g.event(o) && #[trigger] g.knows(a, o)
        implies known(g, e).contains(o) by {
        assert(g.knows(e, o));
    }
}

/// `same_deleted` is monotone in the set.
pub proof fn lemma_same_deleted_mono(t: TreeS, u: TreeS, big: ISet<int>, small: ISet<int>, i: int, j: int)
    requires same_deleted(t, u, big, i, j), forall|o: int| #[trigger] small.contains(o) ==> big.contains(o)
    ensures same_deleted(t, u, small, i, j)
{
    reveal(same_deleted);
    assert forall|d: int| #[trigger] small.contains(d) implies (u.nodes[j].deleted.contains(d) <==> t.nodes[i].deleted.contains(d)) by {
        assert(big.contains(d));
    }
}

/// Each half of agreement is monotone in the set.
pub proof fn lemma_half_mono(t: TreeS, u: TreeS, big: ISet<int>, small: ISet<int>)
    requires half(t, u, big), forall|o: int| #[trigger] small.contains(o) ==> big.contains(o)
    ensures half(t, u, small)
{
    assert forall|i: int| t.node(i) && #[trigger] small.contains(t.nodes[i].author)
        implies exists|j: int| u.node(j) && same_node(t, u, small, i, j) by {
        assert(big.contains(t.nodes[i].author));
        let j = choose|j: int| u.node(j) && same_node(t, u, big, i, j);
        lemma_same_deleted_mono(t, u, big, small, i, j);
        assert(same_node(t, u, small, i, j));
    }
}

/// Agreement is monotone in the set.
pub proof fn lemma_agree_mono(t: TreeS, u: TreeS, big: ISet<int>, small: ISet<int>)
    requires agree(t, u, big), forall|o: int| #[trigger] small.contains(o) ==> big.contains(o)
    ensures agree(t, u, small)
{
    lemma_half_mono(t, u, big, small);
    lemma_half_mono(u, t, big, small);
}

/// `first_known` is the head of the known part of the list.
pub proof fn lemma_first_known_head(t: TreeS, g: GraphS, e: int, siblings: Seq<int>)
    ensures ({
        let kept = t.in_set(known(g, e), siblings);
        t.first_known(g, e, siblings) == if kept.len() == 0 { None } else { Some(kept[0]) }
    })
    decreases siblings.len()
{
    let p = |i: int| known(g, e).contains(t.nodes[i].author);
    if siblings.len() == 0 {
        assert(sel(siblings, p) == siblings);
    } else {
        let first = siblings[0];
        let rest = siblings.drop_first();
        lemma_first_known_head(t, g, e, rest);
        assert(siblings =~= seq![first] + rest);
        lemma_sel_add(seq![first], rest, p);
        lemma_sel_single(first, p);
        if p(first) {
            assert((seq![first] + sel(rest, p))[0] == first);
        } else {
            assert(sel(siblings, p) =~= sel(rest, p));
        }
    }
}

/// Twin lists have twin heads.
pub proof fn lemma_heads_twin(t: TreeS, u: TreeS, x: Seq<int>, y: Seq<int>)
    requires t.names(x) == u.names(y)
    ensures x.len() == y.len(), x.len() > 0 ==> t.id(x[0]) == u.id(y[0])
{
    assert(t.names(x).len() == x.len());
    assert(u.names(y).len() == y.len());
    if x.len() > 0 {
        assert(t.names(x)[0] == t.id(x[0]));
        assert(u.names(y)[0] == u.id(y[0]));
    }
}

pub proof fn lemma_leftmost_known_agree(t: TreeS, u: TreeS, g: GraphS, e: int, at: int, au: int)
    requires t.wf(g), u.wf(g), g.wf(), g.event(e), agree(t, u, known(g, e)), t.node(at), u.node(au), t.id(at) == u.id(au)
    ensures ({
        let (rt, ru) = (t.leftmost_known(g, e, at), u.leftmost_known(g, e, au));
        t.node(rt) && u.node(ru) && t.id(rt) == u.id(ru)
    })
    decreases t.len() - at
{
    lemma_known_closed(g, e);
    let set = known(g, e);
    let (ct, cu) = (t.children(Some(at), false), u.children(Some(au), false));
    lemma_first_known_head(t, g, e, ct);
    lemma_first_known_head(u, g, e, cu);
    lemma_children_names_agree(t, u, g, set, Some(at), Some(au), false);
    let (kt, ku) = (t.in_set(set, ct), u.in_set(set, cu));
    lemma_heads_twin(t, u, kt, ku);
    lemma_in_set_children(t, g, set, Some(at), false, at);
    lemma_in_set_children(u, g, set, Some(au), false, au);
    if kt.len() > 0 {
        let (nt, nu) = (kt[0], ku[0]);
        assert(at < nt < t.len());
        assert(au < nu < u.len());
        lemma_leftmost_known_agree(t, u, g, e, nt, nu);
    }
}

/// Lemma A. Trees that agree on what `e` knows anchor a new element of
/// `e`'s at twin places.
pub proof fn lemma_anchor_agree(t: TreeS, u: TreeS, g: GraphS, e: int, lt: Option<int>, lu: Option<int>)
    requires t.wf(g), u.wf(g), g.wf(), g.event(e), agree(t, u, known(g, e)), twin_parents(t, u, g, lt, lu)
    ensures ({
        let (at, au) = (t.anchor(g, e, lt), u.anchor(g, e, lu));
        twin_parents(t, u, g, at.0, au.0) && at.1 == au.1
    })
{
    lemma_known_closed(g, e);
    let set = known(g, e);
    let (ct, cu) = (t.children(lt, true), u.children(lu, true));
    lemma_first_known_head(t, g, e, ct);
    lemma_first_known_head(u, g, e, cu);
    lemma_children_names_agree(t, u, g, set, lt, lu, true);
    let (kt, ku) = (t.in_set(set, ct), u.in_set(set, cu));
    lemma_heads_twin(t, u, kt, ku);
    let above_t: int = match lt { Some(i) => i, None => -1 };
    let above_u: int = match lu { Some(j) => j, None => -1 };
    lemma_in_set_children(t, g, set, lt, true, above_t);
    lemma_in_set_children(u, g, set, lu, true, above_u);
    if kt.len() > 0 {
        lemma_leftmost_known_agree(t, u, g, e, kt[0], ku[0]);
    }
}

// ---------------------------------------------------------------------------
// Lemma E: one event reads only its restriction.
// ---------------------------------------------------------------------------

/// `same_deleted` depends only on the two `deleted` sets.
pub proof fn lemma_same_deleted_stable(t: TreeS, u: TreeS, t2: TreeS, u2: TreeS, set: ISet<int>, i: int, j: int)
    requires same_deleted(t, u, set, i, j), t2.nodes[i].deleted == t.nodes[i].deleted, u2.nodes[j].deleted == u.nodes[j].deleted
    ensures same_deleted(t2, u2, set, i, j)
{
    reveal(same_deleted);
}

pub proof fn lemma_same_deleted_empty(t: TreeS, u: TreeS, set: ISet<int>, i: int, j: int)
    requires t.nodes[i].deleted == Set::<int>::empty(), u.nodes[j].deleted == Set::<int>::empty()
    ensures same_deleted(t, u, set, i, j)
{
    reveal(same_deleted);
}

pub proof fn lemma_same_deleted_insert(t: TreeS, u: TreeS, set: ISet<int>, i: int, j: int, e: int)
    requires same_deleted(t, u, set, i, j), t.node(i), u.node(j)
    ensures same_deleted(t.delete(i, e), u.delete(j, e), set, i, j)
{
    reveal(same_deleted);
    let (t2, u2) = (t.delete(i, e), u.delete(j, e));
    assert(t2.nodes[i].deleted == t.nodes[i].deleted.insert(e));
    assert(u2.nodes[j].deleted == u.nodes[j].deleted.insert(e));
}

/// A twin of an old element is still its twin after both trees attach.
proof fn lemma_half_attach(t: TreeS, u: TreeS, g: GraphS, set: ISet<int>, e: int, minted: int, item: ItemS, pt: (Option<int>, bool), pu: (Option<int>, bool))
    requires t.wf(g), u.wf(g), half(t, u, set), twin_parents(t, u, g, pt.0, pu.0), pt.1 == pu.1
    ensures half(t.attach(e, minted, item, pt), u.attach(e, minted, item, pu), set)
{
    let (t2, u2) = (t.attach(e, minted, item, pt), u.attach(e, minted, item, pu));
    assert forall|i: int| t2.node(i) && #[trigger] set.contains(t2.nodes[i].author)
        implies exists|j: int| u2.node(j) && same_node(t2, u2, set, i, j) by {
        if i < t.len() {
            assert(t2.nodes[i] == t.nodes[i]);
            assert(set.contains(t.nodes[i].author));
            let j = choose|j: int| u.node(j) && same_node(t, u, set, i, j);
            assert(u2.nodes[j] == u.nodes[j]);
            lemma_same_deleted_stable(t, u, t2, u2, set, i, j);
            if let Some(p) = t.nodes[i].parent { assert(t2.nodes[p] == t.nodes[p]); }
            if let Some(q) = u.nodes[j].parent { assert(u2.nodes[q] == u.nodes[q]); }
            assert(t2.parent_name(i) == t.parent_name(i));
            assert(u2.parent_name(j) == u.parent_name(j));
            assert(u2.node(j) && same_node(t2, u2, set, i, j));
        } else {
            let j = u.len();
            lemma_same_deleted_empty(t2, u2, set, i, j);
            assert(u2.node(j) && same_node(t2, u2, set, i, j));
        }
    }
}

pub proof fn lemma_attach_agree(t: TreeS, u: TreeS, g: GraphS, set: ISet<int>, e: int, minted: int, item: ItemS, pt: (Option<int>, bool), pu: (Option<int>, bool))
    requires t.wf(g), u.wf(g), agree(t, u, set), twin_parents(t, u, g, pt.0, pu.0), pt.1 == pu.1
    ensures agree(t.attach(e, minted, item, pt), u.attach(e, minted, item, pu), set)
{
    lemma_half_attach(t, u, g, set, e, minted, item, pt, pu);
    assert(twin_parents(u, t, g, pu.0, pt.0));
    lemma_half_attach(u, t, g, set, e, minted, item, pu, pt);
}

/// Marking twins removed by one event keeps them twins.
proof fn lemma_half_delete(t: TreeS, u: TreeS, g: GraphS, set: ISet<int>, e: int, i: int, j: int)
    requires t.wf(g), u.wf(g), half(t, u, set), t.node(i), u.node(j), t.id(i) == u.id(j)
    ensures half(t.delete(i, e), u.delete(j, e), set)
{
    let (t2, u2) = (t.delete(i, e), u.delete(j, e));
    assert forall|a: int| t2.node(a) && #[trigger] set.contains(t2.nodes[a].author)
        implies exists|b: int| u2.node(b) && same_node(t2, u2, set, a, b) by {
        assert(t2.nodes[a].author == t.nodes[a].author);
        assert(set.contains(t.nodes[a].author));
        let b = choose|b: int| u.node(b) && same_node(t, u, set, a, b);
        if let Some(p) = t.nodes[a].parent { assert(t2.nodes[p].author == t.nodes[p].author && t2.nodes[p].minted == t.nodes[p].minted); }
        if let Some(q) = u.nodes[b].parent { assert(u2.nodes[q].author == u.nodes[q].author && u2.nodes[q].minted == u.nodes[q].minted); }
        assert(t2.parent_name(a) == t.parent_name(a));
        assert(u2.parent_name(b) == u.parent_name(b));
        if a == i {
            // Its twin is `j`: the one index of `u` with that name.
            lemma_named_unique(u, g, b, j);
            lemma_same_deleted_insert(t, u, set, i, j, e);
            assert(u2.node(b) && same_node(t2, u2, set, a, b));
        } else {
            assert(t2.nodes[a] == t.nodes[a]);
            assert(b != j) by {
                if b == j { lemma_named_unique(t, g, a, i); }
            }
            assert(u2.nodes[b] == u.nodes[b]);
            lemma_same_deleted_stable(t, u, t2, u2, set, a, b);
            assert(u2.node(b) && same_node(t2, u2, set, a, b));
        }
    }
}

pub proof fn lemma_delete_agree(t: TreeS, u: TreeS, g: GraphS, set: ISet<int>, e: int, i: int, j: int)
    requires t.wf(g), u.wf(g), agree(t, u, set), t.node(i), u.node(j), t.id(i) == u.id(j)
    ensures agree(t.delete(i, e), u.delete(j, e), set)
{
    lemma_half_delete(t, u, g, set, e, i, j);
    lemma_half_delete(u, t, g, set, e, j, i);
}

/// What Lemma E asks of the set: closed, and holding everything `e` knows.
pub open spec fn covers(g: GraphS, set: ISet<int>, e: int) -> bool {
    closed(g, set) && forall|o: int| #[trigger] known(g, e).contains(o) ==> set.contains(o)
}

pub proof fn lemma_insert_run_agree(t: TreeS, u: TreeS, g: GraphS, set: ISet<int>, e: int, items: Seq<ItemS>, lt: Option<int>, lu: Option<int>, minted: int)
    requires
        t.wf(g), u.wf(g), g.wf(), g.event(e), covers(g, set, e), agree(t, u, set),
        twin_parents(t, u, g, lt, lu), t.known_or_none(g, e, lt), u.known_or_none(g, e, lu),
        t.minted_below(e, minted), u.minted_below(e, minted),
    ensures ({
        let (t2, m1) = insert_run(t, g, e, items, lt, minted);
        let (u2, m2) = insert_run(u, g, e, items, lu, minted);
        agree(t2, u2, set) && m1 == m2
    })
    decreases items.len()
{
    if items.len() > 0 {
        lemma_agree_mono(t, u, set, known(g, e));
        lemma_anchor_agree(t, u, g, e, lt, lu);
        lemma_anchor_known(t, g, e, lt);
        lemma_anchor_known(u, g, e, lu);
        let (pt, pu) = (t.anchor(g, e, lt), u.anchor(g, e, lu));
        lemma_attach_agree(t, u, g, set, e, minted, items[0], pt, pu);
        lemma_attach_wf(t, g, e, minted, items[0], pt);
        lemma_attach_wf(u, g, e, minted, items[0], pu);
        let (t2, u2) = (t.attach(e, minted, items[0], pt), u.attach(e, minted, items[0], pu));
        assert(twin_parents(t2, u2, g, Some(t.len()), Some(u.len())));
        lemma_insert_run_agree(t2, u2, g, set, e, items.drop_first(), Some(t.len()), Some(u.len()), minted + 1);
    }
}

pub proof fn lemma_delete_run_agree(t: TreeS, u: TreeS, g: GraphS, set: ISet<int>, e: int, prep_t: Seq<int>, prep_u: Seq<int>, at: int, items: Seq<ItemS>, k: int)
    requires
        t.wf(g), u.wf(g), g.wf(), g.event(e), covers(g, set, e), agree(t, u, set),
        t.view_ok(g, e, prep_t), u.view_ok(g, e, prep_u), t.names(prep_t) == u.names(prep_u),
        0 <= at, at + items.len() <= prep_t.len(),
    ensures match (delete_run(t, g, e, prep_t, at, items, k), delete_run(u, g, e, prep_u, at, items, k)) {
        (None, None) => true,
        (Some(t2), Some(u2)) => agree(t2, u2, set),
        _ => false,
    }
    decreases items.len() - k
{
    assert(t.names(prep_t).len() == prep_t.len());
    assert(u.names(prep_u).len() == prep_u.len());
    if 0 <= k < items.len() {
        let (i, j) = (prep_t[at + k], prep_u[at + k]);
        assert(t.names(prep_t)[at + k] == t.id(i));
        assert(u.names(prep_u)[at + k] == u.id(j));
        // The targets are twins, so they hold the same item.
        assert(set.contains(t.nodes[i].author)) by {
            assert(known(g, e).contains(t.nodes[i].author));
        }
        lemma_twin(t, u, g, set, i, j);
        if matches_s(items[k], t.nodes[i].item) {
            lemma_delete_agree(t, u, g, set, e, i, j);
            lemma_delete_wf(t, g, e, i);
            lemma_delete_wf(u, g, e, j);
            let (t2, u2) = (t.delete(i, e), u.delete(j, e));
            assert(t2.view_ok(g, e, prep_t));
            assert(u2.view_ok(g, e, prep_u));
            assert(t2.names(prep_t) =~= t.names(prep_t));
            assert(u2.names(prep_u) =~= u.names(prep_u));
            lemma_delete_run_agree(t2, u2, g, set, e, prep_t, prep_u, at, items, k + 1);
        }
    }
}

pub proof fn lemma_replay_ops_agree(t: TreeS, u: TreeS, g: GraphS, set: ISet<int>, e: int, prep_t: Seq<int>, prep_u: Seq<int>, ops: Seq<OperationS>, k: int, minted: int)
    requires
        t.wf(g), u.wf(g), g.wf(), g.event(e), covers(g, set, e), agree(t, u, set),
        t.view_ok(g, e, prep_t), u.view_ok(g, e, prep_u), t.names(prep_t) == u.names(prep_u),
        t.minted_below(e, minted), u.minted_below(e, minted),
    ensures match (replay_ops(t, g, e, prep_t, ops, k, minted), replay_ops(u, g, e, prep_u, ops, k, minted)) {
        (None, None) => true,
        (Some(t2), Some(u2)) => agree(t2, u2, set),
        _ => false,
    }
    decreases ops.len() - k
{
    assert(t.names(prep_t).len() == prep_t.len());
    assert(u.names(prep_u).len() == prep_u.len());
    if 0 <= k < ops.len() {
        let op = ops[k];
        if op.delete {
            if !(op.at < 0 || op.at + op.items.len() > prep_t.len()) {
                lemma_delete_run_agree(t, u, g, set, e, prep_t, prep_u, op.at, op.items, 0);
                lemma_delete_run_wf(t, g, e, prep_t, op.at, op.items, 0);
                lemma_delete_run_wf(u, g, e, prep_u, op.at, op.items, 0);
                if let (Some(t2), Some(u2)) = (delete_run(t, g, e, prep_t, op.at, op.items, 0), delete_run(u, g, e, prep_u, op.at, op.items, 0)) {
                    assert(t2.view_ok(g, e, prep_t));
                    assert(u2.view_ok(g, e, prep_u));
                    assert(t2.names(prep_t) =~= t.names(prep_t));
                    assert(u2.names(prep_u) =~= u.names(prep_u));
                    assert(t2.minted_below(e, minted));
                    assert(u2.minted_below(e, minted));
                    lemma_replay_ops_agree(t2, u2, g, set, e, prep_t, prep_u, ops, k + 1, minted);
                }
            }
        } else {
            if !(op.at < 0 || op.at > prep_t.len()) {
                let lt = if op.at == 0 { None } else { Some(prep_t[op.at - 1]) };
                let lu = if op.at == 0 { None } else { Some(prep_u[op.at - 1]) };
                if op.at > 0 {
                    assert(t.names(prep_t)[op.at - 1] == t.id(prep_t[op.at - 1]));
                    assert(u.names(prep_u)[op.at - 1] == u.id(prep_u[op.at - 1]));
                }
                assert(twin_parents(t, u, g, lt, lu));
                assert(t.known_or_none(g, e, lt));
                assert(u.known_or_none(g, e, lu));
                lemma_insert_run_agree(t, u, g, set, e, op.items, lt, lu, minted);
                lemma_insert_run_wf(t, g, e, op.items, lt, minted);
                lemma_insert_run_wf(u, g, e, op.items, lu, minted);
                let (t2, m) = insert_run(t, g, e, op.items, lt, minted);
                let (u2, m2) = insert_run(u, g, e, op.items, lu, minted);
                assert(t2.view_ok(g, e, prep_t));
                assert(u2.view_ok(g, e, prep_u));
                assert(t2.names(prep_t) =~= t.names(prep_t));
                assert(u2.names(prep_u) =~= u.names(prep_u));
                lemma_replay_ops_agree(t2, u2, g, set, e, prep_t, prep_u, ops, k + 1, m);
            }
        }
    }
}

/// Lemma E. Two trees that agree on a closed set covering what `e` knows
/// replay `e` to trees that still agree, or both refuse it.
pub proof fn lemma_replay_event_agree(t: TreeS, u: TreeS, g: GraphS, set: ISet<int>, e: int)
    requires
        t.wf(g), u.wf(g), g.wf(), g.event(e), covers(g, set, e), agree(t, u, set),
        t.minted_below(e, 0), u.minted_below(e, 0),
    ensures match (replay_event(t, g, e), replay_event(u, g, e)) {
        (None, None) => true,
        (Some(t2), Some(u2)) => agree(t2, u2, set),
        _ => false,
    }
{
    if let Some(ops) = g.events[e].ops {
        assert forall|o: int| #[trigger] past(g, e).contains(o) implies set.contains(o) by {
            assert(known(g, e).contains(o));
        }
        lemma_agree_mono(t, u, set, past(g, e));
        lemma_visible_agree(t, u, g, e);
        lemma_visible_ok(t, g, e);
        lemma_visible_ok(u, g, e);
        lemma_replay_ops_agree(t, u, g, set, e, t.visible(g, e), u.visible(g, e), ops, 0, 0);
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
