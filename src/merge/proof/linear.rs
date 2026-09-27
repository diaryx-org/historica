//! A history with no concurrency in it, walked: the fast path's model.
//! Compiled only by Verus (`verus_keep_ghost`).
//!
//! In a chain every element is known to the revision replaying, so Fugue's
//! anchoring has no concurrent siblings to step around, and an element
//! attached after `left` reads immediately after `left`
//! ([`lemma_anchor_after`]). From that, one revision replayed onto the tree
//! is exactly one revision applied to the list of what stands — which is
//! what `linear` does without building a tree.

use vstd::prelude::*;

use super::*;

verus! {

// ---------------------------------------------------------------------------
// Reading order.
// ---------------------------------------------------------------------------

/// Every element's author is known to `e`.
pub open spec fn all_known(t: TreeS, g: GraphS, e: int) -> bool {
    forall|i: int| t.node(i) ==> g.knows(e, #[trigger] t.nodes[i].author)
}

/// A top-level element is a right child of the root, as `anchor` places one.
pub open spec fn rooted(t: TreeS) -> bool {
    forall|i: int| t.node(i) && (#[trigger] t.nodes[i]).parent is None ==> t.nodes[i].right
}

/// Down the first left children, as far as they go: where `x`'s subtree
/// begins to read.
pub open spec fn leftmost(t: TreeS, x: int) -> int
    decreases t.len() - x
{
    let below = t.children(Some(x), false);
    if below.len() > 0 && x < below[0] < t.len() { leftmost(t, below[0]) } else { x }
}

/// Where `x` sits in `s`, for a list holding it once.
pub open spec fn index_in(s: Seq<int>, x: int) -> int {
    choose|i: int| 0 <= i < s.len() && s[i] == x
}

/// `s` with `j` put immediately after `p`, or immediately before it.
pub open spec fn put_by(s: Seq<int>, p: int, j: int, after: bool) -> Seq<int> {
    let i = index_in(s, p);
    if after { s.insert(i + 1, j) } else { s.insert(i, j) }
}

/// The children of a node in a shaped tree are nodes after it.
pub proof fn lemma_kids(t: TreeS, x: Option<int>, side: bool)
    requires shaped(t)
    ensures forall|k: int| 0 <= k < t.children(x, side).len() ==> {
        let c = #[trigger] t.children(x, side)[k];
        &&& t.node(c)
        &&& t.nodes[c].parent == x
        &&& t.nodes[c].right == side
        &&& (x matches Some(p) ==> p < c)
    }
{
    lemma_children_nodes(t, x, side);
    assert forall|k: int| 0 <= k < t.children(x, side).len() implies {
        let c = #[trigger] t.children(x, side)[k];
        &&& t.node(c)
        &&& t.nodes[c].parent == x
        &&& t.nodes[c].right == side
        &&& (x matches Some(p) ==> p < c)
    } by {
        let c = t.children(x, side)[k];
        assert(t.hangs(c, x, side));
        assert(t.nodes[c] == t.nodes[c]);
    }
}

/// In a tree every element is known in, the first known sibling is the
/// first sibling.
pub proof fn lemma_first_known_all(t: TreeS, g: GraphS, e: int, siblings: Seq<int>)
    requires all_known(t, g, e), forall|k: int| 0 <= k < siblings.len() ==> t.node(#[trigger] siblings[k])
    ensures t.first_known(g, e, siblings) == if siblings.len() == 0 { None } else { Some(siblings[0]) }
{
    if siblings.len() > 0 {
        assert(t.node(siblings[0]));
    }
}

/// And the leftmost known node is the leftmost node.
pub proof fn lemma_leftmost_known_all(t: TreeS, g: GraphS, e: int, x: int)
    requires all_known(t, g, e), shaped(t), t.node(x)
    ensures t.leftmost_known(g, e, x) == leftmost(t, x)
    decreases t.len() - x
{
    let below = t.children(Some(x), false);
    lemma_kids(t, Some(x), false);
    assert forall|k: int| 0 <= k < below.len() implies t.node(#[trigger] below[k]) by {}
    lemma_first_known_all(t, g, e, below);
    if below.len() > 0 {
        lemma_leftmost_known_all(t, g, e, below[0]);
    }
}

/// The leftmost node of a subtree is in it, and has no left child.
pub proof fn lemma_leftmost(t: TreeS, x: int)
    requires shaped(t), t.node(x)
    ensures
        t.node(leftmost(t, x)),
        under(t, x, leftmost(t, x)),
        t.children(Some(leftmost(t, x)), false).len() == 0,
    decreases t.len() - x
{
    let below = t.children(Some(x), false);
    lemma_kids(t, Some(x), false);
    if below.len() > 0 {
        let c = below[0];
        lemma_leftmost(t, c);
        lemma_under_parent(t, c, leftmost(t, c), x);
    }
}

/// A subtree begins to read at its leftmost node.
pub proof fn lemma_read_first(t: TreeS, x: int)
    requires shaped(t), t.node(x)
    ensures t.read(x).len() > 0, t.read(x)[0] == leftmost(t, x)
    decreases t.len() - x
{
    let below = t.children(Some(x), false);
    lemma_kids(t, Some(x), false);
    if below.len() > 0 {
        let c = below[0];
        lemma_read_first(t, c);
        assert(t.read_all(below, x) == t.read(c) + t.read_all(below.drop_first(), x));
        assert(t.read(x) == t.read_all(below, x) + seq![x] + t.read_all(t.children(Some(x), true), x));
        assert(t.read(x)[0] == t.read(c)[0]);
    } else {
        assert(t.read_all(below, x) == Seq::<int>::empty());
        assert(t.read(x)[0] == x);
    }
}

/// Below `x` and not `x`: one of `x`'s children is above it.
pub proof fn lemma_under_child(t: TreeS, x: int, y: int)
    requires under(t, x, y), y != x
    ensures exists|c: int| x < c <= y && #[trigger] t.nodes[c].parent == Some(x) && under(t, c, y)
    decreases y
{
    let q = t.nodes[y].parent->Some_0;
    assert(0 <= q < y && under(t, x, q));
    if q == x {
        assert(under(t, y, y));
        assert(x < y);
    } else {
        lemma_under_child(t, x, q);
        let c = choose|c: int| x < c <= q && #[trigger] t.nodes[c].parent == Some(x) && under(t, c, q);
        lemma_under_le(t, c, q);
        assert(under(t, c, y));
    }
}

/// A list of siblings reads everything any one of them reads.
pub proof fn lemma_read_all_has(t: TreeS, kids: Seq<int>, above: int, k: int, z: int)
    requires 0 <= k < kids.len(), above < kids[k] < t.len(), t.read(kids[k]).contains(z)
    ensures t.read_all(kids, above).contains(z)
    decreases kids.len()
{
    let first = kids[0];
    let rest = kids.drop_first();
    let tail = t.read_all(rest, above);
    if k == 0 {
        let i = choose|i: int| 0 <= i < t.read(first).len() && t.read(first)[i] == z;
        assert((t.read(first) + tail)[i] == z);
    } else {
        assert(rest[k - 1] == kids[k]);
        lemma_read_all_has(t, rest, above, k - 1, z);
        let i = choose|i: int| 0 <= i < tail.len() && tail[i] == z;
        if above < first < t.len() {
            assert((t.read(first) + tail)[t.read(first).len() + i] == z);
        }
    }
}

/// Everything below a node is read with it.
pub proof fn lemma_read_complete(t: TreeS, x: int, y: int)
    requires shaped(t), t.node(x), t.node(y), under(t, x, y)
    ensures t.read(x).contains(y)
    decreases t.len() - x
{
    let left = t.read_all(t.children(Some(x), false), x);
    let right = t.read_all(t.children(Some(x), true), x);
    assert(t.read(x) == left + seq![x] + right);
    if y == x {
        assert(t.read(x)[left.len() as int] == x);
    } else {
        lemma_under_child(t, x, y);
        let c = choose|c: int| x < c <= y && #[trigger] t.nodes[c].parent == Some(x) && under(t, c, y);
        let side = t.nodes[c].right;
        assert(t.hangs(c, Some(x), side));
        lemma_children_complete(t, Some(x), side, c);
        let kids = t.children(Some(x), side);
        let k = choose|k: int| 0 <= k < kids.len() && kids[k] == c;
        lemma_read_complete(t, c, y);
        lemma_read_all_has(t, kids, x, k, y);
        if side {
            let i = choose|i: int| 0 <= i < right.len() && right[i] == y;
            assert(t.read(x)[left.len() + 1 + i] == y);
        } else {
            let i = choose|i: int| 0 <= i < left.len() && left[i] == y;
            assert(t.read(x)[i] == y);
        }
    }
}

/// Every node is below some top-level node.
pub proof fn lemma_under_root(t: TreeS, y: int)
    requires shaped(t), rooted(t), t.node(y)
    ensures exists|c: int| #[trigger] t.hangs(c, None, true) && under(t, c, y)
    decreases y
{
    match t.nodes[y].parent {
        None => {
            assert(t.nodes[y] == t.nodes[y]);
            assert(t.hangs(y, None, true));
            assert(under(t, y, y));
        },
        Some(q) => {
            assert(t.nodes[y] == t.nodes[y]);
            lemma_under_root(t, q);
            let c = choose|c: int| #[trigger] t.hangs(c, None, true) && under(t, c, q);
            lemma_under_le(t, c, q);
            assert(under(t, c, y));
        },
    }
}

// ---------------------------------------------------------------------------
// Putting an element next to another.
// ---------------------------------------------------------------------------

/// A list holding `x` once finds it at one place.
pub proof fn lemma_index_in(s: Seq<int>, x: int)
    requires s.contains(x), s.no_duplicates()
    ensures
        0 <= index_in(s, x) < s.len(),
        s[index_in(s, x)] == x,
        forall|i: int| 0 <= i < s.len() && s[i] == x ==> i == index_in(s, x),
{
}

/// Putting `j` by `p`, where `p` is in the second half and not the first,
/// leaves the first half alone.
pub proof fn lemma_put_by_right(a: Seq<int>, b: Seq<int>, p: int, j: int, after: bool)
    requires !a.contains(p), b.contains(p), b.no_duplicates()
    ensures put_by(a + b, p, j, after) == a + put_by(b, p, j, after)
{
    lemma_index_in(b, p);
    let ib = index_in(b, p);
    let s = a + b;
    assert(s[a.len() + ib] == p);
    assert forall|i: int| 0 <= i < s.len() && s[i] == p implies i == a.len() + ib by {
        if i < a.len() {
            assert(a[i] == p);
        } else {
            assert(b[i - a.len()] == p);
        }
    }
    let is = index_in(s, p);
    assert(s[is] == p);
    assert(is == a.len() + ib);
    if after {
        assert(s.insert(is + 1, j) =~= a + b.insert(ib + 1, j));
    } else {
        assert(s.insert(is, j) =~= a + b.insert(ib, j));
    }
}

/// And where `p` is in the first half and not the second, it leaves the
/// second half alone.
pub proof fn lemma_put_by_left(a: Seq<int>, b: Seq<int>, p: int, j: int, after: bool)
    requires a.contains(p), !b.contains(p), a.no_duplicates()
    ensures put_by(a + b, p, j, after) == put_by(a, p, j, after) + b
{
    lemma_index_in(a, p);
    let ia = index_in(a, p);
    let s = a + b;
    assert(s[ia] == p);
    assert forall|i: int| 0 <= i < s.len() && s[i] == p implies i == ia by {
        if i >= a.len() {
            assert(b[i - a.len()] == p);
        }
    }
    let is = index_in(s, p);
    assert(s[is] == p);
    assert(is == ia);
    if after {
        assert(s.insert(is + 1, j) =~= a.insert(ia + 1, j) + b);
    } else {
        assert(s.insert(is, j) =~= a.insert(ia, j) + b);
    }
}

// ---------------------------------------------------------------------------
// One element hung alone, and where it reads.
// ---------------------------------------------------------------------------

/// `u` is `t` with one element more, `t.len()`, hung as the only child of
/// `p` on side `side`.
pub open spec fn hung_alone(t: TreeS, u: TreeS, p: int, side: bool) -> bool {
    &&& t.node(p)
    &&& u.len() == t.len() + 1
    &&& forall|i: int| 0 <= i < t.len() ==> #[trigger] u.nodes[i] == t.nodes[i]
    &&& u.nodes[t.len() as int].parent == Some(p)
    &&& u.children(Some(p), side) == seq![t.len() as int]
    &&& t.children(Some(p), side).len() == 0
    &&& forall|x: Option<int>, r: bool| !(x == Some(p) && r == side) && (x matches Some(q) ==> 0 <= q < t.len())
        ==> #[trigger] u.children(x, r) == t.children(x, r)
    &&& u.children(Some(t.len() as int), false).len() == 0
    &&& u.children(Some(t.len() as int), true).len() == 0
}

/// Attaching where nothing hangs yet is hanging alone.
pub proof fn lemma_hung(t: TreeS, author: int, minted: int, item: ItemS, p: int, side: bool)
    requires shaped(t), t.node(p), t.children(Some(p), side).len() == 0
    ensures hung_alone(t, t.attach(author, minted, item, (Some(p), side)), p, side)
{
    let u = t.attach(author, minted, item, (Some(p), side));
    let j = t.len() as int;
    lemma_children_attach(t, author, minted, item, (Some(p), side), Some(p), side);
    assert(u.insert_sorted(t.children(Some(p), side), j) =~= seq![j]) by {
        assert(t.children(Some(p), side) =~= Seq::<int>::empty());
        assert(u.first_greater(Seq::<int>::empty(), j, 0) == 0);
    }
    assert forall|x: Option<int>, r: bool| !(x == Some(p) && r == side) && (x matches Some(q) ==> 0 <= q < t.len())
        implies #[trigger] u.children(x, r) == t.children(x, r) by {
        lemma_children_attach(t, author, minted, item, (Some(p), side), x, r);
    }
    assert forall|k: int, r: bool| 0 <= k < u.len() implies !u.hangs(k, Some(j), r) by {
        if k < j {
            assert(u.nodes[k] == t.nodes[k]);
        }
    }
    lemma_children_none(u, Some(j), false, u.len());
    lemma_children_none(u, Some(j), true, u.len());
}

/// The new element reads as itself alone.
proof fn lemma_read_new(t: TreeS, u: TreeS, p: int, side: bool)
    requires hung_alone(t, u, p, side)
    ensures u.read(t.len() as int) == seq![t.len() as int]
{
    let j = t.len() as int;
    assert(u.read_all(u.children(Some(j), false), j) == Seq::<int>::empty());
    assert(u.read_all(u.children(Some(j), true), j) == Seq::<int>::empty());
    assert(u.read(j) =~= seq![j]);
}

/// Where `p` is below `x`, `x` reads in `u` as it read in `t` with the new
/// element beside `p`; elsewhere it reads as it did.
pub proof fn lemma_read_hung(t: TreeS, u: TreeS, p: int, side: bool, x: int)
    requires shaped(t), hung_alone(t, u, p, side), t.node(x)
    ensures
        under(t, x, p) ==> u.read(x) == put_by(t.read(x), p, t.len() as int, side),
        !under(t, x, p) ==> u.read(x) == t.read(x),
    decreases t.len() - x, 1int, 0int
{
    let j = t.len() as int;
    let (lt, rt) = (t.children(Some(x), false), t.children(Some(x), true));
    lemma_kids(t, Some(x), false);
    lemma_kids(t, Some(x), true);
    lemma_children_upto_no_dup(t, Some(x), false, t.len());
    lemma_children_upto_no_dup(t, Some(x), true, t.len());
    // No child of `x` is above `x`, so none is above `p` when `p` is `x`.
    let above_p = |kids: Seq<int>| exists|k: int| 0 <= k < kids.len() && under(t, kids[k], p);
    if x == p {
        assert(!above_p(lt) && !above_p(rt)) by {
            if above_p(lt) {
                let k = choose|k: int| 0 <= k < lt.len() && under(t, lt[k], p);
                lemma_under_le(t, lt[k], p);
            }
            if above_p(rt) {
                let k = choose|k: int| 0 <= k < rt.len() && under(t, rt[k], p);
                lemma_under_le(t, rt[k], p);
            }
        }
        lemma_read_new(t, u, p, side);
        assert(u.read_all(seq![j], p) =~= seq![j]) by {
            assert(u.read_all(seq![j], p) == u.read(j) + u.read_all(seq![j].drop_first(), p));
            assert(seq![j].drop_first() =~= Seq::<int>::empty());
        }
        lemma_read_no_dup(t, p);
        let tr = t.read(p);
        assert(tr == t.read_all(lt, p) + seq![p] + t.read_all(rt, p));
        assert(u.read(p) == u.read_all(u.children(Some(p), false), p) + seq![p]
            + u.read_all(u.children(Some(p), true), p));
        assert(tr.contains(p)) by { lemma_read_complete(t, p, p); }
        lemma_index_in(tr, p);
        if side {
            assert(u.children(Some(p), false) == lt);
            assert(u.children(Some(p), true) == seq![j]);
            lemma_read_all_hung(t, u, p, side, lt, p, Some(x));
            assert(rt.len() == 0);
            assert(t.read_all(rt, p) == Seq::<int>::empty());
            let a = t.read_all(lt, p);
            assert(tr =~= a + seq![p]);
            assert(tr[a.len() as int] == p);
            assert(index_in(tr, p) == a.len());
            assert(u.read(p) =~= a + seq![p] + seq![j]);
            assert(tr.insert(a.len() as int + 1, j) =~= a + seq![p] + seq![j]);
            assert(put_by(tr, p, j, side) == tr.insert(index_in(tr, p) + 1, j));
        } else {
            assert(u.children(Some(p), true) == rt);
            assert(u.children(Some(p), false) == seq![j]);
            lemma_read_all_hung(t, u, p, side, rt, p, Some(x));
            assert(lt.len() == 0);
            assert(t.read_all(lt, p) == Seq::<int>::empty());
            let b = t.read_all(rt, p);
            assert(tr =~= seq![p] + b);
            assert(tr[0] == p);
            assert(index_in(tr, p) == 0);
            assert(u.read(p) =~= seq![j] + seq![p] + b);
            assert(tr.insert(0, j) =~= seq![j] + seq![p] + b);
            assert(put_by(tr, p, j, side) == tr.insert(index_in(tr, p), j));
        }
        assert(under(t, p, p));
        assert(u.read(x) == put_by(t.read(x), p, j, side));
    } else {
        assert(u.children(Some(x), false) == lt);
        assert(u.children(Some(x), true) == rt);
        lemma_read_all_hung(t, u, p, side, lt, x, Some(x));
        lemma_read_all_hung(t, u, p, side, rt, x, Some(x));
        let (a, b) = (t.read_all(lt, x), t.read_all(rt, x));
        assert(t.read(x) == a + seq![x] + b);
        assert(u.read(x) == u.read_all(lt, x) + seq![x] + u.read_all(rt, x));
        if under(t, x, p) {
            lemma_under_child(t, x, p);
            let c = choose|c: int| x < c <= p && #[trigger] t.nodes[c].parent == Some(x) && under(t, c, p);
            let r = t.nodes[c].right;
            assert(t.hangs(c, Some(x), r));
            lemma_children_complete(t, Some(x), r, c);
            lemma_read_no_dup(t, x);
            lemma_read_all_no_dup(t, lt, x, Some(x));
            lemma_read_all_no_dup(t, rt, x, Some(x));
            lemma_read_all_under(t, lt, x);
            lemma_read_all_under(t, rt, x);
            if r {
                let k = choose|k: int| 0 <= k < rt.len() && rt[k] == c;
                assert(above_p(rt));
                // `p` is on the right, and so not on the left or at `x`.
                assert(!a.contains(p)) by {
                    if a.contains(p) {
                        let m = choose|m: int| 0 <= m < lt.len() && x < lt[m] < t.len() && under(t, lt[m], p);
                        lemma_under_siblings(t, lt[m], c, p);
                    }
                }
                lemma_read_complete(t, c, p);
                lemma_read_all_has(t, rt, x, k, p);
                assert(!(a + seq![x]).contains(p)) by {
                    if (a + seq![x]).contains(p) {
                        let i = choose|i: int| 0 <= i < (a + seq![x]).len() && (a + seq![x])[i] == p;
                        if i < a.len() { assert(a.contains(p)); }
                    }
                }
                lemma_put_by_right(a + seq![x], b, p, j, side);
                assert(!above_p(lt)) by {
                    if above_p(lt) {
                        let m = choose|m: int| 0 <= m < lt.len() && under(t, lt[m], p);
                        assert(t.nodes[lt[m]].right == false);
                        lemma_under_siblings(t, lt[m], c, p);
                    }
                }
                assert(u.read_all(rt, x) == put_by(b, p, j, side));
                assert(u.read_all(lt, x) == a);
                assert(u.read(x) == put_by(t.read(x), p, j, side));
            } else {
                let k = choose|k: int| 0 <= k < lt.len() && lt[k] == c;
                assert(above_p(lt));
                assert(!b.contains(p)) by {
                    if b.contains(p) {
                        let m = choose|m: int| 0 <= m < rt.len() && x < rt[m] < t.len() && under(t, rt[m], p);
                        lemma_under_siblings(t, c, rt[m], p);
                    }
                }
                lemma_read_complete(t, c, p);
                lemma_read_all_has(t, lt, x, k, p);
                assert(!seq![x].contains(p)) by {
                    if seq![x].contains(p) { assert(seq![x][0] == p); }
                }
                assert forall|y: int| a.contains(y) implies !seq![x].contains(y) by {
                    if seq![x].contains(y) {
                        assert(seq![x][0] == y);
                        let m = choose|m: int| 0 <= m < lt.len() && x < lt[m] < t.len() && under(t, lt[m], y);
                        lemma_under_le(t, lt[m], y);
                    }
                }
                assert(seq![x].no_duplicates());
                lemma_no_dup_add(a, seq![x]);
                lemma_put_by_left(a, seq![x], p, j, side);
                assert((a + seq![x]).contains(p)) by {
                    let i = choose|i: int| 0 <= i < a.len() && a[i] == p;
                    assert((a + seq![x])[i] == p);
                }
                lemma_put_by_left(a + seq![x], b, p, j, side);
                assert(!above_p(rt)) by {
                    if above_p(rt) {
                        let m = choose|m: int| 0 <= m < rt.len() && under(t, rt[m], p);
                        assert(t.nodes[rt[m]].right == true);
                        lemma_under_siblings(t, c, rt[m], p);
                    }
                }
                assert(u.read_all(lt, x) == put_by(a, p, j, side));
                assert(u.read_all(rt, x) == b);
                assert(u.read(x) == put_by(t.read(x), p, j, side));
            }
        } else {
            assert(!above_p(lt) && !above_p(rt)) by {
                if above_p(lt) {
                    let k = choose|k: int| 0 <= k < lt.len() && under(t, lt[k], p);
                    lemma_under_parent(t, lt[k], p, x);
                }
                if above_p(rt) {
                    let k = choose|k: int| 0 <= k < rt.len() && under(t, rt[k], p);
                    lemma_under_parent(t, rt[k], p, x);
                }
            }
        }
    }
}

/// And a list of siblings reads the same way: with the new element beside
/// `p` where one of them is above it, and as it did otherwise.
pub proof fn lemma_read_all_hung(t: TreeS, u: TreeS, p: int, side: bool, kids: Seq<int>, above: int, parent: Option<int>)
    requires
        shaped(t), hung_alone(t, u, p, side), kids.no_duplicates(),
        forall|k: int| 0 <= k < kids.len() ==> t.node(#[trigger] kids[k]) && t.nodes[kids[k]].parent == parent
            && above < kids[k],
    ensures
        (exists|k: int| 0 <= k < kids.len() && under(t, kids[k], p))
            ==> u.read_all(kids, above) == put_by(t.read_all(kids, above), p, t.len() as int, side),
        !(exists|k: int| 0 <= k < kids.len() && under(t, kids[k], p))
            ==> u.read_all(kids, above) == t.read_all(kids, above),
    decreases t.len() - above, 0int, kids.len()
{
    let j = t.len() as int;
    if kids.len() > 0 {
        let first = kids[0];
        let rest = kids.drop_first();
        assert(t.node(first));
        assert forall|k: int| 0 <= k < rest.len() implies t.node(#[trigger] rest[k]) && t.nodes[rest[k]].parent == parent
            && above < rest[k] by {
            assert(rest[k] == kids[k + 1]);
        }
        assert(rest.no_duplicates()) by {
            assert forall|a: int, b: int| 0 <= a < b < rest.len() implies rest[a] != rest[b] by {
                assert(rest[a] == kids[a + 1]);
                assert(rest[b] == kids[b + 1]);
            }
        }
        lemma_read_hung(t, u, p, side, first);
        lemma_read_all_hung(t, u, p, side, rest, above, parent);
        let (hf, tf) = (t.read(first), t.read_all(rest, above));
        assert(t.read_all(kids, above) == hf + tf);
        assert(u.read_all(kids, above) == u.read(first) + u.read_all(rest, above));
        let rest_above = exists|k: int| 0 <= k < rest.len() && under(t, rest[k], p);
        if under(t, first, p) {
            assert(!rest_above) by {
                if rest_above {
                    let k = choose|k: int| 0 <= k < rest.len() && under(t, rest[k], p);
                    assert(rest[k] == kids[k + 1]);
                    assert(kids[0] != kids[k + 1]);
                    lemma_under_siblings(t, first, rest[k], p);
                }
            }
            lemma_read_complete(t, first, p);
            lemma_read_no_dup(t, first);
            lemma_read_all_under(t, rest, above);
            assert(!tf.contains(p)) by {
                if tf.contains(p) {
                    let k = choose|k: int| 0 <= k < rest.len() && above < rest[k] < t.len() && under(t, rest[k], p);
                }
            }
            lemma_put_by_left(hf, tf, p, j, side);
            assert(under(t, kids[0], p));
        } else {
            lemma_read_under(t, first);
            assert(!hf.contains(p));
            if rest_above {
                let k = choose|k: int| 0 <= k < rest.len() && under(t, rest[k], p);
                lemma_read_complete(t, rest[k], p);
                lemma_read_all_has(t, rest, above, k, p);
                lemma_read_all_no_dup(t, rest, above, parent);
                lemma_put_by_right(hf, tf, p, j, side);
                assert(rest[k] == kids[k + 1]);
            } else {
                assert(!(exists|k: int| 0 <= k < kids.len() && under(t, kids[k], p))) by {
                    if exists|k: int| 0 <= k < kids.len() && under(t, kids[k], p) {
                        let k = choose|k: int| 0 <= k < kids.len() && under(t, kids[k], p);
                        if k > 0 { assert(rest[k - 1] == kids[k]); }
                    }
                }
            }
        }
    }
}


/// The whole document reads as it did, with the new element beside `p`.
pub proof fn lemma_order_hung(t: TreeS, u: TreeS, p: int, side: bool)
    requires shaped(t), rooted(t), hung_alone(t, u, p, side)
    ensures u.order() == put_by(t.order(), p, t.len() as int, side)
{
    reveal(TreeS::order);
    let roots = t.children(None, true);
    assert(u.children(None, true) == roots);
    lemma_kids(t, None, true);
    lemma_children_upto_no_dup(t, None, true, t.len());
    lemma_under_root(t, p);
    let c = choose|c: int| #[trigger] t.hangs(c, None, true) && under(t, c, p);
    lemma_children_complete(t, None, true, c);
    let k = choose|k: int| 0 <= k < roots.len() && roots[k] == c;
    assert forall|m: int| 0 <= m < roots.len() implies t.node(#[trigger] roots[m]) && t.nodes[roots[m]].parent == None::<int>
        && -1 < roots[m] by {}
    lemma_read_all_hung(t, u, p, side, roots, -1, None);
}

/// A subtree reads as one block inside any reading that holds it.
#[verifier::rlimit(30)]
pub proof fn lemma_read_contig(t: TreeS, x: int, l: int)
    requires shaped(t), t.node(x), t.node(l), under(t, x, l)
    ensures exists|a: Seq<int>, b: Seq<int>| t.read(x) == #[trigger] (a + t.read(l) + b)
    decreases t.len() - x
{
    if x == l {
        assert(t.read(x) =~= Seq::<int>::empty() + t.read(l) + Seq::<int>::empty());
    } else {
        lemma_under_child(t, x, l);
        let c = choose|c: int| x < c <= l && #[trigger] t.nodes[c].parent == Some(x) && under(t, c, l);
        let side = t.nodes[c].right;
        assert(t.hangs(c, Some(x), side));
        lemma_children_complete(t, Some(x), side, c);
        let kids = t.children(Some(x), side);
        let k = choose|k: int| 0 <= k < kids.len() && kids[k] == c;
        lemma_read_contig(t, c, l);
        let (a1, b1) = choose|a: Seq<int>, b: Seq<int>| t.read(c) == #[trigger] (a + t.read(l) + b);
        lemma_read_all_contig(t, kids, x, k);
        let (a2, b2) = choose|a: Seq<int>, b: Seq<int>| t.read_all(kids, x) == #[trigger] (a + t.read(kids[k]) + b);
        let (lr, rr) = (t.read_all(t.children(Some(x), false), x), t.read_all(t.children(Some(x), true), x));
        assert(t.read(x) == lr + seq![x] + rr);
        if side {
            assert(t.read(x) =~= (lr + seq![x] + a2 + a1) + t.read(l) + (b1 + b2));
        } else {
            assert(t.read(x) =~= (a2 + a1) + t.read(l) + (b1 + b2 + seq![x] + rr));
        }
    }
}

/// And a list of siblings reads each of them as one block.
pub proof fn lemma_read_all_contig(t: TreeS, kids: Seq<int>, above: int, k: int)
    requires 0 <= k < kids.len(), above < kids[k] < t.len()
    ensures exists|a: Seq<int>, b: Seq<int>| t.read_all(kids, above) == #[trigger] (a + t.read(kids[k]) + b)
    decreases kids.len()
{
    let first = kids[0];
    let rest = kids.drop_first();
    let tail = t.read_all(rest, above);
    if k == 0 {
        assert(t.read_all(kids, above) =~= Seq::<int>::empty() + t.read(first) + tail);
    } else {
        assert(rest[k - 1] == kids[k]);
        lemma_read_all_contig(t, rest, above, k - 1);
        let (a, b) = choose|a: Seq<int>, b: Seq<int>| tail == #[trigger] (a + t.read(rest[k - 1]) + b);
        if above < first < t.len() {
            assert(t.read_all(kids, above) =~= (t.read(first) + a) + t.read(kids[k]) + b);
        } else {
            assert(t.read_all(kids, above) =~= a + t.read(kids[k]) + b);
        }
    }
}

/// Where `l` has something on its right, the first thing read after `l` is
/// the leftmost node of its first right child.
pub proof fn lemma_next_after(t: TreeS, l: int)
    requires shaped(t), rooted(t), t.node(l), t.children(Some(l), true).len() > 0
    ensures ({
        let o = t.order();
        let f = t.children(Some(l), true)[0];
        &&& o.contains(l)
        &&& index_in(o, l) + 1 < o.len()
        &&& o[index_in(o, l) + 1] == leftmost(t, f)
    })
{
    reveal(TreeS::order);
    let o = t.order();
    let roots = t.children(None, true);
    lemma_kids(t, None, true);
    lemma_kids(t, Some(l), true);
    lemma_under_root(t, l);
    let c = choose|c: int| #[trigger] t.hangs(c, None, true) && under(t, c, l);
    lemma_children_complete(t, None, true, c);
    let k = choose|k: int| 0 <= k < roots.len() && roots[k] == c;
    lemma_read_all_contig(t, roots, -1, k);
    let (a, b) = choose|a: Seq<int>, b: Seq<int>| o == #[trigger] (a + t.read(roots[k]) + b);
    lemma_read_contig(t, c, l);
    let (a1, b1) = choose|a1: Seq<int>, b1: Seq<int>| t.read(c) == #[trigger] (a1 + t.read(l) + b1);
    let right = t.children(Some(l), true);
    let f = right[0];
    let lr = t.read_all(t.children(Some(l), false), l);
    assert(t.read(l) == lr + seq![l] + t.read_all(right, l));
    assert(t.read_all(right, l) == t.read(f) + t.read_all(right.drop_first(), l));
    lemma_read_first(t, f);
    let i = (a.len() + a1.len() + lr.len()) as int;
    assert(o =~= (a + a1 + lr) + seq![l] + (t.read(f) + t.read_all(right.drop_first(), l) + b1 + b));
    assert(o[i] == l);
    assert(o[i + 1] == leftmost(t, f));
    lemma_order_no_dup(t);
    lemma_index_in(o, l);
}

/// The document begins with the leftmost node of its first top-level node.
pub proof fn lemma_order_first(t: TreeS)
    requires shaped(t), t.children(None, true).len() > 0
    ensures t.order().len() > 0, t.order()[0] == leftmost(t, t.children(None, true)[0])
{
    reveal(TreeS::order);
    let roots = t.children(None, true);
    lemma_kids(t, None, true);
    assert(t.read_all(roots, -1) == t.read(roots[0]) + t.read_all(roots.drop_first(), -1));
    lemma_read_first(t, roots[0]);
}

/// Every node is below a top-level node, so a tree without one is empty.
pub proof fn lemma_no_roots(t: TreeS)
    requires shaped(t), rooted(t), t.children(None, true).len() == 0
    ensures t.len() == 0
{
    if t.len() > 0 {
        lemma_under_root(t, 0);
        let c = choose|c: int| #[trigger] t.hangs(c, None, true) && under(t, c, 0);
        lemma_children_complete(t, None, true, c);
    }
}

/// **Attached after `left` in a tree its author knows every element of, an
/// element reads immediately after `left`** — or first, where there is no
/// `left` — whatever tombstones stand around it.
pub proof fn lemma_anchor_after(t: TreeS, g: GraphS, e: int, minted: int, item: ItemS, left: Option<int>)
    requires shaped(t), rooted(t), all_known(t, g, e), left matches Some(l) ==> t.node(l)
    ensures ({
        let u = t.attach(e, minted, item, t.anchor(g, e, left));
        &&& u.order() == match left {
            None => seq![t.len() as int] + t.order(),
            Some(l) => put_by(t.order(), l, t.len() as int, true),
        }
        &&& shaped(u)
        &&& rooted(u)
    })
{
    let j = t.len() as int;
    let place = t.anchor(g, e, left);
    let u = t.attach(e, minted, item, place);
    let above = t.children(left, true);
    lemma_kids(t, left, true);
    assert forall|k: int| 0 <= k < above.len() implies t.node(#[trigger] above[k]) by {}
    lemma_first_known_all(t, g, e, above);
    lemma_order_no_dup(t);
    if above.len() == 0 {
        assert(place == (left, true));
        match left {
            Some(l) => {
                lemma_hung(t, e, minted, item, l, true);
                lemma_order_hung(t, u, l, true);
            },
            None => {
                lemma_no_roots(t);
                reveal(TreeS::order);
                assert(t.order() == Seq::<int>::empty());
                lemma_children_attach(t, e, minted, item, place, None, true);
                assert(u.insert_sorted(Seq::<int>::empty(), j) =~= seq![j]) by {
                    assert(u.first_greater(Seq::<int>::empty(), j, 0) == 0);
                }
                assert(u.children(None, true) =~= seq![j]);
                assert forall|k: int, r: bool| 0 <= k < u.len() implies !u.hangs(k, Some(j), r) by {}
                lemma_children_none(u, Some(j), false, u.len());
                lemma_children_none(u, Some(j), true, u.len());
                assert(u.read(j) =~= seq![j]);
                assert(u.read_all(seq![j], -1) == u.read(j) + u.read_all(seq![j].drop_first(), -1));
                assert(seq![j].drop_first() =~= Seq::<int>::empty());
                assert(u.order() =~= seq![j] + t.order());
            },
        }
    } else {
        let f = above[0];
        lemma_leftmost_known_all(t, g, e, f);
        let lm = leftmost(t, f);
        assert(place == (Some(lm), false));
        lemma_leftmost(t, f);
        lemma_hung(t, e, minted, item, lm, false);
        lemma_order_hung(t, u, lm, false);
        let o = t.order();
        match left {
            Some(l) => {
                lemma_next_after(t, l);
                let i = index_in(o, l);
                assert(o[i + 1] == lm);
                assert(o.contains(lm));
                lemma_index_in(o, lm);
                assert(index_in(o, lm) == i + 1);
            },
            None => {
                lemma_order_first(t);
                assert(o[0] == lm);
                lemma_index_in(o, lm);
                assert(index_in(o, lm) == 0);
                assert(o.insert(0, j) =~= seq![j] + o);
            },
        }
    }
}


// ---------------------------------------------------------------------------
// A run of insertions, as a block.
// ---------------------------------------------------------------------------

/// `o` with `run` put right after `left`, or at the front where there is no
/// `left`.
pub open spec fn put_block(o: Seq<int>, left: Option<int>, run: Seq<int>) -> Seq<int> {
    match left {
        None => run + o,
        Some(x) => {
            let i = index_in(o, x);
            o.subrange(0, i + 1) + run + o.subrange(i + 1, o.len() as int)
        },
    }
}

/// `n` fresh indices from `from`.
pub open spec fn fresh(from: int, n: int) -> Seq<int> {
    Seq::new(n as nat, |k: int| from + k)
}

/// Putting one element after `l` and then a run after it is putting the
/// element and the run after `l`.
#[verifier::rlimit(30)]
pub proof fn lemma_put_block_step(o: Seq<int>, l: int, j: int, run: Seq<int>)
    requires o.no_duplicates(), o.contains(l), !o.contains(j)
    ensures put_block(put_by(o, l, j, true), Some(j), run) == put_block(o, Some(l), seq![j] + run)
{
    lemma_index_in(o, l);
    let i = index_in(o, l);
    let o1 = put_by(o, l, j, true);
    assert(o1 =~= o.subrange(0, i + 1) + seq![j] + o.subrange(i + 1, o.len() as int));
    assert(o1[i + 1] == j);
    assert(o1.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < b < o1.len() implies o1[a] != o1[b] by {
            if a == i + 1 {
                assert(o[b - 1] == o1[b]);
            } else if b == i + 1 {
                assert(o[a] == o1[a]);
            } else {
                let (x, y) = (if a < i + 1 { a } else { a - 1 }, if b < i + 1 { b } else { b - 1 });
                assert(o1[a] == o[x]);
                assert(o1[b] == o[y]);
            }
        }
    }
    lemma_index_in(o1, j);
    assert(index_in(o1, j) == i + 1);
    assert(put_block(o1, Some(j), run) =~= o.subrange(0, i + 1) + (seq![j] + run) + o.subrange(i + 1, o.len() as int));
}

/// And at the front, likewise.
pub proof fn lemma_put_block_front(o: Seq<int>, j: int, run: Seq<int>)
    requires !o.contains(j), o.no_duplicates()
    ensures put_block(seq![j] + o, Some(j), run) == put_block(o, None, seq![j] + run)
{
    let o1 = seq![j] + o;
    assert(o1[0] == j);
    assert(o1.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < b < o1.len() implies o1[a] != o1[b] by {
            if a == 0 {
                assert(o[b - 1] == o1[b]);
            } else {
                assert(o1[a] == o[a - 1]);
                assert(o1[b] == o[b - 1]);
            }
        }
    }
    lemma_index_in(o1, j);
    assert(index_in(o1, j) == 0);
    assert(put_block(o1, Some(j), run) =~= (seq![j] + run) + o);
}

/// **A run inserted after `left`, in a tree its author knows every element
/// of, reads as one block right after `left`**, each item after the one
/// before.
pub proof fn lemma_insert_run_after(t: TreeS, g: GraphS, e: int, items: Seq<ItemS>, left: Option<int>, minted: int)
    requires
        shaped(t), rooted(t), all_known(t, g, e), g.knows(e, e),
        left matches Some(l) ==> t.node(l),
    ensures ({
        let (u, m) = insert_run(t, g, e, items, left, minted);
        &&& u.order() == put_block(t.order(), left, fresh(t.len() as int, items.len() as int))
        &&& shaped(u)
        &&& rooted(u)
        &&& all_known(u, g, e)
        &&& u.len() == t.len() + items.len()
        &&& m == minted + items.len()
        &&& forall|i: int| 0 <= i < t.len() ==> #[trigger] u.nodes[i] == t.nodes[i]
        &&& forall|k: int| 0 <= k < items.len() ==> {
            &&& (#[trigger] u.nodes[t.len() + k]).author == e
            &&& u.nodes[t.len() + k].minted == minted + k
            &&& u.nodes[t.len() + k].item == items[k]
            &&& u.nodes[t.len() + k].deleted == Set::<int>::empty()
        }
    })
    decreases items.len()
{
    let o = t.order();
    let j = t.len() as int;
    if items.len() == 0 {
        match left {
            None => { assert(put_block(o, left, fresh(j, 0)) =~= o); },
            Some(l) => {
                lemma_order_no_dup(t);
                reveal(TreeS::order);
                lemma_under_root(t, l);
                let c = choose|c: int| #[trigger] t.hangs(c, None, true) && under(t, c, l);
                lemma_children_complete(t, None, true, c);
                lemma_kids(t, None, true);
                let roots = t.children(None, true);
                let k = choose|k: int| 0 <= k < roots.len() && roots[k] == c;
                lemma_read_complete(t, c, l);
                lemma_read_all_has(t, roots, -1, k, l);
                lemma_index_in(o, l);
                let i = index_in(o, l);
                assert(put_block(o, left, fresh(j, 0)) =~= o);
            },
        }
    } else {
        let place = t.anchor(g, e, left);
        let u1 = t.attach(e, minted, items[0], place);
        lemma_anchor_after(t, g, e, minted, items[0], left);
        assert(all_known(u1, g, e)) by {
            assert forall|i: int| u1.node(i) implies g.knows(e, #[trigger] u1.nodes[i].author) by {
                if i < j { assert(u1.nodes[i] == t.nodes[i]); }
            }
        }
        lemma_insert_run_after(u1, g, e, items.drop_first(), Some(j), minted + 1);
        let (u, m) = insert_run(u1, g, e, items.drop_first(), Some(j), minted + 1);
        assert(insert_run(t, g, e, items, left, minted) == (u, m));
        lemma_order_no_dup(t);
        let rest = fresh(j + 1, items.len() - 1);
        assert(fresh(j, items.len() as int) =~= seq![j] + rest);
        assert(!o.contains(j)) by {
            lemma_read_all_nodes(t, t.children(None, true), -1);
            reveal(TreeS::order);
            if o.contains(j) {
                let q = choose|q: int| 0 <= q < o.len() && o[q] == j;
            }
        }
        match left {
            None => {
                lemma_put_block_front(o, j, rest);
            },
            Some(l) => {
                reveal(TreeS::order);
                lemma_under_root(t, l);
                let c = choose|c: int| #[trigger] t.hangs(c, None, true) && under(t, c, l);
                lemma_children_complete(t, None, true, c);
                lemma_kids(t, None, true);
                let roots = t.children(None, true);
                let k = choose|k: int| 0 <= k < roots.len() && roots[k] == c;
                lemma_read_complete(t, c, l);
                lemma_read_all_has(t, roots, -1, k, l);
                lemma_put_block_step(o, l, j, rest);
            },
        }
        assert forall|k: int| 0 <= k < items.len() implies {
            &&& (#[trigger] u.nodes[t.len() + k]).author == e
            &&& u.nodes[t.len() + k].minted == minted + k
            &&& u.nodes[t.len() + k].item == items[k]
            &&& u.nodes[t.len() + k].deleted == Set::<int>::empty()
        } by {
            if k == 0 {
                assert(u.nodes[j] == u1.nodes[j]);
            } else {
                assert(u.nodes[u1.len() + (k - 1)] == u.nodes[t.len() + k]);
                assert(items.drop_first()[k - 1] == items[k]);
            }
        }
        assert forall|i: int| 0 <= i < t.len() implies #[trigger] u.nodes[i] == t.nodes[i] by {
            assert(u.nodes[i] == u1.nodes[i]);
        }
    }
}


// ---------------------------------------------------------------------------
// One revision, as a list edit.
// ---------------------------------------------------------------------------

/// One line of the file: who wrote it, their ordinal for it, and the item.
pub struct LineS {
    pub author: int,
    pub minted: int,
    pub item: ItemS,
}

/// Each insert at a later position than the insert before it, which an
/// ordered document's inserts are.
pub open spec fn inserts_ascend(ops: Seq<OperationS>) -> bool {
    forall|a: int, b: int| 0 <= a < b < ops.len() && !ops[a].delete && !ops[b].delete
        ==> #[trigger] ops[a].at < #[trigger] ops[b].at
}

/// Whether an operation holds against `s`: in range, and every item a
/// delete quotes matching the line it quotes.
pub open spec fn holds_on(s: Seq<LineS>, op: OperationS) -> bool {
    if op.delete {
        &&& 0 <= op.at
        &&& op.at + op.items.len() <= s.len()
        &&& forall|k: int| 0 <= k < op.items.len() ==> matches(op.items[k], #[trigger] s[op.at + k].item)
    } else {
        0 <= op.at <= s.len()
    }
}

/// Whether a delete among the first `k` operations covers position `q`.
pub open spec fn covered(ops: Seq<OperationS>, k: int, q: int) -> bool {
    exists|m: int| 0 <= m < k && #[trigger] ops[m].delete && ops[m].at <= q < ops[m].at + ops[m].items.len()
}

/// How many items the first `k` operations insert.
pub open spec fn minted_before(ops: Seq<OperationS>, k: int) -> int
    decreases k
{
    if k <= 0 {
        0
    } else {
        minted_before(ops, k - 1) + if ops[k - 1].delete { 0 } else { ops[k - 1].items.len() as int }
    }
}

/// The indices the `m`th operation, an insert, mints: fresh from `j0` on,
/// after what the operations before it minted.
pub open spec fn block(ops: Seq<OperationS>, m: int, j0: int) -> Seq<int> {
    fresh(j0 + minted_before(ops, m), ops[m].items.len() as int)
}

/// What the first `k` operations insert at position `q`, by index.
pub open spec fn runs(ops: Seq<OperationS>, k: int, q: int, j0: int) -> Seq<int>
    decreases k
{
    if k <= 0 {
        Seq::empty()
    } else {
        runs(ops, k - 1, q, j0) + if !ops[k - 1].delete && ops[k - 1].at == q { block(ops, k - 1, j0) } else { Seq::empty() }
    }
}

/// Position `q` of a revision's view: what is inserted there, then what
/// stood there.
pub open spec fn slot(prep: Seq<int>, ops: Seq<OperationS>, k: int, j0: int, q: int) -> Seq<int> {
    runs(ops, k, q, j0) + if 0 <= q < prep.len() { seq![prep[q]] } else { Seq::<int>::empty() }
}

/// Positions `a` to `b` of the view, in order.
pub open spec fn between(prep: Seq<int>, ops: Seq<OperationS>, k: int, j0: int, a: int, b: int) -> Seq<int>
    decreases b - a
{
    if b <= a {
        Seq::empty()
    } else {
        between(prep, ops, k, j0, a, b - 1) + slot(prep, ops, k, j0, b - 1)
    }
}

/// The lines the `m`th operation, an insert, adds.
pub open spec fn added(ops: Seq<OperationS>, m: int, e: int) -> Seq<LineS> {
    Seq::new(ops[m].items.len(), |i: int| LineS { author: e, minted: minted_before(ops, m) + i, item: ops[m].items[i] })
}

/// The lines the first `k` operations insert at position `q`.
pub open spec fn new_lines(ops: Seq<OperationS>, k: int, q: int, e: int) -> Seq<LineS>
    decreases k
{
    if k <= 0 {
        Seq::empty()
    } else {
        new_lines(ops, k - 1, q, e) + if !ops[k - 1].delete && ops[k - 1].at == q { added(ops, k - 1, e) } else { Seq::empty() }
    }
}

/// Position `q` of the file after the revision: what it inserts there, then
/// the line that stood there unless a delete covers it.
pub open spec fn lslot(s: Seq<LineS>, ops: Seq<OperationS>, e: int, q: int) -> Seq<LineS> {
    new_lines(ops, ops.len() as int, q, e)
        + if 0 <= q < s.len() && !covered(ops, ops.len() as int, q) { seq![s[q]] } else { Seq::<LineS>::empty() }
}

/// Positions `a` to `b` of the file after the revision.
pub open spec fn rebuild(s: Seq<LineS>, ops: Seq<OperationS>, e: int, a: int, b: int) -> Seq<LineS>
    decreases b - a
{
    if b <= a {
        Seq::empty()
    } else {
        rebuild(s, ops, e, a, b - 1) + lslot(s, ops, e, b - 1)
    }
}

/// **One revision applied to a file as a list**: refused where an operation
/// does not hold, and otherwise each position's inserts, then its line
/// unless deleted — what `linear` does.
pub open spec fn lin_event(s: Seq<LineS>, e: int, ops: Seq<OperationS>) -> Option<Seq<LineS>> {
    if forall|k: int| 0 <= k < ops.len() ==> holds_on(s, #[trigger] ops[k]) {
        Some(rebuild(s, ops, e, 0, s.len() + 1int))
    } else {
        None
    }
}

/// The view splits at any position between its ends.
pub proof fn lemma_between_split(prep: Seq<int>, ops: Seq<OperationS>, k: int, j0: int, a: int, q: int, b: int)
    requires a <= q <= b
    ensures between(prep, ops, k, j0, a, b) == between(prep, ops, k, j0, a, q) + between(prep, ops, k, j0, q, b)
    decreases b - q
{
    if q < b {
        lemma_between_split(prep, ops, k, j0, a, q, b - 1);
        assert(between(prep, ops, k, j0, a, b) =~= between(prep, ops, k, j0, a, q) + between(prep, ops, k, j0, q, b));
    } else {
        assert(between(prep, ops, k, j0, q, b) =~= Seq::<int>::empty());
        assert(between(prep, ops, k, j0, a, b) =~= between(prep, ops, k, j0, a, q) + Seq::<int>::empty());
    }
}

/// And unfolds from the front.
pub proof fn lemma_between_front(prep: Seq<int>, ops: Seq<OperationS>, k: int, j0: int, a: int, b: int)
    requires a < b
    ensures between(prep, ops, k, j0, a, b) == slot(prep, ops, k, j0, a) + between(prep, ops, k, j0, a + 1, b)
{
    lemma_between_split(prep, ops, k, j0, a, a + 1, b);
    assert(between(prep, ops, k, j0, a, a) =~= Seq::<int>::empty());
    assert(between(prep, ops, k, j0, a, a + 1) =~= slot(prep, ops, k, j0, a));
}

/// Positions an operation does not insert at are what they were.
pub proof fn lemma_between_same(prep: Seq<int>, ops: Seq<OperationS>, k: int, j0: int, a: int, b: int)
    requires 0 <= k < ops.len(), ops[k].delete || !(a <= ops[k].at < b)
    ensures between(prep, ops, k + 1, j0, a, b) == between(prep, ops, k, j0, a, b)
    decreases b - a
{
    if a < b {
        lemma_between_same(prep, ops, k, j0, a, b - 1);
        assert(runs(ops, k + 1, b - 1, j0) =~= runs(ops, k, b - 1, j0));
    }
}

/// **An insert at `q`, where nothing was inserted before, puts its block
/// right after what stood at `q - 1`** — at the front where `q` is 0.
pub proof fn lemma_between_insert(prep: Seq<int>, ops: Seq<OperationS>, k: int, j0: int)
    requires
        0 <= k < ops.len(), !ops[k].delete, 0 <= ops[k].at <= prep.len(),
        runs(ops, k, ops[k].at, j0) == Seq::<int>::empty(),
        between(prep, ops, k, j0, 0, prep.len() + 1int).no_duplicates(),
    ensures ({
        let q = ops[k].at;
        let left = if q == 0 { None } else { Some(prep[q - 1]) };
        between(prep, ops, k + 1, j0, 0, prep.len() + 1int)
            == put_block(between(prep, ops, k, j0, 0, prep.len() + 1int), left, block(ops, k, j0))
    })
{
    let q = ops[k].at;
    let n = prep.len() + 1int;
    let b = block(ops, k, j0);
    lemma_between_split(prep, ops, k, j0, 0, q, n);
    lemma_between_split(prep, ops, k + 1, j0, 0, q, n);
    lemma_between_same(prep, ops, k, j0, 0, q);
    lemma_between_front(prep, ops, k, j0, q, n);
    lemma_between_front(prep, ops, k + 1, j0, q, n);
    lemma_between_same(prep, ops, k, j0, q + 1, n);
    assert(runs(ops, k + 1, q, j0) =~= b);
    assert(slot(prep, ops, k + 1, j0, q) =~= b + slot(prep, ops, k, j0, q));
    let (front, back) = (between(prep, ops, k, j0, 0, q), between(prep, ops, k, j0, q, n));
    assert(between(prep, ops, k + 1, j0, q, n) =~= b + back);
    let v = between(prep, ops, k, j0, 0, n);
    assert(v == front + back);
    if q == 0 {
        assert(front =~= Seq::<int>::empty());
        assert(between(prep, ops, k + 1, j0, 0, n) =~= b + v);
    } else {
        // `front` ends with what stood at `q - 1`.
        lemma_between_split(prep, ops, k, j0, 0, q - 1, q);
        assert(between(prep, ops, k, j0, q - 1, q) =~= slot(prep, ops, k, j0, q - 1));
        let x = prep[q - 1];
        assert(front.last() == x);
        assert(v[front.len() - 1] == x);
        assert(v.contains(x));
        lemma_index_in(v, x);
        assert(index_in(v, x) == front.len() - 1);
        assert(v.subrange(0, front.len() as int) =~= front);
        assert(v.subrange(front.len() as int, v.len() as int) =~= back);
        assert(between(prep, ops, k + 1, j0, 0, n) =~= front + b + back);
    }
}


// ---------------------------------------------------------------------------
// Filtering, with blocks put in.
// ---------------------------------------------------------------------------

/// Filtering a list everything passes leaves it as it is.
pub proof fn lemma_sel_all(s: Seq<int>, p: spec_fn(int) -> bool)
    requires forall|k: int| 0 <= k < s.len() ==> p(#[trigger] s[k])
    ensures sel(s, p) == s
    decreases s.len()
{
    if s.len() > 0 {
        let d = s.drop_last();
        assert forall|k: int| 0 <= k < d.len() implies p(#[trigger] d[k]) by { assert(d[k] == s[k]); }
        lemma_sel_all(d, p);
        assert(p(s.last()));
        assert(sel(s, p) =~= s);
    }
}

/// Filters that agree on a list filter it alike.
pub proof fn lemma_sel_same(s: Seq<int>, p: spec_fn(int) -> bool, q: spec_fn(int) -> bool)
    requires forall|k: int| 0 <= k < s.len() ==> (p(#[trigger] s[k]) <==> q(s[k]))
    ensures sel(s, p) == sel(s, q)
    decreases s.len()
{
    if s.len() > 0 {
        let d = s.drop_last();
        assert forall|k: int| 0 <= k < d.len() implies (p(#[trigger] d[k]) <==> q(d[k])) by { assert(d[k] == s[k]); }
        lemma_sel_same(d, p, q);
    }
}

/// **Filtering commutes with putting in a block** that passes, after an
/// element that passes.
pub proof fn lemma_sel_put_block(o: Seq<int>, p: spec_fn(int) -> bool, left: Option<int>, run: Seq<int>)
    requires
        o.no_duplicates(),
        left matches Some(x) ==> o.contains(x) && p(x),
        forall|k: int| 0 <= k < run.len() ==> p(#[trigger] run[k]),
    ensures sel(put_block(o, left, run), p) == put_block(sel(o, p), left, run)
{
    lemma_sel_all(run, p);
    match left {
        None => {
            lemma_sel_add(run, o, p);
        },
        Some(x) => {
            lemma_index_in(o, x);
            let i = index_in(o, x);
            let (a, b) = (o.subrange(0, i), o.subrange(i + 1, o.len() as int));
            assert(o.subrange(0, i + 1) =~= a + seq![x]);
            assert(o =~= a + seq![x] + b);
            lemma_sel_add(a, seq![x], p);
            lemma_sel_single(x, p);
            lemma_sel_add(a + seq![x], b, p);
            lemma_sel_add(a + seq![x], run, p);
            lemma_sel_add(a + seq![x] + run, b, p);
            let so = sel(o, p);
            let sa = sel(a, p);
            assert(so =~= sa + seq![x] + sel(b, p));
            lemma_sel_no_dup(o, p);
            assert(so[sa.len() as int] == x);
            lemma_index_in(so, x);
            assert(index_in(so, x) == sa.len());
            assert(so.subrange(0, sa.len() as int + 1) =~= sa + seq![x]);
            assert(so.subrange(sa.len() as int + 1, so.len() as int) =~= sel(b, p));
            assert(put_block(o, left, run) =~= a + seq![x] + run + b);
            assert(put_block(so, left, run) =~= sa + seq![x] + run + sel(b, p));
        },
    }
}


// ---------------------------------------------------------------------------
// Removals, which move nothing.
// ---------------------------------------------------------------------------

/// Two trees placed alike read alike.
pub proof fn lemma_read_placed(t: TreeS, u: TreeS, x: int)
    requires t.len() == u.len(), forall|i: int| 0 <= i < t.len() ==> #[trigger] placed_alike(t, u, i)
    ensures u.read(x) == t.read(x)
    decreases t.len() - x, 1int, 0int
{
    if t.node(x) {
        lemma_children_placed(t, u, Some(x), false);
        lemma_children_placed(t, u, Some(x), true);
        lemma_read_all_placed(t, u, t.children(Some(x), false), x);
        lemma_read_all_placed(t, u, t.children(Some(x), true), x);
    }
}

pub proof fn lemma_read_all_placed(t: TreeS, u: TreeS, kids: Seq<int>, above: int)
    requires t.len() == u.len(), forall|i: int| 0 <= i < t.len() ==> #[trigger] placed_alike(t, u, i)
    ensures u.read_all(kids, above) == t.read_all(kids, above)
    decreases t.len() - above, 0int, kids.len()
{
    if kids.len() > 0 {
        lemma_read_all_placed(t, u, kids.drop_first(), above);
        if above < kids[0] < t.len() {
            lemma_read_placed(t, u, kids[0]);
        }
    }
}

/// And so read the whole document alike.
pub proof fn lemma_order_placed(t: TreeS, u: TreeS)
    requires t.len() == u.len(), forall|i: int| 0 <= i < t.len() ==> #[trigger] placed_alike(t, u, i)
    ensures u.order() == t.order()
{
    reveal(TreeS::order);
    lemma_children_placed(t, u, None, true);
    lemma_read_all_placed(t, u, t.children(None, true), -1);
}

/// A delete's items held against the view and marked: refused where one
/// does not match, and otherwise each quoted element marked removed by `e`
/// and nothing else changed.
pub proof fn lemma_delete_run_marks(t: TreeS, g: GraphS, e: int, prep: Seq<int>, at: int, items: Seq<ItemS>, x: int)
    requires
        0 <= x <= items.len(), 0 <= at, at + items.len() <= prep.len(),
        forall|q: int| 0 <= q < prep.len() ==> 0 <= #[trigger] prep[q] < t.len(),
    ensures
        match delete_run(t, g, e, prep, at, items, x) {
            None => exists|y: int| x <= y < items.len() && !matches(items[y], #[trigger] t.nodes[prep[at + y]].item),
            Some(u) => {
                &&& forall|y: int| x <= y < items.len() ==> matches(items[y], #[trigger] t.nodes[prep[at + y]].item)
                &&& u.len() == t.len()
                &&& forall|i: int| 0 <= i < t.len() ==> {
                    &&& #[trigger] placed_alike(t, u, i)
                    &&& u.nodes[i].item == t.nodes[i].item
                    &&& u.nodes[i].deleted == if prep.subrange(at + x, at + items.len()).contains(i) {
                        t.nodes[i].deleted.insert(e)
                    } else {
                        t.nodes[i].deleted
                    }
                }
            },
        },
    decreases items.len() - x
{
    if x < items.len() {
        let target = prep[at + x];
        if matches(items[x], t.nodes[target].item) {
            let next = t.delete(target, e);
            lemma_delete_run_marks(next, g, e, prep, at, items, x + 1);
            let tail = prep.subrange(at + x + 1, at + items.len());
            let here = prep.subrange(at + x, at + items.len());
            assert(here =~= seq![target] + tail);
            match delete_run(next, g, e, prep, at, items, x + 1) {
                None => {
                    let y = choose|y: int| x + 1 <= y < items.len() && !matches(items[y], #[trigger] next.nodes[prep[at + y]].item);
                    assert(next.nodes[prep[at + y]].item == t.nodes[prep[at + y]].item);
                },
                Some(u) => {
                    assert forall|y: int| x <= y < items.len() implies matches(items[y], #[trigger] t.nodes[prep[at + y]].item) by {
                        if y > x { assert(next.nodes[prep[at + y]].item == t.nodes[prep[at + y]].item); }
                    }
                    assert forall|i: int| 0 <= i < t.len() implies {
                        &&& #[trigger] placed_alike(t, u, i)
                        &&& u.nodes[i].item == t.nodes[i].item
                        &&& u.nodes[i].deleted == if here.contains(i) {
                            t.nodes[i].deleted.insert(e)
                        } else {
                            t.nodes[i].deleted
                        }
                    } by {
                        assert(placed_alike(next, u, i));
                        if here.contains(i) {
                            if i == target {
                                assert(u.nodes[i].deleted == next.nodes[i].deleted.insert(e) || u.nodes[i].deleted == next.nodes[i].deleted);
                                assert(next.nodes[i].deleted == t.nodes[i].deleted.insert(e));
                                assert(t.nodes[i].deleted.insert(e).insert(e) =~= t.nodes[i].deleted.insert(e));
                            } else {
                                let q = choose|q: int| 0 <= q < here.len() && here[q] == i;
                                assert(q > 0);
                                assert(tail[q - 1] == i);
                                assert(next.nodes[i] == t.nodes[i]);
                            }
                        } else {
                            if tail.contains(i) {
                                let q = choose|q: int| 0 <= q < tail.len() && tail[q] == i;
                                assert(here[q + 1] == i);
                            }
                            assert(i != target) by { assert(here[0] == target); }
                            assert(next.nodes[i] == t.nodes[i]);
                        }
                    }
                },
            }
        }
    } else {
        assert(prep.subrange(at + x, at + items.len()) =~= Seq::<int>::empty());
        assert forall|i: int| 0 <= i < t.len() implies #[trigger] placed_alike(t, t, i) by {}
    }
}


// ---------------------------------------------------------------------------
// A revision partway through.
// ---------------------------------------------------------------------------

/// What a revision's view holds: what stood when it began, and what it adds.
pub open spec fn in_view(t0: TreeS, i: int) -> bool {
    (0 <= i < t0.len() && t0.standing(i)) || t0.len() <= i
}

/// Element `i` as a line.
pub open spec fn line(t: TreeS, i: int) -> LineS {
    LineS { author: t.nodes[i].author, minted: t.nodes[i].minted, item: t.nodes[i].item }
}

/// Elements as lines.
pub open spec fn lines_of(t: TreeS, s: Seq<int>) -> Seq<LineS> {
    s.map_values(|i: int| line(t, i))
}

/// The file a tree reads as, line by line.
pub open spec fn lines(t: TreeS) -> Seq<LineS> {
    lines_of(t, sel(t.order(), |i: int| t.standing(i)))
}

/// Whether `i` stands in the view at a position a delete among the first `k`
/// operations covers.
pub open spec fn marked(prep: Seq<int>, ops: Seq<OperationS>, k: int, i: int) -> bool {
    exists|q: int| 0 <= q < prep.len() && prep[q] == i && #[trigger] covered(ops, k, q)
}

/// Revision `e`, begun at `t0` with view `prep`, after its first `k`
/// operations, is the tree `t`.
pub open spec fn partway(t0: TreeS, t: TreeS, g: GraphS, e: int, prep: Seq<int>, ops: Seq<OperationS>, k: int) -> bool {
    &&& shaped(t)
    &&& rooted(t)
    &&& all_known(t, g, e)
    &&& t.len() == t0.len() + minted_before(ops, k)
    &&& forall|i: int| 0 <= i < t0.len() ==> {
        &&& #[trigger] placed_alike(t0, t, i)
        &&& t.nodes[i].item == t0.nodes[i].item
        &&& t.nodes[i].deleted == if marked(prep, ops, k, i) { t0.nodes[i].deleted.insert(e) } else { t0.nodes[i].deleted }
    }
    &&& forall|i: int| t0.len() <= i < t.len() ==> (#[trigger] t.nodes[i]).author == e
        && t.nodes[i].deleted == Set::<int>::empty()
    &&& forall|m: int, x: int| 0 <= m < k && !ops[m].delete && 0 <= x < ops[m].items.len() ==> {
        &&& (#[trigger] t.nodes[t0.len() + minted_before(ops, m) + x]).minted == minted_before(ops, m) + x
        &&& t.nodes[t0.len() + minted_before(ops, m) + x].item == ops[m].items[x]
    }
    &&& sel(t.order(), |i: int| in_view(t0, i)) == between(prep, ops, k, t0.len() as int, 0, prep.len() + 1int)
}

/// `partway`, from its parts.
pub proof fn lemma_partway(t0: TreeS, t: TreeS, g: GraphS, e: int, prep: Seq<int>, ops: Seq<OperationS>, k: int)
    requires
        shaped(t),
        rooted(t),
        all_known(t, g, e),
        t.len() == t0.len() + minted_before(ops, k),
        forall|i: int| 0 <= i < t0.len() ==> {
            &&& #[trigger] placed_alike(t0, t, i)
            &&& t.nodes[i].item == t0.nodes[i].item
            &&& t.nodes[i].deleted == if marked(prep, ops, k, i) { t0.nodes[i].deleted.insert(e) } else { t0.nodes[i].deleted }
        },
        forall|i: int| t0.len() <= i < t.len() ==> (#[trigger] t.nodes[i]).author == e
            && t.nodes[i].deleted == Set::<int>::empty(),
        forall|m: int, x: int| 0 <= m < k && !ops[m].delete && 0 <= x < ops[m].items.len() ==> {
            &&& (#[trigger] t.nodes[t0.len() + minted_before(ops, m) + x]).minted == minted_before(ops, m) + x
            &&& t.nodes[t0.len() + minted_before(ops, m) + x].item == ops[m].items[x]
        },
        sel(t.order(), |i: int| in_view(t0, i)) == between(prep, ops, k, t0.len() as int, 0, prep.len() + 1int),
    ensures partway(t0, t, g, e, prep, ops, k)
{
}

/// The view a revision begins with: what stands, in order.
pub open spec fn fair_view(t0: TreeS, prep: Seq<int>) -> bool {
    &&& prep == sel(t0.order(), |i: int| t0.standing(i))
    &&& prep.no_duplicates()
    &&& forall|q: int| 0 <= q < prep.len() ==> 0 <= #[trigger] prep[q] < t0.len() && t0.standing(prep[q])
}

/// Minting grows.
pub proof fn lemma_minted_grows(ops: Seq<OperationS>, a: int, b: int)
    requires 0 <= a <= b
    ensures minted_before(ops, a) <= minted_before(ops, b)
    decreases b - a
{
    if a < b { lemma_minted_grows(ops, a, b - 1); }
}

/// Nothing inserted at `q` by operations before the first insert there.
pub proof fn lemma_runs_empty(ops: Seq<OperationS>, k: int, q: int, j0: int)
    requires forall|m: int| 0 <= m < k && !ops[m].delete ==> ops[m].at != q
    ensures runs(ops, k, q, j0) == Seq::<int>::empty()
    decreases k
{
    if k > 0 {
        lemma_runs_empty(ops, k - 1, q, j0);
    }
}

/// Every node is read somewhere in the document.
pub proof fn lemma_in_order(t: TreeS, x: int)
    requires shaped(t), rooted(t), t.node(x)
    ensures t.order().contains(x)
{
    reveal(TreeS::order);
    lemma_under_root(t, x);
    let c = choose|c: int| #[trigger] t.hangs(c, None, true) && under(t, c, x);
    lemma_children_complete(t, None, true, c);
    lemma_kids(t, None, true);
    let roots = t.children(None, true);
    let k = choose|k: int| 0 <= k < roots.len() && roots[k] == c;
    lemma_read_complete(t, c, x);
    lemma_read_all_has(t, roots, -1, k, x);
}

/// One delete, held against the view: refused where an item does not match,
/// and otherwise the revision one operation further on.
pub proof fn lemma_ops_delete(t0: TreeS, t: TreeS, g: GraphS, e: int, prep: Seq<int>, ops: Seq<OperationS>, k: int)
    requires
        0 <= k < ops.len(), ops[k].delete,
        0 <= ops[k].at, ops[k].at + ops[k].items.len() <= prep.len(),
        fair_view(t0, prep),
        partway(t0, t, g, e, prep, ops, k),
    ensures ({
        let s0 = lines_of(t0, prep);
        let op = ops[k];
        match delete_run(t, g, e, prep, op.at, op.items, 0) {
            None => !holds_on(s0, op),
            Some(next) => holds_on(s0, op) && partway(t0, next, g, e, prep, ops, k + 1),
        }
    })
{
    let s0 = lines_of(t0, prep);
    let j0 = t0.len() as int;
    let op = ops[k];
    let view = |i: int| in_view(t0, i);
    lemma_minted_grows(ops, 0, k);
    assert forall|q: int| 0 <= q < prep.len() implies 0 <= #[trigger] prep[q] < t.len() by {}
    lemma_delete_run_marks(t, g, e, prep, op.at, op.items, 0);
    match delete_run(t, g, e, prep, op.at, op.items, 0) {
        None => {
            let y = choose|y: int| 0 <= y < op.items.len() && !matches(op.items[y], #[trigger] t.nodes[prep[op.at + y]].item);
            assert(placed_alike(t0, t, prep[op.at + y]));
            assert(t.nodes[prep[op.at + y]].item == t0.nodes[prep[op.at + y]].item);
            assert(s0[op.at + y] == line(t0, prep[op.at + y]));
            assert(!matches(op.items[y], s0[op.at + y].item));
            assert(!holds_on(s0, op));
        },
        Some(next) => {
            assert forall|y: int| 0 <= y < op.items.len() implies matches(op.items[y], #[trigger] s0[op.at + y].item) by {
                assert(placed_alike(t0, t, prep[op.at + y]));
                assert(s0[op.at + y] == line(t0, prep[op.at + y]));
                assert(matches(op.items[y], t.nodes[prep[op.at + y]].item));
            }
            lemma_order_placed(t, next);
            lemma_between_same(prep, ops, k, j0, 0, prep.len() + 1int);
            let range = prep.subrange(op.at, op.at + op.items.len());
            assert forall|i: int| 0 <= i < j0 implies {
                &&& #[trigger] placed_alike(t0, next, i)
                &&& next.nodes[i].item == t0.nodes[i].item
                &&& next.nodes[i].deleted == if marked(prep, ops, k + 1, i) { t0.nodes[i].deleted.insert(e) } else { t0.nodes[i].deleted }
            } by {
                assert(placed_alike(t0, t, i));
                assert(placed_alike(t, next, i));
                if range.contains(i) {
                    let y = choose|y: int| 0 <= y < range.len() && range[y] == i;
                    assert(prep[op.at + y] == i);
                    assert(covered(ops, k + 1, op.at + y));
                    assert(marked(prep, ops, k + 1, i));
                    assert(t0.nodes[i].deleted.insert(e).insert(e) =~= t0.nodes[i].deleted.insert(e));
                } else {
                    if marked(prep, ops, k + 1, i) {
                        let q = choose|q: int| 0 <= q < prep.len() && prep[q] == i && #[trigger] covered(ops, k + 1, q);
                        let m = choose|m: int| 0 <= m < k + 1 && #[trigger] ops[m].delete && ops[m].at <= q < ops[m].at + ops[m].items.len();
                        if m == k {
                            assert(range[q - op.at] == i);
                        } else {
                            assert(covered(ops, k, q));
                        }
                    }
                    if marked(prep, ops, k, i) {
                        let q = choose|q: int| 0 <= q < prep.len() && prep[q] == i && #[trigger] covered(ops, k, q);
                        let m = choose|m: int| 0 <= m < k && #[trigger] ops[m].delete && ops[m].at <= q < ops[m].at + ops[m].items.len();
                        assert(covered(ops, k + 1, q));
                    }
                }
            }
            assert forall|i: int| j0 <= i < next.len() implies (#[trigger] next.nodes[i]).author == e
                && next.nodes[i].deleted == Set::<int>::empty() by {
                assert(placed_alike(t, next, i));
                assert(!range.contains(i)) by {
                    if range.contains(i) {
                        let y = choose|y: int| 0 <= y < range.len() && range[y] == i;
                        assert(prep[op.at + y] == i);
                    }
                }
            }
            assert forall|m: int, x: int| 0 <= m < k + 1 && !ops[m].delete && 0 <= x < ops[m].items.len() implies {
                &&& (#[trigger] next.nodes[j0 + minted_before(ops, m) + x]).minted == minted_before(ops, m) + x
                &&& next.nodes[j0 + minted_before(ops, m) + x].item == ops[m].items[x]
            } by {
                lemma_minted_grows(ops, m + 1, k);
                lemma_minted_grows(ops, 0, m);
                assert(minted_before(ops, m + 1) == minted_before(ops, m) + ops[m].items.len());
                assert(placed_alike(t, next, j0 + minted_before(ops, m) + x));
            }
            assert forall|i: int| next.node(i) implies g.knows(e, #[trigger] next.nodes[i].author) by {
                assert(placed_alike(t, next, i));
            }
            assert forall|i: int| next.node(i) implies match (#[trigger] next.nodes[i]).parent {
                Some(p) => 0 <= p < i,
                None => true,
            } by { assert(placed_alike(t, next, i)); }
            assert forall|i: int| next.node(i) && (#[trigger] next.nodes[i]).parent is None implies next.nodes[i].right by {
                assert(placed_alike(t, next, i));
            }
            assert(minted_before(ops, k + 1) == minted_before(ops, k));
            assert(next.len() == t0.len() + minted_before(ops, k + 1));
            assert(sel(next.order(), view) == between(prep, ops, k + 1, j0, 0, prep.len() + 1int));
            assert(shaped(next));
            assert(rooted(next));
            assert(all_known(next, g, e));
            assert(holds_on(s0, op));
            lemma_partway(t0, next, g, e, prep, ops, k + 1);
        },
    }
}

/// One insert: in range exactly where it holds, and then the revision one
/// operation further on, its block where the view says.
pub proof fn lemma_ops_insert(t0: TreeS, t: TreeS, g: GraphS, e: int, prep: Seq<int>, ops: Seq<OperationS>, k: int)
    requires
        0 <= k < ops.len(), !ops[k].delete,
        0 <= ops[k].at <= prep.len(),
        inserts_ascend(ops),
        g.knows(e, e),
        fair_view(t0, prep),
        partway(t0, t, g, e, prep, ops, k),
    ensures ({
        let op = ops[k];
        let left = if op.at == 0 { None } else { Some(prep[op.at - 1]) };
        let (u, m) = insert_run(t, g, e, op.items, left, minted_before(ops, k));
        &&& holds_on(lines_of(t0, prep), op)
        &&& m == minted_before(ops, k + 1)
        &&& partway(t0, u, g, e, prep, ops, k + 1)
    })
{
    let j0 = t0.len() as int;
    let op = ops[k];
    let q = op.at;
    let minted = minted_before(ops, k);
    let view = |i: int| in_view(t0, i);
    lemma_minted_grows(ops, 0, k);
    let left = if q == 0 { None } else { Some(prep[q - 1]) };
    lemma_insert_run_after(t, g, e, op.items, left, minted);
    let (u, m2) = insert_run(t, g, e, op.items, left, minted);
    let b = block(ops, k, j0);
    assert(fresh(t.len() as int, op.items.len() as int) =~= b);
    lemma_order_no_dup(t);
    if q > 0 {
        lemma_in_order(t, prep[q - 1]);
    }
    assert forall|x: int| 0 <= x < b.len() implies view(#[trigger] b[x]) by {}
    lemma_sel_put_block(t.order(), view, left, b);
    lemma_sel_no_dup(t.order(), view);
    assert forall|m: int| 0 <= m < k && !ops[m].delete implies ops[m].at != q by {
        assert(ops[m].at < ops[k].at);
    }
    lemma_runs_empty(ops, k, q, j0);
    lemma_between_insert(prep, ops, k, j0);
    assert(minted_before(ops, k + 1) == minted + op.items.len());
    assert(u.len() == t0.len() + minted_before(ops, k + 1));
    assert forall|i: int| 0 <= i < j0 implies {
        &&& #[trigger] placed_alike(t0, u, i)
        &&& u.nodes[i].item == t0.nodes[i].item
        &&& u.nodes[i].deleted == if marked(prep, ops, k + 1, i) { t0.nodes[i].deleted.insert(e) } else { t0.nodes[i].deleted }
    } by {
        assert(placed_alike(t0, t, i));
        assert(u.nodes[i] == t.nodes[i]);
        if marked(prep, ops, k + 1, i) {
            let q2 = choose|q2: int| 0 <= q2 < prep.len() && prep[q2] == i && #[trigger] covered(ops, k + 1, q2);
            let m = choose|m: int| 0 <= m < k + 1 && #[trigger] ops[m].delete && ops[m].at <= q2 < ops[m].at + ops[m].items.len();
            assert(covered(ops, k, q2));
        }
        if marked(prep, ops, k, i) {
            let q2 = choose|q2: int| 0 <= q2 < prep.len() && prep[q2] == i && #[trigger] covered(ops, k, q2);
            let m = choose|m: int| 0 <= m < k && #[trigger] ops[m].delete && ops[m].at <= q2 < ops[m].at + ops[m].items.len();
            assert(covered(ops, k + 1, q2));
        }
    }
    assert forall|i: int| j0 <= i < u.len() implies (#[trigger] u.nodes[i]).author == e
        && u.nodes[i].deleted == Set::<int>::empty() by {
        if i < t.len() {
            assert(u.nodes[i] == t.nodes[i]);
        } else {
            assert(u.nodes[t.len() + (i - t.len())] == u.nodes[i]);
        }
    }
    assert forall|m: int, x: int| 0 <= m < k + 1 && !ops[m].delete && 0 <= x < ops[m].items.len() implies {
        &&& (#[trigger] u.nodes[j0 + minted_before(ops, m) + x]).minted == minted_before(ops, m) + x
        &&& u.nodes[j0 + minted_before(ops, m) + x].item == ops[m].items[x]
    } by {
        if m < k {
            lemma_minted_grows(ops, m + 1, k);
            lemma_minted_grows(ops, 0, m);
            assert(minted_before(ops, m + 1) == minted_before(ops, m) + ops[m].items.len());
            assert(u.nodes[j0 + minted_before(ops, m) + x] == t.nodes[j0 + minted_before(ops, m) + x]);
        } else {
            assert(u.nodes[t.len() + x] == u.nodes[j0 + minted_before(ops, m) + x]);
        }
    }
    assert(sel(u.order(), view) == between(prep, ops, k + 1, j0, 0, prep.len() + 1int));
    lemma_partway(t0, u, g, e, prep, ops, k + 1);
}

/// **A revision's operations, replayed in a tree its author knows every
/// element of, refuse exactly where one does not hold against the view, and
/// otherwise leave the tree the revision ends at.**
pub proof fn lemma_ops_chain(t0: TreeS, t: TreeS, g: GraphS, e: int, prep: Seq<int>, ops: Seq<OperationS>, k: int)
    requires
        0 <= k <= ops.len(),
        inserts_ascend(ops),
        g.knows(e, e),
        fair_view(t0, prep),
        partway(t0, t, g, e, prep, ops, k),
    ensures ({
        let s0 = lines_of(t0, prep);
        match replay_ops(t, g, e, prep, ops, k, minted_before(ops, k)) {
            None => exists|m: int| k <= m < ops.len() && !holds_on(s0, #[trigger] ops[m]),
            Some(u) => (forall|m: int| k <= m < ops.len() ==> holds_on(s0, #[trigger] ops[m]))
                && partway(t0, u, g, e, prep, ops, ops.len() as int),
        }
    })
    decreases ops.len() - k
{
    let s0 = lines_of(t0, prep);
    if k < ops.len() {
        let op = ops[k];
        if op.delete {
            if op.at < 0 || op.at + op.items.len() > prep.len() {
                assert(!holds_on(s0, ops[k]));
            } else {
                lemma_ops_delete(t0, t, g, e, prep, ops, k);
                if let Some(next) = delete_run(t, g, e, prep, op.at, op.items, 0) {
                    assert(minted_before(ops, k + 1) == minted_before(ops, k));
                    lemma_ops_chain(t0, next, g, e, prep, ops, k + 1);
                }
            }
        } else {
            if op.at < 0 || op.at > prep.len() {
                assert(!holds_on(s0, ops[k]));
            } else {
                lemma_ops_insert(t0, t, g, e, prep, ops, k);
                let left = if op.at == 0 { None } else { Some(prep[op.at - 1]) };
                let (u, m) = insert_run(t, g, e, op.items, left, minted_before(ops, k));
                lemma_ops_chain(t0, u, g, e, prep, ops, k + 1);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// A revision, begun and ended.
// ---------------------------------------------------------------------------

/// Before any insert, the view is what stood.
pub proof fn lemma_between_none(prep: Seq<int>, ops: Seq<OperationS>, j0: int, b: int)
    requires 0 <= b <= prep.len() + 1
    ensures between(prep, ops, 0, j0, 0, b) == prep.subrange(0, if b <= prep.len() { b } else { prep.len() as int })
    decreases b
{
    if b > 0 {
        lemma_between_none(prep, ops, j0, b - 1);
        assert(runs(ops, 0, b - 1, j0) =~= Seq::<int>::empty());
        if b - 1 < prep.len() {
            assert(prep.subrange(0, b) =~= prep.subrange(0, b - 1) + seq![prep[b - 1]]);
        } else {
            assert(slot(prep, ops, 0, j0, b - 1) =~= Seq::<int>::empty());
        }
    } else {
        assert(prep.subrange(0, 0) =~= Seq::<int>::empty());
    }
}

/// A revision begins partway through at its first operation.
pub proof fn lemma_partway_start(t0: TreeS, g: GraphS, e: int, prep: Seq<int>, ops: Seq<OperationS>)
    requires shaped(t0), rooted(t0), all_known(t0, g, e), fair_view(t0, prep)
    ensures partway(t0, t0, g, e, prep, ops, 0)
{
    let view = |i: int| in_view(t0, i);
    let stands = |i: int| t0.standing(i);
    reveal(TreeS::order);
    lemma_read_all_nodes(t0, t0.children(None, true), -1);
    assert forall|k: int| 0 <= k < t0.order().len() implies (view(#[trigger] t0.order()[k]) <==> stands(t0.order()[k])) by {
        assert(t0.node(t0.order()[k]));
    }
    lemma_sel_same(t0.order(), view, stands);
    lemma_between_none(prep, ops, t0.len() as int, prep.len() + 1int);
    assert(prep.subrange(0, prep.len() as int) =~= prep);
    assert forall|i: int| 0 <= i < t0.len() implies {
        &&& #[trigger] placed_alike(t0, t0, i)
        &&& t0.nodes[i].item == t0.nodes[i].item
        &&& t0.nodes[i].deleted == if marked(prep, ops, 0, i) { t0.nodes[i].deleted.insert(e) } else { t0.nodes[i].deleted }
    } by {
        if marked(prep, ops, 0, i) {
            let q = choose|q: int| 0 <= q < prep.len() && prep[q] == i && #[trigger] covered(ops, 0, q);
        }
    }
    lemma_partway(t0, t0, g, e, prep, ops, 0);
}

/// What the first `k` operations insert at `q`, read as lines.
pub proof fn lemma_runs_lines(t0: TreeS, u: TreeS, g: GraphS, e: int, prep: Seq<int>, ops: Seq<OperationS>, kk: int, k: int, q: int)
    requires 0 <= k <= kk <= ops.len(), partway(t0, u, g, e, prep, ops, kk)
    ensures lines_of(u, runs(ops, k, q, t0.len() as int)) == new_lines(ops, k, q, e)
    decreases k
{
    let j0 = t0.len() as int;
    if k > 0 {
        lemma_runs_lines(t0, u, g, e, prep, ops, kk, k - 1, q);
        let m = k - 1;
        if !ops[m].delete && ops[m].at == q {
            let b = block(ops, m, j0);
            lemma_minted_grows(ops, 0, m);
            assert(lines_of(u, b) =~= added(ops, m, e)) by {
                assert forall|x: int| 0 <= x < b.len() implies #[trigger] lines_of(u, b)[x] == added(ops, m, e)[x] by {
                    assert(b[x] == j0 + minted_before(ops, m) + x);
                    lemma_minted_grows(ops, m + 1, kk);
                    assert(minted_before(ops, m + 1) == minted_before(ops, m) + ops[m].items.len());
                    assert(u.nodes[j0 + minted_before(ops, m) + x].minted == minted_before(ops, m) + x);
                }
            }
            assert(lines_of(u, runs(ops, k, q, j0)) =~= lines_of(u, runs(ops, m, q, j0)) + lines_of(u, b));
        } else {
            assert(runs(ops, k, q, j0) =~= runs(ops, m, q, j0));
        }
    }
}

/// **A revision ended, read line by line, is its lines rebuilt.**
pub proof fn lemma_partway_end(t0: TreeS, u: TreeS, g: GraphS, e: int, prep: Seq<int>, ops: Seq<OperationS>, a: int, b: int)
    requires
        0 <= a <= b <= prep.len() + 1,
        fair_view(t0, prep),
        partway(t0, u, g, e, prep, ops, ops.len() as int),
    ensures
        lines_of(u, sel(between(prep, ops, ops.len() as int, t0.len() as int, a, b), |i: int| u.standing(i)))
            == rebuild(lines_of(t0, prep), ops, e, a, b),
    decreases b - a
{
    let kk = ops.len() as int;
    let j0 = t0.len() as int;
    let stands = |i: int| u.standing(i);
    let s0 = lines_of(t0, prep);
    if a < b {
        lemma_partway_end(t0, u, g, e, prep, ops, a, b - 1);
        let q = b - 1;
        let r = runs(ops, kk, q, j0);
        lemma_minted_grows(ops, 0, kk);
        assert forall|x: int| 0 <= x < r.len() implies stands(#[trigger] r[x]) by {
            lemma_runs_new(ops, kk, q, j0, x);
            assert(u.nodes[r[x]].deleted == Set::<int>::empty());
        }
        lemma_sel_all(r, stands);
        lemma_runs_lines(t0, u, g, e, prep, ops, kk, kk, q);
        let tail = if 0 <= q < prep.len() { seq![prep[q]] } else { Seq::<int>::empty() };
        lemma_sel_add(between(prep, ops, kk, j0, a, b - 1), slot(prep, ops, kk, j0, q), stands);
        lemma_sel_add(r, tail, stands);
        if 0 <= q < prep.len() {
            let i = prep[q];
            lemma_sel_single(i, stands);
            assert(placed_alike(t0, u, i));
            assert(t0.standing(i));
            assert(t0.nodes[i].deleted =~= Set::<int>::empty());
            // Standing now exactly where no delete covered it.
            assert(marked(prep, ops, kk, i) <==> covered(ops, kk, q)) by {
                if marked(prep, ops, kk, i) {
                    let q2 = choose|q2: int| 0 <= q2 < prep.len() && prep[q2] == i && #[trigger] covered(ops, kk, q2);
                    assert(q2 == q) by {
                        if q2 != q {
                            if q2 < q { assert(prep[q2] != prep[q]); } else { assert(prep[q] != prep[q2]); }
                        }
                    }
                }
            }
            if covered(ops, kk, q) {
                assert(u.nodes[i].deleted.contains(e));
                assert(!u.standing(i));
            } else {
                assert(u.nodes[i].deleted =~= Set::<int>::empty());
            }
            assert(line(u, i) == s0[q]);
        }
        let got = sel(slot(prep, ops, kk, j0, q), stands);
        assert(lines_of(u, got) =~= lslot(s0, ops, e, q));
        assert(lines_of(u, sel(between(prep, ops, kk, j0, a, b), stands))
            =~= lines_of(u, sel(between(prep, ops, kk, j0, a, b - 1), stands)) + lines_of(u, got));
    } else {
        assert(sel(Seq::<int>::empty(), stands) == Seq::<int>::empty());
        assert(lines_of(u, Seq::<int>::empty()) =~= Seq::<LineS>::empty());
    }
}

/// What operations insert is fresh: at or past `j0`.
pub proof fn lemma_runs_new(ops: Seq<OperationS>, k: int, q: int, j0: int, x: int)
    requires 0 <= x < runs(ops, k, q, j0).len(), 0 <= k <= ops.len()
    ensures j0 <= runs(ops, k, q, j0)[x] < j0 + minted_before(ops, k)
    decreases k
{
    if k > 0 {
        let prev = runs(ops, k - 1, q, j0);
        lemma_minted_grows(ops, 0, k - 1);
        if x < prev.len() {
            lemma_runs_new(ops, k - 1, q, j0, x);
            lemma_minted_grows(ops, k - 1, k);
        } else {
            assert(runs(ops, k, q, j0)[x] == block(ops, k - 1, j0)[x - prev.len()]);
        }
    }
}


// ---------------------------------------------------------------------------
// The fast path, and the walk over a chain.
// ---------------------------------------------------------------------------

/// Everything in the tree was written and removed by events `e` had seen.
pub open spec fn seen_all(t: TreeS, g: GraphS, e: int) -> bool {
    forall|i: int| t.node(i) ==> {
        &&& g.saw(e, #[trigger] t.nodes[i].author)
        &&& forall|d: int| t.nodes[i].deleted.contains(d) ==> g.saw(e, d)
    }
}

/// **One revision, replayed in a chain, is one revision applied to the list
/// of what stands**: refused exactly where the list edit refuses, and
/// otherwise reading as its result.
pub proof fn lemma_event_chain(t0: TreeS, g: GraphS, e: int, ops: Seq<OperationS>)
    requires
        shaped(t0), rooted(t0), all_known(t0, g, e), g.knows(e, e), seen_all(t0, g, e),
        inserts_ascend(ops),
    ensures ({
        let prep = t0.visible(g, e);
        let replayed = replay_ops(t0, g, e, prep, ops, 0, 0);
        &&& (replayed is Some) == (lin_event(lines(t0), e, ops) is Some)
        &&& replayed matches Some(u) ==> {
            &&& lines(u) == lin_event(lines(t0), e, ops)->Some_0
            &&& partway(t0, u, g, e, prep, ops, ops.len() as int)
        }
    })
{
    let prep = t0.visible(g, e);
    let order = t0.order();
    let seen = |i: int| t0.seen(g, e, i);
    let stands = |i: int| t0.standing(i);
    reveal(TreeS::visible);
    reveal(TreeS::order);
    lemma_read_all_nodes(t0, t0.children(None, true), -1);
    assert forall|k: int| 0 <= k < order.len() implies (seen(#[trigger] order[k]) <==> stands(order[k])) by {
        let i = order[k];
        assert(t0.node(i));
        let a = t0.nodes[i].author;
        assert(g.saw(e, a));
        if !stands(i) {
            let d = choose|d: int| t0.nodes[i].deleted.contains(d);
            assert(g.saw(e, d));
        }
    }
    lemma_sel_same(order, seen, stands);
    assert(prep == sel(order, stands));
    lemma_visible_no_dup(t0, g, e);
    lemma_sel_sub(order, stands);
    assert forall|q: int| 0 <= q < prep.len() implies 0 <= #[trigger] prep[q] < t0.len() && t0.standing(prep[q]) by {
        let j = src(order, stands, q);
        assert(t0.node(order[j]));
    }
    assert(fair_view(t0, prep));
    lemma_partway_start(t0, g, e, prep, ops);
    lemma_ops_chain(t0, t0, g, e, prep, ops, 0);
    let s0 = lines_of(t0, prep);
    assert(lines(t0) == s0);
    match replay_ops(t0, g, e, prep, ops, 0, 0) {
        None => {
            let m = choose|m: int| 0 <= m < ops.len() && !holds_on(s0, #[trigger] ops[m]);
        },
        Some(u) => {
            let kk = ops.len() as int;
            let view = |i: int| in_view(t0, i);
            let now = |i: int| u.standing(i);
            reveal(TreeS::order);
            lemma_read_all_nodes(u, u.children(None, true), -1);
            assert forall|k: int| 0 <= k < u.order().len() implies (now(#[trigger] u.order()[k]) <==> view(u.order()[k]) && now(u.order()[k])) by {
                let i = u.order()[k];
                assert(u.node(i));
                if i < t0.len() && now(i) {
                    assert(placed_alike(t0, u, i));
                    assert forall|d: int| !t0.nodes[i].deleted.contains(d) by {
                        if t0.nodes[i].deleted.contains(d) {
                            if marked(prep, ops, kk, i) {
                                assert(u.nodes[i].deleted.contains(d));
                            } else {
                                assert(u.nodes[i].deleted.contains(d));
                            }
                        }
                    }
                }
            }
            lemma_sel_sel(u.order(), view, now, now);
            lemma_partway_end(t0, u, g, e, prep, ops, 0, prep.len() + 1int);
            assert(s0.len() == prep.len());
        },
    }
}

/// An order every event of which had seen every event before it: a chain.
pub open spec fn chained_order(g: GraphS, order: Seq<int>) -> bool {
    &&& valid_order(g, order)
    &&& forall|i: int, j: int| 0 <= j <= i < order.len() ==> #[trigger] g.knows(order[i], order[j])
}

/// No resolution among the events, and every document's inserts in
/// ascending position, which the fast path is for.
pub open spec fn plain(g: GraphS) -> bool {
    forall|e: int| g.event(e) ==> {
        &&& (#[trigger] g.events[e]).pieces is None
        &&& (g.events[e].ops matches Some(ops) ==> inserts_ascend(ops))
    }
}

/// **The fast path**: the events of `order` applied to a list of lines, one
/// after another, with no tree at all.
pub open spec fn lin(g: GraphS, order: Seq<int>, k: int) -> Option<Seq<LineS>>
    decreases k
{
    if k <= 0 {
        Some(Seq::empty())
    } else {
        match lin(g, order, k - 1) {
            None => None,
            Some(s) => match g.events[order[k - 1]].ops {
                None => Some(s),
                Some(ops) => lin_event(s, order[k - 1], ops),
            },
        }
    }
}

/// Every element written, and every removal made, by one of the first `k`
/// events of the order.
pub open spec fn walked_by(t: TreeS, order: Seq<int>, k: int) -> bool {
    forall|i: int| t.node(i) ==> {
        &&& by_one_of(order, k, (#[trigger] t.nodes[i]).author)
        &&& forall|d: int| t.nodes[i].deleted.contains(d) ==> by_one_of(order, k, d)
    }
}

/// Whether `x` is one of the first `k` events of the order.
pub open spec fn by_one_of(order: Seq<int>, k: int, x: int) -> bool {
    exists|j: int| 0 <= j < k && order[j] == x
}

/// **Over a chain, the walk is the fast path**: the tree it builds reads as
/// the list the fast path keeps, and it refuses exactly where the fast path
/// refuses.
pub proof fn theorem_linear(g: GraphS, order: Seq<int>, k: int)
    requires g.wf(), chained_order(g, order), plain(g), 0 <= k <= order.len()
    ensures
        (walk(g, order, k) is Some) == (lin(g, order, k) is Some),
        walk(g, order, k) matches Some(t) ==> {
            &&& lines(t) == lin(g, order, k)->Some_0
            &&& shaped(t)
            &&& rooted(t)
            &&& walked_by(t, order, k)
        },
    decreases k
{
    if k == 0 {
        let t = TreeS { nodes: Seq::empty() };
        reveal(TreeS::order);
        assert(t.children(None, true) == Seq::<int>::empty());
        assert(t.order() == Seq::<int>::empty());
        assert(sel(Seq::<int>::empty(), |i: int| t.standing(i)) == Seq::<int>::empty());
        assert(lines(t) =~= Seq::<LineS>::empty());
    } else {
        theorem_linear(g, order, k - 1);
        if let Some(t) = walk(g, order, k - 1) {
            let e = order[k - 1];
            assert(g.event(e));
            assert(plain(g));
            assert(g.events[e].pieces is None);
            // Everything already in the tree is by an event `e` had seen.
            assert forall|i: int| t.node(i) implies g.knows(e, #[trigger] t.nodes[i].author) by {
                assert(by_one_of(order, k - 1, t.nodes[i].author));
                let j = choose|j: int| 0 <= j < k - 1 && order[j] == t.nodes[i].author;
            }
            assert(g.knows(e, e));
            assert(seen_all(t, g, e)) by {
                assert forall|i: int| t.node(i) implies {
                    &&& g.saw(e, #[trigger] t.nodes[i].author)
                    &&& forall|d: int| t.nodes[i].deleted.contains(d) ==> g.saw(e, d)
                } by {
                    assert(by_one_of(order, k - 1, t.nodes[i].author));
                    let j = choose|j: int| 0 <= j < k - 1 && order[j] == t.nodes[i].author;
                    assert(order[j] != order[k - 1]);
                    assert forall|d: int| t.nodes[i].deleted.contains(d) implies g.saw(e, d) by {
                        assert(by_one_of(order, k - 1, d));
                        let j2 = choose|j2: int| 0 <= j2 < k - 1 && order[j2] == d;
                        assert(order[j2] != order[k - 1]);
                    }
                }
            }
            assert(walk(g, order, k) == replay_event(t, g, e));
            let s = lin(g, order, k - 1)->Some_0;
            assert(s == lines(t));
            match g.events[e].ops {
                None => {
                    assert(replay_event(t, g, e) == Some(t));
                    assert(walk(g, order, k) == Some(t));
                    assert(lin(g, order, k) == Some(s));
                    assert forall|i: int| t.node(i) implies {
                        &&& by_one_of(order, k, (#[trigger] t.nodes[i]).author)
                        &&& forall|d: int| t.nodes[i].deleted.contains(d) ==> by_one_of(order, k, d)
                    } by {
                        assert(by_one_of(order, k - 1, t.nodes[i].author));
                        let j = choose|j: int| 0 <= j < k - 1 && order[j] == t.nodes[i].author;
                        assert(order[j] == t.nodes[i].author);
                        assert forall|d: int| t.nodes[i].deleted.contains(d) implies by_one_of(order, k, d) by {
                            assert(by_one_of(order, k - 1, d));
                            let j2 = choose|j2: int| 0 <= j2 < k - 1 && order[j2] == d;
                            assert(order[j2] == d);
                        }
                    }
                    assert(walked_by(t, order, k));
                    assert(lines(t) == lin(g, order, k)->Some_0);
                },
                Some(ops) => {
                    lemma_event_chain(t, g, e, ops);
                    let prep = t.visible(g, e);
                    assert(replay_event(t, g, e) == replay_ops(t, g, e, prep, ops, 0, 0));
                    assert(lin(g, order, k) == lin_event(s, e, ops));
                    if let Some(u) = replay_ops(t, g, e, prep, ops, 0, 0) {
                        let kk = ops.len() as int;
                        assert(shaped(u) && rooted(u));
                        assert forall|i: int| u.node(i) implies {
                            &&& by_one_of(order, k, (#[trigger] u.nodes[i]).author)
                            &&& forall|d: int| u.nodes[i].deleted.contains(d) ==> by_one_of(order, k, d)
                        } by {
                            if i < t.len() {
                                assert(placed_alike(t, u, i));
                                assert(by_one_of(order, k - 1, t.nodes[i].author));
                                let j = choose|j: int| 0 <= j < k - 1 && order[j] == t.nodes[i].author;
                                assert(order[j] == u.nodes[i].author);
                                assert forall|d: int| u.nodes[i].deleted.contains(d) implies by_one_of(order, k, d) by {
                                    if d == e {
                                        assert(order[k - 1] == d);
                                    } else {
                                        assert(t.nodes[i].deleted.contains(d));
                                        assert(by_one_of(order, k - 1, d));
                                        let j2 = choose|j2: int| 0 <= j2 < k - 1 && order[j2] == d;
                                        assert(order[j2] == d);
                                    }
                                }
                            } else {
                                assert(u.nodes[i].author == e);
                                assert(order[k - 1] == e);
                            }
                        }
                        assert(walked_by(u, order, k));
                        assert(lines(u) == lin_event(lines(t), e, ops)->Some_0);
                        assert(lines(u) == lin(g, order, k)->Some_0);
                        assert(walk(g, order, k) == Some(u));
                    }
                },
            }
        }
    }
}


} // verus!
