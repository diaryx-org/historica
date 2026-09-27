//! What an ancestry answers, as the proofs read it: whether one event is
//! reachable from another by parent edges. Compiled only by Verus
//! (`verus_keep_ghost`); an ordinary build never sees this module.
//!
//! [`reaches`] is the relation, defined by walks down parent edges so that it
//! needs no order to be stated. Over an order that lists every event once
//! and each after its parents — [`causal`] — it is a partial order:
//! reflexive, transitive, and never both ways between two events, because
//! every step of a walk goes back in the order.

use vstd::prelude::*;
use vstd::set_lib::{lemma_int_range, lemma_subset_equality, set_int_range};

verus! {

/// The parents of each event, as the proof reads them.
pub open spec fn parents_of(parents: Seq<Vec<usize>>) -> Seq<Seq<usize>> {
    parents.map_values(|of: Vec<usize>| of@)
}

/// A walk down parent edges: every step from an event to one of its parents.
pub open spec fn is_path(parents: Seq<Seq<usize>>, path: Seq<int>) -> bool {
    &&& path.len() >= 1
    &&& forall|i: int| 0 <= i < path.len() ==> 0 <= #[trigger] path[i] < parents.len()
    &&& forall|i: int| 0 <= i < path.len() - 1 ==> #[trigger] parents[path[i]].contains(path[i + 1] as usize)
}

/// Whether `o` is in `e`'s causal past, `e` itself included: some walk down
/// parent edges leads from `e` to `o`.
pub open spec fn reaches(parents: Seq<Seq<usize>>, e: int, o: int) -> bool {
    exists|path: Seq<int>| #[trigger] is_path(parents, path) && path[0] == e && path.last() == o
}

/// `order` lists every event once, each after all of its parents.
pub open spec fn causal(parents: Seq<Seq<usize>>, order: Seq<usize>) -> bool {
    &&& order.len() == parents.len()
    &&& forall|i: int| 0 <= i < order.len() ==> (#[trigger] order[i] as int) < parents.len()
    &&& forall|i: int, j: int| 0 <= i < j < order.len() ==> order[i] != order[j]
    &&& parents_first(parents, order)
}

/// Every event of `order` comes after all of its parents in it.
pub open spec fn parents_first(parents: Seq<Seq<usize>>, order: Seq<usize>) -> bool {
    forall|i: int, k: int| 0 <= i < order.len() && 0 <= k < parents[order[i] as int].len()
        ==> #[trigger] placed_before(order, parents[order[i] as int][k], i)
}

/// Whether `p` sits in `order` before place `i`.
pub open spec fn placed_before(order: Seq<usize>, p: usize, i: int) -> bool {
    exists|j: int| 0 <= j < i && order[j] == p
}

/// Placing an event all of whose parents are placed keeps every event after
/// its parents.
pub proof fn lemma_parents_first_push(parents: Seq<Seq<usize>>, order: Seq<usize>, x: usize)
    requires
        parents_first(parents, order),
        forall|k: int| 0 <= k < parents[x as int].len() ==> order.contains(#[trigger] parents[x as int][k]),
    ensures parents_first(parents, order.push(x))
{
    let pushed = order.push(x);
    assert forall|i: int, k: int| 0 <= i < pushed.len() && 0 <= k < parents[pushed[i] as int].len()
        implies #[trigger] placed_before(pushed, parents[pushed[i] as int][k], i) by {
        if i < order.len() {
            assert(pushed[i] == order[i]);
            assert(placed_before(order, parents[order[i] as int][k], i));
            let j = choose|j: int| 0 <= j < i && order[j] == parents[order[i] as int][k];
            assert(pushed[j] == order[j]);
        } else {
            let p = parents[x as int][k];
            assert(order.contains(p));
            let j = choose|j: int| 0 <= j < order.len() && order[j] == p;
            assert(pushed[j] == order[j]);
        }
    }
}

/// Where `e` sits in `order`.
pub open spec fn place(order: Seq<usize>, e: int) -> int {
    choose|j: int| 0 <= j < order.len() && order[j] as int == e
}

/// A causal order holds every event, at one place.
pub proof fn lemma_place(parents: Seq<Seq<usize>>, order: Seq<usize>, e: int)
    requires causal(parents, order), 0 <= e < parents.len()
    ensures
        0 <= place(order, e) < order.len(),
        order[place(order, e)] as int == e,
        forall|j: int| 0 <= j < order.len() && order[j] as int == e ==> j == place(order, e),
{
    let ints = order.map_values(|x: usize| x as int);
    assert(ints.no_duplicates()) by {
        assert forall|i: int, j: int| 0 <= i < ints.len() && 0 <= j < ints.len() && i != j implies ints[i] != ints[j] by {
            if i < j { assert(order[i] != order[j]); } else { assert(order[j] != order[i]); }
        }
    }
    ints.unique_seq_to_set();
    lemma_int_range(0, parents.len() as int);
    let range = set_int_range(0, parents.len() as int);
    assert(ints.to_set().subset_of(range)) by {
        assert forall|x: int| ints.to_set().contains(x) implies range.contains(x) by {
            assert(ints.contains(x));
            let i = choose|i: int| 0 <= i < ints.len() && ints[i] == x;
            assert(order[i] as int == x);
        }
    }
    lemma_subset_equality(ints.to_set(), range);
    assert(range.contains(e));
    assert(ints.to_set().contains(e));
    assert(ints.contains(e));
    let i = choose|i: int| 0 <= i < ints.len() && ints[i] == e;
    assert(order[i] as int == e);
    let p = place(order, e);
    assert forall|j: int| 0 <= j < order.len() && order[j] as int == e implies j == p by {
        if j != p {
            if j < p { assert(order[j] != order[p]); } else { assert(order[p] != order[j]); }
        }
    }
}

/// A list of distinct events, all below `n`, that leaves one out is shorter
/// than `n`.
pub proof fn lemma_short(s: Seq<usize>, n: int, missing: int)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j],
        forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i] as int) < n,
        0 <= missing < n,
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] as int != missing,
    ensures s.len() < n
{
    let ints = s.map_values(|x: usize| x as int);
    assert(ints.no_duplicates()) by {
        assert forall|i: int, j: int| 0 <= i < ints.len() && 0 <= j < ints.len() && i != j implies ints[i] != ints[j] by {
            if i < j { assert(s[i] != s[j]); } else { assert(s[j] != s[i]); }
        }
    }
    ints.unique_seq_to_set();
    lemma_int_range(0, n);
    let range = set_int_range(0, n).remove(missing);
    assert(ints.to_set().subset_of(range)) by {
        assert forall|x: int| ints.to_set().contains(x) implies range.contains(x) by {
            assert(ints.contains(x));
            let i = choose|i: int| 0 <= i < ints.len() && ints[i] == x;
            assert(s[i] as int == x);
        }
    }
    vstd::set_lib::lemma_len_subset(ints.to_set(), range);
}

/// Every event reaches itself.
pub proof fn lemma_reaches_self(parents: Seq<Seq<usize>>, e: int)
    requires 0 <= e < parents.len()
    ensures reaches(parents, e, e)
{
    assert(is_path(parents, seq![e]));
}

/// Stepping to a parent and on from there is a walk from the event.
pub proof fn lemma_reaches_step(parents: Seq<Seq<usize>>, e: int, p: int, o: int)
    requires 0 <= e < parents.len(), parents[e].contains(p as usize), 0 <= p, reaches(parents, p, o)
    ensures reaches(parents, e, o)
{
    let path = choose|path: Seq<int>| #[trigger] is_path(parents, path) && path[0] == p && path.last() == o;
    let longer = seq![e] + path;
    assert(longer[1] == p);
    assert forall|i: int| 0 <= i < longer.len() - 1 implies #[trigger] parents[longer[i]].contains(longer[i + 1] as usize) by {
        if i > 0 {
            assert(longer[i] == path[i - 1]);
            assert(longer[i + 1] == path[i]);
            assert(parents[path[i - 1]].contains(path[(i - 1) + 1] as usize));
        } else {
            assert(longer[i] == e);
            assert(longer[i + 1] == p);
        }
    }
    assert(is_path(parents, longer));
}

/// A walk from an event is the event itself, or a step to a parent and a
/// walk on from there.
pub proof fn lemma_reaches_split(parents: Seq<Seq<usize>>, e: int, o: int)
    requires reaches(parents, e, o), e != o
    ensures exists|p: int| 0 <= p < parents.len() && #[trigger] parents[e].contains(p as usize) && reaches(parents, p, o)
{
    let path = choose|path: Seq<int>| #[trigger] is_path(parents, path) && path[0] == e && path.last() == o;
    let rest = path.drop_first();
    assert(path.len() >= 2);
    let zero = 0int;
    assert(parents[path[zero]].contains(path[zero + 1] as usize));
    assert(path[zero + 1] == path[1]);
    assert forall|i: int| 0 <= i < rest.len() - 1 implies #[trigger] parents[rest[i]].contains(rest[i + 1] as usize) by {
        assert(rest[i] == path[i + 1]);
        assert(rest[i + 1] == path[i + 2]);
        assert(parents[path[i + 1]].contains(path[(i + 1) + 1] as usize));
    }
    assert(is_path(parents, rest));
    assert(rest[0] == path[1]);
}

/// Walks compose.
pub proof fn lemma_reaches_trans(parents: Seq<Seq<usize>>, a: int, b: int, c: int)
    requires reaches(parents, a, b), reaches(parents, b, c)
    ensures reaches(parents, a, c)
{
    let p1 = choose|path: Seq<int>| #[trigger] is_path(parents, path) && path[0] == a && path.last() == b;
    let p2 = choose|path: Seq<int>| #[trigger] is_path(parents, path) && path[0] == b && path.last() == c;
    let joined = p1 + p2.drop_first();
    assert forall|i: int| 0 <= i < joined.len() implies 0 <= #[trigger] joined[i] < parents.len() by {
        if i >= p1.len() { assert(joined[i] == p2[i - p1.len() + 1]); }
    }
    assert forall|i: int| 0 <= i < joined.len() - 1 implies #[trigger] parents[joined[i]].contains(joined[i + 1] as usize) by {
        if i < p1.len() - 1 {
            assert(joined[i + 1] == p1[i + 1]);
        } else if i == p1.len() - 1 {
            assert(joined[i] == b);
            assert(joined[i + 1] == p2[1]);
            assert(p2[0] == b);
        } else {
            assert(joined[i] == p2[i - p1.len() + 1]);
            assert(joined[i + 1] == p2[i - p1.len() + 2]);
        }
    }
    assert(is_path(parents, joined));
    if p2.len() == 1 {
        assert(joined =~= p1);
    } else {
        assert(joined.last() == p2.last());
    }
}

/// Over a causal order, a walk only goes back: what an event reaches sits no
/// later, and at its own place only when it is the event itself.
pub proof fn lemma_reaches_back(parents: Seq<Seq<usize>>, order: Seq<usize>, e: int, o: int)
    requires causal(parents, order), reaches(parents, e, o)
    ensures
        place(order, o) <= place(order, e),
        place(order, o) == place(order, e) ==> o == e,
    decreases place(order, e)
{
    let path = choose|path: Seq<int>| #[trigger] is_path(parents, path) && path[0] == e && path.last() == o;
    assert(0 <= e < parents.len());
    assert(0 <= o < parents.len()) by { assert(path[path.len() - 1] == o); }
    lemma_place(parents, order, e);
    lemma_place(parents, order, o);
    if e != o {
        lemma_reaches_split(parents, e, o);
        let p = choose|p: int| 0 <= p < parents.len() && #[trigger] parents[e].contains(p as usize) && reaches(parents, p, o);
        let i = place(order, e);
        let k = choose|k: int| 0 <= k < parents[e].len() && parents[e][k] == p as usize;
        assert(parents[order[i] as int][k] == p as usize);
        assert(placed_before(order, parents[order[i] as int][k], i));
        let j = choose|j: int| 0 <= j < i && order[j] == parents[order[i] as int][k];
        lemma_place(parents, order, p);
        assert(place(order, p) == j);
        lemma_reaches_back(parents, order, p, o);
    }
}

/// Over a causal order, two events never reach each other unless they are
/// one.
pub proof fn lemma_reaches_antisymmetric(parents: Seq<Seq<usize>>, order: Seq<usize>, a: int, b: int)
    requires causal(parents, order), reaches(parents, a, b), reaches(parents, b, a)
    ensures a == b
{
    lemma_reaches_back(parents, order, a, b);
    lemma_reaches_back(parents, order, b, a);
}

/// A chain: the first event has no parents, and every other has exactly the
/// one before it.
pub open spec fn chained(parents: Seq<Seq<usize>>, order: Seq<usize>) -> bool {
    &&& order.len() > 0 ==> parents[order[0] as int].len() == 0
    &&& forall|i: int| 0 < i < order.len() ==> #[trigger] parents[order[i] as int] == seq![order[i - 1]]
}

/// In a chain, an event reaches exactly the events at or before its place.
pub proof fn lemma_chain_reaches(parents: Seq<Seq<usize>>, order: Seq<usize>, i: int, j: int)
    requires causal(parents, order), chained(parents, order), 0 <= i < order.len(), 0 <= j < order.len()
    ensures reaches(parents, order[i] as int, order[j] as int) <==> j <= i
    decreases i
{
    lemma_place(parents, order, order[i] as int);
    lemma_place(parents, order, order[j] as int);
    if reaches(parents, order[i] as int, order[j] as int) {
        lemma_reaches_back(parents, order, order[i] as int, order[j] as int);
    }
    if j <= i {
        if j == i {
            lemma_reaches_self(parents, order[i] as int);
        } else {
            lemma_chain_reaches(parents, order, i - 1, j);
            assert(parents[order[i] as int] == seq![order[i - 1]]);
            assert(parents[order[i] as int][0] == order[i - 1]);
            lemma_reaches_step(parents, order[i] as int, order[i - 1] as int, order[j] as int);
        }
    }
}

} // verus!
