//! What a document means, and the proof that
//! [`State::applied`](super::State::applied) does it. Compiled only by Verus
//! (`verus_keep_ghost`); an ordinary build never sees this module.
//!
//! The specification never mentions the implementation. [`deleted_at`] and
//! [`inserts_at`] read the document, [`result`] assembles the file from them
//! position by position against the parent, and [`cause`] says what would
//! make a replay refuse. `applied` is held to all three: it replays to
//! `result` exactly when there is no `cause`, and every refusal names one
//! that holds.
//!
//! Positions are stated against the parent and none of them move, so the
//! order a document's operations come in does not enter — for a document
//! the parser accepts, whose inserts name distinct positions.
//! [`theorem_order_independent`] is that claim.

use vstd::prelude::*;

use super::ReplayError;
use crate::core::RevisionId;
use crate::format::Item;
use crate::format::proof::{ItemS, OperationS, matches};
use crate::trusted::digest_of;

verus! {

/// Whether some `delete` in `ops` covers parent position `p`.
pub open spec fn deleted_at(ops: Seq<OperationS>, p: int) -> bool {
    exists|k: int| 0 <= k < ops.len() && ops[k].delete && ops[k].at <= p < ops[k].at + ops[k].items.len()
}

/// The items every `insert` at parent position `p` contributes, in document
/// order.
pub open spec fn inserts_at(ops: Seq<OperationS>, p: int) -> Seq<ItemS>
    decreases ops.len(),
{
    if ops.len() == 0 {
        Seq::empty()
    } else {
        let last = ops[ops.len() - 1];
        let before = inserts_at(ops.drop_last(), p);
        if !last.delete && last.at == p { before + last.items } else { before }
    }
}

/// The file after the document, for parent positions `0..n`: at each gap the
/// inserts there, then the parent's item unless it was deleted.
pub open spec fn result_to(parent: Seq<ItemS>, ops: Seq<OperationS>, n: int) -> Seq<ItemS>
    decreases n,
{
    if n <= 0 {
        Seq::empty()
    } else {
        let gap = result_to(parent, ops, n - 1) + inserts_at(ops, n - 1);
        if deleted_at(ops, n - 1) { gap } else { gap.push(parent[n - 1]) }
    }
}

/// The whole file: every parent position, then the gap past the last item.
pub open spec fn result(parent: Seq<ItemS>, ops: Seq<OperationS>) -> Seq<ItemS> {
    result_to(parent, ops, parent.len() as int) + inserts_at(ops, parent.len() as int)
}

/// Only a file's last line may lack a terminator.
pub open spec fn well_terminated(items: Seq<ItemS>) -> bool {
    forall|i: int| 0 <= i < items.len() - 1 ==> #[trigger] items[i].terminated
}

pub open spec fn any_forgotten(items: Seq<ItemS>) -> bool {
    exists|i: int| 0 <= i < items.len() && #[trigger] items[i].forgotten
}

/// A `delete` that names a position the parent does not have.
pub open spec fn some_delete_out_of_range(parent: Seq<ItemS>, ops: Seq<OperationS>) -> bool {
    exists|k: int| 0 <= k < ops.len() && #[trigger] ops[k].delete && ops[k].at + ops[k].items.len() > parent.len()
}

/// An `insert` that names a gap the parent does not have.
pub open spec fn some_insert_out_of_range(parent: Seq<ItemS>, ops: Seq<OperationS>) -> bool {
    exists|k: int| 0 <= k < ops.len() && !(#[trigger] ops[k].delete) && ops[k].at > parent.len()
}

/// A `delete` quoting an item that is not what the parent holds there.
pub open spec fn some_disagreement(parent: Seq<ItemS>, ops: Seq<OperationS>) -> bool {
    exists|k: int, o: int| 0 <= k < ops.len() && ops[k].delete
        && 0 <= o < ops[k].items.len()
        && ops[k].at + o < parent.len()
        && !matches(#[trigger] ops[k].items[o], parent[ops[k].at + o])
}

/// A stated digest the result does not have. A result holding a forgotten
/// item is not held to one: its bytes are not the bytes the recorder hashed.
pub open spec fn digest_disagrees(out: Seq<ItemS>, stated: Option<RevisionId>) -> bool {
    stated is Some && !any_forgotten(out) && digest_of(out) != stated->Some_0
}

/// What would make a replay refuse, read off the parent and the document
/// alone: an operation past the end, a `delete` quoting what the parent does
/// not hold, a result with an unterminated line before its last, or a stated
/// digest the result does not have.
pub open spec fn cause(parent: Seq<ItemS>, ops: Seq<OperationS>, stated: Option<RevisionId>) -> bool {
    some_delete_out_of_range(parent, ops)
        || some_insert_out_of_range(parent, ops)
        || some_disagreement(parent, ops)
        || !well_terminated(result(parent, ops))
        || digest_disagrees(result(parent, ops), stated)
}

/// Which cause a refusal names: each error is one of them, holding.
pub open spec fn names(error: ReplayError, parent: Seq<ItemS>, ops: Seq<OperationS>, stated: Option<RevisionId>) -> bool {
    match error {
        ReplayError::OutOfRange { .. } =>
            some_delete_out_of_range(parent, ops) || some_insert_out_of_range(parent, ops),
        ReplayError::ItemDisagrees { .. } | ReplayError::TerminatorDisagrees { .. } =>
            some_disagreement(parent, ops),
        ReplayError::UnterminatedItemNotLast { .. } => !well_terminated(result(parent, ops)),
        ReplayError::ResultDisagrees { stated: said, found } =>
            stated == Some(said) && found == digest_of(result(parent, ops)) && said != found
                && !any_forgotten(result(parent, ops)),
        _ => false,
    }
}

/// What the insert map holds for gap `q`: its run, or nothing.
pub open spec fn gap(runs: Map<usize, Vec<Item>>, q: int) -> Seq<ItemS> {
    if 0 <= q <= usize::MAX && runs.contains_key(q as usize) { runs[q as usize].deep_view() } else { Seq::empty() }
}

// ---------------------------------------------------------------------------
// One operation more.
// ---------------------------------------------------------------------------

/// Taking one more operation adds what it deletes and nothing else.
pub proof fn lemma_deleted_step(ops: Seq<OperationS>, k: int, q: int)
    requires 0 <= k < ops.len(),
    ensures
        deleted_at(ops.take(k + 1), q) == (deleted_at(ops.take(k), q)
            || (ops[k].delete && ops[k].at <= q < ops[k].at + ops[k].items.len())),
{
    let prefix = ops.take(k);
    let next = ops.take(k + 1);
    if deleted_at(prefix, q) {
        let j = choose|j: int| 0 <= j < prefix.len() && prefix[j].delete && prefix[j].at <= q < prefix[j].at + prefix[j].items.len();
        assert(next[j] == prefix[j]);
    }
    if deleted_at(next, q) {
        let j = choose|j: int| 0 <= j < next.len() && next[j].delete && next[j].at <= q < next[j].at + next[j].items.len();
        if j < k { assert(prefix[j] == next[j]); }
    }
    if ops[k].delete && ops[k].at <= q < ops[k].at + ops[k].items.len() {
        assert(next[k] == ops[k]);
    }
}

/// Taking one more operation adds its run to its own gap, after what was
/// there, and nothing anywhere else.
pub proof fn lemma_inserts_step(ops: Seq<OperationS>, k: int, q: int)
    requires 0 <= k < ops.len(),
    ensures
        inserts_at(ops.take(k + 1), q) == if !ops[k].delete && ops[k].at == q {
            inserts_at(ops.take(k), q) + ops[k].items
        } else {
            inserts_at(ops.take(k), q)
        },
{
    assert(ops.take(k + 1).drop_last() =~= ops.take(k));
    assert(ops.take(k + 1)[k] == ops[k]);
}

/// Both steps, for every position at once.
pub proof fn lemma_steps(ops: Seq<OperationS>, k: int)
    requires 0 <= k < ops.len(),
    ensures
        forall|q: int| #[trigger] deleted_at(ops.take(k + 1), q) == (deleted_at(ops.take(k), q)
            || (ops[k].delete && ops[k].at <= q < ops[k].at + ops[k].items.len())),
        forall|q: int| #[trigger] inserts_at(ops.take(k + 1), q) == if !ops[k].delete && ops[k].at == q {
            inserts_at(ops.take(k), q) + ops[k].items
        } else {
            inserts_at(ops.take(k), q)
        },
{
    assert forall|q: int| #[trigger] deleted_at(ops.take(k + 1), q) == (deleted_at(ops.take(k), q)
        || (ops[k].delete && ops[k].at <= q < ops[k].at + ops[k].items.len())) by {
        lemma_deleted_step(ops, k, q);
    }
    assert forall|q: int| #[trigger] inserts_at(ops.take(k + 1), q) == if !ops[k].delete && ops[k].at == q {
        inserts_at(ops.take(k), q) + ops[k].items
    } else {
        inserts_at(ops.take(k), q)
    } by {
        lemma_inserts_step(ops, k, q);
    }
}

/// The whole document is every operation taken.
pub proof fn lemma_take_all(ops: Seq<OperationS>)
    ensures ops.take(ops.len() as int) == ops,
{
    assert(ops.take(ops.len() as int) =~= ops);
}

/// A `delete` running past the parent is a cause.
pub proof fn lemma_delete_out_of_range(parent: Seq<ItemS>, ops: Seq<OperationS>, k: int)
    requires
        0 <= k < ops.len(),
        ops[k].delete,
        ops[k].at + ops[k].items.len() > parent.len(),
    ensures some_delete_out_of_range(parent, ops),
{
    assert(ops[k].delete);
}

/// An `insert` past the gap after the last item is a cause.
pub proof fn lemma_insert_out_of_range(parent: Seq<ItemS>, ops: Seq<OperationS>, k: int)
    requires
        0 <= k < ops.len(),
        !ops[k].delete,
        ops[k].at > parent.len(),
    ensures some_insert_out_of_range(parent, ops),
{
    assert(!ops[k].delete);
}

/// A quoted item the parent does not hold is a cause.
pub proof fn lemma_disagreement(parent: Seq<ItemS>, ops: Seq<OperationS>, k: int, o: int)
    requires
        0 <= k < ops.len(),
        ops[k].delete,
        0 <= o < ops[k].items.len(),
        ops[k].at + o < parent.len(),
    ensures
        !matches(ops[k].items[o], parent[ops[k].at + o]) ==> some_disagreement(parent, ops),
{
    if !matches(ops[k].items[o], parent[ops[k].at + o]) {
        assert(!matches(ops[k].items[o], parent[ops[k].at + o]));
    }
}

/// Every operation in range and every quote agreeing is none of the first
/// three causes.
pub proof fn lemma_no_early_cause(parent: Seq<ItemS>, ops: Seq<OperationS>)
    requires
        forall|j: int| 0 <= j < ops.len() && (#[trigger] ops[j]).delete ==> ops[j].at + ops[j].items.len() <= parent.len(),
        forall|j: int| 0 <= j < ops.len() && !(#[trigger] ops[j]).delete ==> ops[j].at <= parent.len(),
        forall|j: int, o: int| 0 <= j < ops.len() && ops[j].delete && 0 <= o < ops[j].items.len()
            ==> matches(#[trigger] ops[j].items[o], parent[ops[j].at + o]),
    ensures
        !some_delete_out_of_range(parent, ops),
        !some_insert_out_of_range(parent, ops),
        !some_disagreement(parent, ops),
{
}

// ---------------------------------------------------------------------------
// Theorems about the specification itself.
// ---------------------------------------------------------------------------

/// What the parser guarantees and the order-independence claim relies on: no
/// two inserts name one position (`ParseErrorKind::InsertsAtOnePosition`).
pub open spec fn distinct_inserts(ops: Seq<OperationS>) -> bool {
    forall|i: int, j: int| 0 <= i < ops.len() && 0 <= j < ops.len() && i != j
        && !ops[i].delete && !ops[j].delete ==> ops[i].at != ops[j].at
}

/// Two documents that state the same facts, in any order.
pub open spec fn same_facts(a: Seq<OperationS>, b: Seq<OperationS>) -> bool {
    forall|x: OperationS| a.contains(x) <==> b.contains(x)
}

/// Under `distinct_inserts`, what is inserted at `p` is the one insert there,
/// or nothing — the document's order does not enter.
proof fn lemma_inserts_at_unique(ops: Seq<OperationS>, p: int)
    requires distinct_inserts(ops),
    ensures
        (exists|k: int| 0 <= k < ops.len() && !ops[k].delete && ops[k].at == p)
            ==> inserts_at(ops, p) == ops[choose|k: int| 0 <= k < ops.len() && !ops[k].delete && ops[k].at == p].items,
        !(exists|k: int| 0 <= k < ops.len() && !ops[k].delete && ops[k].at == p)
            ==> inserts_at(ops, p) == Seq::<ItemS>::empty(),
    decreases ops.len(),
{
    if ops.len() > 0 {
        let rest = ops.drop_last();
        let last = ops[ops.len() - 1];
        assert(distinct_inserts(rest)) by {
            assert forall|i: int, j: int| 0 <= i < rest.len() && 0 <= j < rest.len() && i != j
                && !rest[i].delete && !rest[j].delete implies rest[i].at != rest[j].at by {
                assert(rest[i] == ops[i] && rest[j] == ops[j]);
            }
        }
        lemma_inserts_at_unique(rest, p);
        if !last.delete && last.at == p {
            assert(!(exists|k: int| 0 <= k < rest.len() && !rest[k].delete && rest[k].at == p)) by {
                if exists|k: int| 0 <= k < rest.len() && !rest[k].delete && rest[k].at == p {
                    let k = choose|k: int| 0 <= k < rest.len() && !rest[k].delete && rest[k].at == p;
                    assert(ops[k] == rest[k]);
                    assert(ops[k].at != ops[ops.len() - 1].at);
                }
            }
            assert(inserts_at(ops, p) == last.items);
            let k = choose|k: int| 0 <= k < ops.len() && !ops[k].delete && ops[k].at == p;
            assert(k == ops.len() - 1) by {
                if k < ops.len() - 1 { assert(ops[k].at != ops[ops.len() - 1].at); }
            }
        } else {
            assert(inserts_at(ops, p) == inserts_at(rest, p));
            if exists|k: int| 0 <= k < ops.len() && !ops[k].delete && ops[k].at == p {
                let k = choose|k: int| 0 <= k < ops.len() && !ops[k].delete && ops[k].at == p;
                assert(k < rest.len());
                assert(rest[k] == ops[k]);
                let k2 = choose|k: int| 0 <= k < rest.len() && !rest[k].delete && rest[k].at == p;
                assert(ops[k2] == rest[k2]);
                if k != k2 { assert(ops[k].at != ops[k2].at); }
            } else {
                if exists|k: int| 0 <= k < rest.len() && !rest[k].delete && rest[k].at == p {
                    let k = choose|k: int| 0 <= k < rest.len() && !rest[k].delete && rest[k].at == p;
                    assert(ops[k] == rest[k]);
                }
            }
        }
    }
}

proof fn lemma_same_facts_same_gaps(a: Seq<OperationS>, b: Seq<OperationS>, p: int)
    requires distinct_inserts(a), distinct_inserts(b), same_facts(a, b),
    ensures deleted_at(a, p) == deleted_at(b, p), inserts_at(a, p) == inserts_at(b, p),
{
    if deleted_at(a, p) {
        let k = choose|k: int| 0 <= k < a.len() && a[k].delete && a[k].at <= p < a[k].at + a[k].items.len();
        assert(b.contains(a[k]));
        let j = choose|j: int| 0 <= j < b.len() && b[j] == a[k];
        assert(deleted_at(b, p));
    }
    if deleted_at(b, p) {
        let k = choose|k: int| 0 <= k < b.len() && b[k].delete && b[k].at <= p < b[k].at + b[k].items.len();
        assert(a.contains(b[k]));
        let j = choose|j: int| 0 <= j < a.len() && a[j] == b[k];
        assert(deleted_at(a, p));
    }
    lemma_inserts_at_unique(a, p);
    lemma_inserts_at_unique(b, p);
    if exists|k: int| 0 <= k < a.len() && !a[k].delete && a[k].at == p {
        let ka = choose|k: int| 0 <= k < a.len() && !a[k].delete && a[k].at == p;
        assert(b.contains(a[ka]));
        let jb = choose|j: int| 0 <= j < b.len() && b[j] == a[ka];
        let kb = choose|k: int| 0 <= k < b.len() && !b[k].delete && b[k].at == p;
        if jb != kb { assert(b[jb].at != b[kb].at); }
        assert(inserts_at(a, p) == a[ka].items);
        assert(inserts_at(b, p) == b[kb].items);
    } else {
        if exists|k: int| 0 <= k < b.len() && !b[k].delete && b[k].at == p {
            let kb = choose|k: int| 0 <= k < b.len() && !b[k].delete && b[k].at == p;
            assert(a.contains(b[kb]));
            let ja = choose|j: int| 0 <= j < a.len() && a[j] == b[kb];
            assert(false);
        }
    }
}

proof fn lemma_result_to_same(parent: Seq<ItemS>, a: Seq<OperationS>, b: Seq<OperationS>, n: int)
    requires distinct_inserts(a), distinct_inserts(b), same_facts(a, b),
    ensures result_to(parent, a, n) == result_to(parent, b, n),
    decreases n,
{
    if n > 0 {
        lemma_result_to_same(parent, a, b, n - 1);
        lemma_same_facts_same_gaps(a, b, n - 1);
    }
}

/// `State::apply`'s rustdoc, as a theorem: a document the parser accepts
/// replays to the same file however its operations are ordered, because
/// every position is stated against the parent and none of them move.
pub proof fn theorem_order_independent(parent: Seq<ItemS>, a: Seq<OperationS>, b: Seq<OperationS>)
    requires distinct_inserts(a), distinct_inserts(b), same_facts(a, b),
    ensures result(parent, a) == result(parent, b),
{
    lemma_result_to_same(parent, a, b, parent.len() as int);
    lemma_same_facts_same_gaps(a, b, parent.len() as int);
}

// ---------------------------------------------------------------------------
// The specification on concrete files, so it is not vacuous.
// ---------------------------------------------------------------------------

spec fn line(c: char) -> ItemS { ItemS { text: seq![c], terminated: true, forgotten: false } }
spec fn del(at: int, items: Seq<ItemS>) -> OperationS { OperationS { delete: true, at, items } }
spec fn ins(at: int, items: Seq<ItemS>) -> OperationS { OperationS { delete: false, at, items } }

/// A replacement: `delete 1 [b]; insert 1 [x]` on `a b c` is `a x c`.
proof fn example_replacement() {
    let (a, b, c, x) = (line('a'), line('b'), line('c'), line('x'));
    let parent = seq![a, b, c];
    let ops = seq![del(1, seq![b]), ins(1, seq![x])];
    reveal_with_fuel(result_to, 4);
    reveal_with_fuel(inserts_at, 3);
    assert(ops.drop_last() =~= seq![del(1, seq![b])]);
    assert(ops.drop_last().drop_last() =~= Seq::<OperationS>::empty());
    assert(deleted_at(ops, 1)) by { assert(ops[0].delete && ops[0].at <= 1 < ops[0].at + ops[0].items.len()); }
    assert(!deleted_at(ops, 0)) by {
        if deleted_at(ops, 0) {
            let k = choose|k: int| 0 <= k < ops.len() && ops[k].delete && ops[k].at <= 0 < ops[k].at + ops[k].items.len();
            assert(k == 0 || k == 1);
        }
    }
    assert(!deleted_at(ops, 2)) by {
        if deleted_at(ops, 2) {
            let k = choose|k: int| 0 <= k < ops.len() && ops[k].delete && ops[k].at <= 2 < ops[k].at + ops[k].items.len();
            assert(k == 0 || k == 1);
        }
    }
    assert(inserts_at(ops, 0) =~= Seq::<ItemS>::empty());
    assert(inserts_at(ops, 1) =~= seq![x]);
    assert(inserts_at(ops, 2) =~= Seq::<ItemS>::empty());
    assert(inserts_at(ops, 3) =~= Seq::<ItemS>::empty());
    assert(result_to(parent, ops, 1) =~= seq![a]);
    assert(result_to(parent, ops, 2) =~= seq![a, x]);
    assert(result_to(parent, ops, 3) =~= seq![a, x, c]);
    assert(result(parent, ops) =~= seq![a, x, c]);
}

/// `insert 4` after `delete 3 1` versus `insert 3`: in a linear replay both
/// produce the same file. They differ only in which side of the removed run
/// the new items sit on, which a merge can see and a file cannot.
proof fn example_insert_beside_a_deletion() {
    let (a, b, c, d, e, x) = (line('a'), line('b'), line('c'), line('d'), line('e'), line('x'));
    let parent = seq![a, b, c, d, e];
    let past = seq![del(3, seq![d]), ins(4, seq![x])];
    let before = seq![del(3, seq![d]), ins(3, seq![x])];
    reveal_with_fuel(result_to, 6);
    reveal_with_fuel(inserts_at, 3);
    assert(past.drop_last() =~= seq![del(3, seq![d])]);
    assert(before.drop_last() =~= seq![del(3, seq![d])]);
    assert(past.drop_last().drop_last() =~= Seq::<OperationS>::empty());
    assert forall|p: int| 0 <= p < 5 implies deleted_at(past, p) == (p == 3) && deleted_at(before, p) == (p == 3) by {
        if deleted_at(past, p) {
            let k = choose|k: int| 0 <= k < past.len() && past[k].delete && past[k].at <= p < past[k].at + past[k].items.len();
            assert(k == 0 || k == 1);
        }
        if deleted_at(before, p) {
            let k = choose|k: int| 0 <= k < before.len() && before[k].delete && before[k].at <= p < before[k].at + before[k].items.len();
            assert(k == 0 || k == 1);
        }
        if p == 3 {
            assert(past[0].delete && past[0].at <= 3 < past[0].at + past[0].items.len());
            assert(before[0].delete && before[0].at <= 3 < before[0].at + before[0].items.len());
        }
    }
    assert forall|p: int| 0 <= p <= 5 implies inserts_at(past, p) =~= (if p == 4 { seq![x] } else { Seq::<ItemS>::empty() })
        && inserts_at(before, p) =~= (if p == 3 { seq![x] } else { Seq::<ItemS>::empty() }) by {}
    assert(result_to(parent, past, 1) =~= seq![a]);
    assert(result_to(parent, past, 2) =~= seq![a, b]);
    assert(result_to(parent, past, 3) =~= seq![a, b, c]);
    assert(result_to(parent, past, 4) =~= seq![a, b, c]);
    assert(result_to(parent, past, 5) =~= seq![a, b, c, x, e]);
    assert(result(parent, past) =~= seq![a, b, c, x, e]);
    assert(result_to(parent, before, 1) =~= seq![a]);
    assert(result_to(parent, before, 2) =~= seq![a, b]);
    assert(result_to(parent, before, 3) =~= seq![a, b, c]);
    assert(result_to(parent, before, 4) =~= seq![a, b, c, x]);
    assert(result_to(parent, before, 5) =~= seq![a, b, c, x, e]);
    assert(result(parent, before) =~= seq![a, b, c, x, e]);
}

} // verus!
