//! The proof that [`Ordered`](super::Ordered) holds its operations in
//! decision 0007's order. Compiled only by Verus (`verus_keep_ghost`); an
//! ordinary build never sees this module.

use vstd::prelude::*;

use super::super::{Operation, OperationKind};

verus! {

/// One past the last parent position `op` covers, as `Operation::end`
/// computes it: a `delete`'s run, saturating, and nothing for an `insert`.
pub open spec fn end(op: Operation) -> int {
    if op.kind is Delete {
        if op.at + op.items@.len() > usize::MAX { usize::MAX as int } else { op.at + op.items@.len() }
    } else {
        op.at as int
    }
}

/// Decision 0007's rule for `next` written anywhere after `previous`: a
/// position no lower; at the same position only a replacement, `delete`
/// then `insert`; and past a `delete`, nothing inside its run and no
/// `delete` meeting it.
pub(crate) open spec fn follows(previous: Operation, next: Operation) -> bool {
    &&& previous.at <= next.at
    &&& previous.at == next.at ==> (previous.kind is Delete && next.kind is Insert)
    &&& (previous.kind is Delete && previous.at < next.at) ==> {
        &&& end(previous) <= next.at
        &&& !(end(previous) == next.at && next.kind is Delete)
    }
}

/// Every operation against every one written before it.
pub(crate) open spec fn ordered(ops: Seq<Operation>) -> bool {
    forall|i: int, j: int| 0 <= i < j < ops.len() ==> follows(#[trigger] ops[i], #[trigger] ops[j])
}

/// `last` is the index of the last `delete` in `ops`, if there is one.
pub(crate) open spec fn last_delete(ops: Seq<Operation>, last: Option<usize>) -> bool {
    match last {
        Some(d) => {
            &&& d < ops.len()
            &&& ops[d as int].kind is Delete
            &&& forall|k: int| d < k < ops.len() ==> !(#[trigger] ops[k].kind is Delete)
        },
        None => forall|k: int| 0 <= k < ops.len() ==> !(#[trigger] ops[k].kind is Delete),
    }
}

/// An ordered document holds `next` against the last operation and the last
/// `delete` — the two the parser checks it against.
pub(crate) proof fn lemma_follows_both(ops: Seq<Operation>, last: Option<usize>, next: Operation)
    requires last_delete(ops, last),
    ensures
        ordered(ops.push(next)) ==> {
            &&& ops.len() > 0 ==> follows(ops.last(), next)
            &&& last matches Some(d) ==> follows(ops[d as int], next)
        },
{
    let all = ops.push(next);
    if ordered(all) {
        if ops.len() > 0 {
            assert(follows(all[ops.len() - 1], all[ops.len() as int]));
        }
        if let Some(d) = last {
            assert(follows(all[d as int], all[ops.len() as int]));
        }
    }
}

/// Checking `next` against the last operation and the last `delete` is
/// checking it against all of them.
pub(crate) proof fn lemma_push(ops: Seq<Operation>, last: Option<usize>, next: Operation, count: usize)
    requires
        count == ops.len(),
        ordered(ops),
        last_delete(ops, last),
        ops.len() > 0 ==> follows(ops.last(), next),
        last matches Some(d) ==> follows(ops[d as int], next),
    ensures
        ordered(ops.push(next)),
        last_delete(ops.push(next), if next.kind is Delete { Some(count) } else { last }),
{
    let all = ops.push(next);
    assert forall|i: int, j: int| 0 <= i < j < all.len() implies follows(#[trigger] all[i], #[trigger] all[j]) by {
        if j == ops.len() {
            let n = ops.len() - 1;
            assert(all[j] == next);
            assert(all[i] == ops[i]);
            if i < n {
                assert(follows(ops[i], ops[n]));
            }
            if ops[i].kind is Delete && ops[i].at < next.at {
                let d = last->Some_0 as int;
                if i < d {
                    assert(follows(ops[i], ops[d]));
                }
            }
        } else {
            assert(all[i] == ops[i] && all[j] == ops[j]);
        }
    }
    if !(next.kind is Delete) {
        if let Some(d) = last {
            assert(all[d as int] == ops[d as int]);
            assert forall|k: int| d < k < all.len() implies !(#[trigger] all[k].kind is Delete) by {
                if k < ops.len() { assert(all[k] == ops[k]); }
            }
        } else {
            assert forall|k: int| 0 <= k < all.len() implies !(#[trigger] all[k].kind is Delete) by {
                if k < ops.len() { assert(all[k] == ops[k]); }
            }
        }
    }
}

} // verus!
