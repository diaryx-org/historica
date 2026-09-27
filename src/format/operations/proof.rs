//! What a reader consumes for a document a redaction reached: decision 0014's
//! union rule as [`super::stand_in`] is proved to compute it, and the laws the
//! decision claims of the rule. Compiled only by Verus (`verus_keep_ghost`).
//!
//! [`stood`] is the rule: the shape — the original, or with it destroyed the
//! first document standing in for it — with each item forgotten exactly where
//! the shape or some forgetting document of its shape forgets it. The laws are
//! the Bend spike's (`standins_fold_in_any_order`,
//! `standins_beside_only_forget`, `standins_beside_forget_all_they_say`),
//! restated over it: what is read depends on which documents are held and not
//! on their order or their count, more of them only forget more, and what they
//! do to the shape is forget and nothing else.

use vstd::prelude::*;

use super::super::proof::{DocumentS, ItemS, OperationS};

verus! {

/// An item with its text destroyed and its terminator kept, which is shape.
pub open spec fn forgetting(item: ItemS) -> ItemS {
    ItemS { text: Seq::empty(), terminated: item.terminated, forgotten: true }
}

/// Two operations of one shape: kind, position, count, and terminators.
pub open spec fn same_operation(a: OperationS, b: OperationS) -> bool {
    &&& a.delete == b.delete
    &&& a.at == b.at
    &&& a.items.len() == b.items.len()
    &&& forall|j: int| 0 <= j < a.items.len() ==> (#[trigger] a.items[j]).terminated == b.items[j].terminated
}

/// Two runs of operations of one shape.
pub open spec fn same_shape(a: Seq<OperationS>, b: Seq<OperationS>) -> bool {
    a.len() == b.len() && forall|i: int| 0 <= i < a.len() ==> #[trigger] same_operation(a[i], b[i])
}

/// Whether a document among `stated`, of `held`'s shape, forgets item `j` of
/// operation `i`.
pub open spec fn forgotten_by(held: Seq<OperationS>, stated: Seq<DocumentS>, i: int, j: int) -> bool {
    exists|d: DocumentS|
        #[trigger] stated.contains(d) && same_shape(held, d.operations) && d.operations[i].items[j].forgotten
}

/// One item as it is read: forgotten if anything says so.
pub open spec fn stood_item(item: ItemS, forgotten: bool) -> ItemS {
    if forgotten && !item.forgotten { forgetting(item) } else { item }
}

pub open spec fn stood_operation(held: Seq<OperationS>, stated: Seq<DocumentS>, i: int) -> OperationS {
    OperationS {
        delete: held[i].delete,
        at: held[i].at,
        items: Seq::new(
            held[i].items.len(),
            |j: int| stood_item(held[i].items[j], forgotten_by(held, stated, i, j)),
        ),
    }
}

/// Decision 0014's reading of `held` through the documents standing in for it.
pub open spec fn stood(held: DocumentS, stated: Seq<DocumentS>) -> DocumentS {
    DocumentS {
        forgets: held.forgets,
        result: held.result,
        operations: Seq::new(held.operations.len(), |i: int| stood_operation(held.operations, stated, i)),
    }
}

/// The document the rest are read into: the original where it is held, or
/// else the first that stands in for it.
pub open spec fn shape_of(base: Option<DocumentS>, stated: Seq<DocumentS>) -> DocumentS {
    match base {
        Some(held) => held,
        None => stated[0],
    }
}

proof fn lemma_contains_alike(a: Seq<DocumentS>, b: Seq<DocumentS>)
    requires
        a.to_set().subset_of(b.to_set()),
    ensures
        forall|d: DocumentS| #[trigger] a.contains(d) ==> b.contains(d),
{
    assert forall|d: DocumentS| #[trigger] a.contains(d) implies b.contains(d) by {
        assert(a.to_set().contains(d));
    }
}

proof fn lemma_forgotten_by_more(held: Seq<OperationS>, a: Seq<DocumentS>, b: Seq<DocumentS>)
    requires
        a.to_set().subset_of(b.to_set()),
    ensures
        forall|i: int, j: int| #[trigger] forgotten_by(held, a, i, j) ==> forgotten_by(held, b, i, j),
{
    lemma_contains_alike(a, b);
    assert forall|i: int, j: int| #[trigger] forgotten_by(held, a, i, j) implies forgotten_by(held, b, i, j) by {
        let d = choose|d: DocumentS|
            #[trigger] a.contains(d) && same_shape(held, d.operations) && d.operations[i].items[j].forgotten;
        assert(b.contains(d));
    }
}

/// **The order stand-ins arrive in does not matter, nor does one arriving
/// twice**: what is read depends only on which documents are held.
///
/// With the original destroyed, the shape is the first of them, so this is
/// the rest in any order; a store hands them over in digest order, so that
/// the first is the same one everywhere.
pub proof fn theorem_any_order(held: DocumentS, a: Seq<DocumentS>, b: Seq<DocumentS>)
    requires
        a.to_set() == b.to_set(),
    ensures
        stood(held, a) == stood(held, b),
{
    lemma_forgotten_by_more(held.operations, a, b);
    lemma_forgotten_by_more(held.operations, b, a);
    let (one, other) = (stood(held, a), stood(held, b));
    assert forall|i: int| 0 <= i < held.operations.len() implies one.operations[i] == other.operations[i] by {
        assert(one.operations[i].items =~= other.operations[i].items);
    }
    assert(one.operations =~= other.operations);
}

/// **More stand-ins only forget more.** A stale replica syncing an older,
/// less thorough redaction back cannot un-forget anything, which is what
/// decision 0014 means by *it fails safe*.
pub proof fn theorem_more_forgets_more(held: DocumentS, a: Seq<DocumentS>, b: Seq<DocumentS>)
    requires
        a.to_set().subset_of(b.to_set()),
    ensures
        forall|i: int, j: int|
            0 <= i < held.operations.len() && 0 <= j < held.operations[i].items.len()
                && (#[trigger] stood(held, a).operations[i].items[j]).forgotten
                ==> stood(held, b).operations[i].items[j].forgotten,
{
    lemma_forgotten_by_more(held.operations, a, b);
}

/// **What stands in for a document only forgets it.** What is read has the
/// document's shape, and each item is the document's own or that item
/// forgotten — a stand-in destroys text, and writes none.
pub proof fn theorem_only_forgets(held: DocumentS, stated: Seq<DocumentS>)
    ensures
        same_shape(held.operations, stood(held, stated).operations),
        forall|i: int, j: int|
            0 <= i < held.operations.len() && 0 <= j < held.operations[i].items.len() ==> {
                let read = #[trigger] stood(held, stated).operations[i].items[j];
                read == held.operations[i].items[j] || read == forgetting(held.operations[i].items[j])
            },
{
    let read = stood(held, stated);
    assert forall|i: int| 0 <= i < held.operations.len() implies #[trigger] same_operation(
        held.operations[i],
        read.operations[i],
    ) by {
        assert forall|j: int| 0 <= j < held.operations[i].items.len() implies (
        #[trigger] held.operations[i].items[j]).terminated == read.operations[i].items[j].terminated by {}
    }
}

/// **Every item a stand-in of the document's shape forgets is forgotten in
/// what is read**, whatever else is held beside it.
pub proof fn theorem_forgets_all_it_says(held: DocumentS, stated: Seq<DocumentS>, d: DocumentS)
    requires
        stated.contains(d),
        same_shape(held.operations, d.operations),
    ensures
        forall|i: int, j: int|
            0 <= i < held.operations.len() && 0 <= j < held.operations[i].items.len()
                && (#[trigger] d.operations[i].items[j]).forgotten
                ==> stood(held, stated).operations[i].items[j].forgotten,
{
    assert forall|i: int, j: int|
        0 <= i < held.operations.len() && 0 <= j < held.operations[i].items.len()
            && (#[trigger] d.operations[i].items[j]).forgotten
        implies stood(held, stated).operations[i].items[j].forgotten by {
        assert(forgotten_by(held.operations, stated, i, j));
    }
}

/// **Reading through the same stand-ins twice is reading once**: forgetting
/// what is already forgotten is a no-op.
pub proof fn theorem_again(held: DocumentS, stated: Seq<DocumentS>)
    ensures
        stood(stood(held, stated), stated) == stood(held, stated),
{
    let once = stood(held, stated);
    theorem_only_forgets(held, stated);
    // Forgetting changes no shape, so the same documents are of the shape the
    // second time as the first.
    assert forall|e: Seq<OperationS>| same_shape(once.operations, e) == same_shape(held.operations, e) by {
        if same_shape(held.operations, e) {
            assert forall|i: int| 0 <= i < once.operations.len() implies #[trigger] same_operation(
                once.operations[i],
                e[i],
            ) by {
                assert(same_operation(held.operations[i], e[i]));
                assert(same_operation(held.operations[i], once.operations[i]));
            }
        }
        if same_shape(once.operations, e) {
            assert forall|i: int| 0 <= i < held.operations.len() implies #[trigger] same_operation(
                held.operations[i],
                e[i],
            ) by {
                assert(same_operation(once.operations[i], e[i]));
                assert(same_operation(held.operations[i], once.operations[i]));
            }
        }
    }
    assert forall|i: int, j: int| #[trigger] forgotten_by(once.operations, stated, i, j) == forgotten_by(
        held.operations,
        stated,
        i,
        j,
    ) by {
        if forgotten_by(once.operations, stated, i, j) {
            let d = choose|d: DocumentS|
                #[trigger] stated.contains(d) && same_shape(once.operations, d.operations)
                    && d.operations[i].items[j].forgotten;
            assert(same_shape(held.operations, d.operations));
        }
        if forgotten_by(held.operations, stated, i, j) {
            let d = choose|d: DocumentS|
                #[trigger] stated.contains(d) && same_shape(held.operations, d.operations)
                    && d.operations[i].items[j].forgotten;
            assert(same_shape(once.operations, d.operations));
        }
    }
    let twice = stood(once, stated);
    assert forall|i: int| 0 <= i < held.operations.len() implies twice.operations[i] == once.operations[i] by {
        assert(twice.operations[i].items =~= once.operations[i].items);
    }
    assert(twice.operations =~= once.operations);
}

} // verus!
