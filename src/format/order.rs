//! The order a document's operations are written in, held as they are read.
//!
//! Decision 0007 spells one set of facts one way: operations ascend by
//! position, a replacement is its `delete` then its `insert` at one
//! position, and nothing else shares a position, starts inside a deleted
//! run, or meets one as another `delete`. [`Ordered`] is where the parser
//! puts each operation it reads, and the only way one gets in.
//!
//! Proved, by Verus, of the code below as it runs: what an [`Ordered`] holds
//! is ordered in exactly that sense *pairwise* — every operation against
//! every one before it, not only its neighbour — and an operation is refused
//! exactly when admitting it would break that. Checking each operation
//! against two others, the one before it and the last `delete`, is what makes
//! the pairwise rule hold; a check against the one before alone let an
//! `insert` hide a deleted run from what followed it. The specification and
//! the proof are in `order/proof.rs`, which only Verus compiles
//! (`verus_keep_ghost`); an ordinary build sees none of it.
//!
//! It is written in the part of Rust Verus reads: `matches!` where a derived
//! `==` would be a trait impl the proof takes on trust, a `match` where
//! `Option::map` would be a closure, and [`Ordered::push`] taking its
//! `Ordered` by value, because a type invariant cannot be held across a
//! `&mut` borrow into a call that might unwind.

use super::error::{ParseError, ParseErrorKind};
use super::{Operation, OperationKind};

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
pub(super) mod proof;

/// The operations read so far, each admitted against every one before it.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(super) struct Ordered {
    operations: Vec<Operation>,
    /// The last `delete` among them. An `insert` at a `delete`'s own
    /// position is its replacement and follows it; it must not hide the
    /// deleted run from the operation after it.
    last_delete: Option<usize>,
}

#[cfg_attr(verus_keep_ghost, cfg_eval, verus_verify)]
impl Ordered {
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures r@ == Seq::<Operation>::empty(),
    ))]
    pub(super) fn new() -> Self {
        Ordered {
            operations: Vec::new(),
            last_delete: None,
        }
    }

    /// How many operations have been admitted.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures r == self@.len(),
    ))]
    pub(super) fn len(&self) -> usize {
        self.operations.len()
    }

    /// Admit `next`, read at line `at`, or refuse it for the first rule it
    /// breaks against the operations already admitted.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            r is Ok <==> proof::ordered(self@.push(next)),
            r is Ok ==> r->Ok_0@ == self@.push(next),
    ))]
    pub(super) fn push(self, next: Operation, at: usize) -> Result<Self, ParseError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            use_type_invariant(&self);
            proof::lemma_follows_both(self.operations@, self.last_delete, next);
        }
        follows(self.operations.last(), &next, at)?;
        let deleted = match self.last_delete {
            Some(index) => Some(&self.operations[index]),
            None => None,
        };
        follows(deleted, &next, at)?;
        let Ordered {
            mut operations,
            mut last_delete,
        } = self;
        #[cfg(verus_keep_ghost)]
        proof! { proof::lemma_push(operations@, last_delete, next, operations.len()); }
        if matches!(next.kind, OperationKind::Delete) {
            last_delete = Some(operations.len());
        }
        operations.push(next);
        Ok(Ordered {
            operations,
            last_delete,
        })
    }

    /// The operations, in the order they were admitted.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            r@ == self@,
            proof::ordered(r@),
    ))]
    pub(super) fn into_operations(self) -> Vec<Operation> {
        #[cfg(verus_keep_ghost)]
        proof! { use_type_invariant(&self); }
        self.operations
    }
}

/// Whether `next` may follow `previous`, by decision 0007's rule for two
/// operations in one document.
///
/// Positions ascend and regions never overlap, which is a total order, which is
/// a canonical order: decision 0004's "exactly one byte sequence per set of
/// facts" survives contact with content only because of this.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r is Ok <==> match previous {
            Some(previous) => proof::follows(*previous, *next),
            None => true,
        },
))]
fn follows(previous: Option<&Operation>, next: &Operation, at: usize) -> Result<(), ParseError> {
    use OperationKind::{Delete, Insert};

    let Some(previous) = previous else {
        return Ok(());
    };
    if next.at < previous.at {
        return Err(ParseError::new(
            at,
            ParseErrorKind::OperationsOutOfOrder {
                position: next.at,
                after: previous.at,
            },
        ));
    }
    if next.at == previous.at {
        let kind = match (previous.kind, next.kind) {
            // The canonical replacement, and the only tie there is.
            (Delete, Insert) => return Ok(()),
            (Delete, Delete) => ParseErrorKind::OverlappingOperations { position: next.at },
            (Insert, Delete) => ParseErrorKind::DeleteAfterInsert { position: next.at },
            (Insert, Insert) => ParseErrorKind::InsertsAtOnePosition { position: next.at },
        };
        return Err(ParseError::new(at, kind));
    }
    if matches!(previous.kind, Delete) {
        if next.at < previous.end() {
            return Err(ParseError::new(
                at,
                ParseErrorKind::OverlappingOperations { position: next.at },
            ));
        }
        // Two deletes that meet remove one run, which is one fact.
        if next.at == previous.end() && matches!(next.kind, Delete) {
            return Err(ParseError::new(
                at,
                ParseErrorKind::AdjacentDeletes {
                    at: previous.at,
                    // Saturating where two runs could not both fit in
                    // memory anyway, so the proof need not assume it.
                    total: previous.items.len().saturating_add(next.items.len()),
                },
            ));
        }
    }
    Ok(())
}

#[cfg(verus_keep_ghost)]
verus! {

impl View for Ordered {
    type V = Seq<Operation>;

    closed spec fn view(&self) -> Seq<Operation> {
        self.operations@
    }
}

impl Ordered {
    /// What every `Ordered` is: its operations ordered pairwise, and
    /// `last_delete` the last `delete` among them.
    #[verifier::type_invariant]
    spec fn holds(self) -> bool {
        &&& proof::ordered(self.operations@)
        &&& proof::last_delete(self.operations@, self.last_delete)
    }
}

} // verus!
