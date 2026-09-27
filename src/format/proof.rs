//! The format's items and operations, as the proofs read them. Compiled only
//! by Verus (`verus_keep_ghost`); an ordinary build never sees this module.
//!
//! An [`Item`]'s text is a `String`, and a proof about what a replay keeps
//! and moves wants it as a sequence of characters, which is what `vstd` says
//! a `String` is. [`ItemS`] is an item with its text so read, and
//! [`OperationS`] an operation with its items so read and its kind a flag,
//! and [`DocumentS`] a document of them. [`PieceS`] and [`ResolutionS`] are
//! the second grammar's, read the same way.

use vstd::prelude::*;

use super::{Item, Operation, OperationDocument, Piece, ResolutionDocument};
use crate::core::RevisionId;

verus! {

/// One line of a file, its text a sequence.
pub struct ItemS {
    pub text: Seq<char>,
    pub terminated: bool,
    pub forgotten: bool,
}

impl View for Item {
    type V = ItemS;

    open spec fn view(&self) -> ItemS {
        ItemS { text: self.text@, terminated: self.terminated, forgotten: self.forgotten }
    }
}

impl DeepView for Item {
    type V = ItemS;

    open spec fn deep_view(&self) -> ItemS {
        self@
    }
}

/// One operation, its items read as [`ItemS`].
pub struct OperationS {
    pub delete: bool,
    pub at: int,
    pub items: Seq<ItemS>,
}

impl DeepView for Operation {
    type V = OperationS;

    open spec fn deep_view(&self) -> OperationS {
        OperationS { delete: self.kind is Delete, at: self.at as int, items: self.items.deep_view() }
    }
}

/// One operation document, its operations read as [`OperationS`].
pub struct DocumentS {
    pub forgets: Option<RevisionId>,
    pub result: Option<RevisionId>,
    pub operations: Seq<OperationS>,
}

impl DeepView for OperationDocument {
    type V = DocumentS;

    open spec fn deep_view(&self) -> DocumentS {
        DocumentS { forgets: self.forgets, result: self.result, operations: self.operations.deep_view() }
    }
}

/// One piece of a resolution, its minted items read as [`ItemS`].
pub enum PieceS {
    Keep { document: RevisionId, first: int, count: int },
    Insert { items: Seq<ItemS> },
}

impl DeepView for Piece {
    type V = PieceS;

    open spec fn deep_view(&self) -> PieceS {
        match self {
            Piece::Keep { document, first, count } => PieceS::Keep {
                document: *document,
                first: *first as int,
                count: *count as int,
            },
            Piece::Insert { items } => PieceS::Insert { items: items.deep_view() },
        }
    }
}

/// One resolution, its pieces read as [`PieceS`].
pub struct ResolutionS {
    pub forgets: Option<RevisionId>,
    pub result: Option<RevisionId>,
    pub pieces: Seq<PieceS>,
}

impl DeepView for ResolutionDocument {
    type V = ResolutionS;

    open spec fn deep_view(&self) -> ResolutionS {
        ResolutionS { forgets: self.forgets, result: self.result, pieces: self.pieces.deep_view() }
    }
}

/// Decision 0014's agreement: equal up to forgetting, with the terminator
/// held either way, because that is shape.
pub open spec fn matches(recorded: ItemS, found: ItemS) -> bool {
    recorded.terminated == found.terminated
        && (recorded.forgotten || found.forgotten || recorded.text == found.text)
}

} // verus!
