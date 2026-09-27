//! Decision 0014's union rule in the second grammar, as
//! [`super::stand_in`] is proved to compute it, and the laws decision 0050
//! claims of it by claiming they are the first grammar's word for word.
//! Compiled only by Verus (`verus_keep_ghost`).
//!
//! A resolution's text of its own is what its `insert` pieces mint; a `keep`
//! is a reference and holds none. So [`stood`] is the shape — the original,
//! or with it destroyed the first resolution standing in for it — with every
//! `keep` as it is and each minted item forgotten exactly where the shape or
//! some forgetting resolution of its shape forgets it. The item rule is the
//! operation document's, [`stood_item`], and so are the laws below.

use vstd::prelude::*;

use super::super::operations::proof::{forgetting, stood_item};
use super::super::proof::{ItemS, PieceS, ResolutionS};

verus! {

/// What a piece mints: an `insert`'s items, and nothing for a `keep`.
pub open spec fn items_of(piece: PieceS) -> Seq<ItemS> {
    match piece {
        PieceS::Keep { .. } => Seq::empty(),
        PieceS::Insert { items } => items,
    }
}

/// Two pieces of one shape: the same `keep` exactly, or two `insert`s minting
/// as many items, terminated alike.
pub open spec fn same_piece(a: PieceS, b: PieceS) -> bool {
    match a {
        PieceS::Keep { .. } => a == b,
        PieceS::Insert { items } => {
            &&& b is Insert
            &&& items.len() == items_of(b).len()
            &&& forall|j: int| 0 <= j < items.len() ==> (#[trigger] items[j]).terminated == items_of(b)[j].terminated
        },
    }
}

/// Two resolutions' pieces of one shape.
pub open spec fn same_shape(a: Seq<PieceS>, b: Seq<PieceS>) -> bool {
    a.len() == b.len() && forall|i: int| 0 <= i < a.len() ==> #[trigger] same_piece(a[i], b[i])
}

/// Whether a resolution among `stated`, of `held`'s shape, forgets item `j`
/// of piece `i`.
pub open spec fn forgotten_by(held: Seq<PieceS>, stated: Seq<ResolutionS>, i: int, j: int) -> bool {
    exists|d: ResolutionS|
        #[trigger] stated.contains(d) && same_shape(held, d.pieces) && items_of(d.pieces[i])[j].forgotten
}

pub open spec fn stood_piece(held: Seq<PieceS>, stated: Seq<ResolutionS>, i: int) -> PieceS {
    match held[i] {
        PieceS::Keep { .. } => held[i],
        PieceS::Insert { items } => PieceS::Insert {
            items: Seq::new(items.len(), |j: int| stood_item(items[j], forgotten_by(held, stated, i, j))),
        },
    }
}

/// Decision 0014's reading of `held` through the resolutions standing in for it.
pub open spec fn stood(held: ResolutionS, stated: Seq<ResolutionS>) -> ResolutionS {
    ResolutionS {
        forgets: held.forgets,
        result: held.result,
        pieces: Seq::new(held.pieces.len(), |i: int| stood_piece(held.pieces, stated, i)),
    }
}

/// The resolution the rest are read into: the original where it is held, or
/// else the first that stands in for it.
pub open spec fn shape_of(base: Option<ResolutionS>, stated: Seq<ResolutionS>) -> ResolutionS {
    match base {
        Some(held) => held,
        None => stated[0],
    }
}

/// Whether item `j` of piece `i` is one the pieces mint.
pub open spec fn minted(pieces: Seq<PieceS>, i: int, j: int) -> bool {
    0 <= i < pieces.len() && pieces[i] is Insert && 0 <= j < items_of(pieces[i]).len()
}

/// Two pieces of one shape are of the same shape as any third.
proof fn lemma_same_piece_alike(a: PieceS, b: PieceS, c: PieceS)
    requires
        same_piece(a, b),
    ensures
        same_piece(b, c) == same_piece(a, c),
{
    if a is Insert {
        let (x, y, z) = (items_of(a), items_of(b), items_of(c));
        if same_piece(a, c) {
            assert forall|j: int| 0 <= j < y.len() implies (#[trigger] y[j]).terminated == z[j].terminated by {
                assert(x[j].terminated == y[j].terminated);
                assert(x[j].terminated == z[j].terminated);
            }
        }
        if same_piece(b, c) {
            assert forall|j: int| 0 <= j < x.len() implies (#[trigger] x[j]).terminated == z[j].terminated by {
                assert(x[j].terminated == y[j].terminated);
                assert(y[j].terminated == z[j].terminated);
            }
        }
    }
}

proof fn lemma_forgotten_by_more(held: Seq<PieceS>, a: Seq<ResolutionS>, b: Seq<ResolutionS>)
    requires
        a.to_set().subset_of(b.to_set()),
    ensures
        forall|i: int, j: int| #[trigger] forgotten_by(held, a, i, j) ==> forgotten_by(held, b, i, j),
{
    assert forall|i: int, j: int| #[trigger] forgotten_by(held, a, i, j) implies forgotten_by(held, b, i, j) by {
        let d = choose|d: ResolutionS|
            #[trigger] a.contains(d) && same_shape(held, d.pieces) && items_of(d.pieces[i])[j].forgotten;
        assert(a.to_set().contains(d));
        assert(b.contains(d));
    }
}

/// **The order resolutions standing in arrive in does not matter, nor does
/// one arriving twice**: what is read depends only on which are held.
pub proof fn theorem_any_order(held: ResolutionS, a: Seq<ResolutionS>, b: Seq<ResolutionS>)
    requires
        a.to_set() == b.to_set(),
    ensures
        stood(held, a) == stood(held, b),
{
    lemma_forgotten_by_more(held.pieces, a, b);
    lemma_forgotten_by_more(held.pieces, b, a);
    let (one, other) = (stood(held, a), stood(held, b));
    assert forall|i: int| 0 <= i < held.pieces.len() implies one.pieces[i] == other.pieces[i] by {
        if held.pieces[i] is Insert {
            assert(items_of(one.pieces[i]) =~= items_of(other.pieces[i]));
        }
    }
    assert(one.pieces =~= other.pieces);
}

/// **More resolutions standing in only forget more**, so a stale replica
/// cannot un-forget a minted item by syncing an older redaction back.
pub proof fn theorem_more_forgets_more(held: ResolutionS, a: Seq<ResolutionS>, b: Seq<ResolutionS>)
    requires
        a.to_set().subset_of(b.to_set()),
    ensures
        forall|i: int, j: int|
            minted(held.pieces, i, j) && (#[trigger] items_of(stood(held, a).pieces[i])[j]).forgotten
                ==> items_of(stood(held, b).pieces[i])[j].forgotten,
{
    lemma_forgotten_by_more(held.pieces, a, b);
}

/// **What stands in for a resolution only forgets it.** What is read has its
/// shape, every `keep` is its own, and each minted item is its own or that
/// item forgotten.
pub proof fn theorem_only_forgets(held: ResolutionS, stated: Seq<ResolutionS>)
    ensures
        same_shape(held.pieces, stood(held, stated).pieces),
        forall|i: int|
            0 <= i < held.pieces.len() && held.pieces[i] is Keep
                ==> #[trigger] stood(held, stated).pieces[i] == held.pieces[i],
        forall|i: int, j: int|
            minted(held.pieces, i, j) ==> {
                let read = #[trigger] items_of(stood(held, stated).pieces[i])[j];
                read == items_of(held.pieces[i])[j] || read == forgetting(items_of(held.pieces[i])[j])
            },
{
    let read = stood(held, stated);
    assert forall|i: int| 0 <= i < held.pieces.len() implies #[trigger] same_piece(
        held.pieces[i],
        read.pieces[i],
    ) by {
        if held.pieces[i] is Insert {
            let items = items_of(held.pieces[i]);
            assert forall|j: int| 0 <= j < items.len() implies (#[trigger] items[j]).terminated
                == items_of(read.pieces[i])[j].terminated by {}
        }
    }
}

/// **Every minted item a resolution of the shape forgets is forgotten in what
/// is read**, whatever else is held beside it.
pub proof fn theorem_forgets_all_it_says(held: ResolutionS, stated: Seq<ResolutionS>, d: ResolutionS)
    requires
        stated.contains(d),
        same_shape(held.pieces, d.pieces),
    ensures
        forall|i: int, j: int|
            minted(held.pieces, i, j) && (#[trigger] items_of(d.pieces[i])[j]).forgotten
                ==> items_of(stood(held, stated).pieces[i])[j].forgotten,
{
    assert forall|i: int, j: int|
        minted(held.pieces, i, j) && (#[trigger] items_of(d.pieces[i])[j]).forgotten
        implies items_of(stood(held, stated).pieces[i])[j].forgotten by {
        assert(forgotten_by(held.pieces, stated, i, j));
    }
}

/// **Reading through the same resolutions twice is reading once.**
pub proof fn theorem_again(held: ResolutionS, stated: Seq<ResolutionS>)
    ensures
        stood(stood(held, stated), stated) == stood(held, stated),
{
    let once = stood(held, stated);
    theorem_only_forgets(held, stated);
    // Forgetting changes no shape, so the same resolutions are of the shape
    // the second time as the first.
    assert forall|e: Seq<PieceS>| same_shape(once.pieces, e) == same_shape(held.pieces, e) by {
        if same_shape(held.pieces, e) {
            assert forall|i: int| 0 <= i < once.pieces.len() implies #[trigger] same_piece(once.pieces[i], e[i]) by {
                lemma_same_piece_alike(held.pieces[i], once.pieces[i], e[i]);
            }
        }
        if same_shape(once.pieces, e) {
            assert forall|i: int| 0 <= i < held.pieces.len() implies #[trigger] same_piece(held.pieces[i], e[i]) by {
                lemma_same_piece_alike(held.pieces[i], once.pieces[i], e[i]);
            }
        }
    }
    assert forall|i: int, j: int| #[trigger] forgotten_by(once.pieces, stated, i, j) == forgotten_by(
        held.pieces,
        stated,
        i,
        j,
    ) by {
        if forgotten_by(once.pieces, stated, i, j) {
            let d = choose|d: ResolutionS|
                #[trigger] stated.contains(d) && same_shape(once.pieces, d.pieces)
                    && items_of(d.pieces[i])[j].forgotten;
            assert(same_shape(held.pieces, d.pieces));
        }
        if forgotten_by(held.pieces, stated, i, j) {
            let d = choose|d: ResolutionS|
                #[trigger] stated.contains(d) && same_shape(held.pieces, d.pieces)
                    && items_of(d.pieces[i])[j].forgotten;
            assert(same_shape(once.pieces, d.pieces));
        }
    }
    let twice = stood(once, stated);
    assert forall|i: int| 0 <= i < held.pieces.len() implies twice.pieces[i] == once.pieces[i] by {
        if held.pieces[i] is Insert {
            assert(items_of(twice.pieces[i]) =~= items_of(once.pieces[i]));
        }
    }
    assert(twice.pieces =~= once.pieces);
}

} // verus!
