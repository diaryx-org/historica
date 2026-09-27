//! What the Verus proofs take on trust.
//!
//! Every proof in the library rests on Verus, Z3, and the specifications
//! `vstd` gives the standard library. Beyond those, it rests on this file and
//! nothing else: each function here is a wrapper whose body Verus does not
//! check and whose specification it takes as given, and
//! `tests/trust_boundary.rs` fails if anything elsewhere in `src/` asks the
//! same. Decision 0076 is why there is one file.
//!
//! - **SHA-256.** [`digest`] is [`State::digest`], and what it is said to
//!   compute is [`digest_of`], a function of the items nothing more is said
//!   about. A proof can show a digest is *checked* wherever the code checks
//!   one, and that the same items give the same digest; what SHA-256
//!   computes is below the line.

use crate::core::RevisionId;
use crate::replay::State;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::format::proof::ItemS;

#[cfg(verus_keep_ghost)]
verus! {

/// The digest decision 0031 has a document state: the SHA-256 of the file
/// the items spell, a forgotten item as its marker. Uninterpreted.
pub uninterp spec fn digest_of(items: Seq<ItemS>) -> RevisionId;

} // verus!

/// [`State::digest`], as the proofs take it.
#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures r == digest_of(state@),
))]
pub(crate) fn digest(state: &State) -> RevisionId {
    state.digest()
}
