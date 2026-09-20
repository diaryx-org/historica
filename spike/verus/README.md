# Verus spike: `replay::State::applied`

A one-day question: can the linear replay step be *proven* to do what its
rustdoc says, using [Verus](https://github.com/verus-lang/verus) on a port of
the Rust itself rather than a model of it?

Answer: yes. `replay.rs` here is a faithful port of `State::applied` and
`agrees`, with a specification written independently of the code, and Verus
verifies the whole file — implementation, a theorem about the specification,
and two concrete examples — in about two seconds at the default budget.

## Running it

Verus is a prebuilt bundle (`verus-0.2026.09.13.671956e-arm64-macos`), pinned
to Rust 1.98.1, which is already the org toolchain. Strip Gatekeeper's
quarantine attribute once (`xattr -dr com.apple.quarantine <bundle>`), then:

```
<bundle>/verus spike/verus/replay.rs
```

`--multiple-errors 12` reports more than the first failure per function.

## What is proven

`applied` is held to a specification that never mentions the implementation:

- `deleted_at(ops, p)` — some `delete` in the document covers parent position
  `p`;
- `inserts_at(ops, p)` — the items every `insert` at `p` contributes, in
  document order;
- `result(parent, ops)` — at each parent position, the inserts there, then the
  parent's item unless deleted; then the gap past the last item.

The contract on `applied`:

- **`Ok`** produces exactly `result(parent, ops)`, is well-terminated (only the
  last line may lack a newline), and if the document states a digest and no
  item is forgotten, the digest of what was produced is the stated one.
- **Every `Err` is a real contradiction.** `OutOfRange` only when some delete
  or insert names a position the parent does not have; `ItemDisagrees` /
  `TerminatorDisagrees` only when some recorded item is not what the parent
  holds; `UnterminatedItemNotLast` only when `result` is not well-terminated;
  `ResultDisagrees` only when the stated digest differs from the digest of
  `result`.

Plus `theorem_order_independent`: for two documents stating the same facts
(`same_facts`, membership both ways) that each satisfy `distinct_inserts` (no
two inserts at one position — what the parser's `InsertsAtOnePosition`
guarantees), `result` is the same. This is the rustdoc's "operations out of
order are applied to the same result", with its hypothesis made explicit.

## What the spike found

- **The order-independence claim needs a qualifier.** Two inserts at one
  position would concatenate in document order, so the claim is true *of
  documents the parser accepts*, not of any operation list. The code already
  relies on this ("`document` is expected to be one the parser would accept");
  the spec makes the dependency a named hypothesis.
- **`at + count` overflows.** The first port wrote it plainly and Verus flagged
  it; the crate uses `saturating_add`, which is right. Verus checks arithmetic
  by default, so this class of bug is free.
- **`insert 3` and `insert 4` after `delete 3 1` produce the same bytes** in a
  linear replay (`example_insert_beside_a_deletion`). The rustdoc's distinction
  is real but is only observable through item identity in a merge, which is
  worth saying in the doc.
- **The spec catches mutations.** A no-op delete, a dropped trailing-gap
  insert, and an off-by-one on the delete bound each fail verification.

## What it cost, and where the friction is

- ~600 lines for ~120 lines of Rust, of which roughly half is specification
  and theorem and half is loop invariants and step assertions. Most step
  assertions are the same three lines (`ghost before = v.deep_view()`; push;
  `assert(v.deep_view() =~= before.push(x@))`) and would be one lemma.
- Two deliberate deviations from the crate: `BTreeMap<usize, Vec<Item>>` is a
  `Vec<Vec<Item>>` indexed by gap (vstd's `BTreeMap` specification is thin),
  and SHA-256 is an uninterpreted `digest_s` — what is proven is that the check
  is made, not what SHA-256 computes. Both are the trusted boundary, stated.
- `#[verifier::loop_isolation(false)]` on `applied` lets facts about unmodified
  variables flow into loops; without it every inner loop restates them. At the
  size of this function it costs nothing; a larger one would be split.
- `Item::clone` is hand-written with `ensures r@ == self@` because a derived
  `Clone` carries no such contract.

## What this says about `merge.rs`

`replay.rs` is the easy half: one parent, positions that never move. `merge.rs`
(Eg-walker over Fugue) is ~2100 lines with a transient tree, a causal filter,
and the theorem that matters — convergence for any causal order — needs
induction over the event graph rather than over one document. The data types
are the same shape as here (`Vec`, `BTreeMap`, `BTreeSet`, digests), so the
port cost is comparable per line; the proof is a different order of work,
because the specification itself is the Fugue ordering, and writing it down is
the conformance suite decision 0007 says the module owes.
