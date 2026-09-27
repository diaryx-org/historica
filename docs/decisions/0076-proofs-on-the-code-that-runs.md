# 0076 — Proofs on the code that runs

> **Amended 2026-09-27.** Three of the things *Leaves open* names are done.
> `replay::State::applied` is proved in place: it replays a document exactly
> when nothing is a cause to refuse it, to exactly the file the document
> describes, and every refusal names its cause. The trusted file it needed
> is [`src/trusted.rs`](../../src/trusted.rs), and what it holds is
> SHA-256, as an uninterpreted function of the items. Rewritten for the
> prover, `applied` kept its two passes and its map of inserts, and timed
> against the function it replaced — `cargo xtask bench`, and the two
> binaries alternated on one store with `cache/` emptied before each run —
> it is the same within the noise: 774 and 775 ms, fastest of twelve, for a
> cold `status` on the largest store to hand.
>
> `format::stand_in` is proved as well: what a reader consumes for a
> document that forgetting documents stand in for is its shape with each
> item forgotten exactly where the shape, or a forgetting document of that
> shape, forgets it. The laws the Bend spike stated of decision 0014's rule
> are proved of that statement: the order the documents arrive in and how
> often one does make no difference, more of them only forget more, and
> they destroy text and never write any. Stating it found the rule's one
> order. With the original destroyed the first stand-in is the shape, and
> the store handed them over in whatever order it had listed or learned of
> them, so two that disagreed about the shape read differently depending on
> what their files were called. It now hands them over in digest order, the
> order `check` already read them in. The resolution grammar's `stand_in`
> has the same shape and is not yet proved.

Two spikes asked whether historica's rules could be proved rather than
tested. One restated the crate in Bend, whose checker proves laws of a
program by rewriting, and stated a few hundred of them; one of those laws
failed against the parser, and the fix — an `insert` at a `delete`'s own
position hid the deleted run from the operation after it — is 15ba1b3. The
other took `replay::State::applied` and the merge walk into Verus, which
proves Rust against a specification with an SMT solver, and proved both: the
replay step against a statement of what a document means, and the merge
converging in any causal order.

Both proved a copy. The Bend spike was a second implementation, and the Verus
spike a port — the function retyped in the part of Rust Verus reads, beside
the crate rather than in it. A proof of a copy is a proof about the code only
for as long as someone keeps the two the same, and nothing does: the crate's
`applied` could change tomorrow and the proof would still verify, about a
function nobody runs.

`fs-transaction`, which lands every document historica writes, does it the
other way. Its specifications sit on the functions that run, its proofs sit
beside them in modules only Verus compiles, and an ordinary build sees
neither. There is no copy to drift from.

## The decision

**A proof in historica is a proof of the function that runs.**

- **The specification is on the function.** `#[cfg_attr(verus_keep_ghost,
  verus_spec(…))]` states what it ensures, and `verus_verify` marks it and the
  types it reads. `verus_keep_ghost` is a cfg Verus sets and nothing else
  does, so an ordinary build — every job in CI but one, docs.rs, a caller's
  `cargo build` — compiles the function with none of it.
- **The proof is beside it**, in a `proof.rs` child module declared under
  `#[cfg(verus_keep_ghost)]`: the specification functions the contract is
  written in, and the lemmas that carry it. `format/order.rs` and
  `format/order/proof.rs` are the first pair.
- **The manifest names nothing.** Verus brings its own verified standard
  library; `vstd` is not a dependency, optional or otherwise. The only trace
  in `Cargo.toml` is the two cfgs declared to the `unexpected_cfgs` lint.
- **`cargo xtask proofs` verifies it, and CI runs that.** The job fetches a
  pinned Verus release once into a per-user cache, has `cargo check` build the
  dependencies with the Rust release Verus was built against, and hands the
  one compile that is the library to `verus` in place of `rustc` — xtask is
  the `RUSTC_WORKSPACE_WRAPPER` that does the handing. Verus writes nothing
  cargo counts as a finished build, so every run verifies.

## What it costs

**A proved function is written in the part of Rust Verus reads.** That is a
real constraint on the code that runs, and it shows: `matches!` where a
derived `==` would be a trait impl the proof takes on trust, a `match` where
`Option::map` would take a closure, arithmetic that saturates where it
cannot overflow in practice but a proof cannot know it. A type that holds an
invariant takes itself by value where it would take `&mut self`, because
Verus will not hold an invariant across a borrow into a call that might
unwind. Each proved function's documentation says what shape it takes and
why, so the next edit does not undo it for tidiness.

A hot function rewritten for the prover is measured before it lands, with
`cargo xtask bench`. A proof that makes the program slower is a proof of a
worse program.

**The job is heavy.** The release bundle is about 450 MB zipped and 1.4 GB
unpacked, and CI fetches it on every run. It takes about twenty seconds on a
fast link, and the verification itself a few seconds. Locally it is fetched
once per release.

## What the proofs rest on

Verus and Z3; the specifications `vstd` gives the parts of `std` a proof
calls — `Vec`, `Option`, integer arithmetic; and whatever the library asks
Verus to take on faith, which today is nothing. `tests/trust_boundary.rs`
holds that: an unverified body, an assumed specification, an assumed fact or
an admitted goal anywhere in `src/` fails the test suite, unless it is in a
file the test names. When a proof needs one — `replay` will, for SHA-256,
which a proof can say is *checked* but not what it *computes* — it goes in
one file, and that file is the review.

What a proof covers is the function it is written on. The code around it is
read, not proved: the parser pushes each operation it reads into an
`Ordered` and returns what `into_operations` gives back, and that it does
so is three lines anyone can check.

## The first proof

`format::order`. The parser admits each operation through `Ordered::push`,
and what is proved of it is:

- what an `Ordered` holds is ordered **pairwise** — every operation against
  every one before it, not only its neighbour: positions never descend, the
  only tie is a replacement's `delete` then `insert`, and past a `delete`
  nothing starts inside its run and no `delete` meets it;
- `push` refuses an operation **exactly** when admitting it would break that.

Checking each operation against two others, the one before it and the last
`delete`, is what makes the pairwise rule hold. With the second check taken
out — the parser as it stood before 15ba1b3 — the proof fails, at the step
that needs the last `delete` to have been checked. The bug the Bend spike
found by testing a law is one this proof would have refused to verify.

## Rejected alternatives

**Prove a port, and fingerprint the source it was ported from.** A port
beside the crate, with a hash of each function it copies and a test that
fails when the function changes, so that someone re-reads the port. It
notices drift but cannot close it: the re-reading is the proof's premise and
nothing checks it. It was built for this decision and discarded when the
alternative turned out to work.

**`cargo verus`, with `vstd` a dependency.** The documented way to verify a
crate with dependencies. It needs `vstd` in the manifest — and with it three
macro crates pinned to nightly-dated versions — in every caller's lockfile,
for a library none of them calls. Made optional behind a feature, it is still
in the published manifest, and `--all-features` builds it: the `doc` job and
docs.rs would compile a prover's standard library to document a
version-control library.

**Prove the specification, not the program.** The Bend laws and the merge
model are theorems about a definition, and some of them are worth having as
that: the merge model is where convergence in any causal order is proved,
and nothing in `merge.rs` is yet written in a shape Verus reads. It stays on
the spike branch as a plan for the proof of the code, not as a substitute
for it.

## Leaves open

- **Which functions next.** `replay::State::applied`, whose port is already
  proved against a statement of what a document means and needs rewriting
  into the verified subset without losing its single pass; the Bend spike's
  laws about the stand-in for a forgotten document; the merge walk, largest
  and last.
- **A trusted file**, when the first proof needs one, and what it is called.
- **Caching the bundle in CI**, if twenty seconds a run starts to matter.
