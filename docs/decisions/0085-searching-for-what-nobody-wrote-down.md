# 0085 — Searching for what nobody wrote down

The corpus is the specification executed, and every file in it is a claim
somebody thought to make. [0076](0076-proofs-on-the-code-that-runs.md) proves
what somebody thought to specify. Neither reaches what nobody thought of, and
the two bugs [0078](0078-where-a-cache-is-kept.md) and
[0079](0079-a-reader-looks-where-forget-files.md) closed were exactly that:
each was a sentence in a decision that was true of every case anyone had
written down and false of one a sync could produce. Both were found by hand.

[0007](0007-content-and-merge.md)'s conformance suite already searches,
for merging, from a seed `cargo xtask test` rotates. This decision extends that
to the two places a search was owed next: the strict parsers
[0004](0004-parser-contract.md) stakes the format on, and the sentence
[0003](0003-store.md) stakes the store on — a store is synced by anything
that copies files.

## The decision

- **The parsers are fuzzed with bolero**, in `tests/strict.rs` and beside the
  cache modules that keep their grammars private. A target is an ordinary
  `#[test]`: under `cargo test` it runs on random input for about a second, on
  stable, and the same target runs coverage-guided under libFuzzer through
  `cargo xtask fuzz`. Each grammar is held to what its decision promises,
  which is not the same promise everywhere: a hashed document writes back
  byte for byte (0004); a listing, a bookmark and a skip rule read back as the
  same value; a cache's text is total, round-trips what a writer keeps, and
  never yields an entry its lines do not state (0035, 0036, 0049).
- **The store is simulated**, in `tests/simulation.rs`: replicas in memory,
  each with a clock and a cache outside its store, doing every kind of work
  and meeting only by copies that may be partial, out of order, cut short,
  and never delete. After every step each replica is held to `check`, to its
  cache changing nothing but time, to forgotten items staying forgotten, and
  to agreeing with any replica holding the same documents.
- **The simulation shrinks by hand**, as the conformance suite does and for
  its reason: what makes a counterexample readable is knowing what an action
  means, and a round is a list of actions that each mean something in any
  state.
- **CI pays seconds, and the search moves.** `cargo xtask test` hands both
  seeded searches a fresh seed and bolero draws its own, so every run looks
  somewhere new and prints what reproduces it. `cargo xtask soak` and
  `cargo xtask fuzz` run the same searches for as long as a person cares to
  wait, and are not jobs.
- **What the search finds is a task or a fix**, as anything else found is. A
  finding that needs a decision before it can be fixed is written down as a
  task, and the simulation recognises its signature — narrowly, by the
  conditions the task names — so that the search keeps looking past it;
  `HISTORICA_SIMULATION_STRICT=1` reports it again, and closing the task
  deletes the recogniser.

## Why bolero, and why only there

The repository had no dev-dependencies, and the conformance suite says why it
has no shrinking library: a general one shrinks values, and a readable merge
counterexample needs domain knowledge to shrink. That argument holds for the
simulation and is why the simulation follows it. It does not hold for a
parser. A parser's input is bytes, a byte string shrinks generically, and
what a parser most needs that a random search cannot give is coverage
guidance — the difference between mutating a corpus blindly and learning
which mutations reach a branch nobody has reached. bolero is the one crate
that gives both from one target: a property test on stable and a libFuzzer
target on nightly, so neither CI nor the toolchain floor has to change for
the guided search to exist.

The cost is a dev-dependency tree, compiled by the jobs that build tests, and
a `[profile.fuzz]` in the manifest that only `cargo bolero` reads. Neither
reaches a library consumer.

The machine-generated corpus libFuzzer keeps lives in `tests/__fuzz__/`,
which git ignores. The corpus in `tests/corpus/` stays hand-written.

## What it found

In the course of being written, and each recorded where it lives:

- A catalogue path holding a newline emptied the whole catalogue on every
  read, and a crafted one could state a forgetting nothing on disk states;
  a path ending in a carriage return was read as another path. Fixed.
- `check` reported a merge's resolution as needless, and replayed a merge's
  walk as though a parent had left a file alone, wherever a parent's own
  document had not arrived — an absence 0006 makes a note, reported as two
  contradictions. Fixed.
- `carry` restated a merge verbatim where the merge had joined a rewrite to
  work standing on what it rewrote. Nothing *moved* — the rewrite restated
  the same text — but the merge's past held two copies of it, one per side,
  and carried it held one: a `keep` found fewer elements under a name than
  it keeps, or a deletion on one side took the other side's line. 0059's
  refusal of a merge above moved content now also refuses a merge whose
  past would name different documents, or the same ones a different number
  of times. Fixed.
- [A merge agrees by text](../tasks/a-merge-agrees-by-text.md),
  [a stand-in filed beside another copy](../tasks/a-stand-in-filed-beside-another-copy.md),
  [forget leaves the folder holding what it destroyed](../tasks/forget-leaves-the-folder-holding-what-it-destroyed.md),
  [forget at a rewrite leaves its predecessor legible](../tasks/forget-at-a-rewrite-leaves-its-predecessor-legible.md),
  and [a listing ending in a carriage return](../tasks/a-listing-ending-in-a-carriage-return.md):
  open, each with a repro.

## What this leaves open

The simulation does not yet rename, link, set the executable bit, write skip
rules, `squash`, `arrange`, or use historica's own transports, `receive` and
`fetch`. Each is an action to add, and each addition is a place the search
has not looked.
