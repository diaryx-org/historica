# Historica

Historica is an experiment in readable, convergent version control.

The repository format follows one non-negotiable rule:

> The readable files are the authority.

A person must be able to inspect the history, understand its relationships, and
recover stored content without decoding an opaque database or binary operation
log. Binary indexes and snapshots may eventually exist as disposable caches,
but deleting every cache must lose neither information nor meaning.

## Current scope

The `core` module models the smallest collaboration-safe history:

- immutable revisions, each naming both the digest of its own bytes and the
  change it is a version of;
- explicit causal parents, named by digest, so history is a Merkle DAG;
- explicit supersession, so rewriting a change is recorded rather than hidden;
- a history that merges by set union;
- deterministic head discovery, over parents and over supersession alike;
- resolution of a change to its current revision, including the legitimate
  states of divergence and abandonment;
- rejection of two revisions with disagreeing bytes claiming one digest.

The `format` module reads and writes the revision document those revisions are
stored as. It parses strictly — one byte sequence per set of facts, so that
hashing the file is as trustworthy as hashing a canonical model would be — and
refuses anything else with an error naming the line and the fix. Writing a
parsed document reproduces its bytes exactly, and a revision's ID is the
SHA-256 that `shasum -a 256` already prints for the file.

`tests/corpus/revisions/` is the specification, executed. Seven hand-written
files are a real five-change history containing a merge, an amendment by a
reviewer, and the rewrite that amendment forced; nine more are invalid, each
for one stated reason that `tests/corpus.rs` holds the parser to.

The same module reads and writes the operation document, which is what one
revision did to one file: a list of deletes and inserts against the state at
that revision's parents, positions counted into the parent rather than into
the document being built. It is as strict as the revision document and for the
same reason — operations ascend, never overlap, and never state one fact twice,
so one byte sequence parses per edit and the digest can cover the file. Items
are lines, so an item may hold a carriage return that the format's own lines
may not, and a file whose last line has no terminator says so in one place.

`tests/corpus/operations/` is that half of the specification. The numbered
files are the edits the numbered revisions made to one file, with a gap at 04
because a merge that changes nothing about a file names no operation document;
three more pin the rules that no revision happened to exercise, and seventeen
invalid ones are each refused for their own stated reason by
`tests/operations.rs`. `states/` is that file as it stands at each revision,
hand-written, which is what the replayer is held to.

The `replay` module materialises a file from what was done to it. It does the
linear case, which decision 0007 says costs nothing: positions are stated
against the parent, so applying them is arithmetic rather than interpretation,
and a chain of documents from the root produces the file byte for byte. It is
also where a `delete` line's redundancy is spent — a document whose recorded
items disagree with the parent it claims to edit is refused there, rather than
absorbed into a merge, and so is a result that would leave a line without a
terminator anywhere but at the end.

The `diff` module is the writing half, specified by 0009. Given the file at a
revision's parent and the file as it stands, it records what the revision did:
line matching from `similar`, configured to histogram and to no deadline, and
then Historica's own rules — maximal runs, a replacement anchored at the removed
run's start, and a result that parses whatever the matcher hands over. A file
that did not change names no document at all. `tests/corpus/diffs/` holds a
before, an after, and the document recorded for the pair, for the choices a
property test cannot see; `examples/matchers.rs` is the measurement decision
0009 chose the matcher on.

The `store` module is that format on disk. It loads a `history/` directory by
reading files and never their names, so renaming every revision in a store
changes no identity and breaks no reference — which is what lets a store be
hand-arranged into something a file browser can narrate. The writer still names
files by digest, appends only, and never overwrites. `check` reads a store
without loading it and separates errors, which mean the store contradicts
itself, from notes, which never fail: an undelivered parent, a duplicate, or a
sync tool's conflicted copy is a legitimate state and is reported as one.

It intentionally does not yet merge. Concurrent branches need the Eg-walker
replay decided in 0007, and none of that is built, so a caller supplies the
chain a file is replayed along. Nothing links a revision to its operation
documents either, because that link is the tree, which 0007 defers to 0008, and
that is also why `check` cannot yet hold a document to the parent it edits.
There is no command-line front end yet; `init`, `check`, and `arrange` exist as
decisions, and the first two as library operations. Those should be built
against readable examples rather than hidden behind abstractions.

## Decisions

Choices that constrain later work are written down as they are made.

- [`docs/decisions/0001-identity.md`](docs/decisions/0001-identity.md) — why
  every node carries both a derived revision ID and an assigned change ID.
- [`docs/decisions/0002-revision-document.md`](docs/decisions/0002-revision-document.md)
  — the readable revision document, and why its digest covers the file rather
  than a re-serialised model. Examples live in
  [`tests/corpus/revisions`](tests/corpus/revisions).
- [`docs/decisions/0003-store.md`](docs/decisions/0003-store.md) — the store:
  identity comes from content, filenames are presentation.
- [`docs/decisions/0004-parser-contract.md`](docs/decisions/0004-parser-contract.md)
  — strict reading, the `historica-v0` preamble, and why a reader's
  vocabulary can only ever grow.
- [`docs/decisions/0005-authorship.md`](docs/decisions/0005-authorship.md) —
  authorship is copied into every revision of a change, and is a claim rather
  than evidence.
- [`docs/decisions/0006-store-questions.md`](docs/decisions/0006-store-questions.md)
  — one-line bookmarks, a visible `history/` root, and what `check` treats as
  an error rather than a note.
- [`docs/decisions/0007-content-and-merge.md`](docs/decisions/0007-content-and-merge.md)
  — a revision records what it did rather than what a file is, and concurrent
  edits merge by replay rather than by three-way heuristic. Examples live in
  [`tests/corpus/operations`](tests/corpus/operations).
- [`docs/decisions/0008-tree.md`](docs/decisions/0008-tree.md) — files carry
  identifiers and paths hang off them, there are no directories, and a revision
  records what it did to the file set rather than what the file set is.
- [`docs/decisions/0009-diff.md`](docs/decisions/0009-diff.md) — how operations
  are recorded from an edited file, why the matcher is a dependency where the
  merge rule could never be, and the replacement anchoring 0007 left ambiguous.
- [`docs/loro.md`](docs/loro.md) — the initial Loro evaluation, and the
  conditions that would reverse it.

## Development

```console
cargo fmt --all --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test
```

The corpus checks with tools that are already installed, which is the claim the
format exists to make:

```console
cd tests/corpus/revisions && shasum -a 256 -c MANIFEST
cd tests/corpus/operations && shasum -a 256 -c MANIFEST
cd tests/corpus/diffs && shasum -a 256 -c MANIFEST
```
