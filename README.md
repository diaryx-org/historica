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

It intentionally does not yet choose a document syntax, digest algorithm, tree
model, patch model, or merge policy. Those decisions should be made against
readable examples rather than hidden behind abstractions.

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
  edits merge by replay rather than by three-way heuristic.
- [`docs/loro.md`](docs/loro.md) — the initial Loro evaluation, and the
  conditions that would reverse it.

## Development

```console
cargo test
```
