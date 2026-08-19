# Historica

Historica is an experiment in readable, convergent version control.

The repository format follows one non-negotiable rule:

> The readable files are the authority.

A person must be able to inspect the history, understand its relationships, and
recover stored content without decoding an opaque database or binary operation
log. Binary indexes and snapshots may eventually exist as disposable caches,
but deleting every cache must lose neither information nor meaning.

## Current scope

The first `core` module models the smallest collaboration-safe history:

- immutable changes;
- explicit causal parents;
- a history that merges by set union;
- deterministic head discovery;
- explicit detection of two different changes claiming one ID.

It intentionally does not yet choose a document syntax, content-addressing
scheme, tree model, patch model, or merge policy. Those decisions should be
made against readable examples rather than hidden behind abstractions.

## Development

```console
cargo test
```

See [`docs/loro.md`](docs/loro.md) for the initial Loro evaluation.
