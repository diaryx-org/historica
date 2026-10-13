---
title: A merge agrees by text
description: Decision 0032 lets a merge state a delta, or nothing, where its parents agree, and agreement is decided by comparing text — so two replicas making one edit, or a forgetting on each side, leave `record`, the reader and `check`'s walk answering differently, and `check` calls the store corrupt
status: open
created: 2026-10-13
updated: 2026-10-13
part_of: '[Tasks](/docs/tasks/tasks.md)'
---

# A merge agrees by text

[0032](/docs/decisions/0032-a-merge-states-its-resolution.md) splits what a
merge says about a file in two: where the parents' states are identical it
states nothing, or a delta against that agreed state, and where they differ
it states a resolution. *Identical* is decided by comparing
[`State`](/src/replay.rs)s, which compare by text. The walk that proposes a
merge, and that `check` replays a history with (`merge::quotes`), compares by
identity: an item is `(R, i)`, and two items with one text are two items.
Wherever those two answers part, the history is read three ways.

Found by `tests/simulation.rs`, three ways round.

## Repro: the same edit made twice

Two replicas make one edit, and a person merges them and resolves the file to
what both sides say.

```console
$ historica init . && printf 'a\n' > f.txt && historica record -m root
$ cp -R history ../root-copy
$ printf 'x\na\n' > f.txt && historica record -m left
$ mv history ../left && cp -R ../root-copy history
$ historica record -m right           # the folder already says x, a
$ cp -Rn ../left/ history/            # a sync
$ historica merge                     # renders x twice, between markers
$ printf 'x\na\n' > f.txt
$ historica record --merge <left> --merge <right> -m merge
$ printf 'x\n' > f.txt && historica record -m child
$ historica check
error: <child>, file <f>: <child> deletes `a` at position 1, where its author's view held `x`; one of the two is corrupt, and the digests say which
```

`record` read the parents as agreeing, so the merge states nothing for
`f.txt` and its content is `x, a`. The child's delete is right against that.
`check`'s walk holds both `x`s, reads the merge as `x, x, a`, and finds the
child's quote at the wrong place.

Two more things follow from the same misreading:

- **The conflict markers are not refused.** `merge` renders the walk, which
  sees two `x`s and draws a contest; `record --merge` decides the file is
  agreed, so 0012's refusal of a marker line — which only the
  parents-differ branch asks — never runs. Recording without resolving
  writes the marker lines into history as content.
- **A merge across this one** meets each `x` under two names, which is the
  thing 0032's references exist to prevent.

## Repro: a forgetting on each side

```console
$ # root `a`; left records `a, x`; right records `a, y`; merged and resolved to `a, x, y`
$ historica check                     # nothing to report
$ historica forget <left> f.txt --lines 2
$ historica forget <right> f.txt --lines 2
$ historica check
error: <merge> states a resolution for the file <f>, which both its parents leave exactly the same; …
```

A forgotten item compares as `\ forgotten`, so two parents that differed
compare alike once each has a line forgotten, and the resolution the merge
had to state becomes, to `check`, one it was forbidden to state.
[0014](/docs/decisions/0014-forgetting.md) promises a forgotten store passes
`check`. The converse also happens in the simulation: a merge recorded where
the parents agreed, read on a replica holding a forgetting the recorder did
not, is reported as owing a resolution it does not state, and the delta it
did state is replayed at the wrong positions.

## What it needs

A decision before a fix: what *agree* means in 0032. The candidates the
simulation suggests:

- **Agreement is identity.** The parents agree where they hold the same
  items in the same order — the sequence of `(document, ordinal)` names, not
  the text. Forgetting changes no name, so it cannot flip agreement, and two
  replicas' identical edits are a disagreement that a resolution settles by
  keeping one side. Costs a merge of the same edit made twice a resolution
  where today it states nothing.
- **Agreement stays text, and the walk learns it.** The walk, at a merge
  whose parents agree by text, collapses to the agreed state. Keeps today's
  documents valid and moves the special case into the algorithm 0032
  demoted to proposing.

Whichever it is, `record`'s marker refusal has to ask the same question
`merge` rendered.

## Done when

0032 says what agreement is; `record`, the reader and `check` decide it the
same way; both repros check clean; and `agreed_by_text` in
`tests/simulation.rs` — which recognises this task's signature so that the
search can look past it — is deleted, with `HISTORICA_SIMULATION_STRICT=1
cargo xtask soak` passing.
