# 0092 — The digest a reader checks

[0031](0031-a-document-states-its-result.md) put a digest on every edit and
held replay to it:

> **Replay verifies it.** A replayed state whose bytes do not hash to the
> stated result is refused in the words `replay` already uses for a quoted
> item that disagrees.

`replay::State::applied` did that at every step, so materialising a file
hashed every state of it on the way to the one asked for. The arithmetic of a
step touches the items a document names. The hash reads every byte of the
file. With nothing cached, on a file with a long history, the hash is most of
what reading the file costs.

Measured on this machine, which hashes SHA-256 in software at about 420 MB/s,
with the store's catalogues kept and its states deleted before each run:

|                                              | replay alone | of which hashing |
|----------------------------------------------|--------------|------------------|
| 400 lines, 120 revisions, documents in memory | 6.2 ms       | 4.6 ms           |
| 2,000 lines, 2,000 revisions                 | 645 ms       | 563 ms           |

## The decision

- **A reader holds the state it was asked for to the digest stated about it,
  once.** The walk under `Store::content` applies each document with
  `State::applied_unverified`, which makes every check `applied` makes except
  the hash: positions in range, quoted items that agree, a terminator only
  where one may be missing. It notes, for each revision whose state it has
  not hashed, which documents stated what. When the walk ends, the state
  asked for is hashed against each of those statements with
  `State::check_result`, which is 0031's check.

- **A revision that says nothing about the file is owed its parent's check.**
  It holds its parent's state, so asking for the file there checks the digest
  the last edit stated. A merge whose parents agree is owed every parent's
  check. Its parents hold one state, but two edits can reach that state and
  state different digests of it. Checking only one parent's would make a
  wrong digest pass or refuse by which parent's identifier sorts first.

- **A refusal names the document it named before.** When the walk fails,
  whether on the state asked for not matching a digest or on anything else
  (a quote that disagrees, a position out of range, a document missing), it
  runs again as a reader walked before this decision, with every step
  hashed, and returns the refusal that walk meets. A wrong digest passed on
  the way is then named ahead of a later step that fails for another reason,
  as it was. Failing costs a second walk. Succeeding hashes the state asked
  for and no other.

- **`check` hashes every step**, as 0035 has it: it wants the work, not the
  answer. It walks with `Caching::Replay`, and that walk uses `applied`.

- **`State::applied` is unchanged.** It is now `applied_unverified` followed
  by `check_result`, each proved. The proof of `applied` follows from theirs.
  `replay::replay` and every other caller of `applied` still hash every step.

## Why this does not weaken 0031

No state the walk computes comes from a stated digest. Every state is the
previous state with a document's operations applied. So a wrong digest
stated partway down a history changes nothing the walk produces after it.
It is a document that contradicts the store, and finding those is `check`'s
work.

What 0031 bought is still there. A hand replayer has a digest at every edit.
A second implementation is held to every store it opens: each answer it
gives is hashed against the document that states it. And drift is still
loud. A replayer that gets a step wrong produces a wrong state. That error
either survives to the state asked for, where the hash refuses it, or meets
a later `delete`, which quotes the items it removes and refuses a quote that
disagrees. The one escape is a wrong step that later edits make right again
without a quote noticing, such as identical lines swapped and then both
deleted. A reader no longer refuses there. `check` still does.

## What changed for a caller

A store where a document states the wrong digest and a later revision edits
the same file again now reads at the later revision. Before, every reader
of that file past the wrong document refused. The revision holding the wrong
document still refuses, and so does every revision that holds the same state
because it says nothing about the file. `check` reports the same error it
always did.

## What it measured

The bench store, `cargo xtask bench`'s default shape (30 files, 121
revisions, 400 lines each), and a deep one, `files=1 revisions=1000
lines=2000`. `Store::content` of the file the bench reads at the head, with
the catalogues kept and the states deleted before each run, fastest of ten
or twenty, old and new library alternated on one store:

|                               | before   | after    |
|-------------------------------|----------|----------|
| 30 files × 121 × 400 lines    | 10.6 ms  | 7.3 ms   |
| 1 file × 1,001 × 2,000 lines  | 244 ms   | 106 ms   |

## Deferred

[0093](0093-a-state-read-once-is-moved.md) measured this and found most of
the 41 µs was not `applied` at all: the walk held every state it computed,
so each step copied its parent's whole file before applying anything. The
walk now lets go of a state once the last step that reads it has, and that
step moves it. What follows is what was left, and 0093 defers it again.

**A step that costs what its document says.** `applied` still moves every
item of the parent into a new vector at every step, so a walk costs
revisions × lines even without the hash. On the deep store above, that is
about 41 µs of the 106 µs a revision now costs. Most of the rest is reading
and parsing the documents. Folding a run of documents into one map of
positions and building the file once would remove the per-step cost.
Replacing the vector with a tree that splices in logarithmic time would too.
Either way, [0076](0076-proofs-on-the-code-that-runs.md) has the replay that
runs proved where it runs, so the new structure needs a proof of its own
against `proof::result`. That proof is the work, and these numbers say it
pays only on files with long histories and many lines.
