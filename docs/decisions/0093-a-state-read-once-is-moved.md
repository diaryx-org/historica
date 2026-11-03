# 0093 — A state read once is moved

[0092](0092-the-digest-a-reader-checks.md) took the hash out of each step of
a reader's walk and left a cost it put down to `State::applied`: every step
moved every item of the parent into a new vector, so a walk cost revisions ×
lines even without the hash. It deferred the fix, because changing the
replay that runs means a new proof against `proof::result`
([0076](0076-proofs-on-the-code-that-runs.md)).

Measuring the step on its own showed the cost was somewhere else.
`applied` takes the state by value and moves what it does not touch. The
walk under `Store::content` never gave it a state it could move. The walk
keeps every state it computes in a map, in case another revision asks for
it, so the parent's state was still held when the child's step took it.
`Rc::unwrap_or_clone` then copied the whole file, every line's bytes, once per
revision walked. On a file of 2,000 lines and 1,000 revisions, that copy was
two thirds of reading the file. Rebuilding the vector in `applied` was
about 3 ms of the rest.

## The decision

- **The walk counts its readers first.** Before it applies anything, the
  walk is planned. The plan is the same walk with nothing applied. Each
  revision it reaches is settled the way the walk settles it: by a kept
  state, by a resolution, by the one statement
  [0081](0081-who-states-a-file.md) sends it to, by a creation, or by its
  parents. It counts how many steps will read each revision's state. A
  revision 0081 sends to a statement reads that statement's state once. A
  revision built from its parents reads each parent's once. A creation waits
  for its parents and reads none of them.

- **The last reader moves the state.** Each time a step reads a state, its
  count goes down, and when the count reaches nothing the walk lets go of
  the state. The step that read it last then holds it alone, and
  `unwrap_or_clone` moves it into `applied`. Most states are read by exactly
  one step, so most steps copy nothing. A fork that two sides edit is read
  twice, so the first side copies it and the second moves it.

- **A plan that is wrong costs time, never the answer.** A revision the
  plan did not reach has no count, and the walk never lets go of it. A count
  too high only means a state is held longer than it had to be. A count too
  low lets go of a state that is then read again, and the walk computes it
  again from its parents, as it computes any state it does not hold. Nothing
  the plan says enters a state the walk produces. Where the walk would fail,
  the plan stops, counts nothing, and the walk fails as it always did, with
  the same refusal.

- **The plan's answers are not asked twice.** The kept states it finds are
  handed to the walk, which would otherwise read the cache again. So are
  0081's answers about where a revision that says nothing of the file looks.
  The walk used to ask that question twice of every such revision whose
  statement it had not reached yet: once on the way down, and once on the way
  back with the statement's state in hand.

- **`replay` is unchanged.** `State::applied` and `applied_unverified` are the
  code 0076 proves, and this decision does not touch them. Every proof is
  the proof it was.

## What it measured

`historica cat <head> <file>` with an empty cache, fastest of fifteen or
twenty, the old and new binaries alternated on one store. The machine is a
four-core cloud container, not the one 0092 measured on, and these timings
include starting the process.

|                                                        | before   | after    |
|--------------------------------------------------------|----------|----------|
| 1 file × 1,001 revisions × 2,000 lines                 | 186.2 ms | 59.5 ms  |
| 2 files × 1,001 × 2,000, one file edited a revision    | 193.0 ms | 94.5 ms  |
| 30 files × 121 × 400, every file edited (the default)  | 58.4 ms  | 56.6 ms  |
| 30 files × 301 × 400, two files edited a revision      | 22.7 ms  | 23.0 ms  |

`check`, which walks every step hashed and reads no cache, took the same
time before and after on the first store, within the noise between runs.

The second store has a revision that skips the file between every two that
edit it, so every step goes through 0081's jump. The last two have short
files or few edits to each, so there is little to copy, and they are there
to show that the plan costs nothing a reader notices.

## Deferred

**A step that touches only what its document names.** With nothing copied,
`applied` still walks every item of the parent once to build the result.
Splicing the document's runs into the parent's vector in place, from the end
back, leaves the items before the first edit where they are. Measured on the
first store above, that saves about 3 ms of 61. It is a change to proved
code, so it needs its own proof against `proof::result`, and these numbers
say it is not worth that yet.

**Where 0081 sends a revision.** On the second store, most of what is left
is `Stating::stater`. It finds the latest statement a revision reaches, then
checks every earlier statement it reaches against that one, so asking it at
each of a long run of revisions costs statements × revisions.
