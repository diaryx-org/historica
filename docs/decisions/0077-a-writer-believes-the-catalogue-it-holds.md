# 0077 — A writer believes the catalogue it holds

[0036](0036-where-a-digest-is.md) gave `operations/` a catalogue in `cache/`
and kept one walk of the directory for writers:

> A writer asks the directory, because a writer is about to add to it: the
> question is whether the store already holds these bytes, and `no` is what
> a catalogue taken from `cache/` cannot be believed about. Once per command
> rather than once per document.

Once per command is once per record, and a walk of `operations/` is a
listing of every directory in it — one per revision the store has ever held,
and one more per directory a recorded path sits in. The cost of a record
therefore grew with the length of the history, however little it recorded.

Measured on a folder of 5,000 files of about 1.7 KB, one root revision and
then one file edited and recorded per revision under a restriction naming
it, release build: `record` took 38 ms at the tenth revision and 115 ms at
the two-thousandth. Sampling the loop at 2,000 revisions put 79% of
`record`'s time in `insert_operation_at` → `upgrade` → `catalogue::read` →
`walk`, and most of that in `opendir`. The state walk that
[The state at a revision without the walk](../tasks/closed/the-state-at-a-revision-without-the-walk.md)
is about cost 10 ms of it at that length. A writer that records every few
seconds — a program keeping a folder's history as it is edited, rather than
a person asking — reaches ten thousand revisions in weeks, where the walk
alone would be half a second a record.

## The decision

- **A writer asks the catalogue the store already holds.** Walked where
  something in the command paid for a walk, taken from `cache/` otherwise,
  and a walk only where there is neither — a store with no catalogue at all,
  which is what the first record into a new one is. A `yes` is taken as it
  always was. A `no` is now believed, and the bytes are filed.

- **What a writer files is kept as the revision naming it lands.**
  `Store::insert_at` is the one door a revision goes through, and decision
  0075 already made it where a set of writes ends. It now writes the
  catalogue back there, once, when a writer has added to it since the last
  time: its held lines and the writer's entries together, in the digest
  order `cached` reads. Every command that files content — `record`, a carry,
  `receive`, `fetch`, `export` onto a copy — lands content first and
  revisions last, so each writes the catalogue once; a `receive` of five
  hundred revisions writes it on the first and finds nothing unkept after.

- **`Store::keep_catalogue` is public**, for a caller that files documents
  with no revision after them. Not calling it costs what 0036 already
  charged: a reader that cannot place a digest walks `operations/` once,
  reading only what `cache/` could not account for, and that walk writes the
  catalogue back. It never costs the scan behind it.

- **A removal still walks.** `forget`, `prune` and the compliance inside
  `receive` take a file out of what the directory holds, which has to be
  taken out of the whole of it; each then lets the catalogue go or empties
  `cache/`, and the next reader walks once.

- **`check` is unchanged.** It reads nothing from `cache/` and writes nothing
  to it, as 0035 and 0036 require.

## What a `no` costs when it is wrong

The catalogue in `cache/` is wrong about a digest when the bytes reached
`operations/` without passing through a writer: copied in by hand, or by a
sync that knows nothing of historica, since the catalogue was last kept. A
writer that then files the same bytes files them a second time, under the
name it was given.

That is the whole of the cost. [0003](0003-store.md)
makes content its identity and a filename presentation, so a digest held
twice is still one document: the catalogue maps a digest to one path, and a
duplicate resolves to the first in walk order, as it did before this
decision. `check` reports it as `DuplicateContent`, which is a note. No
answer changes and nothing is lost; what is spent is the bytes of one
document.

It is not a question 0036's argument for walking protected against either.
The one belief 0036 could not check by hashing is *what forgets what*, and a
writer asking whether it holds bytes is not asking that: a forgetting
document that arrives by copy is found by the readers that look for one,
which walk before they report that nothing forgets a digest, exactly as
before.

## What this is not

**Not a writer that writes the catalogue per document.** 0036 refused that
as quadratic, and it is: the catalogue is one line per file in
`operations/`. Once per revision is linear in the store per revision, which
is what the walk it replaces was, and is sequential text where the walk was
a directory open per revision. On the store above the kept catalogue is
about 1 MB at 2,000 revisions.

**Not the end of the slope.** At 2,000 revisions the same record is 33 ms,
against 115 ms; what still grows is opening the store, which reads
`revisions/` in full (0036 deferred it, and it is now the larger part), the
catalogue written back, and the state walk the task above is about.

## Consequences

- `Store::catalogue_to_add` is what the four writers file into —
  `insert_operation_at`, `insert_resolution_at`,
  `insert_forgotten_payload_at`, `insert_payload_in_pieces` — and
  `Store::catalogue_mut`, which walks, is for removal alone.
- `catalogue::render` writes a held catalogue's lines beside the entries
  added to it, so a catalogue taken from `cache/` can be written back.
- The record above: 23 ms at the first revision, 33 ms at the
  two-thousandth, against 38 ms and 115 ms.
- Two tests hold it, in `tests/filesystem.rs`: a record into a store whose
  catalogue is current lists nothing under `operations/`, nor does the next
  reader; and bytes the catalogue does not name are filed a second time and
  `check` notes them and nothing worse.
