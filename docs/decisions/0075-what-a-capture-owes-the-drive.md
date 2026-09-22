# 0075 — What a capture owes the drive

> **Amended 2026-09-17.** The shape the *Deferred* section below asked for
> is what stands: `fs-transaction` 0.3.0 offers *handed over* as
> `Durability::Pushed`, `Filesystem` gained
> [`barrier`](../../src/fs.rs) to say where a set ends, and
> `Store::insert_at` issues it once before every revision. Content is pushed
> per file and barriered once per set, and the first capture of 2,000 files
> is 0.4 s where this decision left it at 1.0–1.6 s. *What a crash can leave*
> is amended in place, because "at most one torn document" was a property
> of the barrier per file and goes with it. The task was
> [`docs/tasks/closed/a-capture-pushes-per-file-and-barriers-once.md`](../tasks/a-capture-pushes-per-file-and-barriers-once.md).

A first capture of 2,000 small files took 13 s on the reference machine, and
0.07 s of that was the process working. The rest was the process waiting for
the drive: `Disk::write_in_pieces`, the write every recorded payload lands
through since [0067](0067-content-that-arrives-whole-is-named-not-carried.md),
asked for two drains of the drive's write cache per file — `File::sync_all`
on the staged bytes and again on the directory, which on Apple platforms is
`F_FULLFSYNC` twice, at 3.5 ms each. Measured directly, the sequence it
performed costs 6.4 ms per file, which is the 6.5 ms per file `record` was
observed to cost. Nothing else in the capture is on that scale.

It was the odd one out. `Disk::create_new`, which lands every document, has
asked for a *barrier* rather than a drain since the change that gave it any
flush at all: `F_BARRIERFSYNC` on the file and on the directory, ordering
the write against everything after it without waiting for the drive to
empty. `Disk::write`, which lands the mutable files — a bookmark, the marker
— drains, and is the one write that should. `write_in_pieces` had been
written by hand because a stream cannot go through `fs-transaction`'s slice
API, and by hand it reached for the only flush the standard library offers,
which is the strong one.

This decision states what each write in a capture owes the drive, so that
the next hand-written write asks for the right thing, and records what the
per-file drain was buying, which is nothing the store needed.

## Three strengths

A write can be asked for three things, and the crate's filesystem layer
(`fs-transaction`) names two of them:

- **Ordered.** Everything written before this lands before anything written
  after it. Nothing is promised about *when*: a crash can lose the lot, but
  never a suffix without its prefix. `F_BARRIERFSYNC` on Apple, a queue
  barrier the device honours; plain `fsync` elsewhere, which is stronger than
  asked.
- **Durable.** When the call returns, the bytes survive a power cut — and,
  because a barrier is device-wide, so does everything ordered before them.
  `F_FULLFSYNC` on Apple. This is the drain, and it is what costs
  milliseconds.

The third is below both: **handed over**, the bytes pushed from the page
cache to the device and ordered against nothing. `fsync(2)` on Apple. It
costs about what the write itself costs. `fs-transaction` did not offer it
when this was written, and the deferred section below is about that; it
does now, as `Durability::Pushed`, and the amendment above is what changed.

## What a capture writes, and what each write owes

A record writes, in this order: every payload and operation document the
revision will name ([0011](0011-working-copy.md) and [0017](0017-content-that-arrives-whole.md)
chose content first); the revision document; and then, where a bookmark
followed the parent, the bookmark. The content is content-addressed and
append-only, and the store already reads a folder holding content nothing
names — an interrupted transfer leaves exactly that, and `check` calls it a
note. What the content cannot tolerate is a *name* that survived a crash the
bytes did not: a revision naming a payload that is not there.

So:

- **Content owes order.** A payload or an operation document must land
  ahead of the revision that names it. As first written, each was
  barriered on its own — its bytes ahead of the entry that publishes it,
  the entry ahead of whatever is written next, `Ordered` on the file and on
  the directory, from `create_new` and `write_in_pieces` alike. As amended,
  each is *handed over* — `Pushed` on the file and on the directory — and
  the order is bought once for all of them, by the barrier below.
- **The revision owes order, and the set owes one barrier.** `Store::insert_at`
  is the one door a revision goes through, and every writer lands content
  first; so it calls `Filesystem::barrier` on the store's root, once, and
  everything handed over since the last barrier lands before the revision
  does. A barrier speaks only for what has reached the device, which is why
  every file is pushed first and why no push can be skipped.
- **The bookmark owes durability.** `write` drains, and the drain carries
  everything barriered before it: when a bookmark moves, the capture it
  points at is on the platter. This was already the whole of the crate's
  durability promise; it is now stated rather than implied.

Nothing in a capture drains except the naming write. On the reference
machine that takes the first capture of 2,000 files from 13 s to 1.0–1.6 s,
of which 0.45 s is the process working; a capture of 2,000 edits, which
never paid the drain, is 1.0 s either way. `cargo xtask bench` now times
both shapes on its way to building the store, so the number stays honest.
With the pushes and one barrier, the first capture is 0.4 s and the edits
are the same.

## What a crash can leave

Because every set is ordered ahead of the revision that names it, a power
cut leaves **some prefix of the sequence of sets, in the order it was
written** — with the interrupted set possibly partial — and each prefix is
a state the store reads:

- **Content, and no revision.** Payloads and operation documents nothing
  names. `check` reports each payload as a note (`UnnamedPayload`) and
  says nothing of a document, which `prune` removes as it removes any
  unreached document; the next capture of the same folder names them
  rather than writing them again. `tests/store.rs` stages this one and
  holds `check` to it.
- **Content and the revision, and no bookmark.** A revision no bookmark
  points at, which is what a record onto a fresh store leaves *on purpose*
  — it moves no bookmark — and which `log` shows and `check` accepts.
- **All of it.** The ordinary case.

A file can be in a worse state than absent, and as amended **any number of
the interrupted set's files can be**, independently, because nothing orders
the files of one set against each other — that is exactly what the pushes
do not buy, and the barrier per file used to:

- A **streamed payload** is staged beside its destination and renamed over
  it, so no *reader* ever meets a torn destination. What a crash usually
  leaves is the staging file — dot-prefixed, suffixed `.partial`, in
  `operations/` where everything that is not a document is a payload — and
  `check` reports it as a payload nothing names; 0067 says this already.
  What a crash can now also leave is the rename landed and the bytes not,
  since the push before the rename orders nothing: a payload under its
  final name whose bytes are not all there.
- A **document** through `create_new` is written under its final name,
  because the exclusive create *is* the concurrency story
  ([0003](0003-store.md)), and a crash mid-write can leave it torn.

Either way its name promises a digest its bytes do not have, `check`
reports that as an error naming the file, and the remedy is deleting it —
the next capture of the same folder writes it again. As first written, with
a barrier per file, at most one document was in that state: the writes
before it landed whole, the writes after it did not start. That property
went with the barriers, and the trade is the one the task made: the
`check` finding and the remedy are the same, and there may be more than one
of each. The drain never protected against a torn file either, since a torn
file is torn before any flush.

## What `record` returning promises

That the store is consistent whenever the cut comes — and not that the
capture survives a cut in the next moments. A record that moves a bookmark
ends with a drain and is durable when it returns. A record that moves none —
the first capture into a fresh store is one — ends with a barrier, and the
tail is the operating system's to flush, which it does within seconds. The
command-line front end happens to write `cache/working.txt` through `write`
after every record, which drains; that is a cache's write asking for more
than a cache needs, and not a promise. This was already true of every
document before this decision, since `create_new` never drained; what
changed is that payloads now keep the same promise as the documents that
name them, rather than a stronger one nothing could cash.

## Refused

- **A drain per payload**, which is what stood. It bought durability for
  bytes that would be named by a revision that was not itself durable, and
  it cost 6 ms per file. The task that measured it is
  [`docs/tasks/closed/first-capture-is-barrier-bound.md`](../tasks/first-capture-is-barrier-bound.md).
- **No flush per file, and one barrier for the set.** The task proposed
  this, and it is unsound as stated: a barrier is issued on one file and
  pushes that file's bytes to the device — other files' bytes stay in the
  page cache, and a barrier orders nothing it has not pushed. Every file
  has to be handed over before a barrier can speak for it, so the floor is
  one push per file, not none.

## Deferred

**Handed over per file, one barrier per set.** *Done, as the amendment at
the top says; the argument is left as it was made.* The right shape, and
the one the refused proposal was reaching for — filed as
[`docs/tasks/closed/a-capture-pushes-per-file-and-barriers-once.md`](../tasks/a-capture-pushes-per-file-and-barriers-once.md),
with fs-transaction's half as a task there: `fsync(2)` on each file and each
directory as it lands (0.14 ms per file, measured, against 0.44 ms for the
barrier pair), then one barrier before the revision document, then the
naming write's drain. Two things stand in the way, and neither is this
crate's alone:

- `fs-transaction` has no strength below `Ordered`. A `Durability` variant
  for *handed over* is a change to a public enum that every `match` on it
  would feel, and its `OrderedBatch` could use the same strength within a
  tier — every file handed over, the last one barriered — which is the
  saving for every consumer and not only this one.
- `Filesystem` would need to say where a set ends. The store knows —
  `Store::insert_at` is the one door a revision goes through, and every
  caller that writes content writes it first — but the trait has no method
  for it, and one with a do-nothing default is the shape
  [0043](0043-what-a-command-does-not-have-to-read.md) gave a capability an
  implementation may decline.

It would also change what a crash can leave: with no barrier between files,
any number of documents in the interrupted tail could be torn, not one.
`check` would report each; a person would delete each. Worth it at 20,000
files, where the barrier pair is 9 s and the push would be 3 s; not worth a
`fs-transaction` release to save 0.6 s at 2,000.

## Open questions

1. **Whether a record should end with a drain of its own.** One
   `F_FULLFSYNC` per command is 4 ms, and it would make "record returned"
   mean "the capture is on the platter" whether or not a bookmark moved.
   `Filesystem` cannot express it today for the same reason the set
   boundary above cannot: the trait does not know which write is the last.
2. **Whether a document should be staged and renamed, as a payload is**, so
   that a crash never leaves one torn. `std::fs::hard_link` from the
   staging file to the final name fails where the name is taken, which
   keeps the exclusive create; the cost is a second directory entry per
   document, briefly.
