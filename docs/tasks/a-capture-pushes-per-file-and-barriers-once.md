---
title: A capture pushes per file and barriers once
description: Land each payload and document handed over rather than barriered, and issue one barrier before the revision document — 0075's deferred shape, once fs-transaction offers the strength
status: open
created: 2026-09-16
updated: 2026-09-16
part_of: "[Tasks](tasks.md)"
---

# A capture pushes per file and barriers once

[0075](../decisions/0075-what-a-capture-owes-the-drive.md) took the first
capture from 13 s to 1.0–1.6 s for 2,000 files by asking `Disk::write_in_pieces`
for the barrier pair `create_new` always asked for, instead of two drains. What
remains per file is that pair: `F_BARRIERFSYNC` on the file and on the
directory, 0.44 ms measured, against 0.14 ms for a plain `fsync(2)` on both.
For 2,000 files that is 0.6 s; for the 20,000-file archive the earlier task
cited, 9 s against 3 s, with the process's own work under a second.

The shape 0075 defers is: hand every payload and document over as it lands —
pushed to the device, ordered against nothing — and issue **one** barrier
before the revision document that names them, with the bookmark's durable
write still the drain. The barrier is what keeps 0011 and 0017's rule that a
revision never survives a crash its content did not; the pushes are what a
barrier needs in order to speak for files it was not issued on.

## What it needs, in order

1. **fs-transaction offers the strength.** `Durability` has no level below
   `Ordered`; `Filesystem` cannot ask for a push through it, and this crate
   forbids `unsafe`, so it cannot make the call itself. That is
   [fs-transaction's task](https://github.com/diaryx-org/fs-transaction/blob/main/docs/tasks/a-strength-below-ordered.md),
   a version Adam names, and a pin bumped here once it is published.
2. **`Filesystem` says where a set ends.** A method with a do-nothing default,
   on [0043](../decisions/0043-what-a-command-does-not-have-to-read.md)'s
   terms for a capability an implementation may decline: *everything written
   before this call lands before anything written after it*. The default is
   right for a filesystem whose every write is durable when it returns and
   for one that promises nothing about a crash, and wrong only for one whose
   writes reorder and which answers with nothing — which the docs have to say.
   It takes a path, because a barrier on Apple is issued on a handle, and the
   store's root is the natural one. The forwarding impls must forward it;
   the macro's comment says why a capability lost behind an `Arc` is worse
   than one never offered.
3. **`Store::insert_at` calls it** before `write_once`, since every writer —
   `record`, `carry`, `receive`, `fetch`, `export` — writes content first and
   the revision last, and `insert_at` is the one door a revision goes through.
   `Disk::create_new` and `Disk::write_in_pieces` then ask for the push
   rather than the pair.

## What it changes for a person

The crash state: with a barrier per file at most one document in the
interrupted tail is torn; with pushes and one barrier, any number may be.
`check` reports each as an error naming the file and the remedy is the same,
deleting it, but 0075's "at most one" goes, and the decision is amended in the
same change. That is a `Behavioural-change:` trailer.

## Done when

- `cargo xtask bench files=2000 revisions=1 lines=3` shows the first capture
  within a small factor of the process's own time — on the reference machine,
  under 0.8 s where 0075 left it at 1.0–1.6 s.
- `tests/store.rs`'s interrupted-capture test still holds, and the in-memory
  filesystem in `tests/filesystem.rs` takes the default and answers alike.
- 0075's "What a crash can leave" is amended, and the fs-transaction pin is
  the published version, not a path.
