---
title: The first capture is barrier-bound
description: Recording a folder into a fresh store costs ~8 ms per file, spent blocked on the device rather than computing — the per-file durability barrier, not the survey
status: open
created: 2026-09-02
updated: 2026-09-02
part_of: "[Tasks](tasks.md)"
---

# The first capture is barrier-bound

`record` into a fresh store costs about **8 ms per file**, and almost all of it
is spent waiting on the storage device. A folder of 2,000 small files takes
**16 s**; a real archive of 20,000 takes minutes. It is the first thing anyone
does with historica, and it is the slowest thing historica does.

The survey is not the problem and neither is the CPU. What costs the time is
that the write phase asks the device for a durability barrier **per file**,
where the store's own design only needs one for the whole capture.

## Reproduce

```sh
N=2000; D=/tmp/hb; rm -rf $D; mkdir -p $D/notes
python3 -c "
for i in range($N): open(f'$D/notes/n{i:05}.md','w').write(f'# Note {i}\n\nbody {i}\n')"
historica init $D
time historica -C $D record -m first
```

All numbers below are from an Apple M3 Pro on APFS (macOS 26.6), historica
1.0.0-rc.1 built `--release`. The shape should hold anywhere `fsync` is honest;
the constant will not.

`cargo xtask bench` is no help here as it stands: it builds a store to order and
then times the **reading** commands against it, so the recording it does is
setup rather than subject. Giving it a recording shape would be a reasonable
first commit on this task, and would keep the number honest afterwards.

## What is known

**It is linear, not quadratic.** 250 / 500 / 1,000 / 2,000 files take 2.10 s /
4.11 s / 8.40 s / 16.13 s — a flat 8.2 ms per file. So this is a per-file
constant to remove, not an algorithm to rewrite.

**It is not the survey.** `record --dry-run` over the same 2,000 files is
**0.06 s** against **15.66 s** for the real thing. Everything is in the write
phase, which lands 2,006 files and 8.3 MB.

**It is not the CPU.** `/usr/bin/time -l` reports **15.21 s real, 0.07 s user,
1.95 s sys**. Roughly 13 s is the process blocked, not working.

**What the flush primitives cost here**, measured directly — 2,000 files,
create + write 200 bytes, one call each, via `fcntl`:

| per file | ms |
|---|---|
| no flush | 0.07 |
| `fsync(2)` | 0.08 |
| `F_BARRIERFSYNC` | 0.58 |
| `F_FULLFSYNC` (Rust's `File::sync_all`) | 3.59 |

The observed 8 ms/file is about two full drains' worth, so the write path is
paying something close to `F_FULLFSYNC` twice for every file it records.

## What has already been ruled out

**It is not simply `write_in_pieces`'s two flushes.** That path
(`src/fs.rs`, `Disk::write_in_pieces`) is the one write in the crate that
ignores its `Durability` argument and calls `sync_all()` on the staged file and
again on its parent directory — two `F_FULLFSYNC` per payload, which matches the
8 ms exactly. It is the path every recorded file's content takes
(`src/store/mod.rs` → `fs::write_from_pieces`). It is still worth fixing, but it
is not the whole cost: **deleting both flushes moved 16.13 s to 13.63 s**, a
saving of 2.5 s where the microbenchmark predicts 14 s.

The lesson for whoever picks this up: **these costs do not add.** A device with
a flush already pending answers the next one cheaply, so removing one barrier
point mostly shifts the wait to the next one. Attributing the time by deleting
one call at a time will mislead you. Count the barrier points first — or trace
them with `fs_usage` / `dtrace` — and then remove them as a set.

**It is not a missing `barrier-fsync`.** historica already declares
`fs-transaction = { version = "0.2", features = ["barrier-fsync"] }`, and
`cargo tree -e features -i fs-transaction` confirms the feature is active in the
built binary, so `Durability::Ordered` really is `F_BARRIERFSYNC` and not the
drain. Two of those per file would be 2.3 s, and we are looking at ~13 s.

## Where to look

Count every flush and barrier the record loop performs **per recorded file**,
rather than per capture. The known points are `write_in_pieces`'s two `sync_all`
above, and `Disk::create_new`, which lands each document as an `OrderedBatch`
with `Durability::Ordered` — barriering the file *and every directory that
gained an entry*, freshly minted parents included.

The fix the design already half-describes is to stop barriering per file at all.
`Disk::create_new`'s own comment argues that nothing there drains the drive
because "what turns the barriers durable is the next mutable write" — the
bookmark or marker that *names* the new revision, landing through `write`'s
durable flush, which carries everything ordered before it. The same argument
retires the per-file barrier: write every payload and document with no flush,
issue **one** barrier once the whole set is on disk, then let the naming write
be the drain. What a crash mid-`record` then leaves behind is content-addressed
files that nothing names — which is the state the store is built to tolerate,
and which an interrupted `record` can already leave today.

That argument is the work, not the speedup.
[0026 — A mutable file changes all at once](../decisions/0026-atomic-mutable-files.md)
and [0067 — Content that arrives whole is named, not carried](../decisions/0067-content-that-arrives-whole-is-named-not-carried.md)
are the ones to read before arguing with it.

## Done when

- A first capture of 2,000 files is CPU-bound rather than blocked — on the
  reference machine, wall time within a small factor of the 2.0 s of CPU it
  already spends, instead of 15 s.
- The crash-safety argument is written down: what a power cut during `record`
  can leave, and why the store still reads it. If that changes what the
  decisions say, the decision is amended in the same change.
- `check` still passes on a store built by the new path, and the existing
  durability tests still hold — with a test that a store interrupted mid-capture
  is one `check` accepts, if there is not one already.
- If any of it is observable to a caller, the commit carries a
  `Behavioural-change:` trailer.

Consumers feel this directly: diaryx takes a capture before every delete and one
when a vault starts keeping history, and the first capture on an existing vault
is the moment a person waits through.
