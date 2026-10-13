---
title: A stand-in filed beside another copy
description: Decision 0079's look beside a payload finds a stand-in where the replica that forgot it filed it, but the same bytes filed by two revisions sit at two paths, so a replica holding them at the other keeps handing a forgotten photograph over through its cache
status: open
created: 2026-10-13
updated: 2026-10-13
part_of: '[Tasks](/docs/tasks/tasks.md)'
---

# A stand-in filed beside another copy

[0079](/docs/decisions/0079-a-reader-looks-where-forget-files.md) closed the
window [0078](/docs/decisions/0078-where-a-cache-is-kept.md) found, for a
payload, by looking beside it: `forget` files a payload's stand-in at the
payload's path with `.ops.txt` after it, a sync copies paths, so "on the
receiving side each lands where the writer put it", and a reader that finds
the bytes looks at that one path before handing them over.

That holds where every replica holds a payload at one path. It does not
hold in general, because a payload is filed under the revision that
recorded it, and one set of bytes can be recorded by more than one revision:
re-recorded after a `prune` took the first, or recorded on two replicas
that each put the same photograph in their folder. Each replica then holds
the bytes where *its* writer filed them, `forget` files the stand-in beside
its own copy, and a replica whose copy sits at the other path looks beside
that one, finds nothing, and — "a miss proves nothing" — hands the bytes
over. A store opened without a cache walks `operations/`, finds the
stand-in, and says the photograph is forgotten.

Found by `tests/simulation.rs`, whose cached and fresh readings of one
replica disagreed.

## Repro

Replica A records a photograph, B is a copy of A. On A: `abandon` the
revision that recorded it, `prune`, and `record` again with the folder
unchanged, which files the same bytes under the new revision's folder. Sync
A to B, then on A `forget head photo.bin`, and sync A to B again — B now
holds:

```text
operations/2026-01/2026-01-01 root 0/photo.bin              the bytes
operations/2026-01/2026-01-01 work 3/photo.bin              the bytes
operations/2026-01/2026-01-01 work 3/photo.bin.ops.txt      forgets them
```

A reader on B whose catalogue places the digest at `root 0/photo.bin` hands
the photograph over; `Store::open_on`, which keeps no catalogue, does not.
`a_stand_in_beside_one_copy_is_read_beside_every_other` in
`tests/simulation.rs` is this round, pinned and ignored:

```console
$ cargo test --test simulation a_stand_in -- --ignored
after step 4, Sync { from: 0, to: 1, … }: replica 1: the cached store and a fresh one disagree
```

## Candidates

- **File the stand-in at the top of `operations/` too**, under its digest,
  where 0079's first rule already has every reader list before it believes a
  catalogue. Every layout then has one place a payload's stand-in is certain
  to be, whatever path the bytes are at. Two copies of one document are
  harmless by [0003](/docs/decisions/0003-store.md).
- **Look beside every path the catalogue knows the digest at**, rather than
  the one it chose. Cheaper on disk, and still a window for a path the
  catalogue never learned.
- **Have `forget` destroy every copy and file beside each**, which only
  helps on the replica that forgets.

## Done when

A cached reader and a fresh one agree on such a store, the pinned test runs
unignored, the simulation's `beside_elsewhere` is deleted, and `HISTORICA_SIMULATION_STRICT=1 cargo
xtask soak` passes.
