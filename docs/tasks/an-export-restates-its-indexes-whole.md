---
title: An export restates its indexes whole
description: One snapshot of a one-file change adds two content files to a published copy and rewrites three files that grow with the history — the offer and the two catalogues under `cache/` — so a consumer that ships a copy one remote object per file pays for the history on every publish
status: open
created: 2026-09-23
updated: 2026-09-23
part_of: "[Tasks](tasks.md)"
---

# An export restates its indexes whole

A snapshot is inherently two new files: the revision document, and the one
file in `operations/` that says what it did to the file that changed. Both
are named by their own digest, both are immutable, and nothing that already
existed has to change for them to be written. What a *publish* of that
snapshot changes is larger, and the difference is not content. It is three
files that describe the store rather than hold it, each re-emitted in full,
each one line longer than last time, and each of which a consumer shipping
the copy file-per-object uploads again.

## The measurement

A scratch store built with the CLI: five tracked files, a revision that
appends one line to one of them each time, and a new file every eighth
revision. It was exported once and offered (`historica export pub/store`,
then `historica offer store > offer.txt` inside `pub/`), then given one
snapshot — a new 17-byte file, `record` — and exported onto the same copy and
offered again. The same was done at 40 and at 400 revisions; the same files
change at both lengths, and the sizes are the point.

What the **published directory** (the copy and the offer beside it) gained or
lost, by `shasum` before and after:

| file | what happened | 40 revisions | 400 revisions |
|---|---|---|---|
| `history/revisions/….rev.txt` | added, digest-named | 328 B | 328 B |
| `history/operations/…/added.md` (an `.ops.txt` for an edit) | added, digest-named | 17 B | 17 B |
| `offer.txt` | rewritten whole | 12.7 KB, 93 lines | 120 KB, 858 lines |
| `history/cache/revisions.txt` | rewritten whole | 18.4 KB | 176 KB |
| `history/cache/operations.txt` | rewritten whole | 6.0 KB | 55 KB |
| `history/cache/<digest>` | added, 0–5 per run | under 100 B each | up to 482 B each |
| the folder's copy of the file | added, or rewritten for an edit | 17 B | 17 B |

Seven files for a change of one, and three of them are whole-file rewrites
whose size is a function of the history rather than of the change. An edit
of one line rather than an added file moved the same set with a different
number of state entries under `cache/` — none at 40 revisions, five at 400 —
so six to ten files in all.

The **live store** behaves the same way on its own side. `record` adds the
revision and the content file, may add a state entry under `cache/`, and
rewrites `cache/working.txt` (1.1 KB and 5.5 KB here, one line per tracked
path, so it grows with the folder and not the history). `cache/revisions.txt`
and `cache/operations.txt` are not written by `record` —
[0036](../decisions/0036-where-a-digest-is.md) and
[0058](../decisions/0058-what-a-command-does-not-have-to-open.md) have them
kept up to date by the next command that reads them — so the whole-file
rewrite of each lands one command later, once per snapshot all the same. The
state entries accumulate: 184 of them after 400 revisions.

What a **fetcher** asks for, over HTTP against the published directory, from
a store that was current before the snapshot: three requests — `offer.txt`,
whole, then the revision and the content file. `Store::fetch` reads the offer,
takes the set difference, hands `Source::prefetch` the revision and document
paths (payloads are left out of the hint, per
[0067](../decisions/0067-content-that-arrives-whole-is-named-not-carried.md)),
and asks for each. The count is already the minimum for the files; the bytes
are not, because the listing is read in full, and it is about 140 bytes per
file the store holds — every revision, every operation document and payload,
every travelling rule, bookmark and reserved file.

So, by kind:

- **One per snapshot, inherently**: the revision, the content document or
  payload per file changed, and the folder's copy of that file. A tool that
  writes one claim per revision under `claims/` adds a file of its own, which
  is digest-named and in the same class.
- **Rewritten whole, and growing with the history**: `offer.txt`,
  `cache/revisions.txt`, `cache/operations.txt`.
- **Rewritten whole, growing with the folder**: `cache/working.txt`, in the
  live store only.
- **New and derived**: state entries under `cache/`, which are digest-named
  and never rewritten, but which nothing removes.

## Why it matters

A consumer that ships a store to a remote as one object per file pays a round
trip and a record per object on the way up, and a fetcher pays one per object
on the way down. For such a consumer the count is the cost, and the size of
the rewritten files is paid again on every publish. A store synced often, in
small increments — the case a published copy that is updated in place
([0052](../decisions/0052-the-copy-a-stranger-fetches-from.md)) was built for
— is the case where the rewrites dominate: two files of content, and an
index of the whole history, three times over, to say so.

Two of the three are not supposed to travel at all.
[0042](../decisions/0042-a-copy-to-take-away.md) leaves `cache/` behind
because it is nobody's, and 0052 states that "`names/` and `cache/` are not
listed because an export has neither". The offer does not list them, so a
fetcher never asks for them. But the export *does* have a `cache/`: opening
the copy to update it and materialising its folder write the two catalogues
and the state entries into it, and the export module's own promise — that
`cache/` in the copy is "neither written nor removed" — is about what the
exporter does deliberately, not about what opening the copy does as a side
effect. A publisher who mirrors the exported directory to a static host, which
0042 names as the simplest host there is, uploads 231 KB of catalogue at 400
revisions to publish a 17-byte file.

The offer is the one whole-file rewrite that travels by design, and
[0056](../decisions/0056-listing-what-it-cannot-read.md) chose that shape on
purpose: a listing is a rendering, written nowhere in the store, refetchable,
and one request. It is linear in the store, and every fetch reads all of it
to learn about the last few lines.

## What could change

Four shapes, each with its cost. They are not exclusive, and this task does
not choose between them.

**An export leaves no `cache/` in the copy.** The copy is opened uncached —
the path `check` already takes — or what opening wrote is removed before the
export returns, so that 0052's sentence is a fact about the directory and a
mirror of it carries only what the offer lists plus the folder. Cheapest in
code, and it makes the published directory match the decisions. The cost is
the one 0036 and 0058 were written to remove: an export onto an existing copy
would read and hash every file in the copy's `operations/` and open every
revision document on every run, which is linear in the history on the
publisher's side instead of the wire's. Keeping the copy's catalogues
somewhere other than the copy — the origin's `cache/`, keyed by the copy's
path — avoids that, at the price of a cache that describes a different
directory than the one it sits in, believed on 0058's stamp rules.

**Say so, and change nothing.** `docs/cli.md`'s account of `offer` says that
a mirror of the published directory should exclude `history/cache/`, or that
the offer is the list to upload. No code, and no cost to anyone who reads
it; no help to anyone who does not, and the directory a static host serves
still holds files the decisions say are not there.

**An offer that is appended to rather than restated.** A small fixed-name tip
naming the heads and the newest page, and pages named by their digest, each
listing what one run added and naming the page before it. A fetcher that was
current reads the tip and one page; a cold one reads the chain, or a base page
that a run periodically compacts into. The cost is a second grammar — a new
header number, which [0047](../decisions/0047-one-spelling-for-the-format.md)
permits for an offer and not for a document — and a publisher that has to
remember what it listed last, which the previous offer beside the copy can
answer. It also has to carry what is not an addition: a forgetting document
changes the set without moving a head, and a withdrawal (a `forget`, a
`prune`, a target moving off a branch) removes lines, so a run that withdraws
anything has to issue a fresh base or state removals explicitly, and 0052's
rule that heads are not a currency check has to survive the paging.

**A run's small files batched into one object.** The files one export adds,
concatenated behind a table of offsets and digests, named by the digest of
the whole, and listed in the offer as one entry that names what it holds; a
fetcher that lacks any of them takes the batch and verifies each file inside
it as it does now. For a one-file change this takes the content from two
objects to one, and it saves more when a snapshot touches many files. The cost
is that a file a person could open becomes a file inside a batch: either the
published copy holds both — twice the bytes, and still readable — or it stops
being the readable store [0016](../decisions/0016-the-store-a-person-reads.md)
and [0021](../decisions/0021-the-store-explains-itself.md) promise. A
forgetting has to reissue every batch holding the destroyed bytes, and a
`Source` has no range request to take one file out of a batch instead.

## Done when

- A test publishes a store at two history lengths (40 and 400 revisions, as
  above), records a one-file change, exports onto the same copy and offers it
  again, and asserts two numbers: how many files in the published directory
  were added or rewritten, and how many bytes of listing a fetcher that was
  current before the change reads. Both are written here, before and after.
  Before, for the added file: seven files, three of them whole rewrites;
  12.7 KB of listing at 40 revisions and 120 KB at 400.
- No file under `history/cache/` in the published directory changes across
  that run, so the directory changes by the revision, the content file, the
  folder's copy of it, and the listing, at either length — or 0052's sentence
  is amended to say what an export's `cache/` holds and why it stays.
- The bytes of listing a current fetcher reads are within a constant of each
  other at 40 and at 400 revisions — or a decision records why the offer stays
  a single whole listing, naming the shapes above as the road not taken.
- `check`, `fetch` and `receive` behave identically on the copy either way,
  and the corpus passes.
