---
title: The web source asks for one file at a time
part_of: '[Tasks](/docs/tasks/tasks.md)'
status: open
created: 2026-10-21
updated: 2026-10-21
description: The CLI's HTTP source does not implement Source::prefetch, so a fetch's small files are fetched one round trip after another — a minute and a half to take historica-git from the hub
---

# The web source asks for one file at a time

`Source::prefetch` (`src/store/fetch.rs`) exists for exactly this. A fetch
offers every small file its plan names to the source before asking for any of
them, so that "a source whose every answer is a round trip … can start all of
them here and hand each back from memory when it is asked." The CLI's HTTP
source, `Web` in `cli/src/cli/fetch.rs`, implements only `get`. It keeps the
default `prefetch`, which does nothing, so every revision and every operation
document is one request after the last.

## Repro

historica-git's repository on the hub, 2026-10-21: 54 revisions, 167
operation documents and 71 payloads.

```console
$ historica init && time historica fetch https://historica-hub.harrisadam42103.workers.dev/adam/historica-git/offer.txt
fetched 54 revisions
fetched 167 content documents
fetched 71 payloads
…
real 98.01
```

Three first fetches that day took 84, 86 and 98 seconds, which is about a
third of a second for each of about 300 files. A fetch with nothing new took
under a second, and a fetch of one new revision 3.4 seconds. The cost is the
number of files, in a row, and it grows with the history.

## The work

- **`Web::prefetch` starts the requests together and keeps the answers**, and
  `get` hands back a kept answer where there is one, and asks as it does
  today where there is not. `get` stays the answer, as the trait says, so a
  prefetch that failed or was never made changes nothing but the time.
- **A bound on requests in flight.** nyquest's client is blocking, so this is
  a few threads, not an executor, and the number is small enough not to look
  like abuse to a static host. Payloads stay out, as the trait says: they
  stream a piece at a time under 0067.
- **Memory.** The small files of a plan are held until asked for. For this
  store that is about 1.5 MB. A plan large enough for that to matter should
  be prefetched in pieces, in plan order.
- **A 404 or 410 under prefetch** is kept as an answer like any other, so
  0048's reading of the manifest again still happens when `get` reaches it.

## Done when

- A first fetch of historica-git from the hub takes seconds, not a minute
  and a half, and `requests` in the fetch's report is unchanged.
- `cli/tests/fetch.rs` passes unchanged, and a test against a source that
  counts what is in flight shows the small files overlapping.
