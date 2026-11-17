---
title: A copy can start from a file's state
description: "A state document says what a file holds at a revision, every line under the name it already has, and is derived: anyone holding the file's chain writes the same bytes, and anyone holding it can check them. A copy that takes the revisions and a state per file opens at once, records and merges as a whole copy does, and fetches a chain only for what reaches back past it — 0007's re-rooting, without a second kind of history"
status: draft
created: 2026-11-17
updated: 2026-11-17
part_of: '[Proposals](/docs/proposals/proposals.md)'
---

# A copy can start from a file's state

## Status

**Draft, 2026-11-17, and not the first thing to build.** Argued from
historica at `932279e`, and from a measurement of what Diaryx Cloud sends a
new device, taken in diaryx with `online/tests/history_weight.rs`. Nothing
is built.

The measurement says most of what a new device waits for today is not depth
of history but number of revisions: Diaryx records every thirty seconds
while a person types, and the same year of writing recorded once per sitting
sends a quarter of the bytes and a tenth of the revisions. That is Diaryx's to
fix, and needs nothing from historica. What is left after it — a download
that is twice the folder after a year and grows with every year after — is
what this proposal is for, and it should be measured again on a library that
old before it is built.

It reopens the question [0007](/docs/decisions/0007-content-and-merge.md)
deferred, *whether a re-rooting revision should exist*, and which
[0028](/docs/decisions/0028-accepting-by-path.md) kept deferred "until
Historica has a transport boundary and a concrete shallow-history operation".
Diaryx Cloud is that boundary: a library's store, sealed, in a bucket, taken
whole by every device that opens it.

## The ask

A person signs in to Diaryx on a new phone, or in a browser, and their
library should be there to read. Today it is there once every revision and
every operation document it was ever sent has come down and been replayed,
because the folder is written from the store and the store cannot be partly
there. The photographs no longer wait (bytes held elsewhere, in Diaryx's
own sync); the words still do, and the words are the cheap part: the folder
is a fraction of the history that makes it.

## What it costs today

Measured in diaryx at `2e3f50e`, release build, over a server made of a map
(`online/tests/history_weight.rs`). A library is written as the app writes
one: a page a day of twelve sentences, an older page touched every seventh
day, and a sync, which records, after each sentence (the app's thirty
seconds) or once a sitting. *Download* is the sealed packs a second device
fetches before its folder can be written; nothing in it is compressed.

| Library | Revisions | Folder | Download | Packs | One sync, at the end |
|---|---|---|---|---|---|
| 90 days, a sync a sentence | 1,092 | 133 KiB | 674 KiB, 5.1× | 1,092 | 326 ms |
| 90 days, a sync a sitting | 102 | 133 KiB | 160 KiB, 1.2× | 102 | 18 ms |
| 365 days, a sync a sitting | 417 | 532 KiB | 1,096 KiB, 2.1× | 417 | 171 ms |

The year at a sync a sentence was not finished: a sync took 41, 143 and
326 ms at days 30, 60 and 90 with the history cache diaryx keeps (98, 366
and 817 ms without), which is the square of the library's age, and puts a
sync a few seconds long by the end of the year.

Three things follow:

1. **The revisions are the cost, before the history is.** The same text in a
   tenth of the revisions is a quarter of the download and an eighteenth of
   the sync. Diaryx can fold a sitting's recordings into one revision before
   it leaves the device (an unpushed run may be rewritten freely), which
   needs nothing here.
2. **What is left still grows.** Folded, a year is a download of twice the
   folder, and every year adds a year of operation documents to it while the
   folder grows by a year of pages. A page revisited often costs its whole
   chain. That is what a state ends.
3. **A record's cost grows with the history**, folded or not: 171 ms at 417
   revisions. That is not this proposal's question, and is a task of its own
   (*Open questions*, 3).

## What is here already

- **A line's name is derived, never stored** (`src/merge.rs`). Item *i* of
  the document a revision stated a file in is named `(D, i)`. A merge
  resolution (`format.txt`, *a merge's file, stated whole*) already states a
  whole file as runs of those names, `keep <digest> <first> <count>`, and a
  kept line "survives under its own name, so a branch that edits it merges
  with it rather than colliding with a copy of it".
- **A merge needs the graph only back to where the branches part.** Eg-walker
  replays from the common ancestor; what came before it reaches the walk only
  as the list of lines visible there, under their names. Nothing older is
  consulted.
- **A copy may lack content and know it** ([0089](/docs/decisions/0089-history-held-elsewhere.md)).
  `fetch --history` takes the revisions and no content; a command that needs a
  file's chain fetches it from the copy it came from, and refuses offline,
  naming what it lacks. `check` reports what is missing as notes, and only
  `check --complete` fails on them.
- **Every stated file says what it comes to.** An operation document and a
  resolution carry `result <digest>`, so the text of a file at a revision can
  be checked against one small document, without its chain.

What 0017 refused, a `text` header on a file that already exists, it refused
because it "would give every line a new name". A state that keeps every
line's name is not that.

## The proposal

**A state document says what one file holds at one revision, each line under
its name.** It is a resolution's pieces with their text carried:

```
historica
state <file ID> <revision>
result <digest>

named 3eca7ea4…f51 0 2
+We took her out every morning that August,
+the summer of 1998, when the lake was still high.
named cbddb8c4…a502 0 1
+Dad repainted her that winter.
```

`named <document> <first> <count>` is `keep` followed by the lines it keeps;
assembling the `+` lines is the file. Pieces are maximal, as a resolution's
are, so one state has one spelling, and a state document is named by its
digest like everything else in `operations/`.

**It is derived, and anyone can check it.** It is worked out from the file's
chain, and anyone holding the chain writes the same bytes. It is not named by
any revision and changes nothing in the graph: deleting every state document
loses no information and no meaning, the condition the README sets for a
cache. Its text is checked against the `result` of the document the revision
states the file in. Its names are checked when the chain arrives.

**`fetch --from <revision>` takes the revisions, and a state for every file
at that revision.** No operation document and no payload of lines older than
it. The copy is *started* at that revision for those files, and says so in
its own state, beside 0089's note of where the rest can be fetched.

**A started copy works as a whole copy does, from where it started:**

- `cat`, `status` and `update` at the start and after it read the state, and
  the operation documents recorded since.
- `record` diffs against the state. What it writes is an ordinary operation
  document, counted into the state's lines.
- A merge whose branches part at or after the start replays from there, with
  each line's name taken from the state. It writes the bytes a whole copy
  writes.
- `blame` needs nothing more: a line's name already says which document, and
  so which revision, wrote it.

**What reaches back past the start fetches the chain, as 0089 does:** a file
at an earlier revision, a diff across the start, a merge whose branches part
before it. Offline, it refuses, naming what it lacks. `check --complete` fails
on a started copy, correctly: it is not whole.

## Why not a re-rooting revision

0007's shape was a revision that states content outright, so a history could
be cut. That changes the graph: two copies of one history disagree about
where it begins, a re-rooted copy cannot merge with work that parted before
the root at all, and the format gains, as 0007 put it, "a second,
snapshot-shaped thing in a format that just argued for one shape".

A state document is in the format and not in the history. The graph stays
whole on every copy, so nothing is cut and nothing disagrees; what a started
copy lacks is content, which 0089 already taught a copy to lack and fetch.

## Costs

- **A started copy still takes every revision.** Under this proposal the
  graph travels whole, as 0089's does. Folded, a year's revisions were
  187 KiB of the store, so a started copy of that library would fetch about
  three quarters of what a whole one does: the saving is in operation
  documents, and it is small for a young library and grows with its age.
  A copy that also leaves old revisions behind is the re-rooting this
  argues against, and would have to be argued for on its own.
- **A sender must hold the chain to write a state**, and a copy started from a
  state cannot write one for a revision before its start. A device that
  publishes states is a whole copy.
- **A wrong name is not caught until the chain arrives.** The text is checked
  against `result`; a name is only as good as whoever wrote the state, and a
  wrong one makes a merge across it differ from a whole copy's. Between a
  person's own devices, sealed under one key, that is the trust the packs
  already ask for. Anywhere else, `check` with the chains is the answer, and a
  source historica does not trust should not be started from.
- **A transport has to carry the graph and the content apart.** Diaryx's packs
  hold one push's revisions and operation documents together, so a started
  copy would need them packed separately, or a pack per kind.
- **The format gains a document kind**, which 0004's strict reader refuses
  until it is taught it.

## Open questions

1. **Where a state is filed.** `operations/`, named by its digest, is the
   proposal; it is found by the file and revision it names, which nothing
   else in `operations/` needs, so a copy keeps an index of them beside 0089's
   note of where the rest is.
2. **Whether a state should also cover a merge's settling**, so that a merge
   whose branches part at the start needs nothing from before it. The walk
   needs the lines visible at the common ancestor, under their names, and a
   state is exactly that; a settled resolution may need more.
3. **A record's cost grows with the history.** Measured above: 171 ms at 417
   revisions, and growing with the square of the library's age. 0049 deferred
   opening a store without reading every revision; this is the measurement
   that brings that question back, separately from this one.
