# 0049 — What a lookup does not prove

0036 gave the store a catalogue and one condition for believing it:

> the set of paths it names is the set the directory now holds

That condition is a directory walk, and every content command paid for it.
At twenty files over eighteen hundred revisions — thirty-six thousand files
in `operations/` — `cat` at the head cost 405ms, of which the answer itself
was a handful of milliseconds: 52ms to open the store, about 50ms to walk
the directory the catalogue was being checked against, and the rest to parse
thirty-six thousand catalogue lines into a map so that one of them could be
read.

Both of those are the cost of proving something a lookup does not need
proved. The catalogue's claim is *where a digest is*, and 0036 already says
what happens to that claim when it is used: the reader goes to the path,
reads it, and hashes it before believing a byte. A catalogue that is wrong
about where a digest is cannot make a reader believe the wrong bytes — it can
only fail to find them, and a lookup that fails already falls back to the
directory. The walk is not what makes a *hit* safe. It is what makes a *miss*
mean something.

## The decision

- **A reader takes the catalogue without walking the directory.** Where the
  file in `cache/` places a digest, that is where the reader looks, and the
  hash is what decides whether it found it. Nothing about what a reader
  believes has changed; what has changed is what it pays to find out.

- **An absence still costs the pass.** *Not here* is a claim about every file
  in the directory, and no hash can check it. So a lookup that misses walks —
  reading only the files `cache/` cannot account for, which is 0036's pass
  unchanged — and only then reads every document, which is what it did before.
  Three questions are absences in this sense and take the same route: a digest
  that places nowhere, what the whole of the directory holds
  (`Store::payloads`), and whether anything forgets a digest whose own bytes
  are gone.

- **A writer walks.** What a writer asks is whether the store already holds
  these bytes, so that one document is not written twice under two names.
  That is an absence too, and answering it from a catalogue that has not seen
  the last three documents would file a second copy of each. Once per command,
  not once per document.

- **Holding the bytes is the answer to whether they were redacted.** 0014
  destroys the original when a forgetting document is complied with —
  `forget` deletes it, `receive` complies before it writes. So a reader that
  has the original's bytes, hashed to the digest it asked for, has a store
  that has complied with nothing about them, and it does not walk the
  directory to be told so. A store holding an original *beside* a document
  that forgets it is the state `check` already reports as `Resurrected`, and
  `check` takes no cached answer of any kind.

- **The held catalogue is searched, not parsed.** It is written in digest
  order, so a reader takes its bytes, notes where each line starts, and finds
  the one it wants by looking. Only that line is parsed. A file that is not
  in digest order is not searchable and is dropped, which costs the pass —
  the same thing every other way of being wrong costs.

## What this does not change

Every rule 0036 states about what may be believed. The catalogue still says
where to look and never what is there; a lookup still hashes what it finds; a
catalogue that is missing, stale, truncated or lying still costs time and
never an answer. `check` still builds its own by reading. What is different
is that the proof has moved to where the doubt is: a hit proves itself, and
only a miss has to be paid for.

## Consequences

On that store: `cat` 405ms to 79ms, `status` 335ms to 150ms, `log`
unchanged at 99ms — it asks the graph and never reaches here. The first read
after a write is unchanged, because it is a miss and always was.

`Catalogue::at` returns an owned `Located` rather than a borrow, since what a
held catalogue holds is text. `Catalogue::iter` is asked only of a catalogue a
pass built, and says so with an assertion rather than a comment.

## Deferred

**`revisions/` still has no catalogue.** Opening a store reads and parses
every revision document — 52ms of the numbers above, and the floor under
every command including `log`. Measured against the directory, that is close
to what merely reading those files costs, so the parser is not what to fix:
the only way past it is to not open the files, and that needs a catalogue
trusted for something no hash can check. A catalogue cannot *hide* a revision
— an unaccounted path is read — but one that names every path and lies about
a `parent` line changes which revisions are heads, and a reader has no way to
notice. 0044's witness is the nearest precedent for a cache producing a
judgement rather than a byte, and it is deliberately narrower than this would
be. Not attempted here.
