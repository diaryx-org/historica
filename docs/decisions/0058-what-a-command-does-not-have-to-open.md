# 0058 — What a command does not have to open

0036 removed the cost of finding a digest in `operations/` and 0043 removed
the cost of taking one. Neither touched the directory every command reads
before it does anything at all.

`Store::open` walks `revisions/`, and for each file it finds it performs one
read and one parse. That is the whole of the graph — a revision document holds
the parents, the supersession, the author, the moment, the message and every
tree fact — so there is no command that does not pay it. `log` pays it,
`status` pays it, `cat` pays it, and `historica names` pays it in order to
print four lines.

The cost is one file open per revision, and on a store of six hundred
revisions holding 688 KB of documents it measures like this:

| what                          | warm    | cold     |
|-------------------------------|---------|----------|
| walking `revisions/`          | 0.9 ms  | 2.9 ms   |
| reading 601 files             | 8.7 ms  | 111.0 ms |
| reading one file of 688 KB    | 0.18 ms | 0.16 ms  |
| hashing all of it             | 0.30 ms | —        |
| parsing all of it             | 3.4 ms  | —        |

The reading is nearly all of it, and none of the reading is content this store
has not already read. It is the same bytes, in the same order, fetched one
`open` at a time because they are in six hundred files rather than one.

## The decision

- **`history/cache/revisions.txt` holds every revision document this store
  has read, verbatim.** A header line, then one entry per document: a line
  `<digest> <size> <modified> <path>`, the path last because a path is the one
  field that may hold a space and the time a whole number of nanoseconds
  either side of the Unix epoch, followed by exactly `<size>` bytes of the
  document and one newline. The header is `historica-revisions-1`, on 0036's
  reasoning: a fixed name has no digest to check it against, so one written by
  a version spelling this differently is discarded whole.

- **It holds the bytes rather than the facts.** A cache of parsed facts would
  be a second grammar for the revision document, kept in step with the first
  by hand, and it would have to be *believed* — there is nothing to check a
  claim about a document's parents against but the document. Bytes cannot lie:
  the entry states the digest it is, and hashing what the entry holds settles
  whether it is that. The whole of the file above costs 0.30 ms to hash, which
  is the cheapest verification in this repository and the only one that makes
  a cache incapable of inventing a history.

- **An entry is believed under three conditions, and read under any other.**
  Its bytes hash to the digest it claims. The directory reports the same size
  and the same modification time the entry recorded. And its recorded time is
  strictly older than the cache file's own, which is 0043's racy-mtime rule
  unchanged and taken here for the same reason: a revision document written
  twice inside one tick of the filesystem's clock would otherwise report a
  stamp that has not moved while holding bytes nobody hashed.

- **The path set is the completeness condition**, which is 0036's. The walk of
  `revisions/` happens anyway; every path it finds that the file does not
  account for is opened and read, and every path the file names that the
  directory no longer holds is dropped. So a `record` costs the next command
  one read, an `arrange` costs it a full pass, and a store this program has
  never seen costs exactly what it costs today.

- **It is written when the pass and the file disagreed**, and never otherwise.
  A store nobody has written to since the last command rewrites nothing.

- **`check` takes none of it.** `Store::open_reading_everything_on` is the
  opening that reads `revisions/` itself, and `check` is its only caller, on
  the rule 0035 set and 0036 restated: the command that holds a store to its
  own rules must not be handed an answer.

## Why the stamps, when the documents are immutable

The store writes documents with `create_new` and never overwrites one, so a
path accounted for once could be argued to hold the same bytes forever — and
0036 already makes exactly that inference about what a document forgets.

It is not available here, because of what this repository is for. The readable
files are the authority, and a person is invited to open them. Somebody who
edits the message in a revision document by hand has made that file a
different revision, which is a corruption `check` reports and which every
other command would notice today, because every other command reads the file.
A cache believed on immutability alone would go on printing the old message
until `check` was run — the tool saying one thing while the file on disk says
another, which is the one failure this format exists to rule out.

The stamps cost 1.55 ms for six hundred files, against the 8.7 ms of reading
them. A filesystem that declines `stamp` believes no entry and reads every
document, which is 0043's rule in the form it always takes: the consequence of
`None` is that a command reads what it would have read anyway.

## What it is not

**Not an index of the graph.** Nothing derived is written down. The parents,
the heads, the ancestry and the supersession are computed from the documents
on every command exactly as they were, and the file holds no claim about any
of them. What changed is where the documents are fetched from, not what is
concluded from them.

**Not a second store.** Every byte in it is a copy of a byte in `revisions/`,
each one hashed against the name it is filed under before it is used. Delete
it, truncate it, fill it with lies, or fill it with valid documents this store
does not hold, and every command answers as it did: an entry that does not
hash is dropped, an entry whose stamp has moved is dropped, and a path the
directory does not hold is not a path any reader is going to ask about.

**Not on the way to a binary format.** It is text with byte-counted documents
inside it, so `head -1` says what it is and the documents in it read as
themselves.

## What this costs

Disk, and a rewrite.

The file is as large as every revision document in the store put together —
773 KB for the six hundred above, against a store of 2.1 MB — and `cache/` was
already the larger half of a store by 0035's measure.

The rewrite is the ceiling, and it is worth stating plainly. There is no append
in `Filesystem` — 0026 gives mutable files atomic replacement and nothing else
— so a store that gained one revision rewrites the whole file on the next
command that reads it. Atomicity is most of what that costs: writing 773 KB
through `Filesystem::write` measures 7 ms where the same bytes written without
the rename and the flush measure 0.2 ms. So a `record` is followed by one
command paying about what opening the store cost before this decision, and
every command after that pays half.

It is linear in the store, where the read it replaces was also linear, and it
becomes the dominant cost somewhere north of a hundred thousand revisions —
where the file is tens of megabytes and a `record` is followed by a rewrite of
all of it. The answer there is more than one file, on 0041's year boundary,
and it is deliberately not built now: the shape of this one is chosen so that
splitting it later is a second header and no new grammar.

`cache/operations.txt` has the same rewrite behaviour, for the same reason, and
this decision does not fix that one either.

## Consequences

On the store above — six hundred revisions over ten files, 688 KB of documents
— `Store::open` falls from 14 ms to 7. Whole commands, measured through `cargo
xtask bench` with `cache/` left alone between runs, fall with it: `log` from
25.1 ms to 19.9, `files` from 26.0 to 20.0, `cat` from 28.3 to 20.5, `status`
from 35.8 to 28.2.

The same benchmark run with `cache/` emptied before every command reports the
other side of it: `log` rises from 24.1 ms to 29.5, which is the 7 ms write and
nothing else. That is a first reader, and a first reader once. It is the shape
every cache in this repository has.

What is left is the parse, at 3.4 ms of the 7, and it is now the largest single
cost of opening a store. That is the honest place for it to sit — it is the
work of turning this format's bytes into this format's facts, and a cache that
removed it would be a cache that had to be believed.

## Deferred

**More than one file**, as above.

**A heads file.** `log --limit 1` still loads the whole store, because the
heads are derived and deriving them needs the documents. A cache that answered
"these are the heads" would be believed about structure rather than checked
about content, which is the line this decision does not cross. If it is ever
crossed, it is crossed for a command that can afford to be wrong and re-ask,
and `check` will be the one that catches it.
