# 0061 — What a command does not have to parse

0058 ended by naming what it had left behind:

> What is left is the parse, at 3.4 ms of the 7, and it is now the largest
> single cost of opening a store. That is the honest place for it to sit — it
> is the work of turning this format's bytes into this format's facts, and a
> cache that removed it would be a cache that had to be believed.

The second sentence is true of a cache and false of the parse. Most of what
opening a store parses is not what anything that opened it asked for.

There is a second cost hiding behind the first, and it is larger. The
projection every command builds — `Store::history`, over the whole store — went
through `RevisionDocument::to_revision`, whose `id` field is
`RevisionDocument::id`, which is `digest(&self.write())`. So asking a store for
its graph *re-serialised and re-hashed every document in it*, to arrive at the
digest each one is already filed under. On a store of six hundred revisions
over twenty files that is 7.3 ms, per call, and `log` alone makes three.

`rank` states the whole argument. `change` is 0, `parent` is 1, `supersedes`
is 2, `author` is 3, and everything from 7 up is a tree fact. What a graph
question needs is `core::Revision` — a digest, a change, the parents, the
supersessions, and the message — and every one of those is either a header of
rank 0 to 2 or the verbatim tail after the separator. The author, the moment,
the rewriting stamps and the whole of the tree are read at open by every
command and used by almost none of them.

So the parse has the wrong shape. It is linear in the *bytes of the history*,
where every question that opening a store exists to answer is linear in the
*number of revisions*. Two stores of nearly identical total size, one long and
narrow and one short and wide, show the difference as plainly as it can be
shown:

|                                   | 1601 revisions × 1 file | 201 revisions × 20 files |
|-----------------------------------|-------------------------|--------------------------|
| document, average                 | 282 bytes               | 2 098 bytes              |
| reading one whole                 | 1.34 µs                 | 8.70 µs                  |
| reading the revision out of one   | 0.21 µs                 | 0.50 µs                  |
| all of them, whole                | 2.14 ms                 | 1.75 ms                  |
| all of them, the revision alone   | 0.33 ms                 | 0.10 ms                  |

Reading the revision costs what it costs per *document*. Reading the document
costs what it costs per *file the revision touched*, which is the number that
grows.

## The decision

- **`format::revision` reads the revision a document states, and `Store::open`
  calls that.** It sits beside `format::digest` and takes the same argument
  for the same reason: these are the two questions answerable about a
  revision document's bytes without interpreting the document. What it
  returns is `core::Revision`, which is what `Store::history` was building
  out of whole documents.

- **It walks every header line, and refuses everything refusable without
  reading a value.** The byte order mark, the carriage return, the bytes that
  are not UTF-8, the preamble, an unterminated line, a line that does not
  split into a key and a value, a key no `rank` knows, a key out of the fixed
  order, a key repeated that may not be, a repeated key whose values descend,
  two facts stated twice, and an empty message after a separator. Every one
  of those is a comparison of a key or of a raw value, and walking the whole
  block to make them costs nothing measurable over stopping at `author`: the
  expense in the parser is parsing values and allocating for them, not
  reaching the lines.

- **It reads the values of `change`, `parent` and `supersedes`, and takes the
  message verbatim.** Nothing else. The values of ranks 3 and above are
  recognised and stepped over.

- **The rest of a document is parsed on first need, from the bytes the store
  already holds.** 0058 put every revision document in memory and this keeps
  them there, so a command that asks for an author, a moment, an extension or
  a tree fact parses that one document whole, once, and keeps it. There is no
  read behind it: this is 0058's cache being asked a second question, and it
  is the shape `operations/` has had since 0036 and 0043.

- **What a deferred parse defers is the meaning of a value.** A `when` that is
  not RFC 3339, a path 0008 refuses, a file ID outside the `k`–`z` alphabet, a
  digest of the wrong length, a `mode` that is neither word, a `link` target
  that parses as neither spelling: each is now refused when something asks
  what that document did rather than when a command opened the store. That is
  0002's strictness in the position 0058 already put it for `operations/` —
  "What the revisions did is read on first need" — and the set of faults it
  covers is smaller than that one, because everything structural above is
  still refused at open.

- **`check` is unchanged.** It parses every revision document whole itself,
  and takes no cache of any kind. The command that holds a store to its own
  rules still reads every rule, and it is where a store learns of a fault
  nothing has happened to ask about.

- **A store holds a revision beside its digest, and stops recomputing it.**
  `Store::history` builds from the revisions read at open, each carrying the
  digest of the bytes it was read from — computed once, by the hashing 0058
  already does. `RevisionDocument::to_revision` stays what it is for the caller
  holding a document and no store, and `insert_at` is the one place left that
  calls it, where the document has just been written and the digest is the name
  it was written under.

- **Nothing is written down, and nothing is believed.** No file in `cache/`,
  no derived fact, no second grammar. This decision does less work rather than
  remembering the work it did.

## Why not a cache of facts, settled

0049 deferred one and said why; 0058 refused one and said why again. The
refusal is worth closing rather than restating, because there is an argument
for crossing it that looks sound and is not.

The argument: a cache of parsed facts could state the digest of the document
set it was derived from, and a reader could hash that set — cheap, since 0058
hashes every document anyway — and believe the cache only when the two agree.
That checks *which documents the cache was built from*. It does not check
*what parsing them yields*, which is the claim actually being made, and the
party in a position to forge a `parent` line in `cache/` is by construction a
party holding the documents and able to compute a matching key over the forgery.

There is no cheaper check, and the reason is 0002. The digest covers the whole
file and the format offers nothing smaller to check a part of it against. A
Merkle structure over the lines would offer exactly that, and it is precisely
what the README promises the digest is not: the SHA-256 that `shasum -a 256`
prints. So a claim about a `parent` line cannot be checked for less than the
cost of parsing the document that states it, ever, and a cache of facts is a
cache that must be believed for as long as this format keeps its promise.

Which is the right outcome, because the parse was never the thing to cache.

## What this costs

**A document read twice, where both halves are wanted.** A command that wants
every document whole — `log` printing every message and author — pays the
walk this decision added and then the parse it deferred: about 16% over
today's cost on the narrow store above, about 6% on the wide one. That is the
price of the other commands paying a sixth of it, and `log --limit` is what
keeps the number of documents `log` wants whole bounded in the first place.

**Bytes held rather than dropped, and copied once.** `load` kept parsed
documents and let the bytes go; it now keeps the bytes and lets most of the
parse go. A believed entry's bytes are copied out of `cache/`'s own buffer,
which 0058 was careful not to do — that decision had no use for them past the
rewrite and this one does, so the copy is what the store is holding rather than
a second copy of it. It is one pass over every revision document, and on a
store of one-line revisions it is most of what this decision costs.

Whether a store is *smaller* in memory depends on its shape. A
`RevisionDocument` is larger than the bytes it came from — every path and every
author is an allocation, every map is a tree — so a store nothing asks whole is
smaller now, and a store every command wants whole is larger by exactly the
bytes, since both live at once. `log` without a limit is the second.

## Consequences

- `format::revision` is the new reader, held to the corpus by the rule that it
  and `RevisionDocument::parse` agree: every valid document in
  `tests/corpus/revisions/` yields the same `Revision` through both paths, and
  every invalid one that fails for a structural reason is refused by both. The
  invalid files that fail for a *value* reason are the deferral, listed by
  name in the test that asserts `format::revision` accepts them.
- `store::revisions::load` returns the bytes alongside the revision, and
  `Store` holds a document as its revision, its bytes, and a `OnceCell` for
  the whole. `Store::document` fills that cell.
- `Store::history` builds from revisions rather than from documents, which is
  what it wanted: `RevisionDocument::to_revision` was cloning a message into a
  projection nothing but a digest comparison reads, and the tree facts beside
  it were parsed for nobody.
- `Store::get` and `Store::iter` are fallible now, because a parse deferred is
  a parse that can fail where it used to have failed already. Every caller that
  wanted a graph fact takes `Store::revision`, `Store::revisions` or
  `Store::holds` instead and is infallible again — which is most of them, and
  is the honest accounting of how much of this store's code was reading whole
  documents to look at two lines of them.

- What the commands do, measured on the two stores above, fastest of seven,
  process start subtracted:

  | command         | 601 × 20 before | after   | 1601 × 1 before | after   |
  |-----------------|-----------------|---------|-----------------|---------|
  | `names`         | 10.1 ms         | 8.2 ms  | 13.7 ms         | 12.6 ms |
  | `log --limit 1` | 20.7 ms         | 17.3 ms | 33.1 ms         | 33.1 ms |
  | `log`           | 21.8 ms         | 18.6 ms | 36.9 ms         | 37.3 ms |
  | `files @`       | 11.1 ms         | 7.6 ms  | 12.3 ms         | 12.4 ms |
  | `cat @`         | 10.6 ms         | 7.6 ms  | 12.5 ms         | 12.3 ms |
  | `status`        | 43.0 ms         | 23.6 ms | 39.5 ms         | 34.4 ms |
  | `check`         | 402 ms          | 327 ms  | 117 ms          | 121 ms  |

  `Store::history` falls from 7.34 ms to 0.07 on the wide store and from 2.93
  to 0.22 on the narrow one, which is the re-hashing leaving. `Store::open`
  falls from 9.04 ms to 7.15 and from 10.43 to 9.68.

  The narrow column is the honest half. A store of one file has documents of
  282 bytes, nearly all of which is the revision, so there is almost nothing
  for this to decline to read and the byte copy `load` now makes costs about
  what the deferred parse saves. The wide column is the shape a repository has,
  and it is where a document is mostly tree.

## Deferred

**The stamp, which this decision makes the largest term by a distance.** Where
opening the 1601-revision store above spends its time, warm:

| what                                          | cost    |
|-----------------------------------------------|---------|
| `read_dir` over `revisions/`, names only      | 0.64 ms |
| one `stamp` per document, on top of that walk | 4.10 ms |
| reading and hashing `cache/revisions.txt`     | 1.3 ms  |
| parsing every document whole                  | 2.14 ms |
| reading the revision out of every document    | 0.33 ms |
| stamping the month directories instead        | 0.03 ms |

The per-document stamp is now five times the walk that finds the paths and ten
times the parse this decision leaves behind, and it buys one thing: 0058's
hand-edit property, which is the reason that decision declined to believe an
entry on immutability alone. The last line is what declining it again would
cost, and it is not available for free — a directory's modification time moves
when an entry is added, removed or renamed, and does not move when a file
inside it is edited in place. So taking the month directories *is* taking
immutability on trust, arrived at by a different road. That is a decision about
what a person editing a readable file is owed, it is the one 0058 already
argued one way, and it is not this one.

**`log` still parses every document it prints**, which is correct: it prints
the author and the message of each. What was worth removing there is removed —
`log` no longer parses the tree of every revision to print none of it.
