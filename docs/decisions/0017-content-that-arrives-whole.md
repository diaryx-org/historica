# 0017 — Content that arrives whole

Two documents deferred the same question from opposite ends.

0008 reserved a spelling for a file a list of lines cannot describe:

> **Binary and non-UTF-8 content.** A list of lines is the wrong model for an
> image. The likely answer is that such a file names its bytes and never
> merges, which is a tree question about what an entry may point at.

0016 found the other half by recording this repository into itself:

> an `add`'s operation document is the whole file with `+` before each line, so
> recording a codebase writes a second copy of it and produces one opaque
> document per source file. Whether 0007's document deserves a shape for "this
> content arrives whole" — and what that would mean for forgetting, which 0014
> built on the payload of an operation document — is a format question, needs a
> format version, and should be decided on its own terms.

They are one question. A photograph and a newly written source file have
nothing in common as content and everything in common as storage: both are a
run of bytes that no operation produced, that no parent state explains, and
that a person can open in the tool they already use for that kind of file. The
difference between them is what the *file* is, which is a fact about identity
and lives in the revision document. It is not a fact about the bytes.

This document decides that storage, its grammar, and the format version the
grammar costs.

## The decision

- **A payload is a file of bytes in the store, named by its digest and
  carrying no format of its own.** Not a document: no preamble, nothing to
  parse, and `shasum -a 256` on it prints the digest the revision names.
- **Payloads live in `operations/`**, beside the documents, under 0016's
  naming scheme. Only `*.ops` is read as an operation document there; every
  other file is a payload, and its identity is its SHA-256.
- **`text <file> <digest>` is the content a file is created with**, as lines.
  It appears only with `add`.
- **`bytes <file> <digest>` is the whole content of a file that has no lines**,
  as 0008 reserved. It appears with `add` and on its own, and a file it
  describes never merges.
- **`add` with `edit` is refused**, because a file added by a revision did not
  exist at its parent to be edited. That is a spelling retired, which
  0004 permits only at a version boundary, so this is **`historica-v1`**.
- **A v1 reader parses v0 exactly as v0 did.** The version 0 histories in the
  corpus are not rewritten, the old spelling stays legal in the documents that
  already use it, and replay keeps the path that reads them. 0004's rule is
  that a reader's vocabulary only grows; a version constrains writers.
- **A file's kind is fixed when it is added**, which 0008 already decided.
  `edit` on a file added with `bytes`, or `bytes` on one added with `text`, is
  refused. Changing kind is `drop` and `add`.
- **Item identity does not change.** A `text` payload is exactly the operation
  document that inserts every line at 0, and its items carry exactly the names
  that document would have given them.

## A payload is not a document, and that is the point

Every file in a store so far has been a document: a preamble, headers, strict
reading, one byte sequence per set of facts. A payload has none of that. It is
`photo.png`. It is `README.md`. Reading it is `cat`, and verifying it is
`shasum -a 256`, and neither of those needs Historica — which is the claim the
whole format exists to make, arrived at here by having nothing to decode.

So the store gains a second kind of file, and the rule that keeps the two
apart is one 0003 already wrote for `revisions/`:

> Only `*.rev` files here are read as revisions.

`operations/` reads the same way. Only `*.ops` is an operation document; every
other file is a payload. A reader keyed on the extension therefore skips
payloads rather than choking on them, and the loud failure such a reader
deserves comes from somewhere better: the `text` or `bytes` header in the
revision document, which is an unknown header in an unknown version, and stops
it dead at the file that says so.

Nothing about a payload is parsed, so nothing about a payload can be malformed.
The only claim it makes is its digest, and that claim is checked by hashing it.

## Where payloads live, and why not a folder of their own

0008 said `history/bytes/`, and the first draft of this document said
`history/attachments/`, which is friendlier. Both are wrong for the same
reason.

A payload has no kind of its own. Whether a run of bytes is a text file's first
content or an image's whole content is stated in the revision document, by
which header names it — 0008 put the kind on the file's identity, deliberately,
so that an operation chain could never become unreplayable underneath one.
Sorting payloads into directories by that fact files bytes by something the
bytes do not carry, which is the exact inversion of 0003's rule. It also
produces two directory trees with the same revision stems in both, so "what did
this revision do" becomes two folders to open, and it invents an edge worth
nothing: two revisions naming one digest, one as `text` and one as `bytes`,
whose single payload would then have two homes.

One home, and it is the one that already shards the right way:

```
history/operations/
└── 2026-08-20 Start a journal/
    ├── README.md            payload — the file, as it was created
    ├── notes⁄photo.png      payload — the image
    └── src⁄cli⁄mod.rs.ops   operation document
```

0016's scheme carries over unchanged: the directory is the revision's arranged
stem, the filename is the path the file had in that revision, and `/` becomes
`⁄` (U+2044) for the reason 0016 gives. A payload takes no extension, because
the extension it has is the one the file has, and a person double-clicking
`notes⁄photo.png` in that folder gets a picture.

Forgetting settles the question on its own, below: a forgotten text payload
*becomes* a document. If payloads lived elsewhere, redacting one would move it.

**When two files want one name.** A payload named for the path `x.ops` and an
operation document named for the path `x` both want `x.ops`. 0016 already
settles this and its rule needs no amendment, only its scope: two things
wanting one filename each take a digest suffix, never a counter, so the
readable name survives and the ambiguity does not. What is added here is that
the name a collision is decided on **includes the extension**, and a document
keeps `.ops` whatever else happens to it — `notes 4a3a5224.ops`, never
`notes.ops 4a3a5224` — because the extension is what says it is a document at
all, and the rule that tells the two kinds apart is the one thing a
disambiguator may not break.

## The grammar

```
add   <file> <path>     a file created, and where it is put
move  <file> <path>     a file's new path
drop  <file>            a file removed
edit  <file> <digest>   an operation document, against the file at the parent
text  <file> <digest>   the lines a created file arrives with
bytes <file> <digest>   the whole content of a file that has no lines
```

Exactly one of these, per file, per revision:

- `add`, alone or with `text` or `bytes`;
- `move`, alone or with `edit` or `bytes`;
- `edit` or `bytes` alone;
- `drop` alone.

This is 0008's list with `edit` removed from the `add` line and `text` put
where it was. The refusal has a reason a person can check by eye: `edit`'s
positions are counted into the file at the revision's parents, and a file this
revision adds is not there. The old spelling worked because the state was
empty and the positions were all zero — an arithmetic coincidence rather than
a meaning.

**`text` appears only with `add`.** Stating a text file's content whole when
the file already exists would give every line a new name, which orphans every
concurrent edit anyone else is holding: their operations quote items that the
merge can no longer find. That is a truncation, not an edit, and it is spelled
`drop` and `add`, which says the same thing and says it honestly. The shape
0007 wanted for re-rooting a history is visible here and is not taken; it
belongs to that question, on its own terms, with its own document.

**`bytes` appears anywhere `edit` may.** A binary file's content is replaced
whole because there is nothing else to do with it, and 0008 already said what
happens when two branches do that concurrently: it is a divergence, reported
exactly as 0001 describes divergence, never a silently chosen winner.

## Item identity does not change

A `text` payload's items are its lines: split after each `\n`, terminator
included, and the last item is unterminated exactly when the payload's last
byte is not `\n`. An empty payload has no items, and a file added with no
content names no payload at all.

That is precisely the operation document

```
historica-v0

insert 0
+…every line…
```

would produce, and the items take the names that document would have given
them — `(R, 0)` through `(R, n-1)`, `R` being the revision that names the
payload. 0007's ordering rule reads them identically, so merge and replay are
untouched by this document. Only the spelling of a creation changes.

Two small things fall out, and both are improvements. The `\ no newline`
marker is not needed for a creation, because a file's final byte already states
that fact and states it in the place a person would look. And a payload holds a
carriage return, or any other byte a line may contain, without the format
having to say it may — 0007 spends a paragraph permitting CR inside an item,
and a payload needs no permission.

A revision recorded under v0 and the same work recorded under v1 produce
different digests, because they name different files. They are different
histories that materialise to the same bytes, which is what a version bump
always means and is why 0004 allows one only when the writer changes.

## Which kind a file is, and who decides

The format's rule is narrow: a `text` payload is valid UTF-8, because a later
`edit` has to quote its items into a document that is UTF-8. A payload named by
`bytes` is any bytes at all. A `text` payload that is not valid UTF-8 is the
store contradicting itself, which makes it an error in `check` rather than a
note.

The tool's rule is where the sniffing lives, and it is a tool rule on purpose:
**`record` stores a file as text when its bytes are valid UTF-8 and hold no
NUL, and as bytes otherwise.** NUL is not the format's business — an operation
document could quote one and round-trip it — but it is the oldest and most
reliable signal that a person did not write this file as prose, and the
recorder is allowed to use signals the format may not.

Sniffing happens once, at `add`, and never again, because the kind then belongs
to the file's identity. Afterwards:

- a text file whose working copy stops being valid UTF-8 is refused by
  `record`, naming `drop` and `add` as the fix, because that is what it is;
- a binary file whose working copy becomes valid UTF-8 stays binary, silently,
  because nothing happened;
- a person who disagrees with the sniff has no override yet. That is deferred
  below rather than guessed at.

This closes 0011's and 0015's outstanding refusal. `WorkingError::NotText` —
"is not UTF-8 text, and binary content is decided but not implemented" — was
always a placeholder for this document, and the files it refused are now
recorded.

## Merging, and the attachment nobody can mark up

Concurrent `bytes` for one file is a divergence, reported and never resolved by
the format. 0012's machinery cannot help: it renders a contested span between
marker lines *in the working copy*, and there are no lines and no spans in a
JPEG. So there is nothing to render and nothing to detect, and pretending
otherwise would mean inventing a filename for one of the two versions — which
0008 forbids in the sentence a merge should be judged by, that a name invented
by a merge is content nobody wrote.

What happens instead is small and honest. `historica merge` reports the
contested path, leaves the working copy alone, and prints the command that
writes each side somewhere the person can look:

```
contested  notes/photo.png
    historica cat kxryzmor notes/photo.png > /tmp/theirs.png
    historica cat mzvwutkl notes/photo.png > /tmp/mine.png
```

`record --merge` then takes whatever bytes are in the working copy, which is
what it does for every other file and is the reason it needs no new rule. The
refusal 0012 built — a merge record refuses while a marker line still stands —
simply does not apply to a file that cannot hold one, and that gap should be
said out loud rather than papered over: for a contested attachment, the tool
cannot tell a resolution from an oversight. The person can, and the report is
how they are told to.

## Forgetting a payload

0016 asked what this would mean for 0014, which built redaction on the payload
of an operation document. The answer is that 0014's mechanism already fits,
and fits better than the thing it was designed for.

A forgetting document stands in for the document whose bytes were destroyed,
states the same operations at the same positions with the same item counts, and
carries `forgets <digest>`. For a text payload, the document it stands in for
is the `insert 0` the payload is equivalent to, so a forgotten text payload is
replaced on disk by an ordinary forgetting document:

```
historica-v1
forgets 9a4cf0b8…

insert 0
\ forgotten
\ forgotten
\ forgotten
```

The revision document is untouched — it still names the payload's digest — and
a reader that cannot find that payload finds a document that forgets it, which
is exactly what 0014 arranged for an operation document. Shape survives,
positions survive, everything downstream still replays.

For a `bytes` payload there are no items and no arithmetic to preserve, which
is the case 0014 anticipated: "the whole payload goes and only its digest and
length remain."

```
historica-v1
forgets e10f37c2…
length 2418573
```

And here is the argument for one directory, made by the format rather than by
taste: forgetting turns a payload into a document, in place. Had payloads lived
in `attachments/`, a redaction would have had to move a file between
directories to change what kind of thing it is — while the thing that names it
is immutable and says nothing about where it lives.

## `historica-v1`

0004 was written for this and its rules apply without amendment:

- **The version constrains writers, never readers.** A v1 reader parses every
  v0 document exactly as v0 did, forever. `add` with `edit` stays legal in a v0
  document, `tests/corpus/revisions/`, `operations/`, and `tree/` are not
  rewritten, and the replay path that reads them is not deleted. Two corpora do
  move, and neither is a history: `diffs/` records what the *writer* emits, so
  it emits v1 now, and the invalid example whose fault is "a version this
  reader lacks" becomes `historica-v2`, because that fault is defined against
  the reader and moves whenever the reader does. The cost of adding a spelling
  is that it can never be removed, and this is that cost being paid rather than
  avoided.
- **A v1 writer writes v1 everywhere**, including operation documents whose
  grammar did not change, because the preamble describes how to read the file
  and one format has one current version.
- **The repository header states the highest document version the store
  holds**, and a writer that stores its first v1 document rewrites it. That
  makes the header the reader's gate: a reader that knows only v0 refuses the
  store at the file that says so, rather than reading four fifths of it and
  calling the result a history. Recording into an existing v0 store therefore
  bumps its header, which is a visible fact and should be printed.

This answers half of 0004's second open question — whether `0` was the
commitment. It was not.

## Consequences

- `format` gains `text` and `bytes`, ranked after `edit` and before `x-`
  (ranks 11 and 12, with `x-` moving to 13), both repeatable, both `<file>
  <digest>`. `RevisionDocument` gains two maps beside `edited`, and the
  cross-header check gains one refusal per contradiction in the grammar above,
  each naming the fix.
- `format` gains a version: `PREAMBLE` becomes the version a writer emits,
  parsing accepts both, and every document carries which one it was written
  under, because the grammar check differs between them.
- `store` gains payloads. They are **not read at open** — a store of
  photographs must not cost a full hash to run `log` — so the directory is
  indexed on first need and memoised for the life of the `Store`. A persistent
  index belongs in `cache/`, which 0003 already promises is disposable.
- `store` gains `payload(digest)`, which returns the bytes or says nothing has
  delivered them, and `content_at`, which returns lines or bytes according to
  the kind the tree holds. `content` stays what it was, for a file of lines.
- `replay` gains the creation path: a `text` payload replays as `insert 0` of
  its lines, and a `bytes` file has no chain to replay at all.
- `tree` gains a kind per file, derived from the revision that added it, and
  the refusals that kind makes possible.
- `diff` is unchanged for text and does nothing for binary: a file whose kind
  is `bytes` and whose digest differs names a new payload, and that is the
  whole comparison.
- `record` gains the sniff, writes payloads, and loses `WorkingError::NotText`
  as a refusal — it becomes a kind instead. `add` stops producing an operation
  document.
- `working` gains reading a file as bytes; `status` compares a binary file by
  digest and says only that it changed; 0015's `refused … not UTF-8 text` line
  disappears from its output.
- `cli`: `cat` writes payload bytes to stdout unchanged, `show` prints a
  payload byte for byte as it prints a document, `log`'s summary counts whole
  content separately from edits, and `merge` reports a contested attachment in
  the shape above.
- `check` gains: a payload nothing names (a note, like a duplicate), a named
  payload nothing delivers (a note, like an undelivered operation document), a
  `text` payload that is not valid UTF-8 (an error), and a payload whose bytes
  do not hash to anything named (which is the same note as the first, arrived
  at from the other side). It is the command that hashes every payload
  deliberately.
- `arrange` files payloads under the revision stem, with the collision
  fallback above.
- The corpus gains a v1 history with an image in it, a v1 creation by payload,
  and invalid examples for each refusal in the grammar. The v0 corpus stays
  exactly as it is, which is the version rule demonstrated rather than
  asserted.
- 0016's opening complaint is answered: recording this repository writes 116
  source files as themselves, not as 116 opaque documents with `+` down the
  left margin, and the store stops being a second copy that reads worse than
  the first.

## Rejected alternatives

**A directory of their own — `bytes/`, or `attachments/`.** 0008's reservation
and the friendlier name for it. Rejected above: kind is a fact about the file,
not about the bytes, so filing by it inverts 0003's rule, duplicates the
revision stems across two trees, and makes redaction a move between
directories.

**Keeping `add` with `edit` legal alongside the new spelling.** No version
bump, no corpus question, and every store that exists keeps working without a
header rewrite. Rejected because it makes two byte sequences say one thing in
one version, which is the property this format spends its strictness on, and
because the cost it avoids is paid once by a writer rather than forever by a
reader.

**Sniffing kind at read time.** Let the file be whatever its bytes look like
when someone opens it. Rejected for 0002's reason: two replicas would answer
"is this file text" with two different library versions, and a history two
replicas disagree about is not a history. It is also 0008's reason — a file
whose content model moved underneath its identity makes every earlier operation
in its chain unreplayable.

**Compressing or packing payloads.** The obvious storage win, and the one that
would make `shasum -a 256` stop printing what the revision names. A store whose
files need a tool to read is the thing this project exists not to build. Size
is a `cache/` question if it is ever a question.

**A `content` header that states a text file's whole content at any revision.**
Rejected above: it orphans concurrent edits by renaming every item. It is also
the shape re-rooting wants, which is a reason to leave it unspent rather than
to spend it here.

**An operation document that names a payload for its inserted items** —
keeping one document type, with the bulk moved out of it. Rejected because it
is the same two files with an indirection between them, and the readable one
would be the one nobody names.

## Deferred

**An override for the sniff.** A person who wants a minified bundle stored
whole, or a UTF-8 file treated as an attachment, has no way to say so. The
shape is either a rule file beside `skipped` or a flag on `record`, and which
one depends on whether the fact is about a path or about an occasion. Nothing
here is blocked by it, and guessing would put a second rule file in a format
that has one.

**Large payloads.** The implementation reads a payload whole to hash it and
whole to write it. Streaming, chunking, and not holding a video in memory are
real work that a journal with photographs in it will not notice and a
repository of build artefacts will. `cache/` is where the digest index goes
when hashing on demand stops being affordable.

**Forgetting, still.** 0014 has a shape and no implementation, and this
document adds the payload case to what that implementation will owe.

**Re-rooting**, 0007's second open question, which now has a visible shape and
deliberately no spelling.

## Open questions

1. **Whether the tool can tell a resolved attachment from an unexamined one.**
   It cannot, above, and `record --merge` takes what it finds. A marker file
   beside the attachment would restore the refusal at the cost of writing
   something into a person's folder that they must remember to delete.
2. **Whether `status` should say more about a changed attachment than that it
   changed.** A size, a dimension, a preview: all of it is the tool reading
   content it has decided not to understand, and all of it is what a person
   actually wants to know.
3. **Whether NUL belongs to the tool or the format.** It is the tool's here, so
   a hand-written store may hold a `text` payload with a NUL in it and every
   operation on it will work. That is either correct minimalism or a rule
   written in the wrong place.
4. **Whether `record` should perform the `drop` and `add` itself** when a text
   file stops being UTF-8. It refuses and says so, on 0011's principle that a
   rename is the one fact a person states — but a file that was rewritten by a
   tool the person did not think of as a rewrite is a different case, and the
   refusal may read as an obstacle rather than as a question.
