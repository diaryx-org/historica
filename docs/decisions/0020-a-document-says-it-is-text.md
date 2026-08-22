# 0020 — A document says it is text

Every document this format writes is UTF-8 text with LF endings, and none of
them says so where an operating system looks. A person who opens
`history/revisions/` and double-clicks `2026-08-20 Start a journal.rev` gets a
dialog asking what application to use. Quick Look shows nothing. A file manager
offers no preview and no icon.

0003's promise is that a person can read a history without the tool:

> A person must be able to inspect the history, understand its relationships,
> and recover stored content without decoding an opaque database or binary
> operation log.

That has been true of the *bytes* since the first document and false of the
*experience* on two of the three platforms this runs on. The fix is four
characters.

## The decision

- **A writer emits `.rev.txt` and `.ops.txt`.** The claim that says which kind
  of document a file is stays first; the claim that says it is text goes last,
  where an operating system reads it.
- **A reader accepts `.rev` and `.ops` as well, permanently.** Decision 0004's
  asymmetry, applied to a filename rule rather than a format one: a store
  written before today must not quietly stop having documents in it.
- **A payload avoids every accepted document suffix**, not merely the written
  one. This is the cost, and it is stated below rather than discovered.
- **`historica`, `names/`, and `history/skipped` keep their names.** The first
  is the store's marker rather than a document, and the other two have
  filenames that mean something — a bookmark's name *is* its filename, and
  `skipped` is named by 0011.
- **The corpus keeps `.rev` and `.ops`.** Not an oversight: it makes the
  specification-executed the standing test that a store written under the older
  names still loads.

## What the extension buys

The last extension is the one every desktop reads. `2026-08-20 Start a
journal.rev.txt` opens in the editor a person already has, previews in Quick
Look, renders inline where a `.rev` prompts a download, and survives being
mailed to somebody.

It costs less in the name than it looks, because both systems that read
extensions also hide them: with the default settings on macOS and Windows, the
file *displays* as `2026-08-20 Start a journal.rev`, which is exactly the name
it has today. So the displayed name is unchanged and the behaviour is better,
which is an unusually cheap trade.

On Linux and at a terminal it buys nothing and costs nothing, since neither
looks at an extension to decide what a file is.

## What it costs

**The double accept is permanent, and it keeps a hazard alive.** A payload
whose path ends in `.ops` is still a name the reader claims, so it still takes
the digest suffix that 0018 gives it. This change does not retire that rule —
it adds a second suffix to the list the rule has to avoid. The corpus files
that produced the failure this rule exists for are still filed as
`adjacent-deletes.ops 3bf103fa6eac` rather than under their own names, and the
only thing that would fix that is refusing to read `.ops`, which would make
every store written before today lose its documents quietly. That is the
failure 0016 named as the worst one available, and it is not worth a filename.

**Every arranged store is re-filed again**, the third time in a week. Renames
only, so no identity moves and no reference dangles, and `arrange` is what does
it. A store nobody re-arranges keeps loading.

**`check` has to strip two suffixes to find a digest.** `FilenameLies` fires
where a whole stem parses as a digest and the bytes hash to something else;
with two suffixes, a stem naively taken is `<digest>.rev`, which parses as
nothing. Left alone, the check would silently stop firing — a check that
quietly stops checking, which is worse than the thing it checks for.

## Rejected alternatives

**`.txt` alone.** Loses the claim that distinguishes a revision from an
operation document, which is the one syllable of a filename this format reads.

**`.md`.** They are not Markdown, and a name that says so is a small lie told
to get a better icon.

**Accepting only `.rev.txt`, and treating `.rev` as a foreign file.** Clean,
and it would let a payload keep the name `notes.ops`. Rejected because a store
written last week would load with its documents missing and `check` would call
their absence ordinary, which is precisely the quiet failure 0016 refused to
build.

**Falling back to content for a `.ops` file — parse it, and call it a payload
if it does not parse.** It resolves the ambiguity in the right direction for a
payload that is not a document, and in the wrong direction for a payload that
*is* one, which this corpus is full of: a stored copy of a valid operation
document would be claimed as a document and then not found as content. Sniffing
trades a visible rule for an invisible one.

**Renaming `historica` to `historica.txt`.** It is one line, it is the marker
`discover` walks up looking for, and a person who opens it learns the version
they already know. Left as an open question rather than done for symmetry.

## Consequences

- `store` gains a written suffix and an accepted list per kind, and the walk
  filters by suffix rather than by `Path::extension`, which cannot see a
  two-part one.
- `check` strips any accepted suffix before asking whether a stem is a digest,
  and its `ForeignFile` and unnamed-payload messages name the suffix a reader
  wants rather than the one it merely tolerates.
- `naming` writes the new suffix and avoids the whole accepted list when naming
  a payload.
- `record`, `arrange`, and every test that spells a filename move together.
- Nothing in `format`, `core`, `merge`, `replay`, or `tree` changes at all,
  which is the sign that this is a filename decision and not a format one.

## Resolved questions

1. **Whether `historica`, `names/*`, and `skipped` should follow.** Each is a
   text file a person might open and none carries an extension. Answered by
   [0021](0021-the-store-explains-itself.md): they become `historica.txt`,
   `names/*.txt`, and `skipped.txt`.
2. **Whether the payload rule can ever be retired.** Answered by
   [0021](0021-the-store-explains-itself.md), which spends the one
   pre-deployment moment when no outside store exists: `.rev` and `.ops` stop
   being accepted, leaving only `.rev.txt` and `.ops.txt`.
