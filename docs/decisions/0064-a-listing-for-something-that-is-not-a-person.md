# 0064 — A listing for something that is not a person

0063 gave `log` a range and filed the next question under what is not here:

> The script a range now permits still has to parse a rendering meant for
> eyes. That is the next thing somebody will want and it is a decision of its
> own, because it is a promise about output nothing currently makes.

This pays it. The reading `log` prints is written for a person and should
stay that way — abbreviations that grow as the store grows, marks in
parentheses, a message indented under its own entry, `(no message)` where
there is none. Every one of those is right for eyes and wrong for a caller,
and the sentence that costs the most is the one printed when there is nothing
to show: a script that split `no revisions here yet` into fields would get
four of them.

## What is already machine-readable

Most of it, which is the unusual part of this decision and the thing that
decides its shape.

0003 makes the readable files the authority and `show` prints one byte for
byte. So a revision's author, its message, its parents, what it supersedes
and what it did to the file set are *already* available to a program, in a
grammar 0002 documents and 0004 holds a reader to. There is no gap there.

The gap is everything that is not in any one document:

- **which** revisions — the set, after a range and the filters
- **in what order** — 0016's presentation order, which is causality with a
  deterministic tie-break and is not derivable from a document either
- **what the graph found about them** — that nothing stands on this revision,
  that something rewrote it, that its change has more than one revision
  anybody could mean. None of the three is a fact a revision states about
  itself; each is read off every *other* document in the store.

A listing that also restated the author and the message would be a second
rendering of text the authority already holds, and 0037 has already refused
that shape once, for diff hunks:

> A tool whose preview disagreed with its commit would be a tool nobody could
> trust twice

## The decision

- **`log --fields` prints the same listing, in fields.** The same command,
  the same selection, the same order, the same filters — one flag choosing
  who the output is for. Not a second command, because a second command is
  two answers about which revisions matter and eventually they differ.

- **A `historica-log-1` header, then one line per revision.** Numbered, for
  0048's reason exactly: a document is permanent and a store's grammar is a
  promise, and this is neither. A reader that meets a spelling it does not
  know discards the listing whole rather than guessing at the fields.

- **`<digest> <change> <when> <marks|-> <parent>...`**, single spaces, and
  nothing escaped or quoted — because no field here *can* hold a space. That
  is not luck; it is what choosing these fields and no others buys, and it is
  0048's discipline restated. That manifest put the path last because a path
  is the one field that may hold a space; this listing has no such field at
  all, so the variable-length one goes last for a different reason: a root
  revision's line simply ends earlier.

- **Spelled whole, where the reading for a person abbreviates.** 0001 makes
  an abbreviation the shortest prefix that is unique *in this store today*, so
  it is a fact about what else the store holds rather than about the revision
  it names. A caller that wrote one down would find it ambiguous after a
  fetch, through no change to the thing it named.

- **The marks are the graph's findings and nothing else: `head`,
  `superseded`, `divergent`**, comma-joined, or `-`. `merge` and `rewrites`
  are in the reading for a person and not here, because the document says
  both outright — `parent` twice, and `supersedes` at all — and a listing
  that pointed at a file and restated it would be the second answer above.
  The field is never empty, because an empty field is two spaces where a
  reader splitting on one expects a word.

- **Parents are in it, and that is the one deliberate copy.** They are in the
  document too, and a caller could read them there. But the whole use for
  this output is walking the graph without opening every document, and a
  walker that had to open every document to find its edges would have been
  given nothing. It is a copy of a minted identifier, which cannot disagree
  with its original the way a re-rendered message could.

- **Nothing to show is a header and no lines under it**, exiting zero. Not
  `no revisions here yet`, not `no revision here matches all of those`, and
  not 0063's `holds nothing`. Those three sentences are answers to a person
  and they stay; what a caller needs is a well-formed listing of nothing,
  which is what an empty one is.

- **The filters and the range compose with it untouched.** They say which
  revisions and this says how they are printed. `--author` and `--grep` read
  text the listing does not print, which is the filters doing their own job
  rather than a disagreement about anything.

## What is not here

**A machine reading of anything else.** `status`, `check`, `files`, `diff`
and `blame` all print for a person, and each is its own decision with its own
fields. This one is built because 0063 named the caller that wanted it. The
header's number is what leaves room for the rest without promising them.

**A field for what a revision did to the file set.** `added 2`, `moved 1` and
the rest are counts of what the document lists, and 0037 already gives the
same question a better answer in `diff`. A caller wanting the file set has
`files`, and one wanting the operations has `show`.

**A stable field count.** A later `historica-log-2` may have more fields, and
a reader that splits and indexes will meet them. That is what the header is
for, and it is why the number is in the first line rather than implied.

**A promise that the reading for a person is stable.** It is not, and this
flag is the answer to anyone who needed one.

## Consequences

- `render::fields` is the second rendering beside `render::log`, and
  `render::kept` is the selection they share, so the two cannot disagree
  about which revisions matter or in what order.
- `render::found` is the machine spelling of the marks and is deliberately
  not `render::marks`: the two lists differ, on the argument above, and one
  function returning both would have hidden the fact that it is a decision.
- The empty-listing sentences stay in `cli::log`, where the person's own
  spellings are, and are skipped whole when `--fields` is set.
