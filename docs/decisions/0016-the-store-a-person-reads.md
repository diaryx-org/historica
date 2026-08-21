# 0016 — The store a person reads by hand

Decision 0003 made a promise that nothing since has fully kept:

> Identity comes from content, so a filename means nothing to the reader and
> everything to the person browsing the folder.

0006 delivered that for `revisions/` and stopped there. This document takes up
the two places the promise is still owed — the `operations/` directory, which
has no naming convention at all, and `history/skipped`, which is the one file
in a store a person is expected to write by hand and which no command helps
them write.

Both are the same kind of surface: the tool writing for a person rather than
for a reader that will check the result. That is what puts them in one
document, and it is also what limits it. Nothing decided here carries
correctness weight, nothing here needs a format version bump, and a store whose
files are all still named by digest is a correct store that is merely tedious.

## What recording a codebase showed

Historica was recorded into its own repository, which is the first store here
with more than a handful of documents in it. The result:

```
history/revisions/   1 file
history/operations/  116 files
```

`arrange` renamed the revision to `2026-08-20 Initial state.rev` and left the
other hundred and sixteen as sixty-four hexadecimal characters each. So the
folder a person opens is 99% hashes, and the one file that reads well is the
one file they would not need to go looking for.

Two things follow, and only the first is decided here.

The first is that a message cannot fix this. A message names a `.rev` and
nothing else, so better titles, or better prompting for them, improve the
readability of one file in a hundred and seventeen. The missing thing is a
scheme, not a habit.

The second is the shape of an import. Every one of those 116 documents is an
`add`, and an `add`'s operation document is `insert 0` followed by the whole
file with `+` before each line — a verbatim second copy, carrying no
arithmetic against any parent, because there is no parent. The store is 1.1M
against 1.1M of source. That is a question about 0007's document, not about
filenames, and it is deferred below rather than answered as a side effect of
this one.

## The decision

- **`arrange` files operation documents under the revision that names them**,
  as `operations/<the revision's arranged stem>/<path>.ops`, the stem being
  0006's own and the path being where the file sat in that revision.
- **A document two paths claim is named for one of them**, chosen by a rule
  that is arbitrary and deterministic rather than clever: the smallest revision
  digest, then the smallest path.
- **The walk recurses, to any depth, and never follows a symbolic link.**
  `revisions/` and `operations/` are read whole, so a person may file
  documents into directories of their own; a link is found, reported, and
  read past.
- **`historica skip <path>… [--suffix <suffix>]`** writes rules into
  `history/skipped`: an append, never a rewrite, refusing as a whole if any
  rule it was given covers a file the tree already holds.
- **A `skip` rule over a tracked file is refused by `record`**, which 0011
  decided and nothing implemented. It is restated here because it is now true,
  not because it is new.

## Naming an operation document

The directory carries the revision, so the filename is free to be the path:

```
revisions/2026-08-20 Start a journal.rev
operations/2026-08-20 Start a journal/src⁄cli⁄mod.rs.ops
operations/2026-08-20 Start a journal/docs⁄decisions⁄0011-working-copy.md.ops
operations/2026-08-20 Say more/src⁄cli⁄mod.rs.ops
```

The directory's name is the revision's own arranged stem, unchanged and
undecorated, which is what makes the correspondence visible: a `.rev` file and
the directory beside it are spelled the same, and one glance says which
documents belong to which revision. A hundred and sixteen files become a
folder.

The path is not in the revision document for an `edit` — only `add` carries
one — so the tree at each revision has to be materialised to find it. That is
real work `arrange` did not previously do, and it is affordable for one reason:
`arrange` is a manual tidying command that nothing runs in a loop.

**`/` becomes `⁄` (U+2044 FRACTION SLASH), not a space.** 0006 replaces `/` in
a *summary* with a space, and that is right there, where a slash is incidental
punctuation in a sentence. In a path it is structure, and `src cli mod.rs`
throws the structure away in a project where five files are called `mod.rs`.
The character is chosen carefully rather than for looks: it has no Unicode
decomposition, so a filesystem that normalises names to NFD — which macOS does
and Linux does not — cannot make two replicas disagree about the bytes of a
name they both derived. An accented character in a *summary* already carries
that hazard and 0006 accepted it, in the language of "a journal is written in
its author's own language". Introducing a new one deliberately would be
different, and this does not.

**Nesting is what buys the length back.** A flat scheme would have had to spell
the date, the summary, and the path in one 255-byte name, and an earlier draft
of this document budgeted them at 40 and 32 characters to fit — which is to say
it clipped both halves of every name to afford a prefix identical on every file
in the directory. With the revision in the directory, the whole budget is one
path:

```
 180   path, 60 characters at three bytes each
   4   ".ops"
  13   collision suffix, a space and twelve digest characters
 ---
 197
```

The path is clipped to 60 **from the left**, keeping the end and marking the
cut with `…`: the tail of a path is what distinguishes it, where the head is
the directories every sibling shares. `…corpus⁄diffs⁄final-newline-lost⁄parent.txt`
is a name a person can act on.

A collision — two paths in one revision clipping to one filename — appends the
digest prefix, never a counter, for 0006's reason unchanged: a counter depends
on what else is in the directory. Collisions are resolved *within* a directory,
because that is where two names would actually meet.

## A document two paths claim

This is not a corner case. The import produced 120 `edit` lines and 116
distinct digests, because identical content is one document:

```
03f368eb…  tests/corpus/diffs/final-newline-gained/child.txt
           tests/corpus/diffs/final-newline-lost/parent.txt
```

Four documents there, each claimed by two paths, in a store with one revision
in it. A scheme that assumed one path per document would have been wrong on its
first real history.

So the rule: **the smallest revision digest, then the smallest path.** Both
halves are content-derived, so two replicas agree, and neither depends on what
else the directory holds.

Nesting sharpens what this costs. A document can be *mentioned* by one path and
still sit beside the others; it cannot sit in two directories. So a document two
revisions edit identically lives under one of them, and a person opening the
other revision's directory will not find it there. That is the price of a
directory meaning "the documents this revision names", and it is worth stating
plainly rather than discovering.

It is worth being plain that this makes the name incomplete rather than wrong.
The document belongs to both paths; the filename mentions one. The alternative
— naming such a document by digest, so that no name makes a partial claim —
was rejected because it puts the least readable names on the documents a person
is most likely to be confused by, and because a filename here is not a claim
the store relies on. There is one exception, and it is worth knowing it does
not apply: `check` reports `FilenameLies` where a *whole stem parses as a
digest* and the bytes hash to something else. An arranged name does not parse
as a digest, so it makes no claim to be checked against — which is also why
arranging a directory cannot introduce that finding.

Ordering by digest is arbitrary from a person's point of view: the name may
cite a later revision than the one where the content first appeared. The
readable alternative, ordering by `when`, was rejected because 0002 keeps
timestamps out of ordering, and a filename scheme is not the place to quietly
reintroduce them.

## The walk recurses

An earlier draft of this document declined to nest, on the grounds that the
loader read one level and that changing it was a format decision a filename
scheme was not entitled to take. The second half of that was true and the first
half was a reason to fix the loader, not to accept it.

What a flat reader actually did with a nested store is worth recording, because
it is sharper than "the documents are invisible". Materialising failed loudly —
`MissingOperations`, naming the document and the revision that wanted it — but
`check` reported the same absence at `Severity::Note`, in the same class as
`MissingParent`, whose entire meaning is "transport has more to deliver". So
the one command whose job is to say whether a store is sound would have called
a store missing a hundred and sixteen documents *healthy and mid-sync*. That is
the failure this format is least willing to produce, and it is an argument for
recursing rather than an argument against.

**The walk is unbounded, and that is safe because it never follows a symbolic
link.** A tree of real directories cannot contain itself, so there is no loop
to guard against and no depth to cap; `symlink_metadata` rather than `is_file`
is the whole of the guard. Decision 0011 refused a symlink in the working copy
on the neighbouring argument — following one reads somebody else's file under
this name — and a store is not the place to give a different answer. A link
where a document would be is reported as a note, `Unfollowed`, because a person
who made one meant something by it and nothing read it.

Recursing is unusually cheap here, and the reason is 0003's. **Identity is
content**, so extra files are harmless: a backup copy of `operations/` nested
inside it yields the same digests and therefore the same documents, at worst a
`DuplicateContent` note that 0003 already calls harmless tidying; unrelated
`.ops` files become documents nothing references, and nothing reads a document
nothing references. In a store addressed by name, an unbounded walk is how a
`.Trash` folder becomes history. Here it is not.

**`check` walks with the loader, not beside it.** Both call the same function.
A `check` that recursed differently from the loader is how a store passes a
check it should not, and the way to not have that bug is to not have two
walks.

**`arrange` renames where a file sits and never moves it.** A person who filed
a revision into a directory meant to, and a tidying command that undid that is
one a person stops running. This also keeps the property that made a flat
`arrange` safe: renaming is renaming, no file crosses a directory, and no
rename can half-succeed in a way that loses a document.

## `historica skip`

`history/skipped` is a key, a space, and a value. A command that writes one is
convenience and nothing else, and the reason to have it anyway is not typing:

- **It knows what a directory is.** `historica skip target` writes
  `skip target/`, because the trailing slash is the one thing a person leaves
  off and the one omission that silently changes the meaning — `skip target`
  matches a file called `target` and nothing beneath it.
- **It refuses before writing.** 0011's rule below, answered while the person
  is standing in front of the answer, rather than at the next `record`.
- **It cannot write a line the parser would refuse.** Every rule renders
  through the same `Display` the parser reads back.

Three smaller choices, each of which could have gone the other way:

**An append, not a rewrite.** The rules are held parsed, and writing them back
out would produce a correct file with every blank line gone. The parser ignores
blank lines; a person grouping their rules with them meant something by them,
and this is not the command that decides they were noise.

**All or nothing.** A command given four rules, one of which is refused, writes
none of them. Half-applying would leave a person reading the error to work out
which half survived, and the file is short enough to retry.

**Checked against every head, so it never asks for `--onto`.** Every other
command that needs a position refuses when there are several heads and makes
the person name one. This one does not need to: the question is whether *any*
line of work holds a path, and asking it of all heads at once has an answer
when asking it of one would have a question.

With no arguments it prints the rules, as `names` prints the bookmarks.

## A rule over a tracked file is refused

0011 decided this and no code did it:

> **A rule that matches a file already in the tree is refused.** Adding
> `skip drafts/` for a directory history already holds would otherwise make
> those files vanish from the folder's point of view, and the next record would
> spell that as `drop` — a line asking for privacy, silently deleting history's
> copy of what it names.

It is checked in `survey`, against the tree's paths *after* any stated `--move`,
so a `--move` onto a skipped path is caught by the same line. Two consequences
are worth stating because neither is obvious.

**`status` refuses too**, since it shares the survey. 0015 made status collect
the refusals `record` raises, on the argument that status is the command a
person runs *because* the folder is in a state. That argument does not reach
here: this is not a fact about the folder, it is a store file contradicting the
history beside it, which is the same class as a malformed line in that file —
and a malformed line already fails every command, `status` included.

**The way out is two steps**: delete the file, record the deletion, and only
then is the rule sayable. This is 0011's "removing a file from the tree is what
deleting it does", and the message says so. Historica could tell a deleted file
from a skipped-but-present one by looking at the filesystem, and deliberately
does not: the rule is about what the tree holds, and a rule that changed its
mind depending on what the folder happened to contain that minute would be a
worse thing to explain.

## Rejected alternatives

**Better default titles, or prompting for them.** The diagnosis this document
opens with. A message names one file per revision, and the readability problem
is a hundred and sixteen files with no scheme at all.

**Leaving `operations/` as digests, and putting readability in `log` and
`show`.** Defensible, and it is what the store does today. Rejected because
0003's promise is about the folder rather than about the commands: a person who
can read a history without the tool installed is the property, and 99% hashes
is not that person's folder.

**A flat `YYYY-MM-DD summary — path.ops`.** This document's first scheme, and
what it looked like before nesting was available. It spent most of a 255-byte
name on a prefix identical for every document in a revision, clipped both the
summary and the path to afford it, and produced a directory where an import
shows a hundred and sixteen names differing only in their last few characters.
Nesting says the same thing once, in the directory.

**Path first, `src⁄working.rs/2026-08-20.ops`** — a directory per file rather
than per revision. Sorts every change to one file together, which is the better
answer to "what happened to this file". Rejected because `revisions/` sorts by
date and the two directories should sort alike, and because a file's history is
what `log` and `show` are for, where "what did this revision do" has no other
reading.

**The last path component only.** Shorter, and it collides constantly — five
`mod.rs` in `src/` alone — which would put a digest suffix on the names it was
supposed to shorten.

**Leaving the loader flat and declining to nest, and the staged plan that
followed it.** An earlier draft shipped the recursing reader and left nesting
for later, on the argument that a store should not require a reader that
readers might not have. That argument is real and it does not apply yet: there
is one reader, it recurses, and the cost of waiting was carrying a flat naming
scheme nobody wanted into a format that would have had to keep reading it.

**Leaving the loader flat.** The first draft's answer.
Rejected once the flat reader's actual behaviour was looked at: it does not
merely fail to see the documents, it lets `check` call their absence ordinary.

**Naming a shared document by digest.** Above: the least readable name on the
document most likely to confuse.

**A `--dry-run` on `skip`.** `skip` prints what it wrote and the file is three
lines long; the preview is `cat`.

## Consequences

- `store::walk` is the one enumeration of what a store's directories hold, and
  the loader, `check`, and `arrange` all call it. `Walk` keeps files and links
  apart because the loader ignores what `check` reports.
- `check` gains `Unfollowed`, a note, and reports it for `revisions/` and
  `operations/` alike.
- `arrange` renames in place rather than into the top of the directory, so a
  store a person has filed stays filed.
- `arrange` gains operation documents, and with them a tree materialisation per
  revision, an `operations/` directory per revision, and the removal of any
  directory it empties — `remove_dir`, which refuses a directory holding
  anything, so a directory a person keeps something else in survives. Its determinism rule now covers two directories rather than one,
  and the rule is unchanged: content-derived suffixes, never counters.
- `historica skip <path>… [--suffix <suffix>]` is the command, dispatched
  beside `name` because `skipped` and `names/` are the two mutable synced files
  in a store.
- `Store::append_skipped` is the writer; `Rule` becomes public and renders the
  line the parser reads back, so a rule cannot be written in a spelling that
  cannot be read.
- `record` and `status` refuse a `skip` rule covering a tracked path, which is
  0011 implemented rather than a new decision.
- Tests worth naming: a directory given without a slash acquires one; a rule
  already stated writes nothing and says so; a refused rule in a command of
  four writes none of the four; blank lines in a hand-written `skipped` survive
  an append; a rule over a tracked file is refused by `record` and the deletion
  route out of it works; two paths sharing one operation document produce one
  filename, deterministically the same one on a second machine; and an arranged
  operations directory arranges to itself the second time.
- The README's front-end paragraph gains `skip`, and its `working` paragraph
  gains the refusal.
- Two tests stopped being about what they claimed and had to move out of
  `CARGO_TARGET_TMPDIR`. Both assert that no store is above a directory, and
  both put that directory under `target/` — which is inside a checkout that
  now holds a `history/`, this being a tool people record their own work with.
  Discovery walked up and found it. The suite is not hermetic against its own
  repository being a store, and a test that asserts an absence has to be
  written somewhere the presence cannot reach.

## Deferred

**What an import should be.** The question this document opened with and did
not answer: an `add`'s operation document is the whole file with `+` before
each line, so recording a codebase writes a second copy of it and produces one
opaque document per source file. Whether 0007's document deserves a shape for
"this content arrives whole" — and what that would mean for forgetting, which
0014 built on the payload of an operation document — is a format question,
needs a format version, and should be decided on its own terms.

**A second reader.** Nesting means a store now requires a recursing reader to
be read correctly, and a reader that does not recurse calls the result healthy
rather than refusing it. Today there is one reader and it recurses. If a second
is ever written — the format's whole promise is that one could be — this is the
thing it must be told, and the fact that a flat reader fails *quietly* is the
reason it belongs in a document rather than in a comment.

**Whether `arrange` should run itself.** Nothing here is automatic, and a
person who records a hundred revisions has a hundred hashes until they ask.
The reason to leave it manual is that renaming under a sync tool is the thing
most likely to produce conflicted copies, and the reason to reconsider is that
a scheme nobody invokes is a scheme nobody has.
