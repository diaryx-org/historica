# 0066 — Forgetting a payload

0014 built forgetting and deferred one case in three sentences:

> **Binary content**, which 0008 gives a shape and no implementation. A binary
> file has no items to preserve, so forgetting one is nearer to prov's case:
> the whole payload goes and only its digest and length remain.

0017 then went further than a deferral usually does. It gave payloads their
home, worked out what redacting one would mean, and wrote the document out —
`forgets`, `length`, nothing else — before deferring the whole subject again
under the heading "Forgetting, still." 0044 wrote down what `check` would owe
when it landed. Every one of those documents is right, and between them they
left a feature that has been designed twice and built never.

What was actually missing was never the shape. It was the answers around it:
what a reader says when a file will not materialise, what `check` calls an
absence somebody made, how a person spells the request for a file with no
lines to name, and whether any of it costs the format anything. This document
settles those and builds it.

The thing worth saying first is that the deferred case is the easy one. 0014's
machinery is elaborate because a file of lines has a shape that has to survive
its own redaction — positions, counts, terminators, item identity, and a
marker per destroyed item, all so that replay and merge never notice. A
payload has none of that. 0017 gave it no items, no grammar, and no chain, so
there is nothing to preserve and nothing to reconstruct. What stands in for a
forgotten payload is not a copy of anything. It is a statement.

## The decision

- **A forgotten payload is replaced by a document of two headers.**

  ```text
  historica
  forgets 8aea125239f85ba50f847a76880a4de4ac5c60326270c6f7a2c019b789f6e6ff
  length 69
  ```

  0017's spelling, unchanged. No separator and no body, because a payload has
  no items and there is nothing for a separator to introduce.

- **It is a document like every other**: it opens with the preamble, it is
  stored under the digest of its own bytes, and it is named by nothing — the
  revision's `bytes` line still names the payload, and a reader that cannot
  find those bytes looks for a document that says it `forgets` them. That is
  0014's arrangement, applied to a file that was never a document before.

- **`length` is shape, and shape survives.** A redaction keeps every count it
  can (0014); a payload's only count is how many bytes there were, so that is
  what is kept. It is also the one thing a person is owed when a file will not
  open: *destroyed, and there were 69 of them* is an answer, and *gone* is not.

- **The `length` header is the dispatch.** `operations/` now holds three
  grammars under one suffix, and each says which it is in its own bytes: a
  body opening with a position is an operation document (0007), a body opening
  with `keep` or a bare `insert` is a resolution (0032), and a header block
  carrying `length` is this. No other document has one.

- **This grows the vocabulary and costs no format version.** 0004's rule, as
  0047 restates it: a reader's vocabulary only ever grows, and only *retiring*
  a spelling breaks a reader. Nothing is retired here. `forgets` keeps exactly
  the meaning it had, `length` was never a key in any grammar, and every
  document written before today parses today unchanged.

- **A payload is forgotten once and everywhere.** Content addressing already
  did 0014's walk: a payload is quoted by its digest, wherever and however
  often it is named, so destroying the one file destroys every quote of it.
  The honest counterpart is that a file of bytes is *replaced* whole, so each
  version of it is its own payload under its own digest and is forgotten on
  its own — and the command says how many others there are rather than
  leaving a person to assume.

- **The extent is derived, never stated.** `historica forget <target> <path>`
  with no `--lines` forgets a payload whole; `--lines` is how a file of lines
  is forgotten and is required there. A file's kind was fixed when it was
  added (0017), so the tool already knows which of the two is even askable,
  and asking for the other is refused by name with the spelling that would
  have worked.

- **A forgotten payload does not materialise, and says which absence it is.**
  `cat`, `update`, and `export` refuse the file, naming the document that
  destroyed it and how much was destroyed. *Destroyed* and *not yet delivered*
  are different answers to a person, and they are now different answers from
  the tool.

- **`check` calls it forgotten rather than missing**, which is exactly the
  branch 0044 wrote down and waited for.

- **Nothing else changes.** Compliance, transport, resurrection, and pruning
  were all written over "what does this document forget?" rather than over a
  grammar, so a third grammar reaches them for free — which is the argument
  for having answered the question that way in the first place.

## What a payload has to survive

0014 earned its design by looking at what a reader actually consumes from an
operation document, and finding that only some of it was payload. Ask the same
question of a payload and the answer is nothing.

`replay` never opens one for a file of bytes: 0017 says such a file has no
chain, because its content is stated whole by whichever revision states it.
`merge` never orders one: there are no items to name, and a concurrent
replacement is a divergence reported rather than a merge performed. `tree`
carries the digest and not the bytes. Nothing downstream of a `bytes` payload
reads a byte of it except the person it is handed to.

So the document that stands in for one has no work to do but be *found*, and
say what happened. Both are true of two headers.

## Why `length` is kept

Destroying it would be free and would buy nothing.

A file's size is not what a person redacts. What they are removing is a
photograph, a key, an export — and the fact that it was 2.4 megabytes is
already recorded, in the sense that everything about the revision around it is
already recorded: its path, its author, its time, and its place in the graph.
0014's "what forgetting cannot hide" is a list this joins rather than
disturbs, and it gains one line: **size**.

What keeping it buys is the difference between a tool that can say how much
was destroyed and one that can only say that something was. It also gives the
document the one property a redaction should have and a bare `forgets` would
not: two replicas that forget the same payload write the same bytes, so their
redaction is one file rather than two, and syncing them is set union with
nothing to reconcile.

There is a case it cannot serve, and it should be said out loud: a person for
whom the *size* is the secret has no answer here, and never did. The revision
document names the file and its path; the answer to a filename that is itself
sensitive is 0014's deferred path case, and the answer to a size that is
itself sensitive is not to record the file.

## Three grammars, one suffix

0032 gave `operations/` two grammars and told them apart by their bodies. This
adds a third, and it cannot be told apart the same way, because its body is
empty and *empty* is not a shape a strict reader should trust: a file that was
truncated after its headers looks exactly like one, and a reader that guessed
would accept half a document as a whole one.

So the dispatch is a header rather than an absence. A `length` line in the
header block says these bytes are this grammar and nothing else, which means a
file claiming it is held to *this* parser's strictness — headers in order,
both present, no `result`, nothing below them — and every one of those
refusals names what to do. A truncated operation document is still refused as
a truncated operation document, by the parser that was always going to refuse
it.

## One destruction reaches every quote

The hardest part of 0014 is that an item forgotten at its insert is still
legible in the delete that quoted it back, so `forget` has to replay a file's
whole history to find every document holding a run. None of that applies here.

A payload is named by its digest, and the file *is* its digest. Two revisions
that state the same bytes name one payload; a file added, dropped, and added
again is the same payload twice; a `keep` in a resolution that points into a
`text` payload points at the same file. Destroying it destroys all of them at
once, because there was only ever one of them. Content addressing did the walk
in advance.

The same fact read the other way is the thing a person must be told. A file of
bytes is replaced whole, so `photo.png` at three revisions is three payloads,
and forgetting the one at a named revision leaves the other two legible. That
is 0014's rule that redaction is per item rather than per file, arriving where
it is least expected — nobody thinks of "the photograph" as three things — so
`forget` counts the others and says so, and does not quietly reach revisions
the person did not name.

## What cannot materialise

Here is the one place a forgotten payload is worse than a forgotten paragraph,
and no wording makes it smaller.

A forgotten run of lines still materialises: the file comes out with
`\ forgotten` where the text was, every revision after it still replays, and
the marker is outside the item grammar so nothing can mistake it for content.
A forgotten payload has no such marker available, because there is no byte
sequence outside "the bytes of a file". Any placeholder — an empty file, a
one-line note, a grey rectangle — would be content nobody wrote, which is the
sentence 0008 asks a merge to be judged by and which applies here word for
word.

So the file does not come out at all. `cat` refuses it, `update` refuses to
write it and leaves the folder alone, and both say what happened and what to
do about it: record the `drop` that makes the file's absence a fact of the
history rather than a hole in it. A person who forgets an attachment and wants
their working copy to stop asking for it is one revision away from that, and
that revision is a thing they state rather than a thing the tool infers.

## What a person reading the store by hand sees

`forget` files the stand-in where the payload was, at the payload's own name
with the document suffix after it — 0016 files what a revision did under that
revision at the path each file had, and 0017 puts payloads there under the
file's own name, so this is those two rules kept rather than a new one:

```text
history/operations/
└── 2026-08/2026-08-25 Start/
    ├── notes.md                 payload — the entry
    └── photo.png.ops.txt        the document that says what became of the photograph
```

Open it and it says which digest went and how many bytes it held. The
extension is what tells a document from a payload (0017), so it is kept
whatever else happens to the name, and a name already taken sends the document
to its digest instead — the one name nothing else can claim.

## Rejected alternatives

**Destroying the payload and writing nothing.** The cheapest possible design,
and it is the failure 0044 spent a whole document on: an absence with nothing
behind it is indistinguishable from a payload still in flight. `check` would
call a completed redaction a shortfall, transport would fetch the bytes back
from the first replica that still had them, and a copy holding the original
would never learn it was supposed to comply. The document is what makes the
destruction a recorded fact instead of a hole, which is 0014's whole argument
about why receiving one may destroy bytes at all.

**An operation document with no operations** — reuse 0007's grammar, carry
`forgets`, leave the body empty. No third grammar and no dispatch question.
Rejected because it says something false: zero operations is a claim about a
file of lines, not the absence of a claim, and the operation parser refuses an
empty body for good reasons it should keep. The place where a payload *is* an
operation document is the `text` case, and that is 0017's point rather than a
loophole: a text payload is exactly the `insert 0` of its lines, so it is
already forgotten as one, with items, markers, and item identity intact. Two
spellings for one act is the thing this format spends its strictness against.

**Omitting `length`**, leaving a document of one header. Simpler, and it
throws away the only shape the file has, against 0014's rule that shape
survives. It also makes the dispatch worse: "a `forgets` with no body" is a
description a truncated file fits, where "carries a `length`" is a description
only this grammar fits.

**Forgetting every version of a file at once.** What a person who types
`forget … photo.png` may well mean. Rejected on 0014's rule that redaction is
per item: a command that destroyed content at revisions nobody named would
destroy content nobody looked at, and the person who wanted exactly that can
run it once per revision and see each one. Saying how many others there are is
the honest half of this, and it is done.

**A placeholder where the payload was** — an empty file, or a note in its
place. Rejected above: `\ forgotten` works for lines because it is outside the
item grammar and no file can hold it, and there is no outside for bytes.

**A renamed payload rather than a document** — mark the file's *name* and
leave nothing in it. Rejected because 0003 makes a name presentation: a fact
stated in a filename is a fact `shasum` cannot check and `arrange` may
rewrite, and the whole point of a forgetting document is that it is a file
whose bytes say what happened.

## Consequences

- `format` gains `ForgottenPayload` — two headers, parsed strictly and written
  canonically — and `is_forgotten_payload`, the dispatch every reader of
  `operations/` now makes. `ParseErrorKind` gains one refusal, for a body
  under a document that can have none; the rest reuse the refusals the other
  grammars already have.
- `store::Body` gains a third variant, and `Body::forgets` answers for it. The
  callers that were written over that question — `prune`, `offer`, `fetch`,
  `receive`, `export` — gain a match arm and nothing else.
- `Store` gains `forgotten_payload(digest)` and `insert_forgotten_payload_at`.
  The catalogue records what this grammar forgets exactly as it records what
  an operation document forgets, so finding a stand-in stays one read.
- `MaterialiseError` gains `ForgottenPayload { payload, by, length }`, which
  `content_at` answers with where it used to answer `MissingPayload`. `update`
  refuses the file and names the `drop`.
- `check`'s `bytes` branch consults the standing set: a named payload nothing
  delivers is `Forgotten` where something stands in for it and `MissingPayload`
  where nothing does, and a payload held beside a document that forgets it is
  `Resurrected`. Completeness counts a stand-in as an answer, since the name
  can be answered. This is 0044's prediction kept, and its witness rule
  inherits the right behaviour without being touched, because that rule is
  stated over the findings `check` makes rather than the absences it sees.
- `Forgetting` gains an `Extent`, so the library states which of the two acts
  it means rather than passing a span that a file of bytes has no use for.
  `forget --lines` on a file of bytes, and `forget` without one on a file of
  lines, are each refused with the other spelling; a link is refused with
  0014's deferred path case, which is what it is.
- The corpus gains `whole/forgotten/`: the stand-in for the photograph 0017's
  corpus files, and five invalid documents, one per stated reason.
- `format.txt` gains the grammar and the sentence a person needs when the file
  will not come out.

## Deferred

**Where a stand-in is filed, generally.** 0014 said `arrange` should name a
forgetting document after the revision and file it stands in for, and it never
has: a forgetting document is named by nothing, so `arrange` leaves it where
it is and `export` writes it under its digest. This document files *its* own
stand-in at the payload's name because `forget` knows the path it just
destroyed, which leaves the readable name a thing one command produces rather
than a thing any of them can reconstruct. Doing it properly means teaching
`arrange` to name all three grammars of stand-in from what they forget, which
is one job worth doing once rather than a third of it done here.

**Two stand-ins that disagree about a length.** Nothing this tool writes can
produce them — the length comes from the bytes, and they are the same bytes —
but a hand-written store may hold both, and no reader can adjudicate, because
the file they describe is gone. The first is used and nothing is reported. If
that ever needs an answer, the answer is a `check` note, not a rule.

**Forgetting bytes this store never held.** The stand-in states a length, and
a length can only be measured from the bytes, so a replica that never received
the payload cannot write one. It refuses and says so. This is the same shape
as `MissingQuoted` for lines — forgetting preserves what a document said, and
what it said has not arrived — and the fix is the same: receive it, or wait
for the forgetting document somebody else will send.

**Forgetting a path**, which is 0014's deferral and is untouched. A file whose
*name* is the sensitive thing is not helped by any of this.
