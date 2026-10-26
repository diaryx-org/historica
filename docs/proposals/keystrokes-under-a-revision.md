---
title: Keystrokes under a revision
part_of: '[Proposals](/docs/proposals/proposals.md)'
status: draft
created: 2026-10-26
description: Keep the steps an editor makes between a revision's parent and the revision as an optional trail that checks itself by replay, beside the revision and never in what it holds or how it merges
---

# Keystrokes under a revision

## Status

Draft, argued 2026-10-26. Nothing here is built. Sources: historica at
`2fd34e7`, twig `main` at `87ed1e3` (diaryx-org/twig#18, #19, #20 and the
three fixes after them), leaf's open diaryx-org/leaf#25 at `bb217afb`, and
leaf's draft proposal *An edit format shared by leaf and the core*
(diaryx-org/leaf#23), called **the edit-format proposal** below.

It answers one question: should the history an editor makes while a person
types, which is finer than a revision, be kept under historica's revisions,
and if so how? The short answer is **yes, as an optional, self-checking
trail beside a revision, and never as part of what a revision is or how it
merges.**

## What is here already

- **historica's revision is a checkpoint.** A revision states what it did to
  each file as line operations against its parents
  ([0007](/docs/decisions/0007-content-and-merge.md)). `record` makes them by
  diffing the file as it stands against the parent state
  ([0009](/docs/decisions/0009-diff.md)). Concurrent revisions merge by
  Eg-walker with Fugue's ordering. Nothing finer than a line is stored, and
  no operation id, version vector or tombstone is written down.
- **0007 left the finer case open on purpose.** "A document edited by
  several people *at once* is a leaf-document problem with a finer operation
  vocabulary, and this decision does not close it. It fixes the granularity
  of version control, not of typing."
- **twig now reports every edit as ops** (twig#18, merged). `Op` is
  `Retain(n)`, `Insert(text)` and `Delete(n)`, in UTF-8 bytes from the start
  of the text, in one canonical spelling. `Editor::last_ops`, `Op::diff`,
  `Op::apply` and `Op::compose` are public. twig's undo step now holds its
  edit's inverse ops, not a copy of the page.
- **leaf hands those ops to its host** (leaf#25, open). `Doc::take_ops`
  returns every change since the host last asked, typing, gestures, undo,
  `replace_source` and reload, as one list against the text the host last
  took.
- **The edit-format proposal plans the live layer.** An edit becomes an
  event with a name `(agent, seq)` and parents. The editor and the Diaryx
  worker each hold a replica of the open page and merge by a shared,
  Verus-verified Eg-walker crate. Its decision 7 says: "The graph is
  discarded when the page settles, and historica records a revision from the
  text, as now."
- **A reserved store directory can travel.**
  [0053](/docs/decisions/0053-room-for-another-tool.md) lets a directory at
  the store root declare a travel class. `claims/` is `travels-and-unions`:
  immutable, digest-named files that `export` carries and `receive` unions.

So the pieces are now in place to keep the finer history, and the
edit-format proposal currently throws it away at settle. This proposal says
what of it is worth keeping, and where.

## What a person gets from it

- **Replay of the writing.** Step through how a page came to be between two
  saves, not only what each save held.
- **Undo that survives a restart.** leaf can build its undo stack from the
  last session's steps when it opens the page again.
- **Fewer revisions.** A host that records a revision every few seconds so
  that nothing is lost makes the flood that
  [0082](/docs/decisions/0082-squashing-a-run.md)'s `squash` exists to tidy.
  With the steps kept beside the revision, a host can record one revision
  when the page settles and lose no detail.
- **Material for an assistant.** An AI that reads a page's history can see
  what was tried and taken back, which a checkpoint does not show. (That is
  also the privacy cost below.)

## The proposal

### What does not change

- **A revision stays a checkpoint.** Its line operations stay the only thing
  `cat`, `diff`, `blame`, `merge` and `update` read. No step, name or
  timestamp from the editor takes part in a merge.
- **No live event graph is stored.** The `(agent, seq)` names of the
  edit-format proposal stay in memory. 0001 calls a stored change id an
  unverifiable claim, and 0007 writes no operation ids; a persisted live
  graph would be both. The edit-format proposal already made this choice
  for that reason, and this proposal keeps it.
- **The item stays a line.** 0007's readability argument for line items
  holds unchanged for the operation document.

### A trail: the steps between a revision's parent and the revision

A **trail** is one document for one file of one revision. It lists, in
order, the steps by which the file went from its text at the revision's
parent to its text at the revision. A step is one list of twig ops: what
the host took with `take_ops`, or one undo step. It holds the facts a
replay needs, and nothing more.

A sketch of its spelling (the decision that builds it fixes the spelling):

```
historica-v0
revision 9c1e40…
file q26ctzx

step
retain 1208
insert
+word
\ no newline
step
retain 1210
delete 2
```

- The preamble and the blank line are 0004's, as in every document.
- `revision` and `file` say what the trail describes. The revision does not
  name the trail.
- Ops are twig's, in the canonical spelling twig#18 fixed. Inserted text
  uses 0007's content lines, so line terminators and carriage returns
  survive exactly.
- **No times by default.** Keystroke timing identifies a person (it is a
  biometric), and a journal's history travels. A host that wants times asks
  for them, and each step then carries an offset from the trail's first.

### A trail checks itself

The revision does not name its trail, so a trail is not covered by any
digest a revision holds. Instead it is checked by what it claims: **applying
its steps in order to the file's text at the revision's parents must give
the file's text at the revision.** A trail that fails is ignored by every
reader and reported by `check`. It cannot change what a revision holds,
because nothing reads content from it.

That is what lets a trail be added after the revision, by another tool, or
not at all, and dropped without rewriting anything. A revision recorded
without a trail is exactly as it is today.

A trail is only for a revision with **one parent**. A merge's text is the
walk's result, not a person's steps, so a merge has no trail. (A live
session that merged another device's events is linear at the worker: the
worker applied each event as a splice. Its trail is the steps as the worker
applied them, against the one parent the session started from.)

### Where a trail is kept

`trails/<digest>.trail` at the store root, named by the SHA-256 of its
bytes, in a new reservation under 0053. That needs a decision document and a
registry line, as 0053 requires.

Its travel class is open question 1. `travels-and-unions` lets a person's
other devices replay and undo. `local-only` keeps what a person typed and
deleted on the device where they typed it.

### Who writes one

- **The Diaryx worker, at settle.** The edit-format proposal's decision 7
  becomes: the worker writes the steps it applied as a trail, records the
  revision, and then discards the graph. Until the worker holds a replica,
  the page can collect leaf#25's `take_ops` lists itself and hand them over
  with the body.
- **historica's API.** `record` takes, for any file, an optional list of
  steps, checks them as above, and files the trail after the revision's
  content (the order 0011 keeps). The CLI gains nothing to write one, since
  a shell has no keystrokes.

### Who reads one

- `historica trail <revision> <path>`: the steps, one per line, with what
  each inserted and deleted.
- `historica cat <revision> <path> --step <n>`: the file after step `n`.
- leaf, through the API: the inverse of each step, to rebuild an undo stack.

### How a trail meets the other acts

- **Forget** ([0014](/docs/decisions/0014-forgetting.md)) is the hard one. A
  trail holds text that **no revision holds**: what a person typed and
  deleted before they saved. Forgetting a run of lines must also drop every
  trail of that file whose revision the forgetting reaches, because a trail
  cannot be redacted and still check itself. A `forget` of trails alone,
  keeping the revisions, is the act for "keep what I wrote, not how".
- **Prune** removes a revision's trails with it.
- **Squash** ([0082](/docs/decisions/0082-squashing-a-run.md)) of a linear
  run where every revision has a trail for a file writes the squash a trail
  that is their steps in order. Otherwise the squash has none for that file.
- **Amend** gives the new revision no trail unless the writer supplies one;
  the old trail still describes the old revision.
- **`check --complete`** does not ask for trails. A store without them is
  whole.

### The decomposition, as a separate question

0009 says the line decomposition "must be recorded once by the person who
made the edit". The editor now knows what the person did, so `record` could
lift the composed ops to line operations rather than diff the two texts.
This proposal does **not** recommend that yet. 0009's goal is decompositions
that *merge well*, not ones that are faithful, and they differ: a line
deleted and typed again composes to a delete and an insert, where the diff
keeps it, and a concurrent edit to that line then conflicts. It is worth
measuring on real trails against `Algorithm::Histogram`, once trails exist
to measure. It needs no format change either way.

### Finer merges, as a later question

The cost 0007 states plainly, that two people who edit one line at once get
both lines, can be lowered without trails. The shared Eg-walker crate is to
be generic over the item. A merge could split a contested region's lines into
characters and walk them, with names derived from the line's name and an
offset, so nothing new is stored. 0007 explains why a merge rule may change
for future merges without changing any recorded one. Whether it should is a
judgment about prose that 0007 made against it ("a sentence merged
character-wise from two intentions is usually nonsense wearing the shape of
sense"). It is open question 3, and waits for the crate.

## Costs

- **Size.** Unmeasured. A step is tens of bytes. Typing coalesced into twig's
  undo steps is a step per word or so, which for a thousand-word session is
  of the order of tens of kilobytes, beside about 4.5 KB per revision on
  historica-git's store. Uncoalesced keystrokes would be several times that.
- **Privacy.** A trail keeps what a person deleted before they saved. That is
  the feature and the risk at once, and it is why trails are opt-in, why
  times are off by default, and why `forget` must reach them.
- **One more document type,** with a parser under 0004's contract, and one
  more reservation.
- **The edit-format proposal changes,** in its decision 7.

## Rejected alternatives

**A revision for each step.** No new document, but every keystroke would be
a revision document, which is two orders of magnitude more than a trail
step, and the history a person reads would be the flood 0082 tidies.

**Character items in the operation document.** 0007 rejected this for
readability, and the reason stands.

**The live event graph on disk, with its names.** Operation ids and change
ids in the store, contrary to 0001 and 0007, and the unbounded metadata 0007
rejected CRDTs for. A Loro or Yjs document as the store is rejected in
[`docs/loro.md`](/docs/loro.md) for recovery.

**The revision names its trail, by a header.** A trail would then be covered
by the revision's digest, but could not be added later, dropped, or forgotten
without rewriting the revision, and a revision would no longer verify without
it.

**A trail as cache.** `cache/` is `derived`: deletable without loss. A trail
cannot be derived from anything else, so deleting it loses information.

## Open questions

1. **Does a trail travel?** `travels-and-unions` (replay and undo on every
   device) or `local-only` (what a person deleted stays on the device that
   saw it). Adam's to decide; it may be a per-library setting.
2. **What is a step?** Each `take_ops` list (about one a frame), or each
   twig undo step (coalesced typing). The second is smaller and is what undo
   needs; the first is what replay at full detail needs.
3. **Character-level merge of contested lines,** as above.
4. **Whether this is historica's or a side tool's.** 0053 allows a tool such
   as `historica-trail` to own `trails/`. The self-check needs only the
   public API. Keeping it out of historica keeps the core smaller; keeping it
   in lets `forget` and `prune` reach trails without a hook.

## Tasks this would spawn

In order, each in the repository whose code it changes:

1. **historica:** a decision for the trail document and the `trails/`
   reservation, after open questions 1, 2 and 4.
2. **historica:** parse, write and check trails; `record` takes steps;
   `forget` and `prune` reach them.
3. **historica:** `trail` and `cat --step`.
4. **leaf:** the edit-format proposal's decision 7 amended; the page hands
   its steps to the worker at settle.
5. **diaryx:** the worker writes the trail when it records.
