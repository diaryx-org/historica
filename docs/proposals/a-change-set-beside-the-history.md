---
title: A change set beside the history
part_of: '[Proposals](/docs/proposals/proposals.md)'
status: implemented
created: 2026-10-29
updated: 2026-10-29
description: 'A change set as historica''s own: an opening revision that records nothing and carries the title, a line of ordinary revisions on it, and shared bookmarks under change-sets/<id> pinning the tip and each decision, so the record travels with the store and any tool can propose a line and have it accepted, by a merge, or declined, by a tombstone'
---

# A change set beside the history

## Status

Implemented 2026-10-29, unreleased, as decision
[0091](/docs/decisions/0091-a-change-set.md), which is the authority from now
on.

Adam settled the one question that changes what he gets, on 2026-10-29:
**accepting is a merge whose parents include the change set's tip.** So
the assistant's steps become part of the accepted history: `log` lists them,
`blame` credits the assistant with the lines it wrote, and the person's
merge vouches for them. The other choice was a fresh snapshot of the
person's that copies the result in, which is what Diaryx does today. It
would have made the Diaryx follow-up smaller, and credited every accepted
line to the person.

## What happened

Diaryx's assistant change sets (`diaryx mcp`, `diaryx changes`) are a line
of unsigned revisions in the library's historica store. Each carries
`diaryx.change-set: <id>`, and the line waits beside the accepted head.
Diaryx sync carries the revisions to every device. It does not carry the
change set's *record*: its title, author, base, and whether it is open,
submitted, accepted or declined. That record is a small file in the
device's caches, `caches/assist/<digest>/<id>`, which `Line::write` writes
and nothing sends anywhere.

So the Diaryx app on a phone cannot list a change set that `diaryx mcp`
proposed on the Mac, or decide one. Neither can the app on the same Mac,
whose caches directory differs from the CLI's. The revisions arrive, and
nothing says they are a proposal, what it is called, or whether somebody
already declined it.

The revisions travel and the record does not. That says where the record
should go: into the store, as things the store already carries.

## What a change set is

Strip Diaryx's vocabulary off and what is left is general. Somebody, a
person or an assistant or a script, proposes a line of work against some
revision. It has a title. It grows one revision at a time. At some point
its proposer says it is finished. Somebody else takes it in, or turns it
down. Historica-git would want the same thing for a pull request
imported from a forge, and the historica CLI wants it for a person who
works on a laptop and reviews on a desktop.

Every one of those facts already has a spelling in this format:

| Fact | Spelling |
| --- | --- |
| The title, the proposer, when, the base | An **opening revision**: parents are the base, records nothing, message is the title, author and `when` are the proposer's |
| Its identity | The opening's **change ID**, minted as every change is |
| Its steps | Ordinary revisions, each on the one before, the first on the opening |
| Where it ends | A shared bookmark, `change-sets/<id>`, **pinning** the tip |
| Finished | `change-sets/<id>/submitted`, pinning the tip as submitted |
| Accepted | A **merge** whose parents include the tip, pinned by `change-sets/<id>/accepted` |
| Declined | A **tombstone** abandoning the opening and every step (0013), pinned by `change-sets/<id>/declined` |

Nothing in the format's grammar changes. A bookmark is still one line and
an optional `private`. A revision is still a revision. What is new is a
directory of names whose shape means something, and three rules about how
those names move.

## Why an opening revision

The title has to live somewhere every replica receives and nobody can
disagree about. A bookmark cannot hold it. Decision 0062 spent a section on
why a bookmark file is a target and an axis and nothing else, and a title is
mutable text in the one directory 0006 calls a store's whole conflict
surface. A dotted header on the first step would hold it, but then the
change set would not exist until its first step, and `diaryx.title` is
Diaryx's word, which historica cannot read (0065). A new store directory
would hold it too, at the price of teaching `check`, `export`, `receive`,
`offer` and `fetch` a new kind of file.

A revision that records nothing already exists: 0013's tombstone, whose
message is the whole of what it says, which is why 0013 makes the message
required. An opening is the same shape facing the other way. A tombstone
says *this work is gone, and here is why*. An opening says *work is coming,
and here is what it is for*. jj users will know it as a change that is
described before it is filled. The message is required for 0013's reason.

The opening also gives the change set an identity for free. Its change is
minted, so the change ID is the change set's id, and `change-sets/<id>` is a
name nobody else can mint by accident. And the line has a first revision
whose parent is exactly the base, so the base is a fact of the graph rather
than a field somebody wrote down.

## Why pins, and not change bookmarks

A bookmark naming a change follows the work: `record` moves it onto any
revision whose parent is the change's current revision (0011). That is
right for `main` and wrong here, in two ways.

Accepting is a merge whose parents include the tip. A change bookmark on the
tip would follow the merge, then every revision the person recorded on top
of it, and the change set would end up pointing at the person's own head.
And a reviewer reads a tip. If the proposer amends it after the review, a
change bookmark would quietly point the acceptance at a revision nobody
read. A pin names what was there.

So each of the four names pins a revision. Pins don't drag, and one rule
gives back the convenience a change bookmark had: **recording a revision
whose only parent is an undecided change set's tip is that change set's
next step, and moves the pin onto it.** A merge naming the tip is not a
step, because that is what an acceptance looks like. A revision recorded on
the tip of a change set already decided is not a step either.

## How a change set converges

The revisions union, as they always have. The names are where two replicas
can disagree, and the rule is as narrow as the facts allow:

- **The tip and `submitted` move forward.** Two readings where one is in the
  other's ancestry come to the one further along, on both sides. That is
  0088's forward rule with the follow condition removed, because a copy
  holds a proposal rather than follows it. Two readings neither of which is
  behind the other mean two replicas each added a step the other has not
  seen. That is a conflict, as it is for any bookmark.
- **The decision names are written once.** `accepted` and `declined` never
  move, so two readings that differ are two acceptances, or two declines,
  of one change set. Somebody did it twice. That is a conflict, and it is
  real.
- **An acceptance outranks a tombstone.** Two replicas can decide one change
  set two ways before either hears of the other. Then both names arrive, and
  they don't conflict, because they are different names. The tombstone
  supersedes the line's revisions, but those revisions are still in the
  ancestry of the merge, so the accepted history holds the change set's
  content however it was declined. *Accepted* is the true description, and
  `declined` stays readable so that a tool can say so.

`receive` applies these rules, and `fetch` applies the first one beside
0088's. A host that syncs by inserting documents, as Diaryx does, applies
them through `change_set::reconcile`. That is the same function `receive`
calls, so the two can't drift apart.

## Why accepting is a merge

This was Adam's question, and the merge is what makes the rest honest.

A merge makes the decision a fact of the graph, not of a name. A replica
that has the merge and not yet the name can still see the line is in. With
a snapshot, nothing in the graph links the acceptance to the change set.
`blame` (0038) credits each line to the change that wrote it, so the
assistant's lines stay the assistant's. And 0046's claim over a revision
covers the ancestry behind it, so a person's signature on the merge is a
signature over the steps it took in. That is what accepting means.

When the person's head has not moved since the change set began, the merge
names the base and the tip, and the base is an ancestor of the tip. That is
a merge with nothing to resolve, which `record` already allows: *a merge
that states nothing still says something*. Here it says the line was taken
in, and by whom.

## Why declining is a tombstone

0013 already has the act: supersede a run ending at a head with a revision
that records nothing and says why. The opening and every step are a run
ending at the tip. The change set's change becomes `Abandoned`, the content
falls out of the ancestry with nothing undone, and `prune` may later take
the superseded revisions off a disk that does not want them. The tombstone
stands where the opening stood, on the base. Its parents are the opening's
parents. So the abandoned work is gone from every descendant, and nothing
is left that a person has to merge.

Review found two ways `abandon` itself got this wrong, so decline writes its
own tombstone over exactly the line. `abandon` takes everything standing on
what it abandons, which would take another change set proposed on this one's
tip with it. Decline refuses while such work stands on the line instead.
And a retitled opening is already superseded, which `abandon` refuses, so
the tombstone supersedes the opening's current revision.

Review also found a race between a decision and a late step. A replica that
has not heard of an acceptance records another step, and the tip moves on
when the two meet. The merge does not hold that step, so a decided change
set is read up to what its decision covers, and the steps beyond are listed
apart, as recorded after it.

## What Diaryx keeps doing on top

Historica learns the shape. Diaryx keeps everything that is about Diaryx:

- **Agent authorship.** The opening and every step are recorded with
  author `agent:<model>`. Historica neither checks nor interprets that
  author.
- **Its headers.** `diaryx.operation`, `diaryx.sources` and `diaryx.by` stay
  on the steps, and `diaryx.by` can go on the opening through
  `Proposing::extensions` (0070). `diaryx.change-set` becomes redundant,
  because the line is now the revisions between the opening and the tip,
  but old lines carry it and can be read by it. `diaryx.accepts` likewise
  gives way to the merge's parents and the `accepted` name.
- **The pedantic rule.** Unsigned revisions are held until the person
  decides. That stays pedantic's rule, and its judge has one thing to learn:
  a signed merge whose parents include an unsigned tip takes that tip's line
  in. That is the point of accepting by merge. Bounded approval
  (`--approve`) signs the same merge under the approver's key.
- **Its own folder writing.** Diaryx's accept merges page by page with
  `merge_lines` and writes the folder. It goes on doing that. What changes
  is the record it makes afterwards: two parents, the accepted head and the
  tip, and then `change_set::accept`.

## The Diaryx follow-up

Diaryx sync carries revisions, operation documents and payloads, and not
`names/`. So nothing here reaches the phone until Diaryx does two things,
which belong in a Diaryx pull request once this one is merged and
`cargo xtask bump historica` takes it:

1. **Carry the names object.** Each device seals
   `Store::change_set_names().write()` and puts it beside its per-device
   head object whenever it changes, since `outgoing` sends nothing while
   the heads stay where they are, and a submission moves no head. `incoming`
   parses each other device's with `change_set::Names::parse` and applies it
   with `change_set::take_names`, which keeps a reading that conflicts as
   this device has it and reports it, rather than refusing the pull. A
   private bookmark is not in the object, by 0062.
2. **Read change sets from the store.** `begin_change_set_by` calls
   `change_set::propose` with the model as author and `diaryx.by` as an
   extension. `record_step` records on `line.tip()` exactly as now, and the
   pin moves itself. `submit_change_set` calls `change_set::submit`.
   `accept_line` asks `change_set::acceptable` with the tip the person
   reviewed before it writes anything, records its capture with that tip as
   a second parent, then calls `change_set::accept` with it. `--approve`
   asks `change_set::approvable`, so a step added after submission cannot
   be approved. `decline_change_set` calls `change_set::decline`.
   `change_sets()` lists `Store::change_sets()`. The device's
   `caches/assist/` record is retired. A one-time conversion reads each
   cached record and its `diaryx.change-set` revisions into an opening, a
   tip, and the decision names, for change sets proposed before the switch.

`own_heads`, which traces an assistant's line back to the person's own,
also has to know that an opening is part of the assistant's line, and that
a tombstone on the base is a head with nothing in it to merge.

## Rejected alternatives

**A record file in a reserved directory.** A `history/change-sets/` of
immutable documents, one per fact, unioned like `claims/` (0046, 0053). It
converges and it holds any field. It also needs `check`, `export`,
`receive`, `offer` and `fetch` to learn a new kind of file, and its facts
would be unsigned documents beside a history that can already sign
revisions. Every fact it would hold already has a home in a revision or a
name.

**Fields in the bookmark file.** A title line beside the target. That is
0062's refused grammar change, and it puts mutable prose in the conflict
surface.

**The title in a header on the first step.** The change set would not exist
until its first step, and the header would be some tool's word, which
historica cannot read. An empty change set is a real state: the assistant
has begun and not yet written.

**A change bookmark on the tip.** It follows the acceptance merge and every
revision after it, and it follows an amendment the reviewer never read.
Above.

**Moving names between directories for state**, `drafts/<id>` to
`proposed/<id>`. A deletion is local (0073), so the old name comes back
from every replica that has it.

**Making `receive` move every pin forward.** A pin is a pin on purpose
(0088). Only the tip and `submitted` are *meant* to move, and they are
meant to because a change set grows.
