# 0090 — Taking a revision back

Every way back this tool has rewrites. [0023](0023-what-an-amendment-keeps.md)'s
`amend` and [0013](0013-abandoning-and-pruning.md)'s `abandon` supersede the
tip, [0059](0059-carrying-a-descendant-across.md)'s `abandon --only` withdraws
a revision from the middle and restates what stood on it, and
[0082](0082-squashing-a-run.md)'s `squash` folds a run into one. Each of them
is a statement that the history should have said something else.

A mistake found a week later wants the opposite statement. The history said
exactly what happened — somebody wrote the wrong paragraph, an assistant's
change set was accepted that should not have been, a file was deleted that
was still needed — and a week of work now stands on it. What a person wants
is for what happens *next* to be that the mistake is taken back. That is a
new revision on the head, and nothing before it changes. `comparison.md` has
carried the row for it since the beginning, with a dash in the middle column:
`git revert`, *undo the edit and `record` it, which is what the history
should say happened*. This decision fills the dash.

It matters more now than when the row was written. A store a library keeps —
a history an assistant proposes changes into and a person accepts them from —
is one where a bad edit is ordinary rather than rare, and where the work that
lands on top of it is somebody else's. Superseding the mistake there means
restating everyone's work above it, on every replica, and refusing whenever
any of it touched the same lines. Recording its undoing means one revision,
from one person, that every replica receives like any other.

## The decision

- **`historica revert <target>` takes one revision's work back out of the
  folder, keeping everything recorded since.** What the target added is
  removed, what it dropped is put back where it was, what it renamed is moved
  back, a mode or a link it changed is changed back, and every line it
  changed is changed back inside whatever the head holds now.
- **It writes the folder and prints the `record` that writes it down.** The
  command records nothing. A person can read what the undoing did with
  `status` and `diff` before the history says anything, exactly as after
  [0012](0012-conflicts.md)'s `merge`.
- **The printed `record` names the paths the undoing touched and nothing
  else**, which is [0039](0039-recording-some-of-the-folder.md): unrecorded
  work elsewhere in the folder is not compared with anything, so it is not
  swept into a revision that says it undid something else. Every rename the
  undoing puts back is stated with `--move`, because the folder cannot show
  one ([0011](0011-working-copy.md)), and without it the file would come back
  as a new file with a new identifier. Every file it brings back is stated
  as the kind it was, with `--bytes` or `--lines`, because the sniff
  ([0017](0017-content-that-arrives-whole.md)) could decide otherwise and a
  file's kind is the history's decision rather than its bytes'.
- **The message names what was undone**: `Undo "<its first line>"
  (<digest>)`, so `log` reads as what happened and `show` finds the revision
  that was taken back. It is a suggestion in a printed command; the person
  recording types what they like.
- **The undoing is [0007](0007-content-and-merge.md)'s merge, run the way
  0059's carry runs it.** For a file of lines, the content the target left is
  the base; the delta back to what its parent held is one side; the delta on
  to what the head holds is the other; the two replay concurrently.
- **Where they meet, the file is refused, and so is the whole undoing.** Later
  work that changed a line the target wrote leaves a person to say which of
  the two they meant to keep. Every refused path is named with its reason and
  nothing is written, because a folder half-holding an undoing would be
  recorded as one.
- **The folder has to hold the head at every path the undoing touches** —
  its bytes and, where the folder can say one, its mode
  ([0034](0034-a-file-can-be-run.md)), or where a link points — and nothing
  at a path it brings a file back to. What is there otherwise is
  somebody's unrecorded work, and [0030](0030-the-folder-catches-up.md)'s
  rule — never overwrite or remove bytes no revision records — is kept by
  refusing rather than by asking.
- **A merge is undone against a side, named with `--parent`.** The parent
  named is kept, and what the merge brought in from its other parents is
  taken back, compared file by file as the merge's tree against that
  parent's — the merge's own document states only what joining needed. This
  is how an accepted change set is taken back in one step: accepting one is
  recorded as a merge whose parents include the change set's tip, so
  reverting the acceptance against what it was accepted onto takes back
  every revision the change set held, and keeps everything since. A merge
  with no side named is refused, because a merge's parents are a set and
  there is no first one to assume.
- **What the head has already taken back is not taken back twice.** An edit
  the head already made is left out of the undoing, so a revert that has
  already been done, by hand or by another revert, settles rather than
  refusing.
- **The library decides all of it.** `historica::revert::plan` takes the
  store, the folder, the target and the head (and `plan_against` the side
  of a merge to keep) and hands back a `Reversal`: an
  [`update::Update`](0030-the-folder-catches-up.md) for `update::apply` to
  perform under the guards it already keeps, the facts the record will state,
  the paths to restrict it to, and the renames to state. A host keeping its
  own folder does the same three steps the command does — plan, apply,
  record — with nothing decided in between.

## Why a new revision rather than a rewrite

0030 already answered *going back* with `abandon` and then `update`, and that
answer stands for what it was given: a run at the tip that should never have
happened, withdrawn on the record. It is the wrong answer to a mistake with
work on top of it, three ways.

**It rewrites what other people did.** `abandon --only` restates every
revision above the target. On one machine that is a carry; between replicas
it is a supersession every copy has to receive before work recorded on the
old revisions converges, and work recorded meanwhile stands on revisions that
are now superseded — 0023's `## Since` state, which `check` notes and `carry`
repairs. A revert is an ordinary revision on the head. A replica that has not
seen it yet merges it like any other.

**It refuses more.** A carry that meets the abandoned work refuses the whole
stack, because restating a descendant is the descendant's author's work. A
revert that meets later work refuses only the files where the two met, and
says which.

**It hides the correction.** A superseded revision is still in the store, but
the history a person reads — `log`, `blame` — no longer shows that the
mistake happened, or that somebody took it back, or when. For a journal that
is often what a person wants, and `abandon` is still there for it. For a
library several people and assistants write into, the correction is part of
the record.

## Why the folder rather than the store

`squash`, `carry` and `abandon` write the store and read no folder, because
what they state is already in the store: a tip, a parent, a tombstone. What a
revert states is a file nobody has written yet — the head's lines with one
revision's lines taken back out — and that is exactly what `merge` faces. So
it takes `merge`'s shape. The folder is where the new content appears, and
`record` is what writes a revision about a folder, minting the change,
reading the author and the clock, and keeping every identifier it already
knows. Nothing here does any of that twice.

It also keeps the act reviewable without a flag. A revert of an assistant's
change set is exactly the moment a person wants to look before the history
moves: `diff` shows what is about to be recorded, and `update` puts the head
back if it is not what they meant.

## What a file goes back to

For each file the target touched, three readings are compared — what the
target's parent held, what the target left, and what the head holds — and
each fact the target stated is undone only where the head still holds what
the target left:

| The target | The head since | The undoing |
|---|---|---|
| added a file | holds it unchanged | removes it |
| added a file | changed it | refuses: taking it away would take the later work too |
| dropped a file | does not hold it | puts its parent's version back at its old path |
| renamed a file | holds it where the target put it | moves it back, stated with `--move` |
| renamed a file | moved it again | leaves the path, and says so |
| changed lines | changed other lines | changes those lines back, keeping the rest |
| changed lines | changed the same lines | refuses |
| replaced a file of bytes | holds the target's bytes | puts the parent's bytes back |
| replaced a file of bytes | replaced them again | refuses: there is no line to undo one change by |
| changed a mode or a link | holds what the target set | sets it back |

A rename put back also moves every link that names the file by identity
([0040](0040-a-file-can-be-a-link.md)): a `file:` target is spelled from the
file's current path, so the undoing re-points those links at where the file
ends up, and the folder it leaves is exactly the one `record` states. A link
naming a file the undoing removes is refused.

Anything the head has already put back by other means is left alone and
reported, and a revert with nothing left to undo says so and succeeds. An
undoing is an ordinary revision, so it can itself be reverted, and the
mistake comes back.

## Refusals

- **A merge with no side named**, or with a side that is not one of its
  parents. The refusal lists its parents.
- **A revision the head does not stand on**, which leaves the head holding
  none of its work.
- **Several heads.** The undoing is recorded on one line of work, and which
  one is a person's choice; `merge` first.
- **A file holding lines `forget` destroyed** ([0014](0014-forgetting.md)),
  for the reason a carry refuses one: recording the marker's text as content
  would launder a redaction into authority.
- **A file of bytes this store does not hold**, named with the `fetch` that
  brings it.

## Rejected alternatives

**Record directly, as `abandon` does.** The new content would have to be
written into the store before anybody had seen it, and the folder would then
be one `update` behind the head on exactly the files a person cares about.
Writing the folder first costs one printed command and buys the look.

**Undo by item identity rather than by content.** 0007's items are named
by the revision that inserted them, so taking out exactly the target's
inserts and putting back exactly its deletes is expressible without a merge.
It is also a second algorithm beside the one 0059 already trusts, and it
says nothing new where the two agree; where they differ — later work that
moved the target's lines about — it guesses where the merge refuses. The
merge is the one decision this format has already made about what concurrent
work means.

**Render the meeting with markers, as `merge` does.** `record --merge`
refuses while a marker line stands; a plain `record` does not look. Marker
lines written by a revert would be recorded as content by the next person
who did not read the folder first, which is the one outcome a tool for
correcting mistakes must not produce.

**A format header naming the revision undone.** It would let `log` draw the
link rather than the message carrying it, and it is a word the format would
have to keep forever ([0047](0047-one-spelling-for-the-format.md)). The
message is enough to start with; a host that wants the link machine-readable
can write it as an extension header ([0065](0065-the-header-another-tool-wrote.md))
on the record it makes.

## What this does not do yet

- **Revert a range** — several revisions taken back in one undoing. Each
  can be reverted in turn, newest first. The range that matters most, a
  change set, is already one step, because its acceptance is a merge; a
  general range would need a rule for what a range across a merge means,
  and nobody has asked for one yet.
- **Undo part of a revision**, a path at a time. The `Reversal` names every
  path; narrowing it is a filter a caller can write, and a flag can follow
  when someone wants one.
- **Resolve a meeting in the folder.** Refused for now, by the argument
  above; a revert that renders markers waits on a `record` that recognises
  them outside a merge.
