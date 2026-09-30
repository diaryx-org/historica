# 0082 — Squashing a run into one revision

[0001](0001-identity.md) named the act this decides before any command
performed it: "a revision may supersede revisions of *other* changes, which is
what squashing is: the absorbed change has revisions, all superseded, and no
current revision of its own." [0013](0013-abandoning-and-pruning.md) built the
first act that reaches that state on purpose, the tombstone, which says the
work is gone. This is the other one, which says the work is here, stated once.

A history can need this without anyone having made a mistake. A writer who
records every few seconds — an editor's autosave, a sync that records
whatever it finds — leaves a revision per half-sentence. A device that raced
itself leaves the same sentence twice, as two lines joined by a merge. Every
revision is true, and none of them is something a person wants to read back.
The work was one piece of work, and the history should be able to say so.

## The decision

- **`squash <base>..<tip>` writes one revision on `<base>` that states what
  `<tip>` holds and supersedes the run between them.** The run is
  [0063](0063-a-range-of-revisions.md)'s range: everything the tip has
  behind it that the base does not.
- **What it states comes from two trees, not from a folder.** Every file
  keeps the identifier it already has, so nothing is minted and no rename
  has to be noticed.
- **The work is described as the run described it.** The one author of its
  work (a merge's author joined it, and is not counted), the moment its
  earliest revision was recorded, and either `-m` or the run's own
  messages, in order. `revised` is the clock now, and `revised-by`
  is written where the person squashing is not the author
  ([0005](0005-authorship.md)).
- **Its change is newly minted,** so every change in the run is squashed:
  0001's `Abandoned`, reached by absorption rather than by a tombstone.
- **What stands on the tip is carried onto the squash in the same act**
  ([0059](0059-carrying-a-descendant-across.md)), verbatim, because the two
  hold the same files. **What stands on any other revision of the run is
  refused.**
- **Nothing is deleted.** The squashed revisions are the undo, exactly as an
  amendment's predecessor is. `prune` is what removes them, on one machine.

## What a squash states

The squash stands on the base and must leave the store holding exactly what
the tip held. Both file sets are in the store already, so the revision is the
difference between two trees, file by file:

| At the base | At the tip | The squash states |
| --- | --- | --- |
| absent | present | `add`, with its lines as `text` ([0017](0017-content-that-arrives-whole.md)), its payload as `bytes`, or its target as `link` |
| present | absent | `drop` |
| at one path | at another | `move` — it is the same file, so no rename has to be guessed |
| lines | different lines | `edit`, naming [0007](0007-content-and-merge.md)'s diff from one state to the other |
| one payload | another | `bytes`, naming the tip's payload by digest |
| one target, or mode | another | `link`, or `mode` |

This is what `record` does between a tree and a folder, done between a tree
and a tree. Doing it from the store rather than the folder is what makes the
command worth having. `amend` restates the folder because the folder holds
the head ([0023](0023-what-an-amendment-keeps.md)). A run worth squashing is
usually not at the head: yesterday's two hundred autosaves have today's work
standing on them. A squash that needed the folder to hold its tip could only
tidy the last thing a person did.

A payload is named, never copied. The store already holds it under the
revision that brought it, or it is held elsewhere, and a name by digest is
the same statement either way.

## Merges inside the run are allowed

`abandon` refuses a run with a merge in it, because the merge's other side
arrived from elsewhere and would fall out of the ancestry with the tombstone.
A squash cannot lose it. Every parent of every revision in the run is either
in the run, and so squashed, or behind the base, and so still in the squash's
ancestry — that is what the range means. The other side's work is in the
tip's files, and so in what the squash states.

That is the case this was written for: two lines through one sentence and
the merge that kept both. Squashed, they are the sentence as it ended up, and
no revision says it was ever written twice.

## What describes the work

**One author.** A revision names one, and choosing one of several would
credit the others' work to the wrong person. A run whose work was recorded by
several authors is refused, naming them; squash each author's part on its
own.

A merge does not count. Its author joined the work, and the work's authors
are on the revisions it joined. This is not a nicety: a host that merges the
same heads alike on every device names itself as the merge's author, so that
every device writes the same bytes. Counting it would refuse exactly the run
this was written for — two lines through one sentence, and the merge that
kept both. Only a run of nothing but merges keeps a merge's author.

**The moment the work began.** 0023 keeps the moment the work was first
recorded when it is rewritten, and a squash rewrites a run whose work began
at its earliest revision. Earliest by instant, not by spelling: two offsets
compare as times.

**The run's messages, when nobody gave one.** Each non-empty message once, in
the run's order: parents before children, and among revisions free to come
next, the earlier first. A run of autosaves said nothing, and the squash of it
may say nothing too, as [0002](0002-revision-document.md) allows.

**A new change.** Reusing a change from the run would leave that change
resolved to a revision stating everyone else's work as its own, and the run
has no one change to reuse anyway: a split holds two, each as early as the
other. Minting says the true thing: this work was replaced by a statement of
all of it.

**No advisory headers.** [0065](0065-the-header-another-tool-wrote.md) forbids
a writer to drop a header it cannot read from a revision it *restates*. A
squash restates no one revision, and copying one revision's headers onto a
statement of several would have that tool vouch for work it never saw.

## What stands on the run

Work standing on the tip is carried onto the squash, and the carry is
verbatim: the squash and the tip hold the same files, so no base moved.

Work standing on a revision in the middle of the run is refused. Its base is
half of the run: the squash states the tip, and the tip is not what that work
was recorded against. Carrying it would restate it against a parent holding
changes it never saw. It would be a merge, and 0059 refuses to make one
silently. The refusal names the work, and a person squashes up to where it
branches, or carries it off first. A revision something has already rewritten
does not count: it is somebody's undo, not work.

## Content is filed before the carry is planned

0059 plans a rewrite's carries before anything is written, holding the
rewrite provisionally, so that only a plan with no refusal reaches the disk.
A tombstone and a reword can be held that way because they name no content
of their own. A squash names operation documents, and the carry reads the
squash's files to compare them with the tip's.

So a squash files its content first, and then plans the carry and writes the
revision. That is the order `record` has always kept
([0011](0011-working-copy.md)): an interruption, or a refusal, leaves content
nothing names, which `check` calls a note — never a revision naming what is
not there. In practice nothing is refused at that point: every refusal a
squash can meet is met before anything is written, and a verbatim carry has
nothing left to refuse.

## Between replicas

A squash is ordinary revisions, and travels as they do. A replica that
receives one holds the run and the squash together. The run's revisions are
still heads by parent edges, but superseded, so the heads a person stands on
are the squash and what stands on it — the rule 0023 already gave `amend`.

A replica that recorded on a squashed revision before the squash arrived
holds work standing on a superseded revision. That is `check`'s note, and
`carry` is its repair: deterministic, so two replicas repairing it write the
same bytes. A squash of the tip carries nothing that another replica could
disagree with; a squash under work somebody else is doing is something to
agree on first, as rewriting shared work always is.

A host that keeps replicas in step itself has to take the same view: a
superseded head is not a line of work to merge. A host that merged it would
bring the run back as a second line holding the same files.

## Not secrecy, and not automatic

What 0013 said of pruning holds here. The squashed revisions are on every
replica that already has them, and their digests stay legible in the squash's
`supersedes` lines. A squash tidies a history; it does not withdraw anything
from it. [0014](0014-forgetting.md)'s forgetting is the act for that.

Nothing squashes on its own. When a run is one piece of work is a judgment
about writing, and a threshold — every revision within a minute, every
revision on one day — would be wrong for somebody and invisible to everybody
else.

## Refusals

- A base the tip does not stand on: the squash would put a line of work in
  its ancestry that none of the run had, and the tip's files stated against
  it would undo that line.
- A range of one revision: that is the revision itself. `amend` rewrites one.
- A revision in the run that something already rewrote: 0023's refusal of a
  second rewrite, for its reason.
- Work standing on the middle of the run, as above.
- Several authors, as above.
- A file of bytes the tip leaves undecided between two payloads
  ([0008](0008-tree.md)): the squash would be the choice nobody made.
- A file of lines with a forgotten run the base does not also hold
  ([0014](0014-forgetting.md)): the squash would have to state lines whose
  bytes are gone, and the marker in their place would be a line nobody typed.

## Rejected alternatives

**Restate the folder, as `amend` does.** Only a run ending at the head, with
the folder holding it, could be squashed. That is the one run a person least
often wants to squash, because they were just writing it.

**Record the squash as a merge of the base and the old tip.** The run would
stay in the ancestry, reachable from every later revision, and nothing would
be squashed. Supersession is what takes it out of the history a person reads
while keeping it in the store.

**Keep the earliest revision's change.** Across a split there is no earliest
one, and whichever was chosen would be left resolved to a revision stating
everyone else's work.

**Delete the run and write the squash in its place.** 0003's store is
append-only, and a deleted file comes back on the next sync (0013). What
converges is a fact written down, and supersession is that fact.

**Squash automatically, by time.** Above: a policy with a number in it,
wrong for somebody, and a store that rewrote itself in the background is not
one whose files are the authority.

## What this does not do yet

- **Squash from the root.** A run with no base would be a new root, which is
  a different history rather than a tidier one.
- **Edit while squashing.** A squash states the tip exactly. A correction is
  a revision of its own, before or after.
- **Split a run's authors apart.** Refused rather than guessed, for now.
