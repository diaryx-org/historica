# 0023 — What an amendment keeps

Decision 0011 listed three things `record` would not do, and gave one reason
covering all three: restating a descendant's operations against a parent whose
content changed is 0007's merge under another name. That reason is entirely
about descendants. A revision that has none can be rewritten with the machinery
that already exists — the folder *is* the content, and the diff is recomputed
against parents that did not move.

So the rewriting half starts at the tip, where 0013 also started, and for the
same reason: the draft that did not work out is at the tip, because the person
was just writing it.

This document decides what such a rewrite copies, what it recomputes, and what
it refuses.

## The decision

- **`historica amend [<target>] [-m <message>]` writes a revision superseding
  the one it names.** It carries the same `change`, `author`, `when`, and
  `parent` lines, and names the amended revision on a `supersedes` line.
- **Every tree fact and every operation is recomputed** from the folder against
  those parents, by the survey `record` already performs. Nothing is
  transformed and nothing is carried across except what is listed here.
- **`revised` is a fresh reading of the clock**, and `revised-by` is the person
  performing it where that differs from `author`. 0010's table says so in one
  line: amending stamps.
- **A file identifier the amended revision minted is kept**, matched by path.
- **The tree facts only a person could have stated are inherited** — the
  amended revision's `move` lines — so amending a revision that renamed a file
  does not spell the rename as a deletion.
- **The message is copied where `-m` says nothing.** An amendment of the folder
  alone asks nobody to retype a description that already exists.
- **A revision something already supersedes is refused, and so is one with a
  descendant**, in the library's own words, naming what stands on it.
- **The position is a head no revision supersedes.** This is a change to what
  `record`, `status`, `merge`, and the `head` target already did.

Nothing here needs a format change. 0001 put supersession in the model on the
first day and `tests/corpus/revisions/05-amended.rev.txt` has spelled an
amendment since 0002, which is the evidence that the primitive was the right
one — the same evidence 0013 collected for abandoning.

## Amending stamps, because a person asked for it

0010 draws its line between a rewrite a person performs and one the tool
performs on its own behalf, and puts the reason in a table:

| The act | Change ID | `author` / `when` | `revised` |
| --- | --- | --- | --- |
| Amending or rewording | copied | copied | recorder, now |
| Carried along by an ancestor | copied | copied | from the cause |

Amend is the first row. The convergence argument that forces the second row —
two replicas independently rebasing one change onto one rewritten parent must
write one file — has no purchase here, because two people amending one revision
are not performing one derivable act. They are writing two different pieces of
work, and 0001 already calls the result divergence and calls it legitimate.
Stamping is what makes that visible; copying would spell two decisions as one.

`when` is copied, which 0010 already settled and 0005 already requires: it is
the moment the change was first recorded, so an amendment keeps it and
`revised` carries the later act. The visible consequence is that a revision
amended a week later is still filed under the date the work started, which is
the reading 0010 chose deliberately.

## An identifier that is kept, and everything else recomputed

The survey is taken against the amended revision's parents, where the files
that revision *added* do not exist. So every path it created surveys as added
again, and minting an identifier for each would be the writer being clever in
exactly the way 0008 built identifiers to prevent: the same file, in the same
place, in the same piece of work, called something else after every amendment.

So an amendment keeps the identifier its predecessor minted for a path, and
mints only for a path the predecessor did not add. This is 0010's rule one
layer down, where 0011 already put it — "minting a file identifier is 0010's
rule word for word" — and the layer below inherits the same sentence: only a
human act introduces fresh randomness, and adding a file that was already there
is not one.

The match is by path, and nothing else. A file added by the amended revision
and then renamed in the folder before amending gets a new identifier, because
the alternative is recovering the connection by content similarity, which is
the heuristic 0008 and 0015 have each refused by name. Nothing is lost when it
happens: the whole life of that file is inside the change being rewritten.

Everything else is genuinely recomputed. The operations, the payloads, the
adds, the drops, and the content of every file come from comparing the folder
with the parents, which is one call to the same function `status` and `record`
share. An amendment is therefore not a patch on a revision; it is a recording
that happens to stand where another one stood.

## The facts a recomputation cannot observe

0011 says a rename is the one fact a person has to state. A recomputation
against the amended revision's parents cannot observe one either, so amending a
revision that recorded a `move` would survey the folder as a `drop` of the old
path and an `add` of the new one — and the amendment would quietly undo the
rename, with the file's identity going with it.

So the amended revision's `move` lines are inherited: each names a file the
parents' tree holds and a path it was put at, which is the same shape 0012's
`--at` already takes and is applied by the same line of the survey. A person
who wants a different rename states `--move`, which overrides an inherited one.

That last flag needed one thing said about it that had never come up before.
`--move old=new` names its `old` against where the revision being written
currently has the file, rather than against the tree its parents hold. For a
record the two are the same set of paths. For an amendment they are not: the
inherited `move` line has already put the file somewhere, and that somewhere is
where the folder holds it and therefore what a person would type.

This also settles what happens when a merge is amended. A path two files
claimed, which the merge record settled with `--at`, is settled again the same
way, because settling it is what the inherited `move` line records. No contest
a person has already answered is put to them twice.

## Two refusals, and what they mean

**A revision with a descendant is refused.** Rewriting it changes its digest,
which changes its children's bytes, which changes their digests, to the end of
every line — decision 0001 calls that automatic rebase and says it is what the
model does rather than a feature built on top. What the model does not yet have
is a way to restate a descendant's operations against a parent whose content
moved, which is 0007's merge under another name, and 0011 and 0013 have each
refused it in these words already. The message names the revisions standing on
the one that was asked for, and says that rebasing them is not built.

**A revision something already supersedes is refused.** Superseding it a second
time produces two current revisions of one change with nothing between them,
which is `ChangeState::Divergent` — legitimate when two replicas did it without
seeing each other, and merely a mistake when one machine did it twice with the
successor in front of it. The message names the successor, which is the thing
the person meant to amend.

There is a third refusal that reads like `record`'s and is not quite.
`record` refuses a revision that would state nothing; **`amend` refuses one
that would state exactly what its predecessor already states**, which is the
same sentence one layer up. The comparison is the whole document with
`supersedes`, `revised`, and `revised-by` set aside on both sides — the three
facts that describe the rewrite rather than the work — so it catches a reword
that reworded nothing without ever consulting a plan. A reword with an
untouched folder is not that case, and is the ordinary use of this command.

## The head, after something has been rewritten

`History::heads` is a pure graph question over parent edges, and 0001 says so
deliberately: "whether a given view hides superseded revisions" is left to the
caller, because the core will not make a rendering decision.

Every caller in this repository was written before anything could be
superseded, and each of them takes `heads()` as the position. The moment an
amendment exists, that answer is wrong in the most ordinary case there is: a
store with one line of work in it, amended once, has two heads by parent edges
— the revision that was rewritten, which nothing names as a parent, and the one
that rewrote it. Asked to record, the tool would refuse and ask which of them
is meant, forever.

So the position is a head no revision supersedes. Where filtering leaves
nothing — a store holding a revision whose successor has not been delivered —
the unfiltered heads are used, so the message is about the store that exists
rather than about an empty one.

`log` is untouched, and shows the superseded revision marked `superseded` next
to `head`, because it is both and a log that hid it would be hiding the thing a
person is most likely to want back.

## The revision that was amended is still there

Nothing is deleted. 0013 already decided this and gave the reason: there is no
operation log here, so a superseded revision *is* the record of what the work
was before it was amended, and `prune` is the command that empties it. `amend`
prints the digest of what it superseded for exactly that reason — the undo is a
digest a person can still type.

`check` is unaffected. A store holding both revisions contradicts itself in no
way: both parse, both hash to their names, both replay, and 0006 already ruled
that a `supersedes` naming a file the store does not hold is neither an error
nor a note.

## The name it is written under

0019's scheme, with no new rule and one tier that had never been reached. The
stem is composed from the copied `when`, the possibly-new message, and the
copied change ID — so an amendment that reworded nothing wants exactly the name
its predecessor already has.

`arrange` has always answered that with three tiers: the base, the base plus
the change ID where two *changes* want one name, and the base plus the change
ID plus the digest where two revisions *of one change* do. The writer had only
the first two, because before this command the third case could only arrive
from another replica, and a writer names one file at a time. It now has all
three, which is a bug fix that arrives with the feature that would have hit it:
a second amendment under one message wanted a filename the first amendment was
already using.

The digest that third tier needs is available, and the reason is worth stating
because it is the same reason 0002 gives for everything else here. **A revision
document says nothing about what it is called** — the digest lives in the name
and in the references other revisions make, never in the file. So what a
revision *names* can be settled before what any of it is *called* is, and the
writer composes the whole document, hashes it, and only then asks the scheme
for a name.

## Rejected alternatives

**Copying `revised` from the amended revision.** That is the rule for a rewrite
nobody decided anything about, and 0010 says which act is which. Copying here
would spell a second person's decision as the first person's, and would make
two independent amendments converge on one file — which is a divergence being
hidden rather than a divergence avoided.

**Minting a fresh change ID.** That is what 0013's tombstone does, and it says
the opposite thing: this work was replaced by a decision to stop. An amendment
is the same work, and 0001 built the second identity precisely so that it could
say so.

**Deleting the amended revision.** 0013 refuses this in one line — the file
comes back on the next sync, and nothing anywhere says it was ever rewritten.

**Opening the editor on the old message.** Tempting, because rewording a long
message from `-m` is unpleasant. It is deferred rather than refused: 0011 was
careful that the editor's template is empty and that nothing is stripped, and
putting existing bytes into that file is a change to what "nothing is stripped"
protects. It wants its own decision, not a paragraph in this one.

**Copying `x-` headers.** Kept, not rejected — an amendment carries them
forward. The case against is that `x-review-url` on a revision that has just
been replaced is a stale claim. The case for wins twice: this writer cannot
read them, and a writer that silently drops what it cannot read is the failure
0020 calls the worst available; and 0005's argument for copying `author` is
that a revision must be a whole document, which is not an argument that stops
at the headers this version happens to understand.

**Spelling it `record --amend`.** 0011 named it that in prose, and it is the
wrong shape now that it exists. `record` takes the folder and adds to history;
`amend` takes the folder and *replaces* something in history. A flag that
changes which of those a command does is a flag worth misreading, and the
refusals are different enough that half the message would be about which mode
the person was in.

**Rebasing descendants now.** The wall 0011 and 0013 both stopped at, unmoved.
It is one piece of work — transforming operations against operations — and it
unblocks amending a middle revision, abandoning one, and moving a change
somewhere new, all at once. Doing a third of it under this command would buy
none of the other two.

## Consequences

- `src/record/` gains `amend`, an `Amendment`, and the two refusals above.
  `record`'s planner grows one internal parameter — the identifiers to keep —
  and the code that files a revision's documents and payloads under 0019's name
  becomes shared rather than written twice.
- `historica amend [<target>] [-m <message>] [--move <old>=<new>] [--dry-run]`
  is the command. `--dry-run` prints the facts and writes nothing, and meets
  every refusal the real thing would, including the one that needs the finished
  document. It never prints "nothing here differs": an amendment restates the
  whole of what it replaces, so an untouched folder is a full plan rather than
  an empty one.
- `naming::stem_for` gains the digest and the third tier above, and `--move`
  reads its `old` against where the revision being written has the file rather
  than against the tree its parents hold. Both are changes to code that
  `record` shares, and neither changes what `record` does.
- The front end's idea of the position changes, above. This is the first
  behavioural change in this repository that a person could notice without
  running a new command, and it is a change from an answer that was only ever
  correct because nothing could rewrite anything.
- Nothing in the format grows, and the corpus grows nothing. If a future
  document needs a vocabulary `supersedes` cannot spell, that is evidence
  against this design rather than an extension of it.
- The tests worth naming are the ones that would catch a writer being clever:
  an amendment keeps the change ID and the file identifiers its predecessor
  minted, so `cat` at the amendment and `cat` at the predecessor name one file;
  `when` survives and `revised` is new; a reword with an untouched folder
  records the same tree facts under a different message; amending a revision
  that renamed a file keeps the rename; a revision with a descendant is refused
  by name; a revision already superseded is refused by name; an amendment that
  states nothing is refused; `record` after an amendment finds one head; and
  `check` accepts the store at every point.
- 0011's first refusal is answered for the head and stays refused everywhere
  else. 0013's `abandon` is now the only command in that document with nothing
  behind it.

## Deferred

**Amending anything but a head**, which is the same wall abandoning meets, and
will be lifted by the same work. The `## Since` section below is what the wall
looks like from the other side, where a receive has already walked around it.

**Rewording in an editor**, above.

**Amending onto a different parent.** 0010 already describes moving a change
elsewhere as its own act with its own row in the table, and giving `amend` an
`--onto` would quietly make it two commands.

**Undoing an amendment.** A superseded revision is still there and can be
amended back into place by hand, but there is no command for it, and whether
one is wanted is a question about how often people reach for it.

## Since

"`check` is unaffected" above is true, and was written when it could not be
tested. If only a head can be amended then no command can leave a revision
standing on one that has been withdrawn, and the state that paragraph excuses
was unreachable. 0029's `receive` reaches it. One replica amends a revision;
another, not having seen that, records on it; a union holds both. Neither
machine did anything a command would refuse, and the wall this document put
in front of `amend` is not in front of transport.

**Supersession does not travel along parent edges.** That is the rule, stated
here rather than left as a gap: it is a claim about which revisions of one
change are current, and parenthood is a different graph, which 0001 keeps
separate on purpose. So a rewrite reaches what it rewrote and nothing built on
it, and a store holding both the supersession and a descendant of the
superseded revision is holding a rewrite that stopped halfway.

What that costs is not confusion about the past. It is a merge. An item's name
is its revision and its index, so a rewrite mints its own items for the lines
its predecessor already minted, and the two sides hold the same lines under
different names. Every one of them is concurrent. A person joining those heads
is shown their own paragraph twice, attributed to two revisions, and asked to
resolve work nobody did twice — and the honest resolution, deleting one copy,
is indistinguishable at the keyboard from deleting somebody's work.

**It is reported and it is not an error.** `check` names the nearest revision
nothing supersedes that stands on one something does, along with what
withdrew it:

```console
note: b8be0e2368d2 stands on 0bedbcb95ea3, which aa78c9c6272e supersedes;
      the rewrite did not reach it
```

A note, on 0006's rule and for its reason: every document parses, hashes and
replays, and nothing here contradicts anything. What the store lacks is the
rest of the rewrite, which is a thing transport may yet deliver — the same
shape as an undelivered parent. `merge` says it too, before it writes a
marker, because that is where a person meets the consequence rather than the
fact. A revision that is itself superseded is passed over: a withdrawn
revision standing on a withdrawn revision is the trailing history every
finished rewrite leaves, and `tests/corpus/revisions/` is a finished one — 05
amends 02, 06 carries the merge across, and nothing is reported.

**The format does not change for this, and should not.** The repair is the
re-diff this document deferred: materialise the descendant's intended result,
re-diff it against the successor, and record it as an ordinary revision whose
`supersedes` names the descendant. Existing grammar throughout, which is why
non-tip rewriting stays a tool question rather than a format one. The shape
that would need grammar — an edge meaning "this line of work has been
rewritten past here", so that a merge could consult it — is rejected on 0001's
grounds: it would make merging depend on supersession, and the whole reason
those are two graphs is that a merge must be computable from parents alone,
identically, on every machine.

Until the re-diff exists, the note is the whole of the answer, and the manual
repair is the one a person can already perform: amend the descendants onto the
successor by hand, tip first.
