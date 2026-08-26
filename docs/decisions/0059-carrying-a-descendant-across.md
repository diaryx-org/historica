# 0059 — Carrying a descendant across

Three decisions stopped at one wall and used the same words each time:
restating a descendant's operations against a parent whose content moved is
0007's merge under another name. 0011 refused it for `record --amend`, 0013
held `abandon` to a head or a run ending at one, 0023 kept both refusals —
and its `## Since` section met the shape anyway, because transport is not
behind the wall: a receive can deliver a rewrite that stopped halfway, and
`check` notes it without there being a command to finish it. The README's
ledger is blunt: everything that needs a descendant reparented — amending a
revision that has one, abandoning one, moving a change somewhere new — is
one piece of work, and none of it is built.

This document designs that piece of work. The sentence every refusal used
turns out to be the design: the way through the wall is to run 0007's merge,
under that name, on operations the store already holds.

## The decision

- **`carry` is the primitive.** Given a revision whose parent a rewrite has
  replaced, it writes the revision stating the same work against the
  replacement: `change`, `author`, and `when` copied, `revised` and
  `revised-by` from the rewrite that caused it, the predecessor on
  `supersedes`, the replacement on `parent`. This is 0010's "carried along
  by an ancestor" row, decided eleven decisions early and exercised at last,
  with `tests/corpus/revisions/06-rebased.rev` already pinning the shape.
- **A file whose base did not move is carried verbatim.** The carried
  revision names the same operation documents — same bytes, same digest,
  same file on disk under 0003's dedup — and only the revision document is
  rewritten.
- **A file whose base moved is restated through 0007's merge.** The delta
  from the old base's content to the new base's, read by `crate::diff`,
  replays as an operation stream concurrent with the descendant's own; the
  merged result is the carried content, and the recorded operations are its
  difference from the new base. A contested span refuses the whole plan
  before anything is written, naming the revision, the file, and the span.
- **`amend` and `abandon` lose their descendant refusals.** Each writes its
  rewrite and carries every descendant across, parents first, in one
  all-or-nothing plan. Amending a non-head is a reword — `-m` required, the
  folder not consulted — because the folder states the head and can state
  nothing else (0030).
- **`historica carry [<target>]` finishes the rewrite transport delivered
  half of**, the state 0023's `## Since` taught `check` to note. It is the
  derivable act, so two replicas repairing one store write byte-identical
  files — 0002's convergence claim, finally doing its work.
- **Moving a change somewhere new is `historica move <target> --onto
  <destination>`**: the same restating with a person deciding, so it stamps
  `revised` from the clock, which is 0010's other row.

Nothing in the format changes. 0023's `## Since` already ruled that the
shape needing grammar — an edge meaning "rewritten past here" — fails on
0001's grounds, and this design confirms it by needing nothing the grammar
does not have.

## The transform the refusals were waiting for

Why the wall stood is worth stating precisely, because it dictates the
mechanism.

Transforming the descendant's operations directly against the rewrite's
operations — OT, position arithmetic over two recorded streams — is
impossible here, and not for the usual reasons. An amendment does not record
a delta from what it supersedes; 0023 recomputes everything from the folder
against the *parents*, so no recorded fact connects the amendment's
insertions to the insertions they replaced. The line the old revision added
and the amendment kept is, to the operation streams, two unrelated
insertions. Only content can align them, and aligning content is a diff.

But the diff cannot be the one 0023's `## Since` sketched — "materialise the
descendant's intended result, re-diff it against the successor" — taken
literally. The descendant's materialised content embodies its old base
everywhere the descendant was silent, so a plain re-diff against the
successor would record operations putting the old base *back*: an amendment
that fixed a typo the descendant never touched would have its fix silently
reverted by the carry. The sketch was a direction, not a construction, and
this paragraph is the correction 0023 will carry in its own `## Since`.

The construction is three-cornered, and every corner is materialisable
today: the old base's content, the new base's content, and the descendant's.
`crate::diff` reads the old base against the new base — the one place a
decomposition heuristic enters — and that delta replays as an operation
stream concurrent with the descendant's recorded operations, over the old
base, through the merge machinery 0007 built: Fugue ordering, contested
spans, the conformance suite behind all of it. Where the two streams touch
one region, the carry is contested and refuses, in 0007's vocabulary,
because 0027 ruled contested regions are ephemeral and never recorded.
Where they do not, the result is what three-way merge would have produced,
computed by the algorithm this project already trusts.

The irony is acknowledged rather than hidden: 0007 rejected diff-dependent
merging because two replicas' heuristics could diverge with nothing
recording the result. A carry does not have that shape. Its output is a
recorded revision with canonical bytes, and the diff it depends on derives
that recording once — the same license 0007 grants its own merge rule, that
what is recorded cannot be reinterpreted. What the dependence costs is
stated under convergence below.

## What a carry does to the tree

The tree facts follow 0023's amendment rules, one layer down, and for the
same reasons.

File identifiers are kept — a carry is nobody's act, so it mints nothing.
`move` lines are inherited verbatim, because no recomputation can observe a
rename. `mode` and `link` facts carry unchanged. An `add` whose path the new
base already holds is refused by name: it is two files claiming one path,
the divergence 0008 reports, arriving through a rewrite instead of a merge,
and resolving it needs the person the refusal summons.

A `drop` or an `edit` of a file the new base no longer holds — possible only
when the rewrite itself removed the file — is a contest of the whole-file
kind, refused the way a contested span is, not silently thinned. A carry
that would state *nothing* after such thinning would anyway be a revision
this design does not know how to mean, which is open question 4.

## The acts, one by one

**Amending a head** is 0023 unchanged. What changes is what happens next:
the descendants are carried, parents first, each taking `revised` from the
amendment — so an amendment and the carries it forces read as one event,
which 0010 says is what they are.

**Amending a non-head is a reword.** The folder states the head's content
and cannot state a middle revision's, and surveying the head's folder
against a middle revision's parents would squash the whole stack into it —
a different act wearing this one's flag. So `amend <non-head>` requires
`-m`, copies every tree fact and operation document verbatim, and exists so
that a message can be fixed without the tip's ceremony. Content-editing the
middle waits on 0030's "working forward from the past", deferred whole,
where it has always lived. The carries a reword forces are all verbatim:
no base moved, so the whole stack re-digests and not one operation document
is touched.

**Abandoning a non-head** writes 0013's tombstone where it stands and
carries the descendants onto it. Their base moved — the abandoned work fell
out of the ancestry — so files the abandoned revision touched are restated,
and a descendant that edited what the abandoned revision introduced is a
contested span: the refusal names the revision still standing on the work
being abandoned, which is exactly the fact the person needs before they mean
it.

**`historica carry [<target>]`** is the repair command. Its target is a
revision standing on a superseded one — `check`'s note, which now names the
command — and with no target it finds every such revision. The successor it
carries onto is the revision whose `supersedes` names the parent; two such
successors is divergence, refused under 0015's vocabulary until a person
resolves which rewrite won. Because every fact derives from the cause, the
replica that repairs and the replica whose `amend` carried inline write
byte-identical revisions, which is the test worth building the feature for.

**`historica move <target> --onto <destination>`** restates a change's
current revision against an arbitrary new parent and carries its descendants
after it. A person decided, so the moved revision stamps `revised` from the
clock; the descendants derive from it as from any cause. A destination that
is itself a descendant of anything being moved is refused, since the result
would stand on a superseded revision by construction — the half-finished
shape manufactured deliberately. Moving under divergence of the target
change is refused until resolved, like every act on a divergent change.

## The folder, and the position

Every one of these acts moves the position: the carried head is the new
head. `carry` leaves the folder exactly where it stands and says so, naming
`historica update` when content moved — the same relationship `receive` has
with the folder, which is the company `carry` keeps: both act on history a
person then chooses to hold. The inline acts are different, because a person
is present and asked for the rewrite: `amend` and `abandon` with descendants
owe the folder catch-up through 0030's machinery, inside the same
all-or-nothing plan, refusing on unrecorded work in 0030's words.

All-or-nothing costs nothing here. Store writes are content-addressed
`create_new` files, so the plan is computed whole — every carry, every
contest — and only a plan with no refusal in it writes anything. A carry
interrupted between files leaves a store `check` still accepts: the carried
prefix is a finished rewrite, the rest is exactly what `carry` repairs, and
running it again resumes.

## What convergence now depends on

A verbatim carry is byte-determined by the store alone. A restated carry is
byte-determined by the store *and* `crate::diff`'s decomposition, and that
dependence is new: until now the diff fed previews and records a person
reviewed, and two versions decomposing differently could at worst spell one
person's edit two ways. Now two replicas repairing one store with different
decompositions would write two revisions of one change — divergence, 0001's
legitimate state, visible and resolvable, but manufactured by nothing a
person did.

So the dependence is named a promise: a change to the decomposition
`crate::diff` produces is a `Behavioural-change:` on the commit that makes
it, stated as what it is — replicas on either side of the change may diverge
when both carry the same stack. The degradation is graceful — divergence is
shown, never silent — and the window is a person's choice, because carries
happen in commands and never on receive.

## What a carry refuses

Collected, because the refusals are most of the interface:

- a contested span, naming revision, file, and how many regions met;
- an `add` whose path the new base holds, and any fact about a file the
  new base lost;
- a whole payload the carried revision states where the rewrite states
  another — 0008's two concurrent `bytes`, arriving through a rewrite, and
  no more resolvable here than at a merge;
- a merge among the descendants, when any content beneath it moved. Its
  parents' agreement would have to be recomputed — a file both sides left
  identically may not survive the rewrite identically, and a merge owes a
  resolution wherever they differ (0032) — and a resolution it carries
  names items whose documents a restating renumbers. Both are real work
  refused rather than guessed at. A merge above a rewrite that moved
  nothing carries verbatim: the same documents are named, so every `keep`
  still counts into the runs it counted into;
- a restated file whose history has forgotten something (0014): the
  stand-in has no bytes to re-diff, and recording the marker's text as
  content would launder a redaction into authority. Verbatim carries are
  unaffected — the same operation documents stay named, so a forgetting
  keeps its grip;
- a carry thinned to nothing — everything the revision stated, the rewrite
  already states — because a revision saying nothing would mean nothing
  (0011's rule, one layer up). The refusal names `abandon`, which is the
  statement a person can still make about work a rewrite absorbed;
- a rewrite that folded two of a merge's parents into one revision, which
  would quietly turn the merge into a chain;
- a divergent successor, above.

## Rejected alternatives

**Operational transformation over the recorded streams.** Above: an
amendment restates rather than deltas, so no operation identity survives for
a transform to follow. The wall was real; it was a wall against OT.

**The literal re-diff of 0023's sketch.** Above: it reverts the rewrite
wherever the descendant was silent. Kept here as the warning it is.

**Carrying on receive.** Transport delivers facts and authors nothing —
0029's receive writes what arrived and only that — and a contested carry
needs a person present to refuse to. The note-and-command shape keeps the
store honest in between, which is what 0023's `## Since` built.

**Recording a contested carry with markers.** 0027: contested regions are
ephemeral. History records resolutions people chose.

**A grammar edge for "rewritten past here".** Rejected in 0023's `## Since`
on 0001's grounds — merging must be computable from parents alone — and
needed by nothing here.

**Squashing the stack into a non-head amend.** The folder-against-middle
survey, refused above by construction rather than by lint.

## Resolved questions

1. **`amend` keeps one meaning, and there is no `reword` command.** Below.
2. **The human move is `carry --onto`**, and there is no `move`. Below.
3. **Resolutions beneath a restated carry are refused**, and more than
   drafted: any merge above moved content is, resolution or not, because
   the parents' agreement itself has to be recomputed before anyone knows
   which files owe resolutions. The re-derivation stays deferred.
4. **A carry thinned to nothing refuses**, naming `abandon`. Writing the
   empty revision would leave the change resolved by a revision nobody
   meant, and the person who did mean it has a command that says so.
5. **`check`'s note names the command**: "it was authored before the
   rewrite. Run `historica carry` to repair automatically." 0021's rule —
   the store explains itself, here down to the repair.

## Since

Questions 1 and 2 are answered, and the three acts they gated are built.

**The axis under question 1 is not head versus non-head.** It is where the
new content comes from. `amend` means *rewrite this revision*: the folder
supplies content, `-m` supplies the message. On a middle revision the folder
cannot speak (0030), so the content axis is simply unavailable, and
`amend <mid> -m` is not a second act — it is `amend` with one axis empty.
That reading keeps `amend` at one meaning and puts the teaching in the
refusal, which is 0021's job anyway: a bare `amend <mid>` names the reword
and the flag that performs it. A `reword` command would have been a name
minted for a temporary restriction, and would collapse into `amend -m` with
nothing of its own left the day 0030's working-from-the-past lands.

**Abandonment is the opposite case, and the asymmetry is the argument.** For
`amend`, the flagless case *refuses*; for `abandon`, the flagless case
*acts*, and would act differently before and after this document. The
existing sentence is "this revision and everything standing on it", and a
carrying abandonment preserves exactly what that destroys. So the existing
sentence keeps the bare spelling and the new act is `abandon <target>
--only` — which names the person's intent, the carry being its consequence.
`--only` also composes with the run form the unflagged command still takes.

**Question 2 dissolves once the two acts are read as one.** There is no
second primitive in the human move: same restating, same refusals, and the
only difference is provenance — which is a difference this document already
states as a pair of 0010's rows. So it is `historica carry <target> --onto
<destination>`, and `carry`'s sentence widens by one word: *restate work
against a different parent*. Without `--onto`, a rewrite the store holds
decided, everything derives, and two replicas converge. With it, a person
decided, so that one revision takes a reading of the clock — and everything
carried above it derives from that, so the stack converges exactly as a
repair's does. No top-level `move`, so `--move` keeps its meaning; `rebase`
stays another tool's word for another tool's guarantee, which is the one
that leaves markers in a folder where this refuses whole.

**"Amending a head" above presumed something that cannot happen.** A
revision anything stands on is not a tip, and `amend` had always refused
one, so the sentence "the descendants are carried, parents first" described
a case with no descendants in it. What the lifted refusal actually reaches
is the reword, and its carries are always verbatim. So: the content-amend
path never carries anything, and the reword path always carries, and always
without writing an operation document. That is a simplification of the
design rather than a change to it, and it is what the tests assert.

**All-or-nothing needed one thing the store did not have.** A carry is
planned against a store that already holds the revision being carried onto,
and the inline acts have to plan theirs before writing anything. So a
revision can now be held in memory alone — `Store::provisionally`, taken
back by `Store::withdraw` — for exactly as long as one planner runs. A
refusal therefore leaves `revisions/` and `operations/` byte-identical.
(`cache/` is not: it is nobody's, per 0035, and every command that reads a
store may rewrite it.)

**An inline act carries only what it stranded.** `Carrying::By` is that
restriction. A half-delivered rewrite somebody else's transport left in the
store stays `carry`'s to repair, because sweeping it into an amendment
would make one command mean two.

The library signatures moved with this: `carry::plan` and `carry::carry`
take a `Carrying` rather than an `Option<&RevisionId>`, `abandonment_plan`
takes the `only` flag, `Abandoning` gains `only`, and `Amended` and
`Abandoned` gain the plan they carried.

## Deferred

**Duplicating a change** — the same restating with a fresh change ID and no
`supersedes`, which is what cherry-pick means in a model with two
identities. The primitive supports it in an afternoon; wanting it is
undemonstrated in a journal.

**Squash as a command.** 0001's supersession across changes already spells
the fact; the act that writes it wants its own decision.

**Content-amending a non-head**, which is 0030's working-from-the-past,
deferred whole there and not reopened here.

**Rewording in an editor**, still 0023's deferral, now with one more
command that would use it.

## Consequences

- `src/record/carry.rs` is the planner and the writer: `plan` works
  everything out to the digest with nothing written, `carry` writes what it
  planned, and `merge::merge` takes the synthetic concurrent stream as
  ordinary events — `crate::diff` is reused, not rethought. The writer's
  carried-along row and `06-rebased.rev` stop being speculative. **This is
  the half that is built**; `amend` and `abandon` keep their descendant
  refusals until open question 1 has its answer, and the human move waits
  on question 2.
- 0023 gains a `## Since`: the sketch corrected, the manual repair retired
  where the carry is clean. 0013's and 0011's refusals become citations to
  this document when their walls lift.
- The tests worth naming, `tests/cli.rs`'s carry set among them: two
  replicas that receive each other and both run `carry` write one revision,
  byte for byte, under one filename — the whole promise in one assertion; a
  carry across a reword restates nothing and `operations/` gains nothing; a
  contested carry refuses with the store byte-identical to how it found it;
  the repair run twice finds nothing the second time; and `check`'s note
  names no revision once `carry` has run.
- One promise is added to the ledger: the diff decomposition participates
  in cross-replica convergence, and changes to it carry the trailer above.
