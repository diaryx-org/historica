# 0012 — Showing a conflict, and recording its resolution

Decisions 0007 and 0008 decided every kind of contest this format can produce,
and each ended the same way: the algorithm never fails, it reports where
concurrent work met, and what a person is shown "is interface work". This is
that work.

Nothing here changes the model. `merge` already returns content plus a list of
`Contested` spans — `Insertion`, `Deletion`, `Terminator` — and 0008 already
resolves the tree: a `drop` concurrent with an edit loses, two concurrent
`move`s resolve to the lower digest, two files claiming one path keep both
identities. Every one of those is reported. This decides what happens next.

## The decision

- **No conflicted state is recorded, and none is stored.** A conflict is a
  function of the graph, so the two heads *are* the conflict.
- **`historica merge <target>`** writes the merged content into the working
  copy, rendering contested spans with markers, and prints the command that
  records it.
- **`historica record --merge <target>`** recomputes the merge, diffs the
  working copy against *the merge result*, and refuses while any line the
  renderer wrote survives anywhere in a contested file.
- **A contested path is stated on the command line**, `--at <file>=<path>`,
  because a path is a value rather than prose and there is nothing to edit.
- **Nothing is remembered between commands.** 0011's rule holds: the pending
  merge lives in the person's terminal, not in the repository.

## What the other systems store, and why this stores nothing

Git and Mercurial keep the conflict in the working copy as markers, plus a
per-machine index or merge-state file. The conflict does not travel, and the
markers can be committed by accident — a file full of `<<<<<<<` is valid
content that nobody wrote.

Pijul keeps it in the pristine: a conflict is a property of the patch graph,
the marked-up file is a view of it, and every replica sees the same conflict.
Jujutsu keeps it in the commit: a conflicted tree is a real object that can be
shared, rebased, and resolved later.

Historica already has Pijul's property and needs to store nothing to get it.
0007 makes a merge a pure function of the event graph — "the structure that
resolves concurrency is built during that walk and thrown away at the end, so
nothing a merge needs is ever written down." Two replicas holding the same
files compute the same contests, in the same places, in the same order. A
conflicted state in the format would be storing what is already derivable,
which is the one thing 0007 forbids by name.

Jujutsu's argument for storing them does not reach here either. What jj can
share and two heads cannot is a *half-resolution*, and it can only do that
because its working copy is itself a commit. Here the working copy is not
history: a half-resolution is a folder, and sharing a folder is copying it,
which is what people already do with these repositories (0003: sync is union by
copy). The conflict travels as two heads; the half-fix travels as a directory;
neither needs a concept in the format.

## The rendering

A contested span is written into the file between marker lines, with each run
inside it labelled by the revision that wrote it:

```text
vvv historica: 4cf00b8c wrote vvv
The entry stands as it was.
vvv historica: d56419e5 wrote vvv
The entry has been reworded.
^^^ historica: resolve, then delete these lines ^^^
```

Three things about this are deliberate.

**The runs are labelled, not the sides.** A merge here is a graph replay rather
than a three-way diff, so there is no base and there are not necessarily two
sides. What there is, is a merged order with each item traceable to the
revision that wrote it — item *i* of revision *R* is named `(R, i)`, and 0007
derives that name rather than storing it. So the rendering shows the real
merged order with authorship attached, which is more than a three-way tool can
say and is free here.

**A `Deletion` contest has no text to fence.** `Contested { len: 0 }` is a
contest over items that are gone: one revision removed what another wrote
beside. It renders as a single line naming both revisions, which the person
deletes to acknowledge. That deletion is the whole resolution, and requiring it
means a removal nobody saw cannot pass silently.

**A `Terminator` contest is reported and not rendered.** Two branches
disagreeing about a final newline is not a span anybody can mark up. The file
ends how the recorded file ends, and `merge` says so on the terminal.

## Detection is content-addressed, which is what frees the spelling

Git chose `<<<<<<<` for improbability, because grep is all it has: the commit
is a different act from the merge, and nothing at commit time knows what the
merge wrote.

Here the merge is recomputable, so `record --merge` knows exactly which lines
the renderer wrote into which file. The rule is per-line and scoped: **while
recording a merge, a contested file holding any line the renderer produced for
it is refused.** Per-line rather than per-span, because a person can edit
inside a span and leave the fence standing; scoped to the merge record, because
a document *about* merge markers is ordinary content the rest of the time.

Two consequences Git cannot have. Markers cannot be recorded by accident. And
this document — which contains its own marker lines a few paragraphs up —
records without complaint, because no merge rendered them here.

The same recomputation is what makes `historica merge` safe to re-run. It can
tell its own rendering from a person's edits, so it declines to overwrite a
file somebody has started fixing rather than silently restoring the conflict.

## A resolution is ordinary content

The merged content is derived, so a merge revision does not record it. What it
records is the difference between the derived merge and the file the person
left — which is exactly what a resolution is, and exactly what the format
already expects: `tests/corpus/revisions/04-merge.rev` names no operation
document at all, because it changed nothing about any file.

So `record --merge` diffs against the merge result rather than against either
parent, and 0009's writer produces the operations from there. A merge that
needed no help records no operations. A merge somebody edited records the edit,
against a state both replicas can recompute.

## Contested paths are arguments

There is nothing to edit for a path. 0008 forbids the format inventing one — "a
name invented by a merge is content nobody wrote" — so the person supplies it,
on the command line, in the shape 0011 already uses for a rename:

```console
$ historica record --merge kxryzmor --at swtlmnkq=docs/README.md
```

Two files claiming one path is the case where the working copy cannot show the
truth: a folder holds one file per name. `merge` writes the lower-digest file
at the contested path and the other beside it under a rendered name —
`README.md (historica: swtlmnkq)` — which is a rendering exactly as the markers
are, is not a name anything records, and is refused at record time until `--at`
says where that file actually goes.

The other two tree contests need no argument, because 0008 already decided
them and both outcomes are things a person can undo with an ordinary revision:
a `drop` that lost to an edit leaves the file in place, and two concurrent
`move`s leave it at the lower digest's path. Both are printed by `merge`, so
the person knows what was decided for them.

## Refusal is whole-record

A merge with three contested files and one of them fixed records nothing. 0011
makes one record cover every changed tracked file, and per-file recording would
need the index it rejected; more to the point, a partially resolved merge is a
state, and the only place to keep it would be the repository.

The person's escape is the same as everywhere else: the folder is theirs, and
they may take as long as they like. Nothing is pending, because nothing was
written down.

## Rejected alternatives

**A conflicted state in the format**, as jj records. It stores what the graph
already implies, and 0007 rejects that in its first paragraph.

**A per-machine merge state**, as Git's index. Same objection, plus 0011's:
state that does not travel produces a repository whose meaning depends on which
machine is looking.

**Improbable markers.** Above: improbability is what a tool needs when its only
check is a string search.

**Inventing a name for a contested path** rather than asking. 0008 refuses it,
and a folder with `README.md` and `README-2.md` in it teaches a person a lie
about what history holds.

**Resolving a contest by timestamp** — the newer edit wins. 0002 refuses to
trust timestamps for anything, and 0008 already broke every tree tie by digest
for that reason.

**Rendering a base**, as a three-way tool does. There is no base: the merge is
a replay of a graph, and the nearest common ancestor is not what produced the
result.

## Consequences

- `historica merge <target>` and `historica record --merge <target>
  [--at <file>=<path>]` are owed, as is the renderer, which needs one thing the
  library does not yet expose: **which revision wrote each item**. `Merged`
  returns the state and the contested spans; the walk knows the origin of every
  item, since names are `(R, i)`, but `State` holds `Item`s carrying only text
  and a terminator. Surfacing the origin — in the merge result, not in the
  format — is the API change this decision costs.
- Wiring `merge` into the store, which the README already names as owed,
  gains its consumer: `Store::content` at a merge, `check` past a merge, and
  this.
- Tests worth naming: a file holding marker lines records fine outside a merge
  and is refused inside one; a merge that needed no help records no operation
  document; a resolution records operations against the merge result rather
  than against either parent; a contested path refuses until `--at` names it;
  and `merge` re-run on a half-fixed file leaves the file alone.
- 0007's and 0008's interface deferrals are answered for merging. Checkout and
  status are still 0008's, and still owed.

## Deferred

**Sharing a half-resolution.** Copying the folder is the answer today. If
handing somebody a partly resolved merge ever becomes routine rather than
occasional, the thing to reach for is a way to record a resolution *in
progress* as ordinary content on a branch of its own — not a conflicted state
in the format.

**A renderer for very large contested spans**, where showing both runs inline
is worse than showing a summary and letting a person open two files. This is
the same interface question `status` will raise, and belongs with it.
