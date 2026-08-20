# 0013 — Abandoning work, and pruning a store

Two acts that sound like one. **Abandoning** is a fact recorded in the graph:
this work is no longer part of the history I mean. **Pruning** is disk: these
bytes are no longer worth keeping here. The first converges across replicas
because it is written down. The second cannot, because deleting a file is not
a fact anything can observe.

Keeping them apart is most of this decision.

## The decision

- **Abandoning is supersession by a revision of a newly minted change.** The
  tombstone stands where the abandoned revision stood, records nothing, and
  carries a message, which is required.
- **One tombstone may abandon a run**, since `supersedes` repeats.
- **`historica prune` deletes a revision document that is superseded by a
  revision this store holds and named as a parent by none**, and any operation
  document nothing kept names. Nothing else is ever deleted.
- **Pruning is local, manual, and printed.** It does not propagate, it is not
  secrecy, and it is the undo history.

## Abandoning already had a spelling

Decision 0001 defines `ChangeState::Abandoned` as every revision of a change
being superseded by revisions of *other* changes, and calls it a legitimate
state — "the work was squashed elsewhere or abandoned, so the change ID still
names something real but has no current revision of its own." Throwing work
away is that state reached deliberately. The revision that reaches it looks
like this:

```text
historica-v0
change qpvuntsmwlrkzxonmvtplsyq        <- newly minted
parent 055465518aec3b40b52fbb1118130149981f9d145cdd38afa8c19730504b0ded
supersedes 6397b3a4b3b8abd444da81f2f731dd67c4f5bcea5dc03c4e8141783d1f1b4c53
author Adam Harris <adam@example.com>
when 2026-08-20T09:14:02-06:00
revised 2026-08-20T09:14:02-06:00

Abandon the draft: the argument does not survive its own example
```

No tree facts and no operations. **The content falls out of the ancestry**:
the tree and the file states at the tombstone are its parents', and the
abandoned revision is not among them. Nothing has to be undone, because nothing
that was undone was ever an ancestor.

The change ID is minted rather than reused, which is what makes the old change
`Abandoned` rather than merely empty. A revision *of the same change* that did
nothing would leave that change resolved — present in every log, pointing at a
revision that says nothing happened. Minting says the true thing: this work was
replaced, and what replaced it was a decision to stop.

A tombstone is an ordinary revision in every other respect. It is a head, work
continues from it, `arrange` gives it a filename, and it is never itself
superseded unless somebody supersedes it — abandoning an abandonment being a
thing a person may legitimately do.

## The message is required

0002 says "nobody should be made to describe work before they are allowed to
record it", and 0011 keeps an empty message allowed for `record`. Abandoning is
the exception, because the reason is the only thing the revision carries.

A tombstone with no message is a hole in the log: a revision that adds nothing,
edits nothing, and explains nothing, sitting where work used to be. The
question it raises — *why is this gone* — is the one question the history is
being asked to answer, and it is being asked by a person who no longer has the
work in front of them. `arrange` would file it under a change ID prefix, too,
which is the fallback for a message that says nothing.

## What abandoning does not do yet

Abandoning a revision that has descendants means reparenting them: their
operations are stated against a parent whose content is about to change, and
restating them is transforming operations against operations — 0007's merge
under another name, and the same wall `record --amend` meets in 0011.

So the first version abandons a head, or a run ending at one, and refuses
anything else in the library's own words. That covers the case people reach for
most: the draft that did not work out, which is at the tip because they were
just writing it.

## What prune may delete

Exactly two things.

**A revision document that is superseded and orphaned.** Superseded by some
revision this store holds — the evidence is on the successor, which is why 0001
put it there — and named as `parent` by nothing this store holds. The second
half matters: an amended revision may still be the parent of a descendant
nobody has rebased yet, and deleting it would leave a history that cannot
materialise its own head. A missing parent is only a note (0006) because
transport has more to deliver; manufacturing one deliberately is a different
act.

**An operation document nothing kept names.** 0007 lets two revisions with
byte-identical edits share one document, so this is a reference count over
digests, not a walk down one revision's `edit` lines.

Nothing else, and one exclusion is worth stating outright: **a head that no
bookmark names is not garbage.** Git reaps unreferenced objects because its
reflog and index make "unreferenced" mean "discarded"; here it means "work
whose author has not given it a name". The graph says what was replaced. That
is the only statement about disposability this format makes, and prune may act
on no other.

`prune` refuses to run on a store `check` calls broken, prints every file it
removes, and `--dry-run` prints them without removing. Running it twice removes
nothing the second time, and a pruned store is one `check` still accepts —
which it already is, since 0006 ruled that a `supersedes` naming no file is
neither an error nor a note, because "reporting it would report the feature".

## Three things prune cannot promise

**It does not propagate.** The store is a grow-only set unioned by copy (0003).
Deleting a file here deletes nothing there, and the next sync may bring it
back. Pruning is disk management on one machine, and saying otherwise would be
a lie a distributed system cannot make true.

**It is not secrecy.** A password recorded and then amended away exists on
every replica that already has it, and its digest stays legible in the
successor's `supersedes` line forever. The answer is the one every
content-addressed system gives: rotate the secret. A tool that implied
otherwise would be worse than one that says nothing.

**It is your undo.** There is no operation log here — no reflog, no `jj op
restore` — so a superseded revision *is* the record of what a thing was before
it was amended. Prune empties that, on purpose, and prints enough to make the
loss visible. Undoing and pruning are not activities to interleave, which is
why prune has no policy knob to make them safer: an age threshold would be a
number that has to live somewhere and would still be wrong for somebody.

## Never automatic

Nothing deletes a readable file except a person asking for it in those words.
An append-only store that quietly removes files is not append-only, and the
promise this project makes about its files — that they are the authority, and
that they are still there — is not one to qualify with a background task.

## Rejected alternatives

**A local list of hidden changes**, as a per-machine file. It does not
converge: the change reappears the moment another replica syncs back, and now
two machines disagree about what the history means, with nothing in the graph
to settle it.

**Deleting the abandoned revision instead of recording a tombstone.** Same
failure, sharper: the file comes back on the next sync, and nothing anywhere
says it was ever abandoned. Recording the intention is what makes abandonment a
fact rather than an absence.

**A do-not-resurrect record**, to make deletion propagate. Permanent state that
grows forever, can never be complete, and turns every replica into a
gravekeeper for work nobody wants.

**Reaping unreferenced heads.** Above: unreferenced means unnamed, not
discarded.

**An age policy** — prune what has been superseded for a fortnight. It puts a
number in a config file for a judgement that belongs to a person, and it still
deletes the amendment somebody wanted back on day fifteen.

**Pruning on record**, or on any other command. Above.

## Consequences

- `historica abandon <target> -m <message>` writes the tombstone, refusing a
  revision with descendants and refusing an empty message. `historica prune
  [--dry-run]` removes the two kinds of file above and prints each one.
- Neither needs a format change. Both are commands over facts 0001, 0002, and
  0006 already provide, which is the evidence that supersession was the right
  primitive.
- Tests worth naming: abandoning a head makes its change `Abandoned` and the
  tombstone the head; content at the tombstone equals content at its parent; a
  pruned store still passes `check`; prune leaves a superseded revision alone
  while any revision still names it as a parent; an operation document shared
  by two revisions survives the pruning of one; and prune run twice is a
  no-op.
- `cache/` is not prune's business. It is disposable by 0003 and removable with
  `rm -r`, and a command that deleted both would blur the one distinction this
  document exists to keep.

## Deferred

**Abandoning with descendants**, which waits on `merge` reaching the store, as
`record --amend` does.

**Resurrection after sync.** A pruned revision that returns is not an error and
is not reported as one; whether a person wants to be told that pruning was
undone by a sync is an interface question, and the answer probably depends on
how often it happens to somebody.
