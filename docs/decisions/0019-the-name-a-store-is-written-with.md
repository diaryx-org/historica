# 0019 — The name a store is written with

0003 chose the writer's default and gave one reason for it:

> The writer still names files by digest, because that default is
> self-verifying and cannot conflict under any file sync — but nothing depends
> on it.

0006 built a readable scheme for revisions, 0016 built one for everything else,
0018 made it a path rather than a spelling of one, and all three left it behind
a command. So every store anyone makes is a wall of hashes until they learn
that `arrange` exists, and the folder 0003 promised is one command away rather
than in front of them. 0016 saw this coming and deferred it:

> **Whether `arrange` should run itself.** Nothing here is automatic, and a
> person who records a hundred revisions has a hundred hashes until they ask.
> The reason to leave it manual is that renaming under a sync tool is the thing
> most likely to produce conflicted copies, and the reason to reconsider is
> that a scheme nobody invokes is a scheme nobody has.

The reason it gave for waiting does not survive being looked at. It is an
argument about *renaming*, and a writer that puts the readable name on the file
the first time never renames anything.

## The decision

- **`record` writes every file at the name the scheme gives it.** Revisions as
  `YYYY-MM-DD summary.rev` (0006), operation documents and payloads under
  `<that stem>/<the path>` (0016, 0018). No file is written under a digest and
  renamed afterwards; the name it is created with is the name it keeps.
- **The collision rule is 0006's, unchanged**: two revisions wanting one name
  each take their change ID, and two revisions of one change fall through to
  the digest.
- **A digest name stays legal, everywhere, forever.** Nothing reads a name;
  `Store::open` is unchanged and could not tell the difference. A store written
  by another implementation, or by this one before today, is a correct store.
- **`arrange` stays and stops being the everyday command.** It applies the
  current scheme to a store that does not have it: one written by an older
  version, by another tool, by hand, or by no scheme at all.
- **`arrange` gains no `--check`, and `check` gains no finding.** A name that
  differs from the scheme is not a fault. This is argued below, because it was
  nearly built the other way.

## What a writer can know, and what it cannot

The property 0003 bought with digest names is worth naming precisely, because
this spends part of it. A digest name is a pure function of the file's bytes,
so no two distinct files ever want one name — without consulting anything,
without a lock, and without having seen the rest of the history.

An arranged name is a function of the date, the summary, and what else the
store holds. The first two a writer has. The third it has only for the
revisions that have reached it, and a replica recording offline has not seen
what the other one wrote this morning. So two revisions written on two machines
on one day under one summary want one filename, and the sync tool that carries
them keeps both — as `2026-08-20 Notes.rev` and `2026-08-20 Notes (conflicted
copy).rev`, or whatever that tool spells it.

Three things make that a cost worth paying rather than a hole:

- **It is already a state the format understands.** `check` reports a sync
  tool's conflicted copy as a note and says both files are legitimate
  revisions, because identity is content and neither file's bytes are in doubt.
  Nothing is lost, nothing is ambiguous, and the store still loads.
- **`arrange` settles it.** Once one replica holds both revisions, the scheme
  sees the collision and gives both their change ID, which is what it was
  always going to do.
- **It needs a coincidence.** The same calendar date in the author's own
  offset, the same summary after normalisation, and concurrent writing. A
  message that says nothing falls back to the change ID and cannot collide at
  all.

What is *not* traded away is anything about identity. A filename has never been
a claim this format relies on, and 0016 established the one exception and why
it does not reach here: `check` reports `FilenameLies` where a whole stem
parses as a digest and the bytes hash to something else. An arranged name does
not parse as a digest, so it makes no claim to be checked against.

## Why there is no lint

The obvious shape for a command that is no longer needed daily is `arrange
--check`: report what would move, exit non-zero, run it in CI. It is the wrong
shape, and the reason is worth writing down.

Once naming is the default, a name that differs from what the scheme would
write is one of four things:

1. **The scheme changed.** 0018 changed it last, and every arranged store is
   now spelled the old way. This is a migration.
2. **Another writer wrote it.** An older version of this tool, or a second
   implementation, which 0004 exists to make possible and which is entitled to
   name files however it likes.
3. **A person filed it themselves.** 0003 says a filename means everything to
   the person browsing the folder, and 0016 built a walk that recurses to any
   depth precisely so a person may file a history however they please.
4. **A sync tool's conflicted copy, or corruption.**

Only the fourth is a fault, and `check` reports the versions content can prove —
`DuplicateContent`, `FilenameLies`, `ImpossibleCollision`, `Unparsable`.
Decision 0027 removes `SyncSuffixed`, which guessed from a name rather than
content. A lint over names could not tell the third case from the first, so it
would report a person's deliberate filing as something to fix, in a store whose
central promise is that they may do exactly that.

So: `check` owns faults and looks at content. `arrange` applies a scheme and
looks at names. Neither is a lint over the other, and the fact that a store's
names are not the ones this version would have chosen is not a finding.

That also answers what "stale" means, which is a question that only has an
answer for cases 1 and 2 — a store written under a scheme this version does not
write any more. Case 3 is not stale, it is filed, and running `arrange` on it
is a person choosing to give that up.

## What `arrange` is now

The same command, run for different reasons: after upgrading, when adopting a
store written elsewhere, and when a person who filed things by hand wants the
scheme back. Its output is unchanged, its determinism rule is unchanged, and it
remains the only thing in this project that renames a file.

Its one new property is that on a store this version wrote, it does nothing —
which is the test that says the two agree.

## The one place they can disagree

`record` names a revision by asking the scheme what it should be called, given
the store as it stands and the revision about to join it. Where that produces a
collision, the new revision takes its change ID and the one already on disk
keeps the plain name it was written under — because `record` does not rename,
which is the whole point of writing the name in the first place. `arrange`,
seeing both, gives both their change ID.

So a store where two revisions collided is spelled one way by `record` and
another by `arrange`, until somebody runs it. Both are unambiguous, both load
identically, and the difference is one filename in a case that needs a
coincidence to arrive at. Making `record` rename the sibling would close it, at
the cost of putting a rename back into the write path for exactly the reason
0016 warned about.

## Consequences

- The naming scheme moves out of the `arrange` command and into the library, as
  `historica::naming`, because two callers now need it and only one of them is
  a command. `arrange` keeps every behaviour it had.
- `record` computes one stem for the revision it is about to write, and the
  filenames within it, before writing anything — which it can, because a stem
  needs `when`, the message, and the change ID, and all three are supplied
  rather than derived.
- `Store`'s writers take the name to write at. The digest-named ones remain,
  because a caller that has no scheme in mind should still get 0003's default.
- Content that the store already holds is still written once: an operation
  document or a payload two revisions name lives under the first revision that
  wrote it, which is 0016's rule about a shared document arrived at from the
  writing side.
- `historica init` and every reader are untouched.
- Every test that asserted digest filenames now asserts readable ones, which is
  the change being visible in the place it should be.

## Rejected alternatives

**Writing at a digest name and renaming immediately.** One line of code: finish
`record`, then run the placement pass. Rejected because it puts a create and a
rename into every write, which is the operation 0016 identified as most likely
to confuse a sync tool, and because a tool that does the wrong thing and
corrects it is a tool that is wrong for as long as the correction takes.

**Putting the change ID in every name**, so that a name is derived from the
document alone and the cross-replica collision cannot happen. Genuinely
tempting: it restores 0003's unconditional property, and the change ID is the
thing a person types at the command line, so the filename would teach it. It
loses to the listing it produces — `2026-08-20 qpvuntsm Start a journal.rev`
on every file, forever, to prevent a coincidence that resolves itself into a
note.

**Leaving the default alone and documenting `arrange` better.** The status quo
with a nicer README. A person who has not read it still has a folder of hashes,
and 0003's promise is about the folder rather than about the documentation.

**A lint.** Above: it cannot tell a person's filing from an old tool's.

## Resolved questions

1. **Whether `record` should rename a colliding sibling.** It does not, above.
   The case for reconsidering is that a store should not have two spellings of
   one scheme in it; the case against is that a write path that renames is the
   thing 0016 warned about, for a coincidence that `arrange` already settles.
   [0027](0027-closing-the-small-questions.md) keeps that boundary: `record`
   creates its chosen name or reports the collision; `arrange` alone tidies.
2. **Whether a person who has filed a store by hand should be able to say so**,
   so that a later `arrange` leaves it alone rather than undoing the work. A
   file in `history/` would do it, and it would be the second thing in this
   format that exists to record a preference.
   [0027](0027-closing-the-small-questions.md) adds no preference file: invoking
   `arrange` is the explicit request to apply its scheme.
