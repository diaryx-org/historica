# 0039 — Recording some of the folder

0011 decided that one record covers every changed tracked file, and spent most
of its length on why:

> There is no index. An index is a second place work can hide, and 0007 already
> makes every operation a permanent event — a person who wants one topic per
> revision gets it by recording more often, not by curating a buffer.

That still holds, and nothing here touches it. What it does not answer is the
question a person asks about ten minutes into using this: they have edited four
files, two of them are the fix and two of them are a thought they had on the
way, and they want the fix recorded now. Today the answer is *record all four,
or move two of them out of the folder and put them back afterwards* — which is
a curated buffer with worse tools, kept in a place `status` cannot see.

The distinction that makes the answer easy is one this project has been making
since 0002: **historica records observed states, never hypothetical ones.** An
index is hypothetical. It holds a version of a file that is in neither the
folder nor the history, and the revision it produces describes a state that
never existed anywhere. Naming paths is not that. The named files are compared
with the tree exactly as they always were, and the unnamed ones are simply not
looked at — which is a smaller claim, not a false one.

## The decision

- **`record <path>...` restricts the survey to those paths.** Every other
  tracked path is left uncompared: nothing is recorded about it, nothing is
  written to it, and the next survey that does look at it sees whatever the
  folder holds.
- **A path is a file the folder holds, or a path the tree holds and the folder
  does not.** The second records the deletion, because absence is observed —
  0011's reason for having no `--drop` is also the reason a deletion needs no
  special spelling here.
- **A path naming a directory names every file beneath it.** There are no
  directories in this format (0008), so it can mean nothing else.
- **A path neither the folder nor the history holds is refused**, and so is one
  a `skip` rule covers. The two have different fixes, so they are different
  messages.
- **A restriction may not spell half a rename.** `--move a=b` requires both `a`
  and `b` inside it, and names both when it refuses.
- **A merge cannot be restricted.** 0032 makes a merge state what every
  contested file *is*; a merge of some of them leaves the rest joined and
  unstated.
- **Path arguments are normalised, as every other path arriving from outside
  is** — 0033, so a person's NFD keyboard finds the store's NFC path.
- **`amend` takes no paths.** 0023 has it restate the whole of what its
  predecessor said, so there is no half of the folder to ask it about.

## Why this is not an index

Three properties, and an index fails all three.

**Nothing is remembered between commands.** A restriction is one argument list.
It lives for the length of the command that carries it, and there is no file it
could be written into and no state a later command could inherit. 0011's rule
survives intact.

**Nothing hides.** The unnamed files are still in the folder, still tracked,
and `status` still lists every one of them, because `status` surveys
everything and always will. The failure an index produces — work that is real,
uncommitted, and invisible — has nowhere to happen: there is exactly one place
to look and it is the same place it was.

**Every recorded fact was observed.** The revision says what the named files
are, and each of those is a file that was on disk, in that state, at that
moment. An index can record a hunk of a file that no file ever held; this
cannot record anything at all that the folder did not say.

## What a restriction may not do

The refusals are all one rule: a restriction narrows what is *looked at*, and
it may never change what a fact *means*.

A rename is the case that makes this concrete. `--move a=b` is the one fact
0011 says a person must state, and it is a fact about two paths. A restriction
holding one of them would record `a` deleted, or `b` arriving out of nowhere —
a false statement assembled out of two true ones, which is exactly the failure
mode 0008 minted file identifiers to avoid. So both ends, or neither.

The merge is the same rule at the level of a revision. 0032 made a merge state
its resolution outright, for every contested file, precisely so that nobody has
to reconstruct what was resolved from a walk. A partial merge would join two
lines of work and stay silent about some of the files it joined, which is a
revision that means something other than what it says.

The refusal a person is most likely to hit is neither: it is naming a path that
does not exist, usually because it was typed wrong. That is refused rather than
quietly recording nothing, on 0011's argument about files that cannot be
recorded — a person who believes work is in history and finds later that it is
not has lost it, and the difference is one error message.

## Rejected alternatives

**`-a`, and paths meaning something else.** Inverting the default so that
`record` with no arguments records nothing would break every existing use and
buy nothing: the whole folder is the right default in a tool for prose.

**A `--only` flag rather than positional paths.** The flag reads as if the
restriction were unusual. It is the ordinary thing a person wants some of the
time, and `record notes.md` is what they will type whether or not it works.

**Recording a hunk.** `record --patch` is an index with the serial numbers
filed off: what it writes is a state no file was ever in. If a person wants
half a file recorded, the way to get it is to have half a file, which is
editing.

**Silently ignoring an unknown path.** Above. It is the one way a restriction
could lose work.

**Restricting `status`.** `status` answers how the folder and the store differ,
and an answer about some of the difference is one a person has to remember the
shape of. It stays whole.

## Consequences

- `record::Restriction` is the value, `Recording` carries it, and `survey`
  takes it: the library decides all of this, and the front end passes an
  argument list through.
- `record::check_restriction` is the half that needs no folder — the merge and
  the half-a-rename — so a front end can ask before it performs a stated
  rename. A refusal that rearranged the folder on its way to saying no would
  have done something.
- A restriction narrows the refusals too. A symlink in a corner of the folder
  stops an unrestricted record, and does not stop a record about one file
  elsewhere, because that file is not among the ones being looked at.
- `Skipped::skips_directory` becomes public, so a command can tell "no such
  path" from "a rule keeps that path out".

## Deferred

**Paths for `status`.** Above, and it stays whole.

**A path relative to the working directory rather than the repository.** Every
path argument this front end takes is repository-relative today — `--move`,
`--at`, `--accept`, `cat` — and one command resolving them differently would
be worse than all of them being what they are. If that changes it should change
everywhere at once.
