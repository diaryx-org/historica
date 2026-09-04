---
title: Saying what a command wrote
description: Implement 0074's `historica-wrote-1` — the `--fields` flag on the writing commands, the parser beside the writer, and the four things the decision has to settle first
status: done
created: 2026-09-02
updated: 2026-09-03
part_of: "[Tasks](tasks.md)"
---

# Saying what a command wrote

**Status: done.** 0074 carries seven amendments rather than the four argued
below; `historica::wrote` is the grammar, writer and parser together;
`--fields` is on the nine commands the amended roster names; and
`cli/tests/wrote.rs` holds every statement to the store that made it.

Three things came out differently from the plan below, each argued in 0074:

- **`merge` is not on the roster.** It reads the store and writes the folder,
  so every statement it could make would be the empty one — which under this
  format's own rule is a lie told by a true sentence. It is deferred with
  `update` and `status`.
- **`Received` and `Fetched` had to change**, from counts to the digests
  themselves. They were the two commands 0074 names that could not say where
  they wrote. That is a break, and it carries the `Behavioural-change:` trailer
  the flag itself does not owe.
- **A failed command still prints a statement**, handled once in `run` rather
  than threaded through every error in the library. The paths worth covering
  are the ones a command has no answer for, and those never reach the printing
  at the end of it.

What is left for somebody else: `fetch --fields` is not driven end to end,
because the command-line path wants an HTTP server that the tests do not stand
up; what it prints from is asserted where the library's fetch is. And the two
sidecar tasks below are unblocked only once the parser is published, since they
depend on `historica` by version.

[0074](../decisions/0074-saying-where-to-look.md) was argued and nothing
implemented it. `grep -rn historica-wrote src cli tests docs` finds nothing, so
this is the whole of the writing half: the grammar, the flag on each writing
command, the parser, the corpus comparison, and the guide.

The reading half exists — 0064's `historica-log-1` — and it is the model for
all of this, including what a caller is owed when there is nothing to say.

## Settle the decision first — done

**These are in 0074 as of the amendment ahead of this work**, along with three
more the reading of the code turned up: the roster of commands that take the
flag, the grammar living in the library rather than in `render.rs`, and the
digests `Received` and `Fetched` have to start carrying. They are kept below as
the argument for what the decision now says.

Four things 0074 did not say, or said wrongly. They were edits to the decision
document, and they came before the code because two of them change the
grammar.

**A bookmark name can hold a space, so `name` and `unname` take the rest of the
line.** 0074 says the vocabulary has no path in it and leans on 0064's "no field
can hold a space, and that is not luck". That does not survive
[0071](../decisions/0071-a-name-with-structure-in-it.md), which makes a name a
path with no *leading or trailing* space — `feature/two words` is a legal
bookmark. The fix is 0074's own rule, that a path goes last: say that `name` and
`unname` take everything after the first space, that a reader splits once, and
add a corpus case with an interior space. Without this the grammar is ambiguous
for a name somebody can actually create today.

**A deterministic line order.** 0074 does not give one, so the corpus comparison
is a set test and a wrapper that reads the statement as a stream has undefined
behaviour. Any rule will do; it only has to be written down and held to.

**What a failed write prints.** `carry` and `merge` write several documents, and
a command that fails partway has some of them on disk. The reading that keeps
0074's central property — every line is a claim the store can be held to — is to
print the statement for what is actually on disk and let the exit code carry the
failure. Say so, and say it for a non-zero exit generally.

**`receive --dry-run --fields` is refused.** `--dry-run` produces a plan, and a
plan cannot be held to anything, which is the one thing this header promises.
Refusing the two flags together is better than lending the header to a preview.
A machine-readable plan, if it is ever wanted, is its own header and its own
decision.

## The work

- `render::FIELDS_HEADER` gains a sibling and `render.rs` gains one writer for
  the grammar, since the vocabulary does not vary by command.
- Each writing command in `cli/src/cli/` grows `--fields`, suppressing the
  reading for a person. The values are the ones the library already returns —
  `Recorded`, `Amended`, `Abandoned` and their kin — so this adds no knowledge,
  only a spelling of it across a process boundary.
- **A public parser for `historica-wrote-1`, in the library, beside the
  writer.** 0074's consequences do not name it and it is the piece the sidecars
  need: `historica-minisign` and `historica-git` read this format from the far
  side of a pipe, and [0053](../decisions/0053-room-for-another-tool.md)
  says a side tool gets what it needs from the API rather than by writing a
  second implementation of a grammar we own. One implementation shared by the
  writer, the corpus test, and every consumer is also the only way the corpus
  comparison tests the thing callers actually use.
- `docs/cli.md` gains the grammar beside 0064's.
- The corpus gains 0074's comparison: for each writing command, the statement it
  made against the store it made.

## What this does not add

No hook, no observer trait, no post-write callback. An in-process host holds the
result value already and can call whatever it likes next; a command-line user
composes with a pipe:

```sh
historica record --fields -m 'note' | historica-minisign sign --wrote -
historica receive --fields ../other | historica-minisign verify --complete
```

Empty statement, wrapper does nothing — which is why the header-and-no-lines
case is the most useful line in the format. Making `historica record` run the
sidecar itself is what 0053 refused and
[0072](../decisions/0072-a-command-this-tool-does-not-have.md) restated; the
only automatic on offer is the person's own alias.

The two sides of that pipe are tasks in their own repositories:
`historica-minisign`'s *Signing a digest it was told about* and
`historica-git`'s *The run around every historica command*. Both are blocked on
the parser above.

## Done when

- The four amendments are in 0074, in the same change as or before the code.
- Every writing command takes `--fields`, and wrote-nothing is a header, no
  lines, exit zero.
- The parser is public, documented, and is what the corpus test and `cli` both
  use.
- The corpus comparison passes for every writing command, including a bookmark
  whose name holds an interior space.
- `docs/cli.md` documents the grammar, and the changelog's unreleased region
  says a flag arrived. No `Behavioural-change:` trailer is owed — 0074 says so,
  and it stays true only if the sentences a person sees are untouched.
