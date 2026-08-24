# 0047 — One spelling for the format

Every document has opened with a numbered preamble — `historica-v0` through
`historica-v5` — since decision 0004 made the first line say how to read the
rest. The number was the gate: a writer claimed the lowest version that could
express its document, a reader refused any version it did not know, and 0004's
asymmetry meant a reader's vocabulary only ever grew. Six versions accumulated
in one year of development, one per grammar change, and nothing was ever
published under any of them.

That machinery was built for a world this format never entered. Version
numbers earn their keep when old readers and new writers coexist — when a
store written today must open under a reader shipped last spring. Before a
first release there are no shipped readers, so what the six numbers actually
recorded was the order this format was designed in: `historica-v0` is not a
compatibility level anyone depends on, it is a fossil of the week before
decision 0017. Carrying the fossil forward costs real weight — a `Version`
enum threaded through every parser, a lowest-version computation in every
writer, a raise-only header in every store, an export that recomputes the
minimum over everything travelling — and buys compatibility with stores only
this repository's own tests ever wrote.

## The decision

- **The preamble is `historica`, unnumbered.** One spelling, for every
  document and for the store header's first line. The gate 0004 built is
  unchanged in kind: a reader that meets any other spelling there refuses the
  document rather than guessing at what it would be leaving out.

- **The grammar below it is the union the versions were converging on.**
  Payloads (`text`, `bytes` — 0017), forgetting (`forgets`, `\ forgotten` —
  0014), `result` (0031), resolutions (0032), `mode` (0034), and `link`
  (0040) are simply the grammar now, gated by nothing. The one spelling the
  versions retired stays retired: `add` with `edit` — version 0's creation —
  is a contradiction, because an edit's positions count into a file at the
  revision's parents and a file added here is not there.

- **The pre-1.0 spellings are used up, and are refused by name.** A reader
  meeting `historica-v0` through `historica-v5` says what it met: a pre-1.0
  format this release no longer reads, which a 0.x release still does. No
  future grammar may reuse those spellings — a preamble whose meaning changed
  under a document would be the silent misreading this format exists to make
  impossible.

- **No migration.** Nothing was published under the numbered formats and no
  store outside this repository holds them, so the flattening orphans nothing.
  A pre-1.0 store that mattered would be read with a 0.x release and re-
  recorded; no command pretends that rewrite is not a rewrite, because
  re-preambling a content-addressed store changes every digest in it.

- **A future break takes a new spelling, not a number.** If the grammar must
  ever change incompatibly, the new format spells its preamble some other way
  — `historica-2`, say — and this reader refuses it at line one, exactly as a
  pre-1.0 reader refuses `historica`. Additive changes need none of that: an
  unknown header is already refused by 0004's strictness, so a document using
  a header this reader lacks fails closed, named, at the line that uses it.

## What this supersedes

0004's parser contract stands — strict reading, canonical identity, refusal
over guessing. What this retires is its versioning half: "a version constrains
writers, never readers" and the promise that every version 0 document parses
forever were promises to readers that were never shipped. The per-version
claims recorded in 0017, 0031, 0034, and 0040 are history, accurate about the
order things were decided and no longer describing a spelling any document
carries.

`result` keeps 0031's judgement rather than gaining a mandate: every document
this tool writes states one, a forgetting document must not (its result is the
destroyed state, and a digest would confirm a guess at it), and a hand-written
document that omits one has lost the replay checkpoint, not its meaning. The
alternative — refusing a document without it — was considered and declined,
because several corpus documents deliberately quote only part of their parent,
and a `result` nobody can compute honestly is worse than one honestly absent.

## Consequences

The `Version` enum, the `needs()` computations, the store's raise-only header
writing, and the export's minimum-version pass are gone. The store header is
written once by `init` and never moves. Every corpus document re-spells its
preamble, which — identity being content — renamed every document and cascaded
through every `parent`, `supersedes`, `edit`, and `keep` line that named one;
the corpus's creations now arrive as 0017 payloads, because the spelling that
created files through operation documents no longer parses. `tests/by-hand.sh`
still writes the merged corpus byte for byte, with one fewer thing to explain.

This is the format 1.0 ships: the preamble is a promise that the grammar under
it does not change, kept by refusing at one line everything that would break
it.
