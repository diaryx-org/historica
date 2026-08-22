# 0002 — The revision document

A revision is one text file: a block of `key value` header lines, a blank line,
then the message verbatim to the end of the file.

```
historica-v0
change qpvuntsmwlrkzxonmvtplsyq
author Adam Harris <adam@example.com>
when 2025-08-19T00:47:11-06:00

Start the readable core

Model causality before content: immutable revisions, explicit parents, and a
history that merges by union. Nothing here chooses a document syntax yet.
```

That is `tests/corpus/revisions/01-root.rev`, and its [`RevisionId`] is what any
Unix system already computes for it:

```console
$ shasum -a 256 tests/corpus/revisions/01-root.rev
c9f5c7d252115911e399bccf5c24d16e34a21f9f8db2736746378edc4df68b68  …
```

[`RevisionId`]: ../../src/core/mod.rs

## The digest covers the file, not a re-serialised model

This is the decision the rest of the format falls out of.

A format that hashes a *parsed model* has to define a canonical serialisation
first, because two spellings of one model would otherwise produce two
identities. That is where formats acquire their unreadable rules: sorted keys,
normalised escapes, elided defaults, and a re-encoding step no person can
perform by hand.

Historica hashes the bytes on disk. A revision *is* its file, so:

- an unrecognised header cannot be dropped, because nothing is re-encoded;
- there is no second representation to disagree with the first;
- verification needs no Historica, only `shasum`;
- hand-editing a revision file does not corrupt it, it produces a different
  revision — which is honest, because the text changed.

Canonical form still matters, but as a *writing* discipline rather than a
prerequisite for identity. See "Two replicas must write the same bytes" below.

## Header rules

- A header line is a key, one space, then a value. The key is lowercase ASCII
  letters and hyphens; the value runs to the end of the line.
- No escaping and no quoting. A value is UTF-8 with no control characters, no
  leading or trailing space, and is never empty: an absent fact is an absent
  line.
- LF endings, UTF-8, no BOM. A carriage return is rejected rather than
  tolerated, because tolerating it would let an editor silently change a
  revision's identity.
- Keys appear in a fixed order: `change`, `parent`, `supersedes`, `author`,
  `when`, `revised-by`, `revised`, then any `x-` headers sorted by key.
  Decision 0004 made that order a parse rule rather than a habit.
- The header block is preceded by the `historica-v0` preamble line, which is
  not a header: it carries no value and its digit puts it outside the key
  grammar entirely. Decision 0004 has the reasoning.
- A repeated fact is a repeated line, so adding a parent is a one-line diff.

| Header | Required | Meaning |
| --- | --- | --- |
| `change` | exactly once | The change this revision is a version of. |
| `parent` | zero or more | A causal parent, by digest. None means a root. |
| `supersedes` | zero or more | A revision this one replaces, by digest. |
| `author` | once | Who did the work. Copied forward across rewrites. |
| `when` | once | When the work was done. Copied forward across rewrites. |
| `revised-by` | optional | Who produced *this revision*, when not the author. |
| `revised` | with `supersedes` | When this revision was produced. |
| `x-…` | zero or more | Advisory. A reader may ignore these. |

The two identities keep their alphabets from decision 0001: `change` is 24
characters of `k` to `z`, and every digest is 64 lowercase hex characters. A
person can tell at a glance which kind of name a line carries, and
`invalid/change-id-in-the-digest-alphabet.rev` records that mixing them is an
error rather than a convenience.

### Authorship survives rewriting; timestamps never mean anything

`author` and `when` describe the work and are copied into every later revision
of the change unchanged. `revised-by` and `revised` describe *this* revision,
and appear only once a revision has predecessors. In
`tests/corpus/revisions/05-amended.rev` a reviewer rewords someone else's
change, and the file states plainly that Adam wrote it on the 19th and Rowan
reworded it on the 20th.

No timestamp participates in identity, causality, or ordering — the core says
so already, and offsets are kept only because "I wrote this at 9pm my time" is
a fact a person cares about. Fractional seconds are not permitted: one less
spelling to reproduce.

The same rule settles two spellings RFC 3339 allows and this format does not.
`Z` is refused, because it and `+00:00` would be one fact written two ways, and
the offset is carried for what it says about the person rather than about the
instant. `-00:00` is refused because RFC 3339 gives it a *different* meaning —
offset unknown — which is a fact this format has no way to act on and every
reader would misread as UTC. A timestamp is therefore exactly
`YYYY-MM-DDThh:mm:ss±hh:mm`, and `src/format/timestamp.rs` accepts nothing
else.

## Two replicas must write the same bytes

Repeated keys are sorted by digest, and the key order is fixed, so that a
deterministic rewrite is deterministic in bytes too.

This is not tidiness. If two replicas independently rebase the same change onto
the same new parent — which is exactly what happens when both sides pull an
amended ancestor — canonical ordering makes them produce one revision that
merges by union. Unordered spellings would produce two revisions of one change
with identical content, and the user would be asked to resolve a divergence
that exists only because two machines sorted differently.

Sorting parents also states that no parent is privileged. Git's first-parent
rule quietly makes merge asymmetric and gives `log` a preferred side; a
convergent history should not have one. A view that wants to draw a mainline
can record that as a hint later, not as a hidden consequence of line order.

## The body is never interpreted

The message begins after the first blank line and runs to the last byte. It is
not parsed, trimmed, re-wrapped, or escaped.
`tests/corpus/revisions/07-verbatim-message.rev` therefore contains a line that
reads exactly like a `parent` header, a trailing space, a tab, non-ASCII
punctuation, and no final newline, and all of it survives.

A message may be empty, spelled as headers with no blank line and no body, as
in `04-merge.rev`. Nobody should be made to describe work before they are
allowed to record it.

The first line is a summary *by convention only*, for rendering. No length is
enforced and no error is raised, because a rule a person must obey to save
their work is a rule that will be resented.

## Strict where the machine reads, verbatim where the human writes

The header block is parsed strictly: one spelling per fact, and anything else
is an error naming the line and the fix. The body is accepted exactly as typed.

Strictness in the headers is what keeps a digest a trustworthy name — one byte
sequence per meaning, and one meaning per byte sequence. Leniency there would
mean a hand-edited file is a valid revision that no writer would ever emit, so
"tidy this up" would silently mint a second revision of the same work.
Friendliness belongs in the error message and in a `normalize` command, not in
a parser that guesses.

## Forward compatibility

An unknown header whose key begins with `x-` is advisory and may be ignored. An
unknown header without that prefix is a hard error: this revision needs a newer
Historica.

The alternative — ignoring what you do not understand — means an old reader
renders `signed-by` as unsigned, or a future `tree` header as an empty change,
and is confidently wrong about history. Refusing is friendlier than lying;
`invalid/unknown-required-header.rev` pins that down.

## SHA-256, declared by every revision

The digest is SHA-256. This section originally declared it once per repository,
in a readable file holding `historica 0` and `digest sha256`. Decision 0004
moved the declaration onto every revision, as the `historica-v0` preamble, so
that a `.rev` file in transit says which digest names it; the repository file
keeps the same one line. The reasoning below stands; only the location changed.

SHA-256 over BLAKE3 for one reason: `shasum -a 256` and `sha256sum` are already
installed everywhere, so a person can verify Historica's central claim without
Historica. `b3sum` is faster and is a reasonable later choice for large file
content, but a recovery story that requires installing a tool is weaker than
one that does not.

Declaring the algorithm per repository rather than labelling every reference
(`sha256:1a4f…`) keeps references short, keeps `RevisionId` a plain 32-byte
digest, and keeps one algorithm per repository instead of a mixture nobody can
reason about. Changing algorithm means rewriting a repository, which is
appropriately deliberate.

## What is deliberately absent

- **A revision does not state its own digest.** It cannot: the digest covers
  the bytes, so a header naming it would have to be inside what it describes.
  The digest lives in the file's name in the store and in the references other
  revisions make to it.
- **No content.** There is no `tree` header yet, because the tree model is a
  later decision. The revision document stays small and readable on purpose;
  file data belongs in separate documents it names.
- **No signatures**, and no store layout beyond "a revision file is named by
  its digest".

## The corpus

`tests/corpus/revisions/` is hand-written, and each file pins down something
the parser must get right.

| File | Pins down |
| --- | --- |
| `01-root.rev` | A root: no parents, summary plus detail. |
| `02-concurrent.rev` | One parent, a one-line message. |
| `03-other.rev` | A second author, a different UTC offset. |
| `04-merge.rev` | Two sorted parents, and an empty message. |
| `05-amended.rev` | Supersession, `revised-by`, and an `x-` header. |
| `06-rebased.rev` | A descendant rewritten because its parent was. |
| `07-verbatim-message.rev` | A body that must not be interpreted. |
| `invalid/carriage-returns.rev` | CRLF is rejected, not normalised. |
| `invalid/change-id-in-the-digest-alphabet.rev` | The alphabets stay disjoint. |
| `invalid/empty-header-value.rev` | An empty value is not an absent fact. |
| `invalid/unknown-required-header.rev` | Unknown non-`x-` headers refuse. |
| `invalid/missing-version-header.rev` | A revision must state its format. |
| `invalid/unknown-version.rev` | A newer version refuses rather than guesses. |
| `invalid/headers-out-of-order.rev` | Key order is a parse rule, not a habit. |
| `invalid/unsorted-parents.rev` | Repeated keys must be in digest order. |
| `invalid/empty-body-after-separator.rev` | An empty message omits the separator. |

The corpus is internally consistent: every `parent` and `supersedes` line holds
the real SHA-256 of another example, so the seven canonical files are a genuine
five-change history containing a merge, an amendment, and the rewrite that
amendment forced. `MANIFEST` is `shasum` output, so the whole corpus checks
with a standard tool:

```console
$ cd tests/corpus/revisions && shasum -a 256 -c MANIFEST
```

`tests/corpus.rs` is that promise kept: every canonical file parses and writes
back byte for byte, every invalid file is refused *for its own reason* rather
than merely refused, and the digests the model computes are checked against the
ones `shasum` printed into MANIFEST.

## Rejected alternatives

**TOML.** Readable, but canonicalisation is painful: several string forms,
escapes, inline versus sectioned tables, and no natural place for a multi-line
message that is not escaped or indented. A message is the part a person writes
most and should be the part a format touches least.

**JSON, canonicalised per RFC 8785.** A rigorous canonical form exists, which
is its only advantage. Messages become one line of `\n` escapes, diffs stop
being line diffs, and a person cannot edit history in a text editor without
thinking about quoting.

**YAML.** More spellings per meaning than TOML, plus type coercion surprises.
A format whose parsers disagree cannot back a digest.

**A binary log with a readable export.** Rejected already in `docs/loro.md`,
for the reason that governs here too: whatever a person can recover from must
be the authority, not a projection of it.

## Resolved questions

1. **A revision in transit has no repository to tell it the algorithm.**
   Answered by [0004](0004-parser-contract.md): every revision carries
   `historica-v0`, and the line of noise buys a self-describing file.
2. **Whether `author` and `when` should be copied forward.** Answered by
   [0005](0005-authorship.md): they are copied, because reading them from a
   change's first revision fails whenever that revision has been pruned —
   which is whenever rewriting has happened.
4. **Whether `x-` is the right escape hatch.** Answered by
   [0004](0004-parser-contract.md): it is kept. The usual objection assumes a
   format can retire a spelling, and a content-addressed one cannot.

## Resolved questions

3. **How paths that are not valid UTF-8 will be spelled** when trees arrive in
   decision 0008. The no-escaping rule cannot survive that untouched, and it
   would be better to choose an escape that is visible only when needed than to
   quote every path forever.

   Answered by [0008](0008-tree.md): paths are UTF-8, and a path that is not
   UTF-8 is refused rather than escaped.
