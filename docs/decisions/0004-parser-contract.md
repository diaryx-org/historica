# 0004 — The parser's contract

Decision 0002 left the reader's side of the format under-specified. It said the
header block is "parsed strictly", that repeated keys sort by digest, and that
unknown `x-` headers are advisory — but it did not say whether a file spelled
in some *other* valid-looking way is a different revision or no revision at
all. That gap has to close before a parser can be written, because it decides
what the parser is for.

This document answers 0002's open questions 1 and 4, and one question 0002 did
not know it had.

The contract has two halves:

> A parser accepts exactly what a writer would emit — and never less than it
> accepted yesterday.

## Strict reading recovers canonical identity

Hashing bytes rather than a parsed model (decision 0002) bought readability at
an apparent cost: two spellings of one set of facts would be two revisions of
identical meaning and different identity. Canonical *writing* was 0002's answer,
but a writing discipline binds only writers, and a hand-edited file has no
writer.

Enforcing the discipline on *reading* closes it. If the parser refuses every
spelling a canonical writer would not emit, then exactly one byte sequence per
set of facts parses, and the digest of the bytes and the digest of a canonical
serialisation of the model would agree — without a serialisation step existing
anywhere. The format keeps the property that made hashing a model attractive,
and pays none of its price: nothing is re-encoded, no unknown header is
dropped, and `shasum` remains the whole verification story.

So the parser rejects, naming the line and the fix:

- headers out of the fixed key order;
- repeated keys not in ascending digest order;
- a value with leading or trailing space, an empty value, or a control
  character;
- a carriage return anywhere;
- a `change` value outside `k`–`z`, or a digest outside lowercase hex;
- a required header missing, or a once-only header repeated.

None of this is tidiness. 0002 already stated the harm: leniency means a
hand-edited file is a valid revision no writer would emit, so normalising it
mints a second revision of the same work, and the person is shown a divergence
they did not create.

Sorting is checkable by eye — hex compares lexicographically and the key order
is seven names long — and the error message carries the correction, so `check`
can say "move line 3 below line 4; the file's digest becomes `…`". Rejecting a
file is not refusing to help. It is refusing to guess which of two meanings the
bytes had.

To that list one rule is added that 0002 did not know it needed:

- **A blank line must be followed by at least one byte.**

An empty message is spelled by omitting the separator entirely, as
`04-merge.rev` does. Without this rule, headers-then-EOF and
headers-then-blank-line-then-nothing are two byte sequences meaning one thing,
which is exactly what this document claims cannot happen — so the format would
have contradicted itself in its most common file, a merge nobody described. An
explicit `---` delimiter in place of the blank line would not have helped; it
has the identical hole.

The neighbouring case is not ambiguous and stays legal. A body that ends
without a final newline is a *different message* from one that ends with it,
because the body is verbatim, so those are two spellings of two facts rather
than one.

### What this does not make strict

The body is still verbatim to the last byte, still never interpreted, and still
allowed to end without a newline. Strictness stops at the blank line. The rule
is unchanged from 0002: strict where the machine reads, verbatim where the
human writes.

## Every revision states its format

A revision opens with a preamble line naming the format and its version:

```
historica-v0
change qpvuntsmwlrkzxonmvtplsyq
author Adam Harris <adam@example.com>
when 2025-08-19T00:47:11-06:00
```

Version 0 means this document's header set, `k`–`z` change IDs, lowercase hex
digests, and SHA-256.

**The preamble is not a header.** It carries no value, and its digit puts it
outside the key grammar, which decision 0002 restricts to lowercase letters and
hyphens — so no parser can mistake it for a `key value` line, and no reader can
mistake it for a fact about the work. That is the point of spelling it this
way. The version describes how to read the file; every line beneath it
describes what somebody did. HTTP puts its version on the request line rather
than in a header for the same reason, and `<?xml version="1.0"?>` is a
declaration rather than an attribute for that reason too.

The cost is honest: the file now has two grammars where it had one, and a
parser must read line 1 explicitly before it can treat anything as a header. It
is one special case, checked once, at a fixed position — and a parser that
instead split the preamble on its first space would produce "empty value on
line 1", which is a confusing way to say "this is not a revision".

0002 declared the digest algorithm once per repository and recorded the cost as
an open question: a `.rev` file attached to an email is self-describing only if
the reader guesses. That cost is larger than a line of noise, because the
central promise of the format is that a person can verify a revision with tools
they already have. A person who cannot tell *which* digest to compute cannot
take that promise up. `historica-v0` is the instruction for doing so, in the
file, where the file is.

Three further things fall out of it:

- **The version is a magic number.** A `.rev` file is identifiable by content,
  so decision 0003's load-bearing extension becomes a claim the file's first
  line either supports or contradicts.
- **A future algorithm change is unambiguous per file**, rather than ambiguous
  for every revision written before the repository header changed.
- **The repository header loses a line.** Decision 0003's store root file is
  now just `historica-v0`; `digest sha256` was the version restated.

The key order is unchanged by this — `change`, `parent`, `supersedes`,
`author`, `when`, `revised-by`, `revised`, then `x-` headers sorted by key —
because the preamble is not in it.

An unknown version is a hard error, not a best effort. It is the one error a
reader can raise that is certainly right.

## A reader's vocabulary only grows

Immutability makes format evolution asymmetric here in a way it is not in
ordinary formats.

A revision written in 2025 is named by the digest of its bytes. If a 2035
parser refuses those bytes, that revision's identity stops being verifiable —
its digest still resolves references, but nothing can confirm the file behind
the digest is a revision at all. History would rot by deprecation.

So: **a version number constrains writers, never readers.** Version 1 may
require a header version 0 did not have, may retire a spelling, may change the
digest algorithm. A version 1 reader must still parse version 0 files exactly
as version 0 did. The accepted set is append-only, forever, and the cost of
adding a spelling is that it can never be removed.

This is the discipline that makes the strictness above affordable. A strict
parser that could also shrink would be a parser that breaks history; a strict
parser that only grows is one that refuses to guess.

## Advisory headers stay `x-`

> Decision 0065 re-spelled the mark as `<tool>.<fact>`, on a complaint this
> section does not answer: `x-` cannot be read, only looked up. What follows is
> the argument for having a mark at all, and for the tier it divides, both of
> which 0065 keeps.

0002's fourth open question asked whether `x-` is the right escape hatch or an
invitation to a second format nothing validates.

The known objection is RFC 6648, which deprecated the `X-` convention because
experimental names become load-bearing and then cannot be migrated: the
prefix is permanent or the fact has two names. That objection assumes a format
can retire a spelling. Under the growth rule above, this one cannot — of
anything, `x-` or not. The prefix therefore costs nothing that immutability was
not already charging.

`x-` is kept, with the rules the objection implies:

- **Advisory means ignorable, not droppable.** Nothing is re-encoded, so an
  unknown `x-` header survives every operation that copies the file. A reader
  that does not understand one renders without it and is not wrong to.
- **Graduation is a new spelling, and the old one keeps parsing.** When an
  advisory fact becomes standard it gets a real key; writers stop emitting the
  `x-` form and readers accept it for as long as the format exists.
- **Collision is the real risk**, not permanence. Two tools that both mean
  something by `x-review` produce files that parse and mislead. The
  recommended spelling is `x-<tool>-<fact>`, as in `x-diaryx-review-url`. This
  is convention, not validation: the parser checks the prefix, the key's
  shape, and the general value rules, and nothing else.

An unknown header *without* the prefix remains a hard error, for 0002's
reason — a reader that ignores `signed-by` renders a signed revision as
unsigned and is confidently wrong.

## Rejected alternatives

**Labelling every reference with its algorithm** (`sha256:1a4f…`). Rejected in
0002 for reference length, and the version header now covers what it was for:
the file says how to hash the file, and references inside a file inherit it.

**A version header on the repository only.** The status quo. It leaves every
revision in transit ambiguous, and makes "verify with `shasum`" a promise that
requires a second file to redeem.

**Lenient parsing with a `normalize` command.** Attractive because hand-editing
gets easier, but it makes normalising a semantic operation: the same work
acquires a second digest, and a person who tidies a file is shown a divergence.
Friendliness belongs in the error message, which can state the exact fix.

**Retiring spellings at a version bump.** Would let the format shed mistakes,
at the cost of old revisions becoming unparseable and therefore unverifiable.
An immutable, content-addressed history cannot afford it.

## Consequences

- Every corpus file gains the preamble, so every corpus digest changes, and
  every `parent` and `supersedes` line that names one changes with it. The
  invalid examples gain it too, so that each still fails for the reason it was
  written to pin down.
- New invalid examples: out-of-order keys, unsorted parents, a missing
  preamble, an unknown version, and a separator with nothing after it.
- Decision 0003's repository header file drops `digest sha256`, leaving the
  same single line a revision opens with.
- `check` and `normalize` are now specified enough to build: both are the same
  parse, differing in whether the correction is printed or applied to produce a
  new revision.

## Resolved questions

1. **Whether `normalize` should exist at all**, given that its output is a
   different revision. It may be honest only as a pre-commit step on a file
   that has never been recorded, and dishonest on one that has. Answered by
   [0027](0027-closing-the-small-questions.md): there is no `normalize` command
   for a recorded revision. A formatter may produce candidate bytes before
   recording, but replacing identified history is a new revision.

2. **What version 0 promises about itself.** Answered by
   [0017](0017-content-that-arrives-whole.md): version 0 was not the format's
   final commitment, version 1 was introduced before deployment, and a version
   1 reader nevertheless reads version 0 documents forever.
