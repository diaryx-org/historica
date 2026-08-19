# 0001 — Two identities: revisions and changes

Historica gives every node in history two names.

- A **revision ID** is derived from the node's canonical readable bytes. It
  answers *are these the same bytes?*
- A **change ID** is assigned once when work begins and copied forward through
  every rewrite. It answers *are these the same piece of work?*

Git has only the first, which is why every rewriting operation in Git has to
imitate the second out of reflogs, patch IDs, and force-push protocol. A tool
that wants amend, rebase, and undo to be ordinary rather than dangerous needs
the second name to exist on disk.

## Why the core needed to decide this first

The first core modelled one opaque `ChangeId` built from an arbitrary string,
and carried an `IdCollision` error for "two different changes claim one ID".
That error is evidence of an unstated decision: it can only occur if IDs are
assigned rather than derived, because a derived ID cannot disagree with its own
content unless the hash is broken.

Every deferred decision — document syntax, content addressing, tree model,
patch model — is downstream of this one. Canonical bytes cannot be specified
before we know whether their hash is an identity, and a readable format cannot
spell an ID it has not defined.

## Revision IDs

A revision is the immutable node. Its ID is a digest of its canonical readable
bytes, and because those bytes name its parents by *their* revision IDs, the
digest commits to the whole ancestry. History is a Merkle DAG: verifying one
head verifies everything behind it.

This is what makes the project's central rule checkable rather than
aspirational. "The readable files are the authority" means a person can
recompute every identity from the text on disk, and any tampering shows up as a
revision whose contents disagree with its name.

Revision IDs are the unit of transport, deduplication, verification, and
signature. They are not stable across rewriting and are not what a person
types.

## Change IDs

A change ID names the work independently of its current contents. Amending a
message, fixing a typo, or rebasing produces a *new revision of the same
change*.

The ID is 96 assigned random bits, spelled as 24 characters.

### Why it is assigned rather than derived

Two derivations are tempting, and both fail.

**From the first revision's digest.** Circular: the ID is part of the document
being hashed, so breaking the cycle needs an elision rule that every
implementation must reproduce exactly — which is the canonical re-serialisation
decision 0002 exists to avoid.

**From the parents and the content**, so that two identical pieces of work
collide and nothing else can. This is `git patch-id`, and it destroys the
property the change ID exists for: amending alters the content and rebasing
alters the parents, so a derived ID changes under precisely the two operations
it must survive. What it produces is a second revision ID, which collapses the
two identities back into the single one Git has.

It would also not be safe to shorten, which is usually the reason it is
proposed. Truncating a hash to *n* bits has the same birthday behaviour as *n*
random bits; "cannot collide unless the content is identical" holds only at
full width. Derivation changes where the bits come from, never how many are
needed.

And its collisions would not all be benign. Identical content is not identical
work: the same typo fixed on two replicas, a formatter run twice, or a change
reverted and later re-made would share one ID and present as divergence of
something that was never one change. A change ID must also exist *before* its
content is final, since work is named while it is still being done, and a
derived ID cannot.

The circularity is a hint rather than an obstacle: a change ID deliberately has
no verifiable relationship to content, because its whole purpose is to survive
content changing. Convergence on identical content is real and valuable, but it
belongs one layer down — two replicas that deterministically produce the same
revision produce the same bytes, hence the same revision ID, and union merges
them for free.

### Why 96 bits

Assignment is uncoordinated, so only accidental collision matters — decision
0001's later warning that a change ID must never be a security boundary means
no adversarial margin is being bought. At 96 bits a repository of ten million
changes collides with probability around one in 10^15, which stays negligible
through any plausible bulk import.

The counterweight is that this name sits on the second line of every readable
file, and 32 characters of `k`–`z` is a wall of noise in a format whose whole
argument is that a person will read it. 96 bits costs eight of those characters
and no safety anyone will encounter. It does not change what a person types:
the unique prefix is governed by how many changes exist, not by the full
length, so it is around eight characters either way.

Two properties are deliberate, both borrowed from Jujutsu:

1. **A disjoint alphabet.** Change IDs are spelled in reversed hexadecimal, the
   letters `k` through `z`. No change ID can be mistaken for a digest and no
   digest for a change ID, so one command-line argument position can accept
   either without ambiguity, and a person reading a log never has to ask which
   kind of name they are holding.
2. **Abbreviation to the shortest unique prefix.** The usability payoff is that
   *change ID prefixes stay valid across rewrites*. A person can type `hx`,
   amend that change four times, and `hx` still resolves. Digest prefixes churn
   on every edit, which is why Git users copy hashes instead of remembering
   them.

## Parent edges name revisions; successors name their predecessors

Parent edges must hold revision IDs. If a parent edge named a change ID, the
graph would mutate underneath a node whenever its parent was amended, and no
recursive digest would be possible.

The consequence is the point of the whole arrangement. Amending a change
changes its digest, which changes its children's bytes, which changes their
digests, to the end of every descendant line. Each descendant therefore gets a
new revision — and each keeps its change ID. The person's model of their work,
"my three changes", is undisturbed while every object beneath it is replaced.
Automatic rebase is not a feature built on top of this model; it is what the
model does.

To make the second layer navigable, a revision records the revision IDs it
**supersedes**. That gives a second DAG whose heads are the current revisions
of a change — computed by the same union-merge and head-discovery already in
the core, which is a good sign that the two layers share one shape.

Storing the edge on the successor rather than the predecessor matters for
transport: a superseded revision may legitimately be absent locally, and the
successor still carries the evidence that it was superseded. An absent
predecessor is normal, unlike an absent parent.

Supersession is not restricted to one change ID. A revision may supersede
revisions of *other* changes, which is what squashing is: the absorbed change
has revisions, all superseded, and no current revision of its own.

## Four states, not one error

Separating the layers separates situations the first core had to conflate.

| Situation | Meaning | Response |
| --- | --- | --- |
| One revision ID, disagreeing bytes | Tampering or a broken digest | Hard error |
| One change ID, one revision supersedes the other | An ordinary rewrite | Resolve to the successor |
| One change ID, concurrent revisions | Divergence | A state to show and offer to resolve |
| One change ID, every revision superseded elsewhere | The change was squashed or abandoned | A state to show |

Only the first row is corruption. Divergence is unavoidable in any tool that
allows both rewriting and offline work, and naming it as legitimate state is
the difference between a tool that explains itself and one that refuses to
proceed. The core therefore resolves a change ID to a `ChangeState` rather than
to a revision or an error.

A collision between two independently minted 96-bit change IDs is
astronomically unlikely, and would present as spurious divergence — a state
that is already displayed and resolvable — rather than as data loss. The
failure mode degrades gracefully, which is part of why assigned bits are
preferable to a shorter human-chosen name.

## Consequences

- Two ID spaces must be documented and taught. The disjoint alphabet reduces
  the cost but does not remove it.
- **A change ID cannot be verified.** Any author can write a revision claiming
  any change ID. A change ID must therefore never be a security boundary:
  signatures cover revision IDs, and "is this the change I reviewed?" is
  answered by digest alone.
- Divergence and abandonment become required interface work rather than
  optional polish.
- The mapping from change ID to revisions is recomputable by reading revision
  files alone, because each revision names its own change ID and predecessors.
  Any index over that mapping is a disposable cache, as the central rule
  requires, and the recovery test must delete it and confirm every change ID
  still resolves identically.
- What a bookmark or branch name points at is now a real choice: a change ID
  follows rewrites automatically, a revision ID is exact but needs constant
  updating. Deferred.

## What this defers

- The digest algorithm, and whether a readable revision ID carries an algorithm
  label. Until decision 0002 fixes the canonical document, the core treats a
  revision ID as an opaque 32-byte digest supplied from outside and spells it
  as bare lowercase hex.
- Computing a revision ID. The core cannot hash a revision until canonical
  bytes exist, so it accepts the ID as given and will gain a `verify` operation
  when the format lands. Until then the one-revision-ID-disagreeing-bytes error
  is load-bearing rather than merely defensive.
- Minting a change ID, which needs a cryptographic random source and belongs to
  the layer that creates revisions rather than to the pure core.
- Whether head discovery hides superseded revisions. The core keeps head
  discovery a pure graph question and exposes the superseded set so that
  rendering can decide.
- Cycle rejection. Derived revision IDs make ancestry cycles infeasible to
  construct, but supersession cycles are not yet checked.
