# 0007 — Content: what a revision changes, and how two of them merge

Decision 0002 left content out deliberately — "there is no `tree` header yet,
because the tree model is a later decision" — and decision 0006 named this
document as the one that takes it up.

This document decides less than the tree and more than it. It introduces no
paths and no directories. It decides what a change *to one file* is, and what
happens when two people change one file at once. The tree becomes 0008, and
the order is not arbitrary: whether a revision names a snapshot or a stream of
operations decides what a tree entry can point at, so a tree written first
would be written against an unknown.

## The decision

A revision does not record what a file *is*. It records what the revision
*did* to it: a list of operations against the state at that revision's
parents, in one readable document per file.

Materialising a file at any revision means replaying those operations from the
root. Merging concurrent branches means replaying them through the Eg-walker
algorithm (Gentle and Kleppmann, EuroSys 2025), whose internal state is built
during the replay and discarded when it ends.

Nothing else is written down. No per-character identifiers, no tombstones, no
version vectors, no operation IDs, and no metadata that survives a merge.

## The causal graph is already the event graph

Eg-walker's persistent input is an *event graph*: operations, each naming the
operations it happened after. Historica has stored that graph since decision
0001. `parent` lines are the edges, revisions are the nodes, and
`History::merge` is already the union that a replicated event graph requires.

The part that makes it fit rather than merely resemble is identity. Every
operation in the algorithm needs a unique name and a total order against its
concurrent peers. Both are *derivable* here and therefore need not be written:

> Operation *i* of revision *R* is named `(R, i)`.

A revision's digest already exists, is already unique, and — because decision
0002 hashes the file's bytes — cannot be claimed falsely. Numbering operations
by their order in the document costs nothing, because the document had to have
an order anyway.

This is the condition `docs/loro.md` set and could not get from Loro. There,
the operation identities lived in a binary log with no stable readable form,
so a readable Historica store could not recreate the history it claimed to be
the authority for. Here the identities are a function of bytes a person can
read, which makes the materialised document a cache by construction rather
than by discipline.

One consequence binds 0008 rather than this document. If a revision changes
several files, `i` must be unique across all of them, so **the tree must give
a revision's files a total order**. Any deterministic order will do; that
there is one is now a requirement rather than a nicety.

The same rule explains why operation names derive from the *revision*, not
from the operation document. Two revisions that make byte-identical edits
share one document under decision 0003's dedup rule, and two genuinely
concurrent events must never share a name.

## Operations are read from a diff, not written as indices

Eg-walker consumes index-based operations — insert at 137, delete 3 from 41 —
expressed against the document state at the operation's parents. That is the
smallest possible encoding and the least readable one: a person cannot say
what a revision did without materialising its parent and counting.

So the stored form is a diff, and the index form is derived when the file is
read. The algorithm does not care where its operations come from, only that
each carries a position, a content, and a causal parent set.

The context this adds is redundant, and that is the point. A deleted line is
recoverable from the parent, so writing it down buys nothing the machine needs
— and buys a person a document that can be read alone, plus a check the
machine can run: an operation whose recorded text disagrees with the parent's
actual text is corruption caught at the moment of replay rather than absorbed
into a merge.

## The operation document

One file per changed file per revision, stored under `history/operations/`
with the extension `.ops`, named by digest under decision 0003's rules and
identified by the SHA-256 of its bytes like everything else.

```
historica-v0

delete 3 1
-Nothing here chooses a document syntax yet.
insert 4
+Model causality before content: immutable revisions, explicit parents, and a
+history that merges by union.
```

The preamble and the blank line are decision 0004's, for its reasons: the
file says how to hash itself, and it can be identified by content rather than
by the extension it happens to carry. Everything else a revision document
holds — change, parents, authorship — is absent, because the revision that
names this document already states it. There is no second causal graph to
disagree with the first.

| Line | Meaning |
| --- | --- |
| `delete P N` | Remove `N` items beginning at position `P` in the parent state. |
| `-…` | One removed item, in order; exactly `N` follow a `delete`. |
| `insert P` | Insert the following items before position `P` in the parent state. |
| `+…` | One inserted item, in order; at least one follows an `insert`. |
| `\ no newline` | The preceding item is the file's last and carries no terminator. |

The reading rules, which decision 0004's parser contract governs unchanged:

- **The blank line is mandatory**, though no header precedes it. An operation
  document is preamble, blank line, operations, with no second spelling — the
  ambiguity 0004 closed for an empty message, where headers-then-EOF and
  headers-then-separator-then-nothing meant one thing twice. The separator does
  different work here than in a revision, and is required for a weaker reason:
  there it divides what is parsed strictly from what is kept verbatim, and
  below it here everything is still read. What it buys is that both documents
  in the format open the same way, so a person learns one shape and a parser
  reads a preamble the same way in both.
- Positions are zero-based indices **into the parent state**, not into the
  document as it is being built. Stating them against a fixed state is what lets
  operations be sorted, read out of order, and checked by eye; the replayer
  converts them to the sequential form the algorithm wants by carrying a running
  offset, which is arithmetic rather than interpretation.
- Operations appear in ascending position order and may not overlap. That is a
  total order, so it is a canonical order, so 0004's "exactly one byte sequence
  per set of facts" survives contact with content.
- At one position, `delete` precedes `insert`. A replacement is then spelled the
  way every diff spells it, minus lines above plus lines.
- A content line is one prefix byte followed by the item's bytes. Exactly one
  byte is stripped; nothing else is trimmed, unescaped, or normalised, so
  trailing spaces and tabs survive as they do in a revision's message.
- An item's bytes may contain a carriage return. Decision 0002 bans CR from the
  *format's own* lines so that an editor cannot silently change a revision's
  identity; a file being versioned is text under version control, and a CRLF
  document is a thing people have.
- A revision that changes nothing about a file names no operation document. An
  absent fact is an absent line, and an empty operation list is a fact spelled
  twice.

A file's first version is `insert 0` with every line. There is no add
operation, no delete-file operation, and no rename: existence is the tree's
business and therefore 0008's.

## Items are lines

Eg-walker is a list algorithm and is indifferent to what a list holds. This
decision makes the item a line, terminator included.

Lines are what the readable artifact wants. A diff is line-shaped, every tool
a person already has is line-shaped, and an operation document at line
granularity is proportional to what changed rather than to what exists.
Characters would merge two people editing one sentence, at the cost of an
operation document that is a column of single characters and a format nobody
would call readable.

The cost is real and worth stating plainly: **two people who edit the same
line concurrently do not get one merged line.** They get both lines, adjacent,
in digest order. For prose and for a journal that is the correct outcome — a
sentence merged character-wise from two intentions is usually nonsense wearing
the shape of sense — but it is a downgrade from what a character-level
algorithm would produce, and anyone comparing Historica to a live
collaborative editor will notice it.

That comparison is where `docs/loro.md`'s second condition lives. A document
edited by several people *at once* is a leaf-document problem with a finer
operation vocabulary, and this decision does not close it. It fixes the
granularity of version control, not of typing.

## Merging is replay, and the replay's state is transient

To materialise the state at a set of heads: find where the branches diverged,
take the state there, and replay every operation after it in topological
order. Eg-walker's contribution is what happens in that replay — concurrent
operations are transformed against each other through an internal list CRDT
that exists only for the duration of the walk.

Three properties matter more than the mechanism:

- **The linear case costs nothing.** When no two operations in the region are
  concurrent — one person, one device, or any history that has already been
  merged — the internal structure is never built and replay is application.
  For the overwhelmingly common history this algorithm is free.
- **The state is discarded.** After the walk there is a document and nothing
  else. This is the property that lets `cache/` be genuinely disposable rather
  than nominally so.
- **Ordering is by digest.** Two concurrent insertions at one position are
  ordered by their revision's digest, then by operation index. No timestamp
  participates, because decision 0002 says none ever does, and no change ID
  participates, because decision 0001 says a change ID is an unverifiable claim
  and merge order should not be something a careless writer can bias.

  The cost is that merge order is unpredictable to a person until they compute
  it. It is deterministic, which is the property convergence needs; it is not
  intuitive, which is the property nobody was offered.

The insertion-ordering rule inside the replay is a parameter of the algorithm.
The reference implementation uses a Yjs-style rule; this decision adopts
Fugue's (Weidner and Kleppmann), which carries the strongest published
guarantee against interleaving — the failure where two concurrently written
paragraphs merge into alternating lines of each. Readability is the project's
rule, and interleaved text is the least readable thing a merge can produce.
Conformance against the reference implementation is owed before this is called
done.

Unlike the parser contract of 0004, **merge semantics cannot be append-only**.
A reader's vocabulary may only grow; a merge rule that changed would change
what old histories mean. Historica is unusually well placed here, and by
accident: a merge result is *recorded* as a revision with its own digest, not
recomputed on demand, so changing the rule changes future merges and rewrites
nothing. A live CRDT, whose state is always the current output of the current
algorithm, cannot say that.

## What replay needs, and what that costs supersession

Replay needs every operation from the divergence point forward, and a state at
that point that is either cached or itself replayed from the root. The store
must therefore hold an unbroken chain of operation documents behind anything
it intends to materialise.

Missing ancestors are not corruption. A head whose ancestry is incomplete
simply has no content yet, exactly as `History::missing_parents` calls an
undelivered parent ordinary. Materialisation is a partial function, and 0006's
`check` was already right to make an absent `parent` a note rather than an
error.

Supersession is where this bites, and it amends a premise rather than only
extending one. Decision 0005 argued from the fact that a superseded revision
may legitimately be absent — that is why the successor carries the evidence.
Under this decision that stays true, with a condition:

> A superseded revision may be dropped only if it is an ancestor of nothing
> retained.

Amend a revision nobody has pulled and the old one is genuinely disposable.
Amend one that someone has already merged and its operations are load-bearing
for content that exists: the merge result was derived from them, and without
them that result can be read but not re-derived or built on.

Git has the same hazard and answers it with a social rule about rebasing
published history. Historica can do better than a social rule, because
supersession is an explicit edge on disk rather than an inference from reflogs
— a tool can *know* which drops are safe. Whether it should refuse the unsafe
ones or merely say so is a tool decision, not a format one, and is left open
below.

## Contested regions are reported, not resolved

A CRDT always produces an answer. That is its virtue for a journal syncing
between two of one person's devices, and its hazard everywhere a wrong answer
looks like a right one.

Replay therefore returns two things: the merged content, and the spans where
concurrent operations touched one region. The second is not conflict markers
and is not written to disk — it is what lets a tool decline to record an
automatic merge and show a person the two versions instead. Decision 0001
already provides the vocabulary for declining: divergence is a legitimate
state, not a failure.

The distinction that keeps this honest is that the *algorithm* never fails and
the *tool* may. A merge Historica records is a revision like any other, with
an author who chose to record it.

## What this trades away

**A person cannot merge by hand.** They can read an operation document, apply
a chain of them along a linear history with a text editor, and verify every
digest with `shasum` — but the merge of two concurrent branches requires the
algorithm. This is the largest concession the project has made to date. What
makes it survivable is that a merge *result* is recorded as a revision, so
what a person recovers is a file rather than a computation; what makes it
honest is saying that the recovery story for a concurrent history is weaker
than for a linear one.

**The store is not greppable.** `revisions/` and `operations/` describe edits,
not documents, so searching them finds the moment a sentence was written and
not the sentences that currently exist. This is what `cache/` is for, and the
README sanctioned it in advance: snapshots may exist as disposable caches, and
deleting every cache must lose neither information nor meaning. Replay from
the root rebuilds them exactly, so that condition holds.

**History cannot be shallow.** A snapshot store can discard old versions and
still show the current one. An operation store cannot, because the current one
is the sum of what it discarded. A re-rooting revision that states content
outright would fix it and is not designed here.

## Rejected alternatives

**A snapshot per revision, merged three ways.** Git's model, and the most
readable one available: recovery is copying a file out. It fails the word
"convergent" in the project's first sentence. A three-way merge is a heuristic
whose result depends on the diff and merge implementations running it, so two
replicas merging one pair of heads can produce different bytes — and decision
0002 spent a section establishing that two replicas performing one
deterministic operation must write one file. Under three-way merge they write
two, and the person is shown a divergence that nothing in their history
created.

**Snapshots as the authority, operations as a cache.** The appealing
inversion, and it does not work in that direction. Operations cannot be
derived from snapshots without choosing a diff algorithm, and that choice is
not a rendering detail: the decomposition it produces is what all later merges
are computed against, so it must be recorded once by the person who made the
edit rather than recomputed by whoever reads it. Operations are authoritative
because they are the part that cannot be regenerated. Snapshots are cache
because they can.

**A CRDT with its metadata on disk** — Automerge, Yjs, Loro. Rejected in
`docs/loro.md` for the recovery argument, and rejected again here for a
readability one that is specific to a readable format: every deleted character
and its identifier would live in the file forever, so the document a person
opens grows without bound with work that was undone. Eg-walker's whole result
is that this is unnecessary.

**Patch theory** — Darcs, and Pijul. The closest relative, and the one this
document is least comfortable dismissing: patches commute, conflicts are
first-class rather than a report, and the stored artifact is a readable patch,
which is nearly what is chosen above. Two reasons to prefer replay. Historica
already has a causal DAG and a merge-by-union history, so a commutation theory
would be a second account of the same relationships; and Pijul's answer to
Darcs' exponential merges is a sophisticated on-disk graph whose vertices and
edges are precisely the metadata this decision exists to avoid writing. Pijul
deserves the treatment `docs/loro.md` gave Loro — an evaluation with the
conditions that would reverse it — and does not have it yet.

**Operational transformation.** Merging long-lived branches is where OT is
weakest and where a version control system lives.

## Consequences

- `src/format/` gains a second document type and `src/` gains a replayer.
  Decision 0005 owed the first; this owes the second.
- `history/operations/` joins the store layout of 0003 and 0006, and `.ops`
  is load-bearing there in the way `.rev` is under `revisions/`.
- `cache/` acquires its first inhabitant: materialised file states keyed by the
  head set they were replayed to.
- `check` gains one error — an operation document whose recorded `-` lines
  disagree with the parent state — and it is an error rather than a note,
  because it is the store contradicting itself.
- The corpus gains operation documents, and gains its first example where the
  interesting property is not what the parser accepts but what the replay
  produces: two concurrent revisions of one file, and the merged bytes.
- The acceptance test is a property test, not an example: random operations from
  several replicas, merged in random orders, must produce byte-identical
  results, and replaying one graph in different topological orders must too.
  The paper's editing traces are usable as a corpus, and `diamond-types` is ISC,
  which is compatible with this project's licence for anything lifted from it.

## Deferred

**The tree.** Paths, directories, existence, and rename become 0008, which
this document constrains in one way: a revision's files need a total order,
because operation identity is derived from it.

**Spelling paths that are not valid UTF-8**, open since 0002 and re-deferred
by 0006, stays with the tree, where the first path will be.

**Binary and non-UTF-8 content.** A list of lines is the wrong model for an
image. The likely answer is that such a file names its bytes and never merges,
which is a tree question about what an entry may point at.

## Resolved questions

1. **Whether the tool should refuse unsafe drops or only report them.** The
   Answer is refusal: [0013](0013-abandoning-and-pruning.md) permits `prune` to
   remove a superseded revision only when no retained revision names it as a
   parent.
5. **Whether Fugue's ordering is the right permanent choice**, and what a
   conformance suite against the reference implementation has to cover before
   that is more than a reading of two papers. Answered by the independent
   reference CRDT in `tests/conformance.rs`: every history both implementations
   can express must produce the same bytes, and concurrent paragraphs must not
   interleave. Fugue remains the choice unless that suite finds a counterexample.

   The suite has one blind spot worth recording, because it bit. Both
   implementations first transcribed Fugue's anchoring rule with the author's
   next *visible* element as the right origin, where the rule wants the next
   element in the tree traversal, tombstones included. The two agreed with
   each other and were both wrong: whenever an insertion's left neighbour held
   a tombstoned right child, two causally ordered elements became siblings and
   the digest tie-break — correct only between concurrent elements — read a
   plain linear chain out in digest order, against what `crate::replay` said
   the same history meant. A shared specification line is exactly what a
   conformance suite cannot check; what caught it was holding the walk to the
   replayer on random linear chains, and that differential test is now pinned
   in `src/merge.rs` alongside the chain that reproduced the defect.

   The suite's simulated edits are items rather than text, so the content it
   searches over includes empty lines, lines carrying a carriage return, and
   files that end without a terminator. That last shape is what reaches
   resolved question 3 below: a merge of two well-formed files can hold an
   item that is neither terminated nor last, which no single history can state
   and `State::applied` refuses a document for producing. Both architectures
   agree on those files, the merge reports the region as contested, and a run
   that reaches neither shape fails the suite rather than passing on a
   narrower search.

## Deferred

2. **Whether a re-rooting revision should exist**, stating content outright so
   that history can be truncated. It would restore shallow clones and would put
   a second, snapshot-shaped thing in a format that just argued for one shape.
   Decision [0028](0028-accepting-by-path.md) keeps it deferred until Historica
   has a transport boundary and a concrete shallow-history operation.

## Resolved questions

3. **How a file with no final newline merges.** `\ no newline` is a property of
   the last item, so two branches that concurrently append to a file whose last
   line lacked a terminator are asserting two different things about one item.
   Answered by [0027](0027-closing-the-small-questions.md): the terminator is
   part of that item, so incompatible concurrent assertions are a contested
   region and neither branch wins.
4. **Whether contested regions should ever be recorded.** They are ephemeral
   and remain so by [0027](0027-closing-the-small-questions.md). Canonical
   history records the resolution a person chose, not a diagnostic derived by
   one merge implementation.
