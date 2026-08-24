# 0032 — A merge states its resolution

This is the second half of `historica-v3`, and the deeper one. 0031 gave the
hand replayer a checkpoint; this gives them the one thing they could not do
at all, and removes the one place where "readable without the tool" was
quietly untrue.

The untruth, stated plainly. A recorded merge's content is a delta against
*the algorithmic merge result*: `record --merge` diffs the folder against
what the event-graph walk produces, so the operations it writes are
positioned into a state only that algorithm can supply. Every revision
downstream of a merge therefore materialises only through a correct Fugue
implementation — forever, on every reader, in every language. 0007 said
"nothing a merge needs is ever written down" and meant it as a virtue; for
an unrecorded, in-flight merge it still is one. For a *recorded* merge it
means the merge algorithm is part of the format's meaning, which is exactly
the kind of dependency the readable files exist to not have. A tool-less
reader hits it as a cliff: no amount of patience with `shasum` and
arithmetic replays a file past a merge. A tool-less writer hits it as a
wall: there is no legal way to write "I read both sides, and here is the
result", because the only spelling of a resolution is a delta from a state
they cannot compute.

## The decision

- **A merge revision states a resolution for every file its parents
  disagree about.** Where the parents' states for a file are identical,
  nothing is stated and the content is that state — the rule a reader can
  check without any algorithm. Where they differ, the revision's `edit`
  line names a **resolution document**.
- **A resolution is a sequence of references and insertions, in file
  order.** `keep <digest> <first> <count>` takes a run of items from an
  existing document — the items 0007 already names `(R, i)`, counted in
  document order — and a bare `insert` with `+` lines mints new ones. The
  assembled sequence *is* the file at the merge. No positions, no parent
  state, no algorithm: concatenation.
- **A resolution never restates content that has an identity.** This is the
  load-bearing choice, argued below: restated bytes would be new items, and
  the first merge reaching across this one would meet every line twice —
  once under its old name from the other branch, once under its new name
  here — and keep both. References preserve identity, so merging across a
  recorded merge stays ordinary.
- **The resolution states its result**, as every v3 document does, so a
  hand-assembled resolution is verified by `shasum` like everything else.
  0031 landed first because this is what it is for.
- **The event-graph merge demotes to proposing.** `merge` still computes
  the Fugue result — it is how the tool previews an uncommitted merge and
  drafts the resolution a person then edits and records. What it stops
  being is load-bearing for reading: recorded history replays by
  arithmetic and reference-following alone, and an implementation with no
  merge algorithm at all can materialise every recorded revision.
- **0012 stands untouched.** Nothing conflicted is recorded; two heads are
  still the conflict; marker lines are still refused at record time. What
  is recorded is the *resolution*, which was always going to be recorded —
  the change is that it is now recorded whole instead of as a delta from a
  computation.

## Why references, and not the two easier spellings

**Restating content — a payload, or a full re-insert.** The obvious
spelling, and wrong in a way that only shows up one merge later. A payload
of the resolved file mints a new identity for every line. Take branches A
and B merged in R, and a third branch C, taken from B before the merge,
edited concurrently. Merging C with a descendant of R walks an event graph
holding B's lines twice: as B's items, surviving on C's side with C's
edits, and as R's restated copies on the other. Two items are two items —
the merge keeps both, and every line B contributed appears twice in the
result. The whole reason 0008 gave files identities — so that no heuristic
recovers a connection later — applies to lines with more force, because
there are thousands of them and they are one edit apart from not matching.

**A delta against one named parent.** Position the merge's operations into
parent A's state — arithmetic again, no algorithm. But B's contributions
then arrive as the delta's insertions, which are new items again, and the
duplication returns wearing different clothes. Any spelling in which the
other side's lines are written down as fresh text has this defect. The only
spelling that does not is the one where surviving lines are *named* rather
than restated — and 0007 already gave every line a name.

**What references cost** is that a resolution is not self-contained prose:
reading it means opening the documents it names. The store's arrangement
already answers this — the named documents are filed, readably, under the
revisions that wrote them — and the `keep` runs are short, because runs are
exactly what the merge rule preserves; a resolved file is typically a
handful of ranges and a few inserted lines. And a reference has one
property restated bytes could never have: **forgetting needs no new rule
here.** A `keep` quotes nothing, so there is nothing for a redaction to
chase — a forgotten item referenced by a resolution simply shows its marker
wherever the resolution places it, and 0014's union rule reaches through
untouched. A resolution that restated content would have been a new quoting
surface for every redaction to hunt, forever.

## What the reader does now

Content at any revision becomes one recursive rule with no algorithm in it:

- a file created here is its payload;
- a file edited on one line of history is the parent's state with the
  document's operations applied — 0007's arithmetic;
- a file at a merge whose parents agree is that agreed state;
- a file at a merge whose parents differ is its resolution: fetch each
  `keep`'s items from the document it names, splice the inserts,
  concatenate, and `shasum` the result against the `result` line.

Each step is something a person can do by hand and check by hand, which
closes the last gap in the claim 0030's review made half-true. It is also a
floor under every implementation: replay across an arbitrarily merge-heavy
history requires resolving references, not running a CRDT. And it is a
performance floor the perf work has been fighting toward from the other
side — materialisation can stop at the nearest resolution instead of
walking to the root, because a resolution *is* the file, stated.

## What the walk does with a resolution

The event-graph merge still exists, for previewing uncommitted concurrency
and for merging branches that reach across a recorded merge. When the walk
crosses a resolution it takes it as what it is — the recorded truth of that
file at that revision:

- an item the resolution does not keep is dead there, exactly as a delete;
- items the resolution inserts are its own, named `(R, i)` where `R` is the
  resolution document's digest;
- items it keeps survive **under their own names**, which is what lets a
  concurrent branch's edits to those same items merge normally instead of
  colliding with copies.

The resolution's sequence is authoritative for the state at its own
revision; concurrent work anchors into it by the item identities it
preserved. Holding the walk to that — and holding the conformance suite's
reference implementation to the same answer — is the implementation
obligation this decision creates, and the property tests over walk orders
extend to graphs containing resolutions.

## The tool-less merge

Worth spelling out, because it converts the impossible to the ordinary. A
person with two heads and no tool reads both sides, decides what the file
should say, and writes a resolution: `keep` lines counted out of documents
they can open and read, `+` lines for what they wrote themselves, a
`result` from `shasum` on the file they assembled, and a revision document
with two `parent` lines naming it. Every ingredient is an editor and a
checksum. Before this decision the same person could not legally record a
merge at all — not laboriously, not carefully, at all.

## Rejected alternatives

**Restating content**, in either spelling. Above: duplication at the next
merge across, and a new quoting surface for forgetting.

**Keeping the status quo and documenting the algorithm harder.** A
specification of Fugue-over-event-graphs is a fine thing to publish and no
answer here: the mission's reader has `shasum` and patience, not a CRDT
implementation, and 0007's own conformance suite exists because two careful
implementations of this class of algorithm can disagree in ways that take
randomised search to find.

**Resolutions for every file, agreeing parents included.** Uniformity at
the price of restating the ordinary case; where parents agree there is
nothing to resolve, and a mandatory no-op document is the snapshot habit
0007 refused, sneaking back in a new uniform.

**A resolution as tree-level fact rather than content.** The tree already
has its merge rules (0008) and they are cheap and total; it is content
whose merge was expensive to interpret. The tree facts stay as they are.

**Deferring until someone asks.** The window does not defer with it: this
is a breaking change, 0.2.0 is unpublished, and 0021 named the moment such
decisions become impossible. It is also the change 0031 exists to serve.

## Consequences

- `format` gains the resolution document: same preamble, `result` header,
  and a body of `keep <digest> <first> <count>` stanzas and bare `insert`
  stanzas in file order — parsed as strictly as everything else, refused
  in a document that also states positions, and claiming `historica-v3`.
- A merge revision must name a resolution for every file whose parents'
  states differ, and may not name one anywhere else; `check` holds both
  directions, and holds every reference to a document and range that
  exist.
- `record --merge` writes resolutions: the folder's final state, aligned
  against the surviving items of the proposed merge, emitted as maximal
  `keep` runs and fresh inserts. The `--merge` refusals — standing
  markers, unsettled paths, unaccepted attachments — are unchanged.
- `Store::content` and replay follow references instead of running the
  walk wherever a resolution is recorded; revisions recorded before v3
  read exactly as they did, walk included, forever.
- The conformance suite and the walk-order property tests extend to
  histories containing resolutions, held to the reference implementation
  as ever.
- The corpus gains a merged history whose merge is a resolution — the
  first corpus a person can replay through a merge by hand — and the
  invalid spellings that pin the grammar.
- comparison.md's "Merge is deterministic across implementations" row gets
  a stronger footing: recorded merges are deterministic by *reference*,
  not by algorithm agreement.

## Deferred

**Resolutions outside merges.** A single-parent revision stating its file
by reference — a "rebase by hand", a squash — has uses, and the grammar
would carry it, but every use is a history-rewriting feature this project
has not decided, so the parser refuses it until one is.

**Binary files at a merge.** Unchanged by this decision: 0008 makes two
concurrent `bytes` a divergence, 0028 makes accepting one explicit, and a
payload needs no resolution grammar because a payload has no items.

**The walk's long-term role.** If resolutions prove universal in practice,
the walk shrinks to a proposal engine and the conformance suite shrinks
with it. Nothing forces that question yet, and the walk earns its keep
previewing every merge a person is still deciding about.

## Since

This decision gave `operations/` a second grammar under the same suffix, and
that is a change to what every consumer of an `edit` digest is asking. Three
of them were still asking the older, narrower question, and each failed in the
same shape: a document the store was holding perfectly well came back as
`None`, and the branch that handles `None` said something untrue about it.

**`receive` dropped resolutions on the floor.** Decision
[0029](0029-receiving-another-store.md) plans a transfer by asking each store
what it holds, and it asked with `Store::operations`, which answers about the
first grammar only. A merge's resolution was therefore planned as neither a
document nor a payload, and never copied. The receiving store reported
success, reported nothing left to receive on the next run, and could not read
the head it had just been given — `check --complete` caught it and nothing in
the transfer path did. `export` had the same question to answer and answered
it correctly, because it was written after this decision; `receive` was
written before it and was never swept.

**`show` accused the store of missing a file that was sitting there.** The
command exists to print what is stored, byte for byte, and a merge is where a
person most wants that. It asked `Store::operation` and reported the resolution
as undelivered.

**`forget` cannot reach a resolution, and now says so.** Decision
[0014](0014-forgetting.md)'s stand-in is written in the operation grammar: a
`forgets` line, and a marker standing where each destroyed item's text stood.
A resolution has neither. Lines a merge only *kept* are still forgotten where
they were written — the `keep` meets the stand-in, and the shape 0014 preserves
is exactly what makes that work — but text a person typed while resolving
exists only as `insert` items in the resolution, and there is no way yet to say
that one of those is destroyed. That is a real hole in 0014's promise rather
than a missing branch, and closing it is a format change: see the deferral
added to 0014. What is fixed here is the refusal, which claimed the document
had not arrived.

The shared cause is that a caller could ask half the question without saying
so. `Store::body` and `Store::bodies` are the whole question — one digest and
the directory — and `Store::operation`, `Store::resolution`,
`Store::operations` and `Store::resolutions` are now for the caller that has
already established which grammar it is holding.
