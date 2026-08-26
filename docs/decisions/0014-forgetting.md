# 0014 — Forgetting

Decision 0013 kept two acts apart — abandoning, which is a fact recorded in the
graph, and pruning, which is disk — and then said a third thing outright:
pruning **is not secrecy**, and the answer to a recorded secret is to rotate
it.

That answer is right for a password and wrong for a journal. You cannot rotate
a paragraph about a person. 0013 was deciding what `prune` may delete, so it
was entitled to decline the question; this document takes it up.

The thing 0013 assumed, and this document contradicts, is that a redacted node
is impossible — that content is interleaved into operation documents so
thoroughly that destroying any of it costs the history its future. It does not,
and the reason is a property of 0007's format that nothing had needed until
now: **an operation's arithmetic and an operation's payload are different
bytes**, and only the payload has to be destroyed.

## The decision

- **Forgetting destroys payload and preserves shape.** A **forgetting
  document** stands in for an operation document. It states the same
  operations, at the same positions, with the same item counts, and replaces
  the items it forgets with a `\ forgotten` marker.
- **It is a document of its own**, carrying a `forgets` header naming the
  digest of the document whose bytes were destroyed, stored under its own
  digest like everything else, so no file ever lies about its own name.
- **Forgetting is monotone and converges by union**, which is the rule the
  store already lives by (0003).
- **A forgotten item is forgotten wherever it is quoted**, including the `-`
  lines of the revision that later deleted it, so `forget` is a walk over a
  file's history rather than an edit to one document.
- **Merge and replay do not consult payload**, so a redacted history
  materialises and merges exactly as it did, byte for byte, outside the
  forgotten runs.
- **A forgetting document carries no message**, inverting 0013's rule for
  tombstones, because the reason for a redaction is usually the redacted thing.
- **Receiving a forgetting document may destroy the bytes it names.** This is
  not an exception to 0013's "never automatic": the fact is in the graph, which
  is precisely what pruning lacks.
- **A store that has forgotten something can prove its structure and not its
  content.** That is the price, and no wording makes it smaller.

## What a redaction has to survive

Look at what a reader actually consumes:

```text
historica-v0

delete 3 1
-Nothing here chooses a document syntax yet.
insert 4
+Model causality before content: immutable revisions, explicit parents, and a
+history that merges by union.
```

`replay` needs `delete 3 1`, `insert 4`, and *how many* content lines follow
each. `merge` needs the same, plus the item names it derives from them — item
*i* of revision *R*, where *i* is the operation's index in the document plus
the item's offset within it. Neither reads a line's text to decide where
anything goes: 0007's ordering rule breaks ties by name because 0002 refuses to
trust a timestamp, and a name is arithmetic.

The text after `+` is the file's content. The text after `-` is redundancy —
`replay` spends it holding the document against the parent it claims to edit,
which is the error 0007 asked for by name.

So a document that keeps every position, every count, and every `\ no newline`,
while destroying the text, replays and merges identically. Everything
downstream still materialises. The file has `\ forgotten` where a run of lines
used to be, and nothing else in the history moves.

This is finer-grained than an archive can manage. prov-history forgets a blob
and loses a whole captured version of a document; here, forgetting costs
exactly the runs that were forgotten. The trade runs the other way too, and is
stated below: prov's forget is total because there is one store.

## The forgetting document

```text
historica-v0
forgets 6397b3a4b3b8abd444da81f2f731dd67c4f5bcea5dc03c4e8141783d1f1b4c53

delete 3 1
-Nothing here chooses a document syntax yet.
insert 4
\ forgotten
\ forgotten
```

The preamble is 0004's, so this file says how to hash itself and is identified
by content rather than by the extension it happens to carry. `forgets` names
the operation document this stands in for; a revision's `edit` line still names
that digest, and a reader that cannot find it looks for a document that says
`forgets` it.

`\ forgotten` is a marker line, standing where a `-` or `+` line stood, one per
destroyed item. The format already spells a fact about an item on a line
beginning with a backslash — `\ no newline` — and 0004 says a reader's
vocabulary can only grow, so this is growth rather than a second grammar. A
`\ no newline` that applied to a forgotten item still follows it, because
whether a file ends without a terminator is shape.

The example forgets the insert and keeps the delete, which is the ordinary
case: redaction is per item, not per document.

Two things follow from storing it under its own digest rather than under the
one it replaces. `FilenameLies` keeps meaning what it means, and
`shasum -a 256 -c MANIFEST` keeps passing on every file the store still holds —
the missing verification is of a file that is not there, which is the honest
shape of the loss.

## Forgetting is monotone, so it converges

Two replicas may redact the same document differently: one forgets a paragraph,
the other forgets the whole insert. The store is a grow-only set unioned by
copy (0003), so both documents survive the sync, and the rule that resolves
them has to be one that does not depend on which arrived first.

**An item is forgotten if any held forgetting document forgets it.** The
reader's view of a document is the intersection of what its forgetting
documents still reveal. That is monotone, order-independent, and idempotent,
which is the same reason set union was the right merge for the history itself.

It also fails safe. A rule taking the *union* of what remains readable would let
a stale replica un-forget a paragraph by syncing an older, less thorough
redaction back — a redaction that could be undone by transport is not one.

## An item forgotten once is forgotten everywhere it is quoted

The `-` lines are the catch. A paragraph inserted by revision *R* and deleted
by revision *S* has its bytes in two documents: *R*'s insert, and *S*'s delete,
which quotes it verbatim so `replay` can check itself. Destroying *R*'s copy
alone destroys nothing.

So `forget` names items, not documents, and walks the file's history for every
document that holds them. Items are named `(R, i)`, but a delete states a
position and a count against a parent rather than a list of names, so finding
the deletes that quote a given run means replaying the file. That is real cost,
and it is why forgetting is a command over a history rather than an edit to a
file.

Replay carries the property forward. A recorded item that is forgotten matches
whatever the parent holds at that position — the redundancy is exactly what was
spent — and the item it produces in the resulting state is forgotten too. Its
terminator is still checked, because that is shape. So forgottenness propagates
into every materialised state that contains the item, which is what makes the
destruction real inside the store rather than merely recorded.

`check` reports a document that still quotes bytes another says were destroyed,
as a note: mid-sync is a legitimate way to be in that state, and 0006's
division is not worth breaking for it.

## The merge does not notice

`merge` names an item `(R, i)` from the operation's index and the item's
offset, anchors it between the identities on its left and right, and breaks
ties by digest and then by index. A forgetting document preserves every one of
those numbers. Fugue's ordering never asks what a line says.

That yields a claim worth holding the implementation to: **redacting a store
changes no merge result except at the forgotten items themselves** — same
bytes, same contested spans, same attribution of every surviving item to the
revision that wrote it. It is a property test over the corpora that already
exist, not a new argument.

## What a forgotten store can still prove

Everything except the one thing that was destroyed.

Every revision document still hashes to the digest that names it, so the graph,
the tree facts, the authorship, and the causal edges are as verifiable as they
ever were. Every forgetting document hashes to its own name. What can no longer
be shown is that the destroyed payload was what the vanished digest said it
was: the link between `edit <digest>` and a run of bytes is exactly what a
person chose to break.

The README's claim — that hashing the file is as trustworthy as hashing a
canonical model — becomes conditional the moment a store forgets something, and
the conditional belongs in the README rather than in a footnote here. A store
that has forgotten nothing is unaffected, which is nearly all of them.

## Complying is a recorded fact carried out, not an automatic deletion

0013 says nothing deletes a readable file except a person asking for it in
those words, and means it. A forgetting document arriving from another replica
looks like a violation of that and is not, for the reason 0013 itself gives
about `prune`: what makes automatic deletion unacceptable is that no fact
stands behind it. Pruning acts on a local judgement about what is worth keeping
and could be wrong. A forgetting document *is* the recorded intention, written
by a person, in the graph, propagating by the same copy every other document
does.

The alternative is worse in the way that matters. A redaction that waits for a
second manual step on every machine is a redaction that has not happened on the
machine the person forgot they owned.

So: `record`, `check`, and `arrange` still delete nothing. Receiving a
forgetting document destroys the bytes it names, prints what it destroyed, and
is the only automatic destruction this format has. A replica that declines to
comply is outside the model and always was.

## No message

0013 requires a message on a tombstone, because the reason is the only thing
the tombstone carries and its absence is a hole in the log.

Forgetting inverts that. "Remove the paragraph about the argument with
Rowan" is a message that survives on every replica forever and leaks the thing
the redaction existed to remove. A forgetting document therefore carries no
message and no author: it states which document, and which items, and nothing
about why or who.

`arrange` names the file after the revision and file it stands in for, since
there is no message for it to file the document under.

## What forgetting cannot hide

Stated plainly, because a tool that implied otherwise would be worse than one
that says nothing:

- **Shape.** That twelve lines were inserted here and two removed there.
- **Position.** Where in the file it happened.
- **The revision around it** — its author, its time, its message, and its place
  in the graph. All of it was recorded in the revision document, whose digest is
  load-bearing for every descendant.
- **That something was forgotten at all.** This is by design: `check`
  distinguishes *forgotten* from *lost* and from *corrupt*, and it can only do
  that if the store says which.
- **Paths.** `add` and `move` live in the revision document, so a filename that
  is itself sensitive cannot be redacted without rewriting a revision — the one
  thing an append-only store cannot do. Deferred below, and it is the limitation
  a journal meets first.

## What forgetting means depends on who has copies

The format can only do one of these. Naming the other two is what keeps the
first one honest.

1. **A shared store.** Bytes are destroyed here; intent propagates; other
   replicas comply or do not. Nothing stronger is available to any design, and
   a system that promised more would be lying about a network.
2. **A store whose replicas can be enumerated** — this machine, or three
   devices one person owns. Here `prune` is already total deletion. 0013 says
   pruning cannot promise secrecy *because* it cannot propagate, which is a fact
   about not knowing who holds copies rather than about the format. Give a store
   a declared replica set and the same command becomes honest, with no format
   change at all.
3. **A file that never leaves.** `MissingOperations` is already a note, so a
   replica that never receives a file's operation documents passes `check`
   today. What it cannot hide is the file's name, for the reason above.

Tiers 2 and 3 are policy and transport, not this decision. They are recorded
here because "forget" means something different in each, and a person asking
for it deserves to be told which one they are in.

## Rejected alternatives

**Deleting the operation document outright.** `MissingOperations` is already a
note, so it is tempting: destroy the file and the store still checks. But every
later operation on that file states its positions into the parent state, so a
missing document costs the file every subsequent revision — forget one
paragraph, lose the file's whole future. This is the assumption 0013 made and
the reason it concluded redaction was impossible.

**Rewriting the operation document in place**, letting its digest change. The
naming revision's `edit` line stops resolving, so the revision must change, so
its digest changes, so every descendant must change. That is a rewrite of the
entire history, converges nowhere, and is what 0003's append-only store exists
to prevent.

**A placeholder written as ordinary content** — `+[redacted]`. Indistinguishable
from a person typing those characters, so `check` cannot separate forgotten
from written, and the redaction becomes invisible to the tool that has to
account for it. `\ forgotten` is outside the item grammar for exactly this
reason.

**Encrypting the payload rather than destroying it.** Key management is a second
store that has to outlive the history, the readable files stop being the
authority (0003), and a key that leaks retroactively un-forgets everything at
once. Destroying bytes is the only operation whose failure mode does not grow
over time.

**A separate snapshot-based area of the workspace** for sensitive files, trading
collaboration for rewritable history. Rejected on three counts. It needs a
second implementation of replay, merge, tree, and `check`, permanently, inside a
project whose claim is that one readable format is the authority. Scoping it to
a directory fights 0008, where there are no directories and a path hangs off a
file's identity, so a file moved out of the private area would change history
model mid-life. And it converges no better than this does: two replicas of a
snapshot area still both hold the old snapshot. A private area may well be worth
having for other reasons; it is not what makes forgetting possible.

**A propagating do-not-resurrect ledger.** 0013 rejected it — permanent state
that grows forever, can never be complete, and turns every replica into a
gravekeeper. A forgetting document is not that: it names one document, is
bounded by the history it belongs to, and is the redaction rather than a policy
about one.

## Consequences

- `historica forget <target> <path> --lines <a>..<b>` resolves the items in that
  span at that revision, walks the file's history for every document holding
  them, writes a forgetting document for each, destroys the originals, and
  prints every file it touched. `--dry-run` prints without destroying.
- Three findings, all notes: a document was forgotten; a store holds both a
  document and a forgetting document naming it, which is 0013's deferred
  resurrection arriving by sync; a document still quotes items another says were
  destroyed, which is a redaction that has not finished arriving.
- `ContentDisagrees` is not reported for a forgotten item, since the comparison
  it makes is the thing that was destroyed. The terminator is still held.
- The README's `shasum -c MANIFEST` claim gains its conditional when this is
  implemented, not before.
- Tests worth naming: every revision after a forgotten one still materialises;
  merge results are identical outside the forgotten runs, including the
  attribution of each item to the revision that wrote it; two forgetting
  documents for one document union to the more-forgotten result in either
  arrival order; the text of an item forgotten at its insert is not recoverable
  from the delete that quoted it; a forgotten store passes `check`; and
  forgetting twice is a no-op.

## Deferred

**Forgetting a path.** Above: `add` and `move` are revision-document facts, and
a revision's digest is named by every descendant. Redacting a filename means
either a format change in 0008 — recording a path indirectly, so that the thing
a revision names is not the sensitive string — or accepting that names leak.
The second is where this lands for now, and it should be said out loud in the
interface rather than discovered.

**Binary content**, which 0008 gives a shape and no implementation. A binary
file has no items to preserve, so forgetting one is nearer to prov's case:
the whole payload goes and only its digest and length remain. Answered by
decision [0066](0066-forgetting-a-payload.md), which spells that as a document
of two headers and finds the deferred case was the easy one — there being no
shape to preserve, the stand-in is a statement rather than a reconstruction.

**Text minted in a resolution** — answered by decision
[0050](0050-forgetting-a-merges-own-text.md), which gave the resolution
grammar a `forgets` header and a marker of its own. Recorded here because the
gap was real: 0032 arrived after this decision, and the text a merge states
that exists nowhere else was for a while the one text this could not reach.

**Enumerable replica sets**, which is tier 2 above and the thing that would let
`prune` say what people already assume it says.

## Deferred

Whether a person should be able to forget an item **without** propagating the
request — destroying it here while saying nothing to any other replica. It is
strictly less useful and strictly more honest, and which one a journal wants
probably depends on whether the other replicas are other people or other
laptops. Decision [0028](0028-accepting-by-path.md) observes that Historica has
no remote or tracked replica to propagate to: stores meet by external copying.
“Local only” therefore has no stable counterpart yet, and remains deferred.
