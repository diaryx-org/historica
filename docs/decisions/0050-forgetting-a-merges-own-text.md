# 0050 — Forgetting a merge's own text

Decision [0014](0014-forgetting.md) destroys an item's payload and preserves
its shape. Decision [0032](0032-a-merge-states-its-resolution.md), which came
later, gave `operations/` a second grammar in which a merge states a contested
file whole: runs kept from documents it names, and `insert` pieces holding
items the person minted while resolving. 0014's stand-in is written in the
first grammar — a `forgets` header, and a marker standing where each destroyed
item's text stood — and the resolution grammar had neither.

So the one kind of text a merge states that exists nowhere else was the one
kind of text that could not be redacted. `forget` refused it, which was honest
and useless.

## The hole was wider than "text typed at a merge"

A resolution cannot reorder the items it keeps. The walk records which
elements survive a merge and which are dropped; where they sit in the file is
the tree's order, not the order the `keep` lines appear in. `replay::assemble`
concatenates in document order, and the two agree only because the recorder
mints anything the person moved.

That is not a defect in the recorder — it is the mechanism holding the two
readings together — but it means minting is unavoidable, and a person who
resolves a merge by putting the two runs in the other order has silently
created a second copy of a run that already had a name. 0032 chose references
over restatement for exactly this reason: "a restated line would be a new
item, and the first merge reaching across this one would meet the same text
twice."

The consequence for 0014 was worse than a refusal. Forgetting that run *where
it was written* destroyed the bytes, wrote a stand-in, passed `check`, printed
success — and left the text readable at the head, in the copy. A redaction
that reports success and does not redact is the one failure this feature must
not have.

## The decision

- **A resolution may forget, in its own grammar.** A forgetting resolution
  carries a `forgets` header naming the digest whose bytes were destroyed,
  states every `keep` exactly and every `insert` at its own length, and
  replaces the items it forgets with `\ forgotten`. Stored under its own
  digest, like everything else.

- **A `keep` is never redacted.** It carries a reference and no text, so there
  is nothing in it to destroy. Items a resolution keeps are forgotten in the
  document that wrote them, and the `keep` then meets the stand-in — which is
  what preserving shape was always for. What a resolution has of its own is
  exactly what its `insert` pieces mint.

- **A forgetting resolution states no `result`.** Decision
  [0031](0031-a-document-states-its-result.md)'s rule and 0014's reason for
  it: the file it assembles is now the destroyed state, and a digest would
  confirm a guess at it. `result` is therefore optional in this grammar,
  mandatory in an ordinary resolution and forbidden in a forgetting one —
  the asymmetry the operation grammar already had.

- **Redactions union, unchanged.** An item is forgotten if any held forgetting
  resolution forgets it. Monotone, order-independent, idempotent, and it fails
  safe, so a stale replica syncing back a less thorough redaction cannot
  un-forget anything. Shape here is easier to check than an operation
  document's: a `keep` must match exactly, and an `insert` must mint the same
  number of items with the same terminators.

- **Forgetting a span forgets the copies a resolution made of it.** An item a
  resolution dropped, matched against an item the *same* resolution minted
  with identical text, is that item restated under a new name, and goes with
  it. To a fixpoint, because a later merge can copy the copy.

  The pairing is deliberately narrow. It is one resolution's drops against
  that same resolution's mints, never text against text across the history: a
  line that reads the same because somebody typed it again is a different
  item and stays one, which is 0014's rule that redaction is per item rather
  than per document — or per string.

## Why this is additive, and keeps the one spelling

Decision [0047](0047-one-spelling-for-the-format.md) reserves a new preamble
for a change that would otherwise be *silently misread*, and says additive
growth needs none: "a document using a header this reader lacks fails closed,
named, at the line that uses it." Every spelling this decision adds does
exactly that, checked rather than assumed — a 1.0 reader meeting `\ forgotten`
inside an `insert` refuses at that line, one meeting `forgets` where it wants
`result` refuses at that line, and one meeting both headers refuses at the
blank line. None parses, and none is mistaken for the other grammar, because
`is_resolution` reads the first line of the *body* and a forgetting resolution
still opens with `keep` or `insert`.

The preamble stays `historica`.

## Consequences

- `ResolutionDocument` gains `forgets`, and `result` becomes `Option`.
- `Store::effective_body` is the one question a reader of an `edit` digest
  asks: the document that digest names, in whichever grammar, with redactions
  folded in. `effective_operation` and `effective_resolution` are filters over
  it. Asking it once is also what keeps decision
  [0049](0049-what-a-lookup-does-not-prove.md)'s bargain — a hit costs no
  directory walk, and a miss costs one for both grammars rather than one
  apiece.
- `Body::forgets` is how every command that must keep a stand-in alive, carry
  it, or comply with it asks what a document forgets. `prune`, `export` and
  `receive` each looked only at operation documents and each would have
  dropped, stranded, or failed to comply with a redacted merge.
- `Quoted` gains the item's `text` and the revisions that `dropped_by` it
  without quoting — the removal a resolution performs by not keeping
  something. Both are what pairing a drop with a mint needs.
- `Forgotten::writes` holds `Body`, since a stand-in is written in the grammar
  of what it stands in for.

## Deferred

**Forgetting a `keep` range as such**, which would mean a resolution stating
that a run it references is redacted rather than the referenced document
saying so. It would duplicate a fact 0014 already places in one spot, and the
union rule would then have two places to disagree. Redacting where the item
was written is the answer, and it works through any number of merges.

**A resolution that can reorder what it keeps.** It would remove minting, and
with it this whole class of copy — but it means the walk taking order from the
resolution rather than from the tree, which is a change to what 0032 records
and to how a later revision counts into a merge. Not attempted here, and the
copy is now redactable either way.
