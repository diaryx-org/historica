# 0031 — A document states its result

This is the first of two decisions that raise the format to `historica-v3`,
and the pair share one purpose, decided when 0030's review of the tool-less
writer was read: **a person with an editor and `shasum` must be able to read,
verify, and write this format by hand.** The reader was already well served.
This decision serves the verifier, and 0032 serves the writer where serving
them is hardest.

An operation document states what a revision did to a file and never what
results. That is 0007's shape and it stays. But it leaves a hole in the
mission's central claim: a person who replays a chain by hand — apply the
deletes, apply the inserts, arrive at a file — has nothing to hold their
work to. The store is full of digests, every one of them checkable with
`shasum -a 256`, and the one artefact a replayer produces is the one artefact
nothing names. The same hole faces an independent implementation: two
replayers that drift apart discover it only when something downstream
misbehaves, because no document ever said what the right answer was.

0017 already fixed this for one case without saying so. A `text` payload *is*
the file's content, named by its digest, so a file's creation carries its
result in the only header that names it. This decision extends that property
from the state a file begins at to every state an edit produces.

## The decision

- **An operation document states the digest of the file it produces.** One
  header line, `result <digest>`, after `forgets` and before the blank line:
  the SHA-256 of the file's bytes after this document's operations are
  applied — exactly what `shasum -a 256` prints for the file a correct replay
  writes.
- **It is mandatory, and carrying it claims `historica-v3`.** 0002's rule —
  one byte sequence per set of facts — forbids an optional header, which
  would be two spellings for one edit. A document without `result` claims
  version 1 or 2 as it always did and is read forever; a document with it
  claims 3. The writer states it on every document it writes, so a store's
  header rises to v3 on the first record after this lands.
- **Replay verifies it.** A replayed state whose bytes do not hash to the
  stated result is refused in the words `replay` already uses for a quoted
  item that disagrees: the document and the store contradict each other, and
  refusing is friendlier than continuing. `check` inherits the verification
  wherever it already replays.
- **A forgetting document states no result.** Not exempted for convenience —
  forbidden, for 0014's own reason. The result of the operations a forgetting
  document restates is the *destroyed* state, and a digest of destroyed
  content is an oracle: anyone who can guess the sentence can confirm it.
  Forgetting destroys the payload and would leave its fingerprint. So the
  header may not appear beside `forgets`, and verification is suspended
  wherever forgottenness reaches, below.
- **Verification stops where forgetting begins.** A state holding any
  forgotten item is not verified against any result, because the bytes that
  would hash are marker bytes, not the bytes the recorder hashed. This is
  0014's sentence — a store that has forgotten something can prove its
  structure and not its content — collecting one more thing, and it was
  always going to.

## What this buys

**The hand-replayer gets a checkpoint.** Reconstruct the file, run `shasum`,
compare one line. Before this, hand replay was possible and unfalsifiable —
the worst combination, since an error compounds silently into every later
position. After it, every edit in a chain is a place to be told you went
wrong. The quoted `-` lines already catch a replayer whose *parent* was
wrong; `result` catches one whose *application* was.

**An independent implementation gets a conformance test in every store.**
The corpus holds the states the replayer is held to, but the corpus travels
with this repository. A v3 store carries its own expected answers, one per
edit, so a second implementation is checked by every store it opens rather
than by the test suite it remembered to run.

**The cache gets its key.** 0007 named `cache/`'s first intended inhabitant —
materialised file states — and left the key undesigned. The key is now in
the document: a cached state is filed under the result digest that names it,
verified by construction, disposable as ever.

**Drift becomes loud.** The linear fast path, the event-graph walk, and any
future replayer must all produce bytes hashing to the same recorded result.
A divergence between implementations, or between versions of this one, stops
being a subtle wrong answer and becomes a refusal naming a digest.

## The cost, stated

The header is derivable, and this format refuses derivable redundancy as a
rule — a fact stated twice is a fact that can disagree with itself. The rule
has one standing exception, made deliberately in 0007: a delete quotes the
items it removes, redundantly, *because* the redundancy lets a reader check
the document against the parent and lets `replay` refuse a document that
lies. `result` is the same purchase at the other end of the same document:
the delete's quotes check the document against where the file was, the
result checks it against where the file ends up. What guards every such
redundancy is that disagreement is an error someone reads, not a choice
something makes — and that is what replay's verification is.

The other cost is that every new document is version 3, not only the exotic
ones. When 0014 introduced version 2 it could say a store that forgets
nothing stays version 1; there is no analogous mercy here, because the point
is that every edit is verifiable, and an edit that opts out is the hole
again. A v2 reader refuses a v3 store. That is acceptable now and only now:
0.2.0 was never published, no store exists whose writer this repository does
not control, and this is precisely the window 0021 said closes on first
contact with a stranger's store.

## Rejected alternatives

**An optional `result`.** Two byte sequences for one set of facts, which
0002 spent itself refusing. Optionality would also make the guarantee
statistical — some edits verifiable, some not — which is a property nobody
can build on.

**Keeping the result in a forgetting document, redacted-state flavoured.**
Compute the digest of the state *with* markers, so the union rule could
still verify something. But two independent redactions union to a state
neither of them hashed, so the value goes stale exactly when forgetting is
exercised as designed, and a header that is usually decorative and
occasionally wrong is worse than none. Verification is suspended under
forgetting either way; the header may as well be honest about it.

**A digest of the state's items rather than its bytes.** Item-level identity
would survive forgetting better, but the mission's verifier is `shasum` over
a file a person can see, and an item serialisation is a second canonical
form to specify, implement, and drift on. The result names bytes because
bytes are what a hand has.

**A separate manifest of states**, one file listing every result. A second
place the same fact lives, and the one file a person would have to keep
consistent by hand. The result belongs in the document that produces it,
where forgetting it is impossible and checking it is one line of reading.

## Consequences

- `format::operations` gains the `result` header: parsed strictly, written
  after `forgets`, refused in a forgetting document, refused when repeated.
  `OperationDocument::needs` claims `Version::V3` for any document carrying
  it, and `Version::CURRENT` becomes V3.
- `diff` stamps the result on every document it produces, which covers
  `record`, `amend`, and `record --merge` in one place; the synthesised
  creation document `replay::creation` builds carries the payload's own
  digest, so verification is uniform across a file's whole chain.
- `replay` verifies a produced state against the document's result whenever
  the state holds no forgotten item, and `check` inherits it everywhere it
  replays.
- The corpus gains v3 documents and the invalid spellings that pin the
  grammar: a malformed result, a repeated result, a result beside `forgets`,
  and a result that disagrees with what replaying produces.
- Tests worth naming: `write(parse(bytes)) == bytes` for a v3 document; a
  document whose result lies is refused at replay and reported by `check`; a
  v1 document still parses and still claims v1; a store that records once
  after this lands raises its header to v3; forgetting a line suspends
  verification for every downstream state that shows the marker, and a
  hand-written marker line in fresh content does not.

## Deferred

**A result for the whole tree.** A revision-level digest of the entire file
set would give hand verification one further checkpoint, but the tree at a
revision is already derivable from headers a person can read, and a
per-revision tree serialisation is a canonical form this format does not
have and should not invent casually. If it ever arrives it arrives as its
own decision.

**`cache/` actually gaining the materialised states** this decision gives a
key to. Sanctioned since 0007; still waiting for the measured need.
