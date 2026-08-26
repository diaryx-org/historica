# 0069 — A place to say a store is newer

0045 wanted a store-layout gate and deferred it. 0051 wanted one and deferred
it, adding that *a third should build it*. 0062 was the third, declined, and
called that "the least defensible sentence in this document."

This is the fourth, and it does not build the gate either. What it does is
notice that one part of the gate has a deadline the rest does not, and that
1.0 is that deadline.

## What 1.0 forecloses

The three deferrals all describe the same failure: a store written by a newer
Historica, opened by an older one, read as healthy and understood wrong. What
none of them noticed is that **1.0 does not merely lack the gate — it promises
there will never be one.** Three sentences, all of them shipping:

> Nothing hashes this file, so a person may write what they like there.

— `check_header`, which takes `text.lines().next()` and discards the rest.

> A directory beside these that is not named here belongs to whichever tool
> wrote it. Historica reads nothing in one and reports nothing about one.

— `format.txt`, which hands every unclaimed name at the store's root to
somebody else, by 0046.

And `check` never enumerates the root at all. It walks the five directories it
knows by name.

Together those leave nowhere in a store that a 1.0 reader will look for a
warning: not the header below its first line, not a new file at the root, not
a new directory. A future release cannot introduce a gate, because a gate is
only a gate if the old reader reads it, and every deployed 1.0 will have been
told not to.

The single counterexample is the evidence rather than the exception. `check`
hard-codes a `StaleSkipped` finding for the literal filename `skipped.txt`,
which is the ad-hoc gate 0045 spent in place of the real one. 0045 was already
honest that it works only because the layout it warns about is the one 0045
replaced. One `if` per historical filename is not a mechanism, and it can only
ever look backwards.

So the thing with a deadline is not the gate. It is the **space** the gate
would occupy, and whether the reader shipped in 1.0 refuses what it finds
there.

## The decision

**The store header is a document's shape, and its header block is reserved and
empty.**

`historica.txt` is read as: the preamble line, then headers up to the first
blank line, then a note nothing parses. That is 0002's layout exactly, and it
is already what `init` writes — `historica`, a blank line, `HEADER_NOTE` —
with an empty block that no reader had been told existed.

- **The block is closed.** There is no header this release writes, and none it
  reads. A reader meeting any line between the preamble and the first blank
  line refuses the store, naming the line and saying a newer Historica likely
  wrote it.
- **Empty is the default and stays the default.** Every store 1.0 writes says
  nothing there, so nothing about this narrows what a later reader will accept.
- **The note is unchanged and still unparsed.** Everything below the blank line
  belongs to whoever opens the folder, as 0021 intended.

That is the whole decision. What goes in the block, who writes it, and when,
are not decided here.

## Why the header file and nowhere else

Because it is the one file in a store that is neither hashed nor referenced,
which `FORMAT_FILE`'s own doc comment already says of both it and `format.txt`.

This is the sharper form of 0047's argument than 0047 gave. 0047 retired the
`historica-v0`–`v5` numbering on the grounds that version numbers earn their
keep only where old readers and new writers coexist, and before a first
release they do not. True, and incomplete. The deeper reason a document cannot
carry a version dial is that **a document is named by the digest of its own
bytes**, so a line added to one renames it: a store could not gain a gate
without every revision in it changing identity, which is the one thing this
format will not do. The store header has no digest to change.

So 0047 did not delete the thing that belonged here. It deleted a version
machine from the layer that could never have held one, and left the layer that
can with nothing. 0045 had already named that gap, two decisions earlier, and
0047 is what made it permanent rather than merely open.

It is also 0062's own move, one level up. 0062 gave a bookmark a second line
so that

> a file whose first line parses and whose second line does not is diagnosably
> a file written by a newer historica

and this gives the store that same sentence about itself. 0062 had the shape
right and was looking at the wrong file.

## What stays deferred, and why that is not a fourth evasion

0062 named three arguments the gate needs: a place of its own, a rule about
who writes it and when, and an account of how 0004's *lowest version that
expresses what it holds* survives in a format with no versions. This decision
answers the first and leaves the other two.

The difference is that only the first has a deadline. A rule about who writes
the header is needed by the first release that writes one; a spelling is
needed by the first thing that needs spelling. Designing either now means
guessing at a layout change nobody has proposed, which is 0045's reason for
deferring and is still correct about those two. Reserving the space costs
nothing and buys the option; deciding the vocabulary costs a guess and buys a
constraint.

What can be said is which way the answer probably goes, so that the next
decision starts from an argument rather than a blank page. **Declare what you
use, not what you are** — names in the block, not an ordinal. That keeps
0004's asymmetry exactly, writers constrained and readers only growing, and it
buys something an ordinal cannot: a newer Historica writing a store that
happens to use nothing new writes no header at all, and 1.0 reads that store
forever. An ordinal locks out every older reader on every layout addition,
including the additions they could have safely ignored.

Against it: names re-grow the raise-on-use writing 0047 was glad to be rid of,
and they reach `export` and `receive`, which would have to carry and union
them. That is smaller than what 0047 deleted — one line in one unhashed file,
against a `Version` enum through every parser and a minimum-version pass over
everything travelling — but it is not nothing, and it is a real trade rather
than an obvious one. Nothing here settles it. The reservation is agnostic: an
ordinal and a set of names occupy the same slot.

## Consequences

- `read_header` is one reader for both callers. `Store::open` and `check` had
  each written their own two lines against the same file, which is how they
  would have drifted; the fault it returns distinguishes a format this reader
  lacks from a layout it lacks, because they are different sentences to the
  person holding the store.
- `StoreError::UnknownLayout` and `Finding::UnknownLayout`, the second at
  `Severity::Error`, beside the `UnreadableStore` they sit next to.
- `HEADER_NOTE` and `format.txt` both describe the block, because a store that
  claims to need no tool has to carry the description that makes the claim
  true. `format.txt` gains a section for `historica.txt` itself, which it had
  never described, and its "Directories another tool wrote" section now says
  where Historica speaks about its own layout — the two mechanisms are
  adjacent and easy to confuse.
- **A hand-written header whose note begins on the second line stops opening.**
  This is the one behavioural change and it is real: `HEADER_NOTE` invited
  exactly that, saying a person may write what they like below the first line.
  Published 0.1.0 and 0.2.0 stores are unaffected, since 0047 already refuses
  them at the preamble, so the reach is somebody who hand-made a store from the
  documentation. Per 0004 the error carries its correction: put a blank line
  above the note.

## Rejected alternatives

**Build the whole gate now.** It would be decided by nothing. Every layout
change this format has actually made is behind it, so the vocabulary would be
designed against imagined changes and would be wrong in the way 0045 predicted
— and, being in a shipped reader, wrong permanently. The space is what cannot
wait; the vocabulary is what should.

**Put the gate in a new root file, `layout.txt`.** It is the same reservation
with an extra file, and it needs 1.0 to refuse unknown root entries — which
contradicts 0046's grant of unreserved names to other tools, and would make
every store carrying a `claims/` directory a store 1.0 refuses. The header
file is already the thing a reader must read first.

**Defer it a fourth time.** This is what the deadline argument rules out.
Every other item on the pre-1.0 list is still available at 1.1; this one is
not, because the promise is made by the readers people install.

**Refuse unknown root entries as well.** A broader gate, and a worse one:
0046 gave those names away deliberately, and a store's root is where a signing
tool, a sync tool and Finder all write. The header block is Historica's own
sentence about its own layout, and that is the only claim it should make.

## Deferred

**What the block says, and who raises it.** As above: the vocabulary, the
writer, and the behaviour of `export` and `receive` when a copy declares
something the origin does not. What would justify deciding it is a layout
change that needs it — and this time the space exists, so the decision that
needs it can be about that change rather than about whether a gate is possible.

**0004's `lowest version that expresses what it holds`, restated.** It is the
same deferral seen from the format's side. The candidate answer is above and
is not adopted.

**Whether `check` should enumerate the store's root.** Distinct from the gate
and worth its own look: today an unknown root entry is invisible to `check`
rather than reported, and 0046 makes that correct for directories it gave
away. Whether a *file* at the root — neither `historica.txt`, `format.txt`,
nor a reserved directory — deserves the `ForeignFile` note that `revisions/`
already gives is an unrelated question this decision does not open.
