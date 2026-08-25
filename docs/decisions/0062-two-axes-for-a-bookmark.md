# 0062 — Two axes for a bookmark

0042 named three things an export leaves behind, and gave one reason for two
of them:

> Not `names/`, not `skipped.txt`, not `cache/`: bookmarks and rules are the
> exporter's, and a cache is nobody's.

0051 took the rules half apart and found the sentence doing two jobs at once.
A rule that keeps a recipient's build output out of a history is a fact about
the repository; a rule that names a client is a disclosure; and calling both
of them *the exporter's* got the second right and the first wrong. The
bookmarks half is in the same position, word for word, and 0051's argument
transfers without modification.

**The exclusion binds only where it is useless.** An export is a replica and
`receive` is its pull, which is 0042's own best property. So a copy that meets
its origin unions the withheld bookmarks straight back: `receive` fills in
every name the receiver lacks, and that is precisely the rule 0042 said this
was waiting on —

> **Bookmarks in an export**, behind the union rule 0029 already wants and
> does not have.

The union rule is built. `receive` takes every name the source states and the
receiver does not hold, and `MutableConflict::Name` is what it says when one
name points two ways. The condition 0042 set has been met and nobody went back
for the deferred item it gated. The party who can perform that receive holds
the origin store entire — a strictly larger disclosure than a list of names —
and the party the exclusion actually withholds from is the stranger who
fetched a tarball, from whom it withholds which revision the exporter calls
`main`.

**And the half 0042 got right transfers too.** `fix-acme-layoffs` states, in
its own filename, the fact `private clients/acme-layoffs/` exists to withhold.
The rule kept the files out of history, so the revisions under that bookmark
say nothing about the client — the files that would have said it were never
recorded. The bookmark's name is the whole of the remaining leak, and no
amount of a recipient wanting to know where `main` is makes that name theirs
to read.

So a bookmark has a second axis, and the only question this decision has to
settle that 0051 did not is where the marker goes. A rule carries its axis in
its own verb, because a rule is a key and a value and the key was already
doing work. A bookmark's whole content is its target. There is nowhere in
`change qpvuntsmwlrkzxonmvtplsyq` for a second fact to live.

## The decision

- **A bookmark file may carry a second line, and `private` is the only line it
  may carry.** The first line is the target, unchanged in every particular:
  `change`, `revision` or `file`, and one of the three. A file with no second
  line is shared, which is every bookmark file written before this decision.
  A second line spelled anything else is malformed, a third line is malformed,
  and `private` without a target above it is malformed.

- **A shared bookmark travels, if the copy holds what it points at.** `export`
  writes a file into the `names/` it already creates empty, for every shared
  bookmark whose target the copy will hold. The test is the one `check`
  already applies: a change some exported revision records, a revision the
  copy holds, or a file identifier some exported revision says anything at all
  about. 0042's clause is superseded in the half that named bookmarks;
  `cache/` stays behind for the reason 0042 gave it, which was never this one.

- **A private bookmark stays behind, and so does one pointing past the
  target.** They are two different facts and `export` reports them as two
  counts, beside the rule counts 0051 gave it. A copy that quietly dropped a
  name is what this decision is fixing, and so is a copy that quietly acquired
  one.

- **The travel axis is a field, and the target conflicts while the axis
  joins.** `receive` compares targets exactly as it does today: a name the
  receiver lacks is taken whole, private or not; one it holds pointing
  somewhere else is `MutableConflict::Name` and the receive writes nothing.
  What is new is that where two replicas agree about the target and disagree
  about the axis, the union is `private`. A name marked private on one machine
  reaches the others by the transport that already runs, which is exactly what
  0051 calls the feature rather than a concession.

- **`Bookmark` is the new type, and `Name` is untouched.** `Name`'s doc comment
  says *what a bookmark points at*, and it goes on saying it. A `Bookmark` is a
  `Name` beside the flag, and that is what `Store::names` maps a name to.

- **`name --private` and `name --shared` state the axis; bare `name` keeps it.**
  A bookmark that already exists keeps whatever axis it has when something
  moves it, which is what `record` does on every commit — a bookmark that
  un-privatised itself because a person recorded onto it would be the leak
  this decision exists to prevent, arriving from the one command nobody
  thinks of as a disclosure.

- **`offer` lists `names/` and `fetch` takes only the names it lacks.** The
  manifest gains a `name` kind, which an older fetcher discards on the
  standing rule 0056 gives an unknown one. A fetcher that holds a name already
  keeps it, whatever the publisher says: `fetch` is *taking what is missing*
  and a bookmark it has is not missing. So a publisher moving `main` forward
  costs a fetcher nothing, which is not true of any rule that made a moved
  bookmark a conflict.

- **`names` prints the axis, and so does every message that prints a
  bookmark.** A conflict between a private bookmark and a shared one naming
  one target would otherwise print the same text twice.

- **`check` gains no finding.** One name is one file, so a bookmark cannot be
  private and shared at once. The contradiction 0051 had to name is closed
  here by construction.

## Why a field and not a key

0051 spent a section refusing exactly what this decision adopts, and the
refusal does not reach here. Read what it turns on:

> A bit is a second fact per rule, and a second fact has to merge. Consider
> one rule held private on the laptop and shared on the desktop. Union — the
> operation every other set in this store uses — has no answer.

The container is the argument. `skipped/` is a set, 0045 spent a whole
decision making it order-free, and a flag on an element of a set makes element
identity ambiguous: two rules or one, and whichever answer union gives is a
precedence rule inside the one place that had none.

`names/` is not a set. It is a map with a name for a key, and it has had an
explicit disagreement rule since 0006 — bookmarks are *the only mutable files
in a store, and therefore its entire conflict surface*. A flag on a map's
value creates no ambiguity about which entry it belongs to. There is one
`main`, there is one file stating it, and the only question is what two
replicas do when they disagree about the flag.

They join, and the join is not a tie-break either. Read the flag as what it
is — an assertion that somebody asked for this name to be withheld — and the
union of *asked* and *did not ask* is *asked*, which is the same union every
other set in this store performs. It fails toward withholding, which is the
direction this design never fails in. What it costs is the reverse trip:
un-privatising is deleting the file and stating it again on every replica, and
one that has not heard yet re-privatises it. That is 0051's deferred
*un-privatising a rule*, in the same safe direction, for the same reason.

The alternative was putting the axis into the target comparison, so that a
disagreement about it is a `MutableConflict::Name`. It is refused because
`ReceiveError::Mutable` refuses the *whole receive* — every revision, every
rule, every payload — and privatising a bookmark on the laptop would deadlock
every sync with the desktop until the person restated it there. That is the
manufactured conflict 0045 removed and 0051 declined to reintroduce, arrived
at from the one direction where it would look principled.

## Why a second line and not a sixth key

The direct mirror of 0051 is keys: `private-change`, `private-revision`,
`private-file`. It is refused on 0051's own test.

> A cross product can only be afforded if the vocabulary on each side is small
> and closed.

The matching side of a rule had two kinds, and 0051 closed it by argument in
the same breath. The pointing side of a bookmark has three, and 0024 already
proved it open by adding `file` to the two 0006 declared. A cross product over
a vocabulary that has grown once is six keys today and eight the next time
somebody finds a thing worth pointing at, and each of them welds an axis into
a word that is supposed to name a kind. Six words for three kinds and two
axes is the arithmetic 0051 refused when it was three keys for a gap it could
not close.

0006 is the sentence that has to give way, and it gives way cleanly:

> A name holds exactly one line, `change` or `revision`, as 0003 described it.
> The two-line form looks free and is not. A second line that can disagree
> with the first needs a precedence rule, and every reader — including a
> person with `cat` — has to know it.

That is an argument about a `revision` witness under a `change` pointer: two
claims about one target, which can disagree, go stale, and need a reader to
know which wins. A travel axis makes no claim about the target and cannot
disagree with it. 0006's sentence is superseded and 0006's reasoning is
untouched, which is the only honest way to supersede a decision that argued
for itself.

There is a second thing the line buys, which the keys cannot. A file whose
first line parses and whose second line does not is diagnosably a file written
by a newer historica; an unknown key on the only line is indistinguishable
from a typo. So the error message can say which it is, and the reader is told
it is old rather than told the file is wrong. That is not the store-layout
gate — see below — but it is the whole of what a grammar can do about it
unaided.

## What a bookmark can and cannot keep out

The ceiling belongs here for 0051's reason, because `private` will otherwise be
read as a protection it is not.

A private *rule* withholds the text of a line about content that was never
recorded, and 0051 is careful that this is a rule about a rule. A private
*bookmark* withholds less. The revisions it points at are in the copy — that
is the condition for it to have been a candidate for the copy at all — so what
stays behind is the label and nothing else. **`private` on a bookmark means
the copy does not learn what you called this.**

That is narrow, and it is still the case that motivated the decision. The
revisions under `fix-acme-layoffs` do not name the client, because
`private clients/acme-layoffs/` kept the files that would have out of history.
The name is what is left, and withholding it withholds the last thing there
was to withhold.

Where it is not the case, `private` accomplishes nothing and should not be
reached for. A bookmark over work the export does not carry stays behind
whatever its axis, because the reachability test drops it first; a bookmark
over work the export does carry hides a word above content that is fully
present. Neither is `forget`, which is what removes recorded content, and the
person reaching for `private` to make a branch disappear has asked the wrong
tool.

## What this reverses in 0052

0052 pinned a sentence about this directory, and a test is named for it:
*`names/` is neither written nor removed. An export has never carried
bookmarks, and one somebody made in the published copy is not the exporter's
to delete.* The first clause is what this decision supersedes. The second does
not survive the first.

A published copy holds no record of which of its bookmarks a previous export
wrote — that is exactly the mutable position 0030 refuses to keep anywhere —
so a copy cannot tell *this name was made here* from *this name was carried and
the origin has since dropped it*. The update is therefore all or nothing, and
the two halves fail in different directions. Withdrawing nothing leaves a name
in a world-readable directory after the origin made it `private`, which is this
decision's whole subject arriving in the one place it matters most; withdrawing
everything costs a label somebody made in a copy that 0052 already refuses to
let them record in.

So it withdraws, on 0052's own argument for withdrawing at all: *an export that
only ever added would publish a permanent record of everything the origin ever
held*. It is the same act 0051 already performs on a rule the copy states and
the origin does not, and 0051 was right to call that the only thing an export
removes that a recipient might have been relying on. There is now a second.

## Why the reachability test, and not a dangling name

A bookmark pointing outside the copy is a problem 0042 never had, because
nothing pointed anywhere. `check` calls it `DanglingBookmark` at
`Severity::Note` — *not here yet*, which is the language of an incomplete
replica rather than a fault — so carrying one would not make a copy `export`
refuses, and there is precedent in the `supersedes` edge the closure
deliberately leaves dangling.

It is still refused, on this decision's own subject. A shared `main` pointing
past the export tells a fetcher that unexported work exists and names the
change it ends at, which is a disclosure the travel axis was supposed to
govern, arriving through the spelling that was supposed to be safe. Under
0052 it is also permanent: a published copy re-exported on a timer would carry
a `main` that no fetch can ever satisfy, and emit the note forever.

The rule that comes out of it is worth stating as one sentence, because it is
what the tests pin: **an export never manufactures a finding the origin did
not have.** The test is `check`'s own, run over what travels.

## The one way this fails

A bookmark whose *target* is a disclosure. `revision` and `change` name
digests, which say nothing; `file` names an identifier, which says nothing.
So the value is safe and the name is the exposure, which is the exact inverse
of a rule, where the value is a path and the filename is a label 0045 says
nobody parses.

The consequence is that this axis protects a name and can protect nothing
else, and a person who reads `private` as *do not ship this branch* has been
misled by a word. It is documented rather than renamed: `withheld` and
`unlisted` were the candidates, and both are worse — the first describes the
export's side of an act rather than the person's intent, and the second
suggests a listing the name is absent from rather than a copy it never
reached. `private` is the word 0051 established for this axis, and one word
for one axis across two grammars is worth more than a shade of precision in
one of them.

## Rejected alternatives

**A sibling `history/private-names/`.** 0051 refused the directory form
because a rule's identity would live in its path while 0045 says the filename
is a label. The objection genuinely does not apply here — a bookmark's name
*is* its filename, by 0006 and 0021, so the reader already parses the name —
and it is refused for a different reason. The name is the identity, so
`names/main.txt` and `private-names/main.txt` are one bookmark claimed twice,
and neither union nor `MutableConflict::Name` has an answer that is not
invented for the occasion. The one-file-per-name property is what makes the
contradiction 0051 had to live with impossible here, and a second directory
spends it.

**Privacy in the target comparison.** Above: it makes a privacy disagreement
refuse the whole receive.

**A bookmark that travels but is renamed on the way out.** A copy holding
`branch-3` where the origin holds `fix-acme-layoffs` is a copy whose names
are fiction, and a person who receives it back has two bookmarks for one
change. Presentation this format is willing to vary; naming is not
presentation here, because the name is the identity.

**Filtering an export's bookmarks by an audience.** 0051 refused audiences for
rules on two counts, and both hold verbatim: an audience silently changes what
every rule that does not mention it means, and there is nothing to anchor the
vocabulary to. A bookmark adds nothing to the argument in either direction.

**Leaving `offer` alone and changing only `export`.** It would make the two
transports disagree about one directory: a stranger who copies a published
export gets names, and a stranger who fetches from it does not. The manifest
is what a static host offers *of an export*, and an export is now a thing with
bookmarks in it.

**`fetch` overwriting a bookmark it holds.** The publisher's `main` is the
publisher's. A fetcher who took it once and then recorded onto it has a `main`
of their own, and a fetch that moved it back would be the only place in this
design where transport overwrites a mutable value without asking. `receive`
is where two stores reconcile; `fetch` takes what is missing.

## Consequences

- `Bookmark` is a new public type — a `Name` beside a `private` flag — with
  `parse` over the file's text and a `write` producing it. `Name::parse` narrows
  to the one line it always read, and `Name`'s `Display` is untouched;
  `Bookmark`'s renders one line for a person, since the conflict message and
  the `names` listing are where it is printed.
- `Store::names` maps to `Bookmark`. `Store::name` keeps returning the target,
  because *what does this point at* is what nearly every caller asks;
  `Store::bookmark` is the one that answers both. `Store::set_name` writes a
  target and preserves the axis; `Store::set_bookmark` states both. `Bookmark`
  and the signature of `Store::names` are public, so the implementing commit
  carries a `Behavioural-change:` trailer.
- `receive`'s name pass compares targets and joins axes, and its plan carries
  `Bookmark`s. A private bookmark and a shared one over one target are no
  longer two things that can both be present, so nothing unions to a
  contradiction.
- `export_plan` gains the bookmarks that travel, the count held back as
  private, and the count held back as unreachable; `Exported` carries the
  three, and `export` prints them beside the rule counts. Under 0052 a
  bookmark the origin deleted, privatised, or moved off the copy's history is
  withdrawn, on the footing 0051's retired rules already have — and a bookmark
  that moved within the copy's history is rewritten, because the copy's
  `names/` is the origin's output there.
- `offer` gains `OfferKind::Name`, spelled `name`, listing every travelling
  bookmark file under `names/`. It is the one kind whose path is a name rather
  than an address, which is not an exception to 0048 so much as the one
  directory 0003's rule never covered: a bookmark's filename is its identity.
- `fetch` gains the kind, wants a name it does not hold, and never replaces
  one it does. What it declines is counted and said.
- `check`'s `names/` walk reads a `Bookmark`, so `MalformedBookmark` covers the
  second line and `DanglingBookmark` is unchanged.
- `name` gains `--private` and `--shared`; `names` prints the axis;
  `MalformedName`'s message states the grammar including the second line, and
  says a file it cannot read may have been written by a newer historica.
- The store listing in `store/mod.rs`, `HEADER_NOTE`, `FORMAT_NOTE` and the
  README's account of `names/` all describe one line and an optional second.

## Deferred

**The store-layout gate, for the third time.** 0051 said it: *this is the
second decision to want the store-layout gate 0045 deferred, and the second to
decline to design it. A third should build it.* This is the third and it
declines, which is the least defensible sentence in this document.

The failure is real and this decision does not invent it. An older historica
opening a store that holds a private bookmark refuses the whole store with
*that bookmark file is malformed*, which is a lie: the file is well-formed and
the reader is old. But the failure belongs to 0006's strict bookmark parser
rather than to the second line — a sixth key fails identically, and so does
every future bookmark spelling of any shape — so choosing the marker's
position neither causes it nor cures it.

What is genuinely new is the shape of the answer. The gate 0045 imagined was a
version dial, and 0047 has since spent the format's numbering: `historica` is
unnumbered and permanent, and *the grammar below it does not change*. So a
store-layout gate can no longer be a bigger number in an existing line. It
needs a place of its own, a rule about who writes it and when, and an account
of how 0004's *lowest version that expresses what it holds* survives in a
format with no versions — and that is three arguments, none of which is about
bookmarks. Building it inside this decision would be deciding it by
implication.

What is done instead is the error message, which is the whole of what a
grammar can do unaided: a bookmark whose first line reads and whose second
does not says so, and names a newer historica as the likely writer.

**Un-privatising, across replicas.** As 0051 deferred it, and for the same
reason: the join means a replica that has not heard puts the flag back. The
person must say it everywhere, and `name --shared` should say so where a
second replica exists. What would justify a better answer is the same thing
that would justify one for rules, which is somebody doing it often enough to
be maintaining the difference by hand.

**A private bookmark over unexported work.** The reachability test drops it
before the axis is consulted, so today the two rules cannot be told apart from
outside. That is fine while the target is a single revision and its ancestry.
It stops being fine if an export ever carries more than one head, since then a
person could reasonably want one head named and another not, and the axis
would be doing work the reachability test currently does for it.

**Whether the manifest should carry a mutable file at all.** Everything else
`offer` lists is immutable and named by the digest of its bytes, and the path
is an address precisely because no two stores have to agree about a filename.
A bookmark breaks both halves: its path is its name, and its bytes change
under a path that does not. It works, because a manifest is regenerated whole
and a fetcher hashes what arrives against the line that named it. But it is
the first entry whose digest is a fact about a moment rather than about a
thing, and a later decision that wants incremental publishing on a timer
should know that this is where the assumption first bent.
