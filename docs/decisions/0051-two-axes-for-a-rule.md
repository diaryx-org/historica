# 0051 — Two axes for a rule

0042 and 0045 disagree about what a `skip` rule is, and the disagreement is
one sentence each.

0042, listing what an export leaves behind:

> Not `names/`, not `skipped.txt`, not `cache/`: bookmarks and rules are the
> exporter's, and a cache is nobody's.

0045, refusing per-machine rules:

> 0011 puts the file in the store on the grounds that what a repository skips
> is a fact about the repository, the opposite of 0010's identity read
> backwards. Nothing here disturbs that.

Both cannot hold. `receive` unions every rule the source states into the
receiver; `export` writes a `skipped/` holding the note and nothing else. So
one rule is a fact about the repository when a replica arrives and a personal
effect when a copy leaves, and which one it is depends only on the direction
it was travelling.

The practical shape of that is a person exporting a repository for somebody
to work in. The copy has never heard of `skip target/`, so the first thing
the recipient's `record` does is offer to record their build output — the
failure 0011 wrote the rules to prevent, arriving because the rules did not.

The privacy the exclusion buys is not durable either. An export is a replica
and `receive` is its pull (0042), so a copy that meets its origin again
unions every withheld rule straight back in. The only party who can perform
that receive is one holding the origin store entire — a strictly larger
disclosure than the rules — and the party the exclusion actually withholds
from is the one who could do nothing with them but keep their own build
output out of a history. An exclusion that binds only where it is useless is
a gap, not a protection.

But 0042 was not wrong about everything, and the sentence it got right is the
one about privacy: `skip clients/acme-layoffs/` states, in its text, a fact
the copy should not carry, and no amount of the recipient needing
`skip target/` makes that line theirs to read. The two are not one kind of
thing.

So a rule has a second axis, and stating it turns out to require settling the
first. Whether a rule travels is orthogonal to what it matches, which means
the keys are a cross product, and a cross product can only be afforded if the
vocabulary on each side is small and closed. The matching side was neither:
three kinds that cannot say `draft-*.md`, one of which is subsumed by a
better spelling of itself. Both halves are here because neither can be priced
without the other.

## The decision

- **`private <path>` and `private <path>/`.** A rule that keeps a file out of
  history exactly as `skip` does, and whose own text does not appear in an
  export. Everything else about it is a rule: it is one file of
  `history/skipped/`, it unions on receive, and it is refused when it covers
  a path the tree holds.

- **A `skip` rule travels.** `export` writes a file for every shared rule the
  store states, into the `skipped/` it already builds. 0042's clause is
  superseded in the half that named rules; `names/` and `cache/` stay behind
  for the reasons 0042 gave them, which were never this one.

- **`skip-name <name>` and `skip-name <name>/`, where the value is one path
  component and `*` matches any run of characters in it.** Any run, including
  an empty one and including a leading dot, so `*.tmp` covers `.tmp` and
  `*` needs no companion rule for dotfiles. Without the trailing slash the
  value is matched against a file's own name, at any depth. With it, the
  value is matched against a directory's name, at any depth, and everything
  beneath that directory is skipped — the same parting `skip target` and
  `skip target/` already make.

- **`*` is the only metacharacter, and the value holds no `/`.** No `?`, no
  character classes, no `**`, no negation, and no escaping — a name that
  genuinely contains a star is spelled with `skip <path>`, which is exact, so
  the pattern never has to express a literal one. A value holding a `/` is
  refused, naming `skip <path>` as what spells a path.

- **A value that is only stars is refused.** `skip-name */` says *the whole
  folder*, which is a request `skip` already refuses when it is spelled as
  the repository root, and rules exist to name the exceptions.

- **`skip-suffix` is retired.** `skip-suffix .tmp` is `skip-name *.tmp`, with
  the same meaning it always had, since the old rule was already a match
  against the last component. The key is refused by name, and `check` reports
  a file still stating one, giving the new spelling.

- **Four keys, and the set closes.** `skip`, `skip-name`, and a `private`
  spelling of each. Every rule a person can state can be stated privately,
  and no combination is missing for a reason nobody can remember.

- **The label is what 0045 made it, and a collision takes the digest.**
  `private docs/` and `skip docs/` want one filename; the second to be
  written falls back to the digest of its own line. A value holding a `*`
  takes the digest too, because a star is a filename no Windows volume will
  carry and a shell will not leave alone.

- **`check` gains a finding where one path is covered both privately and
  shared**, naming both files, at error severity.

- **`export` reports what it held back.** A count of the rules carried and a
  count of the private rules not carried, on the same footing as the rest of
  what it says it did. A copy that quietly dropped rules is what this
  decision is fixing.

- **`skip --private <path>...` writes them**, and `skip` with no arguments
  prints each rule's kind beside the file stating it.

- **`receive` is unchanged.** Union by rule, matching on the rule. A private
  rule and its shared twin are two rules, so a union meeting both keeps both
  — which is the failure `check` now names, arrived at honestly.

## Why a key and not a flag on a rule

The obvious spelling of the travel axis is a rule that carries a privacy bit.
It is the wrong one, and the reason is the reason 0045 exists.

A bit is a second fact per rule, and a second fact has to merge. Consider one
rule held private on the laptop and shared on the desktop. Union — the
operation every other set in this store uses — has no answer: it must either
take the shared reading, which leaks a rule somebody marked private, or
define privacy as winning, which is a precedence rule inside the one
container 0045 spent a whole decision making order-free. The first fails in
the direction this design never fails in. The second is a tie-break, and a
tie-break is what a set is for not having.

A key cannot disagree with itself. `skip x` and `private x` are two rules
that union like any other two, and the state where both are present is not an
ambiguity to resolve but a contradiction a person wrote, in two files, either
of which they can delete. That is the difference between a merge policy and a
`check` finding, and this project has taken the second every time it could.

## Why the boundary is export and not receive

Privacy needs a boundary, and there are only two places a rule crosses one.

`receive` reads a store directory. Whoever can run it already holds the whole
history, the whole rule set, and every payload — the maximal disclosure this
format has. A rule crossing that boundary tells the recipient nothing they
could not read for themselves, which is why private rules union across a
person's own machines exactly as shared ones do. That is not a concession; it
is the feature. The journal on the laptop and the journal on the desktop skip
`therapy/` because the rule reached both, and the person stated it once.

`export` is the only artifact this design deliberately builds *smaller* than
the store. It is assembled rather than mirrored, precisely so that what a
stranger receives is a decision rather than a directory. That makes it the
one edge across which a rule's text is a disclosure, and one edge is what a
travel axis needs: a distinction the transport already makes, rather than a
vocabulary the store would have to invent.

## Why the pattern stops at the component

`Skipped`'s own doc comment says what this decision has to answer for:

> Two keys, and deliberately no pattern language: decision 0011 argues that
> the part people get wrong about gitignore is never the pattern but which of
> five files won.

Read it exactly. The part people get wrong is *not the pattern* — it is
precedence, and 0045 found that precedence lived in the container rather than
in the matching. A star inside one component introduces no file that can win
over another, no order, no negation, and nothing a second reader could
resolve differently. The set stays a set. What 0011 refused, and what this
still refuses, is a language in which two rules can argue.

The danger in a glob is not `*`. It is `/`. Every dialect quarrel worth
having is about separators — whether a star crosses one, whether `**` is a
different thing, whether `docs/*` reaches `docs/a/b`, how a character class
interacts with a boundary — and each of those is a compatibility surface for
a format meant to be re-implemented from its spec by somebody who never met
this code. Forbid `/` in the value and every one of those questions stops
existing. What remains is a matcher a stranger writes in ten lines and gets
right, which is the standard 0004 holds every other part of this format to.

That is also the answer to the vocabulary this decision could have had
instead. A `skip-prefix` beside `skip-suffix` is the obvious pair, and it
fails twice: the word is already taken, since `skip docs/` *is* a path
prefix and a second meaning in a four-key vocabulary is one the reader has to
disambiguate every time; and prefix, suffix and name together are three keys
that still cannot say `draft-*.md`, `~$*.docx`, or any of the editor
droppings that are decorated at both ends. Three keys and a remaining gap is
the bad end of the trade. One pattern key is fewer keys, no gap of that
shape, and a syntax people already read correctly.

## What a rule can and cannot keep out

The ceiling on the travel axis is worth stating outright, because `private`
will otherwise be read as a protection it is not.

**An export carries operation documents and payloads verbatim, and a
revision's ID is the SHA-256 of its own bytes.** So no rule can filter
recorded content out of a copy. Doing it would mean rewriting the documents
that name the file, which changes their digests, which changes the revisions
above them — and the copy would stop being a replica of its origin, taking
0042's best property with it: *an export is a replica, so `receive` is its
pull*. Clone and pull are one design only for as long as the copy's digests
are the origin's.

So `private` is a rule about a rule. It changes exactly one thing — whether
the line naming a path appears in the copy — and it changes nothing about
content, because content a rule covers was never recorded and so was never a
candidate for the copy. 0042 built that guarantee by construction rather than
by filtering, and it is unaffected here.

The corollary is the trap. A `private` line over a path already in the tree
protects nothing, because the content is in history and a rule cannot reach
backwards. That state is already refused — `record` stops, and `check` names
the rule file (0045) — and the message should name `forget` as what removes
recorded content, since a person reaching for `private` on a tracked path has
asked the wrong tool and there is a right one.

## The one way this fails

Both spellings of one path, in one store. It happens two ways: a person
writes both, or a receive meets a replica that spelled it the other way.

The consequence is that the shared rule travels, so the path is named in the
copy, and the private rule accomplished nothing. Privacy is defeated by
addition, which is the failure mode a union has to be watched for — every
other contradiction this format holds is resolved by taking both, and taking
both is exactly what breaks this one.

It is an error rather than a note. `check`'s notes are for states that are
merely untidy — two files stating one rule, in 0045's list — and this one has
a stated intention on one side and a leak on the other. The fix is deleting
one file, and the finding can name both files and the path, so the person
chooses which of the two things they meant.

This is also the whole of the argument for keeping the contradiction
possible. A grammar that refused to hold both would have to refuse it at
receive, which means refusing a rule a replica legitimately states, which is
the manufactured conflict 0045 removed.

## Rejected alternatives

**A separate `history/private/` directory.** Mechanically the cheapest
version — export copies one directory and not the other, with no reading. It
is refused because it puts a rule's identity in its path, and 0045 is
explicit that the filename is a label and the content is the rule: *the
reader never parses a name*. A private rule filed by hand into the wrong
directory would mean something other than what it says, and 0045's whole
answer to "which file states this?" would need a second half.

**Keeping `skip-suffix` beside `skip-name`.** Two spellings of one meaning,
which is the redundancy every other decision here has refused, and the older
one is the weaker: it can say `*.tmp` and nothing else. The migration is one
error message naming the new spelling, which is 0047's treatment of the
numbered preambles and 0045's of `skipped.txt`. This library is young enough
that the number of stores holding a `skip-suffix` is small and the number
holding one somebody would mourn is smaller.

**Globs with separators.** Above: the dialect surface is the separator, and
the cost lands on every future re-implementer rather than on the person
adding the key. There is a second cost, which is that a pattern crossing `/`
makes pruning a structural question — 0039 depends on being able to say
whether a rule keeps a whole directory out, and a component match answers
that by matching one component while `docs/**/tmp*` requires reasoning about
the pattern's shape. And patterns invite negation the way nothing else does,
which the set cannot have.

**Audience keys — `private:work clients/`, and `export --as work`.** As a set
this works: the audience is part of the rule's identity, so union needs no
tie-break, and it is the natural generalisation of what is decided here. It
is refused on two counts. The first is that adding an audience silently
changes what every rule that does not mention it means — `export --as
clients` ships every `private:work` rule unless the tagging was exhaustive,
so the meaning of an old rule depends on a word invented later. That is
0011's gitignore complaint in its true form, precedence rather than pattern,
and it fails in the leak direction. The second is that there is nothing to
anchor the vocabulary to. 0033 can normalise a path because a path names
something on disk; nothing can tell a person that the `work` on this machine
and the `Work` on that one were meant to be one audience. Two tiers earn
their place by matching a distinction the transport already makes. A third
would be a vocabulary the store cannot check.

**Rules that filter recorded history on the way out.** Above: it costs
replica identity, and what it wants is `forget`.

**A size threshold — `skip-over 10M`.** The one candidate whose meaning
changes without anybody editing it: a file crosses the line and a rule that
did not cover it now does. Every other rule here is a fact about a name.
Deferred rather than refused, since the failure is at least loud — a rule
newly covering a tracked file is the error 0045 already built — but a rule
whose reading depends on the state of the disk is a different animal.

**`private` for paths only.** The argument was that a suffix names no path
and so discloses nothing. It does not survive `skip-name`, whose value is a
name a person chose and is as revealing as any path. Orthogonal is one field
in the reader and one sentence in the grammar; the exception was two.

## Consequences

- `Rule` stops being three flat variants and becomes a scope beside a flag
  saying whether the rule travels. The scope is the grammar's two values
  times its two forms: an exact path, a path and everything under it, a name,
  and a name and everything under it.
- A `Pattern` is the new small type — parse, which refuses a `/` and a value
  of only stars, a match against one component, and a `Display` that
  round-trips. Values are NFC on the way in as every other path is (0033),
  and matching is case-sensitive as everything else here is.
- Rule equality includes the flag, which is what makes a private rule and its
  shared twin two rules to `Skipped::stated`, to `receive`'s union, and to
  `skip`'s already-held check. `Rule` is public, so the implementing commit
  carries a `Behavioural-change:` trailer, and so does the retirement of
  `skip-suffix`.
- `Skipped::skips_directory` learns the name-and-under scope, matching the
  directory's own name, so 0039 keeps being able to tell "no such path" from
  "a rule keeps that path out".
- `Rule::label` gains the name scopes, mirroring the directory convention —
  `skip-name drafts/` at `name drafts/all.txt`, `skip-name notes.md` at
  `name notes.md.txt` — and `spellable` refuses a `*`, which is a character
  `naming::scrubbed` passes through untouched today.
- `export` writes the shared rules beside the note, and what the command
  prints carries the two counts.
- `check` gains two findings: one path covered both privately and shared, and
  a file still stating `skip-suffix`. Both are errors, and both name the file
  and the spelling that replaces it.
- `skip` gains `--private`, and its no-argument listing prints the kind.
- The store listing in `store/mod.rs`, `SKIPPED_NOTE`, and the README's
  account of `history/skipped/` all describe four keys and two axes.

## Deferred

**A pattern scoped to a subtree.** `docs/**/*.tmp` is unreachable: a rule can
name a subtree or a pattern, never both. That combination is exactly what
costs the separator dialect, and the workaround is an exact `skip
docs/drafts/`. What would justify revisiting is the scoped form being the one
people actually reach for, and it should be revisited knowing what it buys.

**Audiences.** Above. What would justify revisiting is somebody exporting to
two audiences often enough to be maintaining the difference by hand, and a
proposal for where the vocabulary lives that `check` can hold to.

**Un-privatising a rule.** Turning `private x` into `skip x` is deleting one
file and writing another, and a replica that has not heard yet will union the
private one back — 0045's resurrection, in the direction that is safe here,
since the rule that comes back keeps a path out of a copy. The person must
say it on every replica, and the error message should say so.

**A size threshold.** Above.

**Whether a new key is a format change.** An unknown key is refused (0011),
so every key added here makes an older historica refuse a store that uses
one — the safe direction, and the reason the key set is declared closed
rather than left open. What it is not is a *document* grammar change, and
`historica.txt` states the highest document version a store holds, so there
is nothing today for a reader to consult to learn why it cannot read a rule
file it can plainly see. This is the second decision to want the store-layout
gate 0045 deferred, and the second to decline to design it. A third should
build it.

## Since

0062 was the third and declined. 0069 is the fourth, and it splits the
question this decision asked: the *space* for a gate is reserved at 1.0,
because a reader shipped without one can never be given one, while what the
gate says and who writes it stay deferred for the change that needs them.
