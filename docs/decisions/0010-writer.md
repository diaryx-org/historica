# 0010 — What a writer must supply

Every fact in a revision document comes from somewhere. Parents come from the
history, the tree facts from what a person did to the file set (0008), the
operations from the file they edited (0009), and the message from what they
typed. Three come from nowhere: the change ID, the author, and the time.
Nothing in a store can derive them, and until they are decided there is no
writer — which is why `diff` exists and `record` does not.

## The decision

- **A change ID is 96 bits from the operating system's random source**, minted
  when a person records work that is not a version of work already recorded,
  and copied by every later revision of that change.
- **An author is stated in configuration and never guessed** — the person's own
  configuration, per path and never per repository. A writer with no author
  refuses to record and says which file to write and what to put in it.
- **A time is the system clock at the moment of recording**, spelled in the
  offset the platform reports for that instant.

And the rule the three of them share:

> Only a human act introduces fresh randomness, a fresh clock reading, or a new
> claim about a person. A rewrite the tool performs on its own behalf derives
> all three from what it is rewriting.

That last rule is not decoration. Decision 0002 promises that two replicas
which independently rebase one change onto one parent write *one file*, and a
writer that stamped every rebase with its own clock would break that promise
in the ordinary case of two people pulling an amended ancestor.

## Minting a change ID

Decision 0001 fixed everything about the identifier except where the bits come
from: 96 of them, assigned rather than derived, spelled in `k`–`z`. They come
from the operating system, one call per mint, and nothing about the draw is
remembered.

Keeping no state is the part worth stating. Decision 0003 makes sync "union by
copy" — a store travels by being copied wholesale, and so does a working
directory copied to a second machine. Any seeded generator whose state lived
beside the history would therefore be duplicated by the ordinary way these
repositories move, and both copies would mint the same identifiers from then
on. Asking the operating system every time is the only source with no state to
duplicate.

Change IDs are not a security boundary — 0001 and 0005 both say so — but that
argument is about what a *reader* may conclude from one, not about how it is
drawn. Accidental collision is the risk, so the draw must be uniform over all
2^96 values, which the platform's random source is and a clock, a counter, or a
process ID is not.

If the random source fails, recording fails and says so. There is no weaker
source to fall back to, and a fallback would be exactly the kind of invisible
difference in provenance this project spends its effort avoiding.

Which acts mint, and which copy:

| The act | Change ID | `author` / `when` | `revised` |
| --- | --- | --- | --- |
| Recording new work | minted | recorder, now | — |
| Recording a merge | minted | recorder, now | — |
| Amending or rewording | copied | copied | recorder, now |
| Moving a change elsewhere | copied | copied | recorder, now |
| Carried along by an ancestor | copied | copied | from the cause |

A merge mints because a merge is a human act: somebody decided that two lines
of work belong together. Two people who merge the same two heads therefore
produce two merges, which is not a flaw to design away — it is what happened.

## Stating an author

Decision 0005 settled what an `author` line means: a claim, copied into every
revision of the change, verified by nothing. A writer cannot make it evidence.
What it can do is make sure the claim is the person's own, which is the whole
of this section.

The author comes from the first of these that says anything:

1. `HISTORICA_AUTHOR`, for scripts, tests, and machines where a file is
   inconvenient.
2. An identity file in the platform's configuration directory —
   `$XDG_CONFIG_HOME/historica/identity`, defaulting to
   `~/.config/historica/identity`, and `%APPDATA%\historica\identity` on
   Windows. All three are reachable through `std::env`, so this costs no
   dependency.

The file holds header-shaped lines, the grammar `names/` already uses: a key,
one space, a value to the end of the line. A blank line starts a new block, and
a block headed by `under` applies to the repositories beneath one directory.

```console
$ cat ~/.config/historica/identity
author Adam Harris <adam@example.com>

under ~/work/
author Adam Harris <adam@company.example>
```

Blocks exist so that a path and a name never share a line. This format has no
quoting anywhere — 0002 spends a paragraph on why — and a directory may hold a
space, so the two facts get a line each. The first block heads nothing and is
the default; a later one names a directory, and the longest matching prefix
wins, compared by path component against the canonical path of the directory
holding the store, so `~/work` matches `~/work/journal` and never `~/workshop`.
Two blocks claiming one directory are an error naming the line.

It is read the way a bookmark is read (0006) rather than the way a revision is
read, because nothing here is named by a digest of its bytes and a second
spelling cannot mint a second identity. An unknown key is still an error naming
the line: in a file this small, `autor` is a typo to report, not a fact to
ignore. A value the revision format would refuse — empty, padded, holding a
control character — is refused here instead, where the message can name a file
a person can edit rather than a line in a document they never typed.

**Nothing is guessed.** Git falls back to a name from the account and an
address from the hostname, and the result is thousands of commits authored by
`adam@Adams-MacBook-Pro.local`. Here that mistake is worse in three ways: 0005
copies the author forward into every later revision of the change, so a guess
made once is repeated for as long as the change is worked on; the guess is
covered by every one of those digests, so correcting it rewrites history rather
than editing a field; and the line is a claim about a *person*, which is not a
thing to invent on their behalf. Refusing costs one line of configuration,
once. `historica identity "Adam Harris <adam@example.com>"` writes it, so the
refusal can name a command rather than a paragraph.

**Identity is per-person and per-path, never per-repository.** One person may
keep a journal under one name and contribute to a shared repository under
another, which is the case the `under` blocks answer — and they answer it from
the personal file rather than from a file beside the store, because a file
beside the store travels. A store moves by being copied (0003), and so does the
folder holding it; an identity that travelled with it would arrive on someone
else's machine and record *as its owner*, silently, since 0005 makes the author
a claim nothing verifies. Misattribution is a worse failure than inconvenience.

The cost is that a folder does not say which name it will be recorded under.
That is the right side of the trade: which name a person writes under is a fact
about the person, not about the work, and it becomes visible in the revision
the moment one is recorded.

Reading the author out of `~/.gitconfig` is rejected for a smaller reason: it
would make Historica's claim depend on another tool's configuration, invisible
from any file this project defines.

`revised-by` follows 0005 unchanged: it is the recorder, written only when it
differs from `author`, because a fact equal to another fact is a second
spelling of it.

## Spelling a time

`when` is **the moment the change was first recorded**, which answers decision
0005's first open question. It is not the moment work began, because a writer
cannot know that — a journal entry written on Sunday may describe Thursday —
and the fact a tool can state truthfully is the one it should state. A person
who wants to say when something happened writes it in the message, where
nothing interprets it. Since 0005 copies `when` forward, an amended revision
keeps the moment its change was first recorded, and `revised` carries the later
act.

The instant is the system clock. Nothing refuses it: 0005 already declines to
require `revised` to be later than `when`, on the ground that no timestamp
participates in identity, causality, or ordering, and a clock that is wrong
misleads a reader without misleading the model.

The front end says something, though, because one wrong clock is worth
catching. A machine with no battery or no network says 1970, and 0005 copies
that into every later revision of the change, so a person can accumulate a year
of entries filed under a date that has not been true for half a century. When
the instant being recorded is earlier than the newest `when` the store already
holds, `record` warns and records anyway. Machines that talk to a time server
agree within seconds, so this fires on a clock that is genuinely broken; when
it fires because somebody *else's* clock is broken, it is still saying
something true about the history. The comparison is the front end's, on the
same terms as the one `historica log` already makes — presentation may order
timestamps, and the writer may not.

The offset is the one the platform reports for that instant, so a person who
writes at seven in the evening has an entry dated that evening, in June and in
December alike. This is the fact `arrange` renders into a filename — 0006 calls
it "the date the person experienced" — and a fixed offset written down once
would be wrong for half of every year everywhere daylight saving applies. When
the platform cannot say what its offset is, the answer is `+00:00`, which is
the format's spelling of UTC and never `Z` or `-00:00`.

The instant and the offset arrive together from one call, and the format's
spelling is what that call formats to: a `Zoned::now()` rendered
`%Y-%m-%dT%H:%M:%S%:z` is `2026-08-20T00:00:08-07:00`, and on a machine whose
zone cannot be resolved it is `2026-08-20T07:00:09+00:00`. The fallback to UTC
is the library's own behaviour rather than something Historica arranges around
it.

Seconds are truncated, never rounded: the format has no fractional seconds, and
rounding would move a recording across a minute, an hour, or a day boundary for
no reason a reader could see. A leap second cannot arrive, because Unix time
has none to offer and the parser would refuse `:60` if it did.

## A mechanical rewrite states no fresh facts

Decision 0002 argues that canonical bytes exist so that two replicas which
"independently rebase the same change onto the same new parent — which is
exactly what happens when both sides pull an amended ancestor" — produce one
revision that merges by union, rather than a divergence created by nothing but
two machines disagreeing about spelling.

A rebase records `supersedes`, and 0002 requires `revised` wherever
`supersedes` appears. If that timestamp were the rebasing machine's clock, the
two replicas would write two files differing in one field that means nothing,
and the person would be asked to resolve a divergence created by nothing but
two machines disagreeing about the second — the complaint 0002 makes, one layer
up.

So a rebase copies rather than stamps. The revision it produces carries:

- the same `change`, `author`, and `when` as the revision it supersedes, which
  0005 already requires;
- `revised` and `revised-by` **from the rewrite that caused it** — the new
  parent's own `revised` and, where the parent states one, `revised-by`,
  falling back to that parent's `author`, and omitted entirely when it equals
  this revision's `author`.

Moving a change onto a parent nobody rewrote — "put this on top of the other
line of work" — is not that act. There is no causing rewrite to take a time
from, and nothing happened that a person did not ask for, so it stamps like an
amendment does. The line is not who typed a command but whether the revision
could have been produced without anyone deciding anything: a descendant carried
along by an amendment could, and a change moved somewhere new could not.

The new parent of a carried-along revision is a rewrite, so it carries
`supersedes` and therefore carries `revised`: the value always exists. And it
reads truthfully. Such a descendant was not revised by whoever's machine
noticed first; it was revised by the act that rewrote its ancestor, at the
moment of that act. Every descendant down the line inherits the same pair, so
an amendment and the rebases it forces are legible as one event, which is what
they are.

Where such a revision has more than one rewritten parent — a merge whose sides
were both amended — the pair comes from the parent with the greater digest, and
the timestamps are not consulted.

The obvious rule is the later of the two `revised` instants, and it is rejected
on purpose. It would mean the writer parsing two offsets and ordering two
clocks, which is the one capability three decisions have each refused to grant,
and refusing it in prose while granting it in code is how a rule stops being
visible. Digest order is what every other tie in this format is broken by, it
needs no new sentence to justify, and it costs a rendering only in the rare
case where the earlier of two amendments is the one credited — with both
amendments still plainly in the graph for anyone reading.

That draws a line worth stating outright. **Comparison of timestamps lives in
presentation and never in the model.** `historica log` already breaks ties
among concurrent revisions by `when` as spelled, deliberately and with a note
saying so, because a rendering that reorders itself misleads nobody about
history. A writer producing bytes has no such licence.

`tests/corpus/revisions/06-rebased.rev` stamps a rebase two seconds after the
amendment that forced it, because it was hand-written before this decision
existed. It stays as it is, and a test says in these words that this writer
would have copied the amendment's `revised` instead — the same treatment 0009
gave 0007's replacement anchoring. The corpus pins what a parser must accept,
and a writer producing a narrower set of documents than the parser accepts is
the normal relationship between the two.

## The clock and the random source are inputs

Both enter the writer as values a caller supplies, defaulting to the platform.
This is not testing ceremony: a property test that mints identifiers has to be
reproducible when it fails, and a corpus that pins a writer's bytes cannot be
generated by something that reads a clock. It also keeps the two impure things
in this project in one place small enough to read.

## Rejected alternatives

**Time-ordered identifiers** — UUIDv7, ULID. They put a clock inside an
identifier that decisions 0001 and 0002 keep clocks out of, they tell anyone
holding a change ID when the work happened, and they invite tools to sort by
them, which produces an order that looks like causality and is not.

**Deriving a change ID from content.** Rejected by 0001 and repeated here
because it is the first thing a reader of a content-addressed format reaches
for: a derived identifier changes when the thing it derives from is rewritten,
and rewriting is what change IDs exist to survive.

**A seeded generator, with its state in the store.** Above: stores travel by
being copied, so the state travels too.

**Prompting for an author on first record.** A writer that asks questions
cannot be scripted, and the file it would be asking about is one command away.

**A configured UTC offset.** Above: wrong half the year, and wrong silently.

**A monotonic or logical clock in `when`.** Ordering is the graph's job, and a
field that looked like an ordering would be read as one.

**An identity file beside the store.** Above: it would travel with the history
and record as its owner on someone else's machine.

**Refusing a clock that disagrees with the store.** Warning is the whole of
what is warranted. A refusal would make a timestamp participate in validity,
which is the weight three decisions have denied it, and would turn away
legitimate history from a machine whose clock is merely wrong — including
history recorded by somebody whose clock was right and whose colleague's was
not.

## Consequences

- `Cargo.toml` gains its third and fourth dependencies: `getrandom` 0.4
  (MIT or Apache-2.0, MSRV 1.85, bringing `cfg-if` and `libc`) and `jiff` 0.2
  (Unlicense or MIT, MSRV 1.70, bringing `jiff-core`, and on Windows a bundled
  tz database and `windows-link`). Both are compatible with this project's
  MIT-or-Apache. Neither is needed to *read* a store: a history already written
  does not care what produced it, which is the same line 0009 drew around
  `similar`.
- What makes a dependency necessary in each case is `#![forbid(unsafe_code)]`.
  A random source and a timezone are operating-system facts reached through an
  operating-system call, and this crate makes none of its own.
- `src/` gains a writer module that mints, stamps, and composes a
  `RevisionDocument`, and the store gains no new file: an identity lives with
  the person, not with the history, because a store copied to a second machine
  must not carry the first machine's owner.
- Four tests are owed and are the ones worth naming. Two machines rebasing one
  change onto one rewritten parent write byte-identical documents — the claim
  0002 makes and this document keeps. A merge carried along by two amendments
  takes its pair from the greater digest, whichever amendment came first by the
  clock. A writer with no author refuses, and the message names the file and
  the line. And a revision composed from a fixed clock and a fixed draw is
  byte-identical to the corpus file that pins it, which is what makes the
  writer testable at all.
- 0005's first open question is answered. 0002's rebase convergence claim
  acquires the rule that makes it true.
- The front end owes `historica record`, `historica identity` — which writes a
  block rather than a line, so a second identity costs no hand-editing — and
  the clock warning above, which belongs beside `log`'s tie-break as the second
  place a timestamp may be compared.

## Signatures, and what they can attest

Signatures are a later decision, but two things about them are settled by rules
that already exist, and a writer built now should not contradict either.

**The shape is nearly forced.** A signature covers bytes, and 0002 established
that a revision cannot state its own digest, because the digest covers the
file. A `signed-by` header fails for the same reason twice over: signing
changes the bytes, which changes what was signed. So a signature is a detached
document naming a revision's digest — a third document type in the store,
content-addressed, append-only, unioning by copy like everything else, and
costing the revision grammar nothing.

**Deterministic rebase is the precondition.** This was not the reason for the
rule above, and it is the best evidence for it. A signature over a revision is
worthless to a replica that would have produced a different revision from the
same inputs: two machines rebasing one change onto one rewritten parent would
hold two files, one signature, and no way to check the other. Because a
carried-along rebase now derives every fact from its cause, both machines hold
one file, and a signature over it is valid on both. Signing survives automatic
rebase only in a format where automatic rebase converges.

What a signature will not be able to say is worth writing down before anyone
expects it. A signature attests that a key produced these bytes. `author` is
copied forward, so a reviewer's signature on an amended revision attests the
reviewer's bytes and says nothing about whether the author line is true.
**Signed history verifies revisions; it never verifies changes** — the same
boundary 0001 drew around change IDs, arriving one layer up.

## Deferred

**Binding a key to an author.** A signature needs a key, and a key needs to be
bound to something a revision states, which is the moment `author` stops being
free text. That is decision 0005's second open question — whether an author is
a line or a structured identity — reached from the other direction, and the two
should be answered in one document rather than separately.

**What a working copy is.** Which files a repository tracks, where they live,
and what is recorded when several changed at once. This document decides what a
writer supplies; the next one decides what it is given.
