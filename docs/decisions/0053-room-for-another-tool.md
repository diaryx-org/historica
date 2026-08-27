# 0053 — Room for another tool

0046 gave two directory names away and promised tolerance for the rest:

> a directory at the store root that Historica does not name belongs to
> whichever tool wrote it, and `claims/` and `trust/` are reserved for this
> one.

That sentence does more work than it looks like, and it is short by exactly
one clause. Tolerance is enough while nothing moves: `check` walks the
directories it names and says nothing about the others, and a folder sitting
still asks no further question. The question arrives when the store crosses a
boundary. `receive` reads one store into another and `export` assembles a
third, and each has to decide what becomes of a directory whose grammar
historica has refused to learn.

0046 decided that twice, in opposite directions, without noticing it was one
question. Trust never travels, argued at length and correctly. Claims travel
"by the file sync or copy that already moves stores", which is to say they
travel by not being historica's problem — true of `cp -r`, and false of the
one transport this design builds itself. So `export` carries neither, and
0046 filed the gap under Deferred, waiting on "the tool existing, and on
deciding whose claims an exporter is entitled to ship".

The tool exists. historica-minisign writes claims and reads `trust/`, and a
second tool — historica-git — is already written against the boundary from
the other side. Paying the deferral now means answering the general question
rather than the particular one, because a third tool will not ask permission
before it puts a directory at the root.

The shape of the answer is that a reservation is not just a name. **A
reservation declares how the directory travels**, and export and receive act
on that declaration rather than on which tool wrote it. Three classes cover
everything anybody has actually built.

## The decision

- **A reserved directory at the store root declares its travel class, and
  transport acts on the class.** `export` and `receive` never learn a tool's
  name, a tool's grammar, or a tool's file naming. They ask one question of a
  directory — how does this travel — and the registry answers it.

- **`travels-and-unions`: immutable, digest-named files that cross a store
  boundary freely.** `export` carries the directory into the copy; `receive`
  unions it, add-only, with `create_new` semantics and a name already taken
  left exactly as it is. This is 0003's concurrency story applied to files
  historica cannot read: an immutable digest-named file needs no merge rule,
  because two stores that hold one name hold one file. **`claims/` is this
  class**, which retires 0046's deferred item.

- **`local-only`: never crosses a store boundary, in either direction, by any
  operation.** Not carried out by `export`, not read in by `receive`, not
  listed by anything. **`trust/` is this class**, on 0046's argument
  unchanged: a claim is a fact and trust is an opinion, and the judgment file
  is the one thing in a store another store must never write.

- **`derived`: nobody's, never travels, deletable without loss.**
  **`cache/` is historica's own**, so the class is a description of something
  already here rather than a slot invented for symmetry. What parts it from
  `local-only` is not where it goes — neither goes anywhere — but what its
  absence costs, which is time and never information.

- **A directory nobody reserved is `local-only`, and that is the default
  rather than a refusal.** An unclassified directory is somebody's, this
  store does not know whose, and the two ways to be wrong are not
  symmetrical: leaving it behind costs a copy something it can be given
  again, and carrying it discloses a file nobody said could travel. 0011's
  test, in 0045's words — between an exact answer that can fail either way
  and an inexact one that can only fail the recoverable way, this project has
  chosen the second every time.

- **A new reservation is a decision document and a line in the registry, and
  it is asked for when a tool exists that wants it.** Not a namespace handed
  out in advance, not a prefix convention, not a manifest a tool writes into
  the store. The registry is short because the argument for each entry is
  written down, and 0045's discipline is what keeps it short: need first.

- **`export` carries a travelling directory whole.** Not the subset naming
  revisions the copy holds. The argument is below, and its short form is that
  the filter cannot be written without historica learning a grammar 0046
  spent a decision refusing.

- **`receive` adds and never overwrites.** A file whose name the receiver
  already holds is left untouched and not read, which parts this from
  `write_once`: that helper confirms the bytes because the name is a digest
  historica computed, and here the name is a digest *somebody else* computed
  under a rule historica has not read. Add-only is a promise that can be kept
  without knowing what the rule was.

- **The reservation above is the only special case in the store, and the rest
  of the plugin surface is the Rust API.** A side tool is an ordinary crate
  depending on `historica` at a semver range from crates.io. There is no
  plugin registry, no ABI, no manifest, no discovery, and nothing to install.
  historica-git already works this way and historica-minisign needs nothing from
  the API at all.

- **A fact the API does not expose is a change to historica, not a hole
  opened elsewhere.** historica-git's 0001 states this as a rule it holds
  itself to; this decision promises the other end of it. An extension that
  needs something waits for a version of historica that exposes it — with a
  version number on it, and a decision document behind it where it touches
  the format — rather than reaching through a workspace, a fork, or a
  `pub(crate)` somebody left open.

- **The store is written by historica, except inside a directory reserved to
  the tool.** historica-git's 0001 says "and by nothing else", which is right
  for every directory historica reads and one clause too strong for the two
  it does not. A reserved directory is the reserving tool's to write, by
  hand, with `create_new`, and what makes that safe rather than a licence is
  the class: historica knows how the files travel without knowing what they
  say.

- **An extension point historica itself must call arrives as a trait, one
  decision each, need-first.** `Filesystem` is the
  precedent and the shape — 0025's smallest set of operations anything
  actually performs, with the capabilities a host may decline defaulted so
  that declining costs time and never an answer. 0048's one-method source is
  the second. 0046's enforcement at receive would be the third, on the day
  somebody meets the need in practice.

- **Subprocess dispatch is not a plugin mechanism here.** 0025 exists because
  the folder may be an iCloud document provider or an Android content URI,
  reached by an application that is not a shell and has no `PATH`. A
  mechanism built on spawning a process works on a desktop and nowhere else,
  which would make every embedding host a second-class one and quietly
  relocate this format's centre of gravity to the command line it was
  deliberately not built around.

- **An executable hook inside the store is refused outright.** A store
  travels by `cp -r` (0029), by an assembled copy (0042), and by a fetch from
  a URL a stranger published (0048, 0052). A script in a directory that
  travels is arbitrary code arriving with somebody's history and running by
  the act of opening it. The store walk already refuses to *follow* a
  symbolic link for the smaller version of this reason (0040), and 0034
  carries one mode bit for the folder rather than for the store. Whatever
  else a store is, it is not a thing that runs.

## Whole, or only the claims that name what travelled

This is the genuine tension, and both answers cost something.

An export is the one artifact this design builds deliberately smaller than
the store (0051), so a directory copied into it whole is the shape that
decision is suspicious of. `claims/` holds files naming revision digests, and
a claim over a revision the export left behind — an unexported branch, a
revision the target predates — puts a digest into the copy for something the
recipient cannot fetch and was not offered. The narrow export is exactly the
case where the exporter meant to hand over less.

Three things settle it against the filter.

**The filter cannot be written without a grammar.** Deciding which claims
name exported revisions means parsing claim files, and 0046's first bullet is
that historica gains no grammar — stated in the same breath as the
reservation it is now being asked to qualify. Worse, it would not be *a*
grammar but this tool's: the next reserved travelling directory would need
its own parser, the class would decay into a table of per-tool special cases,
and the thing this decision exists to establish would be gone. Contrast
`skipped/`, which `export` genuinely does filter (0051) — and can, precisely
because historica reads that grammar, owns it, and answers for it in `check`.
A filter is available for a directory historica reads. It is not available
for one it has promised not to.

**The filter drops the claims most worth having.** 0046 makes one claim over
one revision cover its whole ancestry, because a digest pins bytes which pin
parents' digests to the roots. So the claim that vouches for an exported
history is very often a claim over a *later* head — the one the exporter
signs habitually, naming a revision the export deliberately ends before. A
filter keyed on "names a revision in the exported set" throws away the
signature covering the set, keeps the incidental ones, and leaves the copy
looking vouched-for in the least useful way. The obvious filter is not merely
expensive; it is close to backwards.

**Digest disclosure is already priced into the format.** A forgetting
document travels always (0014) and states `forgets <digest>`, naming bytes
that were destroyed on purpose — so an export already carries the name of a
thing nobody can fetch. A revision's `supersedes` line may name a revision
outside the closure, which `export`'s own module documentation calls the
ordinary condition rather than a fault, and `check` has no finding for it.
An export is *already* a store holding digests of revisions it does not have.
A claim adds a key, a role, and a moment to that, all of them facts the
signer stated about their own work, in a directory built to travel with
copies of a store they knew would be copied.

What the whole copy genuinely costs is worth saying plainly rather than
arguing away: an export of a narrow target discloses roughly how much other
history exists and when it was vouched for. That is a shape, not a content,
it is strictly less than the `cp -r` that 0029 declines to replace already
gives away, and the escape from it is a second reservation with a different
class — which is a decision somebody can write when they want one — rather
than a parser historica should never have.

## Why a plugin is a crate

The second half of this decision looks like it is about mechanism and is
about who answers for what.

Every plugin system that dispatches to a process, a dynamic library, or a
sandboxed module is a system in which the host cannot say what its own
invariants are. `check` is historica's invariant to hold, and a hook that
runs between reading a store and believing it makes that sentence untrue —
not because the hook is malicious, but because "does this store pass check"
would stop having one answer. A Rust crate calling a published API has the
opposite property: everything the extension can do is something a caller
could already do, in a version somebody chose, against a surface with a
number on it.

The cost is real and small. A side tool has to be written in Rust or reach
the API through a binding, and a person who wants one has to install a second
program. Set against that: historica-minisign's whole implementation is minisign
and text files, and any of it can be done by hand with two commands that are
neither tool. That is the test 0046 set, and a plugin surface that made the
tool harder to write than the by-hand version would have failed it.

## Rejected alternatives

**Filtering `claims/` to the exported ancestry.** Above, at length: a parser
in historica, a class that decays into per-tool cases, and a filter that
discards the covering claim while keeping the incidental ones.

**`export --claims`, opt-in.** It puts the copy's contents at the mercy of
what somebody remembered to type, and the forgetful direction is the silent
one — a copy shipped without vouching looks exactly like a copy that was
never vouched for. 0042 built the export so that what a stranger receives is
a decision made once, by construction. A flag is that decision made again,
badly, every time.

**A per-tool travel rule rather than a class.** `claims/` is carried because
it is claims. It is the same code and one worse idea: the registry would grow
a policy per entry rather than a classification, nothing could be reasoned
about without reading every entry, and the second tool to want what
historica-minisign has would arrive as a patch to a match arm instead of a line
in a table.

**A manifest inside the store declaring the tool's directories.** The store
would then hold a file describing itself, which `check` would have to have an
opinion about, which two replicas could disagree about, and which a tool
could write to grant itself a class. 0048 refused a listing inside the store
for the smaller version of this reason. A reservation belongs where the
argument for it is, which is a decision document.

**A namespace prefix — `x-claims/`, on the `x-` header's precedent.** The
header space can be open because an unknown header hashes like every other
and changes nothing; a directory is not like that, since the whole question
is what transport does with it, and a prefix answers none of it. An open
namespace with no class attached would mean either carrying everything with
that prefix, which is the disclosure default this decision refuses, or
carrying nothing, which is the status quo with extra syntax.

**Dynamic libraries and a C ABI, or a wasm plugin runtime.** Both buy
language independence, and both buy it with a stability surface far larger
than the Rust API — an ABI historica would have to keep, a host runtime it
would have to embed, and a boundary across which `check`'s invariant cannot
be stated. The one thing that genuinely wants language independence is
reading the store, and the format already answers that: it is text, and
`format.txt` travels with every copy.

**Hooks in the store — `history/hooks/pre-receive`.** Git has these and they
do not travel, for exactly the reason they must not. Here everything at the
store root travels by default under some class or other, so this would be the
one thing in the design that both moves and executes.

## Consequences

- `store` gains `Travel`, a registry of reserved directories, and the
  question `travel(<name>)` answers. All three are public: a tool that
  reserves a directory should be able to ask what historica promises about
  it, and the promise is now something the API states rather than something
  a decision document says.
- `ExportPlan` gains the reserved files that travel and `Exported` gains a
  count of what was carried; `ReceivePlan` and `Received` gain the same pair.
  All four are public, so the implementing commit carries a
  `Behavioural-change:` trailer — an export that previously left `claims/`
  behind now carries it, and a receive that ignored the directory now unions
  it.
- `check` gains nothing. 0046's tolerance is unchanged, and a class is a
  statement about transport rather than about validity.
- `format.txt` gains the paragraph 0046 said it would, now saying what it
  could not say then: the rule, and the two names with their classes. The
  layout listing in `store/mod.rs` matches.
- The `x-` header space remains what 0046 left it: available to any tool for
  advisory annotations, ignored and hashed like everything else.
- An older historica exporting a store that holds claims writes a copy
  without them. The failure is quiet in historica and loud in the tool, which
  reports a revision no trusted key vouches for — so the recovery is a
  re-export with a newer historica, and nothing needs a store-layout gate to
  find out.

## Deferred

**Claims in an offer.** 0048's listing has three kinds — `revision`,
`operation`, `payload` — and a travelling reserved directory would be a
fourth, which is a grammar change to the manifest and a policy for a fetcher
that meets a kind it does not know. Nobody has published a store with claims
in it. When somebody has, that is the decision, and the class established
here is what it will be written against.

**A travelling directory with a private half.** The answer is a second
reservation at a second name with the `local-only` class, and the reason it
is not decided here is that nobody has a tool wanting it. What it must not
become is a filter over one directory, for every reason argued above.

**A class for mutable files.** `travels-and-unions` needs immutability and
digest names to be conflict-free, which is 0003's whole story; a directory of
files that change would want the merge policy `names/` still does not have
(0029, deferred again by 0042 and 0048). Whichever decision finally states
what two replicas' bookmarks mean together is the one that can afford a
fourth class.

**Retiring a reservation.** A name given away is given away; what an older
historica does with a directory it does not know is carry nothing, which is
safe, and what a newer one does with a name a tool abandoned is nothing at
all. Neither needs an answer until a reservation is actually withdrawn.
