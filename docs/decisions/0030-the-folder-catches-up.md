# 0030 — The folder catches up

Decision 0008 deferred "the working directory: checkout, status, and how a
contested path is shown to a person". 0011 answered the half `record` needed,
0012 answered it for merging, and 0015 took status, leaving one word of the
deferral standing and sharpening what it would cost:

> **Checkout**, which is 0008's remaining half and the one that does need a
> position — or needs to decide it does not, which is a larger question than
> this one and should not be answered as a side effect of it.

This is that decision, made on its own and not as a side effect. The command is
`historica update`, it writes the folder the store already records, and the
answer to the larger question is: **it does not need a position, because the
folder is only ever given a head.**

What makes the question due now is 0029. A store can arrive whole — `receive`
copies another store's history into this one — so a person can carry their
journal to a second machine and have every revision and none of their files.
The store is complete, `log` narrates it, `cat` prints any file in it, and the
folder beside it is empty. Every command that writes the folder today writes it
for one purpose: `merge`, for joining. Nothing writes it for the ordinary case
of the store having moved ahead of it.

## The decision

- **`historica update [<target>]` makes the folder hold the tree at the
  target.** Files the target records are written, byte for byte what `cat`
  prints; files the target does not record are removed, if history holds their
  bytes; everything else is left exactly where it is.
- **The target is a current head.** One head needs no argument; several require
  naming one, and the refusal lists them as `record`'s does. A revision that is
  not a head is refused, and the refusal says what serves the want instead.
- **There is still no position, and now there never needs to be.** 0011 said
  the per-machine file becomes necessary "when something other than a head can
  be in the folder". Update is the tool's only way of putting a tree in the
  folder, and it only puts heads there, so the condition never arrives. The
  rule underneath nine decisions holds unqualified: the folder as it stands and
  the store as it stands, and no third thing that can disagree with either.
- **Update replaces only bytes some revision records.** A file whose on-disk
  content no revision has ever recorded is never overwritten and never
  deleted. Where such a file sits at a path the target does not hold, it is
  left alone; where it sits at a path the target holds, the whole update
  refuses and names it.
- **All or nothing.** Refusals are collected, 0015's verb, and one refusal
  stops every write. A folder that half-holds a head is worse than a folder
  that plainly is not there yet, for a reason stated below.
- **The plan is what gets done.** `update::plan` and `update::apply` are a
  library pair on 0025's promise — the plan is what gets done, so `--dry-run`
  and the real thing cannot name different files — and apply looks at each
  destination once more immediately before writing it, so what it returns is
  what happened rather than what was intended.
- **Every removal is printed**, as `prune` prints every file it deletes. A
  deletion a person asked for in one word is still a deletion they should be
  able to read back.

## Why the target is a head

Start with what goes wrong if it is not. Suppose update wrote the tree at some
older revision into the folder, and the store has one head. Every command
derives its position, so the next plain `status` compares that folder against
the head and reports nearly every file edited or dropped — confusing, but
visible. The next plain `record` does the same comparison and *acts* on it: it
writes a revision that reverts everything between the old revision and the
head, silently, as ordinary work. Nothing is lost, because nothing here ever
is, but the history now states something nobody meant, and the tool had no way
to notice, because noticing means remembering where the folder was put — which
is the stored position, which is the third thing.

So the choice is exactly the one 0015 said it would be: store a position, or
decide checkout does not need one. A position is stored by keeping the trap;
this decision removes the trap instead. The folder is where the next record
happens, a record's parent is a head unless a person says otherwise, and so
the folder the tool maintains is a head's folder — always. Update refuses to
create the one state it could not afterwards account for.

What a person actually wants from "checkout to a past revision" has a spelling
already, and the refusal names them:

- **Reading an old state** is `log`, `show`, `files`, and `cat`, which answer
  for any revision without moving anything.
- **Going back** is `abandon` and then `update`. Abandoning a run makes its
  content fall out of the ancestry — the tree at the tombstone is its
  parents' — so the state a person wants to return to *becomes the head's
  state*, on the record, converging on every machine, and update materialises
  it. Going back is not a private excursion here; it is history saying, where
  everyone can read it, that the run was withdrawn. That is not a workaround
  for the missing feature. It is the feature, done in the open.
- **Working forward from an old revision** — the folder at R, edits, a record
  onto R — is the one want with no spelling, and it is deferred rather than
  half-built, below. It is also the only one that would reopen the position
  question, which is why it must not arrive as a flag on this command.

There is a case that looks like checkout-to-the-past and is not: after a
receive, the folder often *is* at an older revision — the revision it was
clean at before the other store's work arrived and became the head. Update is
built for exactly that folder. It needs no flag to say where the folder was,
because the rule below derives everything it needs.

## What may be replaced

`merge` already answered this for itself, in a comment worth promoting to a
rule:

> What distinguishes "the folder is where I left it" from "the folder holds
> something nobody has recorded", which is the only thing a merge must not
> overwrite.

Merge asks the question against the heads being merged. Update generalises it
to the store: **a file on disk may be replaced or removed exactly when some
revision the store holds records its current bytes.** Not "the head holds
them" — a folder standing at a superseded revision after a receive holds bytes
the head does not — and not "the target's ancestry holds them", but anywhere,
superseded and abandoned revisions included. Whether bytes are recoverable is
a fact about the store's files, not about which tips of the graph are current,
and recoverability is the entire question: update never destroys the only copy
of anything.

Three consequences fall out, and each lands somewhere a person can see it.

**A stray file coexists.** A note nobody has recorded, sitting at a path the
target does not hold, is not part of the comparison and is not update's to
touch. It stays, and the next `status` reports it as `added`, exactly as it
did before the update. The folder after an update is the tree at the head plus
whatever unrecorded work was already lying around — which is what "the folder
is theirs" means when a command that writes it comes along.

**Unrecorded work in the way refuses.** A file holding unrecorded bytes at a
path the target holds cannot be written without destroying work, so the whole
update refuses and names every such path. The fix is the fix it has always
been: record it, or move it aside, or delete it — by hand, in the folder,
which is the one place this tool never deletes unrecorded anything.

**Pruning collects here.** 0013 says the superseded revisions are the undo
history and `prune` empties it on purpose. After a prune, bytes only a pruned
document recorded are gone from the store, and a folder still holding them
holds the last copy — so update refuses to remove it. The refusal is 0013's
bill arriving at the folder, and it is correct twice over: the person who
pruned asked for exactly this loss of recoverability, and the tool declining
to finish the job silently is what "prints every file" was for.

The price is stated the way 0015 stated its own: for each path whose bytes
differ from the target's, update materialises that file's content at every
revision that touched it, because there is no index and 0011 is why. At
journal scale this is nothing, and it is paid only for paths that differ. It
is written down here so that it is a known price rather than a discovery, and
so the first person to propose caching candidate states under `cache/` finds
the argument already half-made — that cache is 0007's "materialised file
states" inhabitant, disposable by construction.

## All or nothing

0016 said it for `skip` and 0029 said it for receive, and update has a sharper
reason than either. Suppose update skipped one refused path and wrote the
rest. The folder now *almost* holds the head: the tree holds a file, the
folder does not, and the very next record observes that absence as a fact —
absence is a fact here, 0011 made it one — and records a `drop`. A partial
update is not a smaller update. It is a folder that lies about where it
stands, to the one command whose job is to believe the folder.

So every refusal is collected — unrecorded bytes in the way, content the store
cannot produce, a tree the folder cannot represent — and the update either
does everything it planned or nothing at all. The same argument closes the
missing-content case: a payload the store does not hold yet is 0007's ordinary
partiality and `check` calls it a note, but a *folder* cannot be partially at
a head, so update refuses and names the digest; receiving the rest is the fix.
Forgotten content divides by kind, exactly as 0014 left it: a file of lines
whose history holds forgotten items materialises with the `\ forgotten` marker
standing where the run stood — the same bytes `cat` prints — while a file of
bytes whose payload was forgotten has no content any store can produce, ever,
and refuses. The fix for that one is recording the `drop` that forgetting made
true, from the head where the person stands.

What all-or-nothing cannot promise is atomicity, and 0026 already said so: the
contract is one file, not a transaction. Apply is a sequence of per-file
atomic writes, and a machine that stops halfway leaves a folder some files
into an update — every one of them recorded content, nothing lost, and the
same update run again finishes the job, because a plan computed from the
folder as it now stands plans exactly the remainder.

## The folder that cannot hold the tree

0027 requires "a materialising command to refuse on a filesystem that cannot
represent both", and update is the command it was waiting for. The refusal
comes as early as the knowledge can:

- **A collision the tree itself states refuses in the plan.** Two files at one
  path — the contested state a merge can legitimately record — cannot both be
  a folder's truth, and a path that is also a directory of another path
  cannot be filed at all, 0018's real directories being real. Both refuse
  before anything is written, in `merge`'s words where the words exist.
- **A collision only the filesystem knows is discovered by looking.** Whether
  a folder folds two spellings of a path — case, normalisation — is not a
  fact the format can see, and 0008 already declined to make it one. So apply
  verifies: after writing, each written path is read back, and a file whose
  bytes are not what was just written means the folder folded two paths onto
  one. That is reported loudly, by both names. Nothing unrecorded was at risk
  in the discovery — every byte the fold clobbered is a byte this update had
  just written from the store — and the folder is left saying, accurately,
  that this tree does not fit here.

Two smaller refusals of the same kind: a target path beginning `history/`
would write a working file into the store, which 0022 spent a payload learning
not to allow in the other direction; and a target path a `skip` rule covers
would write a file the walk could never offer back, which is the blind spot
0011 refuses when the rule arrives and update refuses when the file would.

## Why this is not `checkout`

0029 asked "why this is not `sync`" and answered that the borrowed name
promises the wrong things. Checkout is the same case. The word — this
project's own earlier decisions used it, waiting — promises what Git's
command does: travel to any revision, with a stored `HEAD` remembering where
you went, and a detached state for everywhere the store of positions cannot
describe. Half of what this command refuses to do is in that name.

What the command does is narrower and has a plainer name. The store moved
ahead of the folder — a receive brought work in, a merge was recorded, a run
was abandoned, another head was chosen — and the folder catches up. `receive`
brings history into the store; `update` brings the folder up to it. The pair
is the whole story of a second machine: receive, then update, and the journal
is there.

## Rejected alternatives

**A stored position — `history/at`, finally on its merits.** 0011 rejected it
"until checkout needs it, not on its merits", and promised this decision would
introduce it if checkout did. The merits, then. It is per-machine and never
synced, a fourth kind of file in a layout whose three kinds are all accounted
for — 0011 walked through why neither `names/` nor `cache/` can hold it. It
disagrees with the folder the moment anything but the tool touches either —
an edit, a sync service, a person in a file browser — and it disagrees
silently, forever, which is 0015's exact phrase for it. And everything it
buys is the ability to stand somewhere other than a head, which is the one
thing every trap in this document traces back to. Checkout did not need a
position. It needed to stop wanting one.

**Checkout to any revision.** Above: the trap for `record`, and every want it
serves has a spelling that keeps history straight — except working forward
from the past, which is deferred whole rather than shipped as a hazard.

**`--force`.** A flag that overwrites a person's unrecorded work is 0011's
words for `--drop`: the one destructive thing in the tool. The refusal names
every file in the way; a person who wants one gone deletes it themselves, in
the folder, which is theirs.

**Carrying unrecorded work through the update**, as `hg update` and `svn
update` do. Rebasing uncommitted edits onto a different parent is
transforming operations against operations — 0007's merge, run outside the
record, on work nobody agreed to merge. The tool's version of this feature
is: record, then `merge`, which writes its result where a person can read it
and refuses to record while markers stand.

**A partial update that skips what it cannot write.** Above: the folder then
lies to `record`, and the lie becomes a revision.

**A per-file update.** `cat <target> <path>` already prints any file at any
revision, and a shell redirects it; that is retrieval, and it composes with
`record` the way everything here does. Update is not retrieval. It is the
claim that the folder now holds the tree at a head, and a per-file flag would
be a way of making that claim false with the tool's own hands.

**Remembering the last update's target.** 0015 already rejected this file at
a smaller size.

## Consequences

- `historica update [<target>] [-n|--dry-run]` is the command, under "writing
  a store" in the usage text beside `record` and `merge`, because writing the
  folder is that family's work even though the store is only read.
- `src/update.rs` is the module: `update::plan` produces the writes, removals,
  and refusals from the store, the working copy, and a target; `update::apply`
  performs a plan and reports what happened, including anything it looked at
  again and left alone. Both are over `fs::Filesystem`, because a host that
  syncs a store wants the folder for the same reason a person at a terminal
  does — 0025's argument, word for word.
- Update prints each `wrote` and `removed` path as `record` prints its facts,
  says when the folder already held the target, and exits nonzero only when
  it refused.
- Directories a removal empties are tidied upwards until one refuses, which
  is `arrange` and `prune`'s rule and the trait's `remove_directory` contract.
- comparison.md's last row stops being a plain "no": Historica updates the
  folder to a head, and deliberately not to a past revision.
- The README's front-end paragraph gains `update` beside `receive`.
- Tests worth naming: a received store updates an empty folder to files
  byte-identical with the source's, payloads included; an update refuses, all
  of it, while one path holds unrecorded bytes, and names the path; a
  two-headed store switches folder between heads and back, leaving a stray
  unrecorded file untouched throughout; a folder standing at a superseded
  revision catches up to the head with no flags; `abandon` then `update`
  returns the folder to the state before the run, removing the file the run
  added; a non-head target is refused by name; `--dry-run` prints the plan
  and writes nothing; a removal that empties a directory removes the
  directory; a store missing a payload refuses to update; and updating twice
  is the identity the second time.

## Deferred

**Materialising a revision into a directory elsewhere.** Reading a past state
whole — the folder-shaped version of `cat` — needs no position and no safety
rule beyond an empty destination, and it is export rather than checkout. It
waits for something to need it.

**Working forward from a revision that is not a head.** The one want update
declines to serve. Whatever decision builds it inherits the position question
this one closed for heads, and 0011's `history/at` paragraph is where it
would have to begin.

**A pointer from `receive`.** A receive that changed the head could print the
`update` line a person will want next, the way `merge` prints its `record`
line. Interface polish, cheap, and not this decision's to make binding.
