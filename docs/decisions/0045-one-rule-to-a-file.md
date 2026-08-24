# 0045 — One rule to a file

Two machines. One is a laptop where a person wrote `skip target/`; the other is
a desktop where the same person wrote `skip-suffix .tmp`. Neither rule
contradicts the other, neither person disagreed with anybody, and `receive`
refuses:

```console
$ historica receive ../desktop
two stores disagree about what only one of them can say:
  skipped.txt differs
```

The fix is to open both files, notice that the merge is *both lines*, write
them out by hand, and do it again next week. That is a conflict manufactured by
the container. 0003 called mutable names the store's entire conflict surface
and 0026 added `skipped.txt` to the list, but a conflict is supposed to be two
people saying incompatible things, and `skip target/` beside `skip-suffix .tmp`
is not that.

The tell is in the reader. `Skipped::skips` is `rules.iter().any(covers)`:
order means nothing, a rule stated twice means what one means, and no rule can
cancel another because there is no negation (0011 refused one). What the file
holds is a **set**, and it has been a set since 0011. Only the file is a
sequence — and a sequence is the thing two writers cannot both append to.

## The decision

- **`history/skipped/`, a directory, one rule to a file.** It replaces
  `history/skipped.txt`. Every file in it, at any depth, states one rule, and
  history skips what any of them covers.

- **The filename is a label and the content is the rule.** The reader never
  parses a name. This is 0018's arrangement exactly — a name for whoever opens
  the folder, identity from the bytes — and it is what makes a path spellable
  at all, since `skip docs/drafts/` contains a character no filename holds.

- **The label a writer picks mirrors the path.** `skip docs/drafts/` is written
  to `skipped/docs/drafts.txt`, `skip .DS_Store` to `skipped/.DS_Store.txt`,
  and `skip-suffix .tmp` — which names no path — to `skipped/suffix .tmp.txt`.
  A name already taken by a *different* rule takes a digest suffix, which is
  0018's answer to the same collision. A label the filesystem will not accept
  is replaced by the digest of the rule alone. A person writing a file by hand
  may call it whatever they like; the rule is what is inside it.

- **A file states one rule, and a `#` line states nothing.** The grammar of the
  line is 0011's, word for word, and 0022's comments come with it. A file
  stating two rules is malformed, and `check` names the file rather than a line
  number, which is the better half of this trade.

- **Receiving is union by rule.** Every rule the source states that the
  receiver does not gets a file. Matching is on the rule, not the label, so two
  machines that spelled the same rule under different names keep one file
  between them. `MutableConflict::Skipped` is deleted; there is no longer a
  disagreement for it to describe.

- **Removing a rule is deleting its file, and a later receive may bring it
  back.** There are no tombstones. The argument is below, and it is 0011's own.

- **A rule that arrives covering a file the tree already holds is accepted, and
  `record` refuses as it already does.** `check` gains a finding for the state,
  naming the rule file and what it covers, because the fix is now to delete one
  file and the message can say so.

- **`init` writes the directory and one file that states no rule.** 0027 has
  the default explain the grammar and state nothing; a comment-only file is
  that, with no special case in the reader, and it unions with the identical
  file on every other replica to itself.

- **`historica.txt` states `historica-v2`.** Reasoning below: this is the one
  kind of change an older reader must not read past.

## Why removal cannot be exact, and should not be

The wrinkle is real: deleting a file is exactly what a copy from a replica that
still has it undoes. Every conflict-free set meets this, and the two honest
answers are a tombstone or an accepted resurrection.

A tombstone works and costs the thing the design was for. A file saying
`removed skip target/` can never be collected — no replica can know every other
replica has seen it — so `skipped/` becomes a directory where an unknown
fraction of the files mean *not*, and the person who opens it to see what their
history skips has to read all of them and do the arithmetic. That is 0016's
browsable store spent on an edge.

The stronger reason is that resurrection is the **safe direction of failure**,
which 0011 argued when it refused an unknown key:

> a reader that ignored `skip-glob` because it had not heard of it would record
> files somebody asked it not to, into a history that is append-only. Refusing
> to record is recoverable. Recording is not.

A rule that comes back keeps a file out of a history: recoverable, by deleting
the file again. A removal that wins puts a file somebody asked to keep out into
a history that cannot take it back. Between an exact answer that can fail
either way and an inexact one that can only fail the recoverable way, this
project has already chosen, four decisions deep.

And the return is loud. `record` refuses when a rule covers a tracked path —
`RecordError::SkipsTracked`, on 0011's reasoning that the walk would stop
offering the file and the next record would spell a request for privacy as a
deletion. A resurrected rule therefore stops a command with a message rather
than quietly changing what a history holds. The remaining case — a resurrected
rule over an untracked file — hides a file from the folder's point of view
until somebody deletes the file again, which `status` shows and a file browser
shows.

What this genuinely costs: **a person who wants a rule gone must say so on
every replica.** Not a paragraph of hedging — say it in the error message, name
the store the rule came back from, and let the person decide.

## Why this is a version boundary

An older reader opening a store with `skipped/` sees a directory it does not
know, no `skipped.txt`, and therefore no rules. It would then record every file
the person asked it to keep out, into an append-only history. That is precisely
the outcome the previous section calls unrecoverable, so it is not a
compatibility question with two defensible answers.

The version marker is the gate that exists for it. 0017 makes the marker the
reader's refusal point, and while its subject there is document grammar, its
sentence is general — a reader that knows less refuses. This is a store whose
rules a v1 reader cannot see, so a v1 reader must refuse the store.

The rejected alternative is to keep writing `skipped.txt` alongside the
directory for older readers. Two files stating the same truth is the shape 0011
spent a section refusing, under the name *which of five files won*, and a
shadow file whose staleness nothing detects is worse than a refusal a person
can read.

## What the label can and cannot carry

A rule is not a filename, and pretending otherwise is where this design fails
if it fails.

- A path holds `/`. That is why the label mirrors the path into real
  directories rather than escaping it: the walk already recurses, because 0016
  lets a person arrange `operations/` however they like.
- APFS is case-insensitive, so `skip Docs/` and `skip docs/` are two rules that
  want one name. NFD and NFC are the same problem in 0033's clothing, with the
  rules already normalised to NFC on the way in. Both are collisions, and a
  collision takes a suffix.
- 0022 was written from a store that a file browser damaged. `skipped/` is a
  new directory a person will open, so Finder will write a `.DS_Store` into it,
  and `PLATFORM_NAMES` applies here as everywhere: such a file is not a rule
  and not a finding.

None of this is a new mechanism. It is the same mechanism `operations/` uses,
applied to a smaller thing.

## What receive stops needing

The current plan compares the two files against `DEFAULT_SKIPPED` to decide
whether the receiver's file is *really stated* or just what `init` left:

```rust
(None, Some(there)) => plan.skipped = Some(there.to_owned()),
(Some(here), Some(there)) if here == DEFAULT_SKIPPED => { … }
(Some(_), Some(there)) if there == DEFAULT_SKIPPED => {}
(Some(_), Some(_)) => plan.conflicts.push(MutableConflict::Skipped),
```

Three branches whose whole job is to guess intent from a byte comparison
against a constant. They all go. The default states no rules, so the union of a
default store and a store with rules is the rules, arrived at by the same line
that unions everything else. A special case that disappears when the container
changes was a property of the container.

## Rejected alternatives

**Keep the file and union its lines on receive.** This fixes the sync conflict
without touching the layout, and it is the closest alternative. It is rejected
on three counts. It makes `receive` a writer of a file a person hand-edits, so
comments, order and the explaining header must each be preserved or destroyed,
and every answer to that is a policy nobody asked for. It leaves the
same-machine race, since two `skip` commands still read, modify and write one
file. And it makes removal exactly as resurrectible while making it invisible:
a line reappearing inside a file is not a thing a person notices, and a file
reappearing in a directory is.

**Per-machine rules that never sync.** 0011 puts the file in the store on the
grounds that what a repository skips is a fact about the repository, the
opposite of 0010's identity read backwards. Nothing here disturbs that.

**Rules as history.** An operation document stating a rule would give removal
an ancestry, and ancestry is how this format resolves every other ordering
question. It is refused because 0007 makes every operation permanent: a rule
tried and withdrawn would be in the log forever, `log` would fill with folder
housekeeping, and a person could not answer "what do I skip?" without replaying
history. A rule is a fact about the folder *now*. If rules ever need to say why
they exist or who added them, this is the decision to revisit.

## Consequences

- `history/skipped.txt` becomes `history/skipped/`. `SKIPPED_FILE` becomes
  `SKIPPED_DIR`; `DEFAULT_SKIPPED` becomes the text of the one file `init`
  writes.
- `Skipped` keeps its API — `skips`, `skips_directory`, `rules`, `len`,
  `is_empty` are unchanged, and every caller in `record`, `working`, `blame`
  and `export` compiles as it stands. `Skipped::parse` is joined by a reader
  over a directory, and `Rule` gains the label a writer files it under.
- `Store::append_skipped` becomes an add that writes one file per rule with
  `create_new`. Two concurrent `skip` commands on one machine can no longer
  lose a rule, which is 0026's property arriving where 0026 could not put it:
  atomic replacement keeps a value whole, and creation makes two values
  impossible to confuse.
- `MutableConflict::Skipped` is removed, `ReceivePlan::receives_skipped`
  becomes a count of rules, and `Received::skipped` becomes `usize`. All three
  are public, so the implementing commit carries a `Behavioural-change:`
  trailer.
- `check` gains: a file in `skipped/` that is not one rule (error, naming the
  file), a rule covering a file the tree holds (error, naming both), two files
  stating one rule (note), and a legacy `skipped.txt` (note).
- A legacy `skipped.txt` is still read and its rules still apply, so no store
  breaks on upgrade. Nothing converts it automatically: the note says the rules
  can move and the person deletes the file, because a migration that deletes a
  synced file on one replica is the resurrection problem wearing a hat.
- `export` excludes the directory where it excluded the file (0042), and the
  store's own listing in `store/mod.rs` and `store/format.txt` gains a
  directory where it had a file — the layout 0003 counts on one hand now counts
  `names/` and the marker as its mutable surface, with `skipped/` create-only
  beside them.

## Deferred

**Collecting a resurrected rule.** If a person deletes the same rule on three
machines and it keeps returning from a fourth they have not opened since March,
nothing here helps them. A `skip --forget` that wrote a tombstone is the shape
of the answer and this decision declines to build it, because the case is
hypothetical and the tombstone is permanent. What would justify it is somebody
meeting the loop in practice.

**A store-layout gate distinct from the document-version gate.** `historica.txt`
now carries two meanings: the highest document version a store holds, and
whether the reader understands the layout. They will not always move together.
One gate that occasionally refuses more than it must beats two gates a writer
can forget, so this is noted and not fixed.
