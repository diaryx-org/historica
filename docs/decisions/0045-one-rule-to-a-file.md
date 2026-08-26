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
  to `skipped/docs/drafts/all.txt`, `skip .DS_Store` to
  `skipped/.DS_Store.txt`, and `skip-suffix .tmp` — which names no path — to
  `skipped/suffix .tmp.txt`. A directory rule sits *inside* the directory it
  names, which is what parts it from the exact-path rule spelling the same
  characters without either label having to carry a trailing slash. A label
  the store cannot own — a platform name (0022), a name already meaning
  something here, a component no filesystem will take — is the digest of the
  rule instead, and so is a label another rule already holds, which is 0018's
  collision suffix reached by 0018's reasoning. A person writing a file by
  hand may call it whatever they like; the rule is what is inside it.

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
  file and the message can say so. It also notes two files stating one rule,
  which is what a `receive` meeting two labels for one rule leaves behind.

- **`init` writes the directory and one file that states no rule.** 0027 has
  the default explain the grammar and state nothing; a comment-only file is
  that, with no special case in the reader, and it unions with the identical
  file on every other replica to itself.

- **A `skipped.txt` is not read, not converted, and reported.** Reasoning
  below.

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

## What happens to a `skipped.txt`

Nothing reads it. There is no migration, no dual reader, and no conversion
command: this library is young enough that the number of stores holding rules
is small and the number holding rules somebody would mourn is smaller, and a
compatibility path is a thing every later decision has to keep working.

That leaves one danger, which is the danger of every silent removal. A store
carrying rules a reader cannot see records the files those rules kept out, into
an append-only history — the unrecoverable direction again. So the file is
*reported*: `check` calls a `skipped.txt` beside the store an error, saying it
states nothing now and that rules are one to a file in `skipped/`. One finding,
no reading, and the person moves the lines themselves.

The rejected alternative is the version marker. `historica.txt` states the
highest *document* version a store holds, no document grammar changed here, and
a marker raised for a layout change would refuse stores over a difference the
documents do not have. What this really wants is a gate on the layout, which is
noted under Deferred and not built.

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
  `SKIPPED_DIR`; `DEFAULT_SKIPPED` becomes `SKIPPED_NOTE`, the text of the one
  file `init` writes.
- `Skipped` keeps the API its callers use — `skips`, `skips_directory`,
  `rules`, `len`, `is_empty` are unchanged, and `record`, `working`, `blame`
  and `export` compile as they stand. `Skipped::parse` becomes
  `Skipped::rule_in`, which reads one file and returns at most one rule;
  `from_rules` and `stated` build the set; `stating` and `file_of` say which
  file states a rule, since that file is what deleting it means. `Rule` gains
  `parse`, `label` and `digest_label`.
- `Store::append_skipped` becomes `Store::add_skipped`, which writes one file
  per rule with `create_new` and returns the labels it wrote. Two concurrent
  `skip` commands on one machine can no longer lose a rule, which is 0026's
  property arriving where 0026 could not put it: atomic replacement keeps a
  value whole, and creation makes two values impossible to confuse.
- `MutableConflict::Skipped` is removed, `ReceivePlan::receives_skipped`
  becomes `ReceivePlan::skipped` returning the rules, and `Received::skipped`
  becomes a `usize`. All three are public, so the implementing commit carries a
  `Behavioural-change:` trailer.
- `check` gains four findings: a file in `skipped/` that is not one rule
  (error), a rule covering a file the tree holds (error, naming the file to
  delete), two files stating one rule (note), and a `skipped.txt` beside the
  store (error).
- `skip` with no arguments prints the rules with the file stating each, where
  it used to print the file. 0016 said the preview is `cat`, and that was an
  answer for as long as there was one file to cat.
- `export` builds a store whose `skipped/` holds the note and nothing else,
  which is what it did with the file (0042). The store's listing in
  `store/mod.rs` gains a directory where it had a file, and the layout 0003
  counts on one hand now has `names/` and the marker as its mutable surface,
  with `skipped/` create-only beside them.

## Deferred

**Collecting a resurrected rule.** If a person deletes the same rule on three
machines and it keeps returning from a fourth they have not opened since March,
nothing here helps them. A `skip --forget` that wrote a tombstone is the shape
of the answer and this decision declines to build it, because the case is
hypothetical and the tombstone is permanent. What would justify it is somebody
meeting the loop in practice.

**A store-layout gate.** `historica.txt` gates document grammar and nothing
else, so there is no version of anything a reader can consult to learn that a
store's rules live somewhere it does not look. This decision needed one and
spent a `check` finding instead, which works because the layout it warns about
is the one this decision replaced and not a general answer. The next layout
change that can be misread rather than merely unread is where the gate has to
be designed, and designing it then beats guessing at it now.

## Since

0069 reserves the space, four decisions later, and still does not design the
gate. What it adds to the reasoning here is that "designing it then" had a
deadline this decision could not see: at 1.0 the readers people install are
what decide whether a later gate can be read at all, and this decision's own
`StaleSkipped` finding — hard-coded for the literal name `skipped.txt` — is
the evidence that the ad-hoc answer only ever looks backwards.
