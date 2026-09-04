# 0074 — Saying where to look

0064 gave the reading half of this. `log --fields` prints the same listing a
person gets, in fields, under a `historica-log-1` header, for a caller that
would otherwise parse a rendering meant for eyes.

The writing half has nothing. A command that records, amends, abandons,
carries, merges, prunes, forgets, names or receives prints sentences — good
sentences, written under 0021 and worth keeping — and a program that wants to
know what just happened has to either parse them or re-read the whole store and
diff it against a copy of what it saw last time.

Both are bad in the way 0064 named. Parsing the sentences makes the wording an
interface nobody promised, and the README is explicit that it is not one:

> The exact wording a command prints is not an API, though what it has to say
> is, since a person reads it and 0021 makes that a design constraint.

And re-reading the store to find out costs an open — `revisions/` and `names/`
in full — to answer a question the command that just ran already knew the
answer to.

## What this is not, and the objection it has to survive

0064's longest section is a rule about what may go in a machine-read output,
and this decision would be the first thing to test it:

> The gap is everything that is not in any one document:

It admits which revisions, in what order, and what the graph found, because
none of the three is stated by any document. It refuses the converse by name:

> A listing that also restated the author and the message would be a second
> rendering of text the authority already holds, and 0037 has already refused
> that shape once

A statement of what a command wrote looks, at first, exactly like the refused
shape. The revision it names is in `revisions/`. The bookmark it names is in
`names/`. Every fact is already on disk in a grammar 0002 documents, one
command return later.

That objection is right about a *report* and wrong about a *pointer*, and the
whole of this decision is the difference.

## The decision

- **`historica-wrote-1`, and every line is a pointer into the store.** Not a
  description of what was written — a statement of *where to look*. The
  vocabulary is small and closed:

  ```text
  historica-wrote-1
  revision <digest>
  name <bookmark>
  unname <bookmark>
  gone <digest>
  ```

  `revision` is a revision document that was written and is now in
  `revisions/`. `name` is a bookmark that was written or moved and is now in
  `names/`. `unname` is one 0073 removed. `gone` is a digest something
  destroyed, which is `prune` and `forget`'s half.

- **`name` and `unname` take everything after the first space.** A reader splits
  the line once and the remainder is the bookmark, whole. 0064 could say no
  field of its own can hold a space and note that this was not luck; that does
  not survive 0071, which makes a name its path below `names/` and forbids only
  a *leading or trailing* space in it. `feature/two words` is a bookmark
  somebody can create today, and a reader splitting on every space would find
  two fields where the store has one name.

  What makes the remainder unambiguous rather than merely conventional is
  0018's grammar, which 0071 reads rather than restates: a name holds no
  control character, so it can never hold the newline that ends the line it is
  written on. The line is therefore exactly one name after the first space, and
  there is nothing to escape and no length to state.

- **The lines come in a stated order, so two replicas print the same bytes.**
  Kind first, in the order the vocabulary lists them — `revision`, `name`,
  `unname`, `gone` — and within a kind, digests ascending and bookmark names in
  byte order. Almost any rule would have done; what could not stand is having
  none, because a comparison against an unordered statement is a set test, and a
  wrapper reading the statement as a stream has undefined behaviour that happens
  to work.

  Sorted rather than written-order, which is the tempting alternative and the
  wrong one. This is a set of pointers rather than a narrative — nothing in the
  vocabulary says *then* — and the order a command happened to write in is a
  fact about its loop rather than about the store. `carry` already holds the
  standard: nothing is stamped or minted, so two replicas repairing one history
  write the same bytes. A statement of what they wrote should agree.

- **Nothing a document says is restated.** No change ID, no parents, no
  message, no author, no timestamp, no supersession. The caller has the digest;
  the document is the authority and is one read away. This is 0064's rule
  obeyed rather than bent — the listing there copies parents for a stated
  reason, that a graph walker given only digests would have been given nothing,
  and no such reason exists here. A caller reacting to a write opens the
  document it is reacting to.

- **The one copy is a minted identifier**, which is the exception 0064 already
  argued for and the reason the pointer shape is safe:

  > It is a copy of a minted identifier, which cannot disagree with its
  > original the way a re-rendered message could.

  A digest and a bookmark name are both minted or chosen, never rendered. There
  is no formatting decision anywhere in this output for a second implementation
  to make differently.

- **Spelled whole.** Digests in full, never abbreviated. 0001 makes an
  abbreviation the shortest prefix unique *in this store today*, so a caller
  that wrote one down would find it ambiguous after a fetch, through no change
  to the thing it named. 0064 settled this and it carries.

- **`--fields`, on the writing commands, replacing the reading for a person.**
  The same flag as 0064, for the same reason it was one flag there rather than
  a second command: two commands are two answers about what happened, and
  eventually they differ.

  Which commands, said outright rather than left to *the writing ones*:
  `record`, `amend`, `abandon`, `carry`, `merge`, `prune`, `forget`, `name` —
  including `name --delete`, which is what `unname` is for — `receive`, and
  `fetch`. A command outside that list refuses the flag rather than printing an
  empty statement, because a wrapper that asked `update --fields` and was given
  a header and no lines would read it as *nothing was written*, which is the one
  sentence in this format that most needs to be true. `update` and `skip` are
  absent because both are deferred below, not because they write nothing.

- **`--dry-run` and `--fields` together are refused.** A plan is not a claim the
  store can be held to. It is a statement about a store that does not exist yet,
  and every line of it is false at the moment it is printed — which is the exact
  property this header promises, so lending the header to a preview costs more
  than the refusal does. A machine-readable plan is a reasonable thing to want,
  and it is its own header and its own decision.

- **A statement covers what is on disk, and the exit code carries the failure.**
  A command that stops partway has written some of what it meant to, and the
  reading that keeps this document's central property is to print the lines that
  are true and let the status say it went wrong. The alternative — no statement
  at all on a non-zero exit — sends a wrapper back to re-read the store to find
  out what survived, which is the cost this format exists to remove.

  Where a command cannot say what it wrote before it stopped, it prints a header
  and no lines. That is not a weakening. An empty statement is already this
  format's well-formed statement of nothing, and no line of it is ever a claim
  the store would refuse. The writing commands plan and then apply, so nearly
  every refusal they have is raised before anything is written and there is
  nothing to report; what remains is an I/O failure mid-apply, and threading a
  partial result out of every error in the library is a cost this decision does
  not ask for and could not justify from the one wrapper that would notice.

- **Wrote nothing is a header and no lines, exiting zero.** Not silence, and
  not the sentence a person gets. 0064's rule exactly: what a caller needs is a
  well-formed statement of nothing, which is what an empty one is. This is the
  single most useful line in the format, because it is the one that lets a
  wrapper do nothing at all, and it is the one fact here that is *not*
  recoverable from the store — a store that did not change looks identical to a
  store nobody wrote to.

- **A path goes last, or is not in it.** 0064 could say nothing is escaped
  because no field it has can hold a space, and noted that this was not luck.
  It does not survive generalisation: `update` reports paths it wrote and
  `forget` reports files it destroyed, and a path is the one field that may hold
  a space. 0048's manifest already solved this by putting the path last. The
  vocabulary above has no *file* path in it at all, which is the stronger form
  of the same discipline; its one path-shaped field is a bookmark, and the rule
  above puts it last on its line for exactly this reason. The folder is deferred
  below rather than quietly given a quoting rule.

- **The number is the compatibility promise, and the vocabulary is closed so it
  need not move.** A reader that meets a line kind it does not know discards
  the statement whole rather than guessing, which is 0048's discipline as 0064
  read it. Adding a line kind is therefore `historica-wrote-2`. Four kinds were
  chosen to make that unlikely: they are what a store *is* — documents and
  names — rather than what a command *does*, and a fourteenth writing command
  would emit the same four.

## Why the redundancy is the point

The pointer shape leaves this output almost entirely derivable from the store,
and that is not a defect to be engineered away. It is the property that makes
it safe, and it is worth stating as a rule of its own:

**Every line is a claim the store can be held to.** `revision <digest>` says a
document is in `revisions/`; go and see. `name <bookmark>` says a file is in
`names/`; go and see. `gone <digest>` says nothing is there; go and see. So the
statement and the authority can be compared, mechanically, on every write a
test performs — and the comparison is total, because the vocabulary is four
kinds and each one is a question with a yes or no answer on disk.

That makes this the first end-to-end test of 0003's rule from the writing side.
The readable files being the authority is asserted by every decision here and
checked, today, by reading them. A command that says where it wrote and can be
wrong is a command that can be caught being wrong.

It also bounds the damage when it is. Nothing here is load-bearing: a caller
that ignored this output entirely and re-read the store would get the same
answer, more slowly. That is deliberately the same status 0003 gives
`history/cache/` — a fast path that may be discarded without losing meaning —
and it is why this can be added without becoming something a later decision has
to work around.

## What it costs a host that cannot spawn

Nothing, which is the test 0053 set and 0072 restated. This is output on a
descriptor, printed by a command a person or a script ran. A host with no
`PATH` and no process was never reading it, and holds `Recorded`, `Amended` and
`Abandoned` directly — those are public, on the library, and carry strictly
more than this does. Capability stays where 0053 put it; this is a spelling of
the smallest part of it for callers on the far side of a process boundary.

That is also the honest account of what is being added. `historica::record::
Recorded { revision, change, plan, advanced }` already exists. This is not new
knowledge. It is existing knowledge made available across a boundary that
otherwise only carries text meant for eyes.

## Rejected alternatives

**A field set per command.** The writing commands are about thirteen and they
do heterogeneous things; a format shaped to each would be thirteen grammars to
version, and 0064's tightness — five fields, none of which can hold a space,
"that is not luck" — survives in none of them. Shaping the vocabulary to the
store instead of to the commands is what makes one small grammar enough.

**Restating what the document says**, so a caller need not open it. It is the
shape 0064 refused and 0037 refused before it, and the argument does not weaken
just because the restatement would be convenient. A caller that wants the
message reads the document, which `show` also prints byte for byte.

**A machine-readable statement of the folder.** `update` writes files, and a
caller wanting to know which is asking a real question. It is a different one:
the folder is not the authority, its paths can hold spaces, and what changed in
it is what `status` and `diff` answer. Deferred rather than refused.

**Emitting it always, rather than behind `--fields`.** It would put a header
and a list of digests in front of a person for whom 0021 wrote the sentences.

**A file rather than a descriptor.** It would be state between commands, which
0011 does not keep, and it would need a lifetime, a location, and a rule for
who deletes it.

## Consequences

- **The grammar lives in the library, writer and parser together**, and
  `render.rs` calls it rather than holding it. Beside 0064's writer was the
  obvious home and is the wrong one: `historica-minisign` and `historica-git`
  read this format from the far side of a pipe, and 0053 says a side tool gets
  what it needs from the API rather than by writing a second implementation of a
  grammar we own. A parser in the CLI is a parser neither of them can link. One
  implementation, shared by the writer, the comparison and every consumer, is
  also the only arrangement under which that comparison tests the thing callers
  actually use.
- Each writing command in `cli/src/cli/` grows a `--fields` flag that suppresses
  the reading for a person and prints this instead. The values it prints from
  are the ones the library already returns.
- **`Received` and `Fetched` gain the digests they take.** Both report counts
  today — `revisions: usize` — so `receive` and `fetch` are the two commands
  named above that cannot say where to look. The knowledge is not new:
  `ReceivePlan` holds every digest and drops it on the way out. Both structs are
  `#[non_exhaustive]`, so this is an addition rather than a break. Deriving the
  digests in the CLI instead, by taking a plan beside the apply, would be the
  second implementation 0053 refuses, and it would let the statement and the
  store disagree — which is the one thing *Why the redundancy is the point* says
  cannot happen.
- `docs/cli.md` gains the grammar, beside 0064's.
- The corpus gains the comparison described above: for each writing command, the
  statement it makes and the store it made, checked against each other.
- **No `Behavioural-change:` trailer is owed.** Nothing a caller sees today
  changes; a flag that did not exist begins to.

## Deferred

- **The folder.** Above. `update`'s writes, and the quoting rule a path needs,
  are their own decision.
- **A reserved directory, which needs no line and is not an omission.**
  `receive` unions `claims/` under 0053 and counts what arrived in its result's
  `reserved` field, and no line kind reports it. It needs none, and the reason
  is worth stating because it is not obvious: a claim arriving can only ever
  move a revision from unvouched to vouched, never the other way. So the wrapper
  this would serve —

  ```sh
  historica receive --fields ../other | historica-minisign verify --complete
  ```

  — never needs to know that one came. It runs `verify` when the statement has
  any line at all, and the verdict is over the store as it stands rather than
  over what arrived. `trust/` is local-only and never arrives. A line kind for
  it would be `historica-wrote-2` under the compatibility rule above, bought for
  a distinction no caller has needed.
- **`skip`,** which writes a rule rather than a document or a name, and has no
  line kind here. Rules are a fifth thing a store holds and adding them is
  `historica-wrote-2`; nobody has asked yet.
- **Whether `receive` and `fetch` should say what arrived versus what was
  already held.** Both are `revision <digest>` here, and the distinction is one
  a caller can make by having looked before. If that turns out to be the common
  case it is an argument for a mark, and marks are what 0064 spent its own
  paragraph being careful about.
- **A statement for the reading commands.** `show`, `cat` and `files` print
  documents and bytes and need nothing; `status` and `diff` are the folder, and
  are deferred with it.
