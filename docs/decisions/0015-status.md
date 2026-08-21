# 0015 — Status

Decision 0008 deferred "the working directory: checkout, status, and how a
contested path is shown to a person". 0011 answered the half `record` needed
and said the other half stays deferred. 0012 said it again, in the same words,
and pointed one of its own deferrals here.

This takes up status. Checkout stays deferred, and the reason it can stay
deferred is the point of this document: status turns out to need nothing new
stored, and checkout needs a position.

The thing to notice first is that every other version control system
implements status against state it wrote down. Git reads three files to answer
it — the index, `HEAD`, and, mid-merge, `MERGE_HEAD` — and 0011's rule forbids
all three:

> Nothing is remembered between commands. The working copy is the folder as it
> stands and the store as it stands; there is no third thing that can disagree
> with either.

So the question is not what status prints. It is what status is allowed to
know, and the answer is: exactly what `record` already derives, plus the names
0006 already stores.

## The decision

- **Status is derived, and stores nothing.** It is the comparison `record`
  already makes, printed instead of acted on.
- **The survey is the primitive and the plan is derived from it.** One
  path-keyed traversal produces every fact; `plan` is that survey with an
  identifier minted per added path. Status mints nothing.
- **A file the folder cannot offer is reported, not raised.** The walk collects
  refusals instead of returning on the first, and `record` raises the collection
  it already raises one member of.
- **Several heads is a question, not a default.** `--onto` is required when
  there are several, spelled as `record` spells it, and the refusal names each
  head with any bookmark that resolves to it.
- **There is no "on".** Head is derived from the graph, not stored, and a
  person with two heads restates which one on every command.
- **A conflict stays a function of the graph.** Standing marker lines are
  reported only when the person restates the merge with `--merge`, never by
  recognising the syntax, and a path two files claim is reported the way
  `merge` already reports it.
- **A rename is still stated; status may say it noticed.** An added path whose
  bytes are exactly a dropped file's is printed as a suggestion beside the two
  facts, never instead of them, and never on a similarity score.
- **`record --dry-run` stays.** It is the survey with the record flags applied;
  status is the survey with none. Both call the same function, so they cannot
  describe different work.
- **Status exits zero whenever it described the folder.** A refusal is part of
  the description, not a failure of it.

## What status is allowed to know

Three things a person wants from status, and where each comes from.

**What the folder differs by** is `record::plan`, which already computes it:
the merged tree at the parents, a diff of every tracked file against the merged
content, and the four facts of 0011. Nothing about it is stored, and running it
twice on an unchanged folder gives the same answer for the same reason `log`
does.

**Which revision that is against** is `store.history().heads()`, which walks
the graph and returns the revisions nothing supersedes or parents. This is
worth being precise about, because it is easy to call head "the one piece of
state we have" and it is not state at all — it is an observation, recomputed
per command, and it cannot disagree with the store because it *is* the store.
That is what makes it usable here. A stored `HEAD` would be the third thing
0011 refuses.

**What to call it** is the one genuinely mutable thing in a store: bookmarks.
0006 makes `history/names` the only file that is rewritten in place, and 0011
already has records advance a bookmark that named the parent's change. So
status names a head by whatever bookmark resolves to it, and a person reads
`journal` rather than `1f4c2a90`. A bookmark is a name for a head; it is not a
position, nothing is checked out onto it, and moving one does not move the
folder.

That is the whole vocabulary. There is nothing status wants that is not in it.

## The survey is the primitive

`Plan`'s own doc comment states the invariant that shapes this:

> Recording produces it and then acts on it, so the two can never describe
> different work.

A `survey` written alongside `plan` would be a second traversal of the same
folder against the same parents, and the two would drift the first time either
grew a case. So the new shape is not a sibling. It is the primitive, and `plan`
becomes the thin thing:

```rust
pub struct Survey {
    /// Paths the tree does not hold yet.
    pub added: BTreeSet<String>,
    /// Files whose path changed, with the path they moved to.
    pub moved: BTreeMap<FileId, String>,
    /// Files the tree holds and the folder does not, with where they sat.
    pub dropped: BTreeMap<FileId, String>,
    /// What each path's content differs by, added paths included.
    pub edited: BTreeMap<String, OperationDocument>,
    /// Where each path the tree holds resolves to, after the stated renames.
    pub held: BTreeMap<String, FileId>,
    /// Paths the folder holds that nothing here can take, and why.
    pub refused: Vec<(String, String)>,
    /// A dropped path and an added path holding the same bytes, one to one.
    pub renames: Vec<(String, String)>,
    /// What the tree decided by rule rather than by agreement.
    pub contested: Vec<TreeContest>,
    /// Paths several files claim, which only `--at` settles.
    pub unsettled: BTreeMap<String, Vec<FileId>>,
    /// Marker lines still standing, by path, when joining.
    pub standing: Vec<(String, usize)>,
    /// The revisions this was surveyed against.
    pub parents: Vec<RevisionId>,
}
```

Keyed by path where a path is all there is, and by `FileId` where the tree
already holds one — a moved, dropped, or edited file has an identifier because
the tree gave it one. Only an added path lacks one, and minting it is precisely
what recording does and surveying does not.

`held` is what lets `plan` rekey: a surveyed path is either one the tree
already resolves or one about to be minted for. `plan` then mints one
identifier per added path and rekeys `edited` by file.
Every expensive thing — the merged tree, the `merged_content_of` replay per
file, the diff — happens once, in the survey, and both callers get the same
bytes because there is only one place they were computed.

This is also why the obvious shortcut is wrong, and it is worth naming because
somebody will reach for it. `Plan::added` is a `BTreeMap<FileId, String>`, so
handing `plan` a stub `Entropy` that returns a constant does not merely produce
meaningless identifiers — it collapses every added path onto one key, and
status reports one new file out of twenty. A read-only command that mints is a
smell; a read-only command that mints *badly* is a bug that looks like working
software.

## A rename is stated, and status may say it noticed

`moved` is the field status never fills. `plan` populates it from
`recording.moves` and `recording.at` and from nothing else, because 0011
decided that a rename is the one fact a person supplies: "a rename is stated;
everything else is observed." Status supplies nothing, so a folder where
somebody typed `mv` shows an `added` line and a `dropped` line.

That is not a defect and status should not hide it. It is exactly what `record`
would write if the person recorded now without saying `--move`, and status
promising otherwise would be status describing work `record` would not do.

But it is also the moment a person most needs the flag they have forgotten, so
status says what it noticed:

```text
notes/old.md and notes/2026-08-20.md hold the same bytes; if that is a rename,
say so with --move notes/old.md=notes/2026-08-20.md
```

The rule is exact content equality — a dropped file's content at the parent,
byte for byte, against an added path's bytes in the folder — and deliberately
not a similarity score. The `similar` matcher is already a dependency and would
catch the rename-plus-edit case this misses, and reaching for it would undo the
thing 0008 built the tree for. The README states the claim it would cost:
changes are "recorded against the file and no heuristic has to recover the
connection later." A threshold in status is a heuristic recovering the
connection later, with a number nobody can defend, in the one place a person is
deciding what to record. Byte equality is an observation instead: it has no
parameter, no false positives, and it is the case where somebody definitely
typed `mv` and definitely has not edited since.

Three rules keep it honest. The suggestion is printed beside the `added` and
`dropped` lines and never in place of them, so the fact list stays what `record`
would state. A match is offered only when it is one to one — two added paths
holding one dropped file's bytes is a guess, and status declines to make it.
And empty content matches nothing, since every empty file has the same bytes as
every other and a suggestion built on that is noise.

The miss is worth stating: `mv` followed by an edit before recording produces no
suggestion, and the person has to remember `--move` unaided. That is the price
of refusing the threshold, and it is smaller than the price of a rename tool
that is right most of the time.

## A file the folder cannot offer

`Working::read` returns on the first symlink, non-UTF-8 filename, or unusable
path, and `plan` returns on the first file that is not UTF-8 text. For
`record` that is right, and 0011 says why: the difference between losing work
and not is worth one error message.

For status it is backwards twice over. Status is the command a person runs
*because* the folder is in a state, and refusing to describe four hundred files
over one stray binary is the least useful thing it could do. And the current
behaviour makes fixing a folder iterative: five files `record` cannot take
means five runs of `record`, each naming the next one, when what a person wants
is to write five `skip` lines in one pass.

So the walk collects. `Working::read` returns the files it took and the paths
it refused, each with the reason it already knows how to phrase, and `record`
raises the collection it presently raises one member of. Same data, same
refusal, different verb — nothing becomes recordable that was not recordable
before.

Four of the five `WorkingError` variants collect, and one does not.
`NotUtf8`, `Unusable`, and `NotAFile` are facts about a folder that status
exists to report, and `NotText` is the same fact discovered a moment later.
`Io` is different in kind: a directory that cannot be read is not a thing status
knows about the folder, it is status not knowing, and collecting it would
produce a description that is quietly missing whatever was underneath. So `Io`
still returns, and the other four accumulate.

They accumulate from two places, which the shape has to admit. A name, a
symlink, or an unusable path is refused by the walk, before any content is
read. A file that is not UTF-8 text is refused by `working.text` inside the
survey, since knowing that means reading it. `Working::read` therefore returns
the files it took and the refusals it found, and the survey appends its own to
the list before returning it.

```text
$ historica status
5c1e77a2  1f4c2a90  head  journal
edited  docs/decisions/0015-status.md
added   notes/2026-08-20.md
dropped notes/old.md
refused notes/photo.png: not UTF-8 text

notes/old.md and notes/2026-08-20.md hold the same bytes; if that is a rename,
say so with --move notes/old.md=notes/2026-08-20.md
```

The first line is `log`'s first line — change, digest, markers — because a
revision named in two places should be named the same way in both. The rest is
`record --dry-run`'s existing `{fact:<7} {path}`, which `refused` fits without
widening.

Two details of that first line. The digest is abbreviated against every
revision in the store, as `log` abbreviates it, so the prefix status prints is
one `show` and `--onto` will resolve; a fixed eight characters would be a
prefix that stops resolving the week the store grows a collision. And a store
with no revisions has no first line to print, so status says what `log` says —
`no revisions here yet` — and then lists the folder, which against an empty
tree is every file as an `added`. Nothing else about that case is special:
`record` needs no `--onto` when there are no heads, so neither does status.

## Several heads

`cli::record::heads` already decides this correctly for recording: refuse, list
the heads, name `--onto`. Status wants the identical behaviour and the
identical spelling, so the function moves out of `record.rs` into `target.rs`
and both callers use it, gaining the bookmark names on the way.

What moves with it is the rule above it, which is subtler than it looks and
must not be reimplemented: the head is derived only where it is needed, so
`--onto` alone means that revision, `--merge` alone means that revision *and*
the head, and the two together mean exactly what was named. Status resolves its
parents through the same rule, because a status whose parent set differed from
the record it is previewing would be describing a different comparison in the
one place a person went to avoid surprises.

```text
$ historica status
this store has 2 heads, so nothing here is `the` latest; name one with --onto:
  1f4c2a90  journal
  8b3d5e01
```

`--onto` may name any revision, not only a head. Surveying the folder against
something older is the same legitimate act `record --onto` already permits, and
status is the command where a person would want to look before doing it.

The cost is real and belongs in the open: a person with two heads types
`--onto` to every status and every record, and is not remembered between them.
That is 0011's rule collecting its bill. It is already `record`'s bill, this
does not increase it, and the mitigation that is *not* available is writing the
last `--onto` down somewhere.

## The message is not summarised

Status prints the head's change, its digest, and its bookmarks, and says
nothing about its message.

The reason is already in the tree, in the comment on `record`'s editor
template: the format "refuses to interpret a body 0002 promises never to
interpret, and a journal entry beginning with a Markdown heading is the case
that would lose its first line." `log` acts on that — it indents the whole
message and never a first line of it.

A one-line summary in status would be the same interpretation from a command
with less excuse for it, and the alternative — printing the whole message — is
`log`, which is one word away.

## A conflict is still a function of the graph

0012 decided that nothing conflicted is recorded and nothing is remembered, and
`conflict.rs` opens by saying what that buys: "a conflict is a function of the
graph, so the two heads *are* the conflict." Status does not reopen it, and
nothing here is a buffer that outlives a command. The pending merge lives where
0012 put it — the rendered markers sitting in the working-copy files as
ordinary content, and the `record --merge` line printed to the person's
terminal.

Which means status cannot discover a merge, and should not try. `is_marker` is
purely syntactic, so a sweep of every tracked file for lines that look like
markers is a dozen lines of code and would report
`docs/decisions/0012-conflicts.md`, and this document, and any journal entry
about a bad afternoon merging. `unresolved` is deliberately scoped to a merge
record, and the module says why: that scoping is what lets a document about
merge markers be ordinary content the rest of the time.

So the person restates the merge, in the spelling they already typed once:

```text
$ historica status --merge other
5c1e77a2  1f4c2a90  head  journal
8b3d5e01  other
edited  notes/2026-08-20.md
marked  notes/2026-08-19.md (4 left)
```

With two parents the survey has a `Merged` to scope against, so `marked`
counts exactly the lines `record --merge` would refuse on, computed by the same
function. Without `--merge` a marker line is content, and status says nothing
about it, and `record` records it without complaint — which is 0012's rule
holding rather than an exception to it.

The other half of a merge a person has to settle is a path two files claim, and
surveying it turns up something already wrong in `plan`. `Tree::at` returns a
`Vec` precisely because 0008 lets two files hold one path after a merge, and
`merge` prints the contest and offers `--at`. But `plan` builds its
path-to-file map by collecting `placed` the other way round, so where two files
claim a path one of them silently wins, and the working-copy file there is
diffed against whichever the `BTreeMap` kept. `MergedTree.contested` says all
of this and `plan` does not read it.

So the survey carries the contests, and the two callers do what each is for.
`record` refuses a path `--at` has not settled, which is `RecordError::Contested`
saying what it already says for a `--move` onto a claimed path. Status reports
them in the words `merge` uses, since a person reading status is the person
about to type the `--at` that `merge` suggested and status is where they will
look for it again.

## Rejected alternatives

**A stored position — a `HEAD` file, or a `.historica/current`.** The third
thing 0011 refuses, and status is exactly where it would be introduced, because
status is the command that makes its absence felt. Every argument for it is an
argument for not typing `--onto`, and the cost is a file that can disagree with
the graph, silently, forever.

**Remembering the last `--onto`.** The same file, smaller and worse: state
whose only purpose is to be implicit, which is the property that makes state
hard to reason about rather than merely present.

**A syntactic sweep for marker lines.** Above. It flags prose about conflicts,
and there is no threshold of cleverness that fixes that, because a document
quoting a marker line is indistinguishable from a file holding one — which is
the observation 0012 already made when it scoped detection to a merge record.

**Status subsuming `record --dry-run`.** Tempting, since the fact list is
identical. But `--dry-run` answers "what would *this* record state", and this
record may carry `--onto`, `--merge`, `--move`, and `--at`; status answers "how
does the folder differ from head". The flags are the whole difference. Keeping
both costs nothing once they call one function, and collapsing them would mean
either status growing every record flag or `--dry-run` losing them.

**Exiting non-zero when something was refused.** `check` is the command whose
exit code means something, and it earned that by reporting faults and nothing
else; a second command with a fault-dependent code invites scripts to use
whichever one they remember. Status exits zero when it managed to describe the
folder, and non-zero only when it could not — no store, several heads, a store
it cannot read. `record` still refuses, which is where a refusal needs to stop
somebody.

**A stub `Entropy` for status.** Above: it collapses the added map.

**Reporting the store's own faults** — a change with two revisions claiming it,
a head that supersedes something, a document a revision names and the store
does not hold. `log` marks all of it and `check` reports it, and the only
argument for repeating it here is that a person about to record is the person
who most needs to know. Refused because status has one job, and a second one
would make its exit code mean something again — which is the thing the
paragraph above just finished refusing.

**An index, or an mtime cache, to make status fast.** This is the one 0011
answered before it was asked. Both are a third thing that can disagree with the
folder, and the failure mode is the worst available — a status that is wrong
rather than slow.

## Consequences

- `historica status [--onto <target>] [--merge <target>]` is the command, and
  the usage text gains it under "reading a store" even though it reads the
  folder too.
- `record::survey` is the new primitive and `record::plan` is derived from it;
  `facts` moves to `Survey` and `Plan::facts` delegates, since what `record`
  prints after writing is the same list status prints before; `Working::read`
  returns refusals alongside the files it took; `heads` moves from
  `cli/record.rs` to `cli/target.rs`, taking the head-derivation rule with it,
  and learns bookmark names.
- `record` gains a refusal it should always have had: a path two files claim
  and `--at` has not settled is `RecordError::Contested` rather than a silent
  choice between them. This is a behavioural change for a case that could only
  arise after a merge, and the old behaviour recorded work against the wrong
  file rather than saying so.
- Every status replays the full history of every tracked file, because there is
  no index and 0011 is why. At journal scale this is nothing. It is stated here
  so that it is a known price rather than a discovery at ten thousand
  revisions, and so that the first person to propose caching it finds the
  argument already written down.
- The README's front-end paragraph gains `status` in the list of commands that
  read a store.
- Tests worth naming: two runs of status over an unchanged folder produce
  byte-identical output, which is the regression test for minting; a folder
  holding a symlink and a binary file lists both refusals *and* every other
  fact; a store with two heads refuses and names both; status against one head
  states exactly what `record --dry-run` states with no flags; a file holding
  marker lines is ordinary under status and counted under `status --merge`; a
  folder that differs by nothing says so in the words `--dry-run` already uses;
  a `mv` with no edit is suggested as a rename while a `mv` with an edit is not,
  and neither changes the `added` and `dropped` lines; two added files holding
  one dropped file's bytes suggest nothing; an empty added file suggests
  nothing; and a path two files claim refuses under `record` and prints under
  status.

## Deferred

**Checkout**, which is 0008's remaining half and the one that does need a
position — or needs to decide it does not, which is a larger question than this
one and should not be answered as a side effect of it.

**A renderer for very large contested spans.** 0012 deferred this and pointed
it here, so it gets an answer for the half that arrived: status reports a path
and a count and never a span, which is the summary 0012 wanted. What is still
open is what `merge` writes into the file itself when a contested span is
enormous, and that belongs to the renderer rather than to the command that
counts its output.

**Two paths differing only in case**, which 0011 deferred and which status is
where a person would first see — as an add and a drop that look like the same
file. Status showing it plainly may be most of what that deferral needed, but
deciding whether `record` should refuse it is still the case-in-front-of-you
question 0011 said it was.
