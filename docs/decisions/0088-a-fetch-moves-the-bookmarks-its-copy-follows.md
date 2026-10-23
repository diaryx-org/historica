# 0088 — A fetch moves the bookmarks its copy follows

[0062](0062-two-axes-for-a-bookmark.md) made a fetch take only the bookmarks
a copy lacks, so that transport never overwrites a mutable value without
asking. That is right about moving a bookmark *back*, or sideways off the
reader's own work. It left the commonest case without a spelling: a reader
who recorded nothing, whose publisher's `main` is further along the same
line. The reader ran `names`, compared, and typed `historica name main
<change>` every time the publisher recorded. The argument is the proposal
[A fetch moves the bookmarks its copy follows](../proposals/a-fetch-moves-the-bookmarks-its-copy-follows.md),
written after a day of real work through the hub with historica-git.

## The decision

**A fetch moves a bookmark it holds when the move is forward along a line
the copy follows.** Both conditions, after the fetch has taken everything:

- *Forward.* The revision the copy's bookmark resolves to is a strict
  ancestor of the revision the publisher's resolves to. A reader who
  recorded onto `main` has a revision there the publisher's line does not
  contain, so their bookmark does not move. That is 0062's case, with 0062's
  answer.
- *Followed.* The copy follows the publisher's revision under its rule
  ([0086](0086-a-copy-chooses-its-heads.md)). Work the copy holds as held
  does not become the copy's `main` by arriving under a name.

**Only a bookmark naming a change on both sides moves.** A bookmark naming a
revision is pinned on purpose, and one naming a file has no line to be
forward on. A change with no single current revision on either side,
divergent or abandoned, has nothing to resolve to, and its bookmark stays.

**Otherwise the copy keeps its reading and says which, by name.** The report
was a count. It is now one line per bookmark kept, with both readings and the
reason: not forward, not followed, pinned, or unresolved. Two readings that
agree, which includes one the publisher states in the same bytes, are
neither moved nor kept, and are not counted.

**A bookmark the publisher deleted stays, and is reported.** A deletion is
local by design ([0073](0073-taking-a-name-back.md)), and a fetch that deleted
names would make it travel. A page's `gone` line for the name, with no later
page stating it again, is what says the publisher deleted it
([0080](0080-a-listing-in-pages.md)); a whole listing only leaves a name out,
which cannot be told from a name never shared, so a fetch from one reports
nothing.

**A move keeps the copy's travel axis.** The fetch moves a bookmark with
`Store::set_name`, so a name this copy made private stays private.

**`receive` is unchanged.** It reconciles two of one person's replicas, and
0062's conflict is the right answer there.

## The library

`Store::fetch_following(source, manifest, asked, &rule)` is the new way in.
The rule is the caller's, as every other question 0086 asks is, so the
library learns what the copy follows from the call and stores nothing.
`Store::fetch` and `Store::fetch_with` are unchanged: they read no
publisher's bookmark the store already holds, move none, and count the ones
whose bytes differ.

`Fetched` gains `moved`, `kept_names` and `withdrawn`. `FetchPlan` gains
`contested`, the bookmarks the store holds that the publisher states in other
bytes: the ones whose files `fetch_following` reads.

The publisher's file for a contested bookmark is read after the plan is
taken, since the revisions it names must be here to resolve it, and one that
has gone is a moved path like any other: the manifest is read again. The
moves are made only once `check` has passed, so a fetch that fails moves
nothing.

## What "forward" costs

The test is an ancestry walk from each publisher's revision, and a publisher
sharing one bookmark per change set would make that a walk per bookmark. So
it is one walk for every bookmark a fetch weighs. Each distinct publisher's
revision is one bit, every revision carries the bits of those standing on it,
and a revision is walked again only when it gains a bit. The cost is the
ancestry the publisher's revisions cover, times their number in machine
words rather than in walks.

## The CLI

`fetch` passes the rule the copy follows, which is 0086's: its own author and
the `follow` names once an identity block lists them, and every tip until
then. Under every tip, a reader who recorded nothing keeps up with `fetch`
and `update`, which is `git pull` with the two halves named.

```console
$ historica fetch https://…/offer.txt
fetched 1 revisions
…
moved main forward from change kmrq… to the publisher's change lwxn…
kept draft at change pqts…, not the publisher's change lwxn…: it is not behind the publisher's, so work of this copy's own is on it
```

`fetch --fields` lists a moved bookmark as a `name` line, which
`historica-wrote-1` already defines as a bookmark written or moved.

## Fixed on the way

A fetch kept one entry per digest, which is right for content and wrong for a
bookmark, whose path is its name. Two bookmarks naming one change are the
same bytes, so a reader took only one of them. It now takes every bookmark it
lacks.

## Rejected alternatives

**Remote-tracking names**, git's `origin/main`. A stored copy of somebody
else's mutable value, which [0030](0030-the-folder-catches-up.md) refuses.

**Moving every bookmark the publisher states.** 0062's rejected alternative,
still rejected for its reason.

**A flag, `fetch --follow-names`.** Following is a property of the copy
(0086), so two fetches of one publisher must not leave the copy in two
states depending on what was typed.

**Deleting a bookmark the publisher deleted, where it is still an ancestor
of what the publisher last named.** The same forward-only rule applied to
deletion. It would make 0073's local deletion travel, and a whole listing
cannot see a deletion at all, so it would work only from a paged manifest.

## Consequences

- A reader following a publisher sees `main` move on every fetch that
  brings the publisher's work, and the folder follows on `update`.
- A correction published as a rewrite needs no bookmark to move: the
  bookmark names a change, the superseding revision arrives, and it becomes
  current. A correction published as new history is a second line, and two
  heads is the true description of it.
- 0062 gains a `## Since` naming this document.
