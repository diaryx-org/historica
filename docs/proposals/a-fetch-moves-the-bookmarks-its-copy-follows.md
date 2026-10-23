---
title: A fetch moves the bookmarks its copy follows
part_of: '[Proposals](/docs/proposals/proposals.md)'
status: implemented
description: Once a copy chooses its heads (0086), a fetch moves a bookmark it holds where the copy follows the publisher's reading and the move only goes forward, so a reader keeps up with a publisher, and a publisher's correction reaches the readers who follow it, without transport ever overwriting the reader's own work
created: 2026-10-21
updated: 2026-10-22
---

# A fetch moves the bookmarks its copy follows

## Status

Implemented 2026-10-22, unreleased, as decision
[0088](/docs/decisions/0088-a-fetch-moves-the-bookmarks-its-copy-follows.md),
which is the authority from now on. Argued 2026-10-21 after a day of real
work through the hub with historica-git. It needed [0086], which is on `main`
and unreleased, and the two travel in one release.

The open questions were settled by Adam on 2026-10-22:

1. **A bookmark the publisher deleted** stays where it is, and the fetch
   reports it, as proposed. Only a paged manifest's `gone` line can say a
   name was deleted, so a fetch from a whole listing reports nothing.
2. **What "forward" costs:** one ancestry walk per fetch, shared by every
   bookmark it weighs, rather than one per bookmark.

The build differs from the body below here:

- **The library takes the rule per call.** `Store::fetch_following` is the
  new way in, and `fetch` and `fetch_with` keep 0062's behaviour, so an
  embedder that has not said what it follows sees no change.
- **The reasons are four, not two.** Besides *not forward* and *not
  followed*, a bookmark is kept as *pinned* (a revision or a file on either
  side) or *unresolved* (a change with no single current revision).
- **A fetch now takes two bookmarks naming one change.** It kept one per set
  of bytes, which dropped all but one of them.

## What happened

historica-git's own repository is published on the hub. On 2026-10-21 its
store was imported again from git, to repair two merges an older conversion
had written with their parents out of order, and the hub was given the new
store. Then a copy fetched before the repair fetched again:

```console
$ historica fetch https://…/adam/historica-git/offer.txt
fetched 6 revisions
kept this copy's own reading of 1 bookmarks the publisher also states
```

The copy now had two heads, its old `main` and the publisher's, and nothing
said which one replaced the other. Earlier the same day the same thing
happened with no repair at all. The publisher recorded one revision on `main`,
a reader fetched it, and the reader's `main` stayed where it was. The new
revision arrived as the tip, and the bookmark did not follow it.

Both are [0062] working as written. `fetch` takes what is missing, a bookmark
the copy holds is not missing, and the publisher's reading is counted and
dropped. 0062 rejected the alternative in one sentence:

> A fetcher who took it once and then recorded onto it has a `main` of their
> own, and a fetch that moved it back would be the only place in this design
> where transport overwrites a mutable value without asking.

That is right about moving a bookmark *back*, or sideways off the reader's own
work. It does not cover the commonest case, in which the reader has recorded
nothing and the publisher's `main` is simply further along the same line. For
that case, historica has no spelling of `git pull`. The reader runs `names`,
compares, and types `historica name main <change>` by hand, every time the
publisher records.

## The proposal

- **A fetch moves a bookmark it holds when the move is forward along a line
  the copy follows.** Both conditions are needed:
  - *Forward.* The revision the copy's bookmark resolves to is in the ancestry
    of the revision the publisher's bookmark resolves to, after the fetch. A
    reader who recorded onto `main` has a revision there that the publisher's
    line does not contain, so their bookmark is not an ancestor and does not
    move. That is 0062's case, and it keeps 0062's answer.
  - *Followed.* The copy follows the publisher's revision under its rule
    ([0086]). Work the copy holds as held does not become the copy's `main`
    by arriving under a name, which is the reason 0086 rejected heads under
    bookmarks: the contributor would decide what the maintainer stands on.
- **Otherwise the copy keeps its reading, and says which, by name.** Today
  the report is a count. It becomes one line per bookmark kept, with both
  readings and the reason: *not forward* (the reader's own work is on it), or
  *not followed* (the publisher's revision is held here).
- **A pinned bookmark never moves.** A bookmark naming a revision (0062's
  `--revision`, which historica-git writes for a git tag) is pinned on
  purpose. A file bookmark has no line to be forward on. Only bookmarks naming
  a change are in scope.
- **`receive` is unchanged.** It reconciles two of one person's replicas, and
  0062's conflict is the right answer there: two machines disagreeing about
  `main` is something to see.

## Why this makes corrections reach readers

A bookmark names a change, not a revision. When a publisher amends, squashes or
carries, the change keeps its ID and the bookmark keeps its target. What moves
is which revision of that change is current, and under 0086 that is decided by
supersession, counted only where the copy follows the revision that states it.
So for a reader who follows the publisher, a correction published as a
rewrite needs no bookmark to move at all. The superseding revision arrives, it
is followed, and the old one stops being current. The reader's `update` brings
the folder there. This proposal covers what remains: work added on top of the
correction, which is ordinary forward motion.

A correction published as *new history*, which is what happened above, does
not converge this way and should not. The repaired store was a fresh import,
so its revisions supersede nothing. To the reader it is a second line, and two
heads is the true description of it. The lesson for a publisher is to correct
by rewriting, so that the correction says what it replaces. Whether
historica-git can do that is its own question. A rewritten revision loses its
git signature under that tool's decision 0005, so a correction that readers
follow cannot also reproduce the signed commits on GitHub.

## Rejected alternatives

**Remote-tracking names**, git's `origin/main`: the publisher's reading kept
under a name of its own, beside the copy's. It is the honest record of what
the publisher said, and it is a stored copy of somebody else's mutable value,
the third thing [0030] refuses. The publisher's reading is already in the
manifest, and a fetch can report it without keeping it.

**Moving every bookmark the publisher states.** 0062's rejected alternative,
and still rejected, for its reason.

**A flag, `fetch --follow-names`.** Which bookmarks a copy lets the publisher
move would be decided per command, so two fetches of one publisher could leave
the copy in two states. Following is already a property of the copy (0086),
and this proposal asks it.

## Open questions

1. **A bookmark the copy holds and the publisher deleted.** [0080]'s pages
   say it: a `gone` line for the name's file, and no new entry at that path.
   Deleting the copy's bookmark when it is still an ancestor of what the
   publisher last named would be the same forward-only rule. But a
   [0073] deletion is local by design, and a fetch that deleted names would
   make it travel. The proposal leaves such a bookmark where it is, which is
   what a fetch does today, and reports it.
2. **What "forward" costs.** The test is an ancestry walk from the publisher's
   revision, per bookmark the publisher states. For the handful of bookmarks a
   repository shares, that is nothing. A store whose publisher shares
   thousands, one per change set, would want the walk shared across them.

## Not this

**Taking a contribution.** That is [0086]'s `carry`, and the hub's side of
it is historica-view's proposal *A forge of forks and remarks*.

**Fetching less than everything.** Which revisions and content a fetch takes
is the companion proposal,
[History held elsewhere](/docs/proposals/history-held-elsewhere.md).

[0030]: /docs/decisions/0030-the-folder-catches-up.md
[0062]: /docs/decisions/0062-two-axes-for-a-bookmark.md
[0086]: /docs/decisions/0086-a-copy-chooses-its-heads.md
[0073]: /docs/decisions/0073-taking-a-name-back.md
[0080]: /docs/decisions/0080-a-listing-in-pages.md
