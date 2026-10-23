---
title: A merge comes back with its parents in another order
part_of: '[Tasks](/historica-git/docs/tasks/tasks.md)'
created: 2026-10-21
status: done
description: historica sorts a revision's parents by digest, so write can give a merge its parents in another order than git had, and a different object ID
---

# A merge comes back with its parents in another order

**Status.** Done, by `fix(merge): keep the order of a merge's parents`.
[Decision 0012](../decisions/0012-a-merge-keeps-the-order-of-its-parents.md)
carries the order as `git.parents`, by change, on every merge. A merge already
recorded without it keeps historica's order; a fresh import is the remedy, and
saying which merges those are is deferred there.

A commit's parents are an ordered list in git: the first is the line the merge
was made on, and the order is part of the bytes the object ID is the digest of.
Historica keeps a revision's parents as `parent` lines, which `format.txt`
sorts by the digest that follows each one. `import` hands them over in git's
order and the store writes them sorted, so `write` gets them back sorted. For
about half of all merges that is the other order, and the commit `write` makes
is a different commit, as is every commit after it.

[Decision 0005](../decisions/0005-the-facts-git-keeps-that-historica-has-no-word-for.md)
is the class this belongs to: a fact git keeps in the commit's own bytes and
historica has no word for. It names the committer and the signature, and not
parent order, because no repository it was tried on had a merge whose first
parent sorted second.

## Repro

This repository's own merge of pull request #1, `0673301`, has parents
`612e297` (main) and `c9e1652` (the merge of #2). Their revisions sort the other
way.

```console
$ git clone --no-local historica-git g
$ historica-git import g s && historica-git write s g2
$ git -C g2 cat-file -p main~1 | grep ^parent
parent 3c2de3b…    # c9e1652 written again, which also changed
parent 612e297…
```

`diff <(git -C g rev-list --all) <(git -C g2 rev-list --all)` is not empty, as
the README says it is for a repository historica can hold entirely. The hub's
git mirror is written this way, so `git clone` from the hub gives commits other
than the ones on GitHub from that merge on. A colocated directory is not
affected: its `write` names the commits it already holds by object ID.

## The work

- **A decision**, under 0005: where the order goes. A `git.parents` header
  listing the digests in git's order where it differs from the sorted one is
  the obvious shape. Writing it only where it differs keeps a revision of a
  linear history byte-for-byte what it is now.
- **What happens to a merge already recorded without it.** A revision is
  immutable, so a store that already holds one keeps writing it the wrong way
  unless the import supersedes it. Say what a second `import` does with one.
- A corpus test with a merge whose first parent sorts second.

## Done when

- `historica-git import repo store && historica-git write store again` gives
  identical `rev-list --all` output for this repository, and for a fixture
  whose merges sort both ways.
