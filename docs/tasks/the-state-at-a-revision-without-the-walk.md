---
title: The state at a revision without the walk
description: Answer "file F at revision R" — its content digest and its path — by lookup rather than by loading every reachable revision, most likely as a derived index under `cache/`
status: open
created: 2026-09-16
updated: 2026-09-16
part_of: "[Tasks](tasks.md)"
---

# The state at a revision without the walk

`Store::tree` and everything built on it — `cat`, `status`, `update`,
`content_at` — answer by `reachable_from(head)`, which loads every revision
document reachable from the head, and then `tree::merge`, which replays every
tree event in causal order. That is linear in the length of the history, on
every command, and a history only gets longer. [0035](../decisions/0035-the-cache-is-a-file-already-named.md)
bounded the *content* replay with checkpoints and
[0036](../decisions/0036-where-a-digest-is.md) removed the cost of finding a
digest; the walk that finds *which* digest, and *where* the file is, still
stands.

It is a smaller problem than it looks, because the format already states
most of the answer. Since [0031](../decisions/0031-a-document-states-its-result.md)
every operation document names the digest of the file it produces, and since
[0032](../decisions/0032-a-merge-states-its-resolution.md) a merge that
touched a file names its resolution. So for a single revision R, file F's
content is the `result` of the nearest `edit F` or resolution in R's
ancestry — unique, because a merge that did not mention F has the answer on
exactly one side — and its path is the nearest `add F` or `move F`. Both are
one question: *the nearest ancestor of R that says something about F*. The
walk exists to answer that, and nothing else.

## The shapes

Three, in order of how little they change. The first is the one to build; the
other two are recorded so the choice is visible.

**A derived index under `cache/`, no format change.** Two catalogues: a
per-file log — for each file identifier, every revision that mentions it, the
document it names and the path it states, in topological order — and an
ancestry labelling of the revision graph (generation numbers, as Git's
`commit-graph` keeps them, or interval labels), so that *is A an ancestor of
R* is a comparison and not a search. Then F at R is a scan back through F's
log for the first entry whose revision is an ancestor of R, and the whole
tree at R is that once per file. It is a cache in 0003's sense — deleting it
loses nothing — and it follows 0036's rules exactly: named rather than
digest-named, carrying a header, believed only while the set of revisions it
names is the set the store holds, hashing what it points at before believing
it, and read by nothing `check` does. An in-process host whose `Filesystem`
declines to hold it gets the walk it has today.

**A revision states its result tree.** 0031 one level up: a `tree <digest>`
header on the revision document naming a flat `file path content-digest`
list, filed under `cache/` by its digest and rebuilt by the walk on a miss.
State at R becomes a single lookup, and a hand verifier gets what they do not
have today — something to check a tree replay against. [0008](../decisions/0008-tree.md)
refused restating every path *inside the revision document*; a stated digest
is one line. But it raises the format version, and an object stored rather
than cached is Git's tree without subtree sharing, which is the size argument
0008 made coming back. Worth a proposal if the index above turns out not to be
enough; not worth it first.

**An edit names its predecessor for that file** (`after <digest>`). Makes a
file's history a linked list, so `log` and `blame` on one file stop searching
the graph. It does not answer *at R* without still finding the entry point, so
it only helps beside one of the other two, and is not on its own worth a
version.

## What this does not remove

- The content replay from the nearest checkpoint. 0035 already bounds it, and
  that bound is the right one.
- The merge computation when the question is asked of a *set* of heads.
  There is no single state there to have indexed; `merged_tree_of` on several
  heads still merges, but from the indexed state of each head rather than
  from the root.

## Done when

- `cargo xtask bench` shows `cat` and `status` at the head of the bench store
  no longer scaling with the number of revisions — the measurement 0035 and
  0036 were each written against, extended with a history long enough to
  show it.
- `Store::tree`, `content_at` and `merged_content` answer from the index when
  the store holds one, and identically without it; the corpus passes both
  ways.
- Deleting `cache/` changes nothing but the time.
- `check` neither reads nor writes the index.
- A decision records the shape chosen and what it refused, with the two
  alternatives above named as the road not taken.
