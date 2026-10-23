# 0012 — A merge keeps the order of its parents

0005 carried the facts git keeps in a commit's bytes that historica has no
word for, and measured the result on this repository: every commit
round-tripped. Every commit then was on one line. The first two merges, pull
requests #1 and #2, broke the round trip.

A commit's parents are an ordered list. The first is the line the merge was
made on, `git log --first-parent` follows it, and the order is in the bytes
the object ID is the digest of. Historica's revision document holds parents
as a set: `format.txt` sorts repeated lines by the value after them, so
`parent` lines are in digest order. `import` handed the parents over in git's
order and the store wrote them sorted. For about half of all merges that is
the other order. The commit `write` made was a different commit, and so was
every commit after it.

This repository's merge of #1 has `main` first and the merge of #2 second, and
their revisions sort the other way. So the hub's git mirror, which is written
from the store, had other commits than GitHub from that merge on. A colocated
directory did not show it, because its `write` names the commits it already
holds by object ID (0007).

## The decision

- **The order crosses as a header, under 0005's rule.** `git.parents` lists
  the parents in git's order, single-spaced. It is a third fact of the kind
  0005 named, and goes where those went: in the revision's own bytes, under a
  key this tool owns, carried across an amendment by historica's 0023.

- **A parent is named by its change, not its digest.** An amendment or a
  carry gives a revision a new digest and keeps its change. A header of
  digests would stop describing the merge the first time either parent was
  rewritten. A header of changes still names the line the merge was made on.
  A change ID is letters only, so the value needs no quoting.

- **Every merge carries it, not only one the sort disagrees with.** Whether
  git's order matches the digest order today depends on the digests, and a
  rewrite changes them. A merge without the header would then flip its order
  with no record that it had one. One line per merge is the cost, and a
  revision with one parent is byte-for-byte what it was.

- **`write` uses the header only where it names exactly these parents.**
  Each parent's change must appear once, and nothing else may. A rewrite can
  leave a merge with other parents than git named: a `carry` onto a different
  base, or a merge whose parents are two versions of one change. Then the
  header describes a different merge, and using part of it would be a guess.
  The commit takes historica's order, and the conversion says how many did.

- **A revision without the header is written in historica's order, and that
  says nothing.** It is a merge historica made, which never had a git order,
  or one imported before this decision. `write` cannot tell the two apart.

## Consequences

- A fresh import of a repository with merges records different revisions than
  the release before this did, because every merge has the header. Converting
  a repository twice with one release still writes one history (0003).
- A store imported before this decision keeps its merges without the header,
  because a revision is immutable. Its commits are written in historica's
  order, as before. Superseding the merges would not help: a revision that
  supersedes another loses its signature (0005), so its commit would differ
  anyway. A fresh import into an empty folder writes the header.
- This repository round-trips again: all 52 commits, two of them merges, come
  back with their object IDs, and the signed ones still verify.

## Deferred

- **Saying which merges an old store holds without the header.** A second
  `import` recognises a held commit by its object ID and does not read the
  revision again. Comparing each held merge's parents with git's would be a
  walk over every merge on every run, which is a cost to argue for, not to
  slip in.
