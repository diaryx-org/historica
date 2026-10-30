# 0013 — A merge git settled is recorded as git settled it

`git fast-export` states a merge as its difference from the first parent.
Historica records a merge against the tree its parents leave between them,
which is decision 0008's merge in historica and not git's first parent. Where
the two trees agree, the difference converts as it stands. Where they do not,
`record` refused, and it refused on seven of nine repositories in this
organisation. There were two ways to disagree:

- **A rename whose source the merged tree does not hold.** In prov, one side
  closed a task by moving it into `docs/tasks/closed/` and the other deleted
  it. Against the first parent the merge is a rename. In the merged tree the
  file is gone, so `--move` named a path nothing held, which was
  `NotInTheTree`.
- **A path two files claim.** Two sides that each add `Command.ts`, or two
  histories merged in that each hold `.claude/settings.json`, are one file to
  git and two to historica, since a file is its identifier (historica's
  0008). The merge is then `Contested`, which historica's 0012 leaves for a
  person to settle with `--at`.

A third case was waiting behind them: two sides that each change a file of
bytes leave a payload a merge must `accept`.

Git's tree already says what the merge holds, and the folder is made to hold
it. What the conversion has to supply is what a folder cannot say: which file
is which.

## The decision

- **A merge's renames are stated by file, not by path.** Each of git's renames
  is the file the first parent held at its source. Where the merged tree holds
  that file, at any path, `at` places it at the destination. Where the merged
  tree holds it nowhere, the rename is not stated, and the destination arrives
  as a file git's tree has and historica's does not: an `add`. Identity is
  kept wherever historica still has the file, and is not invented where it
  does not.

- **A path two files claim keeps one, and the first parent's.** The first
  parent is the line the merge was made on, which 0012 already treats as a
  fact worth carrying. Where neither file came from it, the least identifier
  wins, so converting twice still writes one history (0003). The others are
  placed at a path the merge commit does not hold, so the walk finds them
  missing and drops them. A `drop` line names no path, so the placeholder is
  written nowhere.

- **A contested file of bytes is accepted from the folder.** The folder holds
  what the merge commit holds, which is the answer git gave. The conversion
  asks only after `record` refuses, since only a merge of bytes is ever
  refused for it.

- **A commit with one parent is converted as before.** Its tree in historica
  is its parent's, which is git's, so stating its renames by path loses
  nothing and its revision is byte-for-byte what it was.

## Consequences

- prov, fig, thorn, twig, leaf and this repository convert where they
  refused. prov and this repository round-trip to the same object IDs.
- The file a merge drops is still in the history: the side that added it
  holds it, and `log --path` there finds it. What the merge says is that git
  kept one, which is what git said.
- A rename of a file the other side deleted becomes an `add`, so `blame` on it
  starts at the merge. That is the identity historica can state, since the
  file it would have continued is one the merged tree dropped.

## Also here

`write` parks every commit on one staging ref, and fast-import continues a
ref's tip when a commit names no parent. A second root, as in a repository
with other histories merged into it, came back standing on the first. A root
after the first is now preceded by a `reset` with no `from`, which clears the
ref. This repository has four roots, and before it round-tripped none of its
commits after the first root's.

An annotated tag on a commit the store holds is excluded with the commit, and
`git fast-export` refused the whole export over a tag whose object it was told
to leave out. `import` passes `--tag-of-filtered-object=drop`. Nothing is lost:
an annotated tag does not cross (0006), and git's refs, not the stream, are
what count it.
