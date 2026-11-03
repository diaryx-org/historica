# 0014 — A commit is recorded by the paths it changed

`import` recorded every commit as a person runs `historica record` with no
paths named. The record surveyed the whole folder: it hashed every file to
compare it with the history, and it asked the store about every file it
found. A commit that changed one file paid for all of them, so a conversion
cost commits × files. diaryx, at 3,578 commits, took 31 minutes.

Git already says which paths a commit changed. Its tree and its parent's
tree are both in the replay, and the paths where they differ are the paths
the commit has anything to say about.

## The decision

- **A commit with one parent is recorded with the paths it changed named.**
  These are the paths whose entry differs between the parent's tree and the
  commit's, and both ends of every rename. This is historica's own
  `record <path>…`, and it states what the whole survey would have stated.
  The revision's tree is its parent's, which is git's parent's tree
  (0013), so no path outside that set differs from what the parent holds.

- **Every link is named too.** Historica's 0040 writes a link's target down
  by the file it names, so a record that drops or moves a file has to look at
  whatever points at it. `record` refuses rather than guess which those are.
  diaryx has generated bindings that are links into another crate, and
  dropping one of their targets was refused until links were named.

- **A submodule alone is not named.** The folder holds nothing for one, and
  `record` refuses a named path that answers to nothing.

- **A merge is recorded whole.** Historica's 0032 has a merge state every file
  its parents leave differently, and `record` refuses a merge that names
  paths.

- **The whole folder where that is cheaper.** A commit that changed nothing
  but a submodule, or more than a quarter of its tree, is surveyed whole. The
  answer is the same either way, and checking each folder path against a long
  list costs more than looking at everything.

## Consequences

- A converted store is byte for byte what it was: prov and leaf convert to
  the same history before and after.
- With historica's 0092, converting diaryx takes 7 minutes rather than 31,
  prov 2.8 seconds rather than 11.7, and leaf about 10 rather than 42.
- The folder is still walked once per commit, because `record` reads it
  through `Working`. Only the files named are hashed.
