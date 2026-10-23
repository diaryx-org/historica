# 0010 — A note said once

0001 makes a conversion state what it could not carry, because the person
holding the result otherwise believes it is the thing it came from. 0007 made
a conversion something run again and again onto what it made before, and 0009
put a run after every historica command. Between them, a note written for a
conversion somebody runs once is now printed many times a day.

Two notes print every time in a colocated directory, whatever the run did:

- After each `historica record` through the wrapper, `1 note on what git cannot
  hold`, which is always the same note: change IDs did not cross.
- After each `import` that follows a `git pull`, `refs under
  refs/remotes/origin/ did not cross`, because every clone has a remote.

Neither says anything about the run that printed it. A note that is always
there is one that a person stops reading, and then they also miss the note
that is about this run.

The second note also made a claim it did not check: *every commit they named
is in the store*. After a `git fetch`, `refs/remotes/origin/main` names work
that no branch has reached, so the claim was false exactly when a person most
needed to hear about the remote.

## The decision

- **A note is either about this run or standing.** A standing note is true of
  every run against the same repository or store, whatever it holds: change
  IDs do not cross, and refs that are neither branches nor tags do not cross.
  Every other note is about the data this run read: a committer, a
  signature, a tag, a link, a branch that could not be moved. These notes
  stay as they were.
- **A whole conversion says every note. A run onto what it made before says
  only the notes about this run.** The whole conversion is the one that made
  the result, so the person holding the result was told then. The run after
  it changes nothing that the standing note is about. `Report::standing`
  holds standing notes apart from `Report::uncarried`, and the command line
  prints them only when `onto` is false. The `--wrote` summary counts only
  `uncarried`, so a record that crossed cleanly prints no note line.
- **A ref that is neither a branch nor a tag is asked about.** Where the store
  holds its commit, it is reported by directory as before. That note is
  standing. Where the store does not hold the commit, the note says what only
  that ref reaches did not cross either, and does not claim otherwise. A
  remote-tracking ref that names work the store does not hold is a note
  about this run, by name, because it is the remote being ahead of every
  branch. The note says that `git merge` or `git pull`, then `import`, is
  what brings the work across. `refs/remotes/<remote>/HEAD` is left out of
  that note: it is git's record of which branch the remote checks out, and it
  names whatever that branch names.

## Why this keeps 0001

0001's failure is a person who believes the result is the thing it came from.
The standing notes are about what a git repository and a historica store are,
not about a repository's contents. A person told once, when the result was
made, still knows it on the hundredth run. Nothing that changes between runs is
made quieter. The one note this decision makes louder, the remote that is
ahead, is the one that was wrong before.

A whole conversion is always one command away. A fresh target, or `colocate`
in a directory that holds only one of the two, prints every note again.

## Rejected alternatives

- **Quiet only the `--wrote` run.** That run already prints a count rather
  than the notes, so this half-fix would leave the count. It would also leave
  the remote note on every `import` that follows a `git pull`, which is the
  other half of a developer's day.
- **Say a standing note once per repository, and remember that it was said.**
  This works, but it needs a third file under `.git/historica/` that records
  something other than a correspondence. The difference between a whole
  conversion and a run onto what it made before already marks the line between
  the first run and every later one.
- **Drop the standing notes entirely.** 0001 asks for them, and the first
  conversion is where a person decides whether the result is what they want.

## Consequences

- `import`, `write`, and `write --wrote` onto what they made before print
  nothing under *what did not cross* unless this run found something.
- After a `git fetch`, `import` names each remote-tracking ref that is ahead of
  every branch. It names the ref again on each import until a branch reaches
  the work, as `git status` says a branch is behind until it is not.

## Deferred

- **A remote added after the first conversion** is standing, and so it is
  never said by a run onto what it made before. Nothing is lost that `git
  remote` does not already show, but it is a fact the first conversion did
  not have.
