# 0011 — A colocated store follows the folder

0008 put a store and a repository in one directory, and said historica owns
the working copy. Two facts about that directory were left to git, and
historica does not read either of them:

- **Which line of work the folder holds.** git says it with HEAD. In historica
  1.0.0-rc.8 a store has no position: its head is the tip that no revision
  stands on. A colocated import brought in every branch, and a repository
  whose `.git` is shared by worktrees has a branch for each one. The first
  time we tried to colocate this repository's own checkout, the branch of an
  open pull request was one commit ahead of `main`. Its tip became the store's
  only head, `historica status` reported the pull request's changes as
  reversed in the folder, and a bare `record` would have recorded that
  reversal and written it to git.
- **What is not part of the project.** git says it with its ignore files. A
  `record` after `cargo build` took `target/`. A `record` after a `.env` was
  written would take the secret, into a history that is append-only.

Historica's 0086 answers the first question for every copy, with a rule that
says which tips a copy follows. It is not released. This decision is what
historica-git does until then, and it stays correct after: it narrows what
crosses, so it does not depend on how historica chooses heads.

## The decision

- **A colocated import follows the branch HEAD is on.** It also follows every
  branch the store already has a bookmark for, and every tag those branches
  reach or the store already names. Nothing else is given to `git
  fast-export`. A branch that is not followed stays in git:
  - If the store holds its work anyway, it is a standing note (0010).
  - If it names work the store does not hold, it is a note on every run, by
    name, like a remote-tracking ref that is ahead. It crosses when a followed
    branch reaches it, or when HEAD is on it for an `import`.
- **A HEAD on no branch follows everything**, as before. There is then no
  branch to say which line is the folder's.
- **A separate folder is unchanged.** 0006 still crosses every branch and tag
  there. That folder is nobody's checkout of one branch.
- **A colocated import turns git's ignore files into skip rules.** It reads
  them in git's order of precedence: the global excludes file, then
  `info/exclude`, then the root `.gitignore`. A rule from `.gitignore` is
  shared, because the file is the project's. A rule from the other two is
  private, because each is a fact about one machine, like 0008's `.git` rules.
  0008's own `/history/` line is not read.
- **Only what a rule says exactly is carried.**
  - `name` becomes `skip-name name` and `skip-name name/`. `name/` becomes
    only the second.
  - An anchored `path` becomes `skip path` and `skip path/`.
  - `**/name` is `name`, and `path/**` is `path/`.
  - Nothing else is carried: `?`, `[…]`, an escape, `**` between
    directories, a wildcard in an anchored path, or a nested `.gitignore`.
    Historica's patterns have only `*`, and a rule by name applies everywhere,
    not only below one directory.
  - A line that a later `!` could re-include is not carried. Historica has no
    negation, and the rule would keep out what git lets in.
  - A rule that covers a tracked file is not made. git keeps a tracked file
    whatever its ignore files say, and the rule would record the file's
    deletion.
  - Each line not carried is a standing note, by file and line, for
    `historica skip` to say by hand.
- **Every colocated import reads the ignore files again.** It adds only the
  rules the store does not state, and reports only those. A `.gitignore` that
  gained a line after a `git pull` reaches the store on the next import.

## Why not pass `--onto` from the wrapper

The wrapper could add `--onto <HEAD's branch>` to `record`. That fixes `record`
and nothing else. `status`, `diff`, `log` and `update` default to the head too,
and `update` would write the other branch's files into the folder. Narrowing
what crosses keeps every command correct without a flag.

## Why the ignore rules are made here and not left to the person

0001 asks a conversion to say what it could not carry. A skip rule is not a
fact of history, so leaving it out is not a loss in that sense. It is a fact of
the directory, and the directory is what colocation makes. The failure it
prevents cannot be undone: history is append-only (historica's own 0011), and
a recorded secret stays recorded.

## Consequences

- In this repository's checkout, colocating gives one bookmark, `main`, and
  one head. Each agent's branch is named on each import until its work reaches
  `main`.
- A branch that HEAD was on once stays followed, because the store has a
  bookmark for it. After `git switch main`, that branch can be ahead and be the
  head again. `historica name --delete` does not end it, because the work is
  still a tip without its bookmark. Until 0086, the work has to be merged into
  `main` or abandoned in the store.

## Deferred

- **A followed branch that is ahead of HEAD's.** This is the consequence
  above. 0086's rule is the answer. Before then, a note when HEAD's branch is
  not the store's only head would at least say it.
- **A line removed from an ignore file.** The rule stays. historica has
  `add_skipped` and no published way to remove a rule.
- **A commit that adds a file a rule covers**, with `git add -f`. The import
  checks only the tracked files at the time of the import.
- **The other direction.** `colocate` on a store makes the repository, and
  does not turn skip rules into `info/exclude`.
