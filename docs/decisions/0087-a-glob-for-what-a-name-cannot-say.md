# 0087 — A glob for what a name cannot say

The rules in `history/skipped/` were meant to be a gitignore a person can
read: one rule to a file ([0045](0045-one-rule-to-a-file.md)), anchoring said
by the key rather than inferred from where a slash falls, and no order
([0011](0011-working-copy.md)). [0051](0051-two-axes-for-a-rule.md) kept the
matcher to one path component with `*` as its only metacharacter, so that a
stranger could write it in ten lines.

That leaves lines git says and historica cannot. Across the `.gitignore`
files of this organisation, about 130 of some 176 distinct lines are a `skip`
or `skip-name` rule exactly. The rest are of three kinds:

- a wildcard in an anchored path: `src/generated/*.wasm`,
  `/spikes/*/target/`;
- `**` between or around directories: `**/.claude/settings.local.json`,
  `/examples/output/**/*.png`;
- `!`, mostly the allowlist idiom: `/*`, then `!/docs/`, `!/README.md`.

Each is a file git leaves out and historica records, the first time one
appears. Listing today's matching paths as `skip` rules does not close the
gap: it is a snapshot, and the file git would ignore tomorrow is recorded into
a history that is append-only. The first of these to bite was a
`.claude/settings.local.json` below the root, which holds the permissions one
person granted on one machine.

No new readable spelling exists for these lines. Anything that can say
`a/**/b` is as dense as `a/**/b`. What makes gitignore hard to read was never
the glob; it is the inferred anchoring, the order, and a later `!` undoing an
earlier line. A glob can be admitted without any of the three.

## The decision

- **Two keys: `skip-glob <pattern>` and `private-glob <pattern>`.** The value
  is one gitignore pattern, meaning what it means in a `.gitignore` at the
  repository root. `private-glob` stays out of an export, as 0051's other
  `private` keys do. The keys are now three kinds of matching by two kinds of
  travel, and the set closes there again.

- **The meaning is git's, stated here so it can be implemented without git:**
  - The value is matched against paths relative to the root, with `/` as the
    separator.
  - A trailing `/` makes it match only a directory, and is removed before
    matching.
  - If a `/` remains at the start or in the middle, the pattern is anchored
    and matched against the whole path. Otherwise it is matched against every
    path's last component, which is to say at any depth.
  - `*` matches any run of characters except `/`, including an empty run and a
    leading dot. `?` matches one character except `/`.
  - `[...]` matches one character from a set: single characters, ranges such
    as `a-z`, and POSIX classes such as `[:alpha:]`. A `!` or `^` first
    negates the set. A set never matches `/`.
  - `**` is special only as a whole component. A leading `**/` matches any
    number of directories, including none. A trailing `/**` matches everything
    beneath. A middle `/**/` matches any number of directories,
    including none, so `a/**/b` covers `a/b`. Anywhere else, `**` is two `*`.
  - `\` makes the next character literal. A trailing space is part of the
    pattern only when escaped, since a rule's value carries no trailing space.

  This is git's `wildmatch` with pathname matching, which is what
  `gitignore(5)` describes. Where that text is silent, git's behaviour
  decides, and the corpus records the case.

- **A glob rule's file may hold `!` lines after its rule.** Each is a
  gitignore pattern with the meaning above, and it narrows that rule and no
  other:

  ```
  skip-glob *.tmp
  !keep.tmp
  ```

  The rule covers a path when the pattern matches the path, or a directory
  above it, and no `!` line matches the same path or directory. The order of
  `!` lines means nothing, so a writer sorts them and two replicas spell one
  rule alike. One rule's exceptions never reach another rule, so rules still
  union and never argue: 0011's condition holds.

- **This says any one `.gitignore` exactly.** git ignores a path when the last
  line matching it, or a directory above it, is a positive one. That is true
  exactly when some positive line matches and no `!` line after it does. So
  each positive line, with the `!` lines that follow it, is one glob rule,
  and the union of those rules is the file. git's refusal to re-include a file
  beneath an excluded directory falls out without a word: the directory
  matches the rule, and the `!` line naming the file does not match the
  directory. A nested `.gitignore` translates by prefixing its directory: a
  line `*.o` in `sub/.gitignore` is `skip-glob sub/**/*.o`.

- **`skip` and `skip-name` are unchanged, and preferred.** They are what a
  person reads first. `check` reports, as a note, a glob rule with no `!`
  lines that a `skip` or `skip-name` rule says exactly, and gives that
  spelling. A glob is the case a name cannot say, and the folder should show
  that at a glance.

- **The refusal of a rule that covers a tracked file is unchanged.** It asks
  whether the rule covers the path, as `record`, `skip` and `check` already
  do.

- **The label follows 0051.** A value holding `*`, `?`, `[` or `\` takes the
  digest of its rule's text, which now includes the `!` lines. Others mirror
  the value under `glob `.

- **`historica skip --glob <pattern>` writes one**, with `--except <pattern>`
  for each `!` line.

## The matcher is historica's own

A dependency, `gix-glob`, would give the matcher in one line, and is the
wrong place for it to live. What a store skips is part of the format: a
change to the matcher changes which files a history takes, without a change
to any file in the store. That has to move only when historica's version
does, and only where a decision says so. gitoxide's crates are 0.x and
release often.

The matcher is small: a pattern compiler and a backtracking match over one
path, around two hundred lines, since git's own is about three hundred lines
of C. Its risk is correctness, and that is tested two ways rather than
trusted to one:

- a corpus of rule, path and verdict, under `tests/corpus/skipped/`, which is
  the specification executed for anybody reimplementing it;
- a by-hand check that runs each corpus case through `git check-ignore`, so
  the corpus is git's answers and not ours.

No other implementation is a dependency, not even a test's: the corpus is
the oracle, and git is what checks the corpus.

git's own `t3070` cases are GPL, so they are a reference to test against
and not text to copy into this repository.

## What it costs

- **The ten-line matcher is gone for one key.** 0051's argument stands for
  `skip-name`, whose matcher is unchanged; `skip-glob` buys parity with what
  the argument gave up, and the price is paid once, in a tested module.
- **An older reader refuses a store that states a glob rule.** The key is
  unknown to it, and 0011 makes an unknown key a refusal to record. That is
  the direction this design fails in, and the changelog says so.
- **`core.ignorecase` is not followed.** Matching is case-sensitive, as
  everything in historica is. Where git ignores case, an import can be wrong
  about case, and historica-git says so when it imports.

## For historica-git

The import stops leaving lines out. Each line becomes a `skip` or `skip-name`
rule where one says it exactly, and a glob rule otherwise, with the `!` lines
that follow it in git's order of files. A rule covering a file git tracks
gains a `!/<path>` line for that file, rather than being dropped. That is
exact when it is written, and goes stale when tracking changes, as the whole
import does when an ignore file changes.

The reading of a line into `skip` or `skip-name` moves into historica, as the
same function `check` uses for its note, so the two cannot disagree.
