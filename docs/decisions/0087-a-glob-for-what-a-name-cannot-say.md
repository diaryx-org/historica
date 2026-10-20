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

- **Two keys: `skip-glob <pattern>` and `private-glob <pattern>`.**
  `private-glob` stays out of an export, as 0051's other `private` keys do.
  The keys are now three kinds of matching by two kinds of travel, and the set
  closes there again.

- **A glob is anchored at the root, always.** It is matched against the whole
  path, as a `skip` value is. Any depth is spelled, with a leading `**/`:
  git's `*.log` is `skip-glob **/*.log`, and git's `/build` and `src/*.rs`
  are `skip-glob build` and `skip-glob src/*.rs`. A leading `/` is refused,
  because it would say again what every glob already says. This removes the
  rule in gitignore that is hardest to read: that a slash at the start or in
  the middle anchors a pattern, and its absence lets it float.

- **Without a trailing `/`, a glob covers a file. With one, it covers
  everything beneath a directory it matches.** This is the parting `skip` and
  `skip-name` already make. git's `foo` matches a file or a directory, so it
  is two rules here, `skip-glob **/foo` and `skip-glob **/foo/`, as a name
  already is in the import.

- **The pattern language, stated so it can be implemented without git:**
  - The value is split on `/` into parts. No part is empty, `.` or `..`.
  - `*` matches any run of characters within one part, including an empty run
    and a leading dot. `?` matches one character within one part.
  - `[...]` matches one character from a set: single characters, ranges such
    as `a-z`, and POSIX classes such as `[:digit:]`. `[!...]` negates the set;
    `[^...]` is refused, so negation has one spelling. A `]` first in the set,
    and a `-` first or last, stand for themselves. A set never matches `/`.
  - `**` is a whole part or it is refused, and two are never adjacent. As the
    first part it matches any number of directories, including none. In the
    middle it does the same, so `a/**/b` covers `a/b`. As the last part, it
    matches every file beneath, at any depth, in a file rule, and every
    directory beneath in a directory rule. git's `a/**` is therefore
    `skip-glob a/**` and `skip-glob a/**/`, and is not `skip a/`: with an
    exception, `a/**` can keep a file directly inside `a`, and `a/` cannot.
  - `\` makes the next character literal, and is allowed only before `*`,
    `?`, `[`, `\`, and a trailing space. A value follows a key, so a `#` or
    `!` at its start is an ordinary character and needs no escape.
  - A file rule whose parts are all `*` or `**`, at least one of them `**`,
    and that states no exception, is refused: it covers every file, and rules
    exist to name the exceptions. `skip-glob *` is allowed, because it covers
    only the files at the root, and the allowlist idiom needs it.

  Matching is git's `wildmatch` with pathname matching, which is what
  `gitignore(5)` describes, applied to an anchored pattern. Where that text is
  silent, git's behaviour decides, and the corpus records the case.

- **A glob rule's file may hold `except <pattern>` lines after its rule.**
  Each pattern has the meaning above, and narrows that rule and no other:

  ```
  skip-glob **/*.tmp
  except **/keep.tmp
  ```

  A file rule covers a path when its pattern matches the path and no
  exception does. A directory rule covers a path when its pattern matches a
  directory above the path and no exception matches that directory. So an
  exception in a directory rule ends in `/`, and one in a file rule does not;
  the other is refused, because it could never apply. The order of `except`
  lines means nothing, so a writer sorts them and two replicas spell one rule
  alike. One rule's exceptions never reach another rule, so rules still union
  and never argue: 0011's condition holds.

- **One spelling for one meaning.** Every refusal above removes a second
  spelling: `/x` beside `x`, `a**b` beside `a*b`, `**/**` beside `**`,
  `[^` beside `[!`, `\#` beside `#`. Two replicas that state one rule then
  write one file and derive one label, and 0045's finding for a rule stated
  twice reaches globs too.

- **This says any set of `.gitignore` files exactly.** git ignores a path when
  the last line matching it, or a directory above it, is a positive line.
  That is true exactly when some positive line matches and no `!` line after
  it does. So each positive line, with the `!` lines that follow it, becomes
  rules here: its file rule takes the `!` lines that can match a file, and its
  directory rule takes every `!` line, written with `/`. The union is the
  file. git's refusal to re-include a file beneath an excluded directory falls
  out without a word: the directory matches the rule, and an exception naming
  the file does not match the directory. A nested `.gitignore` translates by
  its directory: a floating `*.o` in `sub/.gitignore` is
  `skip-glob sub/**/*.o`, and an anchored `/x` there is `skip-glob sub/x`.

- **`skip` and `skip-name` are unchanged, and preferred.** They are what a
  person reads first. `check` reports, as a note, a glob rule with no
  exceptions that a `skip` or `skip-name` rule says exactly, and gives that
  spelling: `skip-glob **/*.log` is `skip-name *.log`, and `skip-glob docs/a`
  is `skip docs/a`. A glob is the case a name cannot say, and the folder
  should show that at a glance.

- **The refusal of a rule that covers a tracked file is unchanged.** It asks
  whether the rule covers the path, as `record`, `skip` and `check` already
  do.

- **The label follows 0051.** A glob holding `*`, `?`, `[` or `\`, or stating
  an exception, takes the digest of its rule's text. Others mirror the value
  under `glob `.

- **`historica skip --glob <pattern>` writes one**, with `--except <pattern>`
  for each exception.

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
- **A set of rules does not always become one `.gitignore`.** The import is
  exact; the reverse is exact only where no rule's exception meets another
  rule's pattern, because a `!` line in a gitignore re-includes from every
  line above it. Nothing writes a `.gitignore` from rules today. Anything that
  does must say when it cannot.
- **`core.ignorecase` is not followed.** Matching is case-sensitive, as
  everything in historica is. Where git ignores case, an import can be wrong
  about case, and historica-git says so when it imports.

## For historica-git

The import stops leaving lines out. Each line becomes rules as above, read in
git's order of files: the global excludes file, `info/exclude`, then each
`.gitignore` from the root down. git's spellings are made canonical on the
way: a floating pattern gains `**/`, a leading `/` goes, `a**b` is `a*b`,
adjacent `**` parts are one, `[^` is `[!`, and `\#` and `\!` lose their
escape. A line that can match nothing, such as one holding `//`, is reported
and dropped, and so is a line that would cover every file with no `!` after
it. Each rule that a `skip` or `skip-name` rule says exactly is
written as that rule.

A file rule covering a file git tracks gains `except <path>` for it, rather
than being dropped. That is exact when it is written, and goes stale when
tracking changes, as the whole import does when an ignore file changes.

The reading of a glob into `skip` or `skip-name` moves into historica, as the
same function `check` uses for its note, so the two cannot disagree.
