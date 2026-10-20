# 0087 — A name with its parents

[0051](0051-two-axes-for-a-rule.md) stopped the pattern at one path
component, and said why in one sentence: "The danger in a glob is not `*`. It
is `/`." This decision lets a `skip-name` value hold a `/`, so it has to show
that the quarrels 0051 named do not come back with it.

The case that forces it is one line of a `.gitignore` that agents now write
into every repository they touch:

```
**/.claude/settings.local.json
```

git ignores the file `settings.local.json` in any directory named `.claude`,
at any depth, and nothing else. Each of the four rules can only approximate
it:

- `skip-name settings.local.json` also skips a `settings.local.json` that is
  not in a `.claude` directory. That file git would commit and historica
  would never record, which is the quiet loss
  [0001](0001-identity.md) forbids.
- `skip-name .claude/` also skips `.claude/settings.json`, which the
  repository tracks, and a rule covering a tracked file is refused.
- `skip .claude/settings.local.json` covers the copy at the root and none
  below it, so a monorepo's `apps/web/.claude/settings.local.json` is
  recorded the first time somebody opens an agent there. It holds the
  permissions a person granted on their own machine.

The rule that says the line exactly names a file by its last components,
wherever those components occur. That is what a name already does with one
component. So the honest spelling is not a fifth key; it is a name that is
allowed to say its parents.

## The decision

- **A `skip-name` value is one or more components joined by `/`, and each
  component is a 0051 pattern.** The value `.claude/settings.local.json`
  has two components; `settings.local.json` has one, and means what it meant.

- **Without a trailing `/`, the value covers a file whose path ends with
  those components.** The path has at least as many components as the value,
  and its last *n* components match the value's *n* components, one to one,
  in order. `skip-name .claude/settings.local.json` covers
  `.claude/settings.local.json` and `apps/web/.claude/settings.local.json`,
  and not `settings.local.json`, `.claude/settings.json`, or
  `.claude/x/settings.local.json`.

- **With a trailing `/`, the value covers everything beneath a directory
  whose path ends with those components.** `skip-name .claude/worktrees/`
  covers `.claude/worktrees/a/b` and `tools/.claude/worktrees/c`, and not a
  file called `.claude/worktrees` nor a `worktrees/` that is not inside a
  `.claude`. This is the same parting a one-component `skip-name build/`
  already makes.

- **A `*` matches within one component and never across a `/`.** Matching
  splits the value and the path on `/` and compares component to component;
  the star never meets a separator, so there is no question for it to
  answer.

- **Every component holds something besides `*`.** 0051 refused a value of
  only stars because it is the whole folder. A component of only stars inside
  a longer value is refused for the reason beneath that one: it would say
  *some directory, any name*, which is a statement about depth, and depth is
  the dialect `**` is. `skip-name docs/*` is therefore refused, not given a
  meaning.

- **A value has no empty, `.` or `..` component, and does not start with a
  `/`.** A leading `/` is an anchor, and an anchored path is spelled with
  `skip`. The refusal says so.

- **`private-name` takes the same values.** The travel axis is orthogonal to
  matching (0051), so it follows without a word of its own.

- **No key is added, and 0051's set stays closed at four.** A one-component
  value is the *n* = 1 case of the new reading, word for word, so every store
  that reads today reads identically.

- **The refusal of a rule that covers a tracked file is unchanged.** It asks
  `covers`, and so do `record`, `skip`, and `check`'s
  `RuleCoversTracked`. The new reading is one more answer to that question,
  not a new question.

- **The label mirrors the value**, as 0045 makes a path's label mirror the
  path: `skip-name .claude/settings.local.json` is filed at
  `name .claude/settings.local.json.txt`. The fallbacks 0051 lists apply, and
  each component, not only the last, is held to the platform-name test.

## Why the quarrels do not return

0051 listed them: "whether a star crosses one, whether `**` is a different
thing, whether `docs/*` reaches `docs/a/b`, how a character class interacts
with a boundary". Taken in turn:

- A star does not cross a separator, because matching happens after the
  split. That is a property of the algorithm, not a convention a second
  implementation could read differently.
- There is no `**`, and a star-only component, which is the closest thing to
  one, is refused.
- `docs/*` is refused, so it reaches nothing. `docs/*.md` covers a file
  ending `.md` whose parent is called `docs`, and nothing deeper, because a
  file rule matches the *last* components and has no room to skip any.
- There are still no character classes.

What 0051 bought by forbidding `/` was a matcher a stranger writes in ten
lines. This one is fifteen: split both on `/`; a file rule compares the
value's components with the path's last ones; a directory rule does the same
against each proper prefix of the path. No component of the value is ever
matched against anything but one component of the path, so the 0051 matcher
is used unchanged inside it.

And 0011's own worry, that two rules can argue, is untouched. There is still
no order, no negation, and no precedence. Two rules covering one path union.

## Why not a fifth key

A key such as `skip-ending` would be honest about the new reading, and
wrong about the old one. `skip-name settings.local.json` *is* a path ending
of length one, so a fifth key would give one rule two spellings, which is the
duplication 0051 removed by retiring `skip-suffix`. It would also need a
`private` twin, opening the cross product 0051 closed.

## Why not anchored patterns

`src/*.rs`, a wildcard in an anchored path, is the other thing git says that
historica cannot. It is not this decision. An anchored pattern is a `skip`
value with a star in it, and `skip` values are exact on purpose: they are how
a name holding a literal `*` is spelled. Giving `skip` a pattern would take
that away, and nothing here needs it.

## What it costs

- **An older reader refuses a store that states such a rule.** It reads a `/`
  in a pattern as malformed, and the loader stops. That is 0011's direction
  of failure, refusing to record rather than recording what was asked to
  stay out, so it is the failure to accept, but it is a compatibility event
  and the changelog says so.
- **`Pattern` stops being the unit a `Scope::Name` holds.** The public type a
  name rule carries becomes a sequence of patterns, which is a change to the
  library's API before 1.0.

## For historica-git

The import ([0011](0011-working-copy.md)'s colocated directory) carries a
`**/`-led line it could not before:

| git line                         | rules                                                        |
|----------------------------------|--------------------------------------------------------------|
| `**/.claude/settings.local.json` | `skip-name .claude/settings.local.json`, `skip-name .claude/settings.local.json/` |
| `**/.claude/worktrees/`          | `skip-name .claude/worktrees/`                               |
| `**/a/*.log`                     | `skip-name a/*.log`, `skip-name a/*.log/`                    |
| `**/a/**`                        | `skip-name a/`                                               |
| `a/**/b`, `src/*.rs`, `**/*/b`   | still left, and said                                         |

A line without a trailing `/` matches a directory as well as a file in git,
which is why it becomes two rules, as `.env` already does. A line that does
not begin with `**/` and holds a `/` is anchored, and stays `skip`'s.
