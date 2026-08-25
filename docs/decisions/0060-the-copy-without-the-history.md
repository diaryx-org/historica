# 0060 — The copy without the history

0042 built the copy a person takes away, and 0052 made it something a stranger
fetches from. Both are the same artifact: a *repository*, holding the folder as
one revision has it and the ancestry that leads there.

That is the right default and it is not always what was wanted. Exporting the
three-hundredth revision of a six-hundred-revision store writes 14 MB and takes
a second and a half, of which 13 MB is `history/`. Three callers want the other
1 MB and none of the rest — somebody reading what a file said last month, a
build of an old revision, and a tree handed to a person who does not have
historica at all.

Nothing stopped them today, which is worth saying before deciding anything:
`export` already accepts any target, not only a head, so
`historica export /tmp/past <revision>` has always written the folder that
revision has. What is missing is not the capability. It is a way to decline the
ancestry.

## Why a flag rather than a command

The first sketch was a command of its own — `extract`, over
[`update::plan_into`][plan_into], which has laid a revision out in an empty
directory since 0030 deferred it and has had no caller in the binary.

It is the wrong shape, and the reason is that the two overlap almost entirely.
`export` already materialises the folder through `update::plan_at` and
`update::apply`; the target resolution, the destination, the rule filtering and
the printing would all be duplicated to do strictly less. A second command
would also have to be *named*, and every name for it — `extract`, `checkout`,
`snapshot` — describes a tool this is not.

The argument against is real and worth writing down: what `export` produces is
a thing that can be recorded into, fetched from and received, and what this
produces cannot. That is a change of noun, and no other flag in this binary
changes what its command produces — `--dry-run` does not, `--refile` does not,
`--complete` does not. It is overruled because the alternative duplicates four
fifths of a command to avoid one sentence of documentation, and because the
sentence is easy to write: *there is no store under it*.

## The decision

- **`export <dir> [<target>] --files-only`** writes the folder the target has
  at `<dir>`, and nothing beneath it. No `history/`, so no revisions, no
  operation documents, no payloads, no rules, no marker, and no reserved
  directory of another tool's.

- **It is the same folder a whole export writes.** The same target resolution,
  the same materialisation through [`crate::update`], and the same rules — the
  ones that *travel*, per 0051, since those are the rules the copy would have
  stated and therefore the ones a full export's folder is filtered by. A
  `private` rule keeps a file out of a history; it is not a statement about
  which files a copy holds. `tests/export.rs` pins the two folders as
  byte-identical, which is the whole of what makes this a flag.

- **The destination must be empty.** 0052 lets a whole export be written over a
  copy of this store because the copy's own `history/` says what the last
  export put there — which is what makes a withdrawal safe. A folder with no
  store beside it cannot answer that question about a single file, so there is
  nothing to diff and nothing that could be withdrawn without guessing. That is
  [`update::plan_into`][plan_into]'s existing rule, arriving here as the second
  thing the flag changes about the command, and it is refused by naming what is
  in the way.

- **It is still an export.** A broken store refuses, on `export`'s own reason
  and `prune`'s and `fetch`'s: a copy of a fault is two faults. Leaving the
  history behind does not make it safe to copy a folder out of a store that
  contradicts itself.

- **The last line says what it is not.** `and no history beside it`, because a
  directory that looks like a repository and is not one is the single thing a
  person could take away from this wrongly.

## What this is not

**Not a checkout, and not a step towards one.** 0030's rule is about the folder
`record` and `status` derive their position from, and nothing here writes a
position anywhere. A person who wants to *work* on a past revision still runs a
whole `export` and gets a repository whose only head is that revision, which is
better than what this produces and always was.

**Not a faster export.** It skips the ancestry; it does not skip the `check`,
and it does not make writing the folder any cheaper. A bisect built on it is
still one materialisation per step.

## Deferred

**Updating a files-only copy in place.** It would need a record of what the
last run wrote, which is what `history/` is, and inventing a smaller one — a
manifest beside the folder — would be a second format for the thing 0052
already solved. A person who wants the folder refreshed deletes it and runs the
command again.

[plan_into]: https://docs.rs/historica/latest/historica/update/fn.plan_into.html
