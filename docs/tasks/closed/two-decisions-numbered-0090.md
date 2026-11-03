---
title: Two decisions are numbered 0090
description: '`0090-taking-a-revision-back.md` and `0090-what-a-command-already-worked-out.md` share a number, and the index lists only the first, so `prov check` finds the second an orphan and every "decision 0090" in the code and docs is ambiguous'
status: done
created: 2026-11-03
updated: 2026-11-03
part_of: '[Closed tasks](/docs/tasks/closed/closed.md)'
---

# Two decisions are numbered 0090

**Status.** Done, by `docs(decisions): number the decision about what a
command already worked out 0094`. The decision about stored states is
`0094-what-a-command-already-worked-out.md` now, its heading says 0094,
`index.md` lists it after 0093, and `git/docs/decisions/0014-…` says
"historica's 0094". 0092 was free when this task was filed, and went to
`0092-the-digest-a-reader-checks.md` and 0093 to
`0093-a-state-read-once-is-moved.md` before the fix landed. Every "0090" left
in the code and docs means `revert`. `prov check` reports nothing.

`docs/decisions/` holds two decisions numbered 0090:

- `0090-taking-a-revision-back.md`, which came with `revert` (2026-10-30)
  and is listed in `docs/decisions/index.md`;
- `0090-what-a-command-already-worked-out.md`, which came with 495892d,
  `perf(store): a command keeps the states and settlings it already worked
  out` (2026-11-01), and is not.

0091 (a change set) was already taken when the second was written, so it
took a number that was not free either.

## Repro

```console
$ prov check
docs/decisions/0090-what-a-command-already-worked-out.md: orphan — on disk but not linked into the workspace
1 finding(s)
$ ls docs/decisions | grep '^0090'
0090-taking-a-revision-back.md
0090-what-a-command-already-worked-out.md
```

CI does not run `prov check`, so nothing caught it.

## What it costs

The second decision cannot be reached from the index. A reader who follows
a "decision 0090" reference has to guess which one is meant. The references
that mean `revert` are `src/revert.rs`, `tests/revert.rs`,
`cli/src/cli/revert.rs`, `cli/tests/revert.rs` and `docs/cli.md`. The one
that means the stored states is
`git/docs/decisions/0014-a-commit-is-recorded-by-the-paths-it-changed.md`
("With historica's 0090, converting diaryx takes 7 minutes rather than
31"), and so is 495892d's commit message.

## Done when

The decision about stored states has a number of its own (0092 is the next
free one), its file and heading carry that number, `index.md` lists it
after 0091, the reference in `git/docs/decisions/0014-…` uses the new
number, and `prov check` reports nothing.
