---
title: Forget at a rewrite leaves its predecessor legible
description: Forgetting lines at an amended revision destroys the amendment's copy and leaves the superseded original's, which mints its own items for the same text (0023), legible until `prune` — and `forget` does not say so
status: done
created: 2026-10-13
updated: 2026-10-30
part_of: '[Closed tasks](/docs/tasks/closed/closed.md)'
---

# Forget at a rewrite leaves its predecessor legible

**Status.** Done, by `feat(store): forget names the superseded revisions
still holding the text`, which takes the first candidate below. `forget
--lines` lists, as `Forgotten::superseded`, every revision the history it
forgets in supersedes that still shows a forgotten line's text through an
item it leaves alone, and the CLI prints one line for each, naming the
revision and the `forget` or `prune` that would take it. An amendment that
left the file alone names the same document as its predecessor, so one
forget destroys both copies and nothing is named. The repro now prints
`<X> still holds that text`.

[0014](/docs/decisions/0014-forgetting.md) forgets *items*, and
[0023](/docs/decisions/0023-what-an-amendment-keeps.md) has an amendment mint
its own items for what its predecessor's folder said. So after an `amend`
that changed anything about a file, the predecessor and the amendment hold
one text under two names, and forgetting it at the head destroys the
amendment's copy alone. The superseded revision stays in the store until
`prune`, and `cat` on it prints the text.

This is the per-item rule applied as written; what is missing is that
`forget` says nothing. For a file of bytes it already counts other content
the file holds `elsewhere`, because 0066 found a person least expects that
there. A rewrite is the same surprise for lines.

Found while writing `tests/simulation.rs`'s forgetting invariant, which had
to move from "this text is never shown again" to "these items are never
shown again" because of it.

## Repro

```console
$ printf 'a\nsecret\n' > f.txt && historica record -m x     # X
$ printf 'a\nsecret\nmore\n' > f.txt && historica amend      # X', superseding X
$ historica forget head f.txt --lines 2
$ historica cat <X> f.txt
a
secret
```

## Candidates

- **Say so**: `forget` reports each superseded revision in the file's
  history still holding the same text, with the `forget` (or `prune`) that
  would take it.
- **Follow supersession**: forgetting at a revision also forgets, in each
  revision it supersedes, the items whose text is identical at the same
  place. Closer to what a person means, and a rule 0014 would have to state.

## Done when

`forget` at an amended head either destroys the predecessor's copy or says,
in its output, that it did not.
