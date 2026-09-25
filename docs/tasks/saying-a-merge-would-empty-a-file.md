---
title: Saying a merge would empty a file
description: status prints nothing for a contested file the folder holds empty, and says nothing differs, where record refuses the same merge as emptying it
status: open
created: 2026-09-25
updated: 2026-09-25
part_of: "[Tasks](tasks.md)"
---

# Saying a merge would empty a file

`status` is meant to say what `record` would state or refuse. For a file of
lines the joined parents contest, which the folder holds with no bytes in it,
it says nothing at all, and where nothing else differs it says nothing differs;
`record` then refuses the same merge with `EmptiedByMerge`.

## Repro

```sh
historica init . && historica identity "Check <check@example.com>"
printf 'a\nb\nc\n' > f.md;     historica record -m base
historica name base head --revision
printf 'a\nLEFT\nc\n' > f.md;  historica record -m left
historica name left head --revision
printf 'a\nRIGHT\nc\n' > f.md; historica record --onto base -m right
historica name right <the digest it printed> --revision
: > f.md
historica status --merge left --merge right
historica record --merge left --merge right -m join
```

`status` prints the two parents and then

```text
nothing here differs from what is recorded
```

and exits 0. `record` refuses:

```text
historica: a merge states what each contested file is, and there is no way to state that one is empty; leave it something and remove it in the revision after, or drop it here:
  f.md
```

## Why

The survey does find it. `record::survey` pushes the path onto
`Survey::emptied` where the text merge has contests and `resolve` finds no
resolution of what the folder holds, and `plan` refuses on it. But
`render::status` prints `survey.facts()`, `refused`, `unsettled`, `standing`
and `contested_bytes`, never `emptied`, and `Survey::is_empty` does not count
it, so the one line `status` does print is the one that is wrong.

The Bend port in `spike/bend` has the same shape, held byte for byte to this
behaviour: `survey.bend`'s `Survey` has no field for an emptied path, so
`Sv.of` drops the `Emptied` observation `lines.proposed` makes.
`LAWS.status_leaves_a_disputed_file_unsettled` states what the survey is told
of such a path, and says in its comment that the report shows nothing for it.

## Done when

`status` gives a contested file the folder holds empty a line of its own —
naming the path and saying that a merge cannot empty it, as `record`'s refusal
does — and does not say that nothing differs while there is one. The change is
a `Behavioural-change:` trailer, since a caller reading `status` sees a new
line and loses the quiet one. The Bend port follows in the same change: a
field on `Survey`, a line in `status.report`, `Sv.is_quiet` counting it,
`check.py` holding a store with such a file to the Rust tool, and
`status_leaves_a_disputed_file_unsettled` stated at the level of the report
rather than of the survey.
