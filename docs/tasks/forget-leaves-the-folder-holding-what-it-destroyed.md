---
title: Forget leaves the folder holding what it destroyed
description: `forget` destroys the store's copies of some lines and leaves every folder holding them, so the next `record` in that folder — or in any replica's — records them again as new work, and the redaction is undone by the person who asked for it
status: open
created: 2026-10-13
updated: 2026-10-13
part_of: '[Tasks](/docs/tasks/tasks.md)'
---

# Forget leaves the folder holding what it destroyed

[0014](/docs/decisions/0014-forgetting.md) has `forget` destroy every copy of
some lines the *store* holds. It says nothing about the folder, and `forget`
touches none. A folder at the head still holds the lines, and the next
`record` sees a file that differs from what the store says — the forgotten
items against the folder's text — and records the text again, as an insert
by a new revision. Nothing warns, and `forget`'s closing line says the text
is destroyed.

Every other replica has the same folder. When the forgetting documents
arrive by sync, nothing tells that folder anything either, and its next
`record` restores the lines from there: 0014's "a redaction that could be
undone by transport is not one" is kept by the store and broken by the
folder beside it.

Found by `tests/simulation.rs`, whose first counterexample was this, in four
actions: edit, `record`, `forget`, `record`. The simulation now models a
person who takes the lines out of every folder they own, which is the only
way the lines are gone everywhere a later `record` can see.

## Repro

```console
$ printf 'a\nsecret\n' > f.txt && historica record -m x
$ historica forget head f.txt --lines 2
$ historica status                    # f.txt: edited
$ historica record -m y
$ historica cat head f.txt
a
secret
```

## Candidates

- **`forget` says so**: names each folder path still holding forgotten text
  — its own folder, at least — the way it already reports a payload held
  `elsewhere`.
- **`forget` takes the lines out of its own folder** where the folder holds
  the head's content for them, as `update` would.
- **`record` refuses to re-record forgotten text**: an insert whose text
  equals an item the store holds forgotten is suspicious, and the store
  cannot compare against text it destroyed — so this only works with a
  digest of the forgotten line kept somewhere, which 0014 would have to
  allow.
- **`status` and `update` treat a forgotten line as matching** whatever the
  folder holds at that position, as replay already does.

## Done when

A `record` after a `forget` does not silently restore the lines in the folder
the `forget` ran in, and the behaviour in another replica's folder is
decided and written down.
