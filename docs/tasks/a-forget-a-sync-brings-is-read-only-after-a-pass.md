---
title: A forget a sync brings is read only after a pass
description: A forgetting document that a file-copying sync puts beside the original it forgets is not seen by a reader that takes its cached catalogue as it stands, so the forgotten text is shown until something makes the store read `operations/` — and nothing a reader does on its own need ever do that
status: open
created: 2026-09-28
updated: 2026-09-28
part_of: "[Tasks](tasks.md)"
---

# A forget a sync brings is read only after a pass

Decisions [0003](../decisions/0003-store.md) and
[0014](../decisions/0014-forgetting.md) let a store be synced by anything that
copies files — rsync, Syncthing, iCloud, `cp -n` — and 0014 says the
redaction survives it: *a redaction that could be undone by transport is not
one*. A sync that copies and deletes nothing brings the forgetting document in
beside the original. [0049](../decisions/0049-what-a-lookup-does-not-prove.md)
lets a reader take the cached `operations.txt` as it stands, reasoning that holding
the original's bytes means nothing has redacted them, because `forget`
destroys them and `receive` complies before it writes. A sync is the one way
that reasoning fails, and 0049 names the result, the state `check` reports as
`Resurrected`, without saying what readers show there.

What they show is the original. `fix(store): a forget that arrives clears the
states read before it` makes the window end at the next pass over
`operations/`: the pass reads the stand-in, clears the cached states, and
records it in the catalogue. What starts that pass is a digest the catalogue
cannot place, `offer`, or a writer with no catalogue. A reader in a store
nobody writes to, or one whose new documents are all found where their
revision files them ([0041](../decisions/0041-where-a-revision-is-filed.md)),
may never take it.

## Reproduce

With `historica` on `PATH`:

```sh
set -e
export HISTORICA_AUTHOR="Check <check@example.com>"
mkdir here && cd here && historica init . >/dev/null
printf 'secret\nv0\n' > f.md && historica record -m first >/dev/null
first=$(historica log --fields | tail -1 | cut -d' ' -f1)
printf 'secret\nv1\n' > f.md && historica record -m second >/dev/null
cd .. && cp -a here elsewhere
(cd elsewhere && historica forget "$first" f.md --lines 1 >/dev/null)
(cd elsewhere/history && find operations -type f) | while read -r f; do
  [ -e "here/history/$f" ] || { mkdir -p "here/history/$(dirname "$f")"; cp "elsewhere/history/$f" "here/history/$f"; }
done
cd here && historica cat head f.md && historica check
```

`cat` prints `secret`, and `check` prints the resurrection note. Run
`historica offer .` (or delete the cache directory, decision
[0078](../decisions/0078-where-a-cache-is-kept.md)) and `cat`
prints `\ forgotten`.

## Where the stand-ins are

`forget` files an operation document's stand-in and a resolution's at the top
of `operations/`, under their digest. It files a payload's stand-in beside the
destroyed payload, under the payload's name plus `.ops.txt`, and at the top
under its digest if that name is taken. A sync copies paths, so on the
receiving side each lands where `forget` put it.

## The proposal

Two cheap looks, taken by a reader before it believes a held catalogue:

- **One listing of the top of `operations/`**, not the walk. A default store
  holds its month directories there, and stand-ins. A file at the top that the
  held catalogue does not name is read, as the pass reads any unaccounted
  path; one that forgets something clears the states and is catalogued.
  That's one `entries` call per command that reads content, against 0077's
  measurement of one per revision directory for the walk.
- **One look beside a payload** as it is read, at the name its stand-in would
  have. A hit is read, hashed and parsed before it is believed, as 0036
  requires of any claim that a document forgets something.

What this does not cover is a stand-in somewhere else: moved by hand, or by an
`arrange` that files it elsewhere. That keeps the window this task is about,
and `check` still reports it. The tension to settle is with 0036's *not a
name-to-digest shortcut*. This does not find a digest by its name. It looks
where the store's own writer files a stand-in, and a miss there is not taken as
proof that nothing is there. Whether that difference is enough is the decision.

Rejected:

- **Walking `operations/` on every read**, which is 0049 undone. 0077 measured
  the walk as most of a record's time on a long history.
- **Directory modification times**, which 0036 rules out. `Filesystem` carries
  no metadata (0025), and rsync sets a directory's time back.

## Done when

- A decision is written, accepting the looks above or saying why the window
  stays, and 0049's reasoning about held originals names the sync case.
- If accepted, a test in `cli/tests/forget.rs` runs the repro above with only
  a reader after the sync: `cat` prints `\ forgotten` with no `offer`, no
  miss, and the cache as the last command left it. The same holds for a payload
  forgotten whole.
- The commit carries a `Behavioural-change:` trailer: readers apply a
  forgetting document a sync brings on the first command after it arrives.
