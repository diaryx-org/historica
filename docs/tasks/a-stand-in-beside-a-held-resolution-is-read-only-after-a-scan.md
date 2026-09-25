---
title: A stand-in beside a held resolution is read only after a scan
description: The catalogue records nothing a resolution forgets, so a forgetting resolution beside the resolution it forgets is found only once something has made the store read every document — and within one command the first reading of that resolution ignores it and a later one applies it
status: open
created: 2026-09-25
updated: 2026-09-25
part_of: "[Tasks](tasks.md)"
---

# A stand-in beside a held resolution is read only after a scan

A store can hold a document and the stand-in that forgets it at once:
a sync that copies files brings the stand-in in beside bytes this replica
never destroyed. [0014](../decisions/0014-forgetting.md) says the redaction
still holds, and `check` says so too: *was forgotten and its bytes are here
again, probably by sync; the redaction still holds*. For an operation
document, every reader applies it. For a resolution, which
[0050](../decisions/0050-forgetting-a-merges-own-text.md) gives stand-ins of
its own, the reader applies it only some of the time, and which time depends
on what else the same command has already read.

## Reproduce

With `historica` on `PATH`: a merge whose resolution inserts `L` itself,
the line forgotten in a copy of the store, and that copy's new files copied
back beside the originals.

```sh
set -e
export HISTORICA_AUTHOR="Check <check@example.com>"
rec() { name=$1; shift; historica record "$@" | sed -n 's/^recorded [a-z]* as \([0-9a-f]*\).*/\1/p' | xargs historica name "$name" --revision; }
mkdir here && cd here && historica init . >/dev/null
printf 'a\nb\n' > f.md;         printf 'one\n' > notes.md; rec first -m first
printf 'a\nb\nL\n' > f.md;      rec left -m left
printf 'R\na\nb\n' > f.md;      rec right --onto first -m right
printf 'L\nR\na\nb\n' > f.md;   rec merged --merge left --merge right -m merged
printf 'two\n' > notes.md;      rec after -m after
cd .. && cp -a here elsewhere
(cd elsewhere && historica forget left f.md --lines 3)
(cd elsewhere/history && find operations -type f) | while read -r f; do
  [ -e "here/history/$f" ] || { mkdir -p "here/history/$(dirname "$f")"; cp "elsewhere/history/$f" "here/history/$f"; }
done
find here/history/cache -type f ! -name README.txt -delete
cd here && historica diff head
```

`forget` wrote two stand-ins, one for `left`'s operation document and one
for `merged`'s resolution, and both now sit beside their originals. `after`
changed only `notes.md`, and `historica diff head` says:

```
--- a/f.md
+++ b/f.md
@@ -1,4 +1,4 @@
-L
+\ forgotten
 R
 a
 b
--- a/notes.md
+++ b/notes.md
@@ -1,1 +1,1 @@
-one
+two
```

So the revision after the merge turned `L` into `\ forgotten` in a file it
never touched. Each side read alone disagrees with that: `historica cat
merged f.md` and `historica cat after f.md` both print `L`, and `historica
diff after f.md` prints the same false hunk. `historica cat left f.md`
prints `\ forgotten`, since an operation document's stand-in is always
applied. `historica check` prints the resurrection note for both digests.

## What is known

`Store::effective_body` reads a held resolution through
`resolutions_beside`, which asks `standing` for the documents that forget
it. Until the store has scanned (`Store::scan`, `scanned`), `standing`
answers from the catalogue, and `store::catalogue::read` records a
resolution as forgetting nothing (`catalogue.rs`, the `is_resolution`
branch, `None`). A catalogue in `cache/operations.txt` written by that code
carries `-` for it too. So the stand-in is invisible to a held resolution.

The scan does parse resolutions and files their `forgets` under
`read.forgetting`, and it runs the first time `read_body` misses. Here that
is when `assemble` asks `minted` for the payload a `keep` names, `f.md`'s
`a\nb\n`, since a payload is not a document. After that, in the same
process, `standing` answers from the scan, and the stand-in is found. `diff
head` materialises `f.md` on both sides: the first reading comes before the
scan and gets `L`, and the second comes after it and gets `\ forgotten`.

Two consequences follow from where the gap is:

- A command that reads such a resolution once gives an answer that depends
  on whether anything earlier in it missed a document.
- A resolution whose keeps name only operation documents may never trigger
  the scan, so the stand-in beside it is never applied.

## What the right behaviour is

The union rule holds for a resolution as it does for an operation
document. A held resolution with a stand-in of its shape beside it is read
with every `insert` item the stand-in forgets forgotten, on every reading,
whatever else the command has read. Here that means:

- `historica cat merged f.md` and `historica cat after f.md` print
  `\ forgotten` where `L` was.
- `historica diff head` shows only `notes.md`.
- `historica diff after f.md` shows nothing.

## Where to look

- `store::catalogue::read` should record what a resolution forgets, as it
  already does for an operation document and a payload's stand-in: from
  the parse, or from the first header, which every forgetting grammar
  opens with.
- A catalogue already on disk says `-` for such a document, so it must not
  keep that answer. Either the header moves (`historica-catalogue-2`), or
  a `.ops.txt` path whose line says `-` is re-read when it is a
  resolution. Decision [0036](../decisions/0036-where-a-digest-is.md) says
  which of those is honest.
- `resolutions_beside` and `forgetting_resolution` can then stay as they
  are.

The Bend port under `spike/bend/` reads such a resolution the way the first
reading does, everywhere (`standin.bend`, `held.fold`). Its `resurrected`
store in `check.py` leaves out `diff head` for this reason, and says so.
When this is fixed, both follow.

## Done when

- A test in `cli/tests/forget.rs` builds the store above. It asserts that
  `cat merged f.md` prints `\ forgotten` for `L`, and that `diff head` lists
  only `notes.md`.
- The same holds with a `cache/operations.txt` that an earlier version
  wrote before the stand-in arrived.
- `store::catalogue` records a resolution's `forgets`, and a catalogue
  that says otherwise is not believed about it.
- The commit carries a `Behavioural-change:` trailer: a reader of a store
  holding a resolution beside its stand-in sees the redaction where it saw
  the original.
- The Bend port's `standin.bend` reads a held resolution through its
  stand-ins, and `check.py`'s `resurrected` store holds `diff head` again.
