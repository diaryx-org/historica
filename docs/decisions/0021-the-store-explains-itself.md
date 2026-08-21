# 0021 — The store explains itself, while strictness is still free

0020 left two things undone, and one fact answers both.

The first was its own open question: the store's documents learned to say they
are text, and the store's *own* files — the marker, the bookmarks, the rule
file — did not, so `history/` is a folder where five things open and three ask
which application to use.

The second was a hazard it could not retire. 0020 kept reading `.rev` and
`.ops` so that a store written the day before would not quietly lose its
documents, and the price was that 0018's rule stayed exactly as onerous: a
payload whose path ends in `.ops` still cannot carry its own name, because that
name is one the reader claims. 0020's second open question asked when that
could ever be undone and answered that it needed "a moment when no store
written under it exists — a moment this format cannot know it has reached."

It has reached it. Nothing is deployed, nobody has a store, and every one that
exists was written this week by the person writing the format. That is a fact
about the world rather than about the design, it is true exactly once, and
spending it is what this document does.

## The decision

- **The marker becomes `historica.txt`, and carries a note.** Its first line
  is still the version. Everything after it is prose for whoever opens the
  folder: what this is, what each directory holds, and that nothing here needs
  Historica to read.
- **A reader takes the version from the first line** and ignores the rest.
  Nothing hashes this file, so a person may write whatever they like under it.
- **`skipped` becomes `skipped.txt`**, and a bookmark becomes `<name>.txt`.
  A bookmark's name is still its filename, now minus the suffix.
- **`.rev` and `.ops` are no longer read.** One suffix per kind, written and
  accepted: `.rev.txt` and `.ops.txt`.
- **0018's payload rule is retired in the form it had.** A payload avoids
  `.ops.txt` and nothing else, so a repository holding `notes.ops` — or a
  corpus full of deliberately invalid `.ops` files, which is what found the bug
  — files them under their own names.
- **The corpus is renamed.** Its files are named `.rev.txt` and `.ops.txt` like
  everything else. No digest changes, because no digest ever covered a name.

## The note

A person who opens `history/` should not have to be told what they are looking
at by someone who already knows. The file that marks the folder as a store is
the obvious place to say it, and it costs nothing: nothing hashes it, no
document references it, and a reader takes one line.

```text
historica-v1

This folder is a Historica store: the recorded history of the files beside it.
...
```

What it says is the store's shape and the one rule that explains the shape —
identity comes from content, so a filename is only ever presentation and
renaming anything here breaks nothing. That sentence is the difference between
a folder a person is afraid to touch and one they can file however they like,
and it has until now lived only in `docs/decisions/0003-store.md`.

## Why `historica.txt` and not `README.txt`

`README.txt` is the friendlier name and the worse marker. `Store::discover`
walks up from the working directory looking for `history/<marker>`, and a
directory called `history` holding a `README.txt` is a thing that exists in
ordinary projects — a folder of old files with a note about them. It would be
claimed as a store and then refused on the version line, which is a confusing
error about a folder that was never a store at all. A marker should be a name
nothing else has.

`historica-info.txt` is distinctive and says less than the note inside it will,
and `.txt` already carries the announcement that the file is readable.

So `historica.txt`: it names the format, nothing else is called that, it sorts
beside the directories at the top of the folder, and the prose inside does the
greeting the filename cannot.

## What closing the window buys

The rule 0018 needed, and 0020 could not retire, was that a payload must avoid
every suffix a reader claims. With one suffix per kind, that list has one entry
and it ends in `.txt`, which is not a thing this project's corpus is full of.
Concretely, recording Historica into its own repository now files

```
operations/<revision>/tests/corpus/operations/invalid/adjacent-deletes.ops
```

under exactly that name, where before it took a digest suffix to keep the
loader from parsing it. The rule survives — a payload at a path ending
`.ops.txt` still yields — but it stops firing on anything anybody has.

## What it costs, and the honest part

Every store written before this document stops loading. There are perhaps five
of them, all in this repository's `target/tmp`, and one in the author's working
copy. `check` will call their documents foreign files and their absence
ordinary, which is precisely the quiet failure 0020 refused to build — and the
reason it is acceptable here and would not be acceptable next month is that
"quiet" needs somebody to be listening.

That asymmetry deserves to be said rather than assumed: **this is the last
decision that gets to do this.** Once a store exists that its author did not
write, the reader's accepted set is append-only forever, on 0004's reasoning
about revisions and for the same reason — a name that stops being read is
content that stops being found.

## Consequences

- `store` keeps one suffix per kind, `HEADER_FILE` becomes `historica.txt`, and
  `read_version` parses the first line rather than the whole file.
- `Store::init` writes the note.
- `working::SKIPPED_FILE` becomes `skipped.txt`, and every message that names
  it moves with it.
- `names/` holds `<bookmark>.txt`; the reader strips one suffix and `check`
  reports anything else there as a note, because nothing reads it.
- `naming` avoids one suffix rather than a list.
- Sixty-one corpus files are renamed, and their `MANIFEST` lines with them.
  Every digest is unchanged, which is the property being demonstrated: the
  manifests still verify with `shasum -a 256 -c` after every name in them
  moved.
- `check` gains nothing it did not have. A store of the older shape fails at
  the marker, which is the loudest place available.

## Rejected alternatives

**Keeping the dual accept.** 0020's answer, correct on the premise that
somebody might hold an older store. Nobody does, and carrying a permanent
exception for a hypothetical user is how a format acquires the scars it will
still have when it has real ones.

**`README.txt` as the marker.** Above: a name every directory might have is not
a marker.

**Leaving `names/` alone**, since a bookmark file is one line and its name is
load-bearing. Rejected for the folder's sake: a person who has understood that
`.txt` means "you can open this" should not find three files in the same store
that disagree.

**A separate `README.txt` beside `historica.txt`.** Two files where one will
do, and the second would have to say what the first already says.

## Open questions

1. **Whether the note should be checked.** It is prose in a file a reader takes
   one line from, so a person may edit or delete it and nothing notices. That
   is either the right amount of respect for their folder or a note that will
   quietly rot away from what the store actually holds.
2. **Whether `cache/` should carry its own note**, since it is the one
   directory whose contents a person is invited to delete and the only way to
   know that is to have read this document.
