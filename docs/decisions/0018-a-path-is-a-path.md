# 0018 — A path is a path

0016 made the argument and stopped one step short of it:

> **Nesting is what buys the length back.** A flat scheme would have had to
> spell the date, the summary, and the path in one 255-byte name … With the
> revision in the directory, the whole budget is one path.

It nested the revision and then spent that budget flattening the path into a
filename, with `⁄` (U+2044 FRACTION SLASH) standing in for the separator and a
clip at sixty characters to fit:

```
operations/2026-08-20 Start a journal/…corpus⁄diffs⁄final-newline-lost⁄parent.txt.ops
```

The reasoning behind that character is sound as far as it goes — it has no
Unicode decomposition, so two replicas cannot disagree about the bytes of a
name they both derived — but it answers the wrong question. It asks which
character should stand in for a separator in a filename. The filesystem already
has a separator, and a directory is what it separates.

This document files a document under the path it names, as directories.

## The decision

- **A path is filed as a path.** `operations/<revision stem>/notes/photo.png`,
  with real directories for real components. `⁄` is gone, and nothing stands in
  for `/` anywhere in a store.
- **Nothing is clipped.** The sixty-character budget, the `…` that marked the
  cut, and the arithmetic that produced them all go. A component that named a
  file in somebody's folder fits in a filename here, because that is what it
  already was.
- **A document keeps `.ops`**, appended to the last component:
  `notes/2026-08-20.md.ops`. A payload keeps the file's own name and nothing
  else, per 0017.
- **A payload never carries `.ops`**, and a name two things would meet at is
  parted by a digest suffix on the last component, never by a counter. Both
  cases are named below.
- **`arrange` tidies the directories it empties, upwards**, stopping at
  `operations/` and stopping the moment a directory holds anything — which is
  `remove_dir` refusing, the same guard 0016 relied on.

## What the fraction slash cost

It is worth being precise about what was wrong with it, because 0016 chose it
carefully and the reason it fails is not the reason it was chosen.

A person cannot type it. Tab completion does not produce it. Copying
`…corpus⁄diffs⁄final-newline-lost⁄parent.txt.ops` out of a terminal and into a
command fails twice — once on the ellipsis and once on a character that looks
exactly like the one that would have worked. `grep -r` over the store finds
nothing under the name a person searched for. It is a homoglyph, which means
its whole design is to be mistaken for something it is not, and the store this
project is trying to build is one where nothing has to be decoded.

And it made the store's folder disagree with the folder beside it. 0011 says
the working copy is the folder next to the store; 0003 says a person should be
able to read the history without the tool. Those two together want
`history/operations/<revision>/` to look like the part of the repository that
revision touched. With `⁄` it looks like a list of mangled strings that
resemble paths.

The clip was the sharper cost. Sixty characters from the left of a path is
enough for the tail that distinguishes it, which was 0016's argument, and it
is still a name that has thrown information away — one a person cannot pass to
any other program, and one two different paths can share, which is why there is
a collision rule at all.

## What nesting removes

Both of those, and the machinery under them:

- the character, and the paragraph justifying it;
- the clip, the `…`, and the byte budget that produced them;
- the collision case they created — **two different paths can no longer produce
  one name**, because the only way two paths collide as directory trees is if
  they are the same path.

What is left is what a filesystem does anyway. The 255-byte limit applies per
component, and every component here already named a file on somebody's disk, so
it fits by construction rather than by arithmetic.

## Two names the format has to decide

**A payload that would carry `.ops`.** Two files apart in the format's own
extension: a payload for the path `x.ops` and an operation document for the
path `x` both want `x.ops`. The digest suffix parts them, on the last component
and inside the extension — `x 4a3a5224.ops` for the document, `x.ops 8aea1252`
for the payload — so a document never loses the extension that says it is one.

This paragraph first said the suffix was for the *collision*, and that was
wrong in a way recording Historica into its own repository found within the
week. A payload whose path ends in `.ops` is filed under a name the loader
hands to the parser **whether or not a document is there to collide with**, and
this project's corpus is full of `.ops` files written to be invalid, so the
store refused to open on a document it had itself written. The rule is
therefore the stronger one it should always have been: **a payload never
carries the document extension**, and takes the digest suffix whenever its own
name would end in one. The collision above is then a case of that rule rather
than the reason for it.

**A file where another file needs a directory.** 0008 says there are no
directories: a path is a string, and nothing stops a history holding both
`notes` and `notes/photo.png`. No working copy can hold both, so this arrives
only from a hand-written store or a merge that put two files at paths that
disagree about what `notes` is — and a filesystem cannot file it either. The
rule is that the file at the shorter path yields: it keeps its digest name at
the top of the revision's directory, where nothing can be a directory over it.
Deterministic, derived from the paths alone, and it costs the readable name on
exactly the file whose path was already in dispute.

The first is reachable from an ordinary folder and was reached from this one.
The second is not: no working copy can hold a file and a directory of one name,
so it arrives only from a hand-written store or a merge. It is written down
anyway, because a format that only works on the inputs its author imagined is
not a format — and because the first case is what that sentence costs when it
is believed too early.

## What it costs

**A revision's directory holds a skeleton.** A revision that edits one file
five directories down files five directories to get to it, and a store with
five hundred such revisions holds five hundred shallow trees. Directory entries
are cheap and a person opening one revision's folder sees the shape of what
that revision touched, which is the thing being bought. But it is more inodes
than a flat directory of names, and a store synced by a tool that charges per
file will notice.

**A path can still be too long overall.** Nesting bounds each component and
does not bound the total, so a deep path plus the store's own prefix can exceed
what a platform allows for a whole path. This is strictly smaller than the
hazard it replaces: it fails as an I/O error naming the file, at the moment
`arrange` tries to create it, rather than as a name that silently threw away
what distinguished it. A person who hits it can leave that store unarranged,
which 0016 already establishes is a correct store that is merely tedious.

**Two revisions that edit one file each file the whole path again.** 0016
already said a document two revisions name lives under one of them; nesting
does not change that, and the directories leading to it are simply repeated
under each revision that has one.

## Consequences

- `arrange` drops `filename`, `PATH_CHARS`, and the clip; the name of a thing
  is now the path with `.ops` appended, or the path.
- `arrange` creates directories to any depth, and tidies upwards, one
  `remove_dir` per level until one refuses.
- The collision pass compares whole relative paths rather than filenames, and
  the two remaining collisions are the ones above.
- The loader needs no change at all. 0016 already made the walk recurse to any
  depth and never follow a symbolic link, which is exactly what this asks of
  it — the reader that was built for one level of nesting reads five.
- `check` needs no change: `FilenameLies` fires on a *stem that parses as a
  digest*, and a path component does not, which is the same reason 0016 gives.
- The store of this repository, arranged, becomes a folder per revision holding
  the subtree that revision touched, with `docs/decisions/0018-a-path-is-a-path.md`
  inside one of them under exactly that name.

## Rejected alternatives

**Keeping `⁄` and dropping only the clip.** Half the cost for none of the
benefit: the name is still untypeable, still ungreppable, and still not the
path.

**A path-shaped name with the real separator, unnested.** Not available.
`notes/photo.png` in a filename *is* nesting, on every filesystem this runs on.
There is no third option here, which is the whole reason the fraction slash was
reached for.

**Nesting only where a path has a separator in it, and flat otherwise.** Two
schemes to learn and one of them arbitrary. A single-component path nests
trivially — it is one file in the revision's directory — so the general rule
already covers it.

**Keeping the flat scheme and adding a command that prints where a document
sits.** A tool answering a question the folder should answer. 0003's promise is
about the folder.

## Resolved questions

1. **Whether `arrange` should refuse a store it cannot fully arrange**, rather
   than arranging what it can and reporting the file whose path was too long.
   Answered by [0025](0025-the-folder-is-asked-for.md): it arranges what it can
   and returns structured failures, so a stricter caller may refuse.
2. **Whether a revision's directory should hold the files it did not touch**,
   as empty directories or otherwise, so that the folder is the tree at that
   revision rather than the diff of it. Refused implicitly here — the directory
   means "what this revision did" — but a person browsing may want the other
   thing. [0027](0027-closing-the-small-questions.md) confirms the refusal:
   untouched files would make the readable diff a second snapshot
   representation; `files` and `cat` answer tree questions.
