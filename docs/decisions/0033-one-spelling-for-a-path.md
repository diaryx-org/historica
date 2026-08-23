# 0033 — One spelling for a path

0008 looked at this and left it alone, deliberately:

> Two paths that differ only in Unicode normalisation, or only in case, are two
> paths here and one file on macOS or Windows. The format compares bytes;
> `check` reports the collision as a note, in 0006's sense — a real hazard that
> is not the store contradicting itself.

0027 kept that answer, and 0011 and 0030 both filed the case away as one that
needed to be in front of somebody before it could be decided. It is in front of
us now, and the two halves of it turn out to have different answers.

**Case is genuinely two names.** `README.md` and `readme.md` are different
files a person may deliberately have, and folding them would be this tool
deciding something about somebody's repository that is none of its business.
0008 is right, and nothing here touches it.

**Normalisation is not.** `café.md` written with U+00E9, and `café.md` written
with `e` and U+0301, are not two names anybody chose. They are one name, and
which byte sequence you get back depends on the filesystem, the editor, the
keyboard layout, and the decade. HFS+ normalised every name it stored to NFD.
APFS preserves what it is given and matches without caring. Linux preserves and
matches on bytes. So the same person, doing the same thing on two of their own
machines, produces two paths — and under 0008's byte comparison, two files, a
`drop` and an `add`, and a history that says work was deleted and rewritten
when nothing of the sort happened.

That is not a hazard for `check` to note. It is Historica getting the wrong
answer to "is this the same file", which is the one question 0008 built file
identities to make answerable.

## The decision

- **A path in a document is in Unicode normal form C.** `check_path` refuses
  one that is not, on the terms it already refuses a leading slash: exactly one
  spelling parses, which is the rule every other value in this format is held
  to.
- **A path arriving from outside is normalised on the way in.** The working
  copy's walk, a `--move` or `--at` a person typed, a rule in `skipped.txt`, a
  path argument to `cat` or `forget`. Normalising is idempotent, so a boundary
  can apply it without knowing whether another one already has, and it is a
  no-op on every ASCII path, which is very nearly all of them.
- **The folder keeps the spelling the folder has.** The store records `café.md`
  composed; if the folder holds it decomposed, that is the file `update`
  writes to. Historica is not in the business of renaming somebody's files to
  suit its own bookkeeping, and a composed twin laid beside a decomposed
  original is the exact failure this decision exists to prevent.
- **Case is untouched.** 0008's second open question is answered by half: the
  normalisation half is closed here, and the case half stays exactly as 0008
  and 0027 left it — two paths, a note, and a materialising command that must
  refuse where the folder cannot hold both.

## Why the store, and not just the comparison

The cheaper-looking answer is to leave the format alone and compare paths
under normalisation wherever they are compared. It fails on the first thing
this project promises. A person reading `history/` with an editor sees the
bytes; if two revisions spell one path two ways, they see two paths, and no
amount of correct comparison inside the tool makes the folder say what is
true. 0003's readable store is readable to a person who does not know what
normalisation is, and the way to keep that promise is for the ambiguity never
to be written down.

It also fails the digest. A path is a value inside a document that is named by
the hash of its own bytes, so two spellings are two documents, two revision
IDs, and two histories that are the same history. Comparison-time folding
cannot merge those; refusing to write the second one can.

And it is the same argument 0004 makes about the parser. A format that accepts
two spellings of one fact and quietly treats them alike has a canonical form it
declines to say out loud, and every reader has to rediscover it.

## What normalising costs

**A file whose real name is decomposed cannot be recorded under that name.**
On a byte-preserving filesystem, `cafe\u{301}.md` and `café.md` really are two
directory entries, and this decision makes Historica record only one of them.
Somebody who deliberately keeps both now has a repository the tool describes
wrongly — as one file, whose content is whichever of the two the walk reached
first.

This is worth naming plainly rather than waving at, and it is still the right
trade. Deliberately keeping two normalisations of one name is vanishingly rare
and, where it happens, close to indistinguishable from a mistake. Accidentally
producing them by using two computers is common. Between a rare deliberate case
the tool describes wrongly and a common accidental one it describes wrongly,
the common one wins — and `check` can grow a note for the rare one, which is
the shape 0008 already chose for the case collision it kept.

**A dependency.** `unicode-normalization` brings the Unicode decomposition
tables, which are not something to hand-roll and not something to approximate.
It is `no_std`-capable, touches no filesystem, and the `bare` job still passes.

## Rejected alternatives

**Normalise to NFD instead.** NFD is what HFS+ produced, so a store written
under it would match one class of macOS folders byte for byte. But NFC is what
the rest of the world writes: it is what W3C and IETF recommend for
interchange, what a Linux filesystem holds, what a text editor emits, and what
`git` records. A format whose paths are meant to be read, grepped, and typed
should spell them the way everything else does.

**Fold at comparison time only.** Above: the folder still says two things, and
two spellings still make two digests.

**Refuse the whole path, and make the person rename the file.** Correct in
some strict sense and useless in practice — the person did not choose the
spelling and often cannot see it, and a tool that refuses to record a file
because of an invisible property of its name is a tool nobody keeps using.

**Add 0008's designed-but-unbuilt `path-bytes` header** to carry the original
bytes beside the normalised path. It solves the deliberate-two-normalisations
case at the price of a header on paths that need nothing, and 0008 already
said what the bar is: "if importing such a repository ever becomes a real need
rather than a hypothetical one". It has not.

## Consequences

- `format::nfc` is the one place normalisation happens, and `check_path`
  refuses anything else. A revision document naming a decomposed path is
  refused where it is read, naming the path and saying why.
- The working copy's walk records the composed path beside the folder's own
  spelling of it, and `update` writes through the second.
- `history/format.txt` says so, because a person hand-writing a revision
  document needs to know which spelling their editor should produce.
- Stores written before this hold whatever they hold. A decomposed path in an
  existing store is refused at load, loudly, which is the same treatment every
  other format tightening gets in an unpublished version.

## Deferred

**Case.** Unchanged, and for 0008's reason: two cases are two names somebody
may have meant.

**A note for two paths that differ only in normalisation.** Impossible to
record now, so there is nothing left for `check` to find — but a store written
before this, or by another implementation, can hold one, and saying so is
kinder than refusing at load with no explanation of what to do. The refusal
names the path today, which is most of the value.

**Normalising anything but paths.** Author names, messages, and file content
are verbatim, and 0002 means it. A message is prose somebody wrote; a path is
a key.
