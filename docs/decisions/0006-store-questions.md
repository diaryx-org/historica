# 0006 — Bookmarks, the store root, and what `check` says

Decision 0003 established that content is identity and filenames are
presentation, and left five questions open. Four of them block interface work
that is now the next thing to build. This document answers those; the fifth,
sharding, is deferred at the end for the reason 0003 gave itself.

## A bookmark holds one line

0003's first question asked whether a name should record both facts — a
`change` to follow rewrites, plus a last-known `revision` as a tamper anchor
and offline resolution hint.

It should not. A name holds exactly one line, `change` or `revision`, as 0003
described it.

The two-line form looks free and is not. A second line that can disagree with
the first needs a precedence rule, and every reader — including a person with
`cat` — has to know it. It goes stale by design, so the common case is a
disagreement that means nothing, which trains people to ignore the line that
was supposed to be evidence. And what it defends against is narrow: a witness
stored in the same mutable file as the pointer stops anyone who can edit one
but not the other, which is a sync tool, not an adversary.

The pin that question was reaching for already exists. A name that must not
move is spelled `revision` and names a digest, and 0003 said so. Head
tamper-evidence beyond that is a signatures problem — the same place 0003
concluded Git ended up, where objects are immutable and refs are the trust
frontier.

```console
$ cat history/names/main
change qpvuntsmwlrkzxonmvtplsyq
$ cat history/names/v0.1.0
revision c9f5c7d252115911e399bccf5c24d16e34a21f9f8db2736746378edc4df68b68
```

The disjoint alphabets of decision 0001 make the two unmistakable, so the key
is a courtesy to a reader rather than information the parser needs.

## The store root is `history/`, and it is visible

0003's third question offered `history/` or `.historica/`, possibly per
repository.

It is `history/`, always, with no choice.

A dotted directory is the filesystem's way of saying *this is not for you*.
Adopting it would contradict the sentence the project is built on: the readable
files are the authority. A store a person is expected to open, read, and
hand-edit in an emergency cannot announce itself as machine territory.

The per-repository option costs more than it looks. Two layouts mean a
discovery rule, two paths in every document and every error message, and a
question at `init` whose answer is cosmetic and permanent. Someone who wants
history out of the way can put the store in a subdirectory; the model never
reads the path.

Discovery walks up from the working directory looking for a `history/`
directory that contains a `historica` file — the file, not the name, so an
unrelated folder called `history` is not mistaken for a store. Per decision
0004 that file now reads:

```
historica-v0
```

## `check` separates errors from notes

0003's second question asked whether `check` should point out duplicate content
and sync-suffixed names, or stay silent about what this decision calls
legitimate.

Neither. `check` reports at two levels, and only one of them fails.

**Errors** are the store contradicting itself:

| Error | Why |
| --- | --- |
| A `*.rev` file does not parse | Decision 0004's strict read, naming file and line |
| The `historica` file is absent or an unknown version | Nothing can be read safely |
| A filename that claims a digest states the wrong one | The name made a claim and it is false |
| Two files with one digest and different bytes | Impossible on disk, so it means a broken read |
| A `names/` entry that is not one valid line | The only mutable files, so the only ones that can be malformed |

[0007](0007-content-and-merge.md) adds one more: an operation document whose
recorded `-` lines disagree with the parent state. It is an error rather than a
note for the reason the rest of this table is — the store contradicting itself.

**Notes** are observations that never fail:

| Note | Why not an error |
| --- | --- |
| A `parent` digest naming no file | Transport has more to deliver; `History::missing_parents` calls this ordinary |
| A `names/` entry naming an unknown change or revision | Same: the name may be ahead of the sync |
| Duplicate content under two filenames | 0003: keeping both is harmless, dedup is tidying |
| Sync-suffixed names (`… (conflicted copy).rev`) | Both files are legitimate revisions |
| Non-`.rev` files under `revisions/` | 0003 ignores them without comment; a note is that comment |

A `supersedes` digest naming no file is neither. Decision 0001 made the
successor carry the evidence *so that* the predecessor may be absent; reporting
it would report the feature.

The division is the same one that runs through the whole format: strict where
the machine reads, friendly where the person reads. `check` exits non-zero only
when the store cannot be trusted, so it can be run in anger without teaching
anyone to ignore it.

## `arrange` must be deterministic

0003's fourth question left the arrange scheme as a tool convention. It stays
advisory, but it acquires one hard constraint that is not about taste.

**Two replicas arranging the same history must produce the same filenames.**
Otherwise sync sees two files per revision, and a scheme meant to make a folder
readable fills it with conflicted copies. This is the canonical-bytes argument
from 0002 applied to names: determinism is what keeps convergence from
manufacturing work.

The scheme:

```
YYYY-MM-DD summary.rev
```

- The date comes from `when`, rendered in the offset the file carries, because
  a presentation layer should show the date the person experienced. Decision
  0002 keeps timestamps out of identity and ordering, which is exactly what
  frees them for this.
- The summary is the message's first line, with `/`, control characters, and a
  leading `.` replaced, and a length limit applied at a word boundary.
  Non-ASCII is preserved: this is a filename shown to a person, not an
  identifier, and a journal is written in its author's own language.
- An empty message falls back to the change ID's first characters, which
  decision 0001 calls the name a person can learn.
- A collision appends the change ID prefix rather than a counter. A counter
  depends on what else is in the directory, so adding a revision could renumber
  its neighbours and two replicas could disagree; a content-derived suffix
  cannot.

None of this carries correctness weight, and it may change without a format
version bump, because nothing reads it.

## Consequences

- `init`, `check`, and `arrange` are now specified enough to build, and are the
  first commands owed.
- The repository header file is `history/historica`, containing `historica-v0`.
- `names/` parsing is a second, much smaller strict parser: one line, one key,
  one identity in the matching alphabet.

## Deferred

**Sharding** (0003's fifth question) stays open and needs no answer. 0003
established that a shard prefix is one more advisory name, so adopting one
later rewrites nothing. A flat directory is browsable at journal scale, and the
question becomes real only with evidence that it is not.

**Spelling paths that are not valid UTF-8** (decision 0002's third question)
cannot be closed here: nothing in the format has a path yet. It belongs with
the first path, which is the tree's — and the tree is now 0008,
[0007](0007-content-and-merge.md) having taken content and merge without
introducing a path of its own. [0008](0008-tree.md) later closes it by requiring
UTF-8 rather than introducing an escape.

## Answered by building it

1. **Whether `check` should hash every file or only digest-named ones.** The
   choice turned out not to exist. Identity comes from content, so a file's
   digest is what loading *is*: `Store::open` must hash every file to know what
   it holds, and `check` reads the same files. The cheaper option was an
   illusion created by thinking of the digest as verification of a name rather
   than as the name itself. Checking a digest-named file's name against its
   content is the extra step, and it is one string comparison.
2. **What `init` writes.** Four directories — `revisions/`, `operations/`,
   `names/`, `cache/` — and a `historica` file holding one line. It refuses a
   directory that is already a store rather than merging into it. Whether that
   is worth a *command*, as against `mkdir` and a here-document, is a question
   for the front end and not for this decision.

## Resolved questions

3. **Which sync-suffixed spellings are worth recognising.** `check` notes
   no spelling specially, by [0027](0027-closing-the-small-questions.md).
   Duplicate content is already a note; guessing which program chose its
   filename adds a claim the store cannot verify.

## Since

The summary rule above named three things a stem gives up — `/`, control
characters, and a leading `.` — and stopped there. That list was drawn from
what a *name* cannot hold, on the systems this was written on. What it missed
is that a store's whole argument is that it travels: 0029 receives one, 0042
carries one away, and the media both of those actually ride on are formatted
FAT, exFAT or NTFS, which refuse `\ : * ? " < > |` in a name outright.

So a message reading `Fix: the parser?` composed a stem no copy onto a memory
card could write. The store was not damaged by it — identity is content, and
a renamed file is still the file — but the copy itself failed, and a copy tool
that mangles rather than fails leaves two replicas naming one history two ways
until somebody runs `arrange`. Either way the folder that was supposed to be
readable anywhere was readable in fewer places than a `.zip` of it.

**The summary gives up everything a filesystem reserves.** `\ : * ? " < > |`
join `/` and the control characters, each replaced by a space, and a trailing
`.` joins the leading one. The trailing dot is not decoration: a stem is a
*directory* name in `operations/`, and Windows drops a trailing dot from one
silently, so two stems differing only there would arrive as one folder — the
determinism this decision insists on, broken by the copy rather than by the
scheme.

**A path is not touched, and the asymmetry is the point.** `scrubbed` still
takes only control characters out of a path, because a path named a real file
in somebody's real folder: the characters in it are theirs, they already
survived one filesystem, and a store that could not be copied because of one
is a store whose *working copy* could not be copied either. A summary is the
opposite case in every respect — historica composes it, from prose nobody ever
typed as a filename — so a character it cannot carry is one historica invented
the problem with.

Nothing here is a format change, for the reason stated above: none of it
carries correctness weight and nothing reads these names. What it costs is
that a store arranged by an older version has stems this scheme would spell
differently, which is [0019](0019-the-name-a-store-is-written-with.md)'s first
case exactly — the scheme changed, and `arrange` is the command that applies
it.
