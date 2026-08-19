# 0003 — The store: content is identity, names are presentation

A history is a directory of revision documents, and Historica builds the graph
by reading files, never their names. Each file's revision ID is the SHA-256 of
its bytes; `parent` and `supersedes` lines resolve against those digests; the
filename participates in nothing.

```
history/
├── historica       # `historica-v0`, per decisions 0002 and 0004
├── revisions/      # one revision document per file, under any name
├── operations/     # what each revision did, per file — added by 0007
├── names/          # bookmarks — the only mutable files
└── cache/          # derived, disposable, deletable without loss
```

## The tension this resolves

A content-addressed store seems to want every file named by its own digest,
and a folder of `1e4e224e….rev` is a ledger, not a story: `ls` shows nothing,
order is invisible, and nobody hand-authors a file whose name is its own hash.
As long as the filename is load-bearing, the store can never look hand-made,
and "readable files are the authority" quietly shrinks to "readable file
*contents* are the authority, but the folder is for machines".

The corpus already disproves the necessity. `tests/corpus/revisions/` is named
`01-root.rev` through `07-verbatim-message.rev` — numbered, slugged, readable
top to bottom like a story — and it is a genuine five-change history whose
every cross-reference is a real digest that `shasum` confirms. Nothing about
it depends on its filenames. This decision makes that the rule rather than an
accident: the corpus is not a stand-in for a store, it *is* one, hand-arranged.

## The identity rule

Loading enumerates `revisions/`, parses each document under decision 0002's
strict rules, and takes the digest of the file's bytes as its revision ID.
From that, everything else follows:

- **Renaming a file changes no identity and breaks no reference.** Layout is
  a presentation operation, as free and as meaningless to the model as
  re-rendering a log.
- **Two files with identical bytes are one revision stored twice.** Keeping
  both is harmless; deleting either is safe; dedup is tidying, not merging.
- **A file that does not parse is an error naming the file**, never a skip.
  Strictness where the machine reads, exactly as in decision 0002.
- **"Two revisions claiming one digest" becomes unrepresentable on disk.** A
  file's digest is whatever its bytes hash to; a *claim* exists only in
  references and in transport, which is where the core's hard error (decision
  0001's first row) continues to apply.

Verification still needs no Historica. `shasum -a 256` on any file yields its
true name, and searching the folder for that digest finds every reference to
it. What a person cannot do by eye is confirm a digest is *absent* — that a
head is really a head — which is taken up under "What this trades away".

One deliberate carve-out: **the `.rev` extension is load-bearing.** Only
`*.rev` files under `revisions/` are read as revisions. The extension is the
file's claim to be one; everything else — `.DS_Store`, editor droppings — is
ignored without comment. The alternative, parsing everything and erroring on
the junk, would make the strictness rule fire on files that never claimed to
be history. The extension is the one syllable of the name that means
something; the rest is free.

## The default writer: digest names

The tool's writer stays canonical, in bytes (decision 0002) and in names: it
writes `<digest>.rev` into a flat `revisions/`, appends only, and never
renames or overwrites. That default has three properties worth keeping:

- **Self-verifying per file.** The name states the expected digest, so a
  one-line shell loop audits the whole store with no other input.
- **Conflict-free under any file sync.** Same name implies same bytes, so
  rsync, Syncthing, iCloud, or `cp -n` can never manufacture a conflict here.
- **No coordination.** Two replicas that deterministically produce the same
  revision — both rebasing onto the same amended ancestor — write one file.

The directory is flat on purpose. Git shards objects into 256 subdirectories
for filesystem performance at millions; a history at journal scale holds
thousands, and a flat directory is browsable. Sharding is itself a naming
scheme — presentation — so it can be adopted later without rewriting anything.

## Arranged stores

Because names are free, a person — or an `arrange` command — may impose a
readable layout on the same files:

```
revisions/
├── 2025-08-19 start the readable core.rev
├── 2025-08-19 reject duplicate digests.rev
├── 2025-08-19 name undelivered parents.rev
├── 2025-08-19 merge.rev
└── 2025-08-20 reject duplicate digests, reworded.rev
```

A date from `when` and a slug from the summary line make the folder
self-narrating in a file browser, with no tool installed. Decision 0002 keeps
timestamps out of identity, causality, and ordering — which is exactly what
frees them for presentation: a misleading date in a filename misleads a
person, but cannot mislead the model, because the model never looks.

The scheme is advisory. Names may collide, drift, or lie; `arrange` may be
rerun; a merge with an empty message needs a fallback slug; none of it carries
correctness weight. The one hard rule an arranged store keeps is the format
inside the files.

Hand-authoring follows the same shape: copy an existing `.rev`, edit the
headers and message, run `shasum` on the parent file to fill in its digest.
That procedure needs a text editor and coreutils, which is the promise — an
escape hatch a person can actually take, not the daily interface. Day to day,
the tool writes canonically and a person reads.

## names/

The identity rule governs revision documents. `names/` is the deliberate
exception, because bookmarks are exactly the part of a repository that *is*
names: mutable files whose filename is the bookmark and whose single line is
what it points at.

```console
$ cat history/names/main
change qpvuntsmwlrkzxonmvtplsyq
```

A name holds one header-shaped line: `change` plus a change ID, or `revision`
plus a digest. The disjoint alphabets from decision 0001 make the two
unmistakable even without the key. `change` is the default and the point —
the bookmark follows amend and rebase automatically, which resolves the
question 0001 deferred. `revision` is the exact pin for the rare reference
that must not move.

These are the only mutable files in the store, so they are the entire
conflict surface. Two replicas moving `main` concurrently is a real
disagreement about where a name points; sync will surface it as a conflicted
file, and the tool must present it as a choice, never resolve it silently.

## Sync is union by copy

The core merges histories by set union; this layout makes union a file copy.
Digest-named files cannot conflict. Arranged stores add one benign wrinkle:
two machines may mint the same friendly name for different revisions, and a
sync tool will keep both as conflicted-copy siblings — which is correct, since
both files are legitimate revisions and the graph unions them regardless of
what they are called. Tidying the names afterwards is optional and safe.

## What this trades away

- **Lazy loading by name.** With advisory names, resolving one digest means
  having read the store. At journal scale a full read is cheap; beyond it,
  `cache/` restores O(1) lookup and stays disposable — the recovery test from
  decision 0001 (delete every cache, confirm every change ID resolves
  identically) is unchanged.
- **Tamper-evidence at unreferenced heads, in arranged stores.** Tampering
  with interior history changes a digest and dangles every reference to it:
  detected. A tampered *head* under an advisory name is simply a different
  revision — not a detectable lie, because nothing names the original. The
  digest-named default keeps per-file evidence day to day; arranging trades
  it away knowingly. Pinning heads is the job of `names/` entries that record
  a revision, and eventually of signatures — the same place Git ended up,
  where objects are immutable and refs are the trust frontier.

## Consequences

- Decision 0002's closing line — "a revision file is named by its digest" —
  is demoted from format rule to writer default. This document supersedes it.
- Store verification is a whole-store pass: every `*.rev` parses, every
  reference resolves, and name-equals-digest is checked only where the name
  makes that claim. A `check` command is required interface work.
- `arrange` and the fallback slug rules become interface work of the same
  kind — owed to users, not to correctness.
- The tree and content model, called decision 0003 in earlier documents, is
  renumbered and also split. Resolving the open questions first took 0004
  through 0006; content and merge then became
  [0007](0007-content-and-merge.md), which introduces `operations/` and defers
  paths, directories, and rename to the tree in 0008.

## Resolved questions

Questions 1 through 4 are answered by
[0006](0006-store-questions.md):

1. **Whether a name should record both facts.** No — one line. A second line
   that can disagree with the first needs a precedence rule, goes stale by
   design, and defends only against something that cannot edit both.
2. **Conflicted-copy hygiene.** `check` reports errors and notes; duplicates
   and sync-suffixed names are notes, which never fail.
3. **The store root** is `history/`, visible, with no per-repository choice.
4. **The arrange scheme** stays advisory but must be deterministic across
   replicas, so collisions resolve by change ID rather than by a counter.

## Open questions

5. **When scale forces sharding**, and whether a shard prefix is ever anything
   but one more advisory name.
