# 0081 — Who states a file

[0031](0031-a-document-states-its-result.md) made every operation document
name the digest of the file it produces, and
[0032](0032-a-merge-states-its-resolution.md) made a merge name its
resolution for every file its parents disagree about. Between them, a file's
content at revision R is what the nearest revision stating it says. That
statement is unique, because a merge that did not mention the file has the
answer on exactly one side.

The store did not use this to find the file. `stated_content` answered one
file at a time. It walked from R through every revision that said nothing
about the file, until it reached one that did. A file untouched since the
import was a walk to the root. `status` asks that question of every file, so
it cost files × depth.

[The state at a revision without the walk](../tasks/closed/the-state-at-a-revision-without-the-walk.md)
measured it on a writer's shape: 5,000 files, one root revision, then one
file edited and recorded per revision. With the cache warm, `status` took
1,325 ms at 1,000 revisions and 3,297 ms at 2,000. `log`, which reads the
same revisions and asks nothing about files, took 27 ms and 59 ms. The
difference was the walk, repeated 5,000 times.

## The decision

- **One pass says who states every file.** `tree::stating` reads each
  revision once, in the causal order the tree merge already builds. For
  every file it keeps the revisions whose document has a `text` line or an
  `edit` line for it, beside the ancestry that orders them. The store builds
  it on the first content question of a command, keeps it for the rest of
  that command, and lets it go whenever a revision is inserted or removed.
  Nothing is written anywhere.

- **The walk jumps.** At a revision that says nothing about the file, the
  walk asks which statements that revision reaches, and which of those no
  other statement it reaches replaced.
  - One: the file there is the file at that statement, and the walk goes
    straight to it.
  - None: the file is absent there.
  - Several: that is concurrency, and the walk steps to the parents as
    before, where 0032's agreement between them decides it.

  Every revision the walk skips says nothing about the file, and every
  statement it skips is one the answer had already seen.

- **A survey compares a digest.** `status`, `record` and `update` ask of every
  file whether the folder's copy is still what history says. Where one
  revision states the file, its `text` line names the payload, and its `edit`
  names a document stating its result (0031). That digest is the comparison
  0043 already makes, so an unchanged file is settled without materialising
  it. The digest is not used, and the file is materialised as before, where
  there is no single stating revision, where the document states no result,
  or where the store holds any forgetting document: a redaction makes the
  file something no document's digest describes.

- **`check` walks every step.** It asks for the work rather than the answer
  (0035), so it takes neither the jump nor the digest.

## What it measured

On `cargo xtask bench files=5000 revisions=N lines=10 edits=1`, the shape
above, with the cache warm:

| | 1,000 revisions | 2,000 revisions |
|---|---|---|
| `log` | 31 ms | 62 ms |
| `status`, before | 1,325 ms | 3,297 ms |
| `status`, after | 84 ms | 137 ms |
| `update --dry-run`, before | 1,411 ms | 3,433 ms |
| `update --dry-run`, after | 163 ms | 193 ms |

`status` still grows with the history, by 53 ms per thousand revisions
against `log`'s 31. What is left is opening the store, which `log` pays too,
and merging the tree and building this index, which every command that asks
about files pays once. `update` still materialises each file it will write.
On the bench's default shape, where every revision edits every file, nothing
moved: a cached `status` is 9.6 ms, as it was.

## Why not the index the task proposed

The task chose **a derived index under `cache/`**: a per-file log and an
ancestry labelling, kept on disk and believed while the set of revisions it
names is the set the store holds. The measurement is why it was not built.
The walk was expensive because it was repeated per file, not because
building the answer takes long. One pass over the revisions a command has
already read costs about what merging the tree costs, and the tree is merged
anyway. A kept index would save that pass and the open that precedes it, and
the open would still read every revision. It would also be a cache that
states a judgement no hash can check, which is what
[0049](0049-what-a-lookup-does-not-prove.md) declined to build for
`revisions/`. The next step past this is the one 0049 deferred: not opening
every revision at all. That is a different decision.

**A revision states its result tree**, a `tree` header naming a flat list of
paths and digests, is still refused for 0008's reason. It is Git's tree
without the subtree sharing. It would also raise the format version to save
work this pass now does in memory.

**An edit names its predecessor** makes a file's history a linked list. It
still needs the entry point this pass finds, so it adds nothing here.

## What this does not change

- **Answers.** The jump reaches the revision the walk would have reached,
  and a comparison of digests is the comparison 0043 made after
  materialising. `src/store/stating_tests.rs` asks every file at every
  revision of every hand-written corpus store that holds files, and of a
  history with branches and merges, both ways and gets the same answers.
  Wherever a digest is stated, it is the digest of what materialising
  gives.
- **Opening a store**, which reads every revision document, and **the tree
  merge**, which replays every tree fact. Both are linear in the history and
  both are what `log` pays. 0049's deferred question is where either would
  change.
- **The cache.** Nothing here is kept between commands, so deleting the cache
  changes nothing this decision adds.
