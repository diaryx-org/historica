# 0094 — What a command already worked out

[0081](0081-who-states-a-file.md) made one command's questions about files
cheap by answering them from one pass. A command that records many revisions
in a row asks the same questions again with every revision it adds, because
the revisions it just recorded are the history the next record reads.
`historica-git import` is that command. It records each git commit in turn
into one open store. Converting diaryx, 3,578 commits, took 31 minutes before
[a-merge-agrees-by-text](../tasks/a-merge-agrees-by-text.md) was worked on,
and far longer after. Three costs repeated:

- **A merge materialised every file.** 0081's survey compares a digest where
  a single revision states a file's content at the parent. A merge has
  several parents, so every file the merge's tree held was materialised once
  per parent and compared as text, including files neither side had touched.
- **A file edited again was replayed again.** `record` worked out the state
  a file was left in, wrote the document stating it, and threw the state
  away. The next record of that file replayed up to sixteen documents to get
  it back, before [0035](0035-the-cache-is-a-file-already-named.md)'s cache
  kept an entry.
- **Each merge's settling was worked out again at every later merge.**
  [0032](0032-a-merge-states-its-resolution.md)'s paragraph *Every walk reads
  it so, and only by keeping* settles each earlier merge whose sides made one
  edit. Settling one walks the file up to that merge, and every reader of a
  merge did it for every earlier merge of the file. A history with many
  merges of a file paid for each of them again at every merge it added.

## The decision

- **A merge compares digests too.** Where every parent states the digest the
  folder holds, the parents agree and the folder holds what they agree on,
  which is the case where a merge states nothing about the file. Anywhere
  else the file is materialised as before.

- **A state worked out is held for the rest of the command.** In memory, by
  the digest of its own bytes, and found the way 0035's cache entries are
  found: by the result digest a document states. A walk that replayed
  anything holds its answer. `record` hands over the state of every file it
  states operations for, under the digest of the folder text that state came
  from, so the next record of that file starts there. What is held is
  bounded at 64 MiB and let go of whole beyond it.

- **What a merge settled is kept, by file and by merge.** What is settled at
  a merge depends only on that merge's past, and a revision added later is
  never in an earlier revision's past. So it is worked out once per command.
  The merge nobody has recorded is never kept, since its parents are
  whichever heads were asked about. `check` keeps nothing, for 0035's reason:
  it wants the work.

- **Both are emptied where the cache is.** Forgetting and pruning clear the
  cache, and clear these with it. A state held from before a forgetting would
  be the bytes [0014](0014-forgetting.md) promises are gone. A settling
  worked out over them could read a forgotten line where the walk now reads
  its marker.

## What it measured

`historica-git import`, with its own 0014 recording each commit by the paths
it changed:

| | before | after |
|---|---|---|
| prov, 535 commits | 11.7 s | 2.8 s |
| leaf, 1,077 commits | 42 s | 10 s |
| diaryx, 3,578 commits | 31 min | 7 min |

## What this does not change

- **Answers.** A held state is the state its digest names, as a cache entry
  is, and a kept settling is the one the walk would work out again.
  Converting prov and leaf writes histories byte for byte what they were.
- **Between commands.** Nothing new is written to disk, so deleting the cache
  changes nothing this decision adds.
- **The tree merge and 0081's pass**, both rebuilt from the whole history
  whenever a revision is added. Each is linear, so a conversion pays for them
  quadratically, and they are most of what is left. Building either
  incrementally goes through the ancestry the proofs cover.
