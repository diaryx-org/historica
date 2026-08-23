# 0035 — The cache is a file already named

0003 reserved `cache/` and made it one promise:

> Binary indexes and snapshots may eventually exist as disposable caches, but
> deleting every cache must lose neither information nor meaning.

Nothing has ever been written there. Meanwhile 0007 made the operation
document authoritative and the file derived, which means the file at a
revision is *replayed from the root of its history, every time anybody asks*.
`cat`, `status`, and `update` each pay that walk on every invocation, and it
is linear in how long the file has existed. A history is a thing that only
gets longer.

Measured on a store of thirty files, a hundred and twenty revisions and four
hundred lines each — `cargo xtask bench` builds it — `status` spent most of
its time replaying histories it had replayed on the previous run and thrown
away.

The obvious cache is the file at a revision. The obvious problem with it is
the one every cache has: knowing when it went stale. That problem is what has
kept `cache/` empty, and it is worth being precise about why it does not
actually arise here.

## The decision

- **An entry is a file named by the SHA-256 of its own bytes**, holding the
  content of some file at some revision. `cache/<digest>`. It is the same rule
  every other directory in the store follows, and it is the whole design.

- **An entry is found by a digest a document already states.** 0031 made every
  content document state the digest of the file it produces. So the mapping
  from *a revision and a file* to *a digest* is already in the store, already
  readable, and already what a hand replayer checks their work against. The
  cache supplies the other half — digest to bytes — and invents nothing.

- **Bytes are hashed before they are believed.** This is what removes
  invalidation as a question rather than answering it. Content named by its own
  digest either is what it claims or is discarded, so an entry written by an
  older version of this program, half-written by an interrupted one, or edited
  by a person is refused at the point of reading. There is no state in which a
  stale entry is *returned*; there is only one in which it is *ignored*.

- **An entry is written under the digest found, not the digest stated.** The
  distinction is what keeps a wrong entry unreachable rather than dangerous. A
  state carrying 0014's forgetting markers hashes to something no document
  names, so caching it files it where nothing will ever ask for it — instead of
  filing it under the digest of the bytes that were destroyed.

- **An answer is kept only when the walk paid for it.** A cache with no limit
  grows one entry per file per revision anybody ever looked at, which on a
  modest history is a `cache/` many times the size of the store. Keeping only
  the answers that cost something turns entries into checkpoints: a walk stops
  at the first one it meets, so it replays a bounded number of revisions and
  the store holds at most one entry per file per that many revisions. The
  number is a guess — deliberately a round one, since both of the things it
  trades off are bounded by it, so being wrong is slow or roomy rather than
  incorrect.

- **`check` reads nothing from `cache/` and writes nothing to it.** Taking a
  cached state means not applying the operations that produce it, and so not
  running 0031's check that they produce what the document says they do —
  which is the check `check` exists to run. Every other command wants the
  answer; this one wants the work. It is also what keeps 0003's promise
  testable: something must still do the work when the cache is gone.

- **Forgetting and pruning empty it.** 0014 is a promise that bytes are gone,
  and a derived copy of them is still a copy. Everything in `cache/` is
  replayable by definition, so clearing it loses nothing that forgetting was
  not already taking.

- **Every failure to read or write an entry is ignored.** A store on a
  read-only filesystem, a full disk, and a `cache/` somebody deleted
  mid-command are all conditions under which reading a file must still
  succeed. There is nothing to report, because nothing was lost.

- **No format version.** An entry is not a document, claims nothing, is
  referenced by nothing, and is named in no grammar. A reader that has never
  heard of this decision deletes the directory and is correct.

## What this is not

It is not an index of `operations/`. Opening a store still reads every
operation document to find out which digest each one holds, because 0016 makes
a filename presentation and a document may live under any name — so the only
way to know what a file holds is to read it. On the bench store that read is
now the largest single cost of `status`, larger than everything this decision
removes. Fixing it means writing down where each digest was found, which is a
second cache with a real grammar, a real staleness question, and no help from
content addressing on the *mapping* it stores. It deserves its own decision,
with real-world measurements behind it.

## Deferred

**A `check` note about `cache/`.** Nothing there can be wrong in a way worth
reporting: an entry is either honest or ignored, and the directory is
deletable. A note saying how much disk it uses might be worth having when
there are stores large enough for the answer to matter.

**Eviction.** Nothing removes entries except forgetting and pruning. The
checkpoint rule bounds growth against history depth, not against how many
revisions a person visits, so a store somebody reads exhaustively at every
revision accumulates. `rm -rf history/cache` is a complete and supported fix,
which is a low enough floor to wait on evidence.

**Caching the tree.** The file set at a revision is derived by the same
argument and is asked for by `files`, `status`, and `update` alike. It is
cheaper to compute than a file's content and has no digest already stated
about it, so it would need something this decision did not have to invent.
