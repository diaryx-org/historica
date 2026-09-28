# 0078 — Where a cache is kept

[0003](0003-store.md) reserved `cache/` inside the store, and
[0035](0035-the-cache-is-a-file-already-named.md) put the first cache there:
files as they stood at a revision, named by their digest. Four more followed
into the same directory. [0036](0036-where-a-digest-is.md)'s catalogue of
`operations/`, [0043](0043-what-a-command-does-not-have-to-read.md)'s catalogue
of the folder, [0058](0058-what-a-command-does-not-have-to-open.md)'s copy of `revisions/`, and the
writer's catalogue [0077](0077-a-writer-believes-the-catalogue-it-holds.md)
keeps as each revision lands. Each argued what may be believed about a cache.
None argued where one should be, because 0003 had already said.

0003 also says a store is synced by anything that copies files, and that is
the argument against the place. A sync cannot tell a cache from content, so it
carries the cache to every device, where it was never true.

- **A cache can undo a forget.** Replica B reads a file and keeps its state.
  Replica A forgets a line of it; `forget` destroys the original and empties
  A's `cache/`. The sync then carries B's `cache/` to A. A reader on A takes a
  state by the digest the unredacted document states, before it asks whether
  anything forgets what produced it, so it prints the forgotten line. `check`
  reads nothing from `cache/` and finds nothing wrong. This was reproduced
  before this decision, and it breaks [0014](0014-forgetting.md)'s promise that
  the bytes are gone from the store.
- **Some of it is only true on one device.** `working.txt` records each
  file's size and modification time, which are facts about one device's copy
  of the folder. `revisions.txt` is believed against the times one filesystem
  reports.
- **It is the store's busiest file.** `operations.txt` is rewritten at every
  revision and grows with the history, so every record uploads it again. Two
  devices recording at once give a sync service a conflict to resolve on a
  file nothing needs. A kept state is a whole file, and many of them can
  outweigh the store.
- **Every copy has to deal with it.** `export` cleared the copy's `cache/`
  when it destroyed anything, and the copy's own catalogues were among the
  files that every publish rewrote.

[prov](id:prov/1ch2991) reached the same answer for its write-ahead journal:
state that belongs to one machine lives in a directory the host owns and
nothing syncs, and the host says which.

## The decision

- **A store holds no cache.** `init` makes no `cache/`, and nothing writes
  one. The store is revisions, operations, names and rules again, which is
  what a sync is for.
- **The host names where a store's caches are kept, or nothing is kept.**
  `Store::open_caching_on(files, root, cache)` keeps every cache 0035, 0036,
  0058 and 0077 describe in `cache`, on the filesystem the store was opened
  on. `Working::read_caching_on` keeps 0043's there too, and
  `Store::cache_directory` says which directory to give it. `Store::open_on`
  and `Working::read_on` keep nothing. 0035 already makes that a question of
  time alone: every answer is the one a cached store gives.
- **Three obligations come with the directory, and all are the host's.**
  - *One directory, one store.* Nothing records which store a cache was for,
    and two stores sharing one would each read the other's catalogues.
  - *Not inside the store*, where a sync carries it. A directory under the
    store's root is ignored, since that obligation is the one the store can
    see.
  - *The store's clock.* 0043's rule believes a catalogue entry only where it
    is strictly older than the catalogue, measured by the times one
    filesystem reports for both. A cache on a volume stamped by another clock
    weakens that rule for a file rewritten in place in the moment the
    catalogue was written.
- **A writer checks a `yes`.** 0077 lets a writer believe the catalogue it
  holds. A cache kept outside the store can outlive it: a folder deleted and
  made again at one path finds its predecessor's catalogue, and a `yes` from
  it named bytes the new store never held. Believed, that `yes` left the bytes
  unwritten and the revision naming them unreadable. So a writer hashes the
  file a `yes` points at before it skips a write. That is paid only when the
  same bytes are filed twice, which is rare, and a `yes` that does not hash is
  a `no`. A `no` is believed as 0077 says.
- **A `cache/` left in a store is deleted when the store opens.** It is
  derived, so nothing is lost, and it may hold the state described above,
  which is 0014's promise broken for as long as it stays. `check` opens
  without deleting it, since `check` writes nothing. `CACHE_DIR` stays
  reserved as `Travel::Derived`, so transport still leaves one behind.
- **The command line names one directory per store** below a base:
  `--cache-dir <dir>` before the command, or `HISTORICA_CACHE_DIR`, or
  `XDG_CACHE_HOME/historica`, or `~/Library/Caches/historica` on macOS and
  `~/.cache/historica` elsewhere. Each store's directory is named by the
  first sixteen hex digits of the digest of the store's canonical path. A
  store that moves starts again with nothing kept, which costs one slow
  command, and two stores never share a directory.

## What this does not change

0035 still decides what may be believed about a kept state: it is hashed
before it is used. 0036, 0043, 0049 and 0058 still decide what may be believed
about a catalogue, and `check` still takes no cached answer of any kind. What
moved is where the files are.

A cache kept on one device still describes that device's reads, so a
forgetting document that a sync brings still has to clear the states that
device kept before it arrived. `fix(store): a forget that arrives clears the
states read before it` does that, and it is unchanged here. The window
[A forget a sync brings is read only after a pass](../tasks/a-forget-a-sync-brings-is-read-only-after-a-pass.md)
describes is about the catalogue's claims, not where it is kept, so it is
still open.

## Consequences

- `Store::open_caching`, `Store::open_caching_on`, `Store::cache_directory`,
  `Working::read_caching` and `Working::read_caching_on` are new. None of the
  existing API is removed.
- `Store::open`, `Store::open_on`, `Store::discover`, `Store::init` and
  `Working::read` now cache nothing. A host that relied on them caching gets
  the same answers, more slowly, until it names a directory.
- `init` no longer writes `cache/README.txt`, and `historica.txt`'s note no
  longer lists `cache/`.
- An `export`'s copy holds no cache, so a publish no longer rewrites the two
  catalogues it used to carry. The price is the one
  [An export restates its indexes whole](../tasks/an-export-restates-its-indexes-whole.md)
  named: the copy is opened with nowhere to keep anything, so an export onto
  a copy it already made opens its revisions and reads its operations in
  full on every run. That cost falls on the machine publishing, not on
  whoever fetches.
- `receive` opens the store it reads from without a cache. That store is read
  once, perhaps from a drive this machine sees once.
