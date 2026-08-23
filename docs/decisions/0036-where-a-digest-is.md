# 0036 — Where a digest is

0003 put identity in content and made filenames presentation:

> Identity comes from content. Filenames are presentation.

That is the rule that lets a person file a history however they please, and
`arrange` exists to help them. It is also the rule that left the store with no
way to find a digest except to read every file in `operations/` and hash it.

0035 removed the cost of *replaying* a long history and left that one standing.
The measurement it was written against says so plainly. On the store `cargo
xtask bench` builds — thirty files, five hundred revisions, four hundred lines
each, fifteen thousand operation documents — `cat` at the head spent 330ms to
answer from a cache entry it already held, because reaching the entry meant
first opening and hashing fifteen thousand files to learn which one was which.
The cached and uncached numbers differed by less than a factor of two, and the
gap did not close as the cache filled, because the cache was never what was
slow.

Worse, it was paid by writers too. Every `insert_operation` asked whether the
store already held the document, and asking meant reading the directory — so
recording into a large history read the whole of it first.

## The decision

- **A catalogue says, for every file under `operations/`, the digest of its
  bytes.** It lives in `cache/`, and it is what turns "find this digest" from a
  pass over the directory into one read.

- **It is named rather than digest-named.** `cache/operations.txt`. This is the
  one way it differs from every entry 0035 describes, and the reason is that a
  catalogue is not content: there is nothing to look it up *by*. It carries a
  header line so that a catalogue written by a version that spelled it
  differently is discarded whole rather than half-understood, which is the only
  failure mode a fixed name introduces that a digest-named entry does not have.

- **It is believed under one condition: the set of paths it names is the set of
  paths the directory now holds.** That is checked by a directory walk, which
  lists names without opening anything, and the store already performs one.
  Anything the walk finds that the catalogue does not account for is read: a
  new path is read and hashed, a vanished path is dropped, and the catalogue is
  written back. So a `record` that wrote thirty documents costs the next reader
  thirty reads, and a store this program has never seen costs one full pass.

- **A lookup hashes what it reads before believing it.** The catalogue says
  where to look; it never says what is there. A path whose bytes do not hash to
  the digest asked for is not the file wanted, whoever renamed or edited it —
  the same rule 0035 applies to a cached state, one level up.

- **A catalogue that cannot answer costs a directory read, never an answer.**
  This is 0003's promise, and it is the part that took the most care. A lookup
  the catalogue misses falls back to reading `operations/` once, and only then
  reports an absence. So a catalogue that is deleted, stale, truncated, or
  deliberately wrong about every path it names produces exactly the answers a
  store with no catalogue produces, and differs only in how long it took.

- **Writers catalogue what they wrote, and do not write the file.** A writer
  knows the path, the digest, and what the document forgets without reading
  anything, so `insert_operation` no longer reads the directory to find out
  whether the store already holds a document. The catalogue file itself is
  written only where it is reconciled — a `record` that rewrote the whole
  catalogue once per document would be quadratic in the size of the store, and
  the cost of not doing so is that the next reader reads the files this one
  wrote.

- **`check` builds its catalogue by reading, never from `cache/`.** 0035 keeps
  that command away from every cached answer because it is the one caller that
  wants the work rather than the result. The reason bites harder here than
  there, and the next point is why.

## What is believed, and what is checked

Everything above hashes before it believes, with one exception, and it is worth
stating rather than burying.

Decision 0014 makes a forgetting document the thing a reader consumes in place
of the document it forgets. A reader must therefore know *every* forgetting
document in the store, and no amount of hashing one file tells you what is in
another. So the catalogue records, per entry, the digest that entry forgets —
and a reader believes the entries that say they forget nothing.

What protects that:

- **The path set is checked.** A forgetting document that arrived by any means
  — written here, received, dropped in by a sync — arrives as a *path*, and a
  path the catalogue does not name is read.
- **The claim is verified in the positive direction.** A catalogue naming a
  document as the stand-in for a digest is not taken at its word: the document
  is read, hashed, parsed, and asked again what it forgets. So a wrong
  catalogue cannot make a reader treat an ordinary document as a redaction.
- **The store never overwrites an immutable file.** Documents are written with
  `create_new` and are never rewritten in place, which is what makes "this path
  still holds the bytes it held" a rule rather than a hope.

What is left is one case: a document whose bytes were replaced *at an unchanged
path* by something outside this program, turning an ordinary document into a
forgetting one. `check` is what finds it, because `check` reads. That is the
same standing 0035 gave itself, and it is why `check` is excluded here too.

## What this is not

**Not a name-to-digest shortcut.** The obvious cheap trick is to notice that a
digest-named store can find a digest by its filename. 0019 makes the default
store readably-named, so the trick does not apply to the stores people actually
have — and it would make `arrange` a performance cliff, which is precisely the
thing 0003 exists to prevent.

**Not a second source of truth.** Nothing about the store's meaning is in
`cache/operations.txt`. Delete it and every answer is the same.

**Not a file-size or mtime index.** 0025 keeps `Filesystem` at nine methods and
gives it no metadata beyond what a directory entry is. A catalogue validated by
size or modification time would need a tenth, and would trade a rule the store
enforces for a signal the platform reports.

## Consequences

- `store::catalogue` is the new module: reading, reconciling, writing, and the
  format of the file.
- `Store::operation`, `Store::resolution` and `Store::forgetting` return owned
  documents rather than references, because a document is now read on demand
  rather than held in a map for the store's lifetime. `Store::operations` and
  `Store::resolutions` return maps for the same reason.
- `Store::operations` and `Store::resolutions` read the whole directory
  themselves rather than going through the catalogue, because their question
  *is* the directory: a document a person edited in place is one they must
  refuse over rather than pass by.
- A broken document now stops the question that needs it and nothing else,
  which is what the test of that name always claimed. Before this, one
  unparsable file made every content question in the store fail.
- The measurement that motivated this: at five hundred revisions, `cat` at the
  head goes from 330ms to 102ms and `status` from 346ms to 115ms, with the cold
  pass unchanged. What remains is linear in the number of documents rather than
  in the number of file opens, which is the shape a store can grow in.

## Deferred

**The revisions directory.** `revisions/` is read in full at open and always
has been, and a catalogue would serve it identically. It is smaller by the
number of files a revision touches, it is what `log` and `files` need in full
anyway, and nothing has yet measured it as the cost. When something does, the
mechanism is here.

**Bounding the catalogue.** It holds one line per file in `operations/`, which
on a large history is a large file to parse on every command. The next thing to
measure is whether that parse becomes the cost that opening the files used to
be, and the answer if it does is a form that can be read without parsing all of
it — which is a binary index, and 0003 permits one so long as deleting it loses
nothing.
