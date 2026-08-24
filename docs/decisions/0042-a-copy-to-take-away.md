# 0042 — A copy to take away

0029 built the receiving half and said what the sending half is not: not SSH,
not HTTPS, not a remembered peer, not a protocol. A Historica store moves
over `cp -r`, rsync, a mounted disk, a sync service, or an attachment,
because it is a folder of files, and `receive` combines what arrives with
what is held.

What is missing is the thing every other tool spells in one line. `git clone
<url>` hands a stranger a working copy and its whole history; Historica hands
them a decision. Copying the repository folder ships too much — the working
copy as it happens to stand, unrecorded edits included, and every file a
`skip` rule exists to keep private — and copying `history/` alone ships a
store with no folder, plus `names/` and `skipped.txt`, which are personal,
and `cache/`, which is nobody's. There is no directory on disk whose bytes
are "the thing a stranger should have," so no pipe, however good, can carry
it.

So the sending half is not a manifest, a protocol, or a server. It is a
command that *builds that directory* — and then any pipe carries it, because
compressing a folder and moving it is the problem every pipe already solves.

## The decision

- **`historica export <dir> [<target>]` writes a fresh repository at
  `<dir>`: the folder as the target revision has it, and the history that
  leads there.** The result is a complete, ordinary store — `log`, `check`,
  `record`, and `receive` all work in it — that has never heard of the
  store it came from.
- **The folder half is `update`'s work.** Recorded files at their recorded
  paths, modes set, links materialised (0040), nothing else — no unrecorded
  edits, no skipped files, by construction rather than by filtering. The
  `wget -r` failure — a mirror that ships what a privacy rule names — cannot
  happen to an assembled copy.
- **The history half is the target's own: its ancestry, closed.** Every
  parent, every operation document and payload those revisions name, and
  every forgetting document that touches any of it — 0014 travels, always.
  Not `names/`, not `skipped.txt`, not `cache/`: bookmarks and rules are the
  exporter's, and a cache is nobody's. `historica.txt` and `format.txt` are
  written fresh, because 0021 promises the copy explains itself to whoever
  opens it. The files get the readable names 0041 files, because the copy is
  for a person.
- **The default target is the head**, and divergence refuses with the heads
  described, exactly as `update` and `cat` refuse — an export of "the
  history" when there are two is a choice someone has to make out loud.
- **A past revision is a legitimate target, and this is where 0030's refusal
  is honoured rather than overridden.** Checkout-to-the-past was refused
  in place because the folder would hold one revision while the store's
  heads said another, and the stored position reconciling them is the
  mutable state this design refuses to keep. An export has no such gap:
  its history *ends* at the target, so the target is its head, the folder
  and the store agree, and no position is written anywhere. The past is not
  visited; a copy of the world as it stood is taken away. In-place
  checkout-to-the-past stays refused.
- **An export is a replica, so `receive` is its pull.** It shares every
  revision with its origin, which is 0029's relatedness on the first try:
  receive the origin later and the copy catches up, divergence and all,
  by the rules that already exist. Clone and pull were one design all
  along; this is the half that was missing.
- **Compression is the pipe's job.** tar and zip exist, and an archive
  format of the house's own would be the beginning of duplicating them.
  The one-line clone is therefore two ordinary tools and no new ideas:

  ```console
  $ historica export journal && tar czf journal.tar.gz journal
  ```

  once, wherever the store lives, and

  ```console
  $ curl -sL https://example.org/journal.tar.gz | tar xz
  ```

  for anyone, anywhere, yielding a folder that is a working copy and a
  complete store. A static file server is a Historica host.

## The supersession question

Ancestry closes over parents. What it does not close over is supersession
from outside: a revision in the target's ancestry may have been rewritten by
a revision that is not — an amendment recorded after the moment being
exported. The export does not chase it. A copy taken at a moment is a
replica that has not yet received what came later; holding a head the origin
has since rewritten is the ordinary condition of every replica between
syncs, and `receive` is the existing answer. What the implementation must
settle, against `check`'s existing rules rather than new ones, is the edge
itself: whether a `supersedes` line may name a digest the store does not
hold, or the closure must include the superseded revision it names — the
superseded side lies *behind* the target in time, so including it drags in
no future, and 0023 keeps it as the whole of the undo anyway.

## Rejected alternatives

**A manifest first.** The earlier draft of this decision: a JSON enumeration
of the transferable files, so a consumer could compute set differences and
fetch what it lacked. Structurally deficient as the *first* sending
primitive — it offers an incremental protocol to a consumer who cannot yet
get the thing once, and the one-line clone it enables is a loop. The
enumeration is real and comes back as the incremental half, below, when
there is a fetching side to want it.

**Serving the store's own directory.** The store a person works in holds
their folder, their rules, their bookmarks. The transferable thing and the
lived-in thing are different things, and every mirror-shaped answer ships
the difference.

**An archive format.** One tar invocation, saved, in exchange for a format
of our own to document, version, and be wrong about. The readable folder is
the interchange format; it is the whole premise.

**A bare export — history with no folder.** A store without a working copy
is a thing 0011 never made, and the first command anyone would run against
one is the `update` the export could have run for them. If a host wants
folderless storage it already has it: `history/` is self-contained, and
`export` is precisely how a folder is conjured from it.

## Consequences

- `Store` gains the closure walk — a target's ancestry with its named
  documents, payloads, and forgetting documents — and an export that writes
  it through a second `Filesystem`, the shape `receive` already crosses two
  filesystems with. The library does it all; the binary renders it, per
  0006.
- `export` refuses a store `check` calls broken, as `prune` does: a copy of
  a fault is two faults.
- `export` into an existing non-empty directory refuses; seeding is
  `receive`'s job and the distinction is worth keeping sharp.
- The exported store's version marker is the lowest that expresses what it
  holds — an export of an all-v0 ancestry from a v4 store is a v0 store,
  0004 working in the other direction.

## Deferred

1. **The enumeration, for incremental transfer.** The digest set of the
   transferable files, computable on both ends; the difference is the
   shipment, which is the whole of want/have with no session. It returns
   as `offer` (likely JSON — its reader is a program) when something on
   the fetching side exists to consume it.
2. **Bookmarks in an export**, behind the union rule 0029 already wants
   and does not have.
3. **A fetch convention** — an HTTP shape a static server satisfies beyond
   one archive. Saying it out loud is a compatibility promise this
   decision does not make.
4. **Narrowing an export by path** — a subtree's files and only the
   history that touches them — which is `forget`-shaped work and deserves
   its own argument if it is ever wanted.
