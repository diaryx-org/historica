# 0029 — Receiving another store

Copying a Historica directory is already a good way to seed a second working
copy, make a backup, or move history through transport Historica does not
implement. `cp -r`, `rsync`, a mounted filesystem, and a person's preferred
encrypted transport all preserve the format without putting SSH or HTTPS in
Historica.

Plain copying stops being sufficient after both copies change. Their immutable
files can be safely combined by identity, but overwriting the directory can
lose one side's bookmarks or rules. Copying arranged filenames can also create
two names for one document, while a received forgetting document must destroy
an original rather than merely sit beside it.

Historica therefore needs a content-aware local operation, not a transport or a
persistent concept of a remote.

## The decision

- **`receive` is a one-way union.** `historica receive <dir>` reads another local
  store and adds its history to the current store. The source is never written.
  Receiving in both directions is two explicit commands.
- **Documents are compared by digest, not filename.** Missing revision,
  operation, forgetting, and whole-content payload documents are written under
  their ordinary digest-derived names. An arranged source name is presentation,
  not identity.
- **The working folders are outside the operation.** Unrecorded changes,
  ignored files, and the source and receiver's checked-out trees are neither
  inspected nor changed.
- **Both stores must pass `check`.** A union must not use malformed or
  contradictory files as instructions. Notes remain notes, as they do for other
  commands.
- **Relatedness is the safe default.** Two nonempty stores must share a revision
  or expose a direct parent or supersession edge across the boundary.
  `--join-unrelated` explicitly permits seeding one store with an independent
  history. An empty store may always be seeded.
- **Immutable content is written before revisions.** Payloads come first, then
  operation and forgetting documents, then revisions. If a process stops, the
  store may contain unreachable content, but a newly visible revision does not
  name content that receive has not attempted to deliver.
- **Forgetting applies to the union.** Originals named by any forgetting
  document in either store are not copied. If the receiver already holds one,
  receive destroys it before making received revisions visible. Forgetting is
  a property of the history, not a local preference.

## Mutable files

Immutable union is deterministic. Mutable files require an explicit
conservative rule:

- A bookmark absent from the receiver is copied.
- A bookmark already pointing to the same object is unchanged.
- Two different targets for one bookmark are a conflict.
- An absent or untouched initial `skipped.txt` may take the source's rules.
- The initial source rules do not erase receiver rules.
- Two differing non-default rule files are a conflict.
- The cache is derived and is never received.
- `historica.txt` prose and local version support remain local. The document
  writers continue to raise the receiver's minimum version when required.

All mutable conflicts are discovered in a preflight plan. Any conflict blocks
the complete receive before its first write; there is no partial success that
silently chooses one side. A person can resolve the mutable files and run the
same receive again.

## Command behavior

`historica receive <dir> --dry-run` prints counts for the immutable documents,
the mutable values it would add, originals it would destroy, and every mutable
conflict. It writes nothing and exits unsuccessfully when conflicts remain.

Without `--dry-run`, the same planning rules are applied immediately before the
write. Repeating a completed receive is harmless: content already present by
identity and equal mutable values are no work.

The source argument may name a repository directory or its `history`
directory, matching the conventions of `init` and `check`.

## Why this is not `sync`

“Sync” usually implies a remembered peer, bidirectional mutation, transport,
incremental negotiation, and a policy for unrecorded working changes. None is
needed to combine two local histories, and pretending otherwise would make the
small operation harder to reason about.

For a blank mirror or backup, copying remains simpler and preserves local
presentation such as arranged names. `receive` earns its place only when the
stores have changed independently or when history rather than a byte-for-byte
store copy is wanted.

## Consequences

- `Store` exposes planning and applying a receive across two possibly different
  `Filesystem` implementations. The primitive remains usable for an in-memory
  or future mounted provider without embedding a protocol.
- Filename collisions and arrangements do not need a merge policy.
- A receive can create multiple heads. That is ordinary graph history; the
  existing merge command decides whether to join them.
- Skip rules are store metadata, not rules for what history receive copies.
  Receiving immutable history never consults them.
- There is no “local-only forgetting.” Without a persistent remote, “local”
  has no stable meaning, and allowing an original to reappear from another
  store would violate decision 0014.

## Deferred

1. Persistent peer names, last-seen state, or remote-tracking bookmarks.
2. SSH, HTTPS, authentication, discovery, and transfer negotiation.
3. Efficient set negotiation for stores too large to scan.
4. Streaming documents that do not fit in memory.
5. A mutable-conflict resolution command. Existing file and bookmark commands
   are sufficient until repeated conflicts show a coherent larger interface.

