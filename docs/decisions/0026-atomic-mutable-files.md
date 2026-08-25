# 0026 — A mutable file changes all at once

The store's documents and payloads are immutable. `create_new` gives them the
one concurrency property they need: another writer can win the name, but no
reader can meet half a digest-named file.

The files that remain mutable did not have the matching property. `write` was
specified as replacement and `Disk` implemented it as `std::fs::write`, which
opens an existing file by truncating it and then writes the new bytes. A reader
in between can see an empty bookmark, half a rule, or a marker with only part of
its version.

0003 calls mutable names the store's entire conflict surface. Since then the
marker and `skipped.txt` have joined them. Their conflicts are real and cannot
be hidden, but a half-written value is not a conflict between two people. It is
an implementation leaking the interval in which it writes.

## The decision

- **`Filesystem::write` is atomic replacement.** Until it commits, a reader
  sees the complete old value. Afterwards a reader sees the complete new value.
  It never sees a missing destination or a prefix of either.
- **The contract is one file, not a transaction.** A command that changes two
  mutable files may expose either complete change first. Historica has no such
  command today, and this decision does not invent a journal to promise one.
- **Concurrent writers are still last-commit-wins.** Atomic replacement keeps
  each candidate whole; it does not merge two edits to `skipped.txt` or decide
  which bookmark target was intended. A syncing provider may still preserve
  both as conflicted copies, as 0003 requires.
- **Immutable files still use `create_new`.** Atomic replacement must not turn
  an append-only document write into an overwrite, and no writer renames a
  digest-named document after creating it.
- **`Disk` writes beside the destination and commits over it.** The temporary
  file is on the same filesystem, so committing cannot cross devices.
  Platform-specific replacement is delegated to `fs-transaction` (originally
  `atomic-write-file`), which supplies the equivalent operation on Unix,
  Windows, and WASI without adding platform-specific unsafe code to Historica —
  and, since the change of delegate, also flushes what the replacement
  publishes, so a committed value survives a power cut.

## Why this strengthens `write` instead of adding a method

Every call to `write` is already a mutable store write, and every mutable store
write needs this property. Keeping a weaker `write` beside `atomic_write` would
give implementations and future callers a choice the format does not have.

This also keeps `Filesystem` at nine methods. An in-memory implementation can
satisfy the rule with one map insertion under its existing lock; a document
provider can use its native replace operation; `Disk` needs the temporary file
because an operating-system file handle otherwise exposes truncation.

`rename` is not reused. Its contract belongs to `arrange`: the caller has
already checked that the destination is free, and the purpose is presentation.
Atomic mutable writing must replace an occupied destination, including on
Windows where an ordinary rename does not promise that.

## What atomic means here

The promise is about **visibility of one complete value**, including when a
write fails or the process stops before commit. It is not:

- mutual exclusion between writers;
- a compare-and-swap against the value the caller read;
- atomicity across several files;
- recovery of a temporary sibling left by a machine that stopped without
  running destructors.

The first two would require revision or generation metadata on mutable files.
The third would require a transaction log. The fourth is tidy-up: an
uncommitted sibling claims no store name and `check` can treat it like any
other foreign file. None is a reason to expose a half-written destination.

## Ordering the version marker

0017 requires the marker never to understate the document versions a store
holds. Writers already raise it before creating the first document of a newer
version. Atomic replacement makes that first step either wholly old or wholly
new; it does not change the ordering. A stop between the two leaves a store
whose marker is conservatively high, so an older reader refuses rather than
partially reading a history it does not understand.

## Consequences

- The trait documentation makes atomic replacement an implementation
  requirement, beside atomic `create_new` and no-follow directory walking.
- The `disk` feature gains `fs-transaction` (originally `atomic-write-file`);
  builds without `disk` do not gain the dependency.
- Initial creation of `historica.txt` and `skipped.txt` uses the same operation.
  There is no old value then, but failure still cannot leave a file that looks
  complete enough for discovery and is not.
- Bookmark updates, version raises, and additions to `skipped.txt` expose only
  complete parseable files.
- Decision 0025's third open question is closed.

## Deferred

1. **Whether mutable writes eventually need comparison as well as atomicity.**
   `append_skipped` reads, extends, and replaces; two simultaneous calls can
   each commit a complete file while one loses the other's new rules. Solving
   that requires a generation a provider can compare, or making the rule file
   append-only in the format. No observed use needs that machinery yet.

   Decision [0028](0028-accepting-by-path.md) keeps this deferred until a real
   provider or concurrent writer supplies a comparison primitive and an
   observed lost update.

   A comparison primitive now exists: fs-transaction 0.2.1's change-set
   expectations check what a path holds inside the same apply that writes it.
   `Filesystem::write_if` offers it through the trait — `update`'s per-file
   guard, decision [0025](0025-the-folder-is-asked-for.md)'s look-again rule,
   is its first user, with `Disk` staging the look as an expectation and every
   other implementation free to take the read-compare-write default. What
   stays deferred is exactly `append_skipped`'s half: no observed lost update
   yet, so the rule file keeps its unguarded read-extend-replace.

## Open questions

2. **Whether abandoned temporary siblings should receive a specific `check`
   note.** They are currently foreign files like any other. A stable spelling
   would let `check` identify them, but would couple the format's diagnostics to
   one filesystem implementation's private name.
