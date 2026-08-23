# 0028 — Accepting bytes is a statement about a path

0027 closes the semantic question around a contested attachment: recording must
not mistake whatever bytes happen to be in the folder for a resolution a person
examined. Text has marker lines the recorder can find. Bytes need an explicit
statement.

The same review also deferred the larger features still named in the decisions,
and exposed one reason they have all remained difficult to choose: each assumes
a boundary Historica does not yet have.

## There is no remote

Historica has replicas in its model, but no **remote** in its interface. Two
stores meet because a person or another program copies files between them.
Historica does not name the other store, remember what it has seen, push to it,
pull from it, or know whether it is another laptop or another person.

That distinction is why local-only forgetting is premature. “Destroy it here
without propagating” needs a named there and an operation that propagates.
Today it would mean only deleting bytes from this store and allowing external
copying to restore them, which is pruning under a more misleading name.

The other large features have the same missing evidence in different forms:

- re-rooting needs a shallow transport operation and a boundary across which a
  truncated history is sent;
- streaming needs a real non-disk provider whose latency, cancellation, and
  consistency rules constrain the trait;
- compare-and-swap needs a provider or concurrent writer with a generation it
  can compare and an observed lost update;
- structured authorship needs signatures, a key authority, and a trust boundary
  that say what an identity must bind.

None is rejected. Each remains deferred until the adjacent system exists,
because building the feature first would invent that system by guesswork.

## The decision

- **`record` accepts `--accept <path>`, repeatably.**
- **Acceptance is required only for contested byte payloads.** The selected
  merge parents must state different whole content for the file at that path.
- **Every contested byte path must be accepted.** The error lists the exact
  options still needed.
- **Every acceptance must be necessary.** A typo, stale option, text path, or
  uncontested attachment is refused rather than silently ignored.
- **Acceptance takes the bytes already in the working folder.** It does not
  choose a parent. A person may inspect either side with `cat`, write the chosen
  or combined bytes to the path, and then accept that path.
- **Text resolution is unchanged.** `--accept` cannot waive marker lines or any
  other recording refusal.
- **`status --merge` names each path requiring acceptance** and prints its
  option, as it already does for contested paths requiring `--at`.

## Why a path

The fact being accepted is “the working file at this path is the resolution.”
A digest would accept one parent rather than a newly edited result. A file
identifier is stable but not what a person sees in the folder. A blanket
`--accept-all` would make the oversight this decision prevents one easy option
again.

The path is checked against the merged tree, so it is not a loose string. If
renames or `--at` change where the file sits, acceptance names the resulting
working path—the same value the person inspected.

## Consequences

- `Survey` reports contested byte paths independently of text markers and tree
  contests.
- `Recording` carries the set explicitly accepted.
- Planning refuses missing and unnecessary acceptances before minting or
  writing anything.
- The CLI and end-to-end tests cover reporting, refusal, stale acceptance, and
  successful recording of the folder's bytes.
- Decisions 0005, 0007, 0014, 0025, and 0026 record why their larger features
  remain deferred rather than merely leaving them open.

A future transport, provider, or signing decision should reopen its own feature
with evidence from the boundary that now exists.
