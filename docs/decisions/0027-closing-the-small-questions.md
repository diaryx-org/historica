# 0027 — The small questions close together

The decisions accumulated questions for good reasons: some waited for a later
feature, some asked whether an initial choice should stand after use, and some
were interface judgements that did not belong in the format decision that
first exposed them.

Enough of them now have evidence, and leaving them labelled open makes the
documents less truthful than choosing. This decision closes the ones that need
no new format and groups the shared rules so one answer applies everywhere.

## Canonical history records facts, not diagnostics

- **There is no `normalize` command for a recorded revision.** Canonical bytes
  are identity. A formatter may produce candidate bytes before recording, but
  replacing bytes already identified is a new revision.
- **Contested regions are not recorded.** They are derived diagnostics whose
  boundaries may improve with an implementation. History records the resolution
  a person chose.
- **A wholesale replacement is still a valid diff.** The library returns it.
  A front end may ask whether it was intended without changing the diff or
  format.
- **Attachment previews and dimensions are presentation.** Core status reports
  that bytes changed. A host that understands an image may say more without
  putting that understanding in the store.
- **Rename lookup remains a graph walk until it is measurably expensive.** A
  disposable path index belongs in `cache/`; canonical history gains no second
  account of a file's paths.

## Explicit intent wins where inference cannot

- **A terminator disagreement is a contested edit.** The final newline is a
  property of the last item. Concurrent branches asserting incompatible
  terminators contest that item, and neither wins by ordering.
- **A concurrent edit beats `drop`.** Ordinary deletion does not silently lose
  work. A redaction has the stronger spelling 0014 gives it: `forget`.
- **Recording a contested byte payload requires explicit acceptance.** The tool
  cannot infer that a photograph was examined, and it does not put a marker
  beside a person's file. The record interface owes an acceptance option for
  that path.
- **Changing a text file into bytes is explicit replacement.** Recording
  continues to refuse it by default. An explicit replacement option may perform
  the required `drop` and fresh `add`, so the convenience never pretends one
  file identity changed kind.
- **NUL remains a recorder signal.** The format requires a text payload to be
  UTF-8 and permits NUL; the recorder uses NUL as evidence that bytes are the
  more useful initial kind.

## A valid store and a representable folder are different questions

Two stored paths that differ only by case or Unicode normalisation remain
distinct and valid, so `check` may note them and does not call the store broken.
A command asked to materialise both on a folding filesystem must refuse,
because that particular folder cannot represent the tree.

`arrange` remains best effort and returns every path it could not file. A
revision directory remains the readable account of what that revision changed,
not a snapshot padded with untouched files. `record` creates the name it chose
and never renames a colliding sibling; tidying names belongs only to `arrange`.
Running `arrange` is itself the request to apply its scheme, so there is no
second mutable file recording that the store was filed by hand.

## Defaults need somebody who knows the folder

`skipped.txt` has **no rules by default**. It explains its syntax so a person or
host can add rules, but the library does not silently omit platform metadata,
build output, dependencies, or anything else. Those defaults belong to a
project template, application, or user preference that knows what the files
mean.

Likewise, `check` does not guess which sync tool produced a filename. Duplicate
content is already a note grounded in bytes; calling a suffix a conflicted copy
adds an attribution the store cannot verify.

Sharding also waits for knowledge. The store remains flat until measured
directory enumeration or sync cost makes it otherwise. A future shard prefix
is still advisory presentation and changes no identity.

## The store's prose belongs to its reader

The prose below the first line of `historica.txt` is not checked. A person may
edit it; only the version line is machine state.

`cache/` does carry `README.txt`, because the permission to delete derived data
belongs at the point where a person is about to act on it. The note is itself
derived and disposable.

A missing payload remains a note. Absence cannot say whether transport has not
delivered the bytes or another writer overwrote them, so `check` names both
possibilities rather than promoting an indistinguishable state to corruption.

## File bookmarks keep naming one identity

A bookmark does not cross a `drop` and fresh `add`: the new file has a new
identifier, and silently following would erase that distinction. At a revision
before the file existed, the bookmark resolves to its identifier and then
refuses because that tree does not hold it. Silence would conflate an absent
file with an invalid name.

## Consequences

- Decisions 0003, 0004, 0006, 0007, 0008, 0009, 0017, 0018, 0019, 0021, 0022,
  and 0024 move the questions above to resolved.
- `init` writes a comment-only `skipped.txt` and `cache/README.txt`.
- `check` removes sync-suffix recognition and describes a missing payload
  without assuming why it is absent.
- The explicit attachment-acceptance and text-to-bytes replacement options are
  interface work owed by `record`; their semantics are settled here before
  their spelling is chosen.
- Re-rooting, authors bound to signatures, streaming reads, local forgetting,
  and atomic compare-and-swap remain open because each needs the larger feature
  that would supply evidence for it.
