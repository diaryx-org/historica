---
title: Bytes held elsewhere
description: A copy that holds the history of a file of bytes without its bytes — fetched without them, fetched one at a time later, and let go of again — decided from what the store holds rather than from a list of what it lacks
status: implemented
created: 2026-09-28
updated: 2026-09-28
part_of: '[Proposals](/docs/proposals/proposals.md)'
---

# Bytes held elsewhere

## Status

Implemented, unreleased, in f3374cc (`record`, `status`, `diff`, `update` and
`export`) and 97aa4ac (`fetch --no-bytes`, `fetch <url> <path>...` and
`evict`). No decision was written for it; this document is the record. The
body below is left as it was argued, and the build differs from it here:

- **`Store::fetch` did not change.** Its callers keep compiling, and the new
  way of asking is `Store::fetch_with` taking a `Fetching`, with
  `leaving_bytes` for `--no-bytes`. Taking a payload by digest is
  `Store::fetch_payloads`, and the folder's half of evicting is
  `update::plan_eviction`.
- **`evict` does not refuse a folder file holding other bytes.** It leaves it:
  that file is an edit `record` has not seen, and letting go of the store's
  copy changes nothing about it.
- **`export` refuses a missing file only at the target.** Payloads missing
  from older revisions travel as they always did, as an absence the copy's
  `check` notes.
- **0044's witness record is still not built**, so `evict` has nothing to
  clear yet.
- **Open questions 1 and 2 are as proposed:** `evict` believes the listing,
  and `record` does not take matching bytes from the folder.
- **`fetch <url> <path>...` does not `check` the store** before or after,
  unlike a whole fetch. A payload arriving under its own digest cannot make a
  store that was right wrong, and checking hashes every payload the store
  holds.

A store of photographs, recordings or scans is mostly payloads. A laptop that
wants the history of that store has to download all of them, and a phone
cannot keep them. What either copy needs for most of its work is the history:
which files exist, what each one is, who changed it and when. The bytes of an
old video are needed only when somebody opens that video.

The format already separates the two. A revision says
`bytes <file> <digest>` ([0017](/docs/decisions/0017-content-that-arrives-whole.md)),
and since [0067](/docs/decisions/0067-content-that-arrives-whole-is-named-not-carried.md)
nothing carries a file of bytes except the payload named by that digest. So
the reference a lighter copy would keep already exists. It is the digest,
and it is in every revision. A store that holds a revision naming bytes it
does not hold is already legal: `check` reports `MissingPayload` as a note.
[0044](/docs/decisions/0044-what-this-copy-has-held.md) decided that the
absence should be an error where this copy once held the bytes, and that has
not been built. Nothing here depends on it, and `evict` below says what it
would owe when it is.

What is missing is the rest of the tool:

- **`fetch` cannot leave a payload behind.** [0048](/docs/decisions/0048-asking-for-what-is-missing.md)
  takes everything the listing names that the store lacks.
- **`update` refuses the whole folder** if the store lacks one payload the
  target names. It tells the person to "receive the rest first".
- **Nothing fetches one payload later**, when somebody opens the file.
- **Nothing lets go of a payload** this copy holds and another copy also
  has. The only way to remove one is `forget`
  ([0066](/docs/decisions/0066-forgetting-a-payload.md)), which destroys it
  for every copy.

The first three are small. The hard question is what `record` makes of the
folder afterwards. If a path the head names has no file in the folder, today
that is a deletion ([0011](/docs/decisions/0011-working-copy.md)). The obvious
fix is to keep a list of the paths that are absent on purpose. 0011 refused
that list as a third source of truth, and
[0015](/docs/decisions/0015-status.md) said why: the working copy is the
folder as it stands and the store as it stands, and there is no third thing
that can disagree with either.

This proposal needs no list. The store already says which bytes it holds.

## The proposal

- **A path whose bytes the store does not hold is not surveyed while it is
  absent.** It is a file of bytes at a path the parent tree names, the
  payload for that path is not in the store, and the store has not forgotten
  it. When the folder has no file there, `record` does not compare that path
  and `status` lists it under its own heading, *held elsewhere*. Nothing is
  remembered to make this so. The rule reads the folder as it stands and the
  store as it stands, which is all 0015 allows. If the store gains the bytes,
  the path is surveyed again, and so is the file as soon as the folder has
  one there.

- **Naming the path still records the deletion.** Under
  [0039](/docs/decisions/0039-recording-some-of-the-folder.md), a path the
  tree holds and the folder does not is a deletion when it is named. So
  `record photos/a.jpg` drops the file whether or not the store holds its
  bytes. The rule above only stops a survey that was not asked about the path
  from concluding something about it.

- **A file at that path is surveyed as usual.** Where the folder holds
  bytes, `record` hashes them and compares the digest with the tree. A file
  of bytes is replaced whole and needs no base, so the store does not have to
  hold the old bytes to record new ones.

- **`update` leaves the path empty instead of refusing.** Where the target
  names bytes the store does not hold, the plan leaves the path empty.
  An earlier version of the file in the folder is removed if its bytes are
  recorded, so that the next `record` does not read it as a revert. Bytes
  nobody recorded at a path the target holds still refuse the whole update,
  as they always have. [0030](/docs/decisions/0030-the-folder-catches-up.md)
  made an update all or nothing because a folder half holding a head lies to
  the next `record`. A gap `record` does not read is not a lie, so the rule
  keeps its reason and loses this one case.

- **`update` removes only bytes this store holds.** 0030 promises that an
  update never destroys the only copy of anything. Today it keeps that
  promise by asking whether some revision *records* the bytes at that path.
  In a store that holds every payload it names, that is the same as holding
  them. In a store that does not, it can delete the only copy on this
  machine. The check becomes whether the store holds them.

- **`fetch --no-bytes` leaves every file of bytes behind, and fetches
  everything else.** The line is the one 0017 already draws, and nothing
  else: no size, no caller's predicate. It is the line because it is the only
  one that costs history nothing. Nothing historica does with a file of bytes
  reads it. It is recorded whole, merged by choosing a digest, and diffed as
  *changed*. A text payload is the base every later operation document of
  its file is replayed onto (0017), so without it `record` cannot diff an
  edit, `merge` cannot replay one, and `cat`, `diff` and `blame` fail at
  every revision. A text file left behind would be a file this copy can
  neither read nor change.

  To know which payloads are files of bytes, the fetch reads the revision
  documents that name them. It asks for those first, since they are among the
  small files [0080](/docs/decisions/0080-a-listing-in-pages.md) prefetches,
  and still writes them into the store last. 0048's ordering exists so that
  an interruption leaves no revision naming bytes that never arrived. It
  governs what reaches the disk first, not what is requested first, and it
  still holds for every payload the fetch keeps.

- **`fetch` takes paths as well, for fetching one file later.**
  `historica fetch <url> photos/a.jpg` resolves the path against the heads,
  asks for the payloads it names, and takes nothing else. The folder is
  untouched, as it always is after a fetch. The next `update` finds the
  bytes held and writes the file. The library takes digests, so a caller
  that already knows the file's SHA-256 does not need a path. prov's
  `content_hash` on an attachment is such a digest.

  Finding the payload's address in the listing is 0080's memory, one step
  further. When a fetch leaves payloads behind, it records their addresses in
  the host's cache beside the pages it applied
  ([0078](/docs/decisions/0078-where-a-cache-is-kept.md)). A fetch for one of
  them reads the address from there, or composes the whole listing if the
  cache is gone. Deleting the cache changes how long this takes and nothing
  else. A later fetch without `--no-bytes` takes the payloads left behind as
  well, from the same addresses. 0080's memory lets a fetch skip the pages
  it has applied, and the payloads left behind are listed in those pages, so
  without the addresses a plain fetch would never ask for them. A fetch
  records its pages as applied once it has taken everything it did not leave
  on purpose.

- **`historica evict <url> <path>...` lets go of a payload this copy
  holds.** It removes the payload from `operations/` and removes the folder's
  file where the folder holds exactly those bytes. When 0044's witness
  record is built, `evict` clears the digest from it, so that `check` reads
  the absence as held elsewhere rather than as lost. It refuses unless the source's listing names the
  digest, and it refuses where the folder holds bytes nobody recorded at that
  path. It writes nothing that travels. Another copy never learns that this
  one let go, which is the difference from `forget`: forgetting destroys the
  bytes for every copy, and evicting only removes them from this one.

- **`export` refuses a target whose folder needs bytes the store does not
  hold**, and names the paths, with `fetch` as the fix. An export builds the
  folder ([0042](/docs/decisions/0042-a-copy-to-take-away.md)), and a folder
  missing a file is not the target. The copy a stranger fetches from
  ([0052](/docs/decisions/0052-the-copy-a-stranger-fetches-from.md)) stays
  whole, so nobody fetching from it has to be told the bytes are somewhere
  further away.

## Why this is not an index

0039 answered this for `record <path>`, and three conditions settle it here
too.

**Nothing is remembered between commands.** The rule reads whether the
store holds a payload, and the store holding a payload is the store as it
stands, not a record about it. Fetching the bytes ends the state. Evicting
them starts it. Neither writes a list, and no file can disagree with the
store about which paths are held elsewhere, because no such file exists.

**Nothing hides.** 0011 refused a tracked-file list because it fails
silently. A file ends up in the folder and out of the history, and nothing
on screen says which. Here `status` names every path held elsewhere, every
time it runs.

**Every fact recorded is one the folder stated.** A path that is not
surveyed produces no fact at all. That is a smaller claim than a deletion,
and not a false one.

One case gets worse, and it should be named. A person who copies a file in
from outside historica, at a path whose bytes the store never held, and then
deletes it, does not have that deletion recorded by a bare `record`. `status`
still lists the path as held elsewhere, which is true, and `record <path>`
records the deletion. The file got there without historica, so historica
could not have put it there.

## Rejected alternatives

**A URL in the revision.** A place to fetch the bytes from, stored beside
the digest. A URL is where one publisher keeps the bytes today, and to the
format it is presentation, the way a filename is
([0003](/docs/decisions/0003-store.md)). It goes stale without any change to
the history, it cannot be verified by hashing, and it would be the first
thing in a revision that a copy with the same history could disagree with.
The listing already says where a digest can be fetched, and it is refetched
rather than kept.

**A pointer file in the folder**, as Git LFS does it. A small text file at
the image's path naming the digest, which `record` recognises and leaves
alone. Every other program that opens the folder reads it as a broken image.
The folder stops being the folder a person reads, and the file lies about
what it is to everything except historica. [0066](/docs/decisions/0066-forgetting-a-payload.md)
refused to invent a placeholder for a forgotten payload, and that reason is
stronger for one that is only somewhere else.

**A symbolic link into the store**, as git-annex does it. A dangling link
until the bytes arrive, and an ordinary link afterwards. `record` already
records a link as a file of its own kind
([0040](/docs/decisions/0040-a-file-can-be-a-link.md)), so it would need to
tell an annex link from a person's link. And a host with no links has no way
to say anything at all.

**A list of the paths absent on purpose**, kept in `history/` as a local-only
file. That is the index 0011 refused, and it fails in the worst way
available. It is state only this device holds, and if it is lost, the next
`record` drops every file on it. It would also be the first file in the
store that a person has to back up in order not to lose history.

**Leaving large text files behind too**, over a megabyte say. The file
could not be edited on this copy at all, for the reasons above. The listing
states no lengths, so a size would also need a new page grammar. Choosing by
size is choosing by a caller's policy, and a caller's predicate over which
payloads to keep was the draft before this one. It was dropped for the rule
above, which needs nothing from the caller and nothing from the listing.

## What this changes

- 0048's sentence *"the fetched set is closed"* becomes: closed over
  revisions and documents, and over every payload the fetch did not leave on
  purpose. The store is still a complete store when the fetch finishes, in
  the sense `check` means: every absence is a note, and none is an error.
- 0030's all-or-nothing rule gains its one exception, with the reason above.
  Its promise not to destroy the only copy becomes a check on what the store
  holds.
- `status` gains a heading, and the library's survey a set of paths held
  elsewhere. `status` has no reading for a program yet, so there is no line
  kind to add.
- `forget` still refuses bytes this store does not hold, since the stand-in's
  `length` is measured from them (0066). That now includes bytes it evicted.
  The fix is to fetch them first, or to wait for somebody else's forgetting
  document.
- A conflict over a file of bytes ([0012](/docs/decisions/0012-conflicts.md))
  can be resolved by choosing a digest, which needs no bytes. It can be
  viewed only where the store holds both sides, and the refusal says which
  side to fetch.

## Open questions

1. **What `evict` believes.** A listing is the publisher's word that the
   bytes are there, not proof
   ([0049](/docs/decisions/0049-what-a-lookup-does-not-prove.md)). The only
   proof is to download and hash the whole file, which is what evicting
   exists to avoid. The proposal accepts the listing's word, and says so
   when it refuses. The other choice is to refuse any payload no second copy
   is known to hold, which needs a way to know about a second copy that this
   format does not have.
2. **Whether `record` takes the bytes from the folder when they match.**
   Where the folder holds a file whose digest is exactly the unheld payload,
   `record` could file it and end the held-elsewhere state at no cost.
   Nothing needs this yet, and it makes `record` write in the store when
   nothing in the folder changed.

## Not this

**Recording a folder without copying its bytes into the store.** 0067
deferred the other half of this, where a folder of video already on the
disk is recorded without a second copy. That is also a store naming bytes it
does not hold, but the bytes are *here*, beside it, rather than somewhere
else. It is a question about what `check` may believe about a file outside
the store, and nothing above depends on it.

**Resuming a payload that was interrupted.** 0067 deferred this too. It
matters most for exactly these files, and it is independent: leaving a file
behind and fetching half of one are different problems.

**A large text file recorded as bytes.** 0017 fixes a file's kind when it
is added, and `record` makes a file text when it is valid UTF-8 with no NUL
byte. A text file big enough to be treated like an attachment would have to
be recorded as bytes when it is added, and then everything above applies to
it unchanged. That is a writing-side question with its own cost: every edit
to a file of bytes stores the whole file again, so a 50 MB log that gains a
line a day grows the store by 50 MB a day rather than by a line.

**When to fetch, and when to evict.** What is fetched when a document opens,
and when a copy lets go of what it holds, are policy. They belong to whoever
calls `fetch <path>` and `evict`.
