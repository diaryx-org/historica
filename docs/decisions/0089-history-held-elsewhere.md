# 0089 — History held elsewhere

The proposal [Bytes held elsewhere](../proposals/bytes-held-elsewhere.md)
let a copy hold the history of a file of bytes without its bytes, and drew
the line at bytes on purpose: a text payload is the base every later
operation document of its file is replayed onto, so a copy without a file's
text chain could neither read nor change that file. That is true of a copy
with no way to get the text back. This decision gives it one. The argument
is the proposal
[History held elsewhere](../proposals/history-held-elsewhere.md), the
companion of [0088](0088-a-fetch-moves-the-bookmarks-its-copy-follows.md).

## The decision

**`fetch --history` takes the revisions, the bookmarks and the rules, and no
content.** No payload and no operation document arrives. The graph is whole,
so `log`, `names` and every question [0086](0086-a-copy-chooses-its-heads.md)
asks about heads are answered. A forgetting document is still taken, since it
is small and is what [0014](0014-forgetting.md) complies with.

**`fetch --name <bookmark>` takes the content of one line.** Every revision
arrives, and content only for the ancestry of what the named bookmarks
resolve to, read as the publisher states them. The ancestry is closed, as
0086's followed set is, so the copy holds whole history for the line it took.
A name the copy does not state as a change or a revision is refused.

**A command that needs content the copy lacks fetches it.** `cat`, `diff`,
`blame`, `update`, `status`, `record` and `amend` ask the store which files of
lines they read are not held whole, fetch those files' chains from the copy
this store last fetched from, hash each document against its digest, and go
on. The copy is remembered in the host's cache, beside the store's other
caches ([0078](0078-where-a-cache-is-kept.md)), so deleting the cache costs
the next such command a refusal naming `fetch <url> <path>`, and nothing
else. A command never fetches from a copy the person did not fetch from
first.

**Without a connection, such a command refuses whole, and names what it
lacks.** It names the files and the `fetch` that brings them, and never
answers from part of a chain: a replay that meets a missing document already
stops with `MissingOperations`, and the command asks before it reads.
`update` refuses the whole head, as [0030](0030-the-folder-catches-up.md)
would.

**`record` reads the folder by bytes held elsewhere's rule, extended to
text.** A file of lines whose content the store does not hold whole, and
which the folder lacks, is not surveyed: it is listed as held elsewhere and
not dropped. Naming it still records the deletion, as for bytes. Where the
folder holds the file, `record` needs the base to diff it, so it fetches the
chain first, and refuses offline. An amendment of a revision that itself
changed such a file is refused, since it cannot restate the change.

**`fetch <url> <path>...` takes a file of lines' content too.** Its chain
at the heads, and nothing else.

**The default does not change.** A plain `fetch` takes everything, and a
plain `fetch` after a `--history` takes everything left, from the addresses
the pages gave.

## What a file's content is

A file of lines at a revision is the payload a `text` line names for it and
every document an `edit` line names for it, across the whole ancestry of the
revision. That is the chain a replay reads, and, at a merge, every side's. It
can be more than the chain of one line, never less. `Store::text_elsewhere`
answers which files at some revisions lack part of theirs, from the store as
it stands. Nothing is remembered to make it so, as nothing is for bytes held
elsewhere: fetching the content ends the state.

A digest the catalogue places is held, and reading it is where a damaged file
is found. A miss proves nothing ([0079](0079-a-reader-looks-where-forget-files.md)),
so a miss asks whether anything here stands in for it before calling it
lacked. A digest something here forgets is not lacked.

## The library

- `Fetching` gains `leave_content` (`leaving_content`) and `names`
  (`naming`). It is no longer `Copy`; it was not released as it was.
- `Store::fetch_content(source, manifest, digests)` takes payloads and
  content documents by digest, from where a fetch that left them remembered
  them, or from the whole listing. A digest the copy forgot is taken as the
  document that stands in for it. `Store::fetch_payloads` is now this.
- `Store::text_elsewhere(revisions, paths)` and `TextElsewhere` name what is
  lacked.
- `FetchError::NoSuchName` is a `--name` the copy does not state.
- The memory a fetch keeps of what it left records a document as
  `left-document <digest> <path>`, beside a payload's `left`.

## Costs

- **A chain is many small documents.** Reading an old file of a long history
  fetches each in turn, since the CLI's HTTP source does not prefetch; that
  is the task *The web source asks for one file at a time*.
- **Reading commands can make requests.** `cat` and `blame` may now reach the
  network. The refusal offline is what keeps that visible.
- **`check --complete` fails on such a copy**, correctly. It is not whole.
- **The survey's question is asked of every file the folder lacks.** It walks
  the ancestry once for all of them, and only when the folder lacks a file
  of lines the head holds.
- **A file fetched into the store is surveyed again.** As with bytes fetched
  by path, a file whose content `cat` fetched reads as deleted to a `record`
  from a folder that never caught up with `update`. The folder as it stands
  and the store as it stands are all [0015](0015-status.md) allows, and that is their answer.

## Deferred

**`evict` for text.** Letting go of a text chain this copy holds is the
symmetric act, and the one most likely to leave a copy that cannot read its
own folder offline. Nothing needs it yet. `evict` stays bytes-only.

**`merge`, `carry`, `squash` and `export`** do not fetch. They read content
across whole histories, and a copy that took only the history refuses them
with the store's own `MissingOperations` or `MissingPayload`, which a plain
`fetch` answers.

## Rejected alternatives

The proposal's: **a shallow copy from a date or a depth**, which needs a new
kind of document stating every file's content at the cut; **a sparse copy by
path**, a refinement of `--name` rather than a different mechanism, deferred
until somebody needs it; and **a URL in the revision**, rejected for payloads
by bytes held elsewhere for reasons that hold for text.

## Consequences

- `status`, `record` and `update` say *this store does not hold its content*
  of a file held elsewhere, whichever kind it is.
- A command that read only the store now may make requests to the copy it
  came from, and only that copy.
