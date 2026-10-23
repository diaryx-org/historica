---
title: History held elsewhere
part_of: '[Proposals](/docs/proposals/proposals.md)'
status: implemented
created: 2026-10-21
updated: 2026-10-22
description: 'A copy that holds every revision and only the content it reads: a fetch that takes the history without the files, or the content of one line, and commands that fetch the rest from the copy it came from when they need it — extending bytes held elsewhere to text, which that proposal could not do without a source to fetch from'
---

# History held elsewhere

## Status

Implemented 2026-10-22, unreleased, as decision
[0089](/docs/decisions/0089-history-held-elsewhere.md), which is the
authority from now on. Argued 2026-10-21, as the companion to
[A fetch moves the bookmarks its copy follows](/docs/proposals/a-fetch-moves-the-bookmarks-its-copy-follows.md),
which was built first (decision 0088). Nothing here depends on it: `--name`
reads the publisher's bookmark from the listing, not the copy's own.

The open questions were settled by Adam on 2026-10-22:

1. **`evict` does not extend to text, for now.** Deferred: nothing needs it
   yet, and it is the act most likely to leave a copy that cannot read its own
   folder offline. `evict` stays bytes-only.
2. **`update` does not leave a text file absent.** It fetches the content the
   head needs, and offline it refuses whole, as proposed.

The build differs from the body below here:

- **`status` and `amend` fetch too**, beside `cat`, `diff`, `blame`, `update`
  and `record`: each reads a file of lines' content to compare it.
- **A file of lines is its content across the whole ancestry.** What a
  command fetches is every `text` and `edit` digest the revision's ancestry
  names for the file, which at a merge is more than one line's chain.
- **`merge`, `carry`, `squash` and `export` do not fetch.** They refuse with
  the store's own `MissingOperations` or `MissingPayload`, which a plain
  `fetch` answers.
- **A forgetting document is always taken**, by `--history` and `--name`
  alike, since it is small and is what decision 0014 complies with.
- **`fetch <url> <path>...` takes a file of lines' content** as well as a
  file of bytes'.

## What is here already

[Bytes held elsewhere](/docs/proposals/bytes-held-elsewhere.md), implemented
and unreleased, lets a copy hold the history of a file of bytes without its
bytes: `fetch --no-bytes`, `fetch <url> <path>...` and `evict`. It drew the
line at bytes on purpose, and gave the reason for not drawing it anywhere
else:

> A text payload is the base every later operation document of its file is
> replayed onto, so without it `record` cannot diff an edit, `merge` cannot
> replay one, and `cat`, `diff` and `blame` fail at every revision. A text
> file left behind would be a file this copy can neither read nor change.

That is true of a copy that has no way to get the text back. This proposal
gives it one, and draws the line again.

The rest is already in place:

- **A store missing content is legal.** `check` reports an `edit` naming an
  operation document the store lacks as `MissingOperations`, and a missing
  payload as `MissingPayload`. Both are notes (`src/store/check.rs`). Only
  `check --complete` fails on them, which is the question it exists to ask.
- **Revisions are the graph, and they are small.** A revision document holds
  the parents, author, times, message and which files it touched. Measured on
  historica-git's store: 54 revisions in 244 KB, against 238 files of
  content, operation documents and payloads, in 1.3 MB. `log`, `names` and `show <revision>` read only
  revisions.
- **A fetch already reads revisions before the rest.** `--no-bytes` asks for
  them first to learn which payloads are bytes, and still writes them last,
  under [0048]'s ordering.
- **The address of content left behind already has a home.** Bytes held
  elsewhere keeps the addresses of payloads it left in the host's cache
  ([0078]), where deleting them costs time and nothing else.

## The proposal

- **`fetch --history` takes revisions, bookmarks and rules, and no content.**
  The graph arrives whole, so `log`, `names`, the record of who did what and
  when, and every question 0086 asks about heads are answered. No
  operation document and no payload is taken. On the 54-revision store above,
  that is about a sixth of the bytes and a fifth of the requests.
- **`fetch --name <bookmark>` takes the content of one line.** Every revision
  arrives, as above, and content only for the ancestry of the revisions the
  named bookmarks resolve to. A reader who wants `main` does not take every
  held contribution under `changes/`, or every fork's offer. The ancestry is
  closed, as [0086]'s followed set is, so the copy holds whole history for the
  line it took.
- **A command that needs content the copy lacks fetches it.** `cat`, `diff`,
  `blame` and `update` resolve the files they read, and where the store does
  not hold a file's chain — its base payload and every operation document
  since — they fetch the chain from the copy this store last fetched from,
  hash every document against the digest its revision names, and continue.
  The address is kept in the host cache beside bytes held elsewhere's, so
  deleting the cache costs the next command a refusal that names
  `fetch <url> <path>`, and nothing else.
- **Without a connection, such a command refuses, and names what it lacks.**
  It says which files' content is held elsewhere and the `fetch` that brings
  it. It never answers from part of a chain.
- **`record` reads the folder by bytes held elsewhere's rule, extended to
  text.** A path whose content the store does not hold is not surveyed while
  the folder has no file there. Where the folder has one, `record` needs the
  base to diff it, so it fetches the chain first, and refuses offline, naming
  the file. A file of bytes still needs no base, as before.
- **The default does not change.** A plain `fetch` takes everything, and a
  copy taken that way can still be read with an editor and `shasum`, which is
  what `format.txt` promises. A copy holding history elsewhere cannot keep
  that promise for the content it never took, and the flag is how a person
  says that is acceptable.

## Why text is different from bytes, and why that is now fine

Bytes held elsewhere stops at bytes because nothing historica does with a
file of bytes reads it. Text is read by everything: every edit is a diff
against a base, and every read replays operations onto one. So a copy without
a file's text chain cannot do anything with that file *on its own*.

The change here is the words "on its own". With a source, the copy can do
everything after a round trip: read the file by fetching its chain, and change
it by fetching its chain first. What it loses is working on that file offline,
which a copy that fetched it whole never loses. The trade is the one a person
makes when they clone a forge's repository to read it rather than to live in
it, and the flags name it.

## Costs

- **A chain is long.** A text file's content at a revision is its base
  payload and every operation document after it, so reading an old file in a
  long history fetches many small documents. That is only bearable if a
  fetch's small files travel together. Today the CLI's HTTP source does not
  implement `Source::prefetch`, so each is a round trip in turn, which is a
  task of its own and the reason a first fetch of historica-git from the hub
  takes a minute and a half.
- **A command that never touched the network now can.** `cat` and `blame`
  become commands that may make requests. The refusal offline is the cost of
  keeping that visible, and a command never fetches from a source the person
  did not fetch from first.
- **`check --complete` fails on such a copy, correctly.** It is not whole.

## Rejected alternatives

**A shallow copy, from a date or a depth.** Git's `--depth`. A text file's
content is built by replaying operations from where the file was first
stored, so cutting history at a point needs every file's whole content at that
point, stated somewhere. No document in the format says that, so a shallow
copy would need a new kind of document, a snapshot, and a rule for what
`blame` says above it. A copy with no history at all, `export --files-only`
([0060]), already covers *I want the files*, and a copy with history held
elsewhere covers *I want the history without paying for it*.

**A sparse copy, by path.** Taking only the content under some directories.
Operation documents are filed under the path the file had, so this looks
cheap, but a file is identified by its identifier through every move, and a
file that moved into the chosen directory has content filed outside it. It is
possible, and it is a refinement of `--name` rather than a different
mechanism. Deferred until somebody needs it.

**A URL in the revision**, saying where content can be fetched. Bytes held
elsewhere rejected this for payloads, for reasons that hold for text: a URL
is one publisher's arrangement, it goes stale without the history changing,
and it would be the first thing in a revision two copies of one history could
disagree about.

## Open questions

1. **Whether `evict` extends to text.** Letting go of a text chain a copy
   holds, as `evict` lets go of bytes. It is the symmetric act, and it is the
   one most likely to leave a copy that cannot read its own folder offline.
2. **Whether `update` may leave a text file absent.** Bytes held elsewhere
   lets `update` leave a file of bytes absent rather than refuse. For text,
   this proposal has `update` fetch instead, since a folder missing its text
   files is not a folder anybody asked for. Offline, it refuses whole, as
   [0030] would.

[0030]: /docs/decisions/0030-the-folder-catches-up.md
[0048]: /docs/decisions/0048-asking-for-what-is-missing.md
[0060]: /docs/decisions/0060-the-copy-without-the-history.md
[0078]: /docs/decisions/0078-where-a-cache-is-kept.md
[0086]: /docs/decisions/0086-a-copy-chooses-its-heads.md
