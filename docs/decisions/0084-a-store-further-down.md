# 0084 — A store further down the folder

[0011](0011-working-copy.md) made the working copy the directory holding
`history/`, and tracked everything beside it except what `history/skipped/`
names. It said nothing about a second `history/` further down, because nobody
had put one there. The walk took it for content: a folder holding another
working copy recorded that copy's revisions, operations and bookmarks as files
of its own, and every revision the inner store wrote arrived in the outer
`status` as a change.

Diaryx put one there on purpose. Its proposal *A book someone else wrote is a
workspace inside the library* (accepted 2026-10-06) keeps a copy of a text the
library's keeper did not write — the Book of Mormon is the case — as a prov
workspace of its own inside the library folder, with its own identity, its own
config and, where it came with one, its own history. The library is one
historica working copy, so the book's folder is inside it, and so is the
book's store.

## The decision

- **A directory below the root is a store when it is called `history` and
  holds `historica.txt`.** That is the test `discover` already applies walking
  up, applied walking down. A folder that is only called `history` — a family
  archive's, say — is walked like any other.
- **The walk does not go into it and tracks nothing in it, with no rule.**
  This folder's own `history/` needs no rule for the same reason: it is a
  store, and a store's files are the store's documents, not content.
- **The folder it sits in is still content.** The book's chapters are files
  this folder holds, so this history records them. The two stores each record
  the same chapters, and neither knows of the other.
- **`Working::stores` lists what the walk found**, for a host that wants to
  know where the other working copies are.
- **A file the tree already holds inside such a store is refused, not
  dropped.** `record` and `status` say `TracksAnotherStore`, naming the file
  and the store. Only a history recorded before this decision can hold one,
  and the walk no longer offers it, so recording would spell it as a deletion
  — 0011's reason for refusing a `skip` rule over a tracked path, arriving by
  another door. The fix is the person's: move that working copy's store out,
  record the deletion, and put it back.
- **Naming a path inside one is refused** (`NamedInAnotherStore`), since
  [0039](0039-recording-some-of-the-folder.md) narrows what is looked at and
  this was never looked at.
- **`update` will not write a working file into one**, as it will not write
  into this folder's own store.

## Why the folder is content and the store is not

Git answers the neighbouring question the other way: a repository inside a
working tree is a submodule, and the outer repository records one pointer to
the inner one's commit rather than any of its files. That suits code, where
the inner project is somebody else's, versioned on its own schedule and
fetched from its own remote.

It does not suit the case that asked. The held book is in the library because
the keeper keeps it there: it has to travel with the library to every device
and into every backup, and the library's history is how it travels. A pointer
to the inner store's head would carry nothing to a device that has not got
the inner store, and the inner store is the part the proposal says need not
travel. So the folder's files are recorded here, as files this folder holds,
and the store beside them is the inner copy's own business.

The two histories can disagree about nothing, because neither records the
other: each records what the folder held when it was asked. A keeper who
corrects a typo in the book changes a file both copies observe, and each
records it when it is next recorded.

## Why there is no rule for it

A host could write the same exclusion as a `skip` rule — Diaryx's skiplist
writes rules from prov's ignore list already. But a rule is a statement about
one folder, written by someone, that can be missing. Without one, every
historica folder that holds another would record the inner store until
somebody noticed, and the inner store is a directory of files whose names
change on every `arrange` and whose count grows on every record: the worst
content there is to record by accident. This folder's own store is excepted
without a rule for exactly that reason, and the inner one is the same kind of
thing.

## What this does not decide

- **Whether a held text's edits are a line beside its source.** The proposal
  expects a keeper's edits to be recorded as a branch beside the source's
  line, to be argued with Diaryx's *An assistant hands back one change set*.
  That is a question about bookmarks and lines, and this decision only keeps
  one store out of another.
- **Which inner files travel.** The proposal has prov take the inner
  workspace's own ignore list for the inner folder. That is prov's walk, and
  arrives here as `skip` rules the host writes.
