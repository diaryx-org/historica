# 0022 — Names the store cannot own

Recording this repository and then opening the store in a file browser
destroyed a payload.

`.DS_Store` at the repository root is bytes, so 0017 stored it whole and 0018
filed it under its own name:

```
history/operations/2026-08-21 My first record!/.DS_Store
```

macOS Finder writes a `.DS_Store` into every folder it displays. It wrote one
there. The 10 244 bytes the revision names are gone, replaced by 6 148 bytes of
Finder's own metadata, and every command that opens the store now fails with

```
fb04b477 names the content 9c110ed2, which this store does not hold yet
```

It does not hold it, it will never hold it, and nothing said so at the time.

The irony is the point. 0016 built the folder to be browsed and 0018 made it
look like the repository so that browsing it would be worth doing. Browsing it
is what broke it.

## The general shape

0018 gave payloads the names their files have, and a name is a thing other
writers use. The format has met this once already — 0021's rule that a payload
never carries `.ops.txt`, because that is a name *this* reader claims — and
that rule was written as though the format were the only other writer in the
folder. It is not. The operating system writes into every directory it is
shown, and it does not ask.

So the rule generalises: **a payload is never filed under a name the store does
not own.** `.ops.txt` is one such name because Historica claims it. `.DS_Store`
is another because Finder claims it.

## The decision

- **A short list of names the platform writes**, matched on a payload's last
  component: `.DS_Store`, `Thumbs.db`, `desktop.ini`, `.localized`,
  `.directory`, and anything beginning `._` — the AppleDouble files that appear
  beside every file when a folder is copied to a drive that cannot hold
  resource forks.
- **Inside the store, a file with one of those names is not a payload**, and
  not a finding either. It is somebody else's file in our folder, and `check`
  saying so on every macOS machine would be a note that means "you opened this
  in Finder".
- **A payload is never filed under one of them.** It takes the digest suffix,
  exactly as 0018 does for `.ops.txt`: `.DS_Store 9c110ed29105`.
- **`history/skipped.txt` gains comments.** A line whose first character is `#`
  states nothing, so 0011's reason for refusing an unknown key — that a reader
  which ignored one would record files somebody asked it to keep out — does not
  reach it.
- **`init` writes a default `skipped.txt`** that keeps those names out of the
  working copy's walk, with a comment saying it is a default and may be
  deleted.

## Why the skip rule is not the fix

Writing `skip-suffix .DS_Store` at `init` stops the file being recorded, and it
would have prevented this particular failure. It is not the fix, and shipping
only that would be the wrong lesson learnt from the right bug.

Finder writes into the store whether or not the working copy has anything to
skip. A person who opens `history/operations/` gets a `.DS_Store` there
regardless, and the store has to know that file is not content. The skip rule
is about what a *history* should hold; the other two rules are about what a
*store* can survive, and only the second kind keeps a promise.

The skip default is worth having anyway, for a reason of its own: recording is
append-only and 0014's forgetting is not built, so a first run that sweeps a
folder of operating-system metadata into a permanent history is a mistake a
person cannot take back. A default they can see and delete is the smaller
imposition.

## What it costs

**It is a blocklist, and blocklists rot.** Some platform will invent a name
this list does not have, and the failure will be the same one: a payload
overwritten by something that had every right to write there. The list is
short, it is stated where a person can read it, and it will need adding to.

What makes that tolerable rather than fine is the failure mode either way. A
name that ought to be on the list and is not costs one payload and a loud
error. A name on the list that need not be costs a digest suffix on one
filename. Those are not symmetrical, which is why the list may lean long.

**A payload legitimately called `.DS_Store` cannot have its own name.** A
repository that stores one deliberately — this one might, as a fixture — gets
`.DS_Store 9c110ed29105`, which is the same trade 0018 already makes for a file
called `notes.ops.txt`.

## What this does not fix

**The store still cannot be repaired.** The bytes are gone; no other copy
exists; the revision names a digest nothing holds. `check` calls a missing
payload a note, on the reasoning that transport has more to deliver — true when
a payload is missing because a replica has not sent it yet, and false when it
is missing because something overwrote it. Telling those apart needs a fact
this format does not record, and `status` failing outright while `check` calls
it ordinary is a disagreement worth its own decision.

## Consequences

- `store` gains the list and a predicate, applied where payloads are indexed
  and where `check` walks `operations/`.
- `naming` avoids the list as well as `OPERATION_SUFFIX`, which is one more
  condition on a rule that already had two.
- `working::Skipped::parse` accepts `#` comments, and keeps refusing unknown
  keys.
- `Store::init` writes `skipped.txt` rather than leaving it absent, which makes
  a store's initial file count one higher and its first `check` no different.
- The corpus is unchanged: none of this touches a document's bytes.

## Rejected alternatives

**Skipping the file and nothing else.** Above: it fixes the recording and
leaves the store corruptible by a file browser.

**Refusing to record any file the platform writes.** A rule about the working
copy dressed as a rule about correctness. A person may want their `.DS_Store`
recorded — it is their history — and the store can hold it perfectly well under
a name Finder will not reach for.

**Making the store's directories hidden, or read-only.** Hiding them defeats
0016 entirely. Read-only defeats a writer that has to append, and a file
browser that wants to write a `.DS_Store` into a read-only directory fails in
ways that are not this project's to explain.

**Naming every payload with a digest suffix, always.** Sound, and it gives up
the readable folder that four decisions have been spent buying.

## Resolved questions

1. **Whether a missing payload should stay a note in `check`.** It means "not
   delivered yet" and it also means "overwritten", and this document found the
   second while the wording assumed the first.
   [0027](0027-closing-the-small-questions.md) keeps it a note because absence
   cannot distinguish the two, and changes the wording to name both.
2. **Whether `skipped.txt` should carry defaults.** Answered no by
   [0027](0027-closing-the-small-questions.md): `init` writes syntax help and
   no rules. Platform, project, and user defaults belong to a higher layer that
   knows what the folder means.
