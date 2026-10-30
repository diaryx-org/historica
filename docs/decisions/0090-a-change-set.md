# 0090 — A change set

A change set is a line of work somebody proposes beside a history, which
somebody else then takes in or turns down. Diaryx built one for its
assistant. The revisions went into the store and travelled. The record, its
title, author, base and state, went into the device's caches and stayed
there. So a phone could not list or decide a change set proposed on a
laptop. The argument is the proposal
[A change set beside the history](../proposals/a-change-set-beside-the-history.md).
Adam settled its one open question on 2026-10-29: accepting is a merge.

## The decision

**A change set is an opening revision, a line on it, and shared bookmarks
under `change-sets/<id>`.**

- **The opening** stands on the revisions the change set is proposed
  against, records nothing, and carries the proposal in its message: a
  title on the first line, and anything after it. Its author proposes the
  change set and its `when` is when it began. Its message is required, for
  0013's reason: a revision that records nothing says only what its
  message says. Another tool's headers may go on it (0070).
- **Its id** is the opening's change ID.
- **The line** is the revisions between the opening and the tip, each
  standing on the one before. They are ordinary revisions.
- **Four names**, each pinning a revision, each shared, each written by the
  library:
  - `change-sets/<id>`: the tip.
  - `change-sets/<id>/submitted`: the tip the proposer said was finished.
  - `change-sets/<id>/accepted`: the merge that took the line in.
  - `change-sets/<id>/declined`: the tombstone that abandoned it.

**Recording onto an undecided change set's tip, with the tip as the only
parent, is its next step.** `record` moves the tip pin onto the new
revision, beside 0011's rule for change bookmarks, and reports it in
`advanced`. A merge naming the tip is not a step. Neither is a revision on
the tip of a change set already accepted or declined. A step that needs
other parents, such as the proposer merging in what the base gained, is
`change_set::advance`, which refuses anything not further along the line.

**Accepting is a merge whose parents include the tip.** It is recorded the
way any merge is, by whoever accepts. `change_set::accept` then writes the
`accepted` name, and refuses a revision with fewer than two parents or
without the tip among them. When the accepted head has not moved since the
change set began, the merge names the base and the tip, which `record`
already allows.

**Declining is a tombstone** over the opening and every step (0013),
standing on the base, with the reason as its message.
`change_set::decline` writes it and the `declined` name. The change set's
change becomes `Abandoned`. It supersedes the change set's own revisions and
nothing else. 0013's `abandon` takes everything standing on what it
abandons, which could be another change set proposed on this one's tip, so
decline writes the tombstone itself and refuses while other work stands on
the line. A tombstone standing there holds no work and does not count.
Where the opening was retitled, the tombstone supersedes the opening's
current revision, since the retitling already superseded the one the line
stands on.

**A change set's state is read from its names.** Accepted if `accepted` is
there, else declined if `declined` is, else submitted if `submitted` is,
else open. An acceptance outranks a tombstone, because a line in the
ancestry of a merge is in the accepted history however it was declined.
Both stay readable.

**A decision covers the line its decider saw.** A replica that has not heard
of an acceptance may record another step. When the two meet, the tip pin
moves on to it, as tips do. That step is not accepted: the merge does not
hold it. So a decided change set is read up to the last step its decision
covers, the acceptance merge's parent on the line or the steps the
tombstone supersedes, and `ChangeSet::tip` is that step. The steps beyond it
are `ChangeSet::after`, recorded before the decision was heard of and not
part of it. The pins still converge, because every replica moves the tip the
same way, and so do the readings.

**Two replicas reconcile by one rule, `change_set::reconcile`.** Readings
at one target agree, and their axes join (0062). A tip or a `submitted`
whose reading on one side is in the ancestry of the other's comes to the
one further along. Anything else that differs is `MutableConflict::Name`,
as before. `receive` asks this rule over the union of both stores'
revisions. `fetch_following` moves a change set's tip and `submitted`
forward by it, and does not ask whether the copy follows the proposer
(0086): a copy holds a proposal, it does not follow one. Everything 0088
says of every other bookmark is unchanged.

## The library

`historica::change_set` holds the whole concept. `ChangeSet` is one read
from a store: its id, opening, title, description, author, created, base,
tip, steps, and the three decisions. `State` is where it stands, and `Part`
reads a name as one of a change set's four. `Store::change_sets` lists them
newest first. It leaves out a name whose revisions have not arrived yet,
because nothing can say what it proposes. `Store::change_set` reads one,
and `Store::acceptances` lists the merges naming its tip. The writers are
`propose`, `advance`, `submit`, `accept` and `decline`. `reconcile` is for a
host that syncs without `receive`.

## The CLI

```console
$ historica change-set propose -m "Tidy the reading list"
proposed change-sets/qpvuntsmwlrkzxonmvtplsyq: "Tidy the reading list"
record its steps with `historica record --onto change-sets/qpvuntsmwlrkzxonmvtplsyq`
$ historica record --onto change-sets/qpvu… -m "One list"
$ historica change-set submit qpvu
$ historica change-set
qpvuntsmwlrk  submitted  1 step  Adam Harris <adam@example.com>  Tidy the reading list
$ historica update change-sets/qpvu…
$ historica record --onto main --merge change-sets/qpvu… -m "Accept it"
$ historica change-set accept qpvu
accepted change-sets/qpvu…: "Tidy the reading list", by 3f2a…
```

`change-set show <id>` prints one change set whole, and `change-set
decline <id> -m <why>` writes the tombstone. A change set is named by its
id, a prefix of it, or its bookmark.

## Rejected alternatives

The proposal's section holds them. In short: a reserved directory of
records, refused because every fact it would hold already has a home in a
revision or a name. Fields in the bookmark file, refused by 0062's own
argument. The title in a step's header, refused because a change set exists
before its first step. A change bookmark on the tip, refused because it
follows the acceptance merge and every amendment. State as a name moving
between directories, refused because a deletion is local (0073). Moving
every pin forward on `receive`, refused because a pin is a pin on purpose.

## Consequences

- `record` moves a change set's tip pin. A caller recording onto one sees
  `change-sets/<id>` in `Recorded::advanced`. That is a `Behavioural-change`.
- `receive` no longer refuses a store whose change-set tip is further along
  than the receiver's, in either direction. `fetch_following` moves one
  that 0088 would have kept as `Pinned`.
- `historica::change_set` and `historica change-set` are new.
- Diaryx keeps agent authorship, its `diaryx.*` headers, and pedantic's
  held rule on top. Its sync has to carry shared bookmarks, through
  `reconcile`, before any of this reaches a second device. The proposal's
  *The Diaryx follow-up* says what changes there.

## Deferred

**A rewritten line.** Amending, squashing or carrying a step leaves the tip
pin on the superseded revision, and `advance` refuses a successor because a
successor is not further along. The proposer re-pins by hand with `name
--revision`. A rule that moved a change set's pin to the one successor of a
rewritten tip would fix this. Nothing has needed it yet.

**Steps after a decision.** `after` says which steps no decision covers, and
nothing yet offers to do anything with them: propose them again as a new
change set, or decline them. A tool that meets them says so for now.

**`check` findings.** A `change-sets/` name pinning a revision that does not
stand on its opening, or a decision pinning something that does not decide
it, is skipped by `Store::change_sets` and not reported. A finding for each
would be right once something writes them other than this library.

**A conflict that keeps going.** Two tips on two lines, or two acceptances,
refuse the whole receive, as 0062 has any bookmark conflict do. For a sync
that runs every thirty seconds that is a deadlock until a person restates
one name. Diaryx's sync keeps its own reading and reports instead, which
`reconcile` lets it do. Whether `receive` should do the same for a change
set is a question for when someone meets it.
