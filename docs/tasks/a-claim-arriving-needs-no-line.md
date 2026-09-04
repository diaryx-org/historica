---
title: A claim arriving needs no line
description: 0074 has no line kind for a reserved directory, and should say in Deferred that it needs none — a claim arriving only ever moves a revision from unvouched to vouched
status: done
created: 2026-09-02
updated: 2026-09-03
part_of: "[Tasks](tasks.md)"
---

# A claim arriving needs no line

**Status: done.** 0074's Deferred carries the argument, as *A reserved
directory, which needs no line and is not an omission*, and `Received` and
`Fetched` say the same thing on the `reserved` field a reader of the code meets
it at. Resolved by the commit that amended 0074 ahead of `historica-wrote-1`.

[0074](../decisions/0074-saying-where-to-look.md)'s vocabulary is four line
kinds — `revision`, `name`, `unname`, `gone` — shaped to what a store holds.
A reserved directory is a fifth thing a store holds. `receive` unions `claims/`
under [0053](../decisions/0053-room-for-another-tool.md) and
counts what arrived in its result's `reserved` field, and no line kind reports
it. 0074 lists `skip` in Deferred for exactly this reason and does not list this.

**The resolution is a paragraph in Deferred, not a line kind.** The reason it is
only a paragraph is worth stating in the decision, because it is not obvious:
a claim arriving can only ever move a revision from unvouched to vouched, never
the other way. So the wrapper this would serve —

```sh
historica receive --fields ../other | historica-minisign verify --complete
```

— never needs to know that one came. It runs `verify` when the statement has any
line at all, and the verdict is over the store as it stands rather than over
what arrived. `trust/` is local-only and never arrives. Adding a line kind would
be `historica-wrote-2` under 0074's own compatibility rule, for a distinction no
caller has needed.

Note the same paragraph in `receive`'s and `fetch`'s rustdoc if it is not
already plain there, so a reader of the code meets the argument too.

## Adjacent, and deliberately not done here

Two things this touches and leaves alone:

- **Enforcement inside receive.** Refusing unvouched history at the door is
  deferred by [0046](../decisions/0046-who-vouches-for-a-revision.md) to a
  need-first trait, and the only in-process host has met the need and declined
  it: diaryx's vouch module argues that refusing at the door leaves a reader
  with nothing to look at and no way to judge what they were asked to judge.
  Receive is add-only, `log` shows what came, `abandon` exists. A command-line
  gate is worse still, because trust never travels — before the receive the
  claims are there and the trust is here, and no tool holds that split.
- **`RESERVED_DIRS` as a caller-supplied value.** Also 0053's need-first trait.
  The table is a library-side, receiver-side check that
  [0056](../decisions/0056-listing-what-it-cannot-read.md) makes the receiver's
  own authority, consulted by export, receive, fetch and offer in hosts with no
  command line — so nothing 0072 or 0074 adds can stand in for it. `claims` and
  `trust` stay in the default whatever happens, because the format promises them
  and the CLI has no other source. Waits for somebody with a third reservation,
  under [0045](../decisions/0045-one-rule-to-a-file.md)'s rule.

## Done when

- 0074's Deferred names the reserved directories and carries the argument above.
- Nothing else changes: no line kind, no version bump, no code.
