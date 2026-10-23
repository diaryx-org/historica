# 0007 — A key has a history, and a copy can follow what keys vouched for

Historica's decision 0086 has a copy choose its heads with a rule asked of one
revision at a time, and names this repository as where a forge's rule comes
from: follow what a maintainer's keys vouched for. The forge proposal
(historica-view, "A forge of forks and remarks") adds that an account holds a
key for each device, as GitHub holds SSH keys, and that a key keeps when it was
added and when it was revoked. A claim by a revoked key still counts for what
it signed before the revocation.

Two things are needed: a trust entry that can carry a key's history, and the
rule.

## The decision

### `trust-1`

```
trust-1
key RWTd8LRCGA9i53mlYecO4IzT51TGPpvWucNSCh1CBM0QTaLn73Y7GFO3
who Adam Harris <adam@example.com>
added 2026-03-02T10:00:00-07:00
revoked 2026-10-19T08:30:00-06:00
```

`trust-0`'s two headers, and `added` and `revoked`, each at most once. A
`trust-1` states at least one of them. An entry with neither is written
`trust-0`, so one entry has one spelling. A key revoked before it was added is
refused. Under `trust-0`, `added` and `revoked` are headers the grammar does not
name, and the entry is refused, as 0001 says.

A claim, or a head statement, by a key counts when its `when` is before
`revoked`. At or after it, it does not count, and `verify` reports it as
`Revoked`: a note, like a claim by a key nobody here believes. Times are
compared as instants, so one moment in two offsets is one moment. Where two
entries hold one key, a revocation in either wins.

`added` bounds nothing. It is a record for the person reading the folder.

`historica-minisign trust revoke <label> [--as-of <time>]` writes the line. It
is the one command that rewrites a trust file, and it writes only if the file
still holds what it read. A revocation only moves earlier.

### The rule

`Vouched` is given a set of trust entries and a store's claims. It accepts a
revision when a `claim-0` over its digest verifies under one of those keys and
was made before that key was revoked. Every claim is read and checked once,
when the rule is made; asking about a revision is a lookup. `into_rule` gives
a closure of the shape historica's `Accepts` has.

Every key it is given counts as one identity. Which keys belong together is the
caller's to say: `Vouched::trusted` takes every key in `trust/`, and a forge
takes the keys on an account. `who` stays a label.

Every role counts unless the caller narrows it with `only`.

## Why

**A new preamble, not two optional headers.** 0001 grows the claim grammar by
minting a preamble for a narrowing, and a revocation is a narrowing. A reader
built before `trust-1` refuses the entry and believes the key not at all. It
can under-count a revoked key and can never count what the key signed after
it was revoked.

**Revocation is a moment the person names.** A claim's `when` is written by
whoever holds the key, so a thief can write an earlier time, and nothing here
can stop that. What revocation stops is everything the key signs afterwards at
its true time: an old laptop still syncing, a script nobody turned off. A
person who revokes a key as of when it may first have leaked gives up the
claims in between and keeps the rest. Head statements (0005) and what a copy
has seen are what catch history that appears later than it says; revocation
does not pretend to.

**`added` is not a lower bound,** for the same reason: anyone holding the key
can write a time after it. A bound would refuse an honest claim made before
somebody added the key, and would stop nobody.

**Every role by default.** A role is what a person says they were doing, and
this repository keeps no vocabulary of roles, so it cannot say which ones mean
"this is my line". A forge where a `reviewer` claim is an approval, and taking
an offer is a separate act, narrows to `author`, so that approving a
contributor's tip does not make it the maintainer's head.

**Shaped like `Accepts`, without naming it.** This crate depends on historica
by version, and the release it is written against predates `Following`. The
rule uses only `RevisionId` and `RevisionDocument`, which every release has,
so a caller on a later historica writes
`Following::Rule(Box::new(rule.into_rule()))`.

## Rejected alternatives

**A key list per identity, in its own file.** One file per identity, listing
its keys, would group keys by person in the folder. It would also be a second
place a key is believed, and two places can disagree. One key to a file stays
0001's rule; grouping is the caller's choice of entries.

**Removing a revoked key's entry.** Removal already exists, and it unseats
every claim the key ever made. Revocation is for the key whose past claims are
still true.
