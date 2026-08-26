# 0046 — Who vouches for a revision

Every revision document states an `author`, and nothing checks it. The store
was built so a person can verify what it holds with `shasum -a 256`; there is
no equivalent command for who holds the pen. 0029 requires both stores to pass
`check` before a receive, and `check` proves a store consistent, not honest: a
history fabricated under somebody else's name, digests all correct, passes
every gate this format has. The digest machinery answers *whether these are
the bytes*; it is silent on *whose word they are*.

The silence is not an oversight to patch in place. The revision document
cannot carry a signature over itself — its identity is the SHA-256 of its own
bytes, and a document cannot contain a signature over a digest that depends on
the signature. The tools that splice a signature into the hashed object buy it
with a hashing rule that has a hole in it: everything except this header. This
format's one non-negotiable rule is that the readable files are the authority,
so the answer to "who vouches for this?" must be more readable files — and it
turns out nothing about writing or checking such files needs Historica at all.

## The decision

- **The trust layer is a separate tool.** Historica gains no command, no
  cryptographic dependency, and no grammar. This decision fixes the boundary —
  what the tool's files are, where they live, and the one promise the store
  makes about them. The tool's name and repository are not this decision's to
  pick.

- **A claim is a readable document that vouches for a digest.** One claim
  states one key, one digest, one role, one moment:

  ```
  claim-0
  revision 33f863f19e9b19f47ae42e41b4c25f03acc3c14acca2da65ea6bb141016b487a
  role reviewer
  key RWTd8LRCGA9i53mlYecO4IzT51TGPpvWucNSCh1CBM0QTaLn73Y7GFO3
  when 2026-08-24T09:12:04-06:00
  ```

  The grammar belongs to the tool's own specification; the shape is fixed
  here. A claim vouches for a digest, and a revision's digest pins its bytes,
  which pin its parents' digests, and so on to the roots — so one claim over
  one revision covers the whole ancestry behind it, and signing every revision
  is a choice, never a requirement.

- **The signature is minisign, detached, beside the claim.** The claim's bytes
  are what is signed; the `.minisig` sits next to the file it signs. Minisign
  is one small tool with one job, `rust-minisign` implements it without a C
  library, and `minisign-verify` verifies with no dependencies at all.
  Checking a claim by hand is two commands and neither is Historica:
  `minisign -Vm` the claim, then `shasum -a 256` the revision it names. That
  is "Checking a store by hand" from `format.txt`, extended by one line.

- **Claims live in `history/claims/`, immutable and deterministically named.**
  A claim's filename is a function of the claim's own content, its signature
  is named for the claim it signs, and neither is ever rewritten. Immutable
  files under deterministic names are the concurrency story 0003 counts on:
  any file sync unions them without conflict, and `cp -r` — the transport 0029
  declines to replace — carries them correctly. *Which* function is the tool's
  own specification to fix; this decision first fixed it as the digest of the
  claim's bytes, and the amendment below relaxes that to 0003's naming rule. The store root is also the one directory `record` never
  walks, so the tool's files can never be swept into the history they vouch
  for.

- **The trust policy is `history/trust/`, one key to a file, and it never
  crosses a store boundary.** This is 0045's container without 0045's receive
  rule. The filename is a label for whoever opens the folder; the content maps
  one minisign public key to the person it speaks for. The tool writes entries
  with `create_new`, so two additions on one machine cannot lose one — 0045's
  property, inherited with the layout. What is not inherited is union: no
  operation of the tool, and no operation of Historica, writes this directory
  from another store. The argument is below.

- **A head statement is a claim.** A second document kind, same signing, same
  directory: this key, a counter, and the heads its history had at that
  moment. A verifier keeps the highest counter it has seen for each key and
  refuses a statement below it. What that buys and what it cannot is argued
  below, plainly.

- **The tool's `verify` reads and never writes.** It reports in 0006's split:
  a signature that fails to verify is an error; a claim by a key the policy
  does not hold, or a revision no trusted key vouches for, is an observation.
  A store with no claims at all verifies vacuously, because a tool that failed
  every store it had not yet met would teach people not to run it.

- **Historica's whole contribution is tolerance, stated.** `check` walks the
  directories it names and says nothing about the rest. That is true today by
  accident; this decision makes it a promise: a directory at the store root
  that Historica does not name belongs to whichever tool wrote it, and
  `claims/` and `trust/` are reserved for this one.

## Why trust does not union

0045 lets skip rules union and lets a deleted rule resurrect, on the argument
that resurrection is the safe direction of failure: a rule that comes back
keeps a file out of an append-only history, and deleting the file again
recovers everything. Both edges of that argument invert here.

A trust entry arriving from another store is authority flowing from the party
the policy exists to judge. For a skip rule, arrival means *record less* — the
failure is closed. For a trust entry, arrival means *believe more* — a store
seeded with an attacker's key verifies the attacker's history, and nothing
downstream can notice. And the one time removal must win is revoking a
compromised key. A revoked key resurrecting from a replica untouched since
March is not 0045's loud return that `status` shows; it is signatures quietly
verifying again. Union without tombstones structurally cannot make removal
win, 0045 accepts that because skips can afford it, and trust cannot.

By 0045's own test — between an exact answer that can fail either way and an
inexact one that can only fail the recoverable way — trust entries must not
union. So they never travel, which also dissolves the conflict 0045 exists to
fix: a file no store ever receives has no merge semantics to get wrong.

What this genuinely costs: a person with three machines states their policy
three times, or copies `trust/` themselves, deliberately, knowing what it is.

The line that keeps this consistent rather than exceptional: **a claim is a
fact, and trust is an opinion.** Claims union freely because holding one
commits a store to nothing — it is evidence, carried like any other document.
Whether the claim counts is the receiver's judgment, and the judgment file is
the one thing in the store another store must never write.

## What a claim cannot say

A signature never stops being valid, so a store can present a subset of a
history — every document intact, every claim verifying — and the subset lies
by omission. The sharp version is a withheld supersession: leave out the
revision that supersedes D, and D looks current, vouched for by signatures
that are all real.

Union already blunts half of this. `receive` only adds, so nobody can roll a
store back by sending to it; the exposure is believing an incomplete store is
complete. Head statements answer the half that remains answerable offline: a
store claiming to carry a key's history must contain everything reachable
from that key's latest statement, and a statement below a counter already
seen is refused. That detects regression from anything a verifier has
witnessed.

What it cannot detect is a withheld *newer* statement — freshness, as opposed
to rollback. The known answer is statements that expire, which makes silence
itself detectable, and its cost is that somebody must re-sign on a schedule
forever. A store that is a folder, moved by `cp -r`, possibly dormant for a
year and no worse for it, should not have a trust layer that rots on a
calendar. Declined, and named here so nobody mistakes the omission for an
oversight.

## Why a tool and not a command

Because the files are the authority, the trust layer needs nothing from the
inside. Writing a claim is writing a file and running minisign; checking one
is minisign and `shasum`; the policy is a directory of text files. Every
operation is one a person could do by hand, which is the test this format
holds itself to everywhere else.

The one thing a tool cannot do is enforce: `receive` refusing history that no
trusted key vouches for must run inside receive's preflight. That hook is
real, and this decision declines to build it, on 0045's own discipline — the
deferred section names it, and meeting the need in practice is what would
justify it. Until then, integration would mean a cryptographic dependency in
core and an enforcement policy nobody has yet needed, purchased before the
document formats have carried a single real signature.

If the documents earn enforcement, the integration is small precisely because
of this boundary: the claims are already in the store, already named
deterministically, already union-safe. Nothing about the format would change; Historica would
start reading files that were there all along.

## Amending the claim filename, because the format has to be hand-usable

This decision fixed the claim filename as the digest of the claim's bytes, and
argued it from concurrency: immutable digest-named files union under any file
sync. That argument is kept in full. What it does not require is the digest —
it requires determinism, and 0003's naming rule is deterministic. Historica's
own revisions are readable, deterministic and union-safe under the same `cp -r`
that carries claims, which is the existence proof this decision did not think
to consult about its own sidecar.

The cost of the digest name is one this decision could not see from here,
because it is a cost to a person rather than to a store. A claim is five lines
of text, and this decision's own argument for minisign is that checking one by
hand must be two commands a person already knows. Writing one by hand was
supposed to be the same kind of thing — and under a digest name it is not, since
the file cannot be named until after it has been written and hashed. A folder of
hashes is a ledger rather than a story, which 0003 says in as many words about
this exact shape of directory, and a person who writes the obvious file under
the obvious name gets a claim the tool silently declines to count.

So the filename is the tool's to choose, under the constraint this decision
actually needs: **a claim's path is a deterministic function of the claim, and
neither claim nor signature is ever rewritten.** historica-sign's decision 0003
chooses 0003's own scheme — the revision's stem, the role, and a content-derived
suffix only where two claims would otherwise meet — and keeps union safety by
the same rule that keeps it for revisions. Nothing in Historica changes: the
directory was already reserved, `receive` already does not carry it, and
`record` already does not walk it.

## Rejected alternatives

**A signature header in the revision document.** The self-reference argument
above, plus two costs the sidecar avoids: a revision could never be signed
after the fact, and never by a second person — yet the reviewer who signs
years later, and the two people who both vouch for one merge, are the normal
cases, not the edge.

**Trust entries that travel.** The inversion argument, in full, above.

**Claims in `cache/`.** 0044 puts facts about a copy in `cache/` because they
are disposable and local. A claim is neither: it is portable evidence, and a
directory that may be deleted without loss is exactly where it must not live.

**Keyless signing and transparency logs.** Binding signatures to networked
identity providers and public logs solves key distribution well, for software
that ships through infrastructure. This store's transport is a copied folder
(0029), its stores may never see a network, and a trust layer that fails
offline fails the format's first rule.

**OpenPGP.** Heavier tooling for the same detached signature, and verification
stops being one short command a person actually runs. The web of trust it
would buy is a key-distribution answer this decision already places in a
directory of readable files.

## Consequences

- Historica's code does not change. `format.txt` gains one paragraph: a
  directory at the store root not named there belongs to another tool, and
  `claims/` and `trust/` are taken. The layout listing in `store/mod.rs` says
  the same in a comment.
- `receive` does not carry `claims/`. Claims travel by the file sync or copy
  that already moves stores, which unions them correctly, or by the tool's own
  union command. If receive ever learns the directory, that is the deferred
  enforcement arriving, not a new idea.
- `export` (0042) builds a fresh store from documents and will not carry
  claims. A taker receives history without vouching, and obtains claims the
  same way they obtained trust in the first place: from the person, not the
  folder. Deferred below.
- The `x-` header space remains what it was: available to this tool for
  advisory annotations, ignored and hashed like everything else.

## Deferred

**Enforcement at receive.** A `receive` that refuses history no trusted key
vouches for is the one integration this design cannot deliver from outside.
Built when somebody meets the need in practice, not before.

**Guarded union of trust.** A trust entry countersigned by a key the receiver
already trusts could safely travel — key delegation and rotation, wearing
receive's clothes. The root keys stay local-only regardless, so this adds
convenience, not a new floor, and it waits for the same evidence everything
else here waits for.

**Claims in an export.** An export that carries the claims for its own
history would let vouching travel with the copy. It waits on the tool
existing, and on deciding whose claims an exporter is entitled to ship.
