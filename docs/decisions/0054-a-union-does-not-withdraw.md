# 0054 — A union does not withdraw

0053 gave a reserved directory a travel class and said what `export` and
`receive` do with each. It settled the question in the shape everybody was
asking it — does this cross a boundary — and left one half of it unasked,
because at the time an export crossed the boundary exactly once:

> `export` carries a travelling directory whole.

0052 made an export something that happens repeatedly onto one destination,
and the sentence stops being complete. Carrying `claims/` into a copy is
obvious the first time and obvious every time the origin gains a file. What
0053 never had to answer is what the *second* run does about a file the copy
holds and the origin does not — because until 0052 there was no second run.

The rest of that export is a diff. 0052's whole argument is that an
add-only publish would leave the world-readable copy holding a permanent
record of everything the origin ever had, so a `forget` withdraws, a `prune`
withdraws, a branch the target left withdraws, and a rule the origin made
`private` withdraws. Against that, a directory the run adds to and never
subtracts from looks like an oversight rather than a policy, and it needs to
be one or the other in writing.

## The tension, stated fairly

The case for mirroring is the case 0052 already made. The origin is
authoritative and the copy is its rendering; the refusal to merge exists so
that nothing accumulates in the copy that the origin cannot account for. A
publisher who deletes a claim — because the key was compromised, because the
role was wrong, because they no longer wish to vouch for that revision —
plainly wants the published copy to stop carrying it, and every other file in
the copy behaves that way.

The case against is that `claims/` is not like every other file in the copy,
and 0053 spent a decision saying exactly how.

## The decision

- **A travelling reserved directory unions in both directions and at every
  run.** `export` onto a copy it already made carries what the copy lacks,
  with `create_new`, and withdraws nothing. A name the copy already holds is
  left exactly as it is and never read, which is what `receive` does on the
  other side of the same boundary (0053) and what `export` now does on both.

- **The class is the reason, not the tool.** `travels-and-unions` promises
  that two stores holding one name hold one file, which is what makes a merge
  rule unnecessary. Withdrawal is a merge rule: it says a name present here
  and absent there means *deleted* rather than *not yet arrived*, and that is
  a claim about a grammar historica has promised not to learn. There is no
  version of the rule that is about `claims/` rather than about the class,
  because the whole point of 0053 is that transport never learns which
  directory it is holding.

- **Absence is not revocation, and this format knows the difference.**
  Everything historica destroys, it destroys because something *says so*: a
  forgetting document is a recorded fact that travels with every copy and is
  complied with wherever it lands (0014). Nothing here says anything. A
  withdrawal keyed on absence would be the one destruction in the design with
  no record behind it — and, worse, an unenforceable one, since 0053 made
  `receive` add-only in the other direction and any replica that still holds
  the file hands it straight back. A redaction the next sync undoes is not a
  redaction; it is a thing that looks like one.

- **A publisher who wants a file out of the copy deletes it from the copy.**
  It is one `rm` in a directory that is theirs, and the next export will not
  put it back, because the origin no longer holds it to carry. That is the
  whole remedy, it is available today, and it is stable — which is more than
  mirroring would have given, since mirroring reintroduces the file the moment
  anybody receives from a replica that kept it.

- **The two ways to be wrong are not symmetrical, again.** Failing to withdraw
  leaves in the copy a file that is *already published* — carried by an
  earlier run, under a class that said it could travel — so nothing new is
  disclosed. Withdrawing wrongly destroys a file historica cannot read, cannot
  reconstruct, and did not write. 0011's test in 0045's words, and 0053's own
  default for an unclassified directory: between an exact answer that can fail
  either way and an inexact one that can only fail the recoverable way, this
  project has chosen the second every time.

## What a stray claim in the published copy means

Worth following through, because it is the case that most looks like it argues
for mirroring and on inspection argues against.

Somebody other than the publisher puts a file into the copy's `claims/`. Under
add-only it stays. Under mirroring it is deleted on the next publish — and
then written again, by whoever could write it the first time, because a party
with write access to the published directory is not stopped by a rule that
runs when the publisher happens to export. Mirroring buys no defence here. It
is a tidying operation dressed as a control.

What it *does* buy is the failure in the other direction, and that one is not
hypothetical. `claims/` is the one directory in the store designed for several
parties to add to: a second signer vouching for the same history writes a file
the origin has never held, and 0046's whole design is that the file is
self-describing, so it needs no permission from anybody's store. Under
mirroring, the publisher's next routine export silently destroys it. The
directory built for more than one voice would be the directory in which only
the origin's voice survives, and nothing would report the loss, because
nothing here reads the files well enough to know one went missing.

Add-only keeps the stray and keeps the co-signature. Mirroring loses the
co-signature to catch the stray it cannot actually catch.

## Rejected alternatives

**Mirror the origin.** Above, at length. Its strongest form — "the copy is the
origin's rendering and should hold what the origin holds" — is true of every
directory historica reads and false of the two it does not, for the reason
0053 already gave: what historica knows about these files is how they travel,
and how they travel is a class rather than a policy.

**Withdraw only what an earlier export carried.** A record of what this
exporter put there, so it removes its own files and leaves everybody else's.
It would need state — a manifest in the copy saying which files were the
exporter's, which is the file-describing-itself that 0053 and 0048 both
refused, or a re-derivation from the origin, which is the mirroring rule with
extra steps and the same answer for the co-signer's file on the day the origin
first lacks it.

**`export --prune-claims`, opt-in.** 0053 refused `export --claims` for a
reason that applies unchanged: a flag makes what the copy holds depend on what
somebody remembered to type, and the forgetful direction is silent. A
destructive flag is worse than an additive one, since the run that forgets it
is the harmless one and the run that includes it is the one nobody reviews.

**A second class, `travels-and-mirrors`.** Coherent, and premature. It is a
line in the registry and a decision document on the day a tool exists whose
files genuinely are the origin's alone — the same rule 0053 set for
reservations themselves: need first. Nothing is foreclosed by deciding
add-only now, because a directory reserved under a new class is a new name.

## Consequences

- `export` onto an existing copy needs no new code for this: `carry_travelling`
  is already `create_new` and already reports whether the name was free. What
  changes is that the count is what was *carried* rather than what was
  offered, so a publish that adds nothing says so.
- The published copy can hold claims the origin has deleted, and 0052's
  consequence about drift gains a second entry: readable names drift because
  collisions are resolved against a growing set, and `claims/` drifts because
  a union is monotone. Neither is read by anything but a person.
- `check` gains nothing, here as in 0053. A class is a statement about
  transport, and this is a statement about one direction of it.
- The store's module documentation and `export`'s say the rule, so that a tool
  reserving a directory can read what historica promises about it rather than
  finding out by publishing twice.

## Deferred

**A recorded revocation.** The thing that would let a claim be *destroyed*
rather than merely not carried is a fact somebody states — historica-minisign's
own forgetting document, in its own grammar, complied with by the tool that
can read it. That is the tool's decision to write and not this one's, and the
class established here is what it will be written against: a revocation file
travels and unions like every other file in the directory, and the tool
reading them is what makes it mean anything.
