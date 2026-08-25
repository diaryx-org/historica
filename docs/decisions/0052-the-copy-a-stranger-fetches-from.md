# 0052 — The copy a stranger fetches from

0048 built a fetch and left the other end of it to a convention:

> `offer.txt` at a root, and every path it names resolves relative to that
> root.

It never says what the root *is*, and the one example it gives —
"conventionally to `offer.txt` beside the store" — reads as an instruction to
publish the store. 0042 spent a whole decision refusing that:

> There is no directory on disk whose bytes are "the thing a stranger should
> have" … The `wget -r` failure — a mirror that ships what a privacy rule
> names — cannot happen to an assembled copy.

The hazard did not change when the pipe became HTTP. It got worse. `skip` and
`private` rules are one file each under `history/skipped/`, named by 0045's
label, so `target.txt` and `clients.txt` are guessable rather than
hash-obscured; 0051 made the text of a `private` rule the disclosure it is
about. A file server hands out any path asked for, and 0048's answer — that
`skipped/` is *not listed* — withholds nothing from anybody willing to type
one. Not listing a file is not declining to serve it.

Every version control system that publishes a repository directory to a plain
web server has this problem and has had it for twenty years. Exposed `.git`
directories are a scanner category. The difference here is that historica
already built the smaller artifact, and building it costs nothing in fidelity,
because 0042 made an export a replica: the same revisions, the same digests,
the same `receive` afterwards. Git has nothing smaller to serve. We do.

What that leaves is the objection that killed the idea the first time: an
export is a whole copy, and re-copying a store on every publish is not a thing
anybody will do on a timer. So this decision is two halves, and neither is
worth having alone.

## The decision

- **The thing at the URL is an export, and the manifest sits beside it.** A
  published root holds `offer.txt` and the exported repository under it. The
  store is untouched: nothing is written into `history/`, which is 0048's
  refusal unchanged, and nothing is written into the copy's folder, which
  would be an untracked file in the working directory of everyone who takes
  the copy.

- **`historica fetch <url>` takes the URL of the manifest, and every path in
  it resolves against the manifest's own directory.** So the paths begin with
  the exported directory's name — `store/history/operations/…` for a manifest
  beside a `store/`. `historica offer <dir>` writes them that way without
  being told, because the directory it was pointed at is the prefix it needs.
  One sentence of convention, as before, and it anchors at a place that is
  nobody's repository.

- **`historica export <dir>` updates an export it already made.** The
  `Occupied` refusal becomes a branch rather than an error where `<dir>` holds
  a store that is related (0029) and passes `check`. Unrelated, broken, or
  simply not a store, and it refuses as it does today.

- **A copy holding a revision the origin lacks is refused, naming `receive`.**
  Somebody recorded in the published copy. Export assembles; it does not
  merge, and the machinery for combining two histories is a command that
  already exists and should be run in the other direction first.

- **The set is `export_plan`'s, unchanged: the target's ancestry, closed.**
  What is new is that the copy is diffed against it rather than built from it,
  so an export has three outcomes per file instead of one — write it, leave
  it, or **withdraw** it.

- **Withdrawal is the point, not a tidy-up.** A `forget` at the origin has to
  destroy bytes in the published copy, or the redaction is defeated by the one
  copy that is world-readable. So does a `prune`, and so does a target that
  moves off a branch. An incremental export that only ever added files would
  publish a permanent record of everything the origin ever held, which is the
  opposite of what 0014 promises.

- **Additions ascend and withdrawals descend.** Payloads, then documents, then
  revisions; and revisions, then documents, then payloads. Both orders keep
  one invariant at every moment in between: *no revision in the copy names
  bytes the copy does not hold*. An interruption understates what is
  reachable, which is 0048's rule for a fetch and receive's rule before it,
  and the next run finishes the job.

- **Forgetting is complied with, where `receive` complies with it.** Between
  the documents and the revisions. A forgetting document that arrives destroys
  the original the copy still holds, exactly as it does anywhere else.

- **Rules are diffed in both directions.** A shared rule the origin has gained
  is written; a rule file the copy holds is withdrawn when the origin deleted
  the rule or made it `private`. This is the only thing an export removes that
  a recipient might have been relying on, and it is 0051's travel axis
  arriving at the one boundary that can be crossed twice.

- **`names/` is neither written nor removed.** An export has never carried
  bookmarks and still does not, and one somebody made in the published copy is
  not the exporter's to delete. `cache/` likewise: it is nobody's.

- **The folder is `update`'s work, as it always was.** `export_onto` already
  ends in `update::plan` and `update::apply`, and a non-empty folder catching
  up to a target is precisely 0030. Nothing here is new; the call site simply
  stops being able to assume the folder was empty.

- **An existing file is never renamed.** A new file whose readable name (0041)
  collides with one already in the copy takes the collision suffix, even where
  a fresh export would have given it the plain name. Renaming a published file
  breaks a fetch in flight for no gain, and 0048 already says a fetched path
  is an address rather than a name.

- **The manifest is written last, by a separate command.** `export` leaves a
  consistent copy; `offer` advertises it. A publisher runs two commands and a
  redirect, and nothing in the store learned that anybody is reading.

## What a stale manifest costs, restated

0048 priced this for a publisher who re-exports or runs `arrange` between a
fetcher reading the manifest and fetching what it names. Incremental export
makes that the ordinary case rather than the accident, so it is worth saying
what the window actually holds.

During an addition-only run, every path the old manifest names is still where
it was — files are added and nothing moves — so a fetcher mid-flight is
working from a subset and never misses. During a run that withdraws, the paths
withdrawn 404, and the answer is 0048's: refetch the manifest, and a digest
gone from the new one was forgotten or pruned at the source, which is an
answer and not an error. Writing the manifest last is what keeps the two
cases in that order.

Nothing here asks the publisher to hold still, take a lock, or know that
anybody is reading, which is the property that keeps a static file server
sufficient.

## Why not keep the copy current with `receive`

It is the obvious answer and it leaks. An export is a store, `receive` is
built to bring one store up to another, and running it inside the published
copy would be one command instead of a new mode for `export`.

It would also union the rules, because that is what 0051 decided `receive`
does, deliberately, on the grounds that whoever can run a receive already
holds the whole history and every payload — the maximal disclosure the format
has, against which a rule's text is nothing. That reasoning is sound and it is
exactly wrong here: the party running this receive is the publisher, and the
party reading the result is the public. Every `private` rule would land in the
copy on the first sync, and the export filter would have protected the copy
only until somebody kept it up to date.

So the incremental publish cannot be receive's union. It has to be export's
filter, run again — which is this decision, and the reason it is one decision
rather than a note on 0048.

## What this settles in 0048

- **`skipped/` is listed.** 0048 withheld it citing 0042's clause about rules
  being the exporter's, which 0051 superseded. The export's `skipped/` holds
  shared rules and nothing else, so listing it is safe by construction rather
  than by policy, and a fetched replica stops being the one copy whose first
  `record` offers to record the recipient's build output.

- **`names/` and `cache/` are not listed because an export has neither.** The
  clause stops being a rule about what a fetcher declines to take and becomes
  an observation about what is there.

- **The heads line is not a currency check.** A forgetting document changes
  the set without moving a head — that is its design — so equal heads cannot
  mean equal content, and a fetcher that stopped there would be the one path a
  redaction never travels. The manifest is one request and its head lines are
  inside it, so nothing is saved by reading them first. They earn their place
  answering relatedness, and 0048's sentence about finding out in one request
  should go.

- **Relatedness from a manifest is stricter than 0029's, and this is where it
  shows.** `related` has three arms; two are answerable from a listing of
  digests, and the third — *their* revision naming a parent or supersession
  *we* hold — needs their revision documents, which the manifest deliberately
  omits. An export is precisely the store that has dangling `supersedes`
  edges, by `export`'s own module documentation, so the unanswerable arm is
  not hypothetical. It fails toward refusal rather than a wrong join, and
  `--join-unrelated` is the escape. Say so rather than implying the listing
  answers 0029.

## Rejected alternatives

**The manifest inside the copy.** At the copy's `history/`, which 0048 refused
for the live store and which is no better here: `check` would need to tolerate
a name it does not own, and anybody who took a `cp -r` of the published copy
would be recording into a store with a stale enumeration in it. At the copy's
*root* instead, beside the folder's files, and it is an untracked file in the
working directory of every recipient — visible in `status`, one careless
`record` away from being in a history forever. Beside the copy, it is nobody's
file and can be deleted without a thought.

**A fixed name for the exported directory.** `<root>/store/`, so a fetcher
could be handed the root rather than the manifest. It buys a shorter URL and
costs a publisher the ability to serve two exports, a signature, or an index
page from one root. Deriving the prefix from the directory `offer` was pointed
at gets the same convenience without the constraint.

**Rebuilding the copy from scratch each publish.** Correct, trivially, and
O(store) per publish on a timer. Hardlinking the immutable files the way `git
clone --local` does would take most of that back, but it makes the publish a
whole-store operation whose cost grows with history for a change that is
usually three files — and it would rename things, breaking fetches in flight
for no reason.

**Publishing only the transferable set — no folder, no `historica.txt`.** The
manifest already enumerates exactly what a fetch takes, so the folder half is
bytes the server holds and nobody downloads. But the folder is what makes the
published root browsable, which is the property the top row of
`comparison.md` claims, and `wget -r` of an export is a working repository —
the thing 0042 said no directory on disk was. The doubling is the publisher's
disk, not anybody's bandwidth.

## Consequences

- `export_onto` grows a second entry: the plan is the same, the writing
  branches on what the copy already holds, and `Occupied` narrows to the cases
  that are genuinely not this store's copy. `Exported` grows counts for what
  was withdrawn and what was destroyed, beside 0051's carried and withheld.
- The diff needs the copy opened as a store, which reads `revisions/` in full
  and walks `operations/` — O(copy), local, and exactly what `receive` already
  pays on the receiving side.
- `offer` takes a directory and writes paths under that directory's name. Run
  in the copy rather than the origin, it needs nothing from the origin at all,
  which is what makes the manifest a rendering of the published artifact
  rather than a claim about a store somewhere else.
- The published copy's readable names drift from what a fresh export would
  produce, because collisions are resolved against a set that grew over time.
  Nothing reads them but a fetcher, which discards them.

## Deferred

1. **Signing the manifest.** Four fields and a header is a small thing to
   sign, and 0046 has the vocabulary. The reason it is not here is that a
   signed manifest is only worth what the fetcher does when it fails to
   verify, and that is a policy question this decision would have to invent an
   answer to.
2. **`export --update` as a distinct verb.** Whether the in-place case should
   announce itself in the command line rather than in the destination's
   contents. It is a question about what a person expects to be safe to type,
   and it can be settled when somebody has typed it.
3. **Publishing several targets from one root.** Two exports and two
   manifests, or one manifest naming two stores. Deferred exactly as far as
   0048 deferred narrowing, and for the same reason: nobody has published
   twice yet.
