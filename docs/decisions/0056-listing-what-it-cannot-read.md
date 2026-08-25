# 0056 — Listing what it cannot read

0053 deferred one thing to a later decision, by name:

> **Claims in an offer.** 0048's listing has three kinds — `revision`,
> `operation`, `payload` — and a travelling reserved directory would be a
> fourth, which is a grammar change to the manifest and a policy for a fetcher
> that meets a kind it does not know. Nobody has published a store with claims
> in it. When somebody has, that is the decision.

Somebody has. 0052 made publishing a thing done repeatedly onto one directory,
and every one of those runs carries `claims/` into the copy — so the first
manifest written against a published export is a manifest with files in the
copy it does not name. A fetcher working from it builds a replica that nothing
vouches for, silently, which is the failure mode 0053 already described for an
older historica exporting a store with claims in it: quiet here, loud in the
tool.

There is a second arrival in the same set, and 0053 had no reason to mention
it. 0052 settled that `skipped/` is listed, reversing 0048 — and 0048's three
kinds have no word for a rule file either. Two additions, then, and what makes
them one decision rather than two notes is that the line between them is a line
this project has already drawn once. 0053 drew it through `export`, refusing to
filter `claims/` and pointing at `skipped/`, which `export` genuinely does
filter:

> A filter is available for a directory historica reads. It is not available
> for one it has promised not to.

The manifest's kinds fall on either side of that sentence.

## The decision

- **`rule` names one file of `skipped/`.** Historica owns that grammar,
  `check` answers for it, and 0051 gave a rule an axis saying whether it
  travels. So the kind is its own, and the listing states the shared rules and
  nothing else under that directory — not the private ones, and not the note
  `init` leaves, which states no rule and so states nothing a recipient needs.

- **`reserved` names one file historica carries and cannot read: a file of a
  reserved directory whose class is `travels-and-unions`.** One word, however
  many directories are ever reserved. It says what the file *is to historica*
  rather than whose it is, which is 0053's rule for transport reaching the
  grammar transport writes.

- **The path is the address, and it is enough to file the bytes by.** A
  manifest's paths resolve against the manifest's own directory (0052), so a
  `reserved` line names the exported directory, `history/`, the reserved
  directory, and the file's own name under it. A fetcher subtracts the first
  two — it constructed the URL, and `history/` is the one directory name this
  format fixes — and what is left is the path the file takes inside a store,
  which is the path it already had at the origin. That is what makes the
  directory union wherever it lands: 0053 keeps the names because two stores
  holding one name hold one file.

- **A fetcher asks its own registry about that directory, and never the
  manifest.** The kind says the publisher's historica thought this travelled.
  Whether it travels *into here* is a question about the receiver, and 0053
  answers it: `travels-and-unions` is written add-only with `create_new`, and
  anything else — `local-only`, `derived`, or a name this receiver has never
  heard of — is not written at all. So a manifest cannot talk a store into
  filling a directory it does not know, which is the property that makes one
  generic word safe where a word per directory would not have been.

- **The fourth column is `-` for both.** A rule file's grammar has no key that
  destroys anything, and a `reserved` file is one nothing here has read — 0054
  deferred a recorded revocation to the reserving tool, and a tool's revocation
  file travels and unions like every other file in the directory, which is to
  say it arrives as an ordinary `reserved` line and means something only to the
  tool that can read it.

- **A kind a reader does not know is a line it discards, not a manifest it
  refuses.** The set has grown once and may grow again, and the header carries
  a number for the case where it grows incompatibly instead. Discarding a line
  costs a file the fetcher does not take, which is the recoverable way to be
  wrong about a file nobody described.

- **The order of the lines is part of the format.** Heads in digest order;
  then payloads, then documents, then revisions, then rules, then the files of
  another tool; and within each group, the path's order. Two things want it. A
  publisher regenerating a manifest on a timer should write one set of bytes
  for one copy, so that a copy nothing changed produces a file nothing changed.
  And the groups are 0048's fetch order, so a fetcher working from the top
  understates what is reachable at every moment rather than leaving a revision
  naming bytes that never arrived. Rules and reserved files come last because
  they sit outside that invariant entirely: no revision names them.

## Why one word rather than one per directory

`claim` would read better in the file, and it is the wrong answer for the
reason 0053 spent a decision on. A word per reservation is a table of per-tool
special cases, relocated from `export` into the grammar — the registry would
grow a token beside its class, every reader would need the whole table to parse
a line, and the second tool to reserve a directory would arrive as a change to
the manifest format rather than as a line in a table and a decision document.
The thing 0053 exists to establish would be gone, and gone from the one artifact
that crosses between two historicas of different ages.

It also answers the half of the deferral that was about policy. 0053 worried
about "a fetcher that meets a kind it does not know", and a per-directory word
makes that the ordinary case: a fetcher one release behind meets `claim`,
`witness`, `attest`, and has to decide what to do about each. With one word it
never happens for a reserved directory at all — the kind is stable, and the
thing that varies is the directory name in the path, which the fetcher was
always going to have to look up in its own registry before writing anything.
The unknown moves from a token with no meaning to a directory with a known
default, and 0053 already fixed that default at `local-only`: leave it behind.

The cost is that a manifest does not say *which* reserved directory a file
belongs to in its first field. It says it in the path, which is the field that
had to carry it anyway.

## Why the rules are filtered rather than trusted

0052 justified listing `skipped/` by a property of exports: an export's
`skipped/` holds shared rules and nothing else, "so listing it is safe by
construction rather than by policy". That is true, and it is a fact about how
the directory got there rather than about the command doing the listing.
`historica offer` is pointed at a directory. It can be pointed at a live store
— a person will, to see what a publish would say — and a live store's
`skipped/` holds the `private` rules 0051 wrote the key for.

Listing one would disclose it. 0045 derives a rule file's name from the rule,
and 0052's own argument against publishing the store turns on exactly that:
`target.txt` and `clients.txt` are guessable rather than hash-obscured, and
0051 made the text of a `private` rule the disclosure it is about. A manifest
naming `history/skipped/clients/acme-layoffs/all.txt` has published the rule
without publishing the file.

So the filter is applied here rather than assumed upstream. It costs nothing —
`export` already parts the two, and the axis is read from a grammar historica
owns — and it makes the listing safe wherever it is pointed rather than only
where 0052 pointed it. Where it is pointed at an export the set is identical,
which is the test a narrowing rule should pass.

## Rejected alternatives

**No kind at all for reserved files: leave them out of the manifest.** The
status quo, and it publishes a copy nothing vouches for while the origin
believes it published one that does. 0053 already priced the same silence for
an older historica and called the recovery a re-export; here there is no
re-export to do, because the files *are* in the copy and only the listing
omits them.

**A per-directory kind — `claim`, and a token per reservation.** Above.

**Listing every file under `skipped/` and letting the export be the filter.**
0052's sentence taken literally. It is correct for the artifact 0052 describes
and wrong for a command that takes a directory, and the difference costs a
disclosure rather than a wasted request.

**Folding rules in with `reserved`, on the grounds that both are "not
content".** It would put a file historica reads, owns, and reports on in
`check` into the class defined by not being read, and a fetcher would then have
to consult its travel registry about `skipped/` — a directory that is not in
the registry and is `local-only` by default, which would mean the rules never
travel. The kinds are not a tidy-up; each one tells the reader which machinery
applies.

**A `directory` field beside the kind, so a reserved line says `reserved
claims …`.** Five fields, and the fifth restates a prefix of the fourth. The
path already carries it, and 0043's trailing-path convention only survives
while the path is genuinely last.

## Consequences

- `store::offer` is the module, `Store::offer` takes the prefix a manifest's
  paths resolve against, and `historica offer <dir>` supplies the name of the
  directory it was pointed at. Nothing is written anywhere; standard output is
  the whole of it, so that `historica offer store > offer.txt` is the publish.
- `OfferKind` is public and `#[non_exhaustive]`, which is the type-level form
  of the rule that an unknown kind is a discarded line.
- 0048's deferred measurement is settled in the implementation rather than
  here, because it is what 0048 called it: a measurement. `operations/` goes
  through 0036's catalogue, taken one entry per *file* rather than one per
  digest, since the catalogue is keyed by digest and collapses two files
  holding one set of bytes — harmless for a lookup, wrong for a listing whose
  paths are addresses. `revisions/` is walked and hashed, because a revision
  document is small, there is one per revision rather than one per file per
  revision, and a second index in `cache/` would be a second thing that can be
  stale.
- `names/` and `cache/` are not walked at all, so a listing of a live store
  costs nothing for the directories it does not name.
- No `check` is run. A manifest describes what a directory holds rather than
  vouching for it; `export` is the command that leaves the copy consistent, and
  a fetcher hashes every arriving file regardless.

## Deferred

**A kind for a class that is not `travels-and-unions`.** There is one class
that crosses a boundary, so there is one word. A second travelling class —
0054's `travels-and-mirrors`, if a tool ever wants it — would need a second
word, because a fetcher that had to *withdraw* on the strength of a manifest is
doing something no line here asks of it.

**What a fetcher does with a `reserved` line for a directory it reserves under
a different class.** The answer is 0053's default, applied: do not write it.
What is not decided is whether that should be said out loud — a fetch that
quietly declines a file the publisher meant to send is the sort of silence
0053 was uneasy about elsewhere — and it is a question about `fetch`'s output,
which is not built.

**Signing the manifest.** 0052 deferred it and nothing here changes the
arithmetic: two more kinds is still a small thing to sign, and what a fetcher
does when the signature fails is still a policy nobody has needed to invent.
