# 0041 — Where a revision is filed

0019 made the readable names the ones a store is written with, and 0016 chose
their shape: `revisions/` holds `2026-08-20 File the photograph.rev.txt`, and
`operations/` holds a directory of the same name. Both are flat, and 0003
deferred the question of when flat stops working as its fifth question.

The measurement answered it. A store of a thousand revisions holds two
thousand files and a thousand directories in two flat listings, and a store
kept the way a journal is kept — one folder, years of entries — will pass ten
thousand without ever having been large. Nothing breaks: the loader reads
files and never their names, so depth and arrangement are already
presentation. What degrades is exactly the thing the readable names exist
for. A directory of five thousand entries is not a folder a person opens; it
is a listing a person scrolls, and every file browser, sync client, and
`ls` gets slower and less legible as it grows.

The names already begin with a date. This decision files them under it.

## The decision

- **The writer files a revision under its year and month.** A revision
  recorded at `2026-08-20T09:12:04-06:00` is written to
  `revisions/2026-08/2026-08-20 File the photograph.rev.txt`, and its
  operations directory to `operations/2026-08/2026-08-20 File the
  photograph/`. The filename itself is unchanged — it still carries the full
  date, so a file separated from its folder still says when it is from, and
  a name that would sort correctly flat still does.
- **The month is read from the timestamp as spelled.** The wall clock in the
  revision's own offset, exactly as the filename's date already is. It is in
  the document, so two replicas filing one history produce one set of paths
  — the determinism rule 0016 stated, untouched. No replica consults its own
  clock or zone for any part of a name.
- **`arrange` produces the same layout**, so a flat store — written by an
  older version, by another tool, or by hand — becomes a filed one by the
  command that already exists for exactly this. On a store this version
  wrote, it does nothing, which is `arrange`'s standing contract.
- **The loader is already correct and does not change.** It walks to any
  depth and reads files, never names. A flat store, a filed store, and a
  store a person rearranged by hand are the same store, and `check` has no
  opinion on any of them. Filing is not a lint, for 0016's reason: a name
  that differs is usually a person filing their own history.
- **Collisions keep their rule.** Two revisions composing one name in one
  month resolve by change ID and then by digest, never by a counter. The
  scope a collision is judged in becomes the month directory, which changes
  nothing about the rule — the suffix is content-derived, so it does not
  depend on what else is in the directory either way.
- **The catalogue is indifferent.** 0036 believes `cache/operations.txt`
  only while the path set it names is the path set the directory holds, at
  any depth. Filed paths are just longer strings in that set.

## Why year-month

A journal's natural unit is the month: big enough that a directory holds a
few dozen entries rather than three, small enough that a decade of history
is a hundred and twenty folders rather than one folder of thousands. A
directory per day would recreate the problem one level down — mostly-empty
folders in their thousands — and a directory per year gives back flat
listings in the hundreds for any store busy enough to need filing at all.

This is a default, not a commitment. The scheme is presentation, so another
one — per-year for sparse stores, per-day for relentless ones — is a future
`arrange` argument and a writer configuration, not a format change. What any
scheme must keep is the one hard rule: derived from the documents alone, so
every replica files alike.

## Rejected alternatives

**Sharding by digest prefix**, as git's objects directory does. Perfectly
uniform, perfectly unreadable. `revisions/2a/` is a name for a machine, and
the folder a person opens is the reason these names exist.

**A flat default with filing as an option.** The stores that need filing are
the ones that got large before anyone thought about it. A default has to be
the right answer for the store nobody is tending.

**Filing by change or by author.** Both are real facts, and both scatter
what a person actually looks for — "what happened in August" — across the
whole tree. Time is how a history is browsed.

## Consequences

- `naming` composes a `YYYY-MM/` prefix from the timestamp it already reads;
  `stems`, collision suffixes, and `SUMMARY_CHARS` arithmetic are otherwise
  untouched.
- The writer and `arrange` share the scheme through `naming`, as they
  already do, which is what keeps them agreeing.
- `arrange` on a formerly flat store moves every file one level down, once.
  Sync clients see that as the renames it is; identity comes from content,
  so no reference anywhere notices.
- `receive` is unaffected: it writes missing documents under digest-derived
  names and has never promised them a pretty place. A later `arrange` files
  them.

## Deferred

**Configurable schemes.** Named above as the future: per-year, per-day, or a
person's own, chosen in configuration and applied by the same two writers.
Deferred until a second scheme has a store that needs it.

**Filing `cache/`.** The catalogue bounds its own size and checkpoint
entries are bounded by `CACHE_AFTER`; neither directory is one a person
browses. If the cache directory ever grows past what a filesystem is happy
listing, it can shard by digest prefix precisely because nobody reads it.
