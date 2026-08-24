# 0048 — Asking for what is missing

0042 built the sending half and deferred the incremental one:

> The digest set of the transferable files, computable on both ends; the
> difference is the shipment, which is the whole of want/have with no
> session.

That sentence is the right instinct with the wrong object. A fetcher does
not need to be told its own half of the set — it holds a store, and
enumerating a store is what `Store::open` does before it does anything else.
What it cannot do is enumerate *the other one*. `cp -r`, rsync and a mounted
disk all hand a reader a directory it can list, and every one of 0029's
rules is written against a source that can be walked. A URL cannot be
walked. There is no `entries()` over HTTP, no listing a static file server
is obliged to serve, and no way to guess: 0003 made filenames presentation,
0019 made the readable names the default, and 0041 put a month directory in
front of them, so the path a document sits at is a thing the publisher chose
and a stranger cannot compute. `arrange` exists to change it.

So the missing thing is not a set difference. It is a directory listing, for
a directory that has no way to say what it holds.

Once a reader has that listing, everything else is already solved and has
been since 0003. Every file under it is immutable and named by the digest of
its bytes, so a fetcher can ask for exactly the ones it lacks, verify each
one on arrival, and stop. No session, no negotiation, no state at either
end, and nothing on the server but files.

## The decision

- **`historica offer` prints a listing of the transferable files.** To
  standard output, where the publisher redirects it — conventionally to
  `offer.txt` beside the store. It is a rendering, the same standing `log`
  and `status` have, and not a file the store holds: an enumeration written
  into `history/` would be derived mutable state going stale beside the
  thing it describes, which is what 0030 refused and what 0042 leaned on
  when it refused to write a position.

- **A line is `<kind> <digest> <forgets|-> <path>`, and the path is last.**
  0043's reason: a path is the one field that may hold a space, so it ends
  the line and nothing needs escaping. The kinds are `revision`,
  `operation` and `payload`, which is what `receive` already sorts the world
  into. Above the lines, a `head` line for each head the store has, and
  above those a header, `historica-offer-1`.

- **Four fields, and each is load-bearing.** The **digest** is identity, and
  the fetcher hashes every arriving file against it before believing
  anything, which is 0036's rule one level out: *the catalogue says where to
  look, it never says what is there*. The **path** is an address the fetcher
  could not otherwise construct. **What an entry forgets** is 0014
  travelling — a fetcher that took a plain set difference would keep an
  original that an arriving forgetting document destroys, so the offer
  states the relationship exactly as a catalogue entry already does. The
  **heads** let a fetcher that is current find out in one request, which for
  a pull run on a timer is the whole common case.

- **It is text, not JSON.** 0042 guessed JSON because the reader is a
  program. So is the reader of every document this format has, and they are
  all line-oriented text on purpose. JSON would be the only JSON in the
  repository, would need an escaping story the trailing-path convention
  already settles, and would buy nothing over a split on whitespace.

- **The header is numbered, unlike a document's.** 0047 retired the numbers
  from the preamble because a document is permanent and a store's grammar is
  a promise. An offer is neither: it is refetchable, and a reader that meets
  a spelling it does not know falls back to fetching the archive, which
  never stopped working. That is the same standing `historica-working-1` has
  in 0043 — a fixed name has nothing to check it against, so it says what it
  is and a stranger discards it whole.

- **`historica fetch <url>` is the other half, and the convention is one
  sentence: `offer.txt` at a root, and every path it names resolves relative
  to that root.** Nothing else. No ranges, no packs, no index, no content
  negotiation — nothing a directory of files behind a plain web server does
  not already do. A static file server was already a Historica host under
  0042; this is what makes it one for the second sync as well as the first.

- **The transport is the binary's, through a one-method source.** The
  library takes something that answers `get(path) -> bytes` and does the
  whole of the algorithm; the binary brings the TLS, the redirects and the
  proxy settings. 0025's shape, applied a second time, and for 0006's
  reason: the library does it, the binary renders it. It also keeps `curl`
  an honest implementation of the trait, and makes a local directory the
  test fixture rather than a special case.

- **Content first, revisions last, exactly as `receive` orders it.**
  Payloads, then operation and forgetting documents, then revisions. An
  interruption understates what is reachable rather than leaving a revision
  naming bytes that never arrived, and what is left unreachable is `prune`'s
  to collect.

- **A fetched path is an address, not a name.** Bytes land under the
  receiving store's own digest-derived names, which is what `receive`
  already does with an arranged source, and `arrange` gives them readable
  ones afterwards. So the offer's paths are used to ask and then discarded,
  and no two stores ever have to agree about a filename — which is just as
  well, since a store and a partial copy of it genuinely cannot: 0041's
  collision suffix is computed over the set a store holds, so an export
  already names a document differently from its origin where two share a
  base.

- **Relatedness is read from the offer.** Does it name a revision this store
  holds, or expose a parent or supersession edge across the boundary — the
  same question 0029 asks, answered from the listing instead of from an
  opened store, with the same refusal and the same `--join-unrelated`. An
  empty store may always be seeded.

- **The folder is untouched.** `fetch` adds history and stops, and `update`
  is the folder's catch-up as it has been since 0030. Two commands, because
  a fetch that moved a person's files under them is a different operation
  than the one they asked for.

## The check that cannot be run

0029's strictest rule is that both stores must pass `check` before either
one is used as an instruction, and `receive_plan` enforces it by running
`check_on` against the source. That rule cannot survive a URL. Checking a
store means reading every file in it, so a `fetch` that honoured it would
download the whole store in order to work out which parts it did not need to
download. The operation would be its own defeat.

What replaces it has to be said plainly rather than assumed:

- **Nothing enters the store unverified.** Every fetched file is hashed
  before it is written, against the digest the offer gave and the name it
  will be stored under. A lying offer costs a wasted request and cannot
  produce a wrong store — the property 0036 already relies on when it
  believes a catalogue it cannot trust.
- **The fetched set is closed.** A fetch takes an ancestry-closed set, so
  the store is a complete store again when the fetch finishes, never a
  store holding a revision whose parents are somewhere else.
- **The receiver checks itself, before and after.** A store `check` calls
  broken does not fetch, for `export` and `prune`'s reason: a copy of a
  fault is two faults. And the store is checked when the fetch completes,
  which is where a contradiction the remote was harbouring becomes this
  store's problem — visibly, at a moment, rather than silently.

What is genuinely lost is the source's *internal* consistency: a remote can
publish an offer for a store whose documents contradict each other, and this
fetcher will discover it at the end rather than refuse at the start. That is
the price of not reading the whole thing, it is paid in a `check` failure
rather than in corruption, and it is the honest reason `receive` against a
local directory remains the stricter operation.

## What staleness costs

The offer is read at one moment and the files fetched after it. A publisher
who re-exports, runs `arrange`, or prunes in between moves or removes the
paths the fetcher is still working through, and the requests 404.

That is ordinary, and the answer is to refetch the offer and retry what is
missing, bounded. A digest that is gone from the new offer was forgotten or
pruned at the source, which is an answer and not an error — the fetcher
stops wanting it. Nothing here needs the publisher to hold still, hold a
lock, or know that anybody is reading, which is the property that keeps a
static file server sufficient.

## Rejected alternatives

**An offer inside the store.** A file at `history/offer.txt`, written by
`export` and updated by every writer. It would be the only file in the store
whose correctness depended on being rewritten, `check` would need a finding
for it being stale, and every command that wrote a document would have to
remember to. The listing is derived; deriving it on demand costs a walk the
store already performs.

**A `Filesystem` over HTTP, so `receive` works unchanged.** Tempting, and
wrong at exactly one method: `entries` is unanswerable, and it is the method
the whole operation turns on. An implementation that answered it by parsing
an offer would be an offer with a directory-shaped hole cut in it, and would
still drag in `check_on` reading the entire remote store. Better to have the
fetch state what it is.

**A DAG in the offer.** Parent edges per revision, so a fetcher could plan a
narrowed fetch without reading anything. A whole-store mirror needs no
parents — the offer's set *is* the target set — and a narrowed fetch can
learn them from the revision documents as they arrive, since those are the
small files and it is fetching them anyway. Keeping the edges out is what
keeps this a listing rather than an index, and an index is a thing that can
disagree with the store.

**Making `fetch` the way to get a first copy.** A thousand requests against
one `tar czf`, to arrive at the same bytes. `export` and an archive remain
the clone; `fetch` is the pull, and it earns its keep from the second sync
onward, when the difference is small and the archive is not. 0042 said clone
and pull were one design all along, and this is the sentence's other end.

**Range requests, packs, or any bulk encoding.** Every one of them is a
thing the server has to do, and the premise is a server that does nothing.

## Consequences

- `store::offer` is the new module: the listing, its format, and the walk
  that produces it. Most of the walk exists — 0036's catalogue already holds
  a digest and a forgetting relationship per file under `operations/`, which
  is the larger half of the listing, already reconciled and already local.
- `revisions/` has no catalogue, and 0036 deferred one waiting on something
  that wanted it. This is that thing. Either the catalogue extends to
  `revisions/` or `offer` walks and hashes it — the smaller directory, read
  in full at open regardless — and the choice is a measurement, not a
  design.
- `Store` gains the fetch: a source trait with one method, the difference
  against its own contents, the ordered requests, and the verification. It
  writes through its own `Filesystem` and never through a second one, which
  is where this differs in shape from both `receive` and `export`.
- `historica.txt` and `format.txt` are not listed and not fetched. A fetcher
  has a store already, with its own; a store that did not would have nothing
  to fetch into.
- `names/`, `skipped/` and `cache/` are not listed, for 0042's reasons
  unchanged: bookmarks and rules are the publisher's, and a cache is
  nobody's.
- A fetch from a divergent remote is a fetch, not a refusal. Divergence is a
  thing this store holds and `merge` resolves; only `update` and `cat` need
  one answer.

## Deferred

1. **Narrowing a fetch to one revision's ancestry.** `fetch --at`, which is
   where the parent walk becomes necessary and where 0042's fourth deferred
   item — narrowing by path — would meet it.
2. **Bookmarks.** 0042 deferred them behind a union rule 0029 wanted and did
   not have. 0045 supplied one for rules and not for names, so this is
   unchanged and belongs to whichever decision finally states what two
   replicas' bookmarks mean together.
3. **Publishing an offer as part of `export`.** Writing `offer.txt` beside
   the directory rather than into it, as a convenience. It is a shell
   redirect, and the convenience is worth having only once somebody has
   published twice.
4. **Authentication, and anything that follows from it.** A private host,
   credentials, or a fetch that is refused. The premise here is a public
   directory of files, and everything else is a transport question the
   binary's source trait is the place to answer.
