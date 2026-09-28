# 0080 — A listing in pages

[0048](0048-asking-for-what-is-missing.md) made the manifest one whole
listing: a header, the heads, and a line for every transferable file.
[0056](0056-listing-what-it-cannot-read.md) chose that shape on purpose. A
listing is a rendering, written nowhere in the store, refetchable, and one
request. It is also linear in the store. A line is about 140 bytes, one per
file the copy holds, so every fetch reads the whole history to learn about
its last few files.

[An export restates its indexes whole](../tasks/closed/an-export-restates-its-indexes-whole.md)
measured it. It published a store at 40 and at 400 revisions, added one
17-byte file, exported onto the same copy and listed it again. The listing a
fetcher that was current then read was 12.7 KB and 120 KB. The change was a
revision and one content file. [0078](0078-where-a-cache-is-kept.md) had
already taken the two catalogues out of the copy. The listing was what was
left.

A store synced often, in small increments, is the case
[0052](0052-the-copy-a-stranger-fetches-from.md)'s copy updated in place was
built for. It is also the case where the listing costs the most, since it is
read whole on every pull.

## The decision

- **`historica offer <dir> --into <file>` keeps a paged manifest at that
  file**, beside the copy, where `offer.txt` already sat. Without `--into`,
  `offer` prints the whole listing as before and writes nothing, so a
  publisher who redirects it changes nothing by upgrading.

- **The manifest names the heads and the pages, not the files.**

  ```text
  historica-offer-2
  head <digest>
  page <digest> <path>
  ```

  The first page is the **base**, which lists the whole copy as it stood when
  it was written. Each page after it is what one publish changed. A page's
  path resolves against the manifest's own directory, as every path in a
  manifest does. Pages are kept in a directory named after the manifest,
  `offer-pages/` beside `offer.txt`, and each is named by the digest of its
  bytes.

- **A page is a whole listing's lines, and `gone` before the ones it
  withdraws.**

  ```text
  historica-offer-page-1
  <kind> <digest> <forgets|-> <path>
  gone <kind> <digest> <forgets|-> <path>
  ```

  An entry line means what it always meant. A `gone` line is a line the pages
  before stated and this listing does not: a file withdrawn. A `forget`, a
  `prune`, a target moving off a branch and a bookmark moving each reach a
  page as a withdrawal, some with an addition beside it. So a withdrawal needs
  no fresh base, and 0052's rule holds that the heads are not a currency
  check. A forget adds a stand-in whose fourth field names what it forgets,
  in a page, exactly as it would in a whole listing. Unknown kinds are
  discarded, and the lines are in 0056's order, as they are in a whole
  listing.

- **Applied in order from nothing, the pages are the whole listing.** That is
  the invariant everything else rests on, and the tests check it after every
  publish.
  `Offer::composed` applies them, and what it gives is what `historica offer`
  prints for the same copy, byte for byte.

- **The publisher remembers what it listed last by reading it back.** A run
  reads the manifest at `--into` and the pages it names, hashes each against
  its digest, and composes them. Then:
  - if nothing changed, it writes nothing, and a copy nothing changed keeps a
    manifest nothing changed;
  - if something changed, it writes one page of the difference and a
    manifest naming it after the others;
  - it writes a fresh base, and a manifest naming it alone, instead of a page
    when there are already sixteen pages after the base, when the pages after
    it would outweigh it, or when there is no manifest it can read back
    whole.

  The page is written before the manifest, and a page is never rewritten, so
  a fetcher holding the old manifest finds every page it names. Pages the
  manifest no longer names are removed last. A fetcher still working from one
  is told nothing is there and reads the manifest again, which is 0048's
  answer to a publisher who moved on.

- **A fetcher remembers which pages it applied, in its cache.** After a fetch
  has taken everything and `check` has passed, the store records the base and
  the pages after it in the directory the host keeps its caches in (0078).
  The next fetch reads only the pages after those, where the manifest's
  pages still begin with them. Anything else reads every page: nothing
  remembered, no cache to remember in, or a fresh base. That composes to the
  whole listing and answers the same. A fetch that skipped pages does not ask
  the listing about relatedness, since the revisions both stores hold are in
  the pages it skipped, and it established relatedness when it applied them.

- **`historica-offer-2` is a new number, and a reader of `-1` refuses it.**
  That is 0048's reason for numbering the header. A fetch built before this
  is told to fetch the archive, which never stopped working. A fetch built
  after reads both.

## What it costs

In the same measurement, repeated as `cli/tests/publish.rs`, a publish of one
added file changes five files of the published directory at either length:
the revision, the content file, the folder's copy of the file, the manifest,
and one page. A fetcher that was current reads 698 bytes of listing at 40
revisions and 698 at 400, instead of 12.7 KB and 120 KB.

The manifest is bounded by the sixteen pages it can name and the heads. A
fetcher starting from nothing reads the base and up to sixteen pages, which
is at most the base's size again, by the rule that writes a fresh base once
the pages would outweigh it. A fetcher that keeps no cache pays that on every
pull. That is at most twice the base, and it is the price of not having
remembered anything.

## What this does not change

- **0048's rule that the store holds no listing.** The manifest and its pages
  are beside the copy, which is the publisher's directory, as the redirected
  listing was. Nothing is written into `history/`, and nothing in the store
  learns that anybody is reading.
- **What a fetch trusts.** Every page is hashed against the digest the
  manifest names before it is read, and every file against the digest its
  line names before it is written. A lying manifest or page costs requests
  and cannot produce a wrong store.
- **What travels.** A page lists what a whole listing would, filtered the
  same way. Private rules and private bookmarks are never named.

## Rejected alternatives

**Saying so and changing nothing** was the cheapest shape the task named,
and it helps nobody who has not read it. **A decision keeping the single
listing for 1.0** would have been honest and left the cost where it was, on
the case 0052 was built for.

**A run's small files batched into one object**, which the task also named,
takes the content of a one-file change from two objects to one. It leaves
the listing whole, and it makes a file a person could open into a file inside
a batch, which 0016 and 0021 promise against.

**A tip naming only the newest page, each page naming the one before.** A
current fetcher reads the tip and walks back until it meets a page it has
applied, so the manifest is one line at any length. But the fetcher cannot
know it has met one without remembering it, which is the memory this
decision keeps anyway. And a fresh base breaks the walk, since a page cannot
name a base written after it. Naming the pages in the manifest costs sixteen
lines and makes both questions a comparison.

**Remembering in the store, or at the publisher.** What a fetcher has applied
is one device's, and 0078 is where that is kept. The publisher remembers
nothing but the manifest it already wrote.

## Consequences

- `Manifest`, `Tip`, `Page`, `PageRef`, `Published`, `PAGED_HEADER` and
  `PAGE_HEADER` are public beside `Offer`. `Offer::composed` applies pages,
  and `Store::publish_offer` keeps a paged manifest.
- `Fetched` gains `pages`, the pages a fetch read.
- A fetch reads `historica-offer-1` and `historica-offer-2`. A test that used
  `-2` as the number a reader does not know now uses `-9`.
- The task *An export restates its indexes whole* is closed.
