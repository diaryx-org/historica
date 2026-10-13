---
title: A listing ending in a carriage return
description: A manifest, tip or page whose unterminated last line ends in `\r` reads a path holding the `\r`, and writes it back as a line that reads without it — choose whether a listing tolerates CRLF on every line or refuses a carriage return
status: open
created: 2026-10-13
updated: 2026-10-13
part_of: '[Tasks](/docs/tasks/tasks.md)'
---

# A listing ending in a carriage return

Found by `tests/strict.rs`, whose `a_listing_reads_back_as_itself` holds
the four listing readers in `src/store/offer.rs` to the promise a listing
makes in place of byte equality: what one reads, written and read again, is
what it read. Every reader there splits with `str::lines`, which takes `\n`
and `\r\n` as terminators and leaves a lone `\r` alone. So a carriage return
before a newline is a line ending, and a carriage return at the end of a
file with no final newline is part of the last field — for a `page` line or
an entry, the path.

## Repro

```rust
use historica::store::Tip;

let digest = "1e4e224e93380a25d4cd1be85d35db37f4064be4388822eba250894c6d6daa0d";
let text = format!("historica-offer-2\npage {digest} p\r");
let tip = Tip::parse(&text).unwrap();          // the page's path is "p\r"
assert_eq!(Tip::parse(&tip.to_string()), Ok(tip)); // fails: it reads back as "p"
```

`Offer::parse` and `Page::parse` do the same with
`historica-offer-1\nrevision {digest} - p\r`, and `Manifest::parse` with
either. First found as `BOLERO_RANDOM_SEED=297822725993281124753952336594166403111`
against an earlier engine; the bytes above are the whole of it, and
`a_listing_ending_in_a_carriage_return_reads_back_as_itself` in
`tests/strict.rs` pins them, ignored until this is done. The live target
skips text ending in `\r` until then.

## What it costs

Little, and nothing wrong reaches a store. A manifest saved with CRLF line
endings and no final newline asks for its last file at an address with a
carriage return on the end; the request fails or fetches bytes that do not
hash to the line's digest, and decision 0048 already refuses those. What it
breaks is the reader's own consistency: one spelling of a line ending is
honoured everywhere but the last line.

## The choice

[0048](/docs/decisions/0048-asking-for-what-is-missing.md),
[0056](/docs/decisions/0056-listing-what-it-cannot-read.md) and
[0080](/docs/decisions/0080-a-listing-in-pages.md) say nothing about line
endings; the tolerance of `\r\n` is `str::lines`'s, not a decision's. Either:

- **Tolerate it everywhere.** Strip one `\r` from the end of every line,
  the last included. A path can then never end in `\r`, which no publisher
  writes — `check_path` refuses a control character in every tracked path
  and in every bookmark's name.
- **Refuse it.** Split on `\n` alone, as decision 0004 has the documents do
  and as the cache readers do, so a CRLF manifest is refused at its header
  and the fetcher falls back to the archive. Stricter, and a change for
  anyone serving a hand-edited manifest today.

## Done when

The choice is made and written down where 0048's grammar is, the four
readers agree with it, and the ignored test runs.
