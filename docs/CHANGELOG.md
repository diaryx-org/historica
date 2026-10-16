# Changelog

All notable changes to historica-remark are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the versions
follow [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## Unreleased

<!-- git-cliff:begin — generated; edits here are overwritten -->

_No commits since the last tag._

<!-- git-cliff:end -->

## v0.6.0 — 2026-10-16

### Breaking

- **deps** — move to fig 7, which is pure Rust and needs no Zig ([`1d8a413`](https://github.com/diaryx-org/historica-remark/commit/1d8a41388aa34155fdd2452ef78a5b06566acfe3))

### Fixed

- **xtask** — send the release commands that left xtask to `release`, not `dx` ([`e96ebd6`](https://github.com/diaryx-org/historica-remark/commit/e96ebd6ee25294fa00341a36de4b0eed511bd190))
- **ci** — restore the cache, and Zig, for a job whose runner leaves out builds ([`10fcc48`](https://github.com/diaryx-org/historica-remark/commit/10fcc489dad4236a76b88a8f3f7befbd429cfb84))

### Behavioural changes

- historica-remark now requires `fig = "7"`. A consumer
still on fig 5 or 6 has two copies of fig, and `Remark::meta` and the
`Fields` impl are for fig 7's `fig::Value`, not the consumer's; move the
consumer's own pin to 7 alongside. The text of `Error::Metadata` is fig
7's account of a malformed block, which may word a parse error
differently from fig 5's.


## v0.5.0 — 2026-10-03

### Breaking

- **annotation** — an `assessing` motivation ([`ec271a4`](https://github.com/diaryx-org/historica-remark/commit/ec271a4ce033e304fd100799a0c3a723b188a7a4))

### Behavioural changes

- `Reader::read` and `Reader::document` now read a document whose `motivation` is `assessing`, which before this commit was an unknown motivation and `Error::Unreadable`.

- `Motivation::ALL` and `Motivation::terms()` include `assessing`, so a store that declares the motivation vocabulary from `terms()` now declares seven terms; one that declared six and validates against them refuses an assessment until it re-declares.


## v0.4.0 — 2026-09-28

### Breaking

- **deps** — move to fig 5 ([`fb6000c`](https://github.com/diaryx-org/historica-remark/commit/fb6000c2ad2250a57d4bbd4ff82203f8715d56f1))

### Fixed

- **annotation** — step between candidate matches by a character, not a byte ([`ecc4189`](https://github.com/diaryx-org/historica-remark/commit/ecc4189e8c5e2c8e732dc5c35cf050e4defc4aab))

### Behavioural changes

- `anchor` no longer panics on a selector whose `exact`
begins with a multibyte character when the text holds more than one
occurrence; it returns the best-scored one as for any other quote.

- historica-remark now requires `fig = "5"`. A consumer
still pinned to fig 4.x resolves two copies of fig — refused outright,
since fig-sys links the one native library — and `document::split`'s


## v0.3.0 — 2026-09-15

### Breaking

- **annotation** — an `editing` motivation, a `replacement` field, and `apply` ([`69af858`](https://github.com/diaryx-org/historica-remark/commit/69af858aea65f65007ed60032110572836c6c26c))

### Behavioural changes

- `Reader::read` and `Reader::document` now return

- `Motivation::ALL` and `Motivation::terms()` include
`editing`, so a store that declares the motivation vocabulary from
`terms()` now declares six terms; a store that declared five earlier
and validates against them will refuse an edit until it re-declares.

- `Annotation::fields()` and `FIELDS` include
`replacement`, written only when set.


## v0.2.0 — 2026-09-14

### Breaking

- **deps** — move to fig 4 ([`ae774a3`](https://github.com/diaryx-org/historica-remark/commit/ae774a3bf7366fbdb315d913b180846a1a140754))

### Behavioural changes

- historica-remark now requires `fig = "4"`. A consumer
still pinned to fig 3.x resolves two copies of fig — refused outright,
since fig-sys links the one native library — and `document::split`'s


## v0.1.1 — 2026-09-03

### Fixed

- **layer** — count the revisions a fetch names, now that it names them ([`94e2a60`](https://github.com/diaryx-org/historica-remark/commit/94e2a6004d147aa64e52d9c63095524828983c22))

## v0.1.0 — 2026-09-02

### Added

- remarks on a historica chain, and the layer that carries them ([`a0f495b`](https://github.com/diaryx-org/historica-remark/commit/a0f495b5f008435f7303e15e11cde3f240f5e1ca))

