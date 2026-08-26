# Historica

Historica is an experiment in readable, convergent version control.

The repository format follows one non-negotiable rule:

> The readable files are the authority.

A person must be able to inspect the history, understand its relationships, and
recover stored content without decoding an opaque database or binary operation
log. Binary indexes and snapshots may eventually exist as disposable caches,
but deleting every cache must lose neither information nor meaning.

## What is here

A library and the command line built on it. Each module carries its own
argument in its rustdoc, and the choice behind it is written down in
[`docs/decisions/`](docs/decisions) rather than restated here.

| Module | What it is |
|---|---|
| `core` | immutable revisions naming their own digest, explicit parents and explicit supersession, so history is a Merkle DAG that merges by set union |
| `format` | the readable documents, parsed strictly enough that hashing the file is as trustworthy as hashing a canonical model |
| `tree` | the file set: files carry identifiers, paths hang off them, and there are no directories |
| `replay` | a file materialised from what was done to it, by arithmetic rather than interpretation |
| `merge` | concurrent branches merged by replaying the event graph, so nothing a merge needs is ever written down |
| `diff` | the writing half: what a revision did to a file, recorded from the folder as it stands |
| `record`, `working` | the writer, and the folder beside the store it is given |
| `fs` | persistence asked for rather than assumed, so a store can live somewhere `std::fs` cannot reach |
| `store` | the format as a folder a person can read, rearrange, and check with `shasum` |
| `conflict` | the view a person edits when two heads disagree |
| `update`, `naming` | the folder made to hold a head, and the filenames both the writer and `arrange` produce |

The binary decides nothing the library has not: every answer a command gives is
one a caller can ask for directly.

### Where to read further

- **Why any of it is the way it is.**
  [`docs/decisions/index.md`](docs/decisions/index.md) lists every decision
  with a paragraph on what it settled and why. They are the authority; anything
  else here is a convenience.
- **What the commands do, and why they are that shape.**
  [`docs/cli.md`](docs/cli.md). `historica help` is the authority on what each
  one takes.
- **The documents themselves.**
  [`src/store/format.txt`](src/store/format.txt) is written for a person
  reading a store without this tool, and is copied into every store `init`
  makes.
- **The specification, executed.** [`tests/corpus/`](tests/corpus) is
  hand-written files — real histories, and invalid ones each refused for one
  stated reason. Its [README](tests/corpus/README.md) is the map.
- **The API.** `cargo doc --open`.
- **How it differs from git and the rest.**
  [`comparison.md`](comparison.md), which several decisions argue against by
  name.

## Installing

historica is published to crates.io as two packages, because the two have
different appetites. The command line is
[`historica-cli`](https://crates.io/crates/historica-cli):

```console
cargo install historica-cli
```

The program it installs is called `historica`. The library is
[`historica`](https://crates.io/crates/historica) — `historica = "1.0"` in a
`Cargo.toml` — and it holds everything: the binary decides nothing the library
has not, so every answer the commands give is one a caller can ask for
directly.

They are separate packages for one reason, which is what a library caller would
otherwise pay. `historica fetch` rides on the platform's own HTTP stack by
decision 0057, and while that lived behind a default feature of one package,
anyone writing `historica = "1.0"` compiled and linked WinRT, NSURLSession or
libcurl in order to build code they had no way to call. A seam a caller has to
know about is not a seam. So the transport sits in the package that has the
command, and depending on the library costs a library.

Both build on stable Rust 1.88 or newer, which is the floor the `msrv` job
holds them to, and both are MIT or Apache-2.0 at the reader's choice:
[`LICENSE-MIT`](LICENSE-MIT) and [`LICENSE-APACHE`](LICENSE-APACHE).

### What 1.0 promises

Two things, and they are not the same promise.

The **format** promises what decision 0047 spells on line one. A document
headed `historica` parses under the grammar this version reads, and 0004's
rule holds inside it: a reader's vocabulary only ever grows, so a document
written today still parses. A format that cannot keep that takes a new
spelling — `historica-2` — rather than a number, and the pre-1.0 spellings
`historica-v0` through `historica-v5` are refused by name and never reused.
This is the promise that would be expensive to retract, which is why it is the
one 1.0 was cut for.

The **Rust API** promises ordinary semver, which before 1.0 it did not: a
change a caller would have to edit their own code for takes a 2.0, and the
smaller differences are written down as `Behavioural-change:` trailers, which
[`docs/CHANGELOG.md`](docs/CHANGELOG.md) collects under each release. That API
is also the whole of the plugin surface, by decision 0053: a tool built on
historica is an ordinary crate depending on it, and a fact the API does not
expose is a change to historica rather than a hole opened from outside.

Three things are outside both. `history/cache/` is disposable by decision 0003
and its contents are nobody's interface — deleting it changes how long a
command takes and nothing else. The exact wording a command prints is not an
API, though what it has to say is, since a person reads it and 0021 makes that
a design constraint. And `xtask` is this repository's CI rather than a
published thing, which is what `publish = false` says.

## The command line

```console
$ historica init .
made a store at /home/adam/journal/history
$ historica log
nwlxsqot  4cf00b8c  (head)
    Adam Harris <adam@example.com>  2025-08-21T22:05:00-06:00
    dropped 1
    Withdraw the entry, keeping what it taught

mzvwutkl  d56419e5
    Adam Harris <adam@example.com>  2025-08-20T08:14:33-06:00
    moved 1  edited 1
    File the README under docs, and say what it covers

kxryzmor  55874ae7
    Adam Harris <adam@example.com>  2025-08-19T09:02:40-06:00
    edited 1
    Say why a path is not an identity

qpvuntsm  f23cda95
    Adam Harris <adam@example.com>  2025-08-19T00:47:11-06:00
    added 2
    Start a journal
$ historica files nwlxsqot
docs/README.md  swtlmnkqvzyrxopwstlnmkqv
$ historica cat nwlxsqot docs/README.md
# Notes

A journal kept in Historica, and the notes that came with it.
$ historica name main nwlxsqot
main -> change nwlxsqotvkzmuprysltnwxqk
$ historica name readme nwlxsqot docs/README.md
readme -> file swtlmnkqvzyrxopwstlnmkqv
$ historica cat nwlxsqot file:readme
# Notes

A journal kept in Historica, and the notes that came with it.
$ ls history/revisions
2025-08
$ ls history/revisions/2025-08
'2025-08-19 Start a journal.rev.txt'
'2025-08-19 Say why a path is not an identity.rev.txt'
'2025-08-20 File the README under docs, and say what it covers.rev.txt'
'2025-08-21 Withdraw the entry, keeping what it taught.rev.txt'
$ historica arrange
/home/adam/journal/history/revisions: 0 renamed, 4 already arranged
$ historica check
/home/adam/journal/history: nothing to report
```

`historica help` lists every command and what it takes.
[`docs/cli.md`](docs/cli.md) is why each one is that shape — including what a
target may be, how a path is told apart from a file identifier, and why `check`
separates the faults that mean a store contradicts itself from the notes that
never fail.

## Decisions

Choices that constrain later work are written down as they are made.
[`docs/decisions/index.md`](docs/decisions/index.md) lists every one of them
with a paragraph on what it decided and why, and
[`docs/loro.md`](docs/loro.md) is the initial Loro evaluation and the
conditions that would reverse it.

## Development

CI is a program rather than a YAML file. Every job the workflow runs is one
entry in `xtask/src/main.rs`, and `cargo xtask ci` runs all of them locally, in
the same order, against the same commands:

```console
cargo xtask            # what the jobs are
cargo xtask ci         # all of them: fmt, clippy, test, msrv
cargo xtask clippy     # or one
```

Which is to say the underlying commands are still the underlying commands:

```console
cargo fmt --all --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test
```

The conformance suite searches randomly from a seed, and `cargo test` runs it
at a fixed one so that two runs are the same run. `cargo xtask test` rotates it
and echoes what it chose, so that CI looks somewhere new each time and a red run
can still be made red again:

```console
HISTORICA_CONFORMANCE_SEED=0x0007c04f0000f00d cargo test --test conformance
```

A failure prints that line for you, along with the failing round shrunk to the
fewest replicas and actions that still reproduce it.

The corpus checks with tools that are already installed, which is the claim the
format exists to make — every directory under `tests/corpus/` carries a
`MANIFEST`, and [its README](tests/corpus/README.md) says what each one pins:

```console
for d in tests/corpus/*/; do (cd "$d" && shasum -a 256 -c MANIFEST); done
```

### Releasing

A release is a tag, the GitHub release cut from it, and a `cargo publish` run by
hand. `cargo xtask release` does the mechanical half — bump the version,
regenerate the changelog's unreleased region into a section under the new
version, commit both, tag — and stops there:

```console
cargo xtask changelog --write   # refresh the unreleased region
cargo xtask release minor       # bump, cut, commit, tag — locally
cargo xtask release minor --push
```

Without `--push` nothing leaves the machine, and the command prints the two
pushes it did not run. `.github/workflows/release.yml` is what the tag starts,
and it asks `cargo xtask release-notes` for the body rather than keeping its own
copy of the notes.

What the tag does not do is publish. crates.io is a separate `cargo publish` a
person runs, deliberately, because it is the only step here that cannot be taken
back: a GitHub release can be deleted and cut again, and a version number on
crates.io can never be reused, even after a yank.

The changelog's generated region needs [git-cliff]; `nix profile install
nixpkgs#git-cliff` or `cargo install git-cliff`. Its **Behavioural changes**
section is built from `Behavioural-change:` trailers on the commits themselves —
[`docs/CHANGELOG.md`](docs/CHANGELOG.md) says how to write one.

[git-cliff]: https://git-cliff.org
