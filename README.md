# Historica

Historica is an experiment in readable, convergent version control.

The repository format follows one non-negotiable rule:

> The readable files are the authority.

A person must be able to inspect the history, understand its relationships, and
recover stored content without decoding an opaque database or binary operation
log. Binary indexes and snapshots may eventually exist as disposable caches,
but deleting every cache must lose neither information nor meaning.

## Current scope

The `core` module models the smallest collaboration-safe history:

- immutable revisions, each naming both the digest of its own bytes and the
  change it is a version of;
- explicit causal parents, named by digest, so history is a Merkle DAG;
- explicit supersession, so rewriting a change is recorded rather than hidden;
- a history that merges by set union;
- deterministic head discovery, over parents and over supersession alike;
- resolution of a change to its current revision, including the legitimate
  states of divergence and abandonment;
- rejection of two revisions with disagreeing bytes claiming one digest.

The `format` module reads and writes the revision document those revisions are
stored as. It parses strictly — one byte sequence per set of facts, so that
hashing the file is as trustworthy as hashing a canonical model would be — and
refuses anything else with an error naming the line and the fix. Writing a
parsed document reproduces its bytes exactly, and a revision's ID is the
SHA-256 that `shasum -a 256` already prints for the file.

`tests/corpus/revisions/` is the specification, executed. Seven hand-written
files are a real five-change history containing a merge, an amendment by a
reviewer, and the rewrite that amendment forced; nine more are invalid, each
for one stated reason that `tests/corpus.rs` holds the parser to.

The same module reads and writes the operation document, which is what one
revision did to one file: a list of deletes and inserts against the state at
that revision's parents, positions counted into the parent rather than into
the document being built. It is as strict as the revision document and for the
same reason — operations ascend, never overlap, and never state one fact twice,
so one byte sequence parses per edit and the digest can cover the file. Items
are lines, so an item may hold a carriage return that the format's own lines
may not, and a file whose last line has no terminator says so in one place.

`tests/corpus/tree/` is a history of two files with a rename in it, and the
first corpus where the revisions and the operation documents describe one
history together rather than narrating the same one separately.

`tests/corpus/operations/` is that half of the specification. The numbered
files are the edits the numbered revisions made to one file, with a gap at 04
because a merge that changes nothing about a file names no operation document;
three more pin the rules that no revision happened to exercise, and seventeen
invalid ones are each refused for their own stated reason by
`tests/operations.rs`. `states/` is that file as it stands at each revision,
hand-written, which is what the replayer is held to.

The `replay` module materialises a file from what was done to it. It does the
linear case, which decision 0007 says costs nothing: positions are stated
against the parent, so applying them is arithmetic rather than interpretation,
and a chain of documents from the root produces the file byte for byte. It is
also where a `delete` line's redundancy is spent — a document whose recorded
items disagree with the parent it claims to edit is refused there, rather than
absorbed into a merge, and so is a result that would leave a line without a
terminator anywhere but at the end.

The `merge` module is the one decision 0007 spent itself on: concurrent
branches merge by replaying their event graph, and the structure that resolves
concurrency is built during that walk and thrown away at the end, so nothing a
merge needs is ever written down. An item's name is derived — item *i* of
revision *R* is `(R, i)`, and *R* is a digest of readable bytes — and ties are
broken by that name, never by a timestamp. Runs written by one author stay
whole, which is the guarantee Fugue was chosen for. A merge returns the content
and the spans where concurrent work met, so a tool can decline to record an
automatic merge and show a person both versions instead.

The `tree` module is the file set, specified by 0008. A revision records what
it did to it — `add`, `move`, `drop`, `edit` — as headers in the revision
document, and the tree at a revision is what replaying those facts produces.
Files carry identifiers and paths hang off them, so a rename keeps everything
recorded against the file and no heuristic has to recover the connection later.
There are no directories: one exists exactly when a file's path names it.

The `diff` module is the writing half, specified by 0009. Given the file at a
revision's parent and the file as it stands, it records what the revision did:
line matching from `similar`, configured to histogram and to no deadline, and
then Historica's own rules — maximal runs, a replacement anchored at the removed
run's start, and a result that parses whatever the matcher hands over. A file
that did not change names no document at all. `tests/corpus/diffs/` holds a
before, an after, and the document recorded for the pair, for the choices a
property test cannot see; `examples/matchers.rs` is the measurement decision
0009 chose the matcher on.

The `store` module is that format on disk. It loads a `history/` directory by
reading files and never their names — revisions and operation documents alike,
so renaming every file in a store changes no identity and breaks no reference — which is what lets a store be
hand-arranged into something a file browser can narrate. The writer still names
files by digest, appends only, and never overwrites. `check` reads a store
without loading it and separates errors, which mean the store contradicts
itself, from notes, which never fail: an undelivered parent, an undelivered
operation document, a duplicate, or a sync tool's conflicted copy is a
legitimate state and is reported as one. It also replays: every revision on a
linear chain is held to the file set it names and every `-` line to the parent
it claims to have edited, which is the error 0007 asked for and 0008 unblocked.
A store can materialise a file — `tree` and `content` at a revision — and
refuses a history with a merge in it rather than ordering it arbitrarily.

The `historica` binary is the front end decision 0006 said was owed. `init`,
`check`, and `arrange` are the three commands it names; `log`, `show`, `files`,
`cat`, and `names` read a store and render it. Nothing there decides anything
the library has not — `files` and `cat` refuse a merge in the library's own
words rather than choosing an order, and `show` prints the stored file byte for
byte, because the readable file is the authority and a rendering of it is not.
`arrange` is the command with a rule to keep: two replicas arranging one
history must produce one set of filenames, so a collision resolves by change ID
and then by digest, never by a counter, which would depend on what else was in
the directory.

What it does not yet do is use that merge for anything. A caller assembles the
events itself: the store still refuses a history with a merge in it rather than
materialising one, `check` still checks a concurrent history as far as its
merges and no further, and 0008's rules for concurrent tree facts — a `drop`
that loses to an edit, two files claiming one path — are decided and unbuilt.
The ordering rule is held to convergence and to non-interleaving by property
tests over every walk order of each graph they generate; the conformance suite
0007 asks for, against the reference implementation, is still owed. Binary
content has a shape in 0008 and no implementation. Nor does any command record
a revision: minting a change ID, stating an author, and spelling the time are
the writer's decisions, and the `diff` module is the only half of that job
built.

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
    added 2  edited 2
    Start a journal
$ historica files nwlxsqot
docs/README.md  swtlmnkqvzyrxopwstlnmkqv
$ historica cat nwlxsqot docs/README.md
# Notes

A journal kept in Historica, and the notes that came with it.
$ historica name main nwlxsqot
main -> change nwlxsqotvkzmuprysltnwxqk
$ historica arrange
renamed 01-start.rev  ->  2025-08-19 Start a journal.rev
renamed 02-entry.rev  ->  2025-08-19 Say why a path is not an identity.rev
renamed 03-move.rev  ->  2025-08-20 File the README under docs, and say what it covers.rev
renamed 04-drop.rev  ->  2025-08-21 Withdraw the entry, keeping what it taught.rev
/home/adam/journal/history/revisions: 4 renamed, 0 already arranged
$ historica check
/home/adam/journal/history: nothing to report
```

A target is a bookmark, a change ID, or a revision digest, and the last two may
be abbreviated to any unambiguous prefix — decision 0001's disjoint alphabets
are what let one argument position accept either. `historica help` lists the
rest. `check` exits non-zero only when the store cannot be trusted, so it can
be run in anger; a duplicate, an undelivered parent, or a sync tool's
conflicted copy is a note, and notes never fail.

## Decisions

Choices that constrain later work are written down as they are made.

- [`docs/decisions/0001-identity.md`](docs/decisions/0001-identity.md) — why
  every node carries both a derived revision ID and an assigned change ID.
- [`docs/decisions/0002-revision-document.md`](docs/decisions/0002-revision-document.md)
  — the readable revision document, and why its digest covers the file rather
  than a re-serialised model. Examples live in
  [`tests/corpus/revisions`](tests/corpus/revisions).
- [`docs/decisions/0003-store.md`](docs/decisions/0003-store.md) — the store:
  identity comes from content, filenames are presentation.
- [`docs/decisions/0004-parser-contract.md`](docs/decisions/0004-parser-contract.md)
  — strict reading, the `historica-v0` preamble, and why a reader's
  vocabulary can only ever grow.
- [`docs/decisions/0005-authorship.md`](docs/decisions/0005-authorship.md) —
  authorship is copied into every revision of a change, and is a claim rather
  than evidence.
- [`docs/decisions/0006-store-questions.md`](docs/decisions/0006-store-questions.md)
  — one-line bookmarks, a visible `history/` root, and what `check` treats as
  an error rather than a note.
- [`docs/decisions/0007-content-and-merge.md`](docs/decisions/0007-content-and-merge.md)
  — a revision records what it did rather than what a file is, and concurrent
  edits merge by replay rather than by three-way heuristic. Examples live in
  [`tests/corpus/operations`](tests/corpus/operations).
- [`docs/decisions/0008-tree.md`](docs/decisions/0008-tree.md) — files carry
  identifiers and paths hang off them, there are no directories, and a revision
  records what it did to the file set rather than what the file set is.
- [`docs/decisions/0009-diff.md`](docs/decisions/0009-diff.md) — how operations
  are recorded from an edited file, why the matcher is a dependency where the
  merge rule could never be, and the replacement anchoring 0007 left ambiguous.
- [`docs/loro.md`](docs/loro.md) — the initial Loro evaluation, and the
  conditions that would reverse it.

## Development

```console
cargo fmt --all --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test
```

The corpus checks with tools that are already installed, which is the claim the
format exists to make:

```console
cd tests/corpus/revisions && shasum -a 256 -c MANIFEST
cd tests/corpus/operations && shasum -a 256 -c MANIFEST
cd tests/corpus/diffs && shasum -a 256 -c MANIFEST
cd tests/corpus/tree && shasum -a 256 -c MANIFEST
```
