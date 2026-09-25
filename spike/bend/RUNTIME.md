# Bend's runtime boundary

The pure Historica implementation stays in Bend: parsing, replay, diff,
revision history, and the laws about those definitions. The next host boundary
should let Bend own command policy and the application lifecycle, with Rust
providing the filesystem and process services it needs.

## Current support

Checked against `bend version` **2.0.25**, `bend guide`, and
`bend guide effects`. The adapter below is built: `store.bend` declares
`Store.locate`, `Store.list`, `Store.at`, `Store.digests`,
`Store.folder`, `Store.tty`, `Store.move`, `Store.write`, `Store.remove`, `Store.real`, `Store.mkdirs`, `Store.now`, `Store.fill`, `Store.once`, `Store.copy`, `Store.tidy`, `Store.sweep`, `Store.exit`, `Store.link` and `Store.runs`, `ffi/store_*.c` marshal them, and `ffi/src/lib.rs` is the Rust static
library. `check.py` builds the archive, emits `main.bend` to C, links the
two, and holds the result — and the `.js` build, which runs the twins in
`ffi/store_*.js` — to the Rust tool.

[Issue #813](https://github.com/bendlang/bend/issues/813) requests a native
library target for pure definitions, with selected exports, a generated
header, and explicit lifecycle and failure contracts. The maintainer's final
comment on the issue says it is planned but unscheduled and tracked in the
SOON section of `WONTFIX.txt`. A compiled Bend executable is not a callable
Rust library. JavaScript can call pure definitions through the documented
loader today.

The workaround reported in that discussion reverses the host relationship:
Bend runs the application, C translates effect values and parks asynchronous
work, and a Rust static library owns external resources. That is the shape
here: the first slice is locating the store and listing its documents, which
is what lets `main.bend` take `historica`'s own arguments instead of paths.

## Shape of an adapter

`bend x.bend -o x` compiles the C itself, with `-O3 -lm -lpthread` and
nothing else, so an archive cannot be linked that way: emit C with `-o x.c`
and link by hand. Bend 2.0.25 emits some 3.5 MB of C for `main.bend` in
about half a minute, which `cc -O3` compiles in ten seconds or so;
`check.py` allows minutes for both. (2.0.20 emitted 60 MB and clang took
the minutes instead.) With `record --dry-run`, `name` and `init` in it, and
under 2.0.27, it is some 9.7 MB in about a minute — a megabyte of it the
notes `init` writes, since a string is a list — and beside the mutation
stage's checkers it can take ten, so `check.py` allows half an hour.

An effect answers a question and decides nothing. `Store.locate` says where
the store is, `Store.list` what paths it holds, `Store.at` where the bytes
with a digest are, `Store.digests` what a file's digest and byte count
are, and `Store.folder` what one directory of the folder beside the store
holds — each entry's name and what it is, a link's target read and never
followed, a file's execute bit and length. Which directories are walked,
which files a `skipped/` rule keeps out, and which paths the format can hold
are decided in `folder.bend`, which asks for a directory only once it has
decided to walk it: a skipped `target/` is never listed. `Store.tty` says
whether standard output is a terminal, and `--color auto` decides. Which files a command opens is the Bend side's, and so is every
conclusion: a path `Store.at` offers is opened and hashed in `sha256.bend`
before the document at it is believed to be the one asked for, which is
`store::catalogue`'s own rule — *the digest of a file is never believed*.

1. A Bend definition returns `IO(Result<..., R>)`; the pure caller decides
   what to do with success or failure. No foreign effect belongs in a law or
   in the pure replay implementation.
2. A C effect registered with `io_eff` translates Bend values to a small C
   ABI. Copy a string using `io_cstr`, pass its explicit byte length to Rust,
   and free the copy. Copy results back using `io_str`/`io_done`/`io_fail`.
3. Rust exposes `extern "C"` functions from a `staticlib`. Keep Rust objects
   and allocation ownership in Rust; pair every returned allocation with a
   Rust release function. Do not pass `String`, `Vec`, or Rust enum layouts
   across C. Errors return through the ABI; unwinding must not cross it.
4. Blocking filesystem work uses `io_work`: its worker callback has no
   `Env` and never accesses Bend's heap. The completion callback marshals
   the result on the event loop. Descriptor readiness can use `io_wait_on`.
5. Compile Bend to C and link that generated program with the Rust archive.
   Pin the compiler and rebuild the adapter on each upgrade. The effect
   symbols and value representation are runtime internals, not a stable ABI.

The twenty effects here are one-shot — a string in, a string out, nothing
held between calls but where a pinned seed's stream has got to — which
avoids persistent handles. Longer-lived resources need a separate ownership design: the guide
currently permits Base handle types but not arbitrary user-defined handles.
Do not represent ownership merely by a freely copyable numeric pointer.
Shutdown, cancellation, and partial initialization must release Rust-owned
resources even when the happy-path Bend continuation is not reached.

## What each command reads

The boundary is where the cost is, so it is worth stating what crosses it.
`log` and `files` read the whole of `revisions/` and nothing else but
`names/` and `skipped/`: the graph is every revision document and a store's
revisions are a megabyte or two, and a bookmark or a rule is a line.
`Store.list` walks `names/` and `skipped/` only when asked for them by name,
since nothing there is a document.
`cat` and `show` read that, then ask `Store.at` for the digests the revisions
along the chain name for the one file asked about, and read those — a handful
of operation documents, and a payload only where the file was written whole.
`check` reports every file a store holds, so it lists them, reads and parses
the ones with a grammar, and asks `Store.digests` for the digest and the size
of each payload.

`diff` and `blame` with no target read the folder as well: they walk it a
directory at a time, ask `Store.digests` for the digest of each file it
tracks, and read here only the files whose digest is not the one the
position's nearest statement of them leaves — a `text` payload's name, or the
`result` an `edit`'s document states — or that the position does not hold.
`status` reads the same, except that it reads a file the position does not
hold not at all — its digest is what a rename is noticed by — and where
`--merge` joins several parents, a file of lines is replayed at each of
them rather than settled by its nearest statement.

`record --dry-run` reads what `status` reads, and a file arriving that a
person said is lines, which has to be text. Before it reads anything it
does the one write here: each rename `--move` states, through `Store.move`,
which asks whether each end is there as the Rust tool asks it — following
links — and renames where the old is and the new is not, making the new
path's directory first, and answers `moved`, `there`, `both` or `neither`.
What each answer means to a person is the Bend side's, and so is which
moves are asked for: one with an end that is absolute or climbs out with
`..` is not, since it would land outside the folder.

`name` reads what `names` reads, and writes one file: `Store.write` makes
the bookmark's directory, stages the bytes beside the file, flushes them
and renames them over it, as the Rust tool's `write` lands a mutable file,
so a reader sees the old bookmark or the new one. `name --delete` asks
`Store.remove` to remove the file and each directory it leaves empty, up
to and not including `names/`. Which file, and what goes in it, is the
Bend side's, and so is every refusal: a name that would leave `names/` is
refused before either is asked.

`init` reads nothing of a store — there is none yet. It asks `Store.real`
for the current directory, and whether `historica.txt` is already where
the store would go (a path that is not there has no real path); makes the
directories with `Store.mkdirs`; writes the four notes through
`Store.write`; and asks `Store.real` once more where the store really is,
to say so.

`record` writes the store, and asks three things only the host has. What
time it is (`Store.now`) and random bytes (`Store.fill`, as hex) are the
two decision 0010 made inputs rather than calls: unset, they are the
system clock in the local offset and the operating system's random
source; with `HISTORICA_PINNED_NOW` and `HISTORICA_PINNED_SEED` set, they
are the moment pinned and the stream `historica-pinned` draws — SHA-256 of
the seed and a block counter, carried across calls in the process, which
is the one thing any effect here remembers. `check.py` sets both for the
port and for `historica-pinned`, the Rust tool's test build, so a record
from either is the same bytes. The host honours the pins in every build of
the port, where the Rust tool keeps them out of `historica` altogether; a
port that shipped would keep them to a build of its own the same way.
Every file it writes goes through `Store.once`, as the store files a
document: made once, left alone where the same bytes are already there,
refused where different ones are. A payload of bytes is `Store.copy`: the
folder's file, filed the same way, refused where it no longer hashes to
the digest the survey found. Who is recording is `HISTORICA_AUTHOR`, read
with Base's own `IO.get_env`. Which identifiers, which files, what they
say, what they are called and which bookmarks follow are all decided in
Bend first.

`amend`, `abandon` and `carry` ask the same things of the host and
nothing new. An `amend` the folder speaks for reads what `record` reads;
a reword, an `abandon` and a `carry` read no folder, only `revisions/`,
`names/`, and — where something is carried — every operation document the
revisions name, fetched once, since a carry that restates a file replays
its content on both sides of the rewrite and the revision's own document
against them. Each revision and each restated document is filed through
`Store.once`, one not already held anywhere, as the Rust store files them;
a bookmark an `abandon` moves goes through `Store.write`. Which revisions
are carried, in what order, what each restates and what it is called are
decided in Bend.

`arrange` reads what `check` reads — every revision and operation
document, read and hashed here, and the digest of each payload from
`Store.digests` — since a file's digest is what it is called for. Each
rename it plans goes through `Store.move`, the effect `record --move`
uses, over the store rather than the folder: it renames where the old
path is and the new is not, and answers `both` where the new name has
filled since the plan, which the Bend side reads as a file to leave.
`Store.tidy` then removes the directory the file left and each above it
until one holds something or the store's own directory is reached, which
is never removed. `Store.sweep` removes every empty directory under the
one named, deepest first, keeping that one. Which files move, where, and
what a refused rename means are all decided in Bend.

`prune` reads what `arrange` reads, and the bookmark and rule files as
text, to ask the part of `check` it asks before destroying anything. Each
file it removes goes through `Store.remove`, with the file's own directory
as where tidying stops, so each call removes one file and nothing else;
the entries of `cache/` named by a digest are found through `Store.folder`
and removed the same way; and `Store.sweep` takes every directory under
`revisions/` and `operations/` that was left holding nothing. Which
revisions go, which content is still needed, and what counts as a cache
entry are decided in Bend.

`receive` reads what `prune` reads, of both stores, and the files of
`claims/`, which `Store.list` now walks when asked for by name, their
digests from `Store.digests`. It writes through the effects `record`
already uses: every document and revision through `Store.once`, the text
read and hashed here under the digest it hashed to; every payload and
every file of `claims/` through `Store.copy`, which hashes it again as it
copies and refuses one that moved on; every bookmark through
`Store.write`; every rule through `Store.once`; and the originals a
forgetting document stands in for through `Store.remove`, then
`Store.sweep`. Which files, under which names, and what a disagreement is,
are decided in Bend. A dry run that finds a disagreement prints it and
ends with code 1, which `IO.die` cannot do without a line on standard
error: `Store.exit` ends the process with the code given. It is the one
effect with no Rust behind it — ending the program is the C runtime's, and
nothing about a store comes into it — and the JS twin's writes are
synchronous, so nothing printed is lost.

`offer` writes nothing but standard output. It reads what `prune` reads,
the bookmarks, and the files of `claims/` with their digests from
`Store.digests`; each rule and bookmark file is read and hashed here, so
its line carries the digest its bytes have. `Store.really` answers
whether the copy holds `history/historica.txt`, and gives the copy's own
name, resolved, to put before every path. Which files are listed, in what
order, and which are private is decided in Bend.

`export` reads what `receive` reads of this store, and the stored texts of
the target's ancestry through `Store.fetch`, as `cat` does, so each file of
lines is replayed here. It writes a copy through the effects `init` and
`receive` already use — `Store.mkdirs` and `Store.write` for `init`'s
layout, `Store.once` for every document, revision and rule, `Store.write`
for every bookmark, `Store.copy` for every payload and file of `claims/` —
and lays the folder out file by file: a file of lines through `Store.once`,
the text replayed here; a file of bytes through `Store.copy`, straight out
of the store; and two effects of its own. `Store.link` makes a link where
it is told, pointing where it is told, at a staged sibling renamed over the
path, and never opens what it points at. `Store.runs` makes a file
runnable the way the Rust tool's `set_executable` does — the execute bits
follow the read bits — and answers whether anything changed, which is
what `--files-only` reports as a `mode` line. Which files, under which
names, spelled how, and which of them run, are decided in Bend: where a
link points is `materialise`'s arithmetic, here. `Store.folder` answers
whether the destination holds anything, and what.

Those three delegations are the only places a digest is computed outside Bend. They
are there because the payloads in a real store are hundreds of megabytes, and
the folder is the store's size again, all of which would have to be read into
a list of bytes and packed before it was hashed — and a payload `record`
files is copied as the Rust tool streams it, hashed on the way past — while nothing in a payload
is parsed, and a folder digest only decides whether a file is read: `check`
prints the digest and the count and that is all, and a file `diff` reads is
compared here, line by line. Every document with a grammar is still read and
hashed in `sha256.bend`, which is what the laws and `corpus_*.bend` check,
and `Store.at`'s answer is still verified against it.

The `.js` twin of an effect also needs an implementation, or a clear
unsupported-backend error. It fails through a `hist_fail` of its own
rather than the runtime's `io_fail`, which keeps only the code and says
the system's words for it — a refusal like "no `history` directory here
or above …" would otherwise reach a person as "No such file or
directory". A native-only adapter must not silently change the
behavior of `bend main.bend` or of the JavaScript tests.

## What the proofs cover

`PROOF.bend` checks source terms and termination. It does not verify the
compiler, the native/JS runtime, C marshalling, Rust effects, or operating
system behavior. Run `python3 spike/bend/check.py` from any directory to check
the laws and exercise both current backends against the same corpora. Any
future adapter needs its own boundary tests for malformed values, errors,
allocation release, and repeated calls before becoming part of the CLI.

The Verus merge convergence theorem has a Bend counterpart,
`merge_converges`, over the model in `merge.bend`: two causal orders of one
graph merge to one file or one refusal. The model differs from
`../verus/merge_model.rs` in shape — a flat name-ordered list rather than an
index tree, and an event's anchor decided on its restricted view rather
than found on the whole tree — so it needs none of the well-formedness
hypotheses the Verus proof carries; it is held to `merge.rs`'s tests rather
than derived from its code.

The current transfer also includes the linear replay specification, proofs
of the executable agreement/advance/delete helpers, and a refinement of the entire
`Ops.apply` cursor implementation to `Cursor.apply`, a forward-order walk.
That refinement preserves exact results and errors for arbitrary inputs,
but shares the public validators. `edit_block_semantics` connects the
implementation to position-based `Spec.result` for an arbitrary insertion,
deletion or same-position replacement at any valid parent gap, and
`script_semantics` composes any list of such blocks, each a stated gap past
the last: `Ops.apply` on a whole script is the positional result, or the
first disagreeing quote read at its own coordinate — stated over raw
operations too, for any list `Block.ordered` accepts — and
`parser_accepts_ordered` shows the parser accepts nothing else, so
`parsed_document_semantics` runs from the document's text. `write_parse`
closes the other direction: what the parser accepts, the writer spells
back byte for byte, decimal numbers included; `diff_applies` says the
document `Ops.diff` writes replays to the child it was written from.
`merge_linear` says the merge walk over a chain of parsed documents reads
what applying them in turn does, which is what `merge.rs`'s `linear` fast
path relies on. `merge_extends` extends that past a line: after any
history, an event that had seen all of it leaves what applying its
document leaves, and `merge_walk_invariant` says every tree a walk builds
keeps the invariant Fugue's anchor needs. The
decimal layer is unary underneath — as every `Nat` here is — so it counts rather than divides;
positions are line numbers, and a million of them spell in well under a
second, but a divmod writer proven equal to `T.digits` would be the fix if
that ever mattered.
