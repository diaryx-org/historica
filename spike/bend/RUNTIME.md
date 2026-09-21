# Bend's runtime boundary

The pure Historica implementation stays in Bend: parsing, replay, diff,
revision history, and the laws about those definitions. The next host boundary
should let Bend own command policy and the application lifecycle, with Rust
providing the filesystem and process services it needs.

## Current support

Checked against `bend version` **2.0.25**, `bend guide`, and
`bend guide effects`. The adapter below is built: `store.bend` declares
`Store.locate`, `Store.list`, `Store.at` and `Store.digests`,
`ffi/store_*.c` marshal them, and `ffi/src/lib.rs` is the Rust static
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
the minutes instead.)

An effect answers a question and decides nothing. `Store.locate` says where
the store is, `Store.list` what paths it holds, `Store.at` where the bytes
with a digest are, and `Store.digests` what a file's digest and byte count
are. Which files a command opens is the Bend side's, and so is every
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

The four effects here are one-shot — a string in, a string out, nothing
held between calls — which avoids persistent handles. Longer-lived resources need a separate ownership design: the guide
currently permits Base handle types but not arbitrary user-defined handles.
Do not represent ownership merely by a freely copyable numeric pointer.
Shutdown, cancellation, and partial initialization must release Rust-owned
resources even when the happy-path Bend continuation is not reached.

## What each command reads

The boundary is where the cost is, so it is worth stating what crosses it.
`log` and `files` read the whole of `revisions/` and nothing else: the graph
is every revision document and a store's revisions are a megabyte or two.
`cat` and `show` read that, then ask `Store.at` for the digests the revisions
along the chain name for the one file asked about, and read those — a handful
of operation documents, and a payload only where the file was written whole.
`check` reports every file a store holds, so it lists them, reads and parses
the ones with a grammar, and asks `Store.digests` for the digest and the size
of each payload.

That last delegation is the one place a digest is computed outside Bend. It
is here because Bend's SHA-256 runs at about three megabytes a second and the
payloads in a real store are hundreds of megabytes, while nothing in a payload
is parsed and nothing about it is concluded — `check` prints the digest and
the count and that is all. Every document with a grammar is still read and
hashed in `sha256.bend`, which is what the laws and `corpus_*.bend` check,
and `Store.at`'s answer is still verified against it.

The `.js` twin of an effect also needs an implementation, or a clear
unsupported-backend error. A native-only adapter must not silently change the
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
document `Ops.diff` writes replays to the child it was written from. The
decimal layer is unary underneath — as every `Nat` here is — so it counts rather than divides;
positions are line numbers, and a million of them spell in well under a
second, but a divmod writer proven equal to `T.digits` would be the fix if
that ever mattered.
