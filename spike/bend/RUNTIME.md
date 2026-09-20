# Bend's runtime boundary

The pure Historica implementation stays in Bend: parsing, replay, diff,
revision history, and the laws about those definitions. The next host boundary
should let Bend own command policy and the application lifecycle, with Rust
providing the filesystem and process services it needs.

## Current support

Checked against `bend version` **2.0.19**, `bend guide`, and
`bend guide effects`. The current commands use Base IO; there is no Rust
adapter in this spike yet. The JS/native test gate also passes on 2.0.20.

[Issue #813](https://github.com/bendlang/bend/issues/813) requests a native
library target for pure definitions, with selected exports, a generated
header, and explicit lifecycle and failure contracts. The maintainer's final
comment on the issue says it is planned but unscheduled and tracked in the
SOON section of `WONTFIX.txt`. A compiled Bend executable is not a callable
Rust library. JavaScript can call pure definitions through the documented
loader today.

The workaround reported in that discussion reverses the host relationship:
Bend runs the application, C translates effect values and parks asynchronous
work, and a Rust static library owns external resources. This is suitable for
Historica too; its first useful slice would be listing store documents, which
currently have to be passed as explicit paths to `main.bend`.

## Shape of an adapter

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

A first directory-listing effect can be one-shot, avoiding persistent
handles. Longer-lived resources need a separate ownership design: the guide
currently permits Base handle types but not arbitrary user-defined handles.
Do not represent ownership merely by a freely copyable numeric pointer.
Shutdown, cancellation, and partial initialization must release Rust-owned
resources even when the happy-path Bend continuation is not reached.

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

The Verus merge convergence theorem is still a theorem of
`../verus/merge_model.rs`. Porting its graph definitions without its
well-formedness hypotheses and proof would not give Bend that guarantee.
The current transfer includes the linear replay specification, proofs of the
executable agreement/advance/delete helpers, and a refinement of the entire
`Ops.apply` cursor implementation to `Cursor.apply`, a forward-order walk.
That refinement preserves exact results and errors for arbitrary inputs,
but shares the public validators. `edit_block_semantics` connects the
implementation to position-based `Spec.result` for an arbitrary insertion,
deletion or same-position replacement at any valid parent gap, and
`script_semantics` composes any list of such blocks, each a stated gap past
the last: `Ops.apply` on a whole script is the positional result, or the
first disagreeing quote read at its own coordinate — stated over raw
operations too, for any list `Block.ordered` accepts. Proving the parser
only accepts ordered documents remains to be done.
