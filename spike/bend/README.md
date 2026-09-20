# Historica, in Bend

The readable core of Historica's format, written in [Bend](https://bend-lang.com)
as an experiment: does the format — every document named by the SHA-256 of its
own bytes, revisions as a Merkle DAG that merges by union, a file materialised
by replaying what was done to it — survive a port to a pure, affine,
termination-checked language, and what can that language *prove* about it?

Everything here is held to the same corpus the Rust crate is
(`../../tests/corpus`), and to the Rust tool itself on a real store.

```console
cd historica/spike/bend
python3 check.py                 # proofs, JS/native corpora, mutation checks
bend PROOF.bend                  # the laws: prints "All terms check."
bend corpus_ops.bend             # the operations corpus, every line `ok`
bend corpus_rev.bend             # the revision corpora, every line `ok`
bend main.bend -- log    history/revisions/*/*.rev.txt
bend main.bend -- check  history/revisions/*/*.rev.txt history/operations/*/*/*
bend main.bend -- replay history/operations/*/Start/notes.txt history/operations/*/*/notes.txt.ops.txt
bend main.bend -- diff   old.txt new.txt
```

## What is here

| File | What it is | Rust counterpart |
|---|---|---|
| `sha256.bend` | SHA-256 over bytes, from FIPS 180-4 on `U32` bit operations; Base has no hash | `sha2` crate |
| `utf8.bend` | bytes ↔ `String`, and reading a file as bytes | `std::str` |
| `text.bend` | lines, fields, canonical numbers, digest spelling | `format::Lines` |
| `ident.bend` | change and file IDs in the `k`–`z` alphabet, spelled and deciphered | `core::{ChangeId, FileId}` |
| `ops.bend` | the operation document: parse, write, replay, diff | `format::operations`, `replay`, `diff` |
| `revision.bend` | the revision document: parse, write; and `History` — heads, superseded, missing parents, change state | `format`, `core` |
| `main.bend` | `log`, `check`, `replay`, `diff` over the documents you name | `cli` |
| `LAWS.bend` / `PROOF.bend` | twenty-two claims about the code, each proven | the test suite and Verus replay helpers |
| `replay_spec.bend` | independent position-based replay specification | `spike/verus/replay.rs` |
| `semantic_replay.bend`, `position_lemmas.bend` | positional semantics for an arbitrary insertion, deletion or replacement block; coordinate translation | first semantic replay bridge |
| `cursor_spec.bend`, `replay_lemmas.bend` | forward cursor specification and accumulator/error algebra | refinement of the Bend walk |
| `replay_tests.bend`, `check.py` | oracle comparisons, refusal regressions, proof mutations; JS and native gates | replay tests |
| `corpus_ops.bend`, `corpus_rev.bend` | the corpus, executed | `tests/*.rs` |

### What the corpus says

`corpus_ops.bend`: nine valid documents parse and write back byte for byte,
twenty-two invalid ones are refused, the three edits in the numbered history
replay to the hand-written states in `states/` (held to `result` where one is
stated), and the four `diffs/` fixtures — a replacement anchored at the
removed run, a surviving line between two rewrites, a final newline gained
and lost — are what `diff` writes, byte for byte.

`corpus_rev.bend`: twenty-five valid revisions across the `revisions`,
`tree`, `links`, `modes`, `whole` and `merged` corpora round-trip; twenty-one
invalid ones are refused, each for its own reason; and the seven-revision
history resolves as the core says — `04` is superseded and still a head of
the graph, the amended change resolves to `05`, the rebased merge to `06`, two
amendments that saw neither diverge.

On a store `historica init` and `historica record` made, `log` prints the
same history, `check` names every document by the digest `shasum` prints, and
`diff` writes the operation document the Rust tool wrote, `result` included.

### What the laws say

`bend PROOF.bend` checks that, for every input:

- a digest is sixty-four characters (`digest_length`);
- an insert removes nothing and a delete's end is its position plus its count
  (`insert_removes_nothing`, `delete_end`);
- a forgotten item ignores text but still requires the same terminator at
  replay, and is nobody's line to the diff (`forgotten_agrees`,
  `forgotten_is_nobodys`);
- the walk that materialises a file never loses an item: kept and left add
  up to what there was, at every distance (`advance_keeps_everything`, by
  induction, with an `add_succ` lemma about `Nat`);
- a delete quoting nothing removes nothing and cannot disagree
  (`drop_nothing`);
- the first operation has nothing to be ordered after (`ordered_first`);
- a single terminated line's text is that line and a newline
  (`text_of_line`);
- the empty history has no heads, a root alone is its history's one head,
  and a change nobody recorded is unknown (`empty_history_heads`,
  `root_is_head`, `no_revisions_unknown`).

The Verus transfer first added four laws:

- `agreement_matches_spec`: runtime agreement equals the independent
  case-based specification, including forgotten payloads and terminators;
- `advance_exact`: advancing transfers precisely the reversed prefix onto
  the accumulator and leaves precisely the suffix, for every distance;
- `drop_checked_exact`: deletion leaves the suffix after the quoted width,
  and its success flag is exactly the incoming flag AND agreement of every
  quoted item with the parent's prefix;
- `result_no_operations`: the position-based specification leaves an
  unedited parent unchanged.

The last three use induction. `replay_spec.bend` ports Verus's `deleted_at`,
`inserts_at`, and `result`: each parent gap contributes its inserts, then the
parent item unless deleted, including the trailing gap. It deliberately
contains no cursor or reversed accumulator. It specifies output only;
range, agreement, newline, and digest validity are separate conditions.

`replay_tests.bend` compares full items (text, terminator, and forgetting
flag) for every insertion gap and deletion interval of five small parents,
plus replacements, trailing-gap inserts, and multiple edits. It checks
refusals and digest handling separately. It also retains Verus's
counterexample to unrestricted order independence: two inserts at one gap
concatenate in document order, so distinct insert positions are a necessary
hypothesis. The parser already enforces that restriction. Bend's current
`Ops.apply` also requires parser-ordered, non-overlapping operations; unlike
the Verus two-pass implementation it does not support shuffling a raw `Doc`.

Two further laws cover the complete cursor implementation:

- `cursor_walk_equivalent` proves, by induction over **every** operation
  list, that `apply.go` equals a forward-order walk with the reversed
  accumulator prepended and the earliest error preserved. The invariant
  permits arbitrary cursor positions, parent suffixes, accumulators, and
  prior errors; it does not assume parser acceptance.
- `cursor_apply_equivalent` lifts that equality through the public
  `Ops.apply` boundary, including exact success items and error strings.

`cursor_spec.bend` describes each operation by `take`, `drop`, forward
append, and the independently specified quote agreement. It uses none of
`advance`, `drop_checked`, `land`, or `apply.go`. The public specification
shares the range, newline and digest validators with the implementation;
this proof verifies their wiring, not their independent correctness.
`replay_lemmas.bend` provides the list reversal/append algebra and
first-error composition that connect the two representations.

The first connection to the independent positional result is now proved:

- `positional_translation` shows that shifting every operation and the
  starting position by the same offset preserves `Spec.result_from`, for
  arbitrary documents, parents and offsets. It needs no ordering assumption.
- `edit_block_semantics` shows that executable `Ops.apply` equals a
  specification whose success payload is **`Spec.result` itself**, for an
  insertion, deletion, or same-position delete/insert replacement. A split
  into arbitrary `before` and `after` lists witnesses any valid parent gap,
  including empty parents and the trailing gap. The quoted/inserted items
  and stated digest are also arbitrary. Disagreements, oversized deletions,
  invalid newlines, and digest errors retain their checks.

`semantic_replay.bend` constructs these three block shapes and uses the
positional model to assemble their output. `position_lemmas.bend` proves the
coordinate, prefix/suffix, deletion-window and replacement lemmas that
connect them to the cursor. Range, newline and digest validators remain
shared; their independent correctness is not claimed. No ordering theorem
for an arbitrary multi-block document or for the parser follows yet.

The next induction must compose these blocks: later operations must start
past the consumed parent interval, while a replacement's insert retains the
original anchor. After that, parser acceptance must establish those global
conditions. The split used here witnesses only one block's starting gap.

The tests compare both specifications for the ordered examples, and
compare the cursor specification with the implementation for raw reversed
positions, repeated inserts, overlapping deletes and competing errors.
Nine mutations cover the primitive helpers, lost inserts, a lost trailing
suffix, an overwritten earlier error, a public replay that skips the
digest check, a positional model that drops the trailing gap, and an
inclusive deletion endpoint. The proof gate rejects each at its expected
proof location.

`check.py` runs the proofs and all three suites on both the default JS and
native C backends, then verifies that deliberate replay mutations fail the
proof gate. Corpus failures now exit nonzero. The runner prints and fixes
the compiler path for each run. The full gate passes on Bend 2.0.20; native compilation of the revision corpus takes a few
minutes on the development machine.

Still unproved are the positional `Ops.apply == Spec.result` contract for
arbitrary multi-block documents and the parser ordering guarantee,
independent error soundness, merge convergence,
`apply(diff(parent, child)) == child`, and `write(parse(s)) == s`. The corpus and oracle comparisons provide
executable checks where those general proofs are still missing. See
[RUNTIME.md](RUNTIME.md) for the C/Rust interop direction and proof boundary.

## What the port found

Checking the ordering assumptions for the cursor proof found a bug shared
by the Rust and Bend parsers: `delete 0 2`, `insert 0`, `delete 1 1` passed
adjacent-operation checks because the insert hid the first deletion's end.
Bend's cursor could then refuse an edit whose positional result is defined.
Both parsers now retain the last deletion across inserts, refusing hidden
overlaps and adjacent deletions. Three shared invalid fixtures and a valid
replacement followed by another edit cover the boundary. Proving that all
parser-accepted documents satisfy the required global ordering predicate
remains separate work.

The original port also found a gap in the crate's *prose*:
`format.txt` was not enough to reimplement the parsers from, and the
`operations.rs` and `format/mod.rs` sources had to be read for rules the
corpus pins and the document does not say:

- a delete may precede an insert at one position, and an insert may not
  precede a delete there;
- two deletes that meet are one delete, refused as two;
- a tool's own headers sort against each other by key, where every other
  repeated header sorts by value;
- `revised-by` naming the author is refused as saying nothing;
- a `text` line names a file this revision `add`s, and nothing else;
- a file's content is stated in one model — `edit`, `text`, `bytes` or
  `link` — never two;
- a timestamp has a signed offset, and `Z` is not a spelling the format has.

Each is a sentence `format.txt` could carry, since it already carries the
rules beside them.

## What is not here

The port is the *format* and the *core*; the Rust crate is 33k lines and this
is under 3k. Not ported:

- **The tree.** Which file is a link, which was added when, what path a file
  has at a revision — `tree.rs` — so the three invalid fixtures that need it
  (`drop-a-referenced-file`, `edit-a-link`, `link-a-plain-file`) are not in
  `corpus_rev.bend`.
- **Merging** concurrent branches by replaying the event graph (`merge.rs`),
  and **resolutions** — the `keep`/`insert` document a merge states.
- **Forgetting** past the marker: `stand_in`, and the two-header document
  that replaces a destroyed payload.
- **The store** as a folder: `init`, `record`, `arrange`, `fetch`, `export`,
  bookmarks. Base cannot list a directory, which is why every command takes
  paths.
- Unicode normal form C on paths, and the timestamp's calendar (leap days).
  The timestamp's shape and ranges are checked.

## What Bend asked for

Things a port learns that the guide states once and the checker enforces
everywhere:

- **No mutual recursion, and a `match` only on a parameter or a pattern-bound
  variable.** A parser that classifies a line and then recurses cannot call a
  helper that calls it back. The idiom throughout is to classify the *head*
  before the recursive call and pass the classification in as a parameter —
  `take_items(ls, r: Read, ..)`, `parse.ops(fuel, n: Next, ..)`,
  `headers.go(ls, h: Result<Header>, ..)`, `backtrack(fuel, v: Verdict, ..)` —
  so the recursion matches only what a pattern bound.
- **Fuel** where a step consumes a variable number of elements: the UTF-8
  decoder and the operation walk count down the input's length.
- **The shrinking argument comes first.** `split_once.go(s, acc)`, not
  `(acc, s)`.
- **`Bool.pick` is eager**, so both branches must be affine-legal at once;
  a branch that recurses gets a `keep`-style helper that matches the `Bool`
  instead.
- **Quantities are part of a function's type**: a def with a `+` parameter
  is not a `String -> Bool`, and is passed to a template as
  `~(x => f(x))`. Template arguments must be closed, so a filter over a
  captured local is a plain recursive def.
- **Constructor names are global**, so a `Key` cannot have a `Move{}`
  beside Base's `Event`; they are `Key.Move{}` here.
