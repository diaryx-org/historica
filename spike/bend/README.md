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
| `LAWS.bend` / `PROOF.bend` | thirty-two claims about the code, each proven | the test suite and Verus replay helpers |
| `replay_spec.bend` | independent position-based replay specification | `spike/verus/replay.rs` |
| `semantic_replay.bend`, `position_lemmas.bend` | positional semantics for an arbitrary insertion, deletion or replacement block; coordinate translation | first semantic replay bridge |
| `composition_lemmas.bend` | a script of blocks, composed: the cursor over a whole document is the positional result | the multi-block theorem |
| `parser_lemmas.bend` | the parser only accepts ordered documents: its per-operation check implies `Block.ordered`, and the parse loop applies it to every operation | the parser theorem |
| `refusal_lemmas.bend` | refusals are justified: every refusal of an ordered document has one of four positional causes, and no cause means the positional result | error soundness |
| `diff_lemmas.bend` | `apply(diff(parent, child)) == child`: the LCS backtrack yields a script that takes the parent to the child, and the runs of that script are blocks the cursor walks to it | `tests/diff.rs` |
| `equality_lemmas.bend`, `decimal_lemmas.bend`, `spelling_lemmas.bend` | `write(parse(s)) == s`: equality decided down to the bits of a word, decimal numbers spelled as read, and every line the parser consumed written back | `writing_a_parsed_document_reproduces_its_bytes` |
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
shared; their independent correctness is not claimed.

The blocks compose. A *script* (`Block.Step`) is a list of blocks, each
sitting `gap` parent items past where the previous one finished — an
insertion consumes nothing, a deletion or replacement consumes what it
quotes — and `Block.script` writes it out as absolute operations. That is
every shape the parser's ordering rules admit, and some they refuse (two
inserts at one gap, an insert directly at a deleted run's end), which the
theorem covers all the same:

- `script_semantics`: for **any** parent, script and stated digest,
  `Ops.apply` equals `Block.replay` — the range check, then the first delete
  whose quote the parent does not hold *at that delete's absolute
  coordinate* (`Block.quote_error`, which reads `List.drop(parent, at)` and
  nothing of the cursor), else `Spec.result` of the whole operation list,
  then the newline and digest checks. Nothing about the cursor, its
  reversed accumulator or its running position appears on the right.

`composition_lemmas.bend` is the induction over the script. Its invariant
is that the cursor's state at position `p` is `List.drop(parent, p)`; each
step peels one block with `walk_block`, `error_block` and `result_block`,
and `skip` moves the positional model across the gap, which needs every
later operation to sit at or past the gap's end (`below`) and the gap to
fit the parent — the range check, which is why `Cursor.checked` runs it
first and why out of range both sides are the same refusal. A quote that
disagrees settles both sides as that refusal before any payload is compared
(`settle`), so a delete running past the end needs no separate case.

The same is stated over raw operations. `Block.ordered` says what a script
looks like written out — each operation at or past where the last finished,
an insert at a delete's own position being that delete's replacement — and
`Block.steps_of` reads the script off such a list:

- `ordered_operations_are_scripts`: whenever `Block.ordered(ops, pos)`,
  `Block.script(Block.steps_of(ops, pos), pos)` is `ops` again;
- `ordered_document_semantics`: so for any ordered `ops`, `Ops.apply` equals
  `Block.replay_ops(parent, stated, ops)`, with no script in sight.

`Block.ordered` is weaker than the parser: it admits two inserts at one
gap, and an insert at a deleted run's end, which the parser refuses; it
refuses what the parser refuses for the cursor's sake — an overlap, an
insert inside a deleted run, a delete hidden behind a replacement. Every
valid document in the operations corpus is ordered (`corpus_ops.bend`
checks it).

The parser is proven to accept nothing else. `Ops.next_op.bounded` is now
the one place operations are ordered: each must follow both the previous
operation and the last delete (`Ops.ordered`), which `parser_lemmas.bend`
names `ordered_all`. Two theorems close the gap:

- `parser_accepts_ordered`: whenever `Ops.parse(s)` is
  `Done{Doc{_, _, ops}}`, `Block.ordered(ops, 0n)` holds. `parser_ordered`
  shows `ordered_all` implies `Block.ordered` by reading each refusal off
  `Ops.ordered` — an insert forbids its own position, a delete its run and
  its end for a delete — and `collect_ordered` shows the loop establishes
  `ordered_all`, through a forward-building twin of the reversed
  accumulator; the header chain is a case per validator.
- `parsed_document_semantics`: so any document the parser accepts replays
  under `Ops.apply` exactly as `Block.replay_ops` says. This is the
  end-to-end statement: text in, positional result or first disagreeing
  quote out, nothing about the cursor in between.

`corpus_ops.bend` runs the last one on every replayed history document.

The writer is proven to reproduce what the parser accepted, byte for byte:
`write_parse` says `Ops.write(doc) == s` whenever `Ops.parse(s)` is
`Done{doc}`. Three files carry it. `equality_lemmas.bend` decides equality
of characters and strings down to the bits of a word (`Word.cmp` returning
`EQ` is `a == b`), so that a comparison the parser made becomes an
equation; the parser now compares with a structural `T.same` rather than
`String.eq`, whose three-way comparison returns tuples a proof cannot open.
`decimal_lemmas.bend` proves `spell_number`: `T.spell(n) == s` whenever
`T.number(s) == Some{n}`. The decimal layer was rewritten for it: one digit
table serves reader and writer, a number is a little-endian digit list
(`T.value`, `T.digits`), and counting up (`T.dsucc`) is what links the two
— ten times a positive number puts a zero in front of its digits, and a
digit below ten added to that puts the digit in front — with no arithmetic
of machine words anywhere. `spelling_lemmas.bend` walks the parser:
`unlines(lines(s)) == s`, then `taken` for the items under an operation
(each line is its prefix and body, a `\ no newline` line unterminates the
item above, a `\ forgotten` line is a forgotten item), `next_op_sp` for the
operation line (cut at its first space, its keyword and numbers spelled
back), `collect_sp` for the loop, and one lemma per header validator.

The diff is proven to replay: `diff_applies` says `Ops.apply(parent, doc)`
is `Done{child}` whenever `Ops.diff(parent, child)` is `Some{doc}` and the
child has a newline on every item but the last (what a file has).
`diff_lemmas.bend` does it in two halves. `edits_ok`: the backtrack over the
LCS table yields an edit script that takes the parent to the child. That
needs nothing about the table's contents — a verdict only has to be
consistent with the items it names, which `step` guarantees by
construction — but it does need the fuel to last, so the induction carries
`i + j ≤ fuel`. `runs_apply`: the runs of an edit script, one block each
(`Ops.runs`, `Ops.block`), apply as a script of blocks; `steps_walk` and
`steps_range` then say the cursor walks such a script to its result and
every block is in range. The diff's grouping was rewritten to emit that
script shape directly, through the same `Ops.script` the theorems are
stated over; the recorded diff fixtures confirm its output is unchanged.

Refusals are justified. `Block.cause` names the four reasons a replay can
be refused, each read off the parent and the operations alone: an
operation past the end, a delete quoting what the parent does not hold at
its own coordinate, an item without a newline that is not last, and a
stated digest the result does not have unless forgetting put unhashed
bytes in it. `refusal_has_cause` says every refusal of an ordered document
has one; `no_cause_replays` says a document with none replays to
`Spec.result`. Both are corollaries of `ordered_document_semantics` read
through the four checks (`refusal_lemmas.bend`); what they add is that no
refusal depends on anything the cursor knows.

Trying to prove the round trip found two ways the port accepted what it
could not write back: a `\ no newline` or `\ forgotten` line, and a header line, with no
newline after it. Both are refused now, as the Rust parser already did, and
`invalid/unterminated-marker.ops.txt` pins the first in both corpora.

The tests compare both specifications for the ordered examples, and
compare the cursor specification with the implementation for raw reversed
positions, repeated inserts, overlapping deletes and competing errors.
Twenty-seven mutations cover the primitive helpers, lost inserts, a lost trailing
suffix, an overwritten earlier error, a public replay that skips the
digest check, a positional model that drops the trailing gap, an
inclusive deletion endpoint, a script that never advances past what a
block consumed, a positional refusal that ignores a disagreeing quote,
a replacement that consumes nothing, an ordering that admits an insert
inside a deleted run, and four parser relaxations: a delete after an insert
at one position, an operation inside a deleted run, a last delete forgotten
across an insert, and a loop that checks the previous operation but not the
last delete; and six round-trip breaks: a writer that omits the marker
after an unterminated item or swaps a delete's position and count, a
parser that accepts an unterminated marker or header line, a reader that
admits a leading zero, and a count that drops the carry; and three diff
breaks: a backtrack that drops kept lines, a replacement block that swaps
what it deletes and inserts, and a kept line that does not start the next
gap; and a digest cause that ignores forgetting. The proof gate rejects
each at its expected proof location. The script tests run both sides on multi-block
documents: a replacement, an insert and a delete in one document, adjacent
deletions, an insert at a deleted run's end, a second block that disagrees
or runs out of range, and forgotten quotes under a wrong digest.

`check.py` runs the proofs and all three suites on both the default JS and
native C backends, then verifies that deliberate replay mutations fail the
proof gate. Corpus failures now exit nonzero. The runner prints and fixes
the compiler path for each run. The full gate passes on Bend 2.0.20; native compilation of the revision corpus takes a few
minutes on the development machine.

Still unproved is merge convergence. The corpus and oracle comparisons provide
executable checks where those general proofs are still missing. See
[RUNTIME.md](RUNTIME.md) for the C/Rust interop direction and proof boundary.

## What the port found

Checking the ordering assumptions for the cursor proof found a bug shared
by the Rust and Bend parsers: `delete 0 2`, `insert 0`, `delete 1 1` passed
adjacent-operation checks because the insert hid the first deletion's end.
Bend's cursor could then refuse an edit whose positional result is defined.
Both parsers now retain the last deletion across inserts, refusing hidden
overlaps and adjacent deletions. Three shared invalid fixtures and a valid
replacement followed by another edit cover the boundary. That every
parser-accepted document satisfies the ordering predicate is now
`parser_accepts_ordered`; the parser refactor it needed — one ordering
check in `next_op.bounded` instead of one in `next_op.count` and one after
it — changes no result and no message, which the corpus run confirms.

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
