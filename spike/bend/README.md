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
bend main.bend -- log                    # in a folder with a history/, like historica
bend main.bend -- files head
bend main.bend -- cat head notes.txt
bend main.bend -- show kxry
bend main.bend -- check
bend main.bend -- replay history/operations/*/Start/notes.txt history/operations/*/*/notes.txt.ops.txt
bend main.bend -- diff   old.txt new.txt
```

The store commands find the store the way `historica` does — the `history/`
here or above — through two host effects (`store.bend`): `bend main.bend` runs
them as JavaScript, and the native binary calls a Rust static library, linked
by hand because `bend -o` links nothing of ours. `RUNTIME.md` is the boundary;
`check.py` builds both and holds `log`, `files`, `cat` and `show` to the Rust
tool byte for byte.

```console
cargo build --release --manifest-path ffi/Cargo.toml
bend main.bend -o main.c
cc -O3 -w -o historica-bend main.c ffi/target/release/libhistorica_bend_ffi.a -lm -lpthread
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
| `tree.bend` | the file set at a revision: `apply`/`replay` along a chain, `merge` over the graph with decision 0008's contests, and the seven faults a store can contradict itself with | `tree.rs` |
| `store.bend`, `ffi/` | where the store is and what it holds: two effects, a C adapter, a Rust static library | `Store::discover`, `std::fs` |
| `main.bend` | `log`, `show`, `files`, `cat`, `check` over the store it finds; `replay` and `diff` over named files | `cli` |
| `LAWS.bend` / `PROOF.bend` | forty-one claims about the code, each proven | the test suite and Verus replay helpers |
| `replay_spec.bend` | independent position-based replay specification | `spike/verus/replay.rs` |
| `semantic_replay.bend`, `position_lemmas.bend` | positional semantics for an arbitrary insertion, deletion or replacement block; coordinate translation | first semantic replay bridge |
| `composition_lemmas.bend` | a script of blocks, composed: the cursor over a whole document is the positional result | the multi-block theorem |
| `parser_lemmas.bend` | the parser only accepts ordered documents: its per-operation check implies `Block.ordered`, and the parse loop applies it to every operation | the parser theorem |
| `refusal_lemmas.bend` | refusals are justified: every refusal of an ordered document has one of four positional causes, and no cause means the positional result | error soundness |
| `diff_lemmas.bend` | `apply(diff(parent, child)) == child`: the LCS backtrack yields a script that takes the parent to the child, and the runs of that script are blocks the cursor walks to it | `tests/diff.rs` |
| `merge.bend`, `merge_lemmas.bend` | the merge as a model — Eg-walker over Fugue, each event decided on its author's view, elements placed by name — and `merge_converges`: two causal orders of one graph merge to one file | `merge.rs`, `spike/verus/merge_model.rs` |
| `string_lemmas.bend`, `tree_lemmas.bend`, `graph_lemmas.bend` | strings compare as they are, down to the bit; what a revision leaves: one file per path, no link dangling, the kind fixed at the add, a move a drop follows; and the merge a function of each revision's parent set, not its parent order | `tree.rs`'s rules, decisions 0017 and 0040 |
| `equality_lemmas.bend`, `decimal_lemmas.bend`, `spelling_lemmas.bend` | `write(parse(s)) == s`: equality decided down to the bits of a word, decimal numbers spelled as read, and every line the parser consumed written back | `writing_a_parsed_document_reproduces_its_bytes` |
| `cursor_spec.bend`, `replay_lemmas.bend` | forward cursor specification and accumulator/error algebra | refinement of the Bend walk |
| `replay_tests.bend`, `check.py` | oracle comparisons, refusal regressions, proof mutations; JS and native gates | replay tests |
| `corpus_ops.bend`, `corpus_rev.bend`, `corpus_tree.bend` | the corpus, executed | `tests/*.rs` |

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

`corpus_tree.bend`: the `tree`, `links`, `modes` and `whole` chains replay
into the file sets `tests/tree.rs` and `tests/links.rs` assert — paths after
a rename, a link's target through its target's rename, a mode set and unset,
a payload replaced — the three invalid documents the parser accepts are
refused by the tree with `tree.rs`'s own words, the graph merge agrees with
the linear replay on every chain and contests nothing on `merged`, and the
hand-built graphs of `tree.rs`'s unit tests resolve as decision 0008 says:
a drop concurrent with an edit loses and is reported, two concurrent moves
take the lower digest, a later move replaces an earlier one silently, two
files may hold one path, and an undelivered parent is refused.

On a store assembled from each corpus, and on one `historica init` and
`historica record` made, `log` prints what `historica log` prints — order,
abbreviations, marks, counted facts, the message verbatim — `files` the same
file set, `cat` the same content, `show` the same bytes, and a target the
Rust tool refuses is refused in the same words; `check.py` compares the native
binary and the JavaScript build against the Rust tool on six such stores.
`check` names every document by the digest `shasum` prints, and `diff` writes
the operation document the Rust tool wrote, `result` included. `cat` of a
link refuses in the Rust tool's words, naming where it points relative to
where it sits. Not read: bookmarks (`names/`), and a merge's `keep`
resolution, which `cat` refuses rather than guesses at.

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

The merge converges. `merge.bend` is a model of `merge.rs`, not a port of
it: a graph is a list of events in digest order, each with the events its
author had seen and the operations it stated; a walk replays them into one
flat list of elements, each named `(author, minted)` and kept in name
order, with a parent name, a side, and the events that removed it. What an
event does is decided on its *view* — the tree restricted to what its
author had seen, `restrict` — read in order, counted into, and anchored by
Fugue's rule; the actions that come out, attach here or mark that, are
then applied to the whole tree as that event's own. `merge_converges` says
two orders of one graph that are causal — each event once, the same
events, none before an event it had seen — produce one `Merge.merged`,
file or refusal. The proof (`merge_lemmas.bend`) is the argument the
model is shaped for. An event's actions are a function of its view, and
another event it had not seen cannot change that view: its attaches are
by an unseen author and its marks are by an unseen event, and `restrict`
drops both (`restrict_apply`). The actions of two such events commute on
the tree: two attaches are one sorted insertion twice, two marks on one
element are one sorted insertion twice, and a mark never lands on an
element the other event wrote, because a delete's target comes from a
view whose authors the deleting event had all seen (`actions_avoid`). So
the two events commute as steps (`comm`), and any causal order is any
other with concurrent neighbours swapped: the first event of one order is
concurrent with everything before it in the other, so it bubbles to the
front (`bubble`), and induction does the rest (`converge`). Nothing about
the graph is assumed beyond the two orders being causal — not that
`knows` is transitive, not that the tree is well-formed, not even that an
index names an event; a bad index refuses in both orders alike.

The tree keeps its rules. `tree.bend` is a port, so its laws are about
the code the store runs: whatever file set `Tree.apply` is given, a
revision it accepts leaves one where every path names at most one file
(`one_file_per_path`), every `file:` link names a file the tree holds
(`no_link_dangles`), and every file that survives holds the kind it was
added with (`kind_fixed`) — no `move`, `mode`, `link`, `bytes` or second
`add` changes it, which is decision 0017 as a theorem rather than a
sentence. The first two are the checks `apply` runs on its result, so
what the proof adds is that the tree returned is the tree checked: the
path check is last, and the payload stage between the dangling check and
the return restates entries without touching their targets and lands
them in a tree that holds every file the old one held
(`tree_lemmas.bend`: `payloads_keep`). The third follows each stage:
`adds` refuses a file the tree holds, so it never re-kinds one; `moves`,
`modes`, `links` and `payloads` each insert a copy of the entry the
lookup found with its kind unchanged (`kind_insert`), and `drops` only
removes (`kind_remove`). Under all of it is the tree's one data
structure: `lookup` after `insert` finds the entry inserted under its
file and what it found before under any other (`lookup_insert`,
`lookup_other`), which needs strings to compare as they are — `String.eq`
is `Cmp.is_eq` of `String.order`, a string equals itself, and two
strings the comparison calls equal are one string — proven in
`string_lemmas.bend` by induction down to the bits of a `Char`, since
Base defines the comparison and states nothing about it. The same
lemmas give `move_then_drop`: restating an entry and then removing its
file leaves what removing its file leaves. `replay_one_file_per_path`
and `replay_no_link_dangles` carry the first two along a chain from
nothing. Two shapes in `tree.bend` exist for the proofs: `insert` takes
its comparison through `insert.at`, so a proof can split on it, and
`apply` is one def per stage, each taking the last stage's result, so a
proof can open the pipeline one `match` at a time instead of stating
the whole `do`-block's continuation.

The merge reads parents as a set. `merge_parents_unordered` says that
two graphs alike but for the order each revision lists its parents —
the same revisions in the same order, the same digests and facts, the
same parents as a set — merge to one `Merged`, tree and contests both,
whenever either merges at all. The parents reach the merge in two
places, and both are proven to see only the set: whether every parent
was delivered (`graph_lemmas.bend`: `delivered_alike`, through
`Rev.without` being empty exactly when each parent is a member of the
ids), and the ancestor tables, where `closure` unions each parent with
its ancestors and the tables built from alike graphs are alike
(`seen_alike_fuel`) — the same revisions with ancestor lists that are
one set, which is all `is_ancestor` reads, so `replaced`, `concurrent`
and every `decide` come out equal (`decide_all_alike`) and the rest of
the merge never sees a parent. The membership algebra under it —
`append`, `without`, `union_ids`, `closure` — is stated as implications
between `Rev.member` results, since Bend consumes a lambda-bound
hypothesis once and a universally quantified one cannot be passed down
an induction. One shape in `tree.bend` exists for it: `merge` is one
def per stage, as `apply` is. What the law leaves open is the fault: a
refusal names the first undelivered parent, which is the order's.

A merge revision that records nothing changes nothing.
`merge_records_nothing` says an event with no document, walked last,
leaves the file the events before it made — `historica merge` on one
head, or a merge recorded with nothing said about this file — which with
`merge_converges` is what a merge revision may add of its own: nothing.
The walk's step on such an event is the identity by computation; the
proof is the index bookkeeping (`merge_lemmas.bend`: `walk_append`,
`get_last`, `walk_below`), stated of an order whose indices the graph
holds (`Merge.below`), since an index past the end is refused. No
mutation is added for it: the breaks that would fail it — a step that
empties the tree on an empty event, a walk that reads the wrong index —
fail `merge_converges` first. Not proven, and the larger claim: that the walk agrees with plain
application on a chain, which is decision 0007's promise and what
`merge.rs`'s `linear` fast path relies on; that needs the in-order
reading of an `attach`-built tree characterised, and is a model reshaped
for it rather than a lemma file.

What the model is faithful to, and not. Verus's `merge_model.rs` states
the same theorem over `merge.rs`'s own shape — an index tree, anchors
found on the whole tree by filtering for known authors — and proves the
filtered anchor equals the anchor on the restriction (its Lemma A); the
Bend model *defines* the anchor on the restriction and so needs no such
lemma, at the price of being one step further from the code. The tests
hold it to `merge.rs`'s unit tests: concurrent runs at one position do
not interleave, whether written forwards or backwards; ties break by
digest; concurrent deletions agree; a deletion beside a concurrent
insertion keeps the insertion; a merge that records nothing changes
nothing; every topological order of a four-event graph reads the same
file; and a document that contradicts its author's view is refused.
Resolutions (decision 0032) and `contested` are not modelled, as in the
Verus file. The reading carries fuel — one more than the element count,
enough for any tree `attach` built — and positions are unary.

Trying to prove the round trip found two ways the port accepted what it
could not write back: a `\ no newline` or `\ forgotten` line, and a header line, with no
newline after it. Both are refused now, as the Rust parser already did, and
`invalid/unterminated-marker.ops.txt` pins the first in both corpora.

The tests compare both specifications for the ordered examples, and
compare the cursor specification with the implementation for raw reversed
positions, repeated inserts, overlapping deletes and competing errors.
Thirty-nine mutations cover the primitive helpers, lost inserts, a lost trailing
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
gap; a digest cause that ignores forgetting; and six merge breaks: a view
that keeps elements of unseen authors or removals by unseen events, an
element appended rather than placed by name, a removal appended rather than
joined in order, a causal order that lets an event precede its past, and an
action applied as another author's; and four tree breaks: a second `add` of
a file the tree holds accepted, two files at one path not refused, a
dangling reference not checked, and a `mode` that resets the kind; and two
graph breaks: an ancestry closure that keeps only the first parent, and a
readiness that checks only the first. The proof gate rejects
each at its expected proof location. The script tests run both sides on multi-block
documents: a replacement, an insert and a delete in one document, adjacent
deletions, an insert at a deleted run's end, a second block that disagrees
or runs out of range, and forgotten quotes under a wrong digest.

`check.py` runs the proofs and all three suites on both the default JS and
native C backends, then verifies that deliberate replay mutations fail the
proof gate. Corpus failures now exit nonzero. The runner prints and fixes
the compiler path for each run. The full gate passes on Bend 2.0.22; emitting
the C for `main.bend` takes a few minutes on the development machine, and
compiling it seconds.

Every theorem the Verus spike states now has a Bend counterpart. What the
merge law is about is the model in `merge.bend`, held to `merge.rs`'s
tests; the store's merge itself is not ported. See
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
is under 5k. Not ported:

- **Merging** concurrent branches as a command over the store (`merge.rs`
  is modelled in `merge.bend`, not ported: no revision graph is read for
  content, no `contested` report is made — the tree's contests are computed
  and not yet printed), and **resolutions** — the `keep`/`insert` document a
  merge states.
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
