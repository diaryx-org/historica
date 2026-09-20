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
| `LAWS.bend` / `PROOF.bend` | fourteen claims about the code, each proven | the test suite, in part |
| `corpus_ops.bend`, `corpus_rev.bend` | the corpus, executed | `tests/*.rs` |

### What the corpus says

`corpus_ops.bend`: eight valid documents parse and write back byte for byte,
nineteen invalid ones are refused, the three edits in the numbered history
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
- a forgotten item agrees with anything at replay and is nobody's line to
  the diff (`forgotten_agrees`, `forgotten_is_nobodys`);
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

Most hold by computation once a case opens the one opaque value; the
`advance` law is the one real induction. The laws are modest on purpose: the
claims worth the most — that replaying `diff(parent, child)` on `parent` is
`child`, that `write(parse(s)) == s` — are stated by the corpus rather than
proven, because a proof about `String.split` or an LCS table is a much larger
piece of work than the port.

## What the port found

Nothing about the crate's code — the port is held to the corpus and matched
the Rust tool everywhere it was tried. One thing about the crate's *prose*:
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
