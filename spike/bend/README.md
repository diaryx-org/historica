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
python3 reach.py                 # how much of what the tool runs a law reaches
bend PROOF.bend                  # the laws: prints "All terms check."
bend corpus_ops.bend             # the operations corpus, every line `ok`
bend corpus_rev.bend             # the revision corpora, every line `ok`
bend main.bend -- log                    # in a folder with a history/, like historica
bend main.bend -- files head
bend main.bend -- cat head notes.txt
bend main.bend -- show kxry
bend main.bend -- check
bend main.bend -- replay history/operations/*/Start/notes.txt history/operations/*/*/notes.txt.ops.txt
bend main.bend -- diff head             # what a revision did, rendered
bend main.bend -- diff                  # the folder against the head
bend main.bend -- blame head notes.txt
bend main.bend -- blame notes.txt        # the folder's lines, attributed
bend main.bend -- status                 # how the folder differs from the head
bend main.bend -- status --onto left --merge right   # and what joining them contests
bend main.bend -- record --dry-run --move a.md=b.md   # what recording would state
bend main.bend -- record -m "what changed"  # and recording it
bend main.bend -- amend -m "said better"  # rewrite the head, or reword one work stands on
bend main.bend -- abandon tip -m "why"    # supersede a run of work with a tombstone
bend main.bend -- carry tip --onto main   # restate work against another parent
bend main.bend -- name main head        # point a bookmark, and `--delete` one
bend main.bend -- init notes            # make a store in notes/history
bend main.bend -- forget head notes.md --lines 3..4   # destroy two lines' text, everywhere it is quoted
bend main.bend -- opdiff old.txt new.txt # the operation document between two files
```

The store commands find the store the way `historica` does — the `history/`
here or above — through fifteen host effects (`store.bend`): `bend main.bend` runs
them as JavaScript, and the native binary calls a Rust static library, linked
by hand because `bend -o` links nothing of ours. `RUNTIME.md` is the boundary;
`check.py` builds both and holds `log`, `files`, `cat` and `show` to the Rust
tool byte for byte.

They read what the command needs and nothing else, which is the Rust tool's
own arrangement. A store's `revisions/` is the graph and is small, so every
command reads the whole of it and hashes it here, in `sha256.bend`.
`operations/` is where the bytes are — a store of three hundred and seventy
megabytes is three hundred and fifty of payloads — and a file there is opened
only once a revision has named the digest it holds: `Store.at` answers where
the bytes with a digest are, the way decision 0036's catalogue does, and what
comes back is a path whose contents are read and hashed here before anything
is believed about them. Nothing walks the payloads to find a name. `check` is
the exception it is in the Rust tool too: it reports every file, and asks the
host for the digest and the size of each payload rather than carrying fifty
megabytes of PDF through a hash in Bend.

On a real archive — two hundred and sixty revisions, four thousand
documents, three hundred and fifty megabytes of them payloads — that is the
difference between a tool and a demonstration. The native build, against the
Rust tool on the same store:

| | before | lazy | packed hash | sets | parse | split | walk | merge | seen | read | `historica` |
|---|---|---|---|---|---|---|---|---|---|---|---|
| `log` | 138 s | 15 s | 15 s | 5.5 s | 2.2 s | 0.89 s | 0.28 s | 0.28 s | 0.30 s | 0.21 s | 0.01 s |
| `files head` | 140 s | 20 s | 0.03 s | 0.03 s | 0.03 s | 0.02 s | 13.5 s | 0.84 s | 0.50 s | 0.40 s | 0.02 s |
| `cat head Resume.md` | 205 s | 29 s | 0.03 s | 0.03 s | 0.03 s | 0.02 s | 13.5 s | 0.77 s | 0.47 s | 0.39 s | 0.02 s |
| `show <revision>` | 143 s | 2.8 s | — | — | 1.9 s | 0.24 s | 0.25 s | 0.23 s | 0.23 s | 0.15 s | 0.00 s |
| `check` | 146 s | 11 s | 6 s | 5.3 s | 4.9 s | 1.1 s | 0.69 s | 0.69 s | 0.73 s | 0.62 s | 0.87 s |

Wall clock, and near enough all of it user CPU: the store was never the
syscalls. A dash is a column `show` was not measured in. The second column is reading only what a command asks for; the
third is the hash in `sha256.bend` becoming bend-sha256's packed-array one,
which runs at about two hundred and seventy megabytes a second here against
the three of the list-of-bytes hash it replaced. The fourth is `log` counting
what a revision did to the file set through a `Set` of the files it added
rather than walking that list once per fact — a revision that adds a folder
names every file in it twice, and the walk was the listing squared — and
`check` closing over the revisions it has already read and hashed rather than
reading `revisions/` a second time. The fifth is the revision parser's
`unique`, `disjoint` and `subset` asking a `Set` rather than walking one file
list against another — the archive's first revision adds two and a half
thousand files — and `log`'s ordering asking a `Set` of the parents still to
print rather than every revision in turn, which was the count cubed. The
sixth was found by timing the parser's pieces one at a time over that first
revision: one linear pass over its four hundred and fifty thousand
characters costs four milliseconds, and `split_once` — the cut at the first
space that every header, every fact and every operation line goes through —
cost four hundred, because it marked the tail of the string reusable and a
strict `Bool.pick` walked one copy to the end of the line at every
character, so the other copy was made whole each time: a line's length
squared, per line. `split_once.fast` carries the head's test in and stops at
the space; `spelling_lemmas.split_fast` proves it is the `split_once.go` the
laws unfold.

The seventh column is the order `log` prints in. `presentation` asked, at
every step, which of the revisions still unprinted no unprinted revision
names as a parent — and answered it by building a `Set` of every parent they
name and querying it once per revision, from scratch, at each of the two
hundred and sixty-four steps. That is the revision count squared with a
digest's length inside it, and it was a hundred and twenty-four of `log`'s
four hundred milliseconds, more than the parsing. The same order comes out of
one table built once: how many unprinted revisions name each digest as a
parent, decremented as each revision goes out, so a revision joins the
frontier the moment its last child has left it, and only the frontier is
searched for the latest. Kahn's algorithm, in other words, with the walk's
own tie-break. Nothing in `LAWS.bend` reaches `presentation`; the gate it
passes is `check.py` and the same bytes out of `log`, `show`, `files`, `cat`
and `check` as the build before it.

The seventh column was measured on the archive as it stands now — a fifth
again as many revisions as when the earlier columns were taken — with the
previous build re-measured beside it: `log` 0.40 s before and 0.28 s after,
`check` 0.70 s and 0.69 s, `show` unchanged. What the growth shows up is
`files` and `cat`, which the earlier columns had at a fraction of a second
and which now take thirteen and a half. Timing their phases says it is not
the reading or the parsing — those are the same two hundred milliseconds
`log` pays — but `Tree.merge`, and not one piece of it but four, each a walk
of one list for every element of another:

- `gather` kept one `Facts` record per file in a list and walked it for
  every fact it filed: five thousand facts in the archive's first revision
  against two and a half thousand files, three seconds. The table is a
  `Map` now, listed in file order once at the end, and the `bytes` and
  `link` files an `add` asks after are `Set`s: 80 ms. `graph_lemmas`'
  `gather_alike` is restated over the `Map`, and nothing else changes,
  because it never looked inside the table.
- `decide_all` put each surviving file into the tree with `insert`, which
  walks it — and the files arrive in file order, so every one went to the
  end. Each now goes on the front and the tree is turned round once: 0.73 s
  to 75 ms.
- `raise`, decision 0040's fixed point, took one step for every revision,
  and every step asked every buried file whether a surviving link names it,
  walking the tree for each. The first step that raises nothing is the
  fixed point, and it stops there: 5.7 s to 20 ms.
- `path_contests` asked, for every entry, which entries share its path and
  whether that path had been reported yet, walking the tree and the report
  each time: 3.1 s. One pass over the tree sorted by path, stably so that a
  path's files stay in tree order, finds the same runs in 30 ms.

An earlier reading of the profile named only the first; timing each stage
of the merge on its own found the other three, which were two thirds of it. None of
`raise`, `place` or `path_contests` is opened by a proof. The eighth column
is the four, measured beside the previous build: `files` and `cat` go from
thirteen and a half seconds to under nine tenths, `log`, `show` and `check`
are unchanged, and all five print the same bytes as before.

The ninth column is `seen`, the ancestor table, which was a third of a
second of what was left. It was built in rounds: each asked every waiting
revision whether all its parents were in the table yet, walked the table to
answer, and added the ones that were at the end of the round — so a chain
took a round per revision whatever order it came in, and the rounds were
the revision count cubed. It is built in passes now: a revision whose
parents are known goes into the table at once, so the next one in the same
pass can build on it, and the rest wait, turned round, for the next pass. A
chain in descending order takes one pass, and in the reverse order two. The
order is the caller's: `tree` hands the revisions over in the order its
walk from the target reached them, turned round, where it handed over the
store's order — which is by file name, and on the archive, named by
message, took 175 passes. `seen` went from 327 ms to 6; `log`, `show` and
`check` do not reach it, and measure the same within noise.

`graph_lemmas` restates what it proved about the rounds for the passes:
two alike passes — alike tables, alike events waiting, and both having
taken an event or neither — stay alike through one event
(`step_alike`), through a list of them (`pass_all_alike`) and through
`seen.go` (`go_alike`), and `seen_alike_fuel` keeps its statement, so
nothing above it changed. The five lemmas about `ready`, `stuck` and
`seen.add` went with them.

The tenth column is the reading, which every command but `check` paid in
the same measure, a fifth of a second of `log`. Timing it a stage at a time
over the archive: the listing was forty milliseconds, the bytes read, hashed
and decoded forty-five, and the parser ninety.

- `Store.list` handed back every path the store holds, and the revision
  readers kept the tenth of them under `revisions/`. The four hundred
  thousand characters of `operations/` paths crossed the boundary a cell
  each to be thrown away. The effect now takes the directories wanted after
  the root, as `Store.at` takes digests, and `revisions` asks for the one it
  reads: forty milliseconds to three. `check` still asks for both.
- A document's bytes were counted three times — by `doc_of`, by the hash,
  and by the decoder for its fuel — besides the two walks that use them. The
  count is taken once and handed to both: eleven milliseconds.
- A header's value was walked for `starts_with`, reversed for `ends_with`,
  and copied to a list for `any`, to say whether it is padded or holds a
  control character; `scan` answers both in one walk. `is_path` reversed the
  path, split it at every `/` and walked it for a backslash; it is one walk
  that knows what the component so far is. Twenty-five milliseconds. No law
  says which values the revision parser accepts, and the corpus refuses none of
  these, so both were held to the definitions they replace over forty-odd
  edge cases — empty, spaced, `.` `..` `...`, `//`, backslashes, C0 and C1
  controls, non-ASCII — as well as to `check.py`.

`log` goes from 0.30 s to 0.21 s, `show` from 0.23 s to 0.15 s, and `files`
and `cat` by as much, all printing the same bytes as before. What is left of
the reading is the parser's other passes — `facts_ok`'s sets over the first
revision's two and a half thousand files are twenty milliseconds of it —
and the revisions read as lists, at about a hundred nanoseconds a cell,
which is what a cons cell costs here. What is left in `files` besides is
`gather` and `decide_all` at eighty milliseconds each, now linear in the
facts, and the printing, a tenth of a second.

`Ops.diff` — `opdiff` — has its own floor. Its table asked `same` — two lines walked
character by character — of every one of its (n+1)(m+1) cells, so each item
is numbered first, by first-seen order through a `Map`, and the cells compare
numbers; and a cell is a `U32` rather than a `Nat` counted in unary. Two
files of three thousand lines, a third of them changed and five hundred
inserted, natively: 7.6 s before, 1.0 s after, the same document out. What
was left was the backtrack reading it. `cell(tbl, i, j)` walked the table
from its first row and the row from its first column, and the backtrack asks
two of them at every one of its (n+m) steps, so reading the table cost the
table's own size over again — two thirds of the walk, against the fifth the
walk spends building all nine million cells.

An `Array<U32>` table would answer it, but an array is a Type, and a Type
cannot be marked `+` for reuse the way `backtrack` reuses its table. It does
not need one. A backtrack only ever moves to (i-1, j), (i, j-1) or
(i-1, j-1), so the only cells it ever reads are the one it stands on, the one
left of it and the one above it. `Ops.Zip` holds the row and the row above
it, each reversed and cut at the column the walk is at, so all three are the
head of a list; the rows below stay as the table built them, and one of them
is reversed up to that column each time the walk drops a row — paid once per
row where the lookup was paid twice per step. Two files of three thousand
lines, natively: `opdiff` 1.00 s to 0.82 s, and the backtrack itself 0.92 s to
0.37 s.

`diff_lemmas.back` carries the zipper where it carried the table, and moves
it by the same three functions the walk does. It never looks inside either:
the verdict's `up_wins` is generalised as a `Bool` in `back.of`, and the
table was already a free variable, so the restatement is the parameter's type
and `Ops.zip.diag`, `Ops.zip.up_move` and `Ops.zip.left_move` written where
`tbl` stood — no new lemma, and `edits_ok` hands `Ops.zip.start` where it
handed `Ops.table`.

What is left in `Ops.diff` is the table itself, nine million cells of a list of
lists, and `item_at(old, i)` — the parent walked from its first line at every
step, which is now the larger half of what the backtrack spends. The same
zipper would answer it, and that one is not free: `back.of` reads the match
as `same(item_at(old, p), item_at(new, q))` and supplies the equation by
computation, so an item taken from a zipper has to be *proven* to be the item
at the index before the lemma will take it.

```console
cargo build --release --manifest-path ffi/Cargo.toml
bend main.bend -o main.c
cc -O3 -w -o historica-bend main.c ffi/target/release/libhistorica_bend_ffi.a -lm -lpthread
```

## What is here

| File | What it is | Rust counterpart |
|---|---|---|
| `sha256.bend` | SHA-256 over bytes: packs them into words for [bend-sha256](https://github.com/Giulio2002/bend-sha256), imported from BendHub by content hash, and spells the digest; Base has no hash | `sha2` crate |
| `utf8.bend` | bytes ↔ `String`, and reading a file as bytes | `std::str` |
| `text.bend` | lines, fields, canonical numbers, digest spelling | `format::Lines` |
| `ident.bend` | change and file IDs in the `k`–`z` alphabet, spelled and deciphered | `core::{ChangeId, FileId}` |
| `ops.bend` | the operation document: parse, write, replay, and the longest-common-subsequence diff the proofs are about | `format::operations`, `replay` |
| `similar.bend` | the diff the commands draw: `similar` 3.2.0's Histogram, with its preflights, its Myers fallback and heuristics, and the compaction around it, held to the crate on two thousand cases, Myers alone among them | `diff`, the `similar` crate |
| `unicode.bend` | which characters are letters or digits, as Rust's `char::is_alphanumeric` reads Unicode 17 | `char` |
| `folder.bend` | the working copy: `skipped/`'s rules read and matched, the folder walked a directory at a time, what it refuses and why, and what counts as text | `working` |
| `survey.bend` | what `status` says of the folder against the position: facts, refusals, claimed paths, bytes to accept, links resolved against the tree the revision would state, and renames noticed; and what `record --dry-run` adds — the paths named, `--at` and `--move` placing files, a `moved` line, and what recording refuses that `status` describes | `record::survey`, `record::plan` |
| `revision.bend` | the revision document: parse, write; and `History` — heads, superseded, missing parents, change state | `format`, `core` |
| `tree.bend` | the file set at a revision: `apply`/`replay` along a chain, `merge` over the graph with decision 0008's contests, and the seven faults a store can contradict itself with | `tree.rs` |
| `store.bend`, `ffi/` | where the store is, what it holds — `cache/` included, when asked — where a digest's bytes are, or which documents stand in for them, what a file weighs, what one directory of the folder holds, and whether output is a terminal; where a path really is; what time it is and random bytes, each pinnable; and the writes — a rename `record --move` states, a bookmark written, a bookmark or what `forget` destroys removed, `init`'s directories, and a document or a payload filed once: fifteen effects, a C adapter, a Rust static library |
| `naming.bend` | what a record's files are called: a revision under its month and day and its message's first line, cut where a filesystem would balk, and made distinct where another revision has the name; each file of content under that at the path it had; and a timestamp as an instant, for the clock warning | `naming` |
| `notes.bend`, `notes.py` | the four texts `init` writes — `historica.txt`'s note, `skipped/README.txt`, `format.txt` and `cache/README.txt` — taken from what the Rust tool's `init` lays down | `HEADER_NOTE`, `SKIPPED_NOTE`, `FORMAT_NOTE`, `CACHE_NOTE` | `Store::discover`, `store::catalogue`, `std::fs` |
| `bookmark.bend` | a bookmark file's grammar, and which files under `names/` are bookmarks | `store::{Bookmark, Name}`, `check_name` |
| `resolution.bend` | the resolution document: a merge's file stated by `keep` and `insert`, parsed as strictly as the Rust reader parses it | `format::resolution` |
| `standin.bend` | what stands in for a forgotten document (decisions 0014, 0050, 0066): the two headers that stand in for a payload, parsed as strictly as the Rust reader parses them; which of a digest's stand-ins agree in shape with the first of its grammar and how they fold into one, a line forgotten in any being forgotten; what a digest reads as once only stand-ins are left, and what `show` prints of them; and `like`, the relation a replay through a stand-in keeps | `format::payload`, `format::{operations, resolution}::stand_in`, `Store::forgetting` |
| `forget.bend` | `forget`: its arguments; the documents that quote a span — the edit that wrote each line, every delete of it, every resolution that copied it, followed through the walk — and the stand-in written for each; the originals found by their bytes and destroyed, and their copies in `cache/` with them; and every message and refusal | `store::forget`, `cli`'s `forget`, `Store::clear_cache` |
| `forget_lemmas.bend` | what `forget` writes keeps its original's shape and destroys only text, and a replay through it reads the forgotten lines as forgotten and every other line as it was; what it rewrites is the file's own documents, one payload for a file of bytes, and the versions it counts are the others; what it destroys is only what it forgets, in `operations/` and in `cache/`; and it reads its words as their plain reading says | `cli/tests/forget.rs`, `cli/tests/cache.rs` |
| `main.bend`, `commands.bend` | the entry point, which reads the command line and dispatches; and `log`, `show`, `files`, `cat`, `check`, `names`, `diff`, `blame`, `status`, `record`, `amend`, `abandon`, `carry` and `name` over the store it finds, reading what stands in for a forgotten document wherever it reads one, and `init` where there is none, and a resolution assembled from what it keeps; `replay` and `opdiff` over named files | `cli`, `replay::assemble` |
| `LAWS.bend` / `PROOF.bend` | a hundred and eighty-six claims about the code, each proven | the test suite and Verus replay helpers |
| `replay_spec.bend` | independent position-based replay specification | `spike/verus/replay.rs` |
| `semantic_replay.bend`, `position_lemmas.bend` | positional semantics for an arbitrary insertion, deletion or replacement block; coordinate translation | first semantic replay bridge |
| `composition_lemmas.bend` | a script of blocks, composed: the cursor over a whole document is the positional result | the multi-block theorem |
| `parser_lemmas.bend` | the parser only accepts ordered documents: its per-operation check implies `Block.ordered`, and the parse loop applies it to every operation | the parser theorem |
| `refusal_lemmas.bend` | refusals are justified: every refusal of an ordered document has one of four positional causes, and no cause means the positional result | error soundness |
| `diff_lemmas.bend` | `apply(diff(parent, child)) == child`: the LCS backtrack yields a script that takes the parent to the child, and the runs of that script are blocks the cursor walks to it | `tests/diff.rs` |
| `merge.bend`, `merge_lemmas.bend` | the merge — Eg-walker over Fugue, each event, edit or resolution, decided on its author's view, elements placed by name — which `cat`, `diff` and `blame` walk where a merge states no resolution; and `merge_converges`: two causal orders of one graph merge to one file | `merge.rs`, `spike/verus/merge_model.rs` |
| `string_lemmas.bend`, `tree_lemmas.bend`, `graph_lemmas.bend` | strings compare as they are, down to the bit; what a revision leaves: one file per path, no link dangling, the kind fixed at the add, a move a drop follows; and the merge a function of each revision's parent set, not its parent order | `tree.rs`'s rules, decisions 0017 and 0040 |
| `linear_lemmas.bend` | `merge_linear`: on one line of history, each event having seen every event before it, the merge walk reads what plain replay makes | `merge.rs`'s `linear` fast path, decision 0007 |
| `walk_lemmas.bend` | `merge_walk_invariant`: every tree a walk builds keeps the invariant, however concurrent its events; `merge_extends`: an event that had seen everything walked before it leaves what `Ops.apply` makes of its document | `merge.rs`'s walk, decision 0007 |
| `order_lemmas.bend` | `walked_order_causal`: the order `commands.bend` walks a merge in — an insertion sort by how many events each had seen — is causal and holds every event once; `walked_reads_every_order`: so the file the tool reads is what every causal order reads | `merge.rs`'s topological order |
| `similar_lemmas.bend` | `similar_diff_applies`: the document `diff` and `blame` draw from `similar`'s search takes the parent to the child — the search's moves are checked in one pass, and moves that pass are an edit script `diff_lemmas.bend` proves; `Ops.diff` answers any that do not, which the crate's two thousand cases never ask for | `historica::diff` |
| `emphasis_lemmas.bend` | `emphasis_keeps_was`, `emphasis_keeps_now`: emphasis changes no character — a changed line's words are the line, and the runs `similar`'s Myers marks on either side read, in order, as that side's line | `diff`'s emphasis |
| `mark_lemmas.bend` | `emphasis_marks_its_own_line`: every mark emphasis computes falls on its own line — a run of removals replaced one for one pairs each with the arrival at the same place, the runs a mark draws read as the line it is drawn on, and only a removal or an arrival has one | `diff`'s emphasis |
| `sort_lemmas.bend` | string order is total and transitive, and Base's `List.sort` by a name returns its items each no smaller than the one before, with the items under each name the ones it was given, in the order given; and whatever holds of every item any sort is given holds of every item it returns, since a merge only moves what it is handed (`all_sort`, and `all_sort_at` for a test that reads one more value) | `diff`'s pairing |
| `pair_lemmas.bend` | `diff_pairs_each_file`: under any file, the pairs `diff` goes on with are the entries each side holds under it, paired in order as far as either goes — each file compared once with itself where each side holds it once | `diff`'s pairing |
| `folder_lemmas.bend` | `rules_are_well_formed`: every rule a file in `skipped/` states is a path with a value or a name that is one component, not empty and not only `*`; `listing_skips_nothing`: reading a directory's listing adds no file or link a rule in `skipped/` skips, and no directory a rule skips whole, so the working copy's walk takes nothing skipped | `working`, decision 0011 |
| `survey_lemmas.bend` | `walk_refuses_nothing_skipped`: the paths the walk refuses are ones no rule in `skipped/` skips, since a rule is how a person silences one; `status_says_an_arrival_once`: no line of `status` but `added` or `dropped` names a file being added; `status_refuses_what_the_folder_holds`: every path `status` refuses is one its walk refused or one the folder holds something at that the position cannot take, never a path only the position holds; `status_offers_a_rename_the_bytes_make`: each rename it offers is from the one path that left holding some bytes, not nothing, to the one that arrived holding them; `record_refuses_a_dangling_link`: `record` refuses exactly where a link of the position names a file it drops and is neither going nor restated; `record_states_a_kind_only_for_an_arrival`: a stated kind goes through exactly where it names a path looked at that no file of the position holds; `record_moves_each_file_once`: one `move` line per file moved, none for a file going, at the last place the renames put it; `record_names_only_what_is_there`: every path named answers to a file of the folder, the position or the renames; `a_rename_keeps_each_file_once`, `a_rename_puts_each_file_where_it_was_said`: `--at` and `--move` leave the position's files each once, at the last place one put it and every other where it was; `record_refuses_only_what_it_looks_at`: whatever the folder and the store answer, a record restricted to some paths refuses only among them; `record_goes_on_where_each_path_holds_one_file`: where `record` goes on, no path it looks at holds two files, since the survey claims every path several files hold; `record_plans_in_file_order`, `record_plans_every_file`: it plans from the position in file order, each file's entries as they were; `a_link_refers_only_to_what_the_revision_states`: a link is written as a reference only where its target lands on a path the revision states; `a_link_resolves_inside_the_folder`: and a link at a path the format holds resolves, if at all, to a path that is not absolute and never climbs out with `..` | `working::walk`, `record::survey`, `record::plan` |
| `status_lemmas.bend` | `status_reads_its_words`: `status` reads its arguments as their plain reading says — the word after a flag is its value, the last `--onto` counting and every `--merge` kept in the order given; `status_joins_held_revisions`: every revision it joins — what `--onto` and each `--merge` resolve to, and the head where it is taken — is one the store holds, through a lemma that Base's `List.sort`, by any order, returns only what it was given; `status_says_what_it_found`: everything the survey found is in the report, in the order found, each on a line of its own naming it — a fact beginning with its kind and ending with its path, a refusal, a claim or an accept beginning with its word and its path; `status_says_each_contest`: where work is joined, each contest the tree merge found but a path several files claim is said once, in its order, on a line naming the file contested by the first eight characters of its name, and where one revision or none is the position, none; `status_compares_with_the_revisions_tree`: against one revision, the folder is compared with the tree `files`, `cat` and `diff` read there; `status_reads_only_lines`: every path it asks the host to read and every file it replays is a file of lines it compares; `status_leaves_a_disputed_file_unsettled`: where the parents being joined leave a file of lines differently, what the survey says of its path, whatever the folder holds, is that a file there is edited, emptied or refused, never unchanged, and that a link or nothing there drops it with no content an arrival could be matched to; `status_believes_what_is_stated`: against one revision it is refused only where a file no statement settles cannot be replayed, and with that refusal; `status_joins_what_it_reads`: joining, each file it compares is paired, in order, with what the parents' readings of it join to — the digest every parent that mentions it reads, the empty digest where none does, and `-` where two read it differently | `status`'s arguments, parents and report |
| `naming_lemmas.bend` | `a_revision_is_filed_under_its_month`: a revision's stem is its month, a `/`, and one name holding nothing a filesystem reserves, whatever its message; `a_summary_fits_its_limit`: the summary is sixty characters at most; `a_summary_gives_up_its_ends`: it neither begins nor ends with a dot or a space; `content_is_filed_under_a_name_a_filesystem_holds`: each file of content is filed under a name with no control character; `record_compares_with_the_latest`: the timestamp the clock is checked against is one the store holds and none is later; `abandon_takes_a_reason_that_says_something`: a reason is taken exactly where it is not all whitespace | `naming`, `abandon`'s reason |
| `name_lemmas.bend` | `name_stays_in_names`: a name `name` takes is never absolute and never climbs out with `..`, so the bookmark's file is under `names/` — every refusal `check_name` and the path rules make stepped past to the two a climbing name would meet; `name_reads_its_words`: `name` reads its words as their plain reading says, a field at a time; `name_does_what_it_reads`: a deletion only where `--delete` was said, of the one other word, with nothing shaping a target, and otherwise a bookmark set of the other words in order, never a file pinned; `name_points_where_asked`: the bookmark set has the name given and points at a revision, a change or a file the store holds, as asked, as private as asked or as it was; `name_deletes_the_bookmark_named`: `--delete` is refused exactly where no bookmark has the name, and otherwise reports the store's bookmark of that name; `name_states_what_it_set`: `--fields` says its header once, early or late, and then `name` | `store::check_name`, `name` |
| `listing_lemmas.bend` | `files_lists_in_path_order`, `files_lists_the_tree`: `files` prints the tree's entries sorted by path and file, under each the ones the tree holds, each line ending with its file identifier; `bookmarks_read_in_name_order`, `names_lists_each_bookmark`: the bookmarks are read in name order and `names` prints a line for each, beginning with its name; `names_resolves_to_held`: a revision pin or a change resolves to an abbreviation of a revision the store holds, or a reason in parentheses; `log_fields_lists_what_it_keeps`: `log --fields` prints its header and a line per revision it keeps, beginning with its digest; `log_counts_each_fact`: an entry counts each `add`, `move`, `drop` and `edit` fact once; `log_follows_a_held_file`: the file `--path` follows is one the tree holds where it is read | `files`, `names`, `log`'s printing |
| `record_lemmas.bend` | `record_reads_its_words`, `rewrite_reads_its_words`: `record`, and `amend`, `abandon` and `carry`, read their words as their plain reading says — each word a flag and what it says, the last `-m` and `--onto` counting, each `--merge`, `--at`, `--move`, `--bytes` and `--lines` in order, every other word a path or the target; `record_restricts_no_merge_and_no_half_rename`, `record_names_only_what_is_there`, `record_gives_kinds_only_to_files`, `record_moves_only_held_files`: a restriction is no merge and takes both ends of each rename, every path named answers to something, every path given a kind is a file the folder holds, and every file a stated rename moves is one the position holds; `record_writes_only_what_is_settled`, `record_says_an_arrival_once`, `record_reads_lines_as_text`: what it goes on to write is a plan the survey settled, whose dry run names an arriving file on its `added` line alone, and a file `--lines` names is text; `record_states_the_folder`, `record_reads_the_position`: an edit it states replays the position's lines to the folder's, text is the folder's bytes and a payload is named by their digest, the position's lines being the store's replay of each file it edits; `record_names_what_it_writes`: each arrival is added under the identifier minted for it, the revision is named by the digest of its text and filed under the name its moment, message and change compose, and each bookmark moved names a parent's change | `record`'s arguments, survey and writing |
| `rewrite_lemmas.bend` | `carry_keeps_what_it_restates`: every revision a carry plans keeps the change, author, moment and message of the one it supersedes, supersedes that one alone, and is named by the digest of its text; `abandon_takes_a_line`, `abandon_asks_for_a_revision_and_a_reason`, `abandon_dry_run_names_the_run`: `abandon` takes a line of work nothing has rewritten, each revision after the first standing on the one before it alone, is asked for a target and a reason that is not blank, and a dry run begins by naming each revision of the run, in order; `reword_changes_only_the_message`: a reword's message is the one `-m` gave and not the old one, and with the old one put back it says what the revision said; `amend_rewrites_a_held_revision`, `carry_carries_a_held_revision`, `amend_keeps_what_it_added`: what `amend` and `carry` act on is a revision the store holds, and an amendment gives every arrival an identifier, each file it added keeping its own; `writes_say_what_they_wrote`: with `--fields` all four writing commands say `historica-wrote-1` and then each revision they wrote once, in digest order | `amend`, `abandon`, `carry`, decisions 0013, 0023, 0059 and 0074 |
| `PROOF.bend` (`replay`) | `replay_keeps_a_refusal`: once a document in the chain is refused, nothing after it — a payload included — makes the chain a file; `opdiff_replays_to_the_child`: the document `opdiff` finds between two files, applied as `replay` applies one, makes the second | `replay`, `opdiff` |
| `target_lemmas.bend` | `target_is_held`: every target — a bookmark, `head`, a digest prefix or a change prefix — resolves to a revision the store holds; setting a key in Base's `Map` never invents a value, so the history heads and changes are read from holds only the store's revisions | `target::resolve` |
| `log_lemmas.bend` | `log_lists_what_it_asks`: every revision `log` lists satisfies every filter asked of it, whatever the limit | `log`'s filters |
| `fileat_lemmas.bend` | `file_is_held`: a file argument — a path, `path:` and a path, `file:` and a file bookmark or an identifier's prefix — names a file the revision's tree holds | `target::file_in` |
| `laid_lemmas.bend` | `laid_keeps_parent`, `laid_reads_child`: the lines `diff` renders and `blame` overlays are both sides — context and removals are the parent, whatever the document, and context and arrivals are the child wherever the document applies | `diff`'s hunks, `blame`'s overlay |
| `hunk_lemmas.bend` | `diff_hunks_apply`: the hunks `diff` groups a comparison into — each run of lines within three of a change — read back as `patch` reads a unified diff, without fuzz, take the parent to the child: each found where its header says on both sides, its lines the parent's there, its counts right | `diff`'s hunks |
| `blame_lemmas.bend` | `blame_shows_the_folder`: `blame <path>`'s rows are the folder file's lines, each once and in order, whatever history holds — built on `similar_diff_applies` and the layout laws | `blame`'s folder overlay |
| `blamed_lemmas.bend` | `blame_reads_the_walk`: `blame <target> <path>`'s rows, read without their authors, are the file the walk of the target's ancestry reads; `blame_numbers_its_lines`: `blame` numbers each line as the file does, and prints exactly the lines whose number falls in the span asked; `blame_prints_each_line`: each line it prints ends with the line it attributes, in order, with the marker after a line without a newline; `blame_reads_the_position`: `blame <path>` compares the folder with a revision the store holds, and the file it names is one that revision holds, or none is at the path; `blame_reads_a_held_file`: `blame <target> <path>` reads a revision the store holds and a file with lines its tree holds; `blame_prints_the_walk`, `blame_prints_the_folder`: what either form prints is one line for each line of the span, ending with it — of the file the walk reads, or of the folder's text; `blame_reads_its_words`: `blame` reads its arguments as their plain reading says — the last `--lines` value is the span, and the other words are the target and the path, in order; `blame_reads_a_folder_file`: `blame <path>` reads a file the folder holds at the path rather than a link, with the kind the position gives it | `blame`'s attribution |
| `diffcmd_lemmas.bend` | `diff_reads_its_words`: `diff` reads its arguments as their plain reading says — `--onto` and `--color` take the word after them, `--color=` spells a colour in the word, the last of each counting, and the other words are the target and the path, in order; `diff_compares_with_the_parent`, `diff_folder_compares_with_a_held_revision`: the other side is what `--onto` names, a revision the store holds, or else the target's one parent or the head; `diff_limits_to_a_held_file`, `diff_folder_limits_to_a_held_file`: a file a comparison is limited to is one the tree it was named at holds; `diff_shows_what_differs`: `diff` shows only files whose two sides differ, and under a path limit only a file at that path on one side; `diff_folder_keeps_what_the_limit_wants`, `diff_folder_shows_what_differs`: over the folder, only paths the limit wants, and of those only ones whose sides differ | `diff`'s arguments, sides and files |
| `colour_lemmas.bend` | `diff_colour_changes_no_character`: every line `diff` renders is kept as runs, and what it renders with colour, read without it, is line for line what it prints without colour — a marked line is its sign and its runs, and every mark reads as its own line | `diff`'s colour |
| `plan_lemmas.bend` | `diff_folder_replays_what_is_unsettled`, `diff_folder_reads_what_is_unsettled`: over the folder, `diff` replays exactly the files of lines no statement settles, and reads exactly the regular files nothing at the position settles — never a file of bytes or a link the position holds | `diff`'s reading of the folder |
| `chain_lemmas.bend` | `chain_follows_first_parents`: the line a file's nearest statement is looked for along begins at the position and follows first parents, each a revision the store holds, and stops where that line does — after a revision with no parent or a first parent the store does not hold, or at once of a name it does not hold — or else after 1 + n revisions of a store of n | the first-parent line |
| `sizes_lemmas.bend` | `diff_sizes_what_the_host_stated`: sizing what `diff` compares changes no side but a file of bytes whose size was unknown, which keeps its digest and has a size only where the host's line for the bytes it found names that very digest | `diff`'s sizes |
| `fetch_lemmas.bend` | `diff_fetches_what_it_replays`, `diff_folder_fetches_what_it_replays`: every document a revision states for a file `diff` replays is among those it fetches; `reading_fetches_what_resolutions_keep`: so is every document a resolution among them keeps; `diff_folder_fetches_the_edits_it_believes`: over the folder, so is the `edit` whose result could settle a file; `diff_asks_every_payload_it_shows`, `diff_stats_where_each_payload_was_found`: the host is asked about every payload shown, each once, and its stat only where it located that payload — through `List.sort` and `distinct` keeping every item | what `diff` asks the store and the host |
| `fulls_lemmas.bend` | `revisions_read_are_their_documents`: every revision a command reads is one a document of `revisions/` spells, under the digest it is known by, byte for byte as `Rev.write` writes what the revision says | `Store::revisions` |
| `span_lemmas.bend` | `log_lists_its_span`: every revision `log` goes on with is one the store holds; with a target, the target is among them wherever the store holds it and every other is a parent of one of them, through an invariant of the walk out from the target — in a store without a cycle, only the target's ancestry; with `a..b`, `a` is never among them, and each is `b` or a parent of one `log b` lists | `log`'s ranges |
| `logargs_lemmas.bend` | `log_reads_its_words`: `log` reads its arguments as their plain reading says — the word after a flag that takes a value is its value, the last counting, `--limit`, `--since` and `--until` read as a count and bounds, `--fields` asked for if it is there, and the other word the target | `log`'s arguments |
| `check_lemmas.bend` | `check_pairs_each_payload`: `check` reports each payload with the digest asked for it — one per payload in the listing's order, none taken by a revision or an operation document; `check_refuses_what_does_not_parse`: it calls a document refused exactly where it does not parse | `check` |
| `show_lemmas.bend` | `cat_reads_a_held_file`: `cat <target> <path>` reads a revision the store holds and a file its tree holds that is not a link; `show_names_a_held_file`, `show_prints_a_held_document`, `show_prints_what_the_revision_states`: `show` names a file the target holds, and prints a document the store holds under the digest named — the revision's own, or the one it states for the file | `cat`, `show` |
| `bookmark_lemmas.bend` | `bookmark_reads_back`: the file the Rust tool writes for a bookmark — the target line, and `private` where the name stays out of an export — parses back as that bookmark wherever its identifier is spelled as its kind is | `store::Bookmark` |
| `abbrev_lemmas.bend` | `abbreviation_is_a_prefix`, `abbreviation_names_one`: the short digest `log` and every message print is a prefix of the digest, and no other digest of its length starts with it | `log`'s abbreviations |
| `view_lemmas.bend` | `view_keeps_invariant`: every author's view of a walked tree — the tree restricted to a set holding the past of each of its events — keeps the invariant, since it is the tree that set alone walks to; `merge_intent`: an event that had seen part of a history reads, in its own view, its document applied to what it saw | `merge.rs`'s view, decision 0007 |
| `anchor_lemmas.bend` | the reachable-state invariant of a view and one insertion landing at the visible gap it asked for, tombstones or not | `merge.rs`'s anchor, Fugue's rule |
| `equality_lemmas.bend`, `decimal_lemmas.bend`, `spelling_lemmas.bend` | `write(parse(s)) == s`: equality decided down to the bits of a word, decimal numbers spelled as read, and every line the parser consumed written back | `writing_a_parsed_document_reproduces_its_bytes` |
| `revision_lemmas.bend` | `write(parse(s)) == s` for revision documents: validation sorts the headers by rank, and sorted headers are what `write` spells | the revision round-trip tests |
| `cursor_spec.bend`, `replay_lemmas.bend` | forward cursor specification and accumulator/error algebra | refinement of the Bend walk |
| `replay_tests.bend`, `check.py` | oracle comparisons, refusal regressions, proof mutations; JS and native gates | replay tests |
| `corpus_ops.bend`, `corpus_rev.bend`, `corpus_tree.bend` | the corpus, executed | `tests/*.rs` |

### What the corpus says

`corpus_ops.bend`: nine valid documents parse and write back byte for byte,
twenty-two invalid ones are refused, the three edits in the numbered history
replay to the hand-written states in `states/` (held to `result` where one is
stated), and the four `diffs/` fixtures — a replacement anchored at the
removed run, a surviving line between two rewrites, a final newline gained
and lost — are what `diff` writes, byte for byte. `check.py` holds the
`opdiff` command to the same four, on both builds, from the files to the
bytes it prints.

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
binary and the JavaScript build against the Rust tool on sixteen such stores.
Every revision a command reads is one a document of `revisions/` spells,
under the digest it is known by, and what `Rev.write` writes of it byte for
byte (`revisions_read_are_their_documents`).
`check` names every document by the digest `shasum` prints, and `opdiff`
writes an operation document the Rust tool reads, `result` included. `cat` of a
link refuses in the Rust tool's words, naming where it points relative to
where it sits.

Bookmarks are read as the Rust tool reads them (`bookmark.bend`): every file
under `names/` whose path is a name, in name order, and a file that is not one
line and at most `private` after it refuses every command, naming the file.
A bookmark wins as a target over any other spelling, `head` included; a pin
must be here, a change must have one current revision, and a file bookmark is
refused as a target in the Rust tool's words. The path position takes `file:`
and a file bookmark or an identifier's prefix among the files at that
revision, and `path:` for a file whose own name begins `file:`. `names` prints
each bookmark and where it resolves — a file bookmark to where the file sits
in what the current heads say together — and a list of heads names the
bookmarks on each. `check.py`'s `names` store is pointed by the Rust tool's
own `name`, with a `head` bookmark and two that point at nothing here.

`log` takes what the Rust tool's takes: `--limit`, which counts what the
filters left; `--author` and `--grep`, which ask whether the author line or
the message holds the text; `--since` and `--until`, which bound the wall
clock each author read, in their own offset, a bare date being that whole
day; `--path`, which reads the path once, at the revision named or the one
head, and then follows the file through its renames; `<from>..<to>`, what
`<to>` has behind it and `<from>` does not; and `--fields`, the
`historica-log-1` listing; whatever the filters, it goes on only with
revisions of the store its span names — the target wherever the store
holds it and parents of what it lists, and of `a..b` never `a`
(`log_lists_its_span`). A timestamp is held to the calendar now — a leap
day only in a leap year, no sixtieth second, and `-00:00` refused as the
unknown offset — which is what the Rust parser always did, for a revision's
`when` as for a bound. A usage error says what the Rust tool says, with the
same exit code, and not the Rust tool's usage text after it.

A merge's resolution (`resolution.bend`, decision 0032) is the file stated
whole: `keep` runs of the items a document minted — an operation document's
inserts, an earlier resolution's, or a payload's lines — and `insert`s of
its own. Where an `edit` names one, `cat` fetches the documents it keeps
from, assembles the pieces, and holds the result to the digest the
resolution states, refusing in the Rust tool's words a document that is not
here, a run past what one mints, an unterminated line before the last, and
a result that disagrees. `check.py`'s `merge` store is two merges the Rust
tool resolved, and six written by hand to fail each way.

`diff <target> [<path>]` renders what a revision did, and `--onto` what one
revision holds against another: the facts about each file first — new,
deleted, renamed, a mode, a link's target — then its hunks, three lines of
context around each change, or the digest and length of a file of bytes;
`blame <target> <path> [--lines <first>..<last>]` names the change, author
and day that wrote each line. Two sides hold the same content for a file
where the same revisions stated it, so only the files that differ are
replayed, and for each of those everything a revision states of it is
fetched first (`diff_fetches_what_it_replays`), with whatever a resolution
among them keeps (`reading_fetches_what_resolutions_keep`). A file of bytes
is shown with the size the host gives it: every payload shown is asked
about (`diff_asks_every_payload_it_shows`), its stat only where the host
located it (`diff_stats_where_each_payload_was_found`), and a size is
believed only where the bytes found there hash to that very payload,
sizing changing nothing else (`diff_sizes_what_the_host_stated`). What is laid over the
parent is what the Rust tool lays:
`similar`'s Histogram diff, recomputed, which `similar.bend` ports whole —
the preflight that answers two long, nearly disjoint sides with one
replacement, the search for a rare shared run, the Myers search it falls
back to where every shared line is common (with Myers' own preflight, its
heuristics, and its exact search where one side is small), and the
compaction that slides each run of changes to where it groups. `check.py`
holds it to the crate on two thousand cases drawn to reach every one of
those paths, and the document written from what it finds is proven to
take the parent to the child (`similar_diff_applies`), and on the archive `diff head --onto` an early revision prints
the Rust tool's 2,479 lines byte for byte. What it prints of that document,
`patch` reads back (`diff_hunks_apply`): read as a unified diff without
fuzz, each hunk is found at the line its header names on both sides, its
context and removals are the parent's lines there, its counts are the
lines each side holds, and the hunks take the parent to the child. The
files compared are paired by name (`diff_pairs_each_file`): each side is
sorted with Base's `List.sort`, proven to return every entry in order
(`sort_lemmas.bend`), and walked together, so a file each side holds once
is compared once, with each side's entry for it.

With no target, both read the folder beside the store (`folder.bend`),
walked as the working copy is: everything is tracked but `history/` itself,
what a rule in `skipped/` keeps out — a path, a directory, a name with `*`s
in it, or a directory's name, filed flat or in folders of their own — and a
path the format cannot hold. `diff` compares it with the head, or with what
`--onto` names, a path or `file:` limiting it to one file; the folder has
no identifiers, so a file that moved there is a loss and an arrival. A file
the position holds as lines must still be text, and one it does not is
lines or bytes as decision 0017 sniffs it. `blame <path>` attributes the
folder's lines as far as history can and marks the rest `(the folder)`. A
file of lines is read only where the host's digest of it is not the one its
nearest statement on the head's first-parent line leaves, so `diff` over
the archive's folder takes 1.4 s. What it replays is exactly the files of
lines no statement settles, and what it reads of the folder exactly the
regular files nothing at the position settles, never one the position holds
as bytes or a link (`diff_folder_replays_what_is_unsettled`,
`diff_folder_reads_what_is_unsettled`); the line the statements are read
along follows first parents from the position to where that line ends
(`chain_follows_first_parents`);
and what a replay needs, and the `edit` whose result could settle a file, are
fetched before (`diff_folder_fetches_what_it_replays`,
`diff_folder_fetches_the_edits_it_believes`). A statement settles a file
only while every document its content was made of is here: where a
forgetting destroyed one, no digest any document states is the file's, and
it is replayed through what stands in. A malformed rule in `skipped/` refuses
every command, in the Rust tool's words, as a malformed bookmark does.

`status` says how the folder differs from the head, or from what `--onto`
names, as `record::survey` finds it: each path `added`, `dropped`,
`edited`, or given a `mode` or a `link` target the position does not
state; the paths nothing here can take, `refused` with why — a pipe, a
name with space at an end or a control character, a link whose target is
not UTF-8 or begins with `file:`, a file of lines no longer text; and a
dropped path and an added one holding the same bytes, one to one, offered
as a `--move`. A link's target is resolved as the recorder resolves it,
against the tree the revision would state, so a target spelled another way
to the same file says nothing and one pointing at an arrival is a
reference. Where `--merge` names revisions being joined, the position is
all of them, merged, and `status` says what the merge decided by rule
rather than by agreement: a file one side dropped and the other kept, a
file moved two ways, bytes stated whole on both sides, a mode or a link
target set two ways — the tree's contests, which `tree.bend` computes and
which were not printed until now. A file of lines the parents leave
differently is `edited` whatever the folder holds, since the merge owes it
a resolution. What the renderer's marker lines leave standing in such a
file (`marked`) is not reported: that needs the content contests
`merge.bend` does not model.

What the reading commands and `status` print is decided before anything
is printed: each builds its lines — an entry of `log`, a line of `files` or
`names`, the report `status` makes of its survey — and one `print_lines`
prints them, so a law can read what they say, and `check.py` holds the
same bytes. `files` lists each file of the tree once, in path order;
`names` lists every bookmark in name order, and says where a pin or a
change resolves as a revision the store holds; `log --fields` names each
revision it keeps by its digest, an entry counts each fact once, and
`--path` follows a file the tree holds. `status` says everything its survey
found, each on a line naming it, and where work is joined each contest but
a claimed path once, naming its file; against one revision it compares the
folder with the tree `files` reads there; it reads and replays only files
of lines, believes a digest a statement gives, and is refused only where a
replay is; and joining, it compares each file with what the parents'
readings of it join to, and settles none they read differently. What no law reaches
is the IO itself — the order of the effects each command performs. A
refusal before any effect is a `die`, which halts at once, so a law could
say a wrong command line does nothing; but the proof would rest on the
foreign effects the IO value names, and the gate would no longer print
`All terms check.` alone.

`record --dry-run` is the first of the writing commands, less the writing:
it prints what `record` would state — the lines `status` prints, and a
`moved` line for each file a person moved — or the refusal `record` would
stop at, in the order the Rust tool asks. The paths named narrow what is
looked at, a directory covering what is beneath it; `--at` puts each file
several claim somewhere of its own; `--bytes` and `--lines` say what an
arriving file is; `--accept` takes the folder's bytes where the parents
being joined stated different ones. What is refused: a merge restricted to
some paths, one end of a rename left out of them, a named path nothing
answers to or a rule keeps out, a kind stated for a file already recorded,
for one not looked at or not there, or `lines` for bytes that are not
UTF-8, a link not looked at whose target is going, a path several files
still claim, what nothing here can take, a merge that empties a file, and
contested bytes accepted or not. And `--move` renames in the folder before
anything is read, as the Rust tool does, dry run or not — through
`Store.move`, which renames and answers which of the four cases the folder
was in. `check.py` runs each `record` on a
copy of the store of its own, per tool, and compares the folder after as
well as what was said: 90 commands across fourteen stores, one of them
`claimed`, built for the merge refusals — two files added at one path,
settled with `--at` by file bookmark, bytes written two ways, and a link to
a file the folder dropped. A usage error is now compared too, to the end of
its message.

`record` writes, too, where no merge is being recorded. It mints an
identifier for each file arriving, in path order, then the change's; says
what each file holds now — a new file of lines as its text, a file edited
as the operation document `Ops.diff` finds between the position's content
and the folder's, a file of bytes as a payload — with a `mode` line for a
file arriving that can be run, and each link spelled `file:` and the
identifier where its target resolves to one file of the tree the revision
states; writes the revision, in the order the format fixes; files the
content under the revision's stem, at the path each file had, and none the
store already holds; and moves each bookmark naming a parent's change on to
this one, private or not. What it prints is what the Rust tool prints — or,
with `--fields`, `historica-wrote-1`, the revision and the bookmarks — and
before any refusal but a usage error the header goes out first, whenever
`--fields` is among the words, which is the Rust tool's own test. Before it
surveys it asks who is recording, what time it is, and why, in that order:
a clock behind the newest work the store holds is said on standard error,
and a revision that would state nothing is refused.

The time and the identifiers are the two things decision 0010 made inputs,
and they are what made this comparable. The Rust command line takes them
as arguments now too, and `historica-pinned` — a test build of it, never
installed, behind a `pinned` feature — fixes both from
`HISTORICA_PINNED_NOW` and `HISTORICA_PINNED_SEED`; the port's host reads
the same two. So `check.py` gives both writers one moment, one seed and one
author, and compares the whole store each leaves byte for byte, less the
Rust tool's `cache/`: the revision's name and bytes, every file of content
and where it was filed, and every bookmark. Its `recording` store was
recorded by `historica-pinned` too, and has every kind of file arriving,
edited, going, renamed, run and pointed at; a message another revision of
the same day already has, one that is nothing a filesystem will take, and
one cut between words; twins, and a file whose bytes the store already
holds; a clock behind the store; an author the format cannot hold; and a
record of nothing — twenty-one records there and four more on the `fresh`
store, the first a store has.

The laws hold the survey and the names to what a person relies on. What
`status` refuses is only what the folder holds, never a path only the
position holds (`status_refuses_what_the_folder_holds`), and a rename it
offers is from the one path that left holding some bytes to the one that
arrived holding them (`status_offers_a_rename_the_bytes_make`). What
`record` plans names only what is there (`record_names_only_what_is_there`)
and, restricted to some paths, refuses only among them, whatever the folder
and the store answer (`record_refuses_only_what_it_looks_at`); it states a
kind only for a file arriving (`record_states_a_kind_only_for_an_arrival`),
goes on only where each path it looks at holds one file
(`record_goes_on_where_each_path_holds_one_file`), writes a link as a
reference only to a path the revision states
(`a_link_refers_only_to_what_the_revision_states`), and one never outside
the folder (`a_link_resolves_inside_the_folder`),
refuses a link left dangling exactly where one would be
(`record_refuses_a_dangling_link`), and writes one `move` line per file,
at the last place the renames put it (`record_moves_each_file_once`) —
which is where the position it goes on with has the file, with every other
where it was and none lost or doubled
(`a_rename_puts_each_file_where_it_was_said`,
`a_rename_keeps_each_file_once`). A revision's stem is its month, a `/`,
and a name holding nothing a filesystem reserves
(`a_revision_is_filed_under_its_month`), its summary sixty characters at
most (`a_summary_fits_its_limit`) and never beginning or ending with a dot
or a space (`a_summary_gives_up_its_ends`); each file of content is filed
under a name with no control character
(`content_is_filed_under_a_name_a_filesystem_holds`); the clock is checked
against the latest work the store holds
(`record_compares_with_the_latest`); and `abandon` takes a reason exactly
where it is not all whitespace
(`abandon_takes_a_reason_that_says_something`).

`amend`, `abandon` and `carry` write too, and are held to
`historica-pinned` the same way. `amend` of a revision nothing stands on is
`record`'s survey against that revision's parents, keeping its change, its
author and its moment, the renames it stated as `--at`, the kind of each file
it added, and the identifiers it minted — only a path it did not add gets a
new one; of a revision work stands on it is a reword, the message alone.
`abandon` supersedes a run of work, a line from the revision named to its
tip, with a tombstone of a newly minted change that states nothing, and
moves each bookmark on the run's changes to it; `--only` abandons the one
revision. Both refuse a second rewrite of one revision, and each thing
0013, 0023 and 0059 refuse, in the order the Rust tool meets them.

What stands on a rewrite is carried in the same act, and `carry` is that
restating as a command: with no target it repairs every revision standing
on a rewritten one, and `--onto` moves one revision onto another parent,
with the person's reading of the clock. A file whose base did not move is
named unchanged. One whose base moved is put through the merge walk
`LAWS.merge_converges` is about, as three events — the old base, the delta
to the new one, and the revision's own document — and restated as the
document from the new base to what the walk reads; where the delta and the
revision's own work meet, `commands.bend` counts the
contested regions as `merge.rs` does — siblings two authors placed
unaware of each other, a removal beside concurrent work, each counted over
the run its author wrote, and a missing terminator — and refuses, naming
how many. The `rewriting` store has a line of four revisions and two lines
beside it, and holds sixty-odd commands to the Rust tool's bytes: runs and
single revisions abandoned, rewords carrying a stack and an amendment the
folder speaks for, moves that restate cleanly and ones that meet, and every
refusal; `stranded` has a tombstone that arrived without the carries it
forced, and `carry` repairs it.

What the four writing commands decide is pure, and the IO shells open,
draw, write and print what they are handed. `record` reads its words as
their plain reading says (`record_reads_its_words`), as `amend`, `abandon`
and `carry` read theirs (`rewrite_reads_its_words`). A restriction is no
merge and takes both ends of each rename
(`record_restricts_no_merge_and_no_half_rename`), every path named answers
to something (`record_names_only_what_is_there`), every path given a kind
is a file the folder holds (`record_gives_kinds_only_to_files`), and every
file a stated rename moves is one the position holds
(`record_moves_only_held_files`). What it goes on to write is a plan the
survey settled (`record_writes_only_what_is_settled`), whose dry run names
an arriving file on its `added` line alone (`record_says_an_arrival_once`),
and a file `--lines` names is text (`record_reads_lines_as_text`). What it
states each file holds is what the folder holds — an edit is the document
`Ops.diff` finds, which replays the position's lines to the folder's
(`record_states_the_folder`), the position's lines being the store's
replay of each file it edits (`record_reads_the_position`) — and what it
writes is named as it says: each arrival under the identifier minted for
it, the revision under the digest of its text and the name its moment,
message and change compose, and each bookmark it moves one on a parent's
change (`record_names_what_it_writes`). An amendment rewrites a revision
the store holds (`amend_rewrites_a_held_revision`) and keeps the
identifiers it minted (`amend_keeps_what_it_added`); a reword changes the
message alone (`reword_changes_only_the_message`). `abandon` is asked for a
target and a reason that is not blank
(`abandon_asks_for_a_revision_and_a_reason`), and takes a line of work
nothing has rewritten, each revision after the first standing on the one
before it alone (`abandon_takes_a_line`), which a dry run begins by naming,
in order (`abandon_dry_run_names_the_run`). A carry acts on a revision the
store holds (`carry_carries_a_held_revision`) and keeps the change,
author, moment and message of each revision it restates, superseding that
one alone under the digest of its own text
(`carry_keeps_what_it_restates`). With `--fields` all four say what they
wrote in decision 0074's words, each revision once, in digest order
(`writes_say_what_they_wrote`). What no law reaches is the order of their
effects, and what the host draws and files.

`name` is the first command that writes the store. It points a bookmark
at a change, which follows amend and rebase; at a revision with
`--revision`; or at a file, where a path is given — by path, `path:`, or
`file:` and a file bookmark or identifier. A bookmark moved keeps whether
it is private unless `--private` or `--shared` says, and `--shared` says
that a replica still calling it private will make it private again. A
name is refused by `check_name`'s rules — empty, a backslash, and the
path rules — and where it is spelled as a file identifier; and none it
takes leaves `names/` (`LAWS.name_stays_in_names`). `--delete` removes a
bookmark and each directory it leaves empty, `names/` itself kept. With
`--fields` it states what it wrote in decision 0074's words —
`historica-wrote-1`, then `name` or `unname` — and leaves the header
behind where it stops, whatever stopped it, except a command line that
was wrong. The file lands as the Rust tool lands it, staged beside itself
and renamed over, through `Store.write`, and goes through `Store.remove`.
`check.py` holds 58 `name` commands to the Rust tool with `names/` compared
after: every target, nested names and a name beside a directory of the
same name, every refusal, and a store whose bookmarks will not open.
What `name` decides is pure, and the IO shell only opens, writes and
prints what it was handed: the plan its words make (`name_reads_its_words`,
`name_does_what_it_reads`), the bookmark it sets (`name_points_where_asked`),
the one `--delete` finds (`name_deletes_the_bookmark_named`) and the lines
it says after (`name_states_what_it_set`).

`init [<dir>]` makes a store: `history/` in the directory named, or this
one, with the directories it lacks, joined as `Path::join` joins, so a
refusal names the path as it was joined — `…/./history` for `init .` —
and refused wherever a `historica.txt` is already there. It lays down the five directories and
the four notes the Rust tool writes, and says where the store is as the
path really is. The notes are prose the Rust tool keeps in its source;
`notes.py` takes them from the bytes a Rust `init` writes into
`notes.bend`, and `check.py`, which compares everything `init` leaves,
fails where they have drifted. The `bare` store, a folder with no store
in it, has seven `init`s and the commands that need a store refusing.

Colour is the Rust tool's too: `auto` asks the host whether standard output
is a terminal (`Store.tty`) and gives way to `NO_COLOR`, and a line
replaced one for one has the words that differ drawn in inverse video —
the line cut into runs of letters and digits and single other characters,
by the Unicode 17 table Rust's `char::is_alphanumeric` reads
(`unicode.bend`), and compared with `similar`'s Myers, which
`similar.bend` also ports and `check.py` holds to the crate. On a terminal,
`diff head --onto` an early revision prints the Rust tool's bytes, its 653
marks of emphasis included. Each mark falls on its own line
(`emphasis_marks_its_own_line`): a removal is paired with the arrival at
the same place in its run, and the runs a mark draws read as its line.
Colour changes no character (`diff_colour_changes_no_character`): a line is
kept as runs, and what `diff` renders with colour, printed without it, is
line for line what it prints without colour. Names are compared as the filesystem spells
them, with no normal form C. `opdiff` is what `diff` was here before: the operation
document between two files, by `Ops.diff`.

A file's content is decision 0032's rule, as the Rust tool reads it: a
revision that says nothing holds what its parents agree on, and a parent
that never saw the file has no say. Where the parents disagree and the
merge states no resolution, the rule stops, and so does every edit
recorded on top. There `cat` and `diff` read the file from
`merge.bend`'s walk, the one `merge_converges`, `view_keeps_invariant`
and `merge_intent` are proven about. It walks the target's ancestry in
digest order, each revision with its ancestors as indices, in order of
how many ancestors it has. Where every revision had seen more than any it
had seen — which the tool checks before it walks, and a store's ancestry
always satisfies — that is a causal order of every event
(`walked_order_causal`, `order_lemmas.bend`), so what the tool reads is
what every causal order reads (`walked_reads_every_order`), and so is
the whole reading of a target's ancestry, from the graph it builds out of
the store (`walked_file_every_order`). `blame` reads the walk everywhere, as
the Rust tool's reads `merged_content`, and names the author of each
standing element: on one line of history the walk is plain replay
(`merge_linear`), so no overlay of each edit is kept beside it. A resolution in that history is walked as `merge.rs`
walks one: a `keep` of a digest names the elements minted by the events
that stated that document. `check.py`'s `walked` store has four
hand-written merges that state nothing:
- two edits apart, one of them a delete beside the other's insert;
- two inserts at one place, where the digests break the tie;
- one joining all three;
- one joining a merge the Rust tool resolved with an edit concurrent with
  it, whose edit lands on a line the resolution kept.

It also has a revision recorded on top of the first. Every `cat`, `blame`
and `diff` over them prints what the Rust tool prints.

A store something was forgotten in is read as the Rust tool reads it
(`standin.bend`, decisions 0014, 0050 and 0066). A digest the store holds
nothing for may have been forgotten, and what stands in for it is a
document of its own, named by its own digest and by nothing else, so where
`Store.at` finds nothing the documents under `operations/` are read and
each asked what it `forgets`. Several may stand in for one digest — each
`forget` of another span of a document writes one more — and they are read
together as the Rust tool's union rule reads them: the first of each
grammar is the shape, every later one that agrees with it is folded in, and
a line forgotten in any is forgotten. Replay does not consult the text of a
forgotten item, only its terminator, so `cat` and `blame` show the line as
`\ forgotten`, `diff` renders it removed or kept like any other line, and
a merge's resolution that copied it has a stand-in of its own. `show`
prints the stand-ins where it would print the document, and a payload
forgotten whole is the two headers `forgets` and `length`, which `show`
prints and `cat` refuses in the Rust tool's words: how many bytes went and
which document stands where they were. `status`, `diff` and `record` over
the folder settle a file by the digest its nearest statement leaves; a
stand-in states no `result`, so where any of a file's documents is
forgotten the file is replayed instead. `check.py`'s `forgotten` store has
the Rust tool's `forget` destroy a line of a file added whole as `text`,
two lines of an edit, a line a merge's resolution copied, a payload of
bytes, and a second span of the first document, so that two stand-ins name
one digest; forty-five commands read it — `log`, `files`, `cat`, `show`,
`diff`, `blame` and `status` at the revisions it touched, and `record`,
`amend` and `carry` over it, with the store compared after — and ten
`forget`s run over what is already forgotten.

`forget <target> <path> --lines <first>..<last>` destroys a span's text
everywhere history quotes it (`forget.bend`). The lines are those the
target reads, each traced through the walk to the document that wrote it —
an edit's inserts, a `text` payload, or a resolution's own `insert` — and
from there to every delete that quotes it and every resolution that copied
it (decision 0050), none of them another file's
(`forget_rewrites_only_the_files_documents`). Each gets a stand-in: the
document with those items' text replaced by the marker and nothing else
(`forgetting_destroys_only_text`), its shape kept, so that the union rule
folds it in (`forgetting_keeps_shape`), and folded with whatever already
stands in for it. The stand-ins are filed first, through `Store.once`, and
only then is each original — found by its bytes among `operations/`, as
everything in a store is (`forget_destroys_only_what_it_forgets`) —
removed through `Store.remove`, so an interruption leaves a document and
one naming it, never bytes gone with nothing said. A file of bytes has no
lines: it is forgotten whole, the payload the target holds for it and no
other (`forget_whole_takes_one_payload`), its stand-in filed where it was
with `.ops.txt` after its name where that is free, and the other versions
of the file counted and left alone (decision 0066,
`forget_counts_only_other_versions`). Every entry of `cache/` named by a
digest goes with it, since an entry is some file's content and may be a
copy of what went; the note and the catalogues stay
(`forget_clears_only_copies`). `--dry-run` says what would be written and
destroyed and does neither; `--fields` states each digest `gone` under
`historica-wrote-1`, the header left behind by a refusal as `name`'s is.
`check.py`'s `forgetting` store is the same history with nothing forgotten
yet, read by the Rust tool first so that `cache/` holds a state of
`notes.md` and a catalogue of `operations/`; its forty-two `forget`s — a
span of an edit, of a `text` payload, of a line a resolution copied and of
one it inserted, a payload with other versions beside it, `file:` and a
signed span, and every refusal and usage error — are each run on a copy of
the store of their own, per tool, and the whole store after compared,
`cache/` and all.

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
operation and the last delete (`Ops.ordered`), which `semantic_replay.bend`
names `Block.ordered_all`. Two theorems close the gap:

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

The revision writer is proven the same way: `revision_write_parse` says
`Rev.write(r) == s` whenever `Rev.parse(s)` is `Done{r}`
(`revision_lemmas.bend`). The parser keeps the headers as it read them, but
`Rev` does not: it keeps the causal headers as fields, and `write` spells
them in a fixed order. The proof has to show that the order it read them in
was that one. `validate_sorted` says that what `validate` passes is sorted
by rank, with a rank repeated only where its key may repeat. Headers sorted
that way are, in order, those of each named rank followed by the facts.
`split` cuts off one rank at a time, `slice_values` says a rank's headers
are `values_of` under its name, and `single` says a key that may not repeat
gives at most one value. `canon` puts them together as the text `write`
spells. Two lemmas tie this back to the text. `classify_named` says a
header of a named rank is spelled with that rank's name, and `headers_sp`
says the header loop's headers and message are its lines: each header line
is its key, a space and its value (`header_line`, through `split_top`), and
the blank line and message after them come back as they were read.

Three changes to `revision.bend` exist for the proof, and none changes a
result or a message. `classify` walks a table of names with `T.same`,
because the checker cannot invert a match against fifteen string literals:
its fallthrough case keeps the key as a partially known string, which
`classify` will not reduce. The `historica` line is compared with `T.same`
rather than matched as a literal. `assemble` is one def per stage, as
`Tree.apply` is. Three mutations are refused where they should be: a
writer that puts `when` before `author` (`written`), a validator that lets
`change` repeat (`canon`), and a table that files `parent` under
`supersedes` (`classify_named`).

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
author had seen and what it stated — operations, or a resolution; a walk replays them into one
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
view whose authors the deleting event had all seen (`actions_avoid`).
A resolution (decision 0032) is an event of the same kind. On its view it
takes each `keep` as the first standing element minted under that name
that no earlier keep took. It anchors its inserts by Fugue's rule after
what came before them, kept or its own. It removes whatever it left
unkept. So its actions are attaches and marks decided on its view, and the
same lemmas hold of them (`resolve_avoid`, `resolve_stable`). Every law
about walks covers histories holding resolutions: convergence, the
invariant of every walked tree (`res_ok`) and of every view
(`resolve_restrict`). So
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
fail `merge_converges` first.

On one line of history the walk is plain replay. `merge_linear` says: for
documents each of which the parser would accept (`Block.each_ordered`,
every one `Block.ordered_all`), if applying them in turn to the empty file
with `Ops.apply` gives `f` (`Merge.replay`), then the walk of the chain
they make — event `n` has seen events `0..n` (`Merge.chain`) — over the
order `0..n` gives `f` too. That is decision 0007's promise and what
`merge.rs`'s `linear` fast path relies on. The ordering hypothesis is not
a convenience: two inserts at one gap in one document are read by the
merge in the reverse of the order plain replay writes them, and the
parser refuses such a document ("two inserts at one position"). The proof
(`linear_lemmas.bend`) walks one run beside `Cursor.walk`, operation by
operation (`run_sim`), carrying a Bool conclusion (`fine`): the view the
run acts on keeps `insert_at_gap`'s invariant, every name in it is by an
event the author had seen or by the author earlier in the run, and its
visible reading is the file so far. Positions are
counted in a view written as a prefix already walked and `drop(P, c)` of
what is left; deletes are tracked as the marks `cuts` a view has taken
and the marks `mk` a run has yet to apply, and separated from the
inserts by the reading's `nodup`. The order the run needs — a delete then
an insert at one position is one replacement, an insert closes the gap
behind it — is `strict`, and `parser_strict` derives it from
`Ops.ordered`. Across the chain, `restrict(t, seen)` is the whole tree,
because each event has seen everything before it, so the invariant
`insert_at_gap` takes as a hypothesis is carried rather than assumed. The
statement was fuzzed against the runtime before it was proven, which is
how the two-inserts case was found; one mutation, a chain whose events
have seen nothing before them, is rejected at `chain_go`.

The same holds after any history, not only a line. `merge_walk_invariant`
says every tree a walk builds keeps the invariant, in any order that
names each event once — causal or not, however concurrent — and
`merge_extends` says: walk any such history `p` to `f0`, then an event
outside it that had seen every event of `p` and states a document the
parser would accept; the walk leaves exactly what `Ops.apply` makes of
that document on `f0`. A merge revision that edits the merged file is
this case, and `merge_linear` is it repeated. The work is the invariant
(`walk_lemmas.bend`): an element a concurrent event attached may sit
anywhere among its siblings in name order, where `insert_at_gap`'s
argument needed it an only child. So the first half shows any fresh leaf
that is not its own parent, attached anywhere, keeps the invariant
(`invariant_leaf`). The tree splits at the attach point
(`children_attach_split`), so the leaf's sibling list is the part before,
the leaf, and the part after; a reading that does not reach the leaf's
parent reads as it did (`read_same`); one that does is the old reading
with the leaf spliced in once, returned through a continuation that
names the halves (`hit`, split on whether the parent is the element read,
or below its left children, its right children, or its later siblings);
and the reading still finishes one fuel up, since each sibling costs a
fuel and the leaf's cost is the one fuel the longer tree adds
(`read_app`, `fits_app`, `li_read`). The second half carries that through
an event: for any document, the run's view stays bounded by the events
the author had seen (`rok`), each attach it decides hangs under a name
its view holds and is minted above the last (`aok`, `anchor_pok`), so
every attach the walk applies is such a leaf (`apply_ok`), and every
event keeps the invariant (`ev_ok`, `walk_ok`). The bound that made a
chain's names fresh — every author below the event's index — became
"every author in the set the event had seen" (`Lin.before`, `Lin.inw`),
which is what a graph gives. An event that had seen everything walked
then has the whole tree as its view (`restrict_id`), and `run_sim`
applies unchanged (`event_c`). No mutation is
added: the breaks that would fail these laws — names that collide,
siblings out of name order, an order that repeats an event — fail
`merge_converges` first.

Every view keeps the invariant, including an event's view walked after
events it had not seen. `view_keeps_invariant` says: restrict a tree any
walk built to a set of events that holds the past of each
(`Merge.closed`, which is what an author had seen), and the invariant
holds. The restriction is the tree the set's own events walk to, in the
same order (`view_lemmas.bend`: `wr`), and `merge_walk_invariant` applies
to that walk. The events outside the set leave the restriction alone
(`restrict_apply`, from the convergence proof). An event inside it
decides on the restriction what it decided on the whole tree, because
restricting to a set and then to a subset of it is restricting to the
subset (`restrict_restrict`, `actions_restrict`). Its actions commute
with restricting (`restrict_apply_in`). That needs two facts every walked
tree has (`wf`, `wf_apply`): its names are in order, so an element placed
before one the restriction drops is still before all the rest
(`restrict_attach_in`), and each removal list is in index order, for the
same reason (`keep_ins_in`). With `insert_at_gap`, every insertion of
every event lands where its author asked, however concurrent the merge.
The pasts in `merge.rs`'s graph are ancestor sets and so closed; the
model's `Rev.past` is whatever the graph says, so closure is a
hypothesis. One mutation, a `closed` that does not check an event's
past, is rejected at `closed_has`.

An event applies its document to what its author saw, however much of
the history it had not seen. `merge_intent` says: walk any history `p` to
`t`. An event outside it had seen the closed set `past`, and so saw the
file of `t` restricted to `past`. If its document applies to that file,
then once the event is walked, its author's view — `past` and the event
itself (`Merge.seen_file`) — reads what the document made of it. That is
Eg-walker's promise for every event, and `merge_extends` is the case
where `past` holds all of `p`. The proof reduces to that case. The view is
the walk of `only(p, past)` (`wr`), where `merge_extends` applies. Walked
in the whole history, the event decides the same actions
(`actions_restrict`), and they commute with restricting to its view
(`restrict_apply_in`). Nothing in `t` is by the event itself
(`restrict_absent`), and every walked tree is in order (`walk_wf`). A
runtime test has an event that saw one of two concurrent edits, and reads
its document applied to that edit alone, in either order of the history.
One mutation, a view that reads the whole tree, is rejected at
`intent_at` and by that test. `merge_intent` is about an edit. No law yet says the same of
a resolution: that its view, once walked, reads the file its pieces
assemble to. That holds where its keeps run in view order, as every
resolution this tool writes does. The runtime tests and the `walked`
store hold it to examples.

One insertion lands at the gap its author asked for. `insert_at_gap`
says: on a view with the reachable-state invariant, an element of a
fresh name anchored by Fugue's rule after the visible element at `at`
(`left_of`, counting with the tombstones left out) is read, once the
tombstones are left out again, at exactly that gap —
`take(visible, at) ++ [it] ++ drop(visible, at)`. The invariant
(`Merge.invariant`) is two facts about the view: the reading of every
sibling list finishes within the fuel `order` gives it (`Merge.fits`),
and no element is read twice (`Merge.nodup` of the reading). It holds of
the empty view and is kept by an anchored attach of a fresh element and
by a mark (`invariant_empty`, `insert_keeps_invariant`,
`mark_keeps_invariant`), which is everything `inserts` and `deletes` do
to a view. The argument (`anchor_lemmas.bend`): the anchor's place has
no child yet — the element followed had no right child, or the descent
through its first right child's left children (`leftmost`, tombstones
included) landed on an element with none — so `attach`, which places by
name among siblings, gives the element no sibling and changes no other
list (`children_attach_other`, `children_attach_here`); the reading of
the new tree is the old reading with the element spliced beside its
parent (`read_attach`, one fuel up); and the parent is the element
followed, or the next element read after it (`next_is_read`,
`head_read`), so with the reading duplicate-free the splice is the
insertion after the element followed (`splice_swap`), which commutes
with leaving tombstones out because the element followed is visible
(`standing_splice`). The freshness `inserts` relies on — a name the view
neither holds nor hangs anything under — is a hypothesis
(`Merge.fresh`), as is the invariant of the view; every tree a walk
builds has it (`merge_walk_invariant` above), and so does every view
of such a tree an author can hold (`view_keeps_invariant`). What is fuel-bound stays explicit: `fits` is carried in the
invariant, not derived from a depth, and `leftmost`'s fuel (the element
count) is shown enough from it (`lchain_of_fits`, `leftmost_lands`,
`leftmost_stable`), so neither bound is assumed past what the invariant
states. Two mutations: an anchor that finds the right children among the
standing elements only, and a descent that follows standing left
children only — both the classic tombstone-skipping bug, both rejected
(`anchor_of_nil`, `leftmost_stay`), and both caught at runtime by the
two `replay_tests` cases built for them.

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
nothing; an insert after an element whose right child is a tombstone,
and one whose descent passes a tombstone, land where asked; every topological order of a four-event graph reads the same
file; and a document that contradicts its author's view is refused.
Resolutions say what survived, keep their elements' names so a
concurrent edit lands on one, and refuse a keep of an element nobody
wrote or one already kept. `contested` is not modelled, as in the Verus
file. The reading carries fuel — one more than the element count,
enough for any tree `attach` built — and positions are unary.

Forgetting keeps what it promises (`forget_lemmas.bend`). Decision 0014
says replay does not consult the text it destroys, and
`standin_replays_like_what_it_stands_in_for` is that as a theorem. Call a
line *like* another when it is the same line or that line forgotten, with
the same terminator either way: a stand-in — each item of its original, or
that item forgotten, and no `result` stated — applied to a file whose
lines are like the original parent's, makes a file wherever the original
makes one, and each of its lines is like the original's. The walk reads a
forgotten item's terminator and nothing else, which the proof follows
through every step `Ops.apply` takes: dropping, advancing, landing and the
range check. `chain_replays_like_through_standins` carries it along a
file's whole history as `Merge.replay` reads it, any of the documents
stood in for, in any part. What `forget` writes is such a stand-in
(`forgetting_destroys_only_text`), and of the shape the union rule folds
in, for an operation document and for a resolution
(`forgetting_keeps_shape`, `forgetting_a_resolution_keeps_shape`);
`show_prints_what_the_revision_states` is restated so that what `show`
prints of a forgotten document is documents the store holds, whole and in
its order, each saying it `forgets` the digest named. Of the command: every
document `--lines` writes a stand-in for is one a revision states for that
file (`forget_rewrites_only_the_files_documents`); a file of bytes loses the
one payload its tree holds at the target, or nothing
(`forget_whole_takes_one_payload`), and the versions it counts beside it
never include that one (`forget_counts_only_other_versions`); a file is
destroyed only where its bytes are a digest forgotten
(`forget_destroys_only_what_it_forgets`), and in `cache/` only an entry
named by a digest (`forget_clears_only_copies`); and its arguments are
read as their plain reading says (`forget_reads_its_words`). No law says
the converse of the first of these — that the documents found are *every*
document quoting the span; that walk is held to the Rust tool by the
stores, not proven complete.

Trying to prove the round trip found two ways the port accepted what it
could not write back: a `\ no newline` or `\ forgotten` line, and a header line, with no
newline after it. Both are refused now, as the Rust parser already did, and
`invalid/unterminated-marker.ops.txt` pins the first in both corpora.

The tests compare both specifications for the ordered examples, and
compare the cursor specification with the implementation for raw reversed
positions, repeated inserts, overlapping deletes and competing errors.
A hundred and eighty-two mutations cover the primitive helpers, lost inserts, a lost trailing
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
readiness that checks only the first; and two anchor breaks: right
children found among standing elements only, and a descent that follows
standing left children only; and three revision round-trip breaks: `when`
written before `author`, `change` allowed to repeat, and `parent` classified
as `supersedes`; and one chain break: an event of a chain that has seen
none of the events before it; and two view breaks: a closed set that need
not hold its events' pasts, and an author's view that reads the whole
tree; and one resolution break: a resolution that removes what its author
never saw; and two walk-order breaks: ranks by index rather than by what
each event had seen, and a walk that runs where its order is not known to
be causal; and one diff break: a check that lets a kept line differ; and one emphasis break: a marked line
that drops the words two lines share; and one folder break: a walk that
takes a file without asking the rules; and one target break: a bookmark's
revision taken without asking the store; and one log break: a listing
that keeps a revision no filter was asked of; and one file break: a file
bookmark taken where the revision does not hold its file; and one layout
break: a removed line laid as context; and one blame break: a line that
stayed dropped from the rows; and one rule break: a name rule whose
pattern may hold a slash; and one bookmark break: a change bookmark read
back as a file bookmark; and one abbreviation break: a digest cut at the
longest prefix it shares rather than one past it; and one walked-blame
break: rows read from every element the walk placed, removed or not; and
one span break: a span that drops its last line; and one printing break:
the marker after a line without a newline left out; and one position
break: a `path:` spelling looked up with its prefix; and four blame
breaks: the kind asked of the spelling rather than the file, a span
ignored, bytes the position never saw taken for text, and the target and
path read in reverse; and one folder-file break: a link in the folder
read through; and one diff-argument break: `--onto` taking every word
after it; and two diff-side breaks: a revision compared with nothing
rather than its parent, and a limit set to the spelling rather than the
file it names; and one shown-file break: a file shown whose sides agree; and one
folder-limit break: the folder's paths kept whatever the limit; and one
log-argument break: `--author` read as `--grep`; and two check breaks: a
document taking a payload's digest, and a parsed operation document called
refused; and two cat-and-show breaks: a document found whose digest the
named one begins, and a link printed through; and three hunk breaks: an
arrival numbered as a line of the parent, a side that holds none of a
hunk's lines named by its first line anyway, and a change shown only where
another is near; and three emphasis breaks: a removal compared with its
arrival the wrong way round, the arrivals' marks drawn before the removals',
and a context line given no mark; and three pairing breaks: the two
sides walked comparing their files the wrong way round, a file only the
parent holds dropped, and the child's files sorted backwards; and two
refusal breaks: a path refused without asking the rules, and a refusal
naming a path other than the one asked about; and one survey break: an
arriving file said to have changed as well; and two replay breaks: a
payload after a refusal starting the file over, and a document applied to
nothing rather than to what came before; and two status breaks: the
revisions joined kept newest first, and a `--merge` joined by its spelling
rather than the revision it names; and six name breaks: a name taken without
asking the path rules, the other words kept newest first, the header sent
early without `--fields`, a bookmark moved that forgets it was private,
`--revision` pinning the change, and `--fields`' header said twice; and six
listing breaks: `files` in reverse path order or with the path last, a pin
the store lacks said as its digest, bookmarks read in reverse, `log
--fields` with the change first, and facts of every kind counted; and fifteen
status-report breaks: a fact named by its path first, the accepts left out,
contests said where no work is joined, a contest line that leaves out the
file it contests, a claimed path said among the contests, the parents
after the first merged alone, a file of bytes read, a file replayed
whatever its kind, a disputed file compared with a digest, a disputed file
read as one the parents agree on, a disputed file emptied in the folder
said as nothing, a stated file replayed, a join that takes the first
parent's digest where the parents differ, a file read at the first parent
only, and a file no parent mentions joined as disputed; and eleven survey breaks: a link to a file the
record drops let dangle, a link written as a reference where the revision
states nothing, a link's `..` pushed rather than climbed, a run of one path
counted once too few, a file of lines refused
at a path other than its own, a kind stated for a file already there, a
`move` line for a file moved again later, a move that moves every file but
the one named, a restricted record refusing what the walk refused
elsewhere, a rename offered for bytes more than one path left, and a path
nothing answers to let through; one reason break: a reason of only
whitespace taken; and four naming breaks: a summary keeping a separator, a
fallback longer than the limit, a filed path keeping its control
characters, and the clock compared with the earliest work; and one colour break: a marked line drawn without its sign; and two
folder-plan breaks: a settled file of lines replayed, and a folder file the
position holds as bytes read; and two chain breaks: a chain that stays at
the revision it began at, and one that stops after it; and one revision-reading break: a document
outside `revisions/` read as a revision; and two size breaks: a size
believed whatever digest the host's line names, and a payload the host
could not find asked the stat of; and four fetch breaks: a file replayed
with nothing fetched for it, what a resolution keeps left unfetched, an
`edit` the folder's plan believes left unfetched, and a payload shown left
unasked; and three span breaks: `a..b` read as `b..a`, a walk from a
target that takes nothing in, and one that follows a revision's change
rather than its parents; and nineteen writing breaks: `record` keeping the first `--onto`
and a rewrite the first `-m`, a carried revision authored by whoever
carried it, a merge let onto an abandoned run, a reword that drops what the
revision stated, an edited file diffed against nothing, the bookmarks on
every change but a parent's moved, an acceptance nothing contests let
through, `carry` taking a change for the revision named, a rename moving
the path named rather than the file at it, a restriction taking one end of
a rename, a skipped name nothing answers to let through, a dry run giving
an arriving file a `link` line, `carry --fields` naming a revision twice,
a file with no NUL taken for text, the position read as empty, an
amendment changing the identifier of a file it added, a reason of spaces,
and an `abandon` dry run naming the run in reverse; and one stand-in
break: a document taken as standing in whatever its header forgets; and
eight forgetting breaks: a stand-in that resets a forgotten item's
terminator, one that writes an empty line where the marker goes, a line's
stand-in written for the revision that wrote it rather than the document it
names, a payload's length written where its digest goes, a file destroyed
without asking whether its bytes are forgotten, the span after `--lines`
taken as a word too, every file of `cache/` but its note cleared, and the
version forgotten counted among the others. The
proof gate rejects
each at its expected proof location. The script tests run both sides on multi-block
documents: a replacement, an insert and a delete in one document, adjacent
deletions, an insert at a deleted run's end, a second block that disagrees
or runs out of range, and forgotten quotes under a wrong digest.

`check.py` runs the proofs and all three suites on both the default JS and
native C backends, then verifies that deliberate replay mutations fail the
proof gate. Corpus failures now exit nonzero. The runner prints and fixes
the compiler path for each run. The full gate passes on Bend 2.0.25; emitting
the C for `main.bend` takes about half a minute on the development machine,
and compiling it ten seconds or so.

Every theorem the Verus spike states now has a Bend counterpart. What the
merge laws are about is `merge.bend`, held to `merge.rs`'s tests, and it
is the code `commands.bend` runs wherever a merge states no resolution, and
for every `blame`.

`reach.py` measures how far that goes. It follows every def from `main`,
and every def a law in `LAWS.bend` names, through the imports, and prints
per file how many of the lines the tool runs a law reaches; `check.py`
prints it too. Reached is generous — a def a law only mentions counts — so
the number is where to look, and what it calls unreached has no law at all.
`python3 reach.py --unproven` lists those defs. See
[RUNTIME.md](RUNTIME.md) for the C/Rust interop direction and proof boundary.

## What the port found

Porting `record` found that its output could not be compared at all.
Decision 0010 made the clock and the random source inputs to the library
so that "a corpus that pins a writer's bytes" could exist, but the
command line reached for the machine's own in four places, so no two runs
of `historica record` — the Rust tool's own included — leave the same
bytes. The command line now takes both as arguments, `main` is the one
place they come from the machine, and `historica-pinned` is the test build
that fixes them; `historica` itself cannot be told either, whatever it was
built with.

Porting `init` found that the JavaScript build had never said why an
effect failed: Bend's JS runtime builds a failure from its code alone and
says the system's words for it, so where there was no store the JS build
said "No such file or directory" and the native build said what the Rust
tool says. Every twin now fails with its own message, and the `bare`
store holds the JS build to the Rust tool's words where there is no store.

Porting `record --dry-run` found that the Rust tool's `--move` renames
before it asks whether either end is a path, and joins the path to the
folder with `Path::join` — which an absolute path replaces. So
`record --dry-run --move notes.md=/abs` moves `notes.md` to `/abs`, outside
the folder, and then refuses `/abs` as a path; `--move ../x=notes.md`
moves a file in from outside. The port refuses the same, in the same words,
without moving: a move with an end that is absolute or climbs out with `..`
is not performed. Every other refused path is moved first, as the Rust tool
moves it, and `check.py` holds the folder to it.

Stating `replay_keeps_a_refusal` found that `replay` hid a refusal: a
payload after a document that did not apply started the file afresh, so a
chain with a broken document printed a file and exited zero. A payload now
leaves a refused chain refused.

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

- **Merging** concurrent branches as a command over the store. A stated
  resolution is read. Where a merge states none, the proven walk reads
  the file. `status --merge` prints the tree's contests; the content
  contests of a file both sides edited are counted only where `carry`
  restates a file, so neither the rendering with markers nor `status`'s
  `marked` count of them is here.
- **Refusing a name that is not UTF-8**: the walk leaves it out, as the
  Rust walk does, but `status` does not list it, since the host's listing
  carries no spelling of it.
- **Forgetting** as `check` sees it: the port's `check` is not the Rust
  tool's and says nothing of what was forgotten. A stand-in filed while its
  original is still held — one that arrived from another replica — is not
  folded into the reading, since the port reads stand-ins only for a digest
  the store holds nothing for. And a directory under `operations/` already
  empty before `forget` ran is left there, where the Rust tool removes
  every empty directory it finds there; the port removes only the ones its
  own removals empty.
- **Writing the store**: `record --merge`, whose resolutions nothing here
  writes; `arrange`, `fetch`, `export`. `record` and `abandon` without
  `-m` do not open an editor — with no `$VISUAL` or `$EDITOR` both refuse
  as the Rust tool does — and who is recording is
  read from `HISTORICA_AUTHOR` alone, not from the identity file the Rust
  tool falls back on. It writes no `cache/`, which any reader rebuilds. The Rust tool finds a store by a `history` directory
  and refuses one without `historica.txt` as not a store; the port looks
  for the file, so it goes on looking above such a directory. `-C` is
  not read. `check` does not report on `names/`. A merge's file
  still holding the renderer's marker lines is not refused by
  `record --dry-run`, since the markers are not modelled.
- **A name that is not UTF-8**, which the Rust tool's `record` refuses
  with the rest of what the folder cannot take, is not among the paths
  `record --dry-run` refuses, as `status` does not list it.
- Unicode normal form C on paths, bookmark names and the folder's names.

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
- **A nested pattern of character literals is expensive to check.** A span
  cut at `..` by `SCon{'.', SCon{'.', rest}}` inside a match on the string
  took the checker more than ten minutes over `forget.bend`; the same cut by
  `String.starts_with` checks in seconds.
- **Types and constructors are global across modules too**, so
  `forget.bend`'s are `Fg.Plan{}`, `FgQuoted` and the like, spelled from
  another module as `Fg.Fg.Plan{}`; and an effect declared in one module is
  called from another only through a def there, which is why `store.bend`
  has `operations` and `cached` beside `Store.list`.
