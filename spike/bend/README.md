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
bend main.bend -- check --complete        # what is wrong with the store, and what has not arrived
bend main.bend -- -C notes log           # as if started in notes/
bend main.bend -- help                   # the usage text, and `--version`
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
bend main.bend -- identity "Ada <ada@example.com>"   # who records, from now on
bend main.bend -- skip build/            # a rule `record` and `status` keep to
bend main.bend -- update tip            # make the folder hold a head
bend main.bend -- merge right           # lay two lines of work out together, fenced where they met
bend main.bend -- record --merge right -m "joined"  # and record what the person left
bend main.bend -- arrange -n            # the readable names, planned; and given
bend main.bend -- forget head notes.md --lines 3..4   # destroy two lines' text, everywhere it is quoted
bend main.bend -- git status            # no such command here: `historica-git`, on PATH
bend main.bend -- opdiff old.txt new.txt # the operation document between two files
```

The store commands find the store the way `historica` does — the `history/`
here or above — through twenty-seven host effects (`store.bend`): `bend main.bend` runs
them as JavaScript, and the native binary calls a Rust static library, linked
by hand because `bend -o` links nothing of ours. `RUNTIME.md` is the boundary;
`check.py` builds both and holds every command here to the Rust tool byte
for byte. The JavaScript build is run as `bend main.bend -- <words>`, or
`bun main.js -- -- <words>`: the runtime reads `--help` and `--threads` for
itself unless a `--` comes first, and Bun takes the first `--` after a
script as its own.

They read what the command needs and nothing else, which is the Rust tool's
own arrangement. A store's `revisions/` is the graph and is small, so every
command reads the whole of it and hashes it here, in `sha256.bend`.
`operations/` is where the bytes are — a store of three hundred and seventy
megabytes is three hundred and fifty of payloads — and a file there is opened
only once a revision has named the digest it holds: `Store.at` answers where
the bytes with a digest are, the way decision 0036's catalogue does, and what
comes back is a path whose contents are read and hashed here before anything
is believed about them. The answer is read as the adapter writes it — a
line for each digest asked, in order, a path or `-`, then a line for each
document said to forget one — so a document is read at each path given
and at no other, the digests held and lacking are one answer to each, and
a forgetting document is read only for a digest the store holds
(`at_answer_reads_back`, `unsettled_answer_reads_back`). Nothing walks the
payloads to find a name. `check` is
the exception it is in the Rust tool too: it reports every file, and asks the
host for the digest and the size of each payload rather than carrying fifty
megabytes of PDF through a hash in Bend. `forget` and `arrange` ask the same
of the files they weigh, and pair each path with the line the host wrote
for it, none skipped and none shifted onto another
(`forget_reads_what_the_host_hashed`,
`arrange_reads_what_the_host_hashed`).

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
own tie-break. `LAWS.log_fields_lists_what_it_keeps` holds it to presenting
only revisions it was shown (`presentation_lemmas.bend`), but no law holds
its order; the gate the order passes is `check.py` and the same bytes out of
`log`, `show`, `files`, `cat` and `check` as the build before it.

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
| `nfc.bend`, `nfc_tables.bend`, `nfc.py` | Unicode normal form C, decision 0033's one spelling of a path, as `unicode-normalization` 0.1.25 computes it: canonical decomposition, Hangul by arithmetic, canonical ordering by combining class and composition by primary composites; the tables written by `nfc.py` from what `ffi/examples/nfc_tables.rs` asks the crate of every scalar value, so the Unicode is the Rust tool's 17.0.0, and held to the crate on nineteen thousand strings | `format::nfc`, the `unicode-normalization` crate |
| `folder.bend` | the working copy: `skipped/`'s rules read and matched, the folder walked a directory at a time, each name read in normal form C and each file opened where the folder spells it, what it refuses and why — a name that is not UTF-8 among it — and what counts as text | `working` |
| `survey.bend` | what `status` says of the folder against the position: facts, refusals, claimed paths, bytes to accept, links resolved against the tree the revision would state, and renames noticed; and what `record --dry-run` adds — the paths named, `--at` and `--move` placing files, a `moved` line, and what recording refuses that `status` describes | `record::survey`, `record::plan` |
| `revision.bend` | the revision document: parse, write; and `History` — heads, superseded, missing parents, change state | `format`, `core` |
| `tree.bend` | the file set at a revision: `apply`/`replay` along a chain, `merge` over the graph with decision 0008's contests, and the seven faults a store can contradict itself with | `tree.rs` |
| `store.bend`, `ffi/` | where the store is, what it holds — `cache/` included, when asked — where a digest's bytes are and which documents the catalogue says forget it, what a file weighs, what one directory of the folder holds, and whether output is a terminal; where a path really is; what time it is and random bytes, each pinnable; and the writes — a rename `record --move` states, a bookmark written, a bookmark, what `forget` destroys or a directory it leaves empty removed, `init`'s directories, a document or a payload filed once, and the directories a rename or a removal leaves empty, tidied; and the folder laid out — a file of lines written staged or in place, a payload laid, a link made, a bit set, a file made runnable; a document or a file asked for over HTTP; and a program run and an exit code: twenty-seven effects, a C adapter, a Rust static library |
| `naming.bend` | what a record's files are called: a revision under its month and day and its message's first line, cut where a filesystem would balk, and made distinct where another revision has the name; each file of content under that at the path it had; and a timestamp as an instant, for the clock warning | `naming` |
| `notes.bend`, `notes.py` | the four texts `init` writes — `historica.txt`'s note, `skipped/README.txt`, `format.txt` and `cache/README.txt` — taken from what the Rust tool's `init` lays down | `HEADER_NOTE`, `SKIPPED_NOTE`, `FORMAT_NOTE`, `CACHE_NOTE` | `Store::discover`, `store::catalogue`, `std::fs` |
| `bookmark.bend` | a bookmark file's grammar, and which files under `names/` are bookmarks | `store::{Bookmark, Name}`, `check_name` |
| `words.bend` | the Rust tool's words for a document it refuses: `ParseErrorKind`'s display, one def per kind, the line in front as `ParseError` puts it | `format::error` |
| `resolution.bend` | the resolution document: a merge's file stated by `keep` and `insert`, parsed as strictly as the Rust reader parses it, and written back | `format::resolution` |
| `argv.bend` | the command line before the command word, read as the Rust tool's `run` reads it: `-C <dir>` as often as given, the last counting; `help`, `-h`, `--help` and `-V`, `--version`; any other `-` word refused | `cli::run` |
| `shell.bend` | the usage text and the version, a usage error's message with the usage after it, and decision 0072's dispatch of a word no command here has to `historica-<word>` on `PATH` | `cli::{main, run, dispatch}` |
| `identity.bend` | who records: `$HISTORICA_AUTHOR`, or else the identity file under `$XDG_CONFIG_HOME` or `~/.config`, its blocks read and the deepest `under` holding the repository winning; and `identity <author>` writing it | `identity` |
| `editor.bend` | a message asked of `$VISUAL` or `$EDITOR` when `record` or `abandon` is given no `-m`: the file handed over, empty, the editor run where the repository is, and what it leaves read back as the message, nothing stripped | `cli::from_an_editor` |
| `skip.bend` | `skip`: the rules `skipped/` holds, listed; and a rule written for a path, a directory or a name, privately or not, under a name its file does not yet have, with every refusal the Rust tool makes | `cli::skip`, `working::Skipped` |
| `check.bend` | `check [<dir>] [--complete]`: everything `Store::check` finds, walked and read as it reads the store, and reported as `render::report` reports it | `store::check`, `render::report` |
| `conflict.bend`, `conflict_lemmas.bend` | where concurrent work met in one file and how a person is shown it: the contested regions, the rendering with fences, the renderer's lines still standing in what a person left, and the resolution `record --merge` states — the walk's proposal aligned with the folder's file, each surviving line named by the document that minted it. `merge_renders_the_uncontested_as_itself`: a file where nothing met renders as the walk's file, byte for byte; `merge_resolution_reads_back`: the resolution `record --merge` writes, assembled as `cat` assembles one, is the folder's file | `merge.rs`'s contests, `conflict.rs`, `diff::resolve` |
| `standin.bend` | what stands in for a forgotten document (decisions 0014, 0050, 0066): the two headers that stand in for a payload, parsed as strictly as the Rust reader parses them; which of a digest's stand-ins agree in shape with the first of its grammar and how they fold into one, a line forgotten in any being forgotten; what a digest reads as once only stand-ins are left, and what `show` prints of them; what a held document reads as with stand-ins beside it; and `like` and `covers`, the relations a replay through a stand-in keeps and what is read owes one | `format::payload`, `format::{operations, resolution}::stand_in`, `Store::forgetting` |
| `forget.bend` | `forget`: its arguments; the documents that quote a span — the edit that wrote each line, every delete of it, every resolution that copied it, followed through the walk — and the stand-in written for each; the originals found by their bytes and destroyed, their copies in `cache/` with them, and every directory `operations/` holds empty; and every message and refusal | `store::forget`, `cli`'s `forget`, `Store::clear_cache` |
| `forget_lemmas.bend` | what `forget` writes keeps its original's shape and destroys exactly the text of the items picked, and the stored history `replay` reads through such stand-ins reads the forgotten lines as forgotten and every other line as it was; what it rewrites is only what a revision's headers state for the file, and each stand-in opens by naming one of those digests as what it forgets, one payload for a file of bytes, and the versions it counts are the others; what it destroys is only what it forgets, in `operations/`, and in `cache/` every copy and only what the host listed there under a digest's name, never the note or a catalogue; it reads its words as their plain reading says, flags, span and all; and stand-ins beside a held original only forget, forget all they say, and fold alike in any order | `cli/tests/forget.rs`, `cli/tests/cache.rs` |
| `forgetting_lemmas.bend` | `forget_states_what_it_made_unreadable`, `forget_says_what_it_destroys`: what it prints reads back, as `gone` lines or as `destroyed` ones, as what it made unreadable and what it destroys; `forget_files_documents_where_nothing_is`: every document it writes is filed as one, at its own digest or at a name no file has; `forget_files_a_payloads_standin_where_it_was`, `forget_files_a_payloads_standin_by_its_digest_where_that_is_taken`: forgetting bytes no document holds, the stand-in is filed beside a payload that held them, at a name no file has, wherever every such name is free, and at its own digest's name wherever every such name is taken; `forget_takes_no_file_of_lines_whole`: a file of lines is never forgotten without a span; `forget_sweeps_only_what_lists_empty`, `forget_sweeps_only_listed_directories`, `forget_sweeps_past_a_links_target`: a step of the sweep removes exactly the directory it listed where the listing was read and empty, never `operations/` itself, and goes on only into directories the listing names on `d ` lines, a link's target line naming none | `cli/tests/forget.rs`, `store/forget.rs` |
| `main.bend`, `commands.bend` | the entry point, which reads the command line and dispatches; and `log`, `show`, `files`, `cat`, `names`, `diff`, `blame`, `status`, `record` — `record --merge` included — `amend`, `abandon`, `carry` and `name` over the store it finds, reading what stands in for a forgotten document wherever it reads one, and `init` where there is none, and a resolution assembled from what it keeps; `replay` and `opdiff` over named files | `cli`, `replay::assemble` |
| `arrange.bend` | `arrange`: every revision's stem over the whole store — the base, a change's first letters, a digest's — each file of content filed under the stem of the revision whose claim on it wins, at the path it had; the plan, in the Rust tool's walk order, and the renames carried out, each asking again whether its name is free; and the opening the Rust tool refuses where a revision does not parse | `store::arrange`, `naming::stems` |
| `arrange_lemmas.bend` | `arrange_plans_no_overwrite`: every rename it carries out goes from a path to a different one the store's listing does not hold, the code's set of taken paths read back as the list it was built from; `arrange_moves_each_file_once`: of each directory, a path is renamed from no more often than the walk found a file there; `arrange_keeps_a_revision_where_it_sits`: without `--refile`, a revision is renamed only within its directory; `arrange_opens_what_parses`: it opens no store holding a revision document whose text does not parse, wherever it stands; `arrange_counts_every_file`: every file it walks is counted once in what it prints | `arrange` |
| `prune.bend` | `prune`: what may go, to the Rust tool's fixed point — each revision asked, in digest order, against what is kept at its turn — and the content nothing kept still needs, forgetting documents included; the whole of `check` asked first, before the store is opened, as the Rust tool asks it; the files removed, `cache/` cleared, and the directories left empty swept | `store::prune`, decision 0013 |
| `prune_lemmas.bend` | `prune_keeps_what_work_stands_on`: no revision it keeps names one it lets go of as a parent, through an invariant every step of every pass keeps; `prune_lets_go_only_what_is_superseded`: every revision it lets go of is one a revision of the store says it supersedes, through a second such invariant; `prune_removes_only_unneeded_content`: every document and payload it removes holds a digest no revision it keeps names by its own `edit`, `text` or `bytes` headers, and is no forgetting document standing in for one that is; `prune_dry_run_names_what_prune_removes`: a dry run removes nothing and names, a line each and in order, the files the real run removes; `prune_clears_only_derived_files`: it clears from `cache/` only files named by a digest | `prune` |
| `receive.bend` | `receive`: two stores read as the Rust tool opens them, each held to the whole of `check` as the Rust tool's `receive_plan` holds it, related or joined; the union planned — revisions, documents and payloads this store lacks and neither forgets, bookmarks new or joined on their axis and the disagreements, rules under the labels `Rule::label` gives, the files of `claims/` — and carried out, content before the revisions naming it, with the originals a forgetting document stands in for destroyed | `store::receive`, decisions 0029, 0044, 0045, 0053, 0062 |
| `receive_lemmas.bend` | `receive_takes_only_revisions_it_lacks`: every revision it files is one of the source's revision documents, by digest and text, under a digest no revision document here has, through the sort and the pass that keeps each digest once; `receive_takes_only_documents_it_lacks` and `receive_takes_only_payloads_it_lacks`: every document and payload is one of the source's, under a digest this store holds nothing under and neither store forgets; `receive_joins_only_related_histories`: between two stores the check passes, it plans exactly where the histories are related, read from the revisions, or it was asked to join them; `receive_moves_no_bookmark`: each bookmark it writes, by name and target, is new here or one this store has at that target; `receive_destroys_only_what_is_forgotten`: every original it destroys is one a forgetting document of either store names in its header; `receive_removes_only_the_originals`: every file it removes for them is an operation document or payload file of this store, at that path, holding one of those digests; `receive_trusts_what_it_plans_from`: nothing is planned into or out of a store holding a revision document whose text does not parse | `receive` |
| `offer.bend` | `offer`: the published copy's store read as `prune` reads it and opened as the Rust tool opens a store, and its manifest written to standard output — the header, every head of the graph, then payloads, documents, revisions, rules, the other tool's files and bookmarks, each group by path and each path under the copy's own name — with no private rule or bookmark named | `store::offer`, decisions 0048, 0052, 0056 |
| `offer_lemmas.bend` | `offer_names_no_private_bookmark`: the manifest is the one a store with no private bookmark would have; `offer_names_no_private_rule`: and the one a store with no private rule would have; `offer_names_each_file_by_its_digest`: every line names a file by the digest the store's listing gives it; `offer_lists_forgetting_as_prune_reads_it`: what the manifest says a document forgets is what `prune`, `receive` and `export` read it as forgetting, save a resolution the Rust tool's catalogue does not parse; `offer_lines_read_back`: `fetch`'s line reader reads each line it writes back as the file it names, whatever spaces the path holds | `offer` |
| `export.bend` | `export`: a fresh copy — `init`'s layout, the target's ancestry closed over parent edges, every document and payload it names followed through a resolution's `keep` lines, every forgetting document standing in for any of it, the shared rules, the shared bookmarks whose target the copy holds, the files of `claims/`, each file named as `arrange` names it over what travels — and the folder the target has, laid out path by path; a copy it made brought up to date, the folder caught up; or `--files-only`, the folder and nothing beside it | `store::export`, `update::plan_at`, `update::apply`, decisions 0042, 0051, 0052, 0053, 0062 |
| `export_lemmas.bend` | `export_lays_out_every_path`: every path the tree places gets one outcome, at that path, in order; `export_names_only_what_travels`: every bookmark a copy is given is shared and finds what it names; `export_states_no_private_rule`: every rule file a copy is given states a shared rule; `export_writes_over_no_unrecorded_work`: catching a copy's folder up writes over a file only where some revision's record of that path holds its bytes, or the folder is the export's own output; `export_removes_only_recorded_files`: and removes only what such a record holds; `export_writes_only_where_a_copy_may_go`: a fresh copy only where nothing is held, an update only into a store; `export_lays_each_file_as_the_tree_has_it`: lines as `cat` prints them, bytes as the entry names them from a file holding them, links as materialised, each running where the tree says; `export_lays_out_only_what_the_walk_offers_back`: every path outside the store, no other file's directory, and none a rule covers; `export_carries_only_this_stores_files`: every document, forgetting document and payload a copy carries is one of this store's; `export_renames_nothing_a_copy_holds`: each revision a copy holds keeps its stem; `export_destroys_only_what_is_forgotten`: an update destroys only what a forgetting document of this store or the copy names in its header | `export` |
| `catchup_lemmas.bend` | `export_catches_up_to_a_fresh_copy`: once the steps of a copy's folder plan are taken, every path of the folder a fresh export lays out for the same target holds that file — by digest and mode, or by where its link points — one step a file, and nothing removed is one of those paths; `export_settles_only_on_what_it_laid_out`: a folder the plan calls settled already holds all that; `export_spares_the_unrecorded`: every file the plan writes or links over, and every file it removes, holds bytes `cat` of some revision of the copy reads for some file of its tree, or a payload that tree names — `update`'s promise, met at `update_lemmas.lookup_rec` | `export` onto a copy |
| `onto_lemmas.bend` | `export_updates_only_a_copy_it_could_have_made`: an update goes on exactly where the copy is related and holds no revision this store neither holds nor names as a parent or as superseded; `export_update_leaves_the_copy_the_whole_set`: every revision, document, forgetting document and payload the set names is one the copy holds, one the update writes, or one a forgetting document of either side says is gone; `export_update_gives_up_only_what_the_set_no_longer_names`: every file an update withdraws or retires is a revision, document or payload file the set does not carry, a rule file of a rule the origin does not share, or a bookmark file of one that does not travel; `export_update_carries_only_the_claims_a_copy_lacks`: a file of `claims/` travels exactly where the copy has none of that name; `export_update_states_no_private_rule`: every rule file an update adds states a shared rule | `export` onto a copy |
| `dryrun_lemmas.bend` | `export_dry_run_names_what_it_would_write`: read back, `export -n`'s `would withdraw` lines are the files a copy gives up, in order, and its `write` lines every path the tree places, once each and in path order; `export_files_only_dry_run_names_what_it_lays_out`: `--files-only -n`'s `write` and `link` lines are the files and links the real run says it wrote and linked | `export -n` |
| `filesonly_lemmas.bend` | `export_reads_a_directory_listing_back`: the host's listing of a directory reads back as its entries' names, once each and in order, a link's target no entry of its own; `export_writes_only_into_nothing`: `--files-only` lays a folder out, and a fresh copy is made, exactly where that listing names no entry; `export_calls_a_folder_folded_exactly_where_it_reads_back_otherwise`: reading the host's digest line for each file it wrote, `--files-only` refuses the folder as folding the tree's paths exactly where some file reads back as other bytes than it laid | `export`, `export --files-only` |
| `words_lemmas.bend` | what each command reads its words as, said as plain facts about the words rather than through the command's own reading: `arrange_reads_its_words`, `prune_reads_its_words`, `receive_reads_its_words`, `offer_reads_its_words`, `export_reads_its_words` and `fetch_reads_its_words` — a command line is accepted exactly where every word starting `-` is one of the command's flags and the other words are as many as it takes, a flag counts where it is among the words, wherever it stands, and the other words, in the order typed, are what the command holds; `receive`'s and `fetch`'s single passes over their words included | `arrange`, `prune`, `receive`, `offer`, `export`, `fetch` |
| `fetch.bend` | `fetch`: the URL cut at the manifest's directory, and refused in the Rust tool's words where it names no manifest or carries a query; the manifest read as `Offer::parse` reads it; the plan worked out against this store — what it lacks and neither side forgets, each digest once, the bookmarks it does not hold, the reserved directories it carries and the ones it declines, relatedness from the listing — and carried out in `receive`'s order, every file hashed against its line before it is filed under its digest, the manifest read again where a path has gone, three times at most | `store::fetch`, `cli`'s `fetch`, decisions 0048, 0052, 0056, 0057 |
| `fetching_lemmas.bend` | `fetch_asks_under_the_manifests_directory`: a URL it accepts is the manifest's directory, ending with `/`, and a name with no `/` in it, put back together; `fetch_asks_only_for_what_the_manifest_names`: every path a pass asks the host for is a path of the manifest; `fetch_files_only_text_that_hashes_to_its_line`: a document is filed only where the text that arrived hashes to the digest its line gave; `fetch_lands_a_file_only_where_it_hashes_to_its_line`: a file that arrives whole is moved in from where it was staged only where the host found its bytes to hash to that digest; `fetch_files_a_payload_under_what_it_hashes_to`: and a payload is filed under the digest its bytes have; `fetch_writes_a_bookmark_once_a_pass`: once a pass has written a bookmark, whatever the host answers for a later line naming it, no bookmark is written for it | `fetch` |
| `manifest_lemmas.bend` | `fetch_reads_the_manifest_offer_writes`: the lines `offer` prints, each with a newline after it and answered by the host as the text at the manifest's URL, are read by `fetch` as the heads and files they were printed from, every kind, digest, forgotten digest and path as written | `offer`, `fetch` |
| `fetchplan_lemmas.bend` | `fetch_refuses_only_what_shares_no_revision`: a refusal as unrelated is where no join was asked, each side holds a revision, and no revision the manifest lists is one this store holds or one a revision here names as a parent or as what it supersedes; `fetch_refuses_what_shares_no_revision`: and there it refuses, in the Rust tool's words; `fetch_destroys_only_what_is_forgotten`: every original it destroys is one a forgetting document of this store, or a line of the manifest, says is forgotten; `fetch_asks_for_no_payload_held_or_forgotten`, `fetch_asks_for_no_document_held_or_forgotten` and `fetch_asks_for_no_revision_it_holds`: every payload and document it asks for is one this store holds nothing under the digest of and neither side forgets, and every revision one it does not hold; `fetch_says_what_it_took`: asked for `--fields`, it names each revision it took once, in digest order, and none it did not | `fetch` |
| `escape_lemmas.bend` | `fetch_asks_for_a_path_by_its_bytes`: whatever the bytes of a path, what `fetch` asks for decodes, each escape read as `%` and two uppercase hex digits, back to exactly those bytes; `fetch_asks_in_characters_a_url_may_hold`: and holds only characters RFC 3986 leaves unreserved, `/` and `%`; `fetch_asks_for_what_is_unreserved_as_itself`: and each unreserved character, and `/`, is asked for as itself — every byte of the 256 shown to the checker, and with the three laws the whole of how a byte is spelled | `fetch` |
| `LAWS.bend` / `PROOF.bend` | three hundred and eighty claims about the code, each proven | the test suite and Verus replay helpers |
| `replay_spec.bend` | independent position-based replay specification | `spike/verus/replay.rs` |
| `semantic_replay.bend`, `position_lemmas.bend` | positional semantics for an arbitrary insertion, deletion or replacement block; coordinate translation | first semantic replay bridge |
| `composition_lemmas.bend` | a script of blocks, composed: the cursor over a whole document is the positional result | the multi-block theorem |
| `parser_lemmas.bend` | the parser only accepts ordered documents: its per-operation check implies `Block.ordered`, and the parse loop applies it to every operation | the parser theorem |
| `refusal_lemmas.bend` | refusals are justified: every refusal of an ordered document has one of four positional causes, and no cause means the positional result | error soundness |
| `diff_lemmas.bend` | `apply(diff(parent, child)) == child`: the LCS backtrack yields a script that takes the parent to the child, and the runs of that script are blocks the cursor walks to it | `tests/diff.rs` |
| `merge.bend`, `merge_lemmas.bend` | the merge — Eg-walker over Fugue, each event, edit or resolution, decided on its author's view, elements placed by name — which `cat`, `diff` and `blame` walk where a merge states no resolution; and `merge_converges`: two causal orders of one graph merge to one file | `merge.rs`, `spike/verus/merge_model.rs` |
| `string_lemmas.bend`, `tree_lemmas.bend`, `graph_lemmas.bend` | strings compare as they are, down to the bit; what a revision leaves: one file per path, no link dangling, the kind fixed at the add, a move a drop follows; and the merge a function of each revision's parent set, not its parent order | `tree.rs`'s rules, decisions 0017 and 0040 |
| `map_lemmas.bend` | what Base's `Map` and `Set` hold, for Base's own definitions: `Map.new` holds nothing; a key finds what `Map.set` just wrote for it, in any map (`get_set_same`, `has_set_same`); in every map `Map.new` and `Map.set` build — `wf_new` and `wf_set_map` prove each keeps the trie's invariant — writing one key changes nothing another key finds (`get_set_other`, `has_set_other`); and a set built from a list holds exactly the list's strings (`set_from_list`); the same for `Set.add`, `Set.del` and `Set.from_list`, whose sets `Set.add` goes on keeping; a map built from a list of pairs gives each key the value beside its last appearance (`get_from_list`, `has_from_list`); `Map.keys` lists exactly the keys `Map.has` holds (`keys_has`); what `Map.pop` hands back is what `Map.get` finds, beside `Map.del`'s map (`pop_get`, `pop_map`); and after `Map.del` the key finds nothing and every other key what it did, the invariant kept (`get_del_same`, `get_del_other`, `wf_del_map`). Under them, where `Map.diff` parts two keys, down to the bit: they agree at every position before it (`agree_below_diff`) and differ at it (`split_at_diff`) | Base's `Map` and `Set` |
| `linear_lemmas.bend` | `merge_linear`: on one line of history, each event having seen every event before it, the merge walk reads what plain replay makes | `merge.rs`'s `linear` fast path, decision 0007 |
| `walk_lemmas.bend` | `merge_walk_invariant`: every tree a walk builds keeps the invariant, however concurrent its events; `merge_extends`: an event that had seen everything walked before it leaves what `Ops.apply` makes of its document | `merge.rs`'s walk, decision 0007 |
| `order_lemmas.bend` | `walked_order_causal`: the order `commands.bend` walks a merge in — an insertion sort by how many events each had seen — is causal and holds every event once; `walked_reads_every_order`: so the file the tool reads is what every causal order reads | `merge.rs`'s topological order |
| `similar_lemmas.bend` | `similar_diff_applies`: the document `diff` and `blame` draw from `similar`'s search takes the parent to the child — the search's moves are checked in one pass, and moves that pass are an edit script `diff_lemmas.bend` proves; `Ops.diff` answers any that do not, which the crate's two thousand cases never ask for | `historica::diff` |
| `emphasis_lemmas.bend` | `emphasis_keeps_was`, `emphasis_keeps_now`: emphasis changes no character — a changed line's words are the line, and the runs `similar`'s Myers marks on either side read, in order, as that side's line | `diff`'s emphasis |
| `mark_lemmas.bend` | `emphasis_marks_its_own_line`: every mark emphasis computes falls on its own line — a run of removals replaced one for one pairs each with the arrival at the same place, the runs a mark draws read as the line it is drawn on, and only a removal or an arrival has one | `diff`'s emphasis |
| `sort_lemmas.bend` | string order is total and transitive, and Base's `List.sort` by a name returns its items each no smaller than the one before, with the items under each name the ones it was given, in the order given; and whatever holds of every item any sort is given holds of every item it returns, since a merge only moves what it is handed (`all_sort`, and `all_sort_at` for a test that reads one more value) | `diff`'s pairing |
| `pair_lemmas.bend` | `diff_pairs_each_file`: under any file, the pairs `diff` goes on with are the entries each side holds under it, paired in order as far as either goes — each file compared once with itself where each side holds it once | `diff`'s pairing |
| `folder_lemmas.bend` | `rules_are_well_formed`: every rule a file in `skipped/` states is a path with a value or a name that is one component, not empty and not only `*`; `listing_skips_nothing`: reading a directory's listing adds no file or link a rule in `skipped/` skips, and no directory a rule skips whole, so the working copy's walk takes nothing skipped | `working`, decision 0011 |
| `nfc_lemmas.bend` | `nfc_leaves_ascii`: a path of ASCII is its own normal form C; `nfc_orders_marks_by_class`: canonical ordering leaves no mark after one of a higher class with no starter between; `nfc_ordering_keeps_every_mark`: and the marks of every class are the ones it was given, in order; `nfc_class_misses_nothing`: the class lookup, stopping at the first run past a character, finds what a search of every run finds over the crate's table; `nfc_leaves_separators_alone`: in the crate's tables `/` and `.` have no class and are in no pair and no decomposition; `the_walk_yields_a_path_once`: the walk yields no two files in a row at one path, and loses no path it found; `the_folder_spells_what_is_opened`: a read opens a name whose normal form is the path, or the path itself; `a_name_that_cannot_be_spelled_is_refused`: the host's lines for any directory, read back, refuse each name that is not UTF-8 once, where it is on disk, in the Rust tool's words, and nothing else | `format::nfc`, `working::walk` |
| `host_lemmas.bend` | what the host answers, written as the adapter writes it and read back: `at_answer_reads_back`: `Store.at`'s answer in its `forgets` form asks for the document at each path it gives and at no other, reads one answer to each digest asked, in order, held or not, and reads a forgetting document only for a digest the store holds; `unsettled_answer_reads_back`: the digests the same answer leaves unsettled are those the store holds nothing for, in order, then each a document is said to forget; `run_asks_for_what_it_names`: `Store.run`'s question, split at NUL as the host splits it, is the directory, the program and every argument, each whole and in order | `ffi/src/lib.rs`, decisions 0014, 0036, 0072 |
| `stats_lemmas.bend` | what the host hashed, written as the adapter writes `Store.digests`' answer — `<digest> <size>` a line, or `- 0`, one to each path asked, in order — and read back: `forget_reads_what_the_host_hashed`: `forget` pairs each file of `operations/` with the digest and size on the line for it; `arrange_reads_what_the_host_hashed`: `arrange` names each payload by the digest on its line | `ffi/src/lib.rs`, `forget`, `arrange` |
| `standing_lemmas.bend` | `a_stand_in_stands_for_what_it_forgets`: every forgetting document the port writes — an operation document or a resolution forgetting a digest, and a payload's two headers — is kept by the scan for stand-ins exactly where the digest it forgets is among those asked, and for no digest that only begins its own | decision 0014, `Store::forgetting` |
| `listed_lemmas.bend` | one directory of the folder, written as the adapter writes it and read back by the walk: `a_directory_is_read_as_the_host_lists_it`: each line is read as the entry it was written for, whatever its name holds but a newline — the directories it names are listed next, each named in normal form C beside where the folder spells it, the files and links `tracked` takes are found, a file with its execute bit and size and a link with its target as the folder spells it, each entry is refused for what `refusal.of` finds in it, a link's target is no entry, and each name that cannot be spelled is refused where it is on disk; `the_walk_yields_its_files_in_path_order`: what the walk yields is sorted by path; `the_walk_keeps_the_file_it_met_last`: and holds, at each path, exactly the file it met there last, or nothing where it found none | `working::walk`, decisions 0011, 0033 |
| `pattern_lemmas.bend` | a name rule's pattern as decision 0011 reads it, `*` any run of characters and nothing else special: `a_pattern_matches_each_name_it_spells`: whatever run each `*` stands for, the name the pattern then spells is one `Folder.matches` matches, though it looks for each run only at the first place it stands; `a_pattern_matches_only_names_it_spells`: and a name it matches is one the pattern spells with some run for each `*` | `working::Pattern`, decision 0011 |
| `survey_lemmas.bend` | `walk_refuses_nothing_skipped`: the paths the walk refuses are ones no rule in `skipped/` skips, since a rule is how a person silences one; `status_says_an_arrival_once`: no line of `status` but `added` or `dropped` names a file being added, read against the list of what arrives; `status_refuses_what_the_folder_holds`: `status` refuses what its walk refused first, as the walk found it, and after that only a path where the folder holds a link whose target the format cannot hold, or a file recorded as lines whose bytes are no longer text, saying which — never a path only the position holds; `status_offers_a_rename_the_bytes_make`: each rename it offers is from the one path that left holding some bytes, not nothing, to the one that arrived holding them; `record_refuses_a_dangling_link`: where `record` goes on, a link of the position it keeps that names a file it drops sits where the folder holds a link the format can hold; `record_states_a_kind_only_for_an_arrival`: where `record` goes on, every kind stated names a path the restriction covers and no file of the position is at; `record_moves_each_file_once`: the `move` lines give each file the renames moved and the record keeps exactly one place, the last the renames put it, and a file dropped or never moved none; `record_names_only_what_is_there`: `record` goes on exactly where each path named covers a file of the folder, the position or the renames, whatever the rules say; `a_rename_keeps_each_file_once`, `a_rename_puts_each_file_where_it_was_said`: `--at` and `--move` leave the position's files each once, and `--at` alone leaves each at the path the last `--at` naming it gave and every other where it was; `record_refuses_only_what_it_looks_at`: whatever the folder and the store answer, a record restricted to some paths refuses only among them; `record_goes_on_where_each_path_holds_one_file`: where `record` goes on, no path it looks at holds two files, since the survey claims every path several files hold; `record_plans_in_file_order`, `record_plans_every_file`: it plans from the position in file order, each file's entries as they were; `a_link_refers_only_to_what_the_revision_states`: a link is written as `file:` and an identifier only for the file the revision holds where its target lands, in normal form C — the arrival minted there, or the one file of the position there the record keeps; `a_link_resolves_inside_the_folder`: and a link at a path the format holds resolves, if at all, to a path that is not absolute and never climbs out with `..` | `working::walk`, `record::survey`, `record::plan` |
| `status_lemmas.bend` | `status_reads_its_words`: `status` reads its arguments as their plain reading says — the word after a flag is its value, the last `--onto` counting and every `--merge` kept in the order given; `status_joins_held_revisions`: every revision it joins — what `--onto` and each `--merge` resolve to, and the head where it is taken — is one the store holds, through a lemma that Base's `List.sort`, by any order, returns only what it was given; `status_says_what_it_found`: everything the survey found is in the report, in the order found, each on a line of its own naming it — a fact beginning with its kind and ending with its path, a refusal, a claim, a file still marked or an accept beginning with its word and its path; `status_says_each_contest`: where work is joined, each contest the tree merge found but a path several files claim is said once, in its order, on a line naming the file contested by the first eight characters of its name, and where one revision or none is the position, none; `status_compares_with_the_revisions_tree`: against one revision, the folder is compared with the tree `files`, `cat` and `diff` read there; `status_reads_only_lines`: every path it asks the host to read and every file it replays is a file of lines it compares; `status_surveys_each_path`: the survey is told of each path once, in order, and of each path, as the folder's digest, the host's answer for it and none for a path it was not asked; `status_leaves_a_disputed_file_unsettled`: where the parents being joined leave a file of lines differently, what the survey is told of its path, whatever the folder holds, is that a file there is edited, emptied, refused or still marked — emptied only where it holds no bytes, edited only where it holds some — and that a link or nothing there drops it with no content an arrival could be matched to; the report `status` prints has no line for an emptied file, as the Rust tool's has none, which `docs/tasks` holds; `status_believes_what_is_stated`: against one revision it is refused only where a file no statement settles cannot be replayed, and with that refusal; `status_joins_what_it_reads`: joining, each file it compares is paired, in order, with what the parents' readings of it join to — the digest every parent that mentions it reads, the empty digest where none does, and `-` where two read it differently | `status`'s arguments, parents and report |
| `update.bend`, `update_lemmas.bend` | `update`: the folder made to hold a head — the plan of what each path takes, from the target's tree, the walk, a directory's listing where the walk took nothing, and what history records at each path; the effects that carry it out, a list `apply` performs one host write at a time; and the IO. `update_reads_its_words`: `-n` or `--dry-run` anywhere makes a dry run, and the target is the one word not beginning with `-`; `update_holds_only_a_head`: whatever it is told, the revision it lays out is a current head of the store, and told nothing, the store's only one; `update_lands`: where it plans at all, every path the target holds with one file ends up holding what the store reads there — the bytes `cat <target> <path>` prints, or the payload the tree names, with the tree's mode, or a link pointing where `cat` says; `update_spares_the_unrecorded`: every file it writes over or takes away holds bytes `cat` of some revision the store holds reads for some file, or a payload its tree names; `update_touches_only_the_target`: every file it writes, mode it sets and link it makes is at a path the target's tree holds, and it removes only at a path the tree does not hold, where the walk found a file whose bytes some revision records for a file history put there, or a link; `update_again_keeps`: run again from what it left, it keeps every path it stepped through, whatever history then records; `update_settles_exactly_what_stays`: it says the folder already holds the target exactly where carrying its plan out would change nothing; `update_dry_run_names_what_it_does`: the dry run's lines, read back by the verb each begins with, name exactly the effects `apply` performs, kind by kind and in order, and say the folder holds the target exactly where there are none; `update_says_settled_as_its_dry_run`: with nothing to do, `update` says what its dry run says. What a path holds after its step is `after`'s model of the host's writes, which `check.py` holds to the Rust tool and nothing here proves | `cli::update`, `update::{plan, apply}` |
| `walk_fault.bend` | why a walk refused, in `merge.rs`'s words: the first event whose document its author's view contradicts, found by walking again where `Merge.walk` answered only that it refused | `merge::MergeError` |
| `merging.bend`, `merging_lemmas.bend` | `merge`: the heads joined — what is named, and every current head that is not — and laid out in the folder: each file of lines as the walk reads it, fenced where concurrent work met, each file of bytes as the payload the tree kept, each link where it points, and a file holding work nobody recorded left alone; then the `record` line that records it, built as the words a person types. `merge_joins_held_revisions`: every revision it joins is one the store holds; `merge_joins_every_head`: whatever a person names, every current head is joined, through a lemma that a sort by digest keeps every item under each digest; `merge_spares_the_unrecorded`: file by file, every act it performs for a file of the merged tree is accounted for by that file — at the name `beside` gives it where it gives one and otherwise at its own path, with its mode; a file of lines as the walk of the heads renders it, a payload the tree names, a link where `cat` says — and a file is written only over what the folder's walk read as nothing, not text, what it writes, the walk unfenced, or what one of the heads reads for the file; `merge_rewrites_nothing_merged`: where the trees contest nothing and the folder already holds the merge, every file it writes it writes with the bytes already there, and it points no link; `merge_counts_the_files_that_met`: the number it says hold work that met is the number of files where the store's walk of the heads met or no side's payload wins; `merge_counts_what_it_fences`, `merge_counts_nothing_unfenced`: a label or closing line it renders, standing on a line of its own that the walk's reading does not hold, is counted by `status.marked.of`, the search `status` and `record --merge` read a file with, and the walk's reading unfenced is counted nowhere; `merge_prints_the_record_that_records_it`: the words of the `record` line it prints, read by `record`'s own parser, are a merge of every head it joined as the person typed it, settling each file set aside at the path it wrote it; `merge_sets_aside_the_claims`: the files it writes beside a path are exactly those a contest names after the first, which keeps the path | `cli::record::merge`, `conflict::render` |
| `naming_lemmas.bend` | `a_revision_is_filed_under_its_month`: a revision's stem is its month, a `/`, and one name holding nothing a filesystem reserves, whatever its message; `a_summary_fits_its_limit`: the summary is sixty characters at most; `a_summary_gives_up_its_ends`: it neither begins nor ends with a dot or a space; `content_is_filed_under_a_name_a_filesystem_holds`: each file of content is filed under a name with no control character; `record_compares_with_the_latest`: `record` warns exactly where a timestamp it is handed names a later instant than the clock; `record_names_the_latest_work`: the one it compares with is one it was handed and none is later; `a_timestamp_is_read_at_its_offset`: the same local time names an instant that many hours and minutes before `Z` at `+HH:MM`, and after it at `-HH:MM`; `abandon_takes_a_reason_that_says_something`: a reason is taken exactly where it is not all whitespace | `naming`, `record`'s clock check, `abandon`'s reason |
| `name_lemmas.bend` | `name_stays_in_names`: a name `name` takes is never absolute and never climbs out with `..`, so the bookmark's file is under `names/` — every refusal `check_name` and the path rules make stepped past to the two a climbing name would meet; `name_reads_its_words`: `--delete` and `--fields` are asked for where they are among the words, the pin and the privacy are the last of each pair said, and the flags shaping a target and the other words are each kept in order; `name_does_what_it_reads`: a deletion only where `--delete` was said, of the one other word, with nothing shaping a target, and otherwise a bookmark set of the other words in order, never a file pinned; `name_points_where_asked`: the bookmark set has the name given and points at what its target names as `resolve` reads it — that revision, the change it carries, or the file `show` names at it and the path, as asked — as private as asked or as it was; `name_deletes_the_bookmark_named`: `--delete` is refused exactly where no bookmark has the name, and otherwise reports the store's bookmark of that name; `name_states_what_it_set`: `--fields` says its header once, early or late, and then `name` | `store::check_name`, `name` |
| `listing_lemmas.bend` | `files_lists_in_path_order`, `files_lists_the_tree`: `files` prints the tree's entries sorted by path and file, under each the ones the tree holds, each line ending with its file identifier; `bookmark_file_reads_back`: `names/`, a name `Bm.name_ok` accepts and `.txt` — the file `name` writes — is read back as that name; `bookmarks_read_in_name_order`, `bookmarks_read_each_once`: the bookmarks are read sorted by name, and under each name are exactly the paths the store lists that `Bm.name` reads as it, each with its own path, as many and in the order listed, read from the listing itself rather than through `named`; `names_lists_each_bookmark`: `names` prints a line for each bookmark read, in order, beginning with its name and two spaces and, for a pin or a change, ending with where it resolves — and `no bookmarks here yet` where there is none; `names_resolves_to_held`: a pin the store holds, or a change's one current revision, is said as an abbreviation of that revision's digest — a prefix of it, eight characters at least, that no other held digest of its length begins with — a pin it lacks as `(not here yet)`, and any other change as a reason in parentheses; `log_fields_lists_what_it_keeps`: `log --fields` prints its header and then lines each beginning with the whole digest of a revision the span shows that every filter admits, no more of them than `--limit` allows; `log_counts_each_fact`: an entry's figures are how many `add`, `move`, `drop` and `edit` facts its revision states, and how many `mode`, `link` and `bytes` facts about a file no `add` fact names, given that a `Set` built from a list holds exactly its members; `log_follows_a_held_file`: the file `--path` follows is one the tree holds where it is read | `files`, `names`, `log`'s printing |
| `presentation_lemmas.bend` | what `log`'s walk presents is what it was shown: its frontier, the table of revisions it has not reached and what it prints hold only revisions of the list it was given, since setting a key in Base's `Map` invents no value and popping one gives back a value the map held — the step `log_fields_lists_what_it_keeps` takes | `log`'s order |
| `record_lemmas.bend` | `record_reads_its_words`, `record_reads_renames_and_paths`, `amend_reads_its_words`, `abandon_reads_its_words`, `carry_reads_its_words`: after any words a command has read, one word more does what its plain reading says, spelled out field by field and refusal by refusal — which flags each command takes, the last `-m` and `--onto` counting, `--merge`, `--at`, `--move`, `--bytes` and `--lines` adding after the ones before, a value cut at its first `=` and kept whole after it, a word not beginning with `-` a path or a target refused as a second, a trailing `/` changing nothing; `record_restricts_no_merge_and_no_half_rename`, `record_names_only_what_is_there`, `record_gives_kinds_only_to_files`, `record_moves_only_held_files`: the restriction check goes on exactly where no path is named, or where there is one parent at most and both ends of every `--move` are covered, a path named is refused exactly where it answers to nothing, every path `--bytes` or `--lines` named is a file the folder holds, and every file a stated rename moves is one the position holds; `record_writes_only_what_is_settled`, `record_says_an_arrival_once`, `record_reads_lines_as_text`: what it goes on to write is the survey's plan unchanged, neither the walk nor the survey having refused a path, no file still holding a line the renderer wrote and no contested file of lines observed empty, every link of the position anchored, and the paths accepted being exactly the contested ones, whose dry run names an arriving file — read against the list of what arrives — on its `added` line alone, and an arriving file `--lines` names is read and its bytes are UTF-8; `record_states_the_folder`: each edit, applied to the store's replay of that file at the position, gives the folder's lines, text is the folder's bytes and a payload is named by the digest the walk gave its path; `record_resolves_as_the_walk_proposes`: where the parents being joined leave a file differently, it states the resolution `Conflict.resolve` makes of the walk of those parents and the folder's lines; `record_names_what_it_writes`, `record_moves_the_bookmarks_on_its_parents`, `record_moves_only_the_bookmarks_on_its_parents`: the revision's stem begins with the name its moment, message and change compose and is that name exactly where no held revision has it, and the bookmarks moved are exactly the store's bookmarks on the change of the first revision it lists under a parent's identifier | `record`'s arguments, survey and writing |
| `rewrite_lemmas.bend` | `carry_says_what_it_files`: with `--fields` a carry names exactly the revisions it files, each once, in digest order, each by the digest of the bytes it files, the name the store reads it back under; `abandon_takes_a_line`, `abandon_abandons_only_a_word_it_was_given`, `abandon_refuses_a_dry_run_with_fields`, `abandon_dry_run_names_the_run`: `abandon` takes a line of work nothing has rewritten, each revision after the first standing on the one before it alone, goes on only with a target that is one of its words and not a flag, refuses `--dry-run --fields` after any words it reads as a usage error, and a dry run says a line for each revision of the run, in order, by the first twelve letters of its digest and then only the bookmarks there, then that a tombstone would supersede them, then only what it would carry; `reword_changes_only_the_message`: a reword's message is the one `-m` gave and not the old one, and with the old one put back it says what the revision said; `amend_rewrites_the_revision_named`, `amend_rewrites_the_one_head`, `carry_carries_a_held_revision`, `amend_keeps_what_it_added`: what `amend` rewrites is the revision its target resolves to or, with none named, the store's one current head, what `carry` is asked to carry is a revision the store holds, and an amendment gives every arrival an identifier, each file it added keeping its own; `writes_say_what_they_wrote`: with `--fields` all four writing commands say `historica-wrote-1` and then, read back from their `revision` lines, exactly the revisions they wrote, each once, in digest order | `amend`, `abandon`, `carry`, decisions 0013, 0023, 0059 and 0074 |
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
| `plan_lemmas.bend` | `diff_folder_compares_like_with_like`: over the folder, what `diff` replays and reads of each path follows from what each side holds there — a file only the folder holds read and nothing replayed, a file of bytes or a link the position holds neither, a file of lines against anything but a regular file replayed and nothing read, and against a regular file replayed exactly where the folder's is read; `diff_folder_believes_a_stated_digest`: a file of lines whose nearest statement is `text` and a digest is replayed and read exactly where the host's first word for its path is another | `diff`'s reading of the folder |
| `chain_lemmas.bend` | `chain_follows_first_parents`: the line a file's nearest statement is looked for along begins at the position and follows first parents, each a revision the store holds, and stops where that line does — after a revision with no parent or a first parent the store does not hold, or at once of a name it does not hold — or else after 1 + n revisions of a store of n | the first-parent line |
| `sizes_lemmas.bend` | `diff_sizes_only_what_the_host_stated`: sizing what `diff` compares changes no side but a file of bytes whose size was unknown, which keeps its digest and has a size only where a line the host answered names that very digest; `diff_sizes_what_the_host_stated`: where the host answered the stat of a payload it located with its digest, a space and a size, a file of bytes with that payload is shown with that size | `diff`'s sizes |
| `fetch_lemmas.bend` | `diff_folder_plans_by_the_edits_it_fetches`: `diff` over the folder plans each path from nothing the store holds but the `edit` documents it asks for — any documents that answer those digests as the store's do give the store's plan; `reading_finds_what_resolutions_keep`: where the store answers each digest a reader asks for after its first documents with a document under it, every `keep` of every resolution among those finds one; `diff_asks_every_payload_it_shows`, `diff_asks_each_payload_once`, `diff_stats_where_each_payload_was_found`: the host is asked about exactly the payloads shown, none twice — `List.sort` puts every item in order and keeps each, and `distinct` leaves each once — and the stat of each only where it located that payload | what `diff` asks the store and the host |
| `fulls_lemmas.bend` | `revisions_read_are_their_documents`: every revision `fulls` reads — what `record`, `amend`, `forget`, `merge`, `update` and the other writing commands read — is one a document of `revisions/` spells, under the digest it is known by, byte for byte as `Rev.write` writes what the revision says — or, where the parser refuses it and a path it states is not in normal form C, with the refusal naming that path and line in place of its facts and the rest what the mended document says; `revisions_read_lose_no_document`: every document of `revisions/` that reads whole so is read; `unnormal_names_its_line`: the line such a refusal names is an `add` or `move` header, among the headers, ending in the path it names, which is not in normal form C; `mended_changes_only_path_headers`: mending leaves the message and every other header as they were, line for line | `Store::revisions` |
| `span_lemmas.bend` | `log_lists_its_span`: with a target, every revision `log` goes on with is one the store holds, the target among them wherever the store holds it and every other a parent of one of them, through an invariant of the walk out from the target — in a store without a cycle, only the target's ancestry; and where the store files each revision once, every parent the store holds of one of them is among them too, through a second invariant, that each parent of a revision taken in is taken in, waiting, or not the store's, and a count of the steps the walk owes, which the steps it is given always cover; with `a..b`, what `log b` lists and `log a` does not, no more and no less | `log`'s ranges |
| `logargs_lemmas.bend` | `log_reads_its_words`: `log` reads its arguments as their plain reading says — the word after a flag that takes a value is its value, the last counting, `--limit`, `--since` and `--until` read as a count and bounds, `--fields` asked for if it is there, and the other word the target | `log`'s arguments |
| `check_lemmas.bend` | `check_pairs_each_payload`: `check` reports each payload with the digest asked for it — one per payload in the order found, none taken by an operation document; `check_walks_causally`: the order it walks a merged file's events in places each after every event its author had seen; `check_reads_its_words`: `--complete` is read wherever it stands, and every other word, in order, as a directory | `check` |
| `finding_lemmas.bend` | `check_reports_errors_then_notes`: `check`'s report is every error in the order found, then every note, then how many of each — `nothing to report` only where nothing was found — and how many heads cannot be produced; `check_fails_on_an_error`: it fails exactly where it found an error, and with `--complete` where it found a head it cannot produce; `check_follows_the_bookmarks_name_writes`: a bookmark file `name` wrote reads back as that bookmark, drawing nothing where what it points at is here and one note otherwise; `check_reads_each_line_of_a_listing`: each line of a directory's listing is read as the host writes it, a link's target passed over whatever it says; `check_reads_only_held_text`: every `text` payload read as a file's lines is one the store holds, under a digest some `text` header names, read from where it holds it | `render::report`, `Report::is_ok`, `store::check`, `store::walk` |
| `skip_lemmas.bend` | `skip_path_rule_reads_back`, `skip_name_rule_reads_back`: the file `skip` writes for a path or a name it accepts is read back by the reader of `skipped/` as exactly the rule meant, private or not — a line the reader splits, trims and keys as `Skipped::rule_in` does; `skip_path_rule_skips_under_its_path`: that rule skips the file, or the directory whole and every file under it; `skip_path_rule_skips_nothing_else`, `skip_path_rule_skips_no_other_directory`: and a file it skips is the path named or, for a directory, that path, a `/` and the rest, and a directory it skips whole is the one named; `skip_reads_its_words`, `skip_reads_flags_as_flags`: spelled back, what `skip` read is the words it was given, no word it reads as a path is a flag, and it stops only at a flag it does not take; `skip_private_wherever_it_stands`, `skip_shares_without_private`: `--private` makes every rule private wherever it stands, and without it every rule is shared; `skip_reads_the_path_past_the_repository`, `skip_refuses_the_repository_itself`, `skip_refuses_a_path_outside_the_repository`: a rule's path is what lies past the repository, and the repository itself and a path outside it are refused; `skip_covers_nothing_history_holds`: where `skip` goes on to write, no rule it writes skips a file any head holds (decision 0011); `skip_lists_each_rule_once`: the listing names every rule the files state and none twice; `skip_writes_what_is_new`: what `skip` writes is no rule the store states and none twice, and every rule asked is written or already there; `skip_rules_equal_only_when_equal`, `skip_rule_equals_itself`: rule equality is equality, so "held" is membership | `cli::skip`, `cli::path_scope`, `working::Skipped` |
| `argv_lemmas.bend` | `argv_reads_its_words`: `-C <dir>` is read as often as it is given, the last counting, and the command word and every word after it — a `-C` among them — are the command's, as written; `argv_reads_the_version`, `argv_reads_help`: `-V` and `--version` read as the version, and `help`, `-h` and `--help` as the usage, whatever `-C`s come before them and whatever follows | `cli::run` |
| `shell_lemmas.bend` | `dispatch_runs_no_path`: the program a word is dispatched to holds no `/`, so it is looked up on `PATH` rather than run from where a path would put it; `dispatch_runs_a_spelled_word`, `dispatch_refuses_any_other_word`: a word is looked for exactly when it is ASCII letters and digits, as Base classes them, with hyphens only between, and what runs is `historica-` and the word | decision 0072 |
| `opening_lemmas.bend` | `header_opens_under_a_note`: a store's header opens whatever its note says, once a blank line sets the note apart — the one `init` writes among them | `Store::open`, decision 0069 |
| `init_lemmas.bend` | `init_lays_down_only_its_store`: every directory `init` makes and every note it writes is its root, a `/` and components none of them empty, `.` or `..`, each note in the root or a directory it makes, whatever the root; `init_writes_text`: every note is lines of Unicode scalar values that are no control character, each ended by a newline; `check_finds_nothing_in_a_new_store`: the store `init` lays down holds no document, and what `check` gathers from it — `historica.txt` and `skipped/`'s note read back from the bytes written — it finds nothing wrong with; `init_takes_an_absolute_dir_as_it_is`, `init_doubles_no_slash`, `init_keeps_a_dot`: `<dir>` is joined as `Path::join` joins it — an absolute one wherever `init` runs, a `/` after it not doubled, `.` not resolved | `Store::init`, `cli::init` |
| `utf8_lemmas.bend`, `utf8_lemmas.py` | `utf8_reads_back`: a string of Unicode scalar values, encoded as UTF-8 and read back as the store reads a file as text (`read_to_string`), is itself — `invalid` finds nothing wrong with the bytes, and `decode` gives back every character. Each code point is taken apart into its thirty-two bits: the width `encode` gives it shows the bits above that width clear; each bit `decode` puts back is shown to be the one it came from, a bit at a time so that no case split multiplies another; and each byte is shown to be one the validator takes — a lead or second byte by the few bits that decide it, after `E0`, `ED`, `F0` and `F4` included, a continuation byte whatever bits it carries. `utf8_lemmas.py` writes out the lemmas that say the same of every bit and every lead | `str::from_utf8`, `char::encode_utf8` |
| `opened_lemmas.bend` | `opening_reads_what_a_revision_states`: what opening a store reads of a revision it accepts is the change, author and time its first `change`, `author` and `when` lines say, every `parent` and `supersedes` line in order, and the message after the blank line as written | `format::revision`, decision 0061 |
| `identity_lemmas.bend` | `identity_reads_back`: the file `identity` writes reads back as its author for work in any directory, wherever that author is one a revision can hold; `identity_takes_the_environment_first`: `$HISTORICA_AUTHOR`, set and not empty, decides before any file is read; `identity_file_is_where_the_rust_tool_looks`, `identity_makes_the_files_directory`: the file is where `identity_path` puts it, and the directory `identity` makes is the one it is in; `identity_reads_its_blocks`: a file of blocks reads back as the default author and every directory's, in order; and nine laws, `identity_refuses_…`, one for each refusal the Rust tool makes of a file, each after any such blocks and at the line it names; `editor_file_is_in_the_temporary_directory`: the editor's file sits directly in `$TMPDIR` or `/tmp` | `record::identity`, `identity` |
| `editor_lemmas.bend` | `editor_is_the_one_chosen`: the editor is `$VISUAL`, `$EDITOR` only where `$VISUAL` is not set, and none where the one deciding is empty; `editor_is_read_only_when_it_saved`: what it leaves is read only where it exited 0 | `cli::from_an_editor` |
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
Every revision `fulls` reads — the reading `record`, `amend`, `forget`,
`merge`, `update` and the other writing commands open the store with — is
one a document of `revisions/` spells, under the digest it is known by, and
what `Rev.write` writes of it byte for byte, or, where the parser refuses
it for a path not in normal form C, that refusal over what the mended
document says (`revisions_read_are_their_documents`); the line the refusal
names is the header naming that path (`unnormal_names_its_line`), and
mending changes nothing but such headers (`mended_changes_only_path_headers`).
Every document there that reads as a revision is read
(`revisions_read_lose_no_document`). The commands that ask what a revision
did open the store with `opened.fulls`, which also holds revisions only an
opening accepts, and no law here speaks for those.
`opdiff` writes an operation document the Rust tool reads, `result`
included. `cat` of a
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
`historica-log-1` listing; whatever the filters, it goes on with what its
span names — the target wherever the store holds it, parents of what it
lists and, where each revision is filed once, every parent the store holds
of what it lists, and of `a..b` what `log b` lists and `log a` does not
(`log_lists_its_span`). The walk out from a target is given a step for
each digest it starts from and each parent the store names; twice the
store's length, which it was given before, left most of an ancestry behind
where merges joined more than two, and `check.py`'s `wide` store, of
six-parent merges three deep, holds it to the Rust tool there. A timestamp is held to the calendar now — a leap
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
tool resolved, six written by hand to fail each way, and one keeping its
first line twice, which `cat` assembles and a walk reaching across it
refuses.

`diff <target> [<path>]` renders what a revision did, and `--onto` what one
revision holds against another: the facts about each file first — new,
deleted, renamed, a mode, a link's target — then its hunks, three lines of
context around each change, or the digest and length of a file of bytes;
`blame <target> <path> [--lines <first>..<last>]` names the change, author
and day that wrote each line. Two sides hold the same content for a file
where the same revisions stated it, so only the files that differ are
replayed, and for each of those everything a revision states of it is
fetched first, with whatever a resolution among them keeps: once the store
has answered each of those, every `keep` of every resolution fetched finds
a document to take its items from (`reading_finds_what_resolutions_keep`).
A file of bytes is shown with the size the host gives it: the host is asked
about exactly the payloads shown, and about each once
(`diff_asks_every_payload_it_shows`, `diff_asks_each_payload_once`), its
stat only where it located the payload
(`diff_stats_where_each_payload_was_found`), and a size is
believed only where the bytes found there hash to that very payload,
sizing changing nothing else (`diff_sizes_only_what_the_host_stated`), and
where the host answered with that digest and a size, the file is shown
with that size (`diff_sizes_what_the_host_stated`). What is laid over the
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
path the format cannot hold. A name matches exactly as its pattern reads,
each `*` any run of characters: every name the pattern spells with some run
for each `*`, and no other (`a_pattern_matches_each_name_it_spells`,
`a_pattern_matches_only_names_it_spells`). `diff` compares it with the
head, or with what
`--onto` names, a path or `file:` limiting it to one file; the folder has
no identifiers, so a file that moved there is a loss and an arrival. A file
the position holds as lines must still be text, and one it does not is
lines or bytes as decision 0017 sniffs it. `blame <path>` attributes the
folder's lines as far as history can and marks the rest `(the folder)`. A
file of lines is read only where the host's digest of it is not the one its
nearest statement on the head's first-parent line leaves, so `diff` over
the archive's folder takes 1.4 s. What it replays and what it reads of
each path follow from what each side holds there: never a file the
position holds as bytes or a link, and a file of lines against a regular
file is replayed exactly where the folder's is read, so a stand-in is only
ever compared with a stand-in (`diff_folder_compares_like_with_like`);
where the file's nearest statement is `text` and a digest, that is exactly
where the host's first word for its path is another
(`diff_folder_believes_a_stated_digest`); the line the statements are read
along follows first parents from the position to where that line ends
(`chain_follows_first_parents`);
and what a replay needs is fetched before it. The plan is read from nothing
the store holds but the `edit` documents fetched for it, whose results are
the digests that can settle a file: any documents that answer those digests
as the store's do give the plan the store's give
(`diff_folder_plans_by_the_edits_it_fetches`). A statement settles a file
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
a resolution — `refused` where it is no longer text, and where the folder
holds it empty, nothing at all: the Rust tool's report has no line for a
merge that would empty a file, which only `record` refuses, and neither
has this one (`docs/tasks/saying-a-merge-would-empty-a-file.md`). Where
such a file still holds lines the renderer wrote for this merge — a label
or a closing line its fences draw, and the walk's own file does not hold —
`status` says it is `marked`, with how many are left, as
`conflict::unresolved` counts them; a file quoting a fence some other merge
drew is not marked, since the lines are scoped to this one. Where the walk
of their union refuses — a resolution behind one of them keeping a line
more often than its author's view held it, say — `status` refuses with the
walk's reason, as the Rust tool's survey stops there, and so does
`record`.

What the reading commands and `status` print is decided before anything
is printed: each builds its lines — an entry of `log`, a line of `files` or
`names`, the report `status` makes of its survey — and one `print_lines`
prints them, so a law can read what they say, and `check.py` holds the
same bytes. `files` lists each file of the tree once, in path order;
`names` reads the file `name` writes — `names/`, the name and `.txt` —
back as that name, wherever the name is one `Bm.name_ok` accepts, and lists
every bookmark once, in name order, under each name exactly the files the
store lists that are its, in the order listed; each line begins with its
name, and says where a pin or a change resolves as the abbreviation of the
revision it names — one no other digest the store holds begins with — or
why there is none; `log --fields` lists, by its whole digest, only
revisions its span shows that every filter admits, never more than
`--limit`; an entry's figures are what its revision's facts state; and
`--path` follows a file the tree holds. `status` says everything its survey
found, each on a line naming it, and where work is joined each contest but
a claimed path once, naming its file; against one revision it compares the
folder with the tree `files` reads there; it tells its survey of each path
once, with the host's answer for it as the folder's digest; it reads and
replays only files of lines, believes a digest a statement gives, and is
refused only where a replay is; and joining, it compares each file with
what the parents' readings of it join to, and settles none they read
differently. What no law reaches
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
still claim, what nothing here can take, a file of a merge still holding
lines the renderer wrote — each named with how many are left — a merge
that empties a file, and contested bytes accepted or not. And `--move` renames in the folder before
anything is read, as the Rust tool does, dry run or not — through
`Store.move`, which renames and answers which of the four cases the folder
was in. `check.py` runs each `record` on a
copy of the store of its own, per tool, and compares the folder after as
well as what was said: 90 commands across fourteen stores, one of them
`claimed`, built for the merge refusals — two files added at one path,
settled with `--at` by file bookmark, bytes written two ways, and a link to
a file the folder dropped. A usage error is now compared too, to the end of
its message.

`record` writes, too. It mints an
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

`record --merge` records a merge, decision 0032, and says it joins as
many lines of work as the revision has parents. A file the parents agree
about is stated as `record` states any; one they leave differently owes a
resolution (`conflict.bend`), stated against what the walk of their
union proposes. `similar`'s Histogram diff aligns the proposal with what
the person left, checked in one pass as `diff`'s moves are, and each line
that survived is named — `keep`, the digest of the document that minted
it and its ordinal there, a run of one document's consecutive items as
one — while what the person wrote is `insert`ed. A line restated rather
than named would be a new item, which the first merge reaching across
this one would meet twice. `merge_resolution_reads_back` is the promise
this keeps: the resolution written for a file, assembled as `cat`
assembles one, is exactly the file the person left, its digest the one
`cat` checks, wherever the store's documents mint each element as the
walk read it. `resolved` is the `meeting` merge laid out by `merge` and
resolved by hand, file by file, then recorded three ways — `--onto` and
`--merge` in either order, `--fields`, a message at length — each
compared whole with what `historica-pinned` writes; `meeting` records the
merge where the folder holds one side's work alone.

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
`status` refuses is what its walk refused, as the walk found it, and then
only a link whose target the format cannot hold or a file of lines that is
no longer text, each said as such — never a path only the position holds
(`status_refuses_what_the_folder_holds`); and a rename it offers is from
the one path that left holding some bytes to the one that arrived holding
them (`status_offers_a_rename_the_bytes_make`). `record` goes on exactly
where each path named covers something the folder, the position or the
renames hold, whatever the rules say (`record_names_only_what_is_there`),
and, restricted to some paths, refuses only among them, whatever the
folder and the store answer (`record_refuses_only_what_it_looks_at`); it
states a kind only for a path it looks at where no file of the position
is (`record_states_a_kind_only_for_an_arrival`), goes on only where each
path it looks at holds one file
(`record_goes_on_where_each_path_holds_one_file`), writes a link as a
reference only to the file the revision holds where its target lands
(`a_link_refers_only_to_what_the_revision_states`), and one never outside
the folder (`a_link_resolves_inside_the_folder`), keeps a link to a file
it drops only where the folder holds a link at its path
(`record_refuses_a_dangling_link`), and writes one `move` line for each
file moved and kept, at the last place the renames put it
(`record_moves_each_file_once`). The position it goes on with holds every
file once, none lost or doubled (`a_rename_keeps_each_file_once`), and with
`--at` alone has each file where the last `--at` naming it said, every
other where it was (`a_rename_puts_each_file_where_it_was_said`). A revision's stem is its month, a `/`,
and a name holding nothing a filesystem reserves
(`a_revision_is_filed_under_its_month`), its summary sixty characters at
most (`a_summary_fits_its_limit`) and never beginning or ending with a dot
or a space (`a_summary_gives_up_its_ends`); each file of content is filed
under a name with no control character
(`content_is_filed_under_a_name_a_filesystem_holds`); the clock is compared
with the timestamps of the work the store holds, and a warning given exactly
where one is later (`record_compares_with_the_latest`), naming the latest
(`record_names_the_latest_work`), each read at the offset it spells
(`a_timestamp_is_read_at_its_offset`); and `abandon` takes a reason exactly
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
draw, write and print what they are handed. Each reads its words one at a
time, and one word more after any words it has read does what its plain
reading says: `record_reads_its_words` and `record_reads_renames_and_paths`
spell out what each flag, value and path does to what `record` has read,
field by field, and each refusal word for word, and `amend_reads_its_words`,
`abandon_reads_its_words` and `carry_reads_its_words` do the same for the
others, with the flags each takes and the second target each refuses. The
restriction check goes on exactly where no path is named, or where there is
one parent at most and both ends of every `--move` are among the paths
named (`record_restricts_no_merge_and_no_half_rename`). A path named is
refused exactly where it answers to nothing
(`record_names_only_what_is_there`), every path
`--bytes` or `--lines` named is a file the folder holds
(`record_gives_kinds_only_to_files`), and every file a stated rename moves
is one the position holds (`record_moves_only_held_files`). What it goes on
to write is the survey's plan unchanged, and one the survey settled:
neither the walk nor the survey refused a path it looked at, no file
still holds a line the renderer wrote, no contested file of lines was
observed left empty, every link the position holds is anchored, naming no
file the record drops unless it goes too or the folder holds a link at its
path that this format can hold, and the paths `--accept` names are exactly
the ones the survey found contested (`record_writes_only_what_is_settled`),
whose dry run names an arriving file on its `added` line alone
(`record_says_an_arrival_once`); an arriving file `--lines` names is read,
and where `record` goes on its bytes are UTF-8
(`record_reads_lines_as_text`). What it states each file holds is what the
folder holds: each edit, applied to the store's replay of that file at the
position, gives the folder's lines, text is the folder's bytes, and a
payload is named by the digest the walk gave its path
(`record_states_the_folder`); where the parents being joined leave a file
differently, the resolution it states is the one `Conflict.resolve` makes
of the walk of those parents and the folder's lines
(`record_resolves_as_the_walk_proposes`). The revision is filed under a stem that
begins with the name its moment, message and change compose, and is that
name exactly where no revision the store holds has it
(`record_names_what_it_writes`), and the bookmarks it moves are exactly the
store's bookmarks on the change of a parent: a parent named being the
identifier of a revision the store holds, the first it lists with that
identifier, each bookmark on that revision's change moves, name and privacy
kept, and each bookmark that moves is one of those
(`record_moves_the_bookmarks_on_its_parents`,
`record_moves_only_the_bookmarks_on_its_parents`). Neither law reads the
parents' changes through the lookup `record` makes; each states them from
the parents named and the revisions the store holds. An amendment rewrites the revision
its target resolves to, as every command resolves that spelling
(`amend_rewrites_the_revision_named`), or with none named the store's one
current head, refusing where there are several or none
(`amend_rewrites_the_one_head`), and keeps the identifiers it minted
(`amend_keeps_what_it_added`); a reword changes the message alone
(`reword_changes_only_the_message`). `abandon` goes on only with a target,
one of its words and not a flag, so nothing is abandoned by default
(`abandon_abandons_only_a_word_it_was_given`); whatever words it reads,
`--dry-run --fields` after them is a usage error
(`abandon_refuses_a_dry_run_with_fields`); and it wants a reason that says
something (`abandon_takes_a_reason_that_says_something`). It takes a line
of work nothing has rewritten, each revision after the first standing on
the one before it alone (`abandon_takes_a_line`), and a dry run says that
line and nothing else: each revision in order by the first twelve letters
of its digest and then only the bookmarks there, the tombstone, and what
it would carry (`abandon_dry_run_names_the_run`). A carry acts on a
revision the store holds (`carry_carries_a_held_revision`), and with
`--fields` names exactly the revisions it files, each by the digest of the
bytes it files, which is the name the store reads a document back under
(`carry_says_what_it_files`). With `--fields` all four say what they wrote
in decision 0074's words: read back from the `revision` lines, exactly the
revisions they were handed as written — their own and the ones they
carried — each once, in digest order (`writes_say_what_they_wrote`). What
no law reaches is the order of their effects, what the host draws and
files, and that a carry keeps whose work it restates and when it was done:
that holds by construction, and saying it of what the store reads back
would need the parser to read back what `Rev.write` writes, the direction
`revision_write_parse` does not prove.

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
`name_does_what_it_reads`), the bookmark it sets, at what its target names
as every command resolves it (`name_points_where_asked`),
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
What `init` lays down is pure: the layout relative to a root
(`init.laid`), put under the root it joins (`init.layout`, `init.root`),
which the IO shell makes and writes as handed, and which `export` lays
down for its copy too. The laws say it writes nothing outside that root
and each note into a directory it makes (`init_lays_down_only_its_store`),
that every note is `format.txt`'s "UTF-8 text with Unix line endings"
(`init_writes_text`), that `check` finds nothing wrong with what it lays
down, read back from the bytes written (`check_finds_nothing_in_a_new_store`),
and that `<dir>` is joined as `Path::join` joins it
(`init_takes_an_absolute_dir_as_it_is`, `init_doubles_no_slash`,
`init_keeps_a_dot`).

A document that does not parse is refused in the Rust tool's words
(`words.bend`), on the line it names. The parsers here decide whether a
document is accepted, and their proofs are about that; where one refuses,
the document is read over again in the Rust reader's own order —
`OperationDocument::parse`, `ResolutionDocument::parse`,
`RevisionDocument::parse`, and `format::revision`, the reading that opens a
store, which splits and weighs a revision's headers a line at a time and
reads only the values that name revisions — and the first thing that
reading refuses is what is said. Opening a store refuses the first revision
whose shape does not read, for every command, naming the file; a revision
that reads that far and not whole is in the graph, and a command asking
what it did — `log` before it prints, `show`, the tree `files` and `cat`
read, the ancestry `blame`, `status` and `diff` read — is refused naming
it, a head listed with only its digest and change. An operation document
or a resolution that does not parse is found the first time something asks
what it says, as `what the revisions did could not be read`. `check.py`'s
`-invalid` stores file every document of the corpora that does not parse
among the ones that do, and `unreadable` names two from a revision;
`log`, `files`, `show` and `cat` at every revision, and `check`, say what
the Rust tool says.

The command line is read as the Rust tool's `run` reads it (`argv.bend`):
`-C <dir>` as often as it is given, the last counting, and every command
then runs as if started there — the store found from there, a path argument
read from there, `init` making its store there; `help`, `-h`, `--help` and
no words at all print the default build's usage text, which `notes.py`
takes from `historica help`, and `-V` or `--version` the workspace's
version, which `check.py` holds to `Cargo.toml`; any other word starting
`-` before the command is refused. A usage error prints its message, a
blank line and the usage, and exits 2 (`shell.bend`). A word no command
here has is decision 0072's: spelled in ASCII letters, digits and interior
hyphens, it is looked up on `PATH` as `historica-<word>` and run in `-C`'s
directory with the process's own streams, and the tool ends with its code
(`Store.run`, `Store.exit`) — the directory, the program and each argument
handed over with a NUL between, which the host's split gives back each
whole (`run_asks_for_what_it_names`); a program that is not there is "there is no
such command", one a signal ends or that will not start is said, and a
word spelled otherwise is never looked for: exactly the words Base's
classes of character make ASCII letters and digits with hyphens only
between them run (`dispatch_runs_a_spelled_word`,
`dispatch_refuses_any_other_word`), and none with a `/` in it
(`dispatch_runs_no_path`). The store is the nearest
`history` directory, and one without `historica.txt` is refused as not a
store rather than looked past; its header is decision 0069's gate — the
format line, a pre-1.0 `historica-vN` told so, a line under it refused as a
layout only a newer Historica writes, and a note under a blank line read
past (`header_opens_under_a_note`). A writing command asked for `--fields`
that fails for any reason but its words prints decision 0074's
`historica-wrote-1` first, a store that will not open included, and not
where `record`, `amend`, `abandon` and `carry` find no store, which the
Rust tool looks for before it reads their words. `check.py`'s `shell` and
`headless` stores hold all of it.

Who records is `$HISTORICA_AUTHOR` where it is set and not empty, refused
where it names one no revision can hold, before any file is read
(`identity_takes_the_environment_first`), or else what the identity file
under `$XDG_CONFIG_HOME` or `~/.config` says for the repository
(`identity.bend`): a block of `author` alone is the default, a block headed
`under <dir>` — `~` for the home — the author for work beneath it, the
deepest holding the repository winning, and every way a file is not blocks
of keys and values refused with its line. The file is where the Rust
tool's `identity_path` puts it (`identity_file_is_where_the_rust_tool_looks`);
a file of blocks reads back as the default author and every directory's,
in order (`identity_reads_its_blocks`), and after any such blocks each way
the Rust tool refuses a file is refused at the line it names — two authors
or two directories in a block, `under` after the author, a directory with
no author, a second default, a directory claimed twice, a key it does not
know, a value no revision can hold and a line with no space
(`identity_refuses_…`). `identity <author>` writes the file where there is
none, making the directory it goes in
(`identity_makes_the_files_directory`), and the file it writes reads back
as that author (`identity_reads_back`). `record` and `abandon` given no
`-m` ask `$VISUAL`, or `$EDITOR` where `$VISUAL` is not set at all, for
the message (`editor.bend`, `editor_is_the_one_chosen`): the editor is run
on an empty `historica-message` directly in the temporary directory
(`editor_file_is_in_the_temporary_directory`), in `-C`'s directory, and
what it leaves is the message, nothing stripped, as decision 0011 has it;
one that fails or stops with any code but 0 stops the command
(`editor_is_read_only_when_it_saved`), and one set but empty is a usage
error. The `identity` and `editing` stores hold both
to the Rust tool, each command given a home, a configuration directory and
a temporary directory of its own inside the store it runs on.

`skip` lists the rules `skipped/` states, in the order the loader walks
them, and writes one for each path, directory or `--name` pattern it is
given, one to a file, `--private` keeping a rule's text out of an export
(`skip.bend`). A rule is written under its label — the path scrubbed of
control characters, as `<path>.txt` or `<path>/all.txt` or `name
<pattern>.txt` — or under the first twelve characters of its digest where
that cannot be a file or is another rule's; one already stated is said so,
and every refusal is the Rust tool's, in its order: outside the
repository, space at either end, a `/` in a name, and any rule covering a
file some head holds. The `skipping` and `badskip` stores hold it. What
it writes is proved to read back: the file for a path or a name it accepts
is, to the reader of `skipped/`, exactly the rule meant, private or not
(`skip_path_rule_reads_back`, `skip_name_rule_reads_back`), and that rule
skips what was named — the file, or the directory whole and every file
under it — and nothing else: not a path that only begins with the one
named, and nothing under a file's (`skip_path_rule_skips_under_its_path`,
`skip_path_rule_skips_nothing_else`,
`skip_path_rule_skips_no_other_directory`). What it writes is new to the
store and named once, and nothing asked is lost
(`skip_writes_what_is_new`); its listing names every stated rule once
(`skip_lists_each_rule_once`). Those two are stated over a membership
that is proved to be equality, not over the equality the code asks. Its
words are read in a pure def, `Skip.read`, before a path is resolved
against the store: spelled back, what it read is the words it was given,
no word it reads as a path is a flag, and it stops only at a flag it does
not take (`skip_reads_its_words`, `skip_reads_flags_as_flags`), and the
IO says that refusal once every word before it has had its say.
`--private` makes every rule private wherever it stands, and without it
every rule is shared (`skip_private_wherever_it_stands`,
`skip_shares_without_private`). A rule's path is what lies past the
repository, over the components `Path::components` reads, and the
repository itself and a path that stops or turns aside before the
repository ends are refused (`skip_reads_the_path_past_the_repository`,
`skip_refuses_the_repository_itself`,
`skip_refuses_a_path_outside_the_repository`). Decision 0011 is decided
in a pure step over the paths every head's tree holds: where `skip` goes
on to write, no rule it writes skips, by the loader's own `skips`, a file
any head holds (`skip_covers_nothing_history_holds`).

`check [<dir>] [--complete]` reads the store as `Store::check` does and
reports as `render::report` does (`check.bend`): the header refused or not
there, every file of `revisions/`, `operations/`, `skipped/` and `names/`
walked as the store walks them — a link found and never followed — each
document hashed and parsed, and each payload's digest and size asked of the
host rather than carried through a hash here, and paired with its own
(`check_pairs_each_payload`). It finds files nothing reads, names that
claim a digest they do not hash to, one document stored twice, parents,
documents and payloads not here yet, content forgotten and content back
again, work standing on a superseded revision, chains that do not replay
and merges that do not say what they resolve, stale, retired and duplicated
skip rules, malformed and dangling bookmarks, and heads the store cannot
produce, which only `--complete` fails on. A file past a merge, or in a
history that forgets something, is walked as `merge::quotes` walks it:
each event stating what the store holds for the file, nothing where it
holds none, in Kahn's order by digest, which places each event after all it
had seen (`check_walks_causally`); the first event its author's view
refuses says why in `MergeError`'s words. `check.py` asks `check` and
`check --complete` of every store, and has four built to be found wanting:
`damaged`, `gutted`, `tampered`, and `redacted`, the corpus that forgets a
payload, beside the forgetting documents of it that do not parse; and it
asks them of `forgotten` and `forgetting` too, where the Rust tool's own
`forget` destroyed the lines and bytes. A line
forgotten where one revision wrote it and another deleted it is sought at
every site that still holds its text (`StillQuoted`): `quoting` and
`requoted` bring one of the two documents back without its forgetting, the
deleter's and the writer's. A bookmark or a rule file whose bytes are not
UTF-8 is refused by every command as the store opens, in `Utf8Error`'s
words, and is an error to `check` (`unnamed`, `unruled`).
What `check` says is held to a reading of its findings as a list: every
error in the order found, then every note, then how many of each, and the
heads it cannot produce (`check_reports_errors_then_notes`); and it fails
exactly where it found an error, or, with `--complete`, a head it cannot
produce (`check_fails_on_an_error`). One directory's listing is read in a
pure step, each line as `Store.folder` writes it, a link's target line
passed over whatever it says (`check_reads_each_line_of_a_listing`); the
`text` payloads it reads as a file's lines are planned in another, and
each is one the store holds, under a digest some revision's `text` header
names (`check_reads_only_held_text`); and a bookmark `name` wrote reads
back as that bookmark, drawing a note, never an error, only where what it
points at is not here (`check_follows_the_bookmarks_name_writes`).

`arrange` gives a store's files the names decision 0006 made
deterministic, and touches no file's bytes. Every revision takes a stem
over the whole store — its month and day and its message's first line,
the change's first eight letters where another revision has that, and its
own digest's first twelve where another of the same change does too — and
is renamed where it sits (`arrange_keeps_a_revision_where_it_sits`), or
filed under its month with `--refile`. Every file of `operations/` is
filed under the stem of the revision whose claim on its digest wins — the
smallest revision, then the smallest path, a payload before a document —
at the path it had there, as `naming.bend` files a record's content. A
file already at its name stays, one whose name is taken is left, and one
no revision names is counted; the plan is worked out in the Rust tool's
walk order, a path at a time by component, and no rename it carries out
is onto a path the store's listing holds (`arrange_plans_no_overwrite`),
nor moves a file more often than the walk found it
(`arrange_moves_each_file_once`). Two revisions are not promised two
names: as in the Rust tool, a stem can meet another across its tiers, or
two digests share their first twelve letters, and the second file to want
a name finds it taken and is left. `-n` prints the plan;
without it each rename asks the host once more, through `Store.move`,
whether its new name is free — two files holding one document want one
name — and the directories it empties go through `Store.tidy`, up to the
store's own. Opening the store is the Rust tool's: a revision that does not
parse refuses it, naming the file, wherever among the store's files it
stands (`arrange_opens_what_parses`). Its words are read as they plainly
say: a line is accepted exactly where every word is one of its three
flags, and `-n` or `--dry-run` plans while `--refile` refiles, wherever
each stands (`arrange_reads_its_words`). The
`arranging` store is filed flat by digest, with one revision in a folder
of a person's own, content in a directory of its own, a duplicate of each
kind, a file no revision names, and three revisions sharing a summary —
two changes, and a reword — so every tier of a stem is reached; with
`arrange` added to the corpus stores, to `log`'s and to the stores `prune`
reads, `check.py` holds twenty `arrange`s to the Rust tool, every file of
the store compared after.

`prune` is decision 0013's disk half. A revision may go where a revision
the store keeps supersedes it, nothing kept names it as a parent, and it
is not itself the evidence that something kept was superseded; the Rust
tool asks that of each revision in digest order against what is kept at
that moment, pass after pass until one lets nothing go, and so does
`prune.bend` — so a run abandoned whole clears over as many passes as it
takes, and no revision work it keeps stands on is let go
(`prune_keeps_what_work_stands_on`). Every revision let go is one a
revision of the store says it supersedes
(`prune_lets_go_only_what_is_superseded`) — not always one it keeps, since
a superseded run clears in one pruning and the successor that let one go
may go after it. Content goes where no revision kept names its digest in
an `edit`, `text` or `bytes` header of its own, and a forgetting document
stays while what it stands in for is named
(`prune_removes_only_unneeded_content`). Files are found by what
they hold, so every copy of a pruned revision goes. Before any of it, a
store `check` would call broken is refused; the port asks the part of
`check` it reads — every document parses, no file's name claims a digest
its bytes do not have, every bookmark and rule file is one, and every head
has a tree. Each file goes through `Store.remove`, the digest-named
entries of `cache/` with them, and `Store.sweep` takes the directories
left empty. `-n` prints the plan the real run carries out: it removes
nothing, and names a line each, in order, the files the real run removes
(`prune_dry_run_names_what_prune_removes`); `--fields` prints decision
0074's `gone` lines. Of `cache/`, only files named by a digest are
cleared, so the note `init` writes there stays
(`prune_clears_only_derived_files`). The `pruning` store has an amendment and an abandoned run of three,
content only they named and content a kept revision shares, a second copy
of a pruned revision, an empty directory, a platform's file and a cache
entry; `lying` and `unparsed` are two stores `check` calls broken, and
`badname`, `badskip`, `bare`, `rewriting` and `stranded` add their own;
`check.py` holds nineteen `prune`s to the Rust tool.

`receive <dir>` unions another local store's history into this one, as
decision 0029 has it: by what documents hold. The source is the directory
named, or the store below it; each side is opened as the Rust tool opens a
store and held to the whole of `check` (`check.bend`), and two nonempty
stores that share no revision or edge are refused unless joined. A
revision arrives only from the source's revision documents, by its digest
and its text, where no revision document here has that digest
(`receive_takes_only_revisions_it_lacks`); a document or a payload only
from the source's, where this store has nothing under its digest and
neither store forgets it (`receive_takes_only_documents_it_lacks`,
`receive_takes_only_payloads_it_lacks`): each document is read and hashed
here and filed under the digest its bytes have, and each payload copied
through `Store.copy`, which hashes it on the way past. A bookmark this
store lacks arrives whole, one both hold at one target is made private
where either says so, and one they hold at two targets is a disagreement
that stops the receive, or makes a dry run exit 1 after saying so: each
bookmark written is one this store has none of by that name, or has at
that very target (`receive_moves_no_bookmark`); the dry run's exit goes through
`Store.exit`, since the Rust tool says nothing on standard error there.
Rules arrive under `Rule::label`'s names, a rule's digest where a file here
already has the name; the files of `claims/` by name, unread. An original
here that an arriving forgetting document stands in for is destroyed
(`receive_destroys_only_what_is_forgotten`) — every file removed for one
an operation document or payload file of this store holding that digest
(`receive_removes_only_the_originals`) — and so are the directories
that leaves empty. Nothing is planned from a store `check` calls broken,
on either side — a store holding a revision
document that does not parse, wherever it stands, is one
(`receive_trusts_what_it_plans_from`) — nor between two histories that
share no revision or edge unless the person asked to join them: between
two stores the check passes, a plan is made exactly where one is empty,
they share a revision, or a revision of either names one of the other's as
a parent or as what it supersedes, or `--join-unrelated` was given
(`receive_joins_only_related_histories`), and the `receiving` store's
stranger holds the refusal to the Rust tool. A
command line is read as its words plainly say, flags wherever they stand
and the one other word the source, and never as a plan and a statement at
once (`receive_reads_its_words`). The `receiving` store has four stores in
its folder: a
copy that went on, with its `main` moved and without; a stranger; and a
copy that forgot a line this store still holds. `check.py` holds twenty
`receive`s to the Rust tool, every file of every store in the folder
compared after.

`offer <dir>` writes decision 0048's manifest, as 0052 amends it, to
standard output: the listing a published copy cannot give, since a URL
cannot be walked. It is pointed at the copy `export` wrote, and refuses a
directory with no `history/historica.txt` in it, naming the store inside
as the likely mistake; the store is opened as the Rust tool opens one.
The heads come first — every head of the graph, superseded ones too —
then a line per file that travels, in the order a fetcher should take
them: payloads, documents with what each forgets, revisions, then the
rules, the other tool's files of `claims/` and the bookmarks (decision
0056), each group by path and each path under the copy's own name. A rule
or a bookmark that is private is left out, since its file's name is the
disclosure its key exists to prevent: the manifest is the one the store
would have with no private bookmark (`offer_names_no_private_bookmark`)
and with no private rule (`offer_names_no_private_rule`). `check.py`
holds nine `offer`s to the Rust tool, over the stores of the `receiving`
folder, one of them with a private rule and two private bookmarks, and
the refusals: no directory, two, a word it does not take, the store
rather than the copy, and a directory that is not there; a command line
it accepts is exactly one word that does not start `-`, and that word is
the directory (`offer_reads_its_words`).
Every line names a file by the digest the store's listing gives the file
at that path, group by group (`offer_names_each_file_by_its_digest`), so
a fetcher checking a file against its line checks it against what the
store holds; and what a document's line says it forgets is what `prune`,
`receive` and `export` read it as forgetting, save a resolution, which the
Rust tool's catalogue does not parse and lists as forgetting nothing
(`offer_lists_forgetting_as_prune_reads_it`). And `fetch`'s own reader
reads each line back as the file it names — its kind, digest, what it
forgets and its path, whatever spaces the path holds
(`offer_lines_read_back`) — so what a fetcher checks a file against is the
digest the listing gave it.

`export <dir> [<target>]` writes decision 0042's copy: a fresh repository
at `<dir>`, assembled rather than mirrored. The target — `head` where none
is named — is resolved as every command resolves one, and a store `check`
would call broken is refused, since a copy of a fault is two faults. What
travels is the target's ancestry, closed over parent edges and nothing
else, every document and payload those revisions name, followed through a
resolution's `keep` lines, and every forgetting document standing in for
any of it — each a file this store holds
(`export_carries_only_this_stores_files`); the shared rules, filed under
`Rule::label`'s names
(`export_states_no_private_rule`); the shared bookmarks whose target the
copy holds (`export_names_only_what_travels`), the rest counted as held
back or as pointing past the target; and the files of `claims/`, whole.
The copy's files are named as `arrange` names them, over what travels. The
folder is laid out path by path, each path the tree places given one
outcome at that path (`export_lays_out_every_path`): a file of lines
holding exactly what `cat` prints there, a file of bytes the payload its
entry names, copied out of the file of the store holding it, a link made
where it sits and spelled as decision 0040 spells it, each runnable exactly
where the tree says (`export_lays_each_file_as_the_tree_has_it`) — and
every path outside the store, no other file's directory, and none a rule
of the copy covers, so the copy's own walk offers back all it was given
(`export_lays_out_only_what_the_walk_offers_back`); or, where the folder
cannot take the tree whole, every path in the way named. `-n` prints the
counts, a `would withdraw` line for each file a copy being updated gives
up, in the order they go, and a `write` line for every path the tree
places, once each and in path order, no other line reading as either
(`export_dry_run_names_what_it_would_write`). `--files-only` lays the
same folder out into a directory holding nothing, with no store beside it,
says each link and mode it set, and reads each file it wrote back, refusing
a folder that folds two of the tree's paths onto one file exactly where some
file reads back as other bytes than it laid
(`export_calls_a_folder_folded_exactly_where_it_reads_back_otherwise`); its `-n` names,
file for file and link for link, what the real run then says it wrote and
linked (`export_files_only_dry_run_names_what_it_lays_out`). What a
directory holds is read from the host's listing of it, which reads back as
the entries' own names, once each and in order, a link's target never
taken for an entry (`export_reads_a_directory_listing_back`), so a folder
alone, and a fresh copy, is laid out exactly where that listing names
nothing (`export_writes_only_into_nothing`). A directory
holding anything that is not a copy is refused, one that cannot be listed
in the Rust tool's words for why, on both builds: a fresh copy goes only
where nothing is held, and an update only into a store
(`export_writes_only_where_a_copy_may_go`). A command line is accepted
exactly where the words starting `-` are all its flags and one or two
words do not, which are the directory and the target in the order typed,
each flag counting wherever it stands (`export_reads_its_words`).

A directory holding a copy this store made is brought up to date rather
than refused (decision 0052), once it passes `check` — asked before the
copy is opened, as the Rust tool asks it — and exactly where it is related
and holds no revision this store neither holds nor names as a parent or as
superseded (`export_updates_only_a_copy_it_could_have_made`). The set is
the same; the copy is diffed against it by content: each
revision the set names is held under the stem it has, each document or
payload either side forgets destroyed, each file the set no longer names
withdrawn — revisions, then documents, then payloads — and each rule file
and bookmark the origin no longer shares retired, and nothing else is given
up (`export_update_gives_up_only_what_the_set_no_longer_names`). What the update writes
is one value, `onto.writes`, which it files and counts: after it the copy
holds every revision, document, forgetting document and payload of the
set, or a forgetting document of one side says it is gone
(`export_update_leaves_the_copy_the_whole_set`); the files of `claims/` it
carries are exactly those the copy has none of by name
(`export_update_carries_only_the_claims_a_copy_lacks`); and the rule files
it adds state shared rules only (`export_update_states_no_private_rule`).
Newcomers are named
around what the copy holds, as `stems_around` names them. The folder is
caught up as `update::plan_at` catches one up: a path already holding what
the target records is kept, one holding bytes some revision of the copy
records is written over, and one holding work nothing recorded refuses the
whole export — unless the folder is exactly what the copy's one head
records and the export is about to take something away, when it is the
export's own output and rewritten whole, and a folder is taken for that
only where it holds, path by path, what a fresh export of that head lays
out (`export_settles_only_on_what_it_laid_out`). Once the plan's steps are
taken, every path holds what a fresh export of the target lays there, and
nothing removed is one of them (`export_catches_up_to_a_fresh_copy`): no
write lands on work no revision's record of that path holds
(`export_writes_over_no_unrecorded_work`), and every file written over or
removed holds bytes `cat` of some revision of the copy reads, or a payload
its tree names (`export_spares_the_unrecorded`); nothing is destroyed that no
forgetting document of either side names in its header
(`export_destroys_only_what_is_forgotten`), no revision the copy holds is
renamed (`export_renames_nothing_a_copy_holds`), and nothing is removed
that no such record holds (`export_removes_only_recorded_files`). The
`updating` store has copies at
the first revision and at the head, one with a file edited, one with a
stray file, one disturbed at the head, one recorded in, one broken, and a
stranger's store, made before the store forgot a line, deleted a bookmark,
made one private and traded a rule for another; nineteen `export`s bring
each up to date, at the head and back at the first revision, or refuse it,
and refuse a destination that is a file or under one.

The `exporting` store has lines, bytes, a runnable
file, links by reference and verbatim, three revisions, a forgetting
document for a file only the second holds, bookmarks shared, private,
pinned and naming a file, rules shared, private and none, and a file of
`claims/`. With a copy of the `walked` store's resolved merge, which carries
every document the resolution keeps items of, and its folder laid out from
the merge walk; the `folder` store's links, mode and rules; the `pruning`
store's head, whose ancestry leaves a `supersedes` edge dangling; and the
`merge` store refused as broken, and the nineteen of the `updating` store,
`check.py` holds forty-one `export`s to the Rust tool, every file written
compared after.

`fetch <url> [--join-unrelated] [--fields]` is decision 0048's other half:
it reads the manifest `offer` wrote and takes what this store lacks. The
URL is cut at its last `/` — every path in a manifest resolves against the
directory the manifest sits in (decision 0052) — and one with no scheme,
no manifest named, a directory named, or a query or a fragment is refused
before anything is opened; what it keeps is the URL up to its last `/`,
that included, and a manifest's name with no `/` in it
(`fetch_asks_under_the_manifests_directory`). A command line is read as
its words plainly say, the flags wherever they stand and the one other
word the URL (`fetch_reads_its_words`). The store is opened and held to
the whole of `check`, before anything is asked for and again once
everything has arrived; the manifest is read as `Offer::parse` reads it,
an unknown kind a discarded line and an unknown header a refused manifest,
and what `offer` prints is read back as the heads and files it was printed
from, each file's kind, digest, what it forgets and path, spaces and all
(`fetch_reads_the_manifest_offer_writes`). The plan is worked out before a
byte is asked for: the payloads and documents this store has nothing under
the digest of and neither side forgets, the revisions it lacks, the rules
whose bytes no file of `skipped/` holds, another tool's files of `claims/`
it does not have, and the bookmarks it does not hold — one it holds is
kept, and said so (decision 0062) — each digest once; a store with
revisions, fetching from a copy with revisions, must share one or name one
as a parent, or be asked to join: the fetch is refused exactly there, said
of the manifest's `revision` lines and of this store's revisions and the
revisions they name, not through the plan's own reading of either
(`fetch_refuses_only_what_shares_no_revision`,
`fetch_refuses_what_shares_no_revision`). An original is destroyed only
where a forgetting document of this store, or a line of the manifest, says
it is forgotten (`fetch_destroys_only_what_is_forgotten`), and nothing is
asked for that this store holds or either side forgets
(`fetch_asks_for_no_payload_held_or_forgotten`,
`fetch_asks_for_no_document_held_or_forgotten`,
`fetch_asks_for_no_revision_it_holds`). The files are asked for in
`receive`'s order, content first, then compliance with forgetting, then
revisions, then the rest, and each is hashed against the digest its line
gave before it is filed under that digest, here: nothing whose bytes are
not its digest is written
(`fetch_files_only_text_that_hashes_to_its_line`,
`fetch_lands_a_file_only_where_it_hashes_to_its_line`,
`fetch_files_a_payload_under_what_it_hashes_to`); a bookmark written in a
pass is held for the rest of it, so a second line naming it writes nothing
(`fetch_writes_a_bookmark_once_a_pass`); and nothing is asked for that the
manifest does not name (`fetch_asks_only_for_what_the_manifest_names`). A
path is asked for by its bytes as the Rust tool spells them — every byte
that is not unreserved written `%` and two uppercase hex digits, `/` kept
— so what is asked for decodes to exactly the path's bytes and holds
nothing a URL's path may not (`fetch_asks_for_a_path_by_its_bytes`,
`fetch_asks_in_characters_a_url_may_hold`,
`fetch_asks_for_what_is_unreserved_as_itself`). A path the server says is
gone (404, 410) is the publisher having moved on, and the manifest is read
again, three times at most. The host's part is two effects that decide
nothing (`RUNTIME.md`): the text at a URL, and a file at a URL written
into the store under a name Bend chose, answered by its digest. `check.py`
serves `export`ed copies with their `offer.txt` over HTTP from a thread of
its own and holds thirty-six `fetch`es to the Rust tool, the whole store
compared after: into an empty store and into one holding the first
revision, a copy with nothing new, a stranger refused and joined, a copy
that forgot a line and a payload, a manifest naming a digest a payload's
bytes do not have, a revision gone every time, a copy being rewritten
while it is read, a reserved directory declined and a kind discarded,
manifests misspelled, malformed and not text, none at all, and every usage
error, with `--fields` beside each kind of ending; what `--fields` says
names each revision taken once, in digest order, and none that was not
(`fetch_says_what_it_took`).

`update [<target>] [--dry-run]` makes the folder hold a head, decision
0030: the one head there is, or the one named, and a revision that is not
a current head is refused with the heads listed. Each path the head's tree
holds is written as the target records it — a file of lines as the text
`cat` prints, a file of bytes as the payload the store holds, copied, a
link spelled relative to where it sits — and a file whose bytes are right
and whose bit is not has its mode set; each path the folder holds that the
head does not is removed where some revision, superseded or abandoned
included, records its bytes, and a directory it empties goes with it.
Nothing any revision does not record is written over or removed: such a
file where the head wants one refuses the whole update, and at a path the
head does not hold it is left, said to be where a current head tracks it
and silent where nothing does. So is everything the folder cannot take — a
path two files claim, bytes a merge left contested, a file and a
directory at one path, the store's own directory, a rule in `skipped/`, a
payload the store does not hold, a directory, a link or something the walk
did not offer where a file goes — all collected, sorted and said at once
before anything is written. The plan (`update.bend`) is pure, and so is
what carrying it out does — `effects`, each removal, each file written,
each link made and each mode set, the list the dry run is read against —
and the IO performs that list with four writes that decide nothing: `Store.put` lands a
file of lines staged and renamed over what stood there, keeping its
permissions as the Rust tool's `write_if` does; `Store.lay` copies a
payload in as a new file, refused where its bytes are not the digest;
`Store.link` makes a link beside the path and renames it over; and
`Store.chmod` asks the bit of the path and, where it differs, sets it as
the read bits say, answering what it was, which is how a `mode` line is
owed. A written file that does not read back
as what was written is the folder folding two paths onto one, and is
refused after the fact, as the Rust tool refuses it. What the port does not
do is look again at each path just before touching it: the Rust tool's
`apply` narrows the window between the plan and the write, and a folder
changing under an update is not something `check.py` can make happen.
`check.py`'s `updating` store has two heads beside a base, and a folder
standing at the base with a stray and a file nobody recorded; `caught` is
the same folder once it holds the tip; and `blocked` has a head no folder
can take, and a folder in its way at every turn. With `update` over the
corpus stores, which arrive with no folder at all, over the walked and
resolved merges, and where there is no store or nothing recorded, 33
comparisons hold it to the Rust tool, the folder after included.

`merge [<target>...]` lays two lines of work out in the folder together,
decision 0012 (`merging.bend`): what is named, and every current head
that is not, so `merge` alone joins the heads there are, and a store with
one refuses in the Rust tool's words. Nothing is recorded. Each file of
lines the merged tree holds is written as the walk reads it
(`conflict.bend`): the runs concurrent authors met in — siblings two
authors placed unaware of each other, a removal beside concurrent work —
fenced, a line naming the revision that wrote each run and one closing
the fence, and the rest as it stands. A file of bytes is the payload the
tree kept, or, contested, left as it is with the `historica cat` line for
each side; a link points where the tree says, and a mode is set where
the bit differs. A path two files claim gets each file beside it, under a
name that says whose it is. What the folder holds at a path is written
over only where it is nothing, what this merge would write, the walk's
reading unfenced, or what one of the heads leaves; anything else is work
nobody recorded, and is left alone and said to be. It closes with how
many files hold work that met and the `record` line that records the
merge, each head named as the person typed it — built as the words a
person types, which `record`'s own parser reads back as this merge. A file of lines is
written as the Rust tool's `fs::write` writes one, in place and through a
link standing at its path (`Store.through`); a payload, a link and a bit
are `update`'s writes. What makes writing into the folder safe where nothing met is
`merge_renders_the_uncontested_as_itself`: such a file renders as the
walk's file, byte for byte. `check.py`'s `meeting` store is two lines of
work that met every way a file of lines can — one line rewritten both
ways, a deletion beside an insertion, a last line two sides end
differently, edits apart, a file one side alone touched, a mode one side
set — beside a file neither side recorded; `marked` and `marked1` are the
same once a person has started resolving it; and `through` is a folder
whose files of lines are links — to a head's version, to nothing yet, to
a plain copy of a file the tree runs, to work nobody recorded — and whose
payload is a link to its bytes. With `merge` over the corpus, walked,
resolved and hand-written merges too, 17 `merge` comparisons hold it to
the Rust tool, the folder after included, and 9 more hold `status`'s
`marked` and `record`'s refusal of it.

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
line for line what it prints without colour. `opdiff` is what `diff` was here before: the operation
document between two files, by `Ops.diff`.

A path is spelled one way, as decision 0033 has it: in Unicode normal form
C, which `nfc.bend` computes as the `unicode-normalization` crate the Rust
tool uses does, from the crate's own tables (`nfc_tables.bend`, which
`nfc.py` writes from what `ffi/examples/nfc_tables.rs` asks the crate of
every scalar value — Unicode 17.0.0, where Python's `unicodedata` here is
14). `check.py`'s `nfc` stage holds it to the crate on nineteen thousand
strings, on both normal forms C and D: every character that decomposes,
alone and before marks, and strings drawn from what the tables are about.
A path is normalised wherever the Rust tool normalises one: each name the
walk reads, a rule in `skipped/`, every path a person types — `record`'s
paths, `--at`, `--move` at both ends, `--bytes`, `--lines`, amend's
`--move`, and the path `cat`, `show`, `diff`, `blame`, `name` and
`log --path` read, `path:` or not — and a link's target once it is
resolved against the tree. The folder keeps its own spelling, which is
what has to be opened: a directory is listed by the name it was listed
under, each line of its listing read as the entry the host wrote it for
(`a_directory_is_read_as_the_host_lists_it`), and a file is opened by the
name its listing spells the path with,
which `Folder.on_disk` asks the listing for only where the path could be
spelled another way — a path of ASCII without `;`, `K` or `` ` ``, which
three characters decompose to, cannot. `update` writes the same way: a
file the walk found is rewritten, removed, relinked and given its bit
where the folder spells it, rather than laid again beside it, and any
other path is joined on as the tree spells it, as are the directories it
tidies above a removal — so one spelled decomposed that a removal empties
stays, as the Rust tool leaves it. `merge`, like the Rust tool's, reads
no walk and asks the folder at the tree's spelling. Two names a
filesystem tells apart that are one path are one file, the one the walk
met last, and the walk yields its files in path order
(`the_walk_keeps_the_file_it_met_last`,
`the_walk_yields_its_files_in_path_order`). And
`check_path`'s last rule is here: a revision stating a path not in normal
form C, and a bookmark named so, are refused, and `name` says why in the
Rust tool's words.

The Rust tool refuses such a revision only where something reads the
whole of it — opening a store reads a revision's causal headers alone,
the first `change`, `author` and `when`, every `parent` and `supersedes`,
and the message after the blank line, as written
(`opening_reads_what_a_revision_states`) — and the port does the same: `fulls` keeps the causal headers of a
revision refused only for that, with the refusal, naming the file and the
line, in place of its facts, and a tree made from it refuses with what the
revisions did, `log` of what it lists and `show` of what it prints as they
are, while what reads only what came before it goes on. A name the host
cannot spell as UTF-8 is refused as `WorkingError::NotUtf8` refuses it,
whatever the rules say, naming where it is on disk; the host lists it as
`to_string_lossy` spells it, and the walk files the refusal where it met
the name, between the entries around it. Four stores hold all of it to
the Rust tool: `normal`, a folder whose names the filesystem hands back
decomposed, recorded, edited, renamed and added to, with every command
given decomposed paths, 32 commands; `renormal`, such a folder in step
with one head and a second line of work beside it, updated to each and
merged, 11; `unnormal`, a revision restated by
hand with a decomposed path, every reader of it and every one that goes
on, 27; and `unspelled`, names that are not UTF-8 beside the store, in a
directory, as one, and under one spelled decomposed, 9.

The laws say what that rests on. A path of ASCII is its own normal form
(`nfc_leaves_ascii`), so normalising at every boundary changes nearly
nothing. Canonical ordering is Unicode's canonical order, stated over
classes alone — no mark after one of a higher class with no starter
between (`nfc_orders_marks_by_class`) — and moves no mark past another of
its class, losing and adding none: the marks of every class are the ones
it was given, in order (`nfc_ordering_keeps_every_mark`). The class
lookup, which stops at the first run of the table past a character, finds
what a search of every run finds, since the crate's table is in order
(`nfc_class_misses_nothing`). In the crate's tables `/` and `.` have no
class and are in no pair and no decomposition
(`nfc_leaves_separators_alone`), the tables' part of why normalising a
path a name at a time normalises the whole of it. Of the walk: it yields
no two files in a row at one path, in path order, and loses no path it
found (`the_walk_yields_a_path_once`); a read opens a name whose normal
form is the path, or the path itself (`the_folder_spells_what_is_opened`);
and the host's lines for any directory, read back, refuse each name that
is not UTF-8 once, where it is on disk, in the Rust tool's words, and
nothing else (`a_name_that_cannot_be_spelled_is_refused`). No law says
that normalising twice is normalising once; that is the crate's promise,
and the `nfc` stage holds the port to the crate.

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
that stated that document. A walk that refuses says why in `merge.rs`'s
words — the event whose document names a position past what its author
saw, removes an item other than the one there, or keeps a name its view
does not hold as often as it keeps it — found by walking again on the
refusing path alone (`walk_fault.bend`), since `Merge.walk`, which the
laws are about, answers only that it refused; and a document that does
not parse is named by where it was read from. `check.py`'s `walked` store has four
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
each asked what it `forgets`: a stand-in the port writes, in any of the
three grammars, is kept exactly for the digest its first header forgets
(`a_stand_in_stands_for_what_it_forgets`). Several may stand in for one
digest — each
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
forgotten, or stood in for, the file is replayed instead. `check.py`'s `forgotten` store has
the Rust tool's `forget` destroy a line of a file added whole as `text`,
two lines of an edit, a line a merge's resolution copied, a payload of
bytes, and a second span of the first document, so that two stand-ins name
one digest; forty-five commands read it — `log`, `files`, `cat`, `show`,
`diff`, `blame` and `status` at the revisions it touched, and `record`,
`amend` and `carry` over it, with the store compared after — and ten
`forget`s run over what is already forgotten. The moves read it too:
`prune`, `receive` from itself, `offer`, and three `export`s, each copy
compared whole. The `check` those ask first, and the stores' own readers,
read `operations/` in three grammars, as the Rust tool's `Store::body`
does — a payload's stand-in, told by its `length` header, before a
resolution and an operation document — so a store that forgot a payload
is not called broken; and an export carries every forgetting document with what it
stands in for and lays each file out as `cat` reads it. `offer` lists
what the Rust tool's catalogue of `operations/` says each document
forgets, and that catalogue parses no resolution: a forgetting resolution
is listed as forgetting nothing (`-`), there as here.

A stand-in can also sit beside the original it forgets: one a sync that
copies files brought, or one that arrived while a replica kept its bytes.
The Rust store reads the original through it, and so does the port. The
Rust catalogue records what each document forgets, and `Store.at`, asked
in its `forgets` form, answers from that catalogue — its `forgets` column
where it accounts for a path, a document's first header where it does not
— and the port reads each document it names and asks it again. An
operation document is read with every item any stand-in of its shape
forgets forgotten, and a `text` payload as the document inserting every
line at 0, read the same way; what is read is the original with items
forgotten and nothing else (`standins_beside_only_forget`), everything a
stand-in of its shape forgets is forgotten in it
(`standins_beside_forget_all_they_say`), and the order stand-ins arrive in
changes nothing (`standins_fold_in_any_order`). `show` prints the held
document, a held payload of bytes is its bytes, and `forget` counts a
version with a stand-in as forgotten whether or not its bytes are still
here. A held resolution is read as held: the Rust catalogue records
nothing a resolution forgets, so the Rust store finds a resolution's
stand-in only once something has made it read every document — which
assembling a resolution that keeps from a payload does. Within one Rust
command, then, the first reading of such a resolution ignores the
stand-in beside it and a later one applies it, and `diff head` over a
store like that says the revision after the merge turned a line into
`\ forgotten` in a file it did not touch. The port reads it as the first
reading does, everywhere. `check.py`'s `resurrected` store copies the
stand-ins the Rust tool's `forget` wrote in a copy of the history in
beside the originals, and holds forty-two commands to the Rust tool —
every reader, `record`, `amend` and `carry`, and `forget` over what
already stands beside — leaving out `diff head`, whose answer is that
inconsistency.

`forget <target> <path> --lines <first>..<last>` destroys a span's text
everywhere history quotes it (`forget.bend`). The lines are those the
target reads, each traced through the walk to the document that wrote it —
an edit's inserts, a `text` payload, or a resolution's own `insert` — and
from there to every delete that quotes it and every resolution that copied
it (decision 0050), each one a revision's headers state for that file,
and each stand-in opening by naming one of them as what it forgets
(`forget_rewrites_only_the_files_documents`). Each gets a stand-in: the
document with exactly those items' text replaced by the marker and nothing
else (`forgetting_destroys_the_picked_text`, `forgetting_destroys_only_text`),
its shape kept, so that the union rule
folds it in (`forgetting_keeps_shape`), and folded with whatever already
stands in for it. The stand-ins are filed first, through `Store.once`, and
only then is each original — found by its bytes among `operations/`, as
everything in a store is (`forget_destroys_only_what_it_forgets`) —
removed through `Store.remove`, so an interruption leaves a document and
one naming it, never bytes gone with nothing said. A file of bytes has no
lines: it is forgotten whole, the payload the target holds for it and no
other (`forget_whole_takes_one_payload`), its stand-in filed where it was
with `.ops.txt` after its name where that is free
(`forget_files_a_payloads_standin_where_it_was`) and at its own digest's
name where it is not
(`forget_files_a_payloads_standin_by_its_digest_where_that_is_taken`), and the other versions
of the file counted and left alone (decision 0066,
`forget_counts_only_other_versions`). Every entry of `cache/` named by a
digest goes with it, since an entry is some file's content and may be a
copy of what went (`forget_clears_every_copy`), and nothing else: what it
removes the host listed there, under a digest's name
(`forget_clears_only_copies`), so the note and the catalogues stay
(`forget_keeps_the_note_and_catalogues`). Last, every directory under `operations/`
holding nothing is removed, `operations/` itself kept, whether this
forgetting emptied it or it was empty before, as the Rust store sweeps
them: the port lists `operations/` a directory at a time through
`Store.folder` and asks `Store.remove` for each empty one, which takes the
directories above it that it leaves empty too. `--dry-run` says what would be written and
destroyed and does neither; `--fields` states each digest `gone` under
`historica-wrote-1`, the header left behind by a refusal as `name`'s is.
`check.py`'s `forgetting` store is the same history with nothing forgotten
yet, read by the Rust tool first so that `cache/` holds a state of
`notes.md` and a catalogue of `operations/`; its forty-two `forget`s — a
span of an edit, of a `text` payload, of a line a resolution copied and of
one it inserted, a payload with other versions beside it, `file:` and a
signed span, and every refusal and usage error — are each run on a copy of
the store of their own, per tool, and the whole store after compared,
`cache/` and all, and with two directories under `operations/` that were
empty before it.

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
Base defines the comparison and states nothing about it.
`map_lemmas.bend` does the same for Base's `Map`, a crit-bit trie, and
`Set`, a `Map` of `Unit`: read through plain definitions — the leaf a
key's bits lead to and what the key finds there — `Map.get` after
`Map.set` finds what was written, and any other key what it found before,
in every map `Map.new` and `Map.set` build, whose invariant is a `Bool`
two lemmas carry; under it, that two keys agree at every bit before
`Map.diff` of them and differ at it, proven down a `Word`. With them the
digest map `status` builds from the host's answers gives each path the
host's answer for it (`status_surveys_each_path`), and the arrival laws
read the arriving paths as a list rather than through the set the code
builds of them. The same
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
wrote or one already kept. `contested` is not part of the model, as in
the Verus file; `conflict.bend` reads it off the finished tree. The reading carries fuel — one more than the element count,
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
range check. `replay_reads_alike_through_standins` carries it along a
file's stored history as `replay` reads it, any operation document replaced
by one that parses as a stand-in for it and every payload kept. What
`forget` writes is such a stand-in (`forgetting_destroys_only_text`), with
the text gone from exactly the items picked, each marked forgotten with its
terminator kept, and every other item as it was
(`forgetting_destroys_the_picked_text`), and of the shape the union rule folds
in, for an operation document and for a resolution
(`forgetting_keeps_shape`, `forgetting_a_resolution_keeps_shape`);
`show_prints_what_the_revision_states` is restated so that what `show`
prints of a forgotten document is documents the store holds, whole and in
its order, each saying it `forgets` the digest named. Of the command: every
document `--lines` writes a stand-in for is one a revision states for that
file, read straight off its headers — an `edit`, `text` or `bytes` header
naming the file and the digest — and every stand-in it writes opens with the
format line and a `forgets` header naming one of those digests, the one it
is filed as forgetting (`forget_rewrites_only_the_files_documents`); a file of bytes loses the
one payload its tree holds at the target, or nothing
(`forget_whole_takes_one_payload`), and the versions it counts beside it
never include that one (`forget_counts_only_other_versions`); a file is
destroyed only where its bytes are a digest forgotten
(`forget_destroys_only_what_it_forgets`), and in `cache/` every entry
named by a digest (`forget_clears_every_copy`) and only an entry the host
listed there under a digest's name (`forget_clears_only_copies`), so never
the note `init` writes or a catalogue
(`forget_keeps_the_note_and_catalogues`); and its arguments are
read as their plain reading says, with no classifier of its own: each
`--lines` and its word set aside, the target and the path the words left
that do not open with `-`, a dry run and `--fields` exactly where they are
among those words, and the span read from the word after the last
`--lines` (`forget_reads_its_words`). That every document quoting a
forgotten line is among those rewritten is not stated: saying which
documents quote an element needs the walk, and a law that decides it with
the code's own walk says nothing the code does not. What it prints reads back
as what it does: under `--fields` a `gone` line for each digest the plan
made unreadable and nothing else (`forget_states_what_it_made_unreadable`),
and otherwise `destroyed` lines, `would destroy` under `--dry-run`, for
exactly the files it destroys (`forget_says_what_it_destroys`). Every
document it writes is filed as one, at the name its bytes give it or at
one no file of `operations/` has (`forget_files_documents_where_nothing_is`),
and a payload's stand-in, where no document holds the bytes it forgets,
beside a payload that held them at a name no file has, wherever every
such name is free (`forget_files_a_payloads_standin_where_it_was`), and at
its own digest's name wherever every such name is taken
(`forget_files_a_payloads_standin_by_its_digest_where_that_is_taken`);
a file of lines given no span is refused, never forgotten whole
(`forget_takes_no_file_of_lines_whole`); and each step of the sweep after it
adds to what it removes exactly the directory it listed, where the listing
was read and said nothing, never `operations/` itself
(`forget_sweeps_only_what_lists_empty`), and goes on only into
directories that listing names on a `d ` line
(`forget_sweeps_only_listed_directories`), a link's line and its target
line naming none (`forget_sweeps_past_a_links_target`). Where stand-ins sit beside a held original,
three laws say what is read, over the union the reader folds them with:
it is the original with each item as it was or forgotten
(`standins_beside_only_forget`), so a stand-in from another replica
redacts and never rewrites; every item a stand-in of the held shape
forgets is forgotten in it, whatever is folded in after
(`standins_beside_forget_all_they_say`, stated over `covers`, which asks
only that a forgotten item stay forgotten); and two stand-ins swapped fold
to the same document (`standins_fold_in_any_order`), so any order does,
and a stale replica's narrower redaction, arriving last, brings nothing
back.

Trying to prove the round trip found two ways the port accepted what it
could not write back: a `\ no newline` or `\ forgotten` line, and a header line, with no
newline after it. Both are refused now, as the Rust parser already did, and
`invalid/unterminated-marker.ops.txt` pins the first in both corpora.

The tests compare both specifications for the ordered examples, and
compare the cursor specification with the implementation for raw reversed
positions, repeated inserts, overlapping deletes and competing errors.
Four hundred and seventy mutations cover the primitive helpers, lost inserts, a lost trailing
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
document taking a payload's digest, and a merged file's event walked before
what it had seen; and two cat-and-show breaks: a document found whose digest the
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
rather than the revision it names; and nine name breaks: a name taken without
asking the path rules, the other words kept newest first, `--private` read
as `--shared`, `--change` misspelled, the header sent early without
`--fields`, a bookmark moved that forgets it was private, a bookmark set at
the head whatever its target, `--revision` pinning the change, and `--fields`' header said twice; and seventeen
listing breaks: `files` in reverse path order or with the path last, a
bookmark's name read keeping the slash after `names/` or the dot of `.txt`,
no bookmark found under `names/`, only the first file there read, a pin
the store lacks said as its digest, a pin cut to eight characters whether
or not they are unique, a change's revision abbreviated against no other,
nothing said where there are no bookmarks, one space after the widest name,
bookmarks read in reverse, `log --fields` with the change first, the whole
store listed rather than the span shown, one revision more than `--limit`
asks, facts of every kind counted, and an added file's bytes counted as
stored; and seventeen
status-report breaks: a fact named by its path first, the accepts left out,
contests said where no work is joined, a contest line that leaves out the
file it contests, a claimed path said among the contests, the parents
after the first merged alone, a file of bytes read, a file replayed
whatever its kind, a disputed file compared with a digest, a disputed file
read as one the parents agree on, a disputed file emptied in the folder
said as nothing or as edited, a file the parents dispute forgotten as
disputed, a stated file replayed, a join that takes the first
parent's digest where the parents differ, a file read at the first parent
only, and a file no parent mentions joined as disputed; and seventeen survey breaks: a link to a file the
record drops let dangle, the folder's link looked for at a dangling link's
file rather than its path, a link written as a reference where the
revision states nothing or to a file the record drops, a link's `..`
pushed rather than climbed, a run of one path counted once too few, a file
of lines refused at a path other than its own, a link's own path checked
rather than its target, a kind stated for a file already there or for a
path not looked at, a `move` line for a file moved again later, a line for
each time a file moved, a move that moves every file but the one named, a
restricted record refusing what the walk refused elsewhere, a rename
offered for bytes more than one path left, a path nothing answers to let
through, and a path only the renames put there refused; one reason break: a reason of only
whitespace taken; and seven naming breaks: a summary keeping a separator, a
fallback longer than the limit, a filed path keeping its control
characters, the clock compared with the earliest work, a warning given where
the clock is ahead of the store, an offset read west for east, and its
minutes read from its hours; and one colour break: a marked line drawn without its sign; and three
folder-plan breaks: a settled file of lines replayed, a folder file the
position holds as bytes read, and a file's statement looked up by its path;
and two chain breaks: a chain that stays at
the revision it began at, and one that stops after it; and one revision-reading break: a document
outside `revisions/` read as a revision; and three size breaks: a size
believed whatever digest the host's line names, a file of bytes shown with
no size, and a payload the host could not find asked the stat of; and six fetch breaks: what a resolution
keeps left unfetched, a resolution's `keep` left out of what it keeps, an
`edit` the folder's plan believes left unfetched, what a `text` names
fetched in place of an `edit`'s document, a payload shown left unasked, and
one asked about twice; and seven span breaks: `a..b` read as `b..a` or taking away only
`a` itself, a target listed alone, a walk from a target that takes
nothing in, one that follows a revision's change rather than its parents,
and one given twice the store's length in steps or a step for each
revision rather than each parent; and forty writing breaks: `record` keeping the first `--onto`,
merging the last `--merge` first, cutting a rename's new path at a second
`=` and keeping the slash a shell leaves after a directory, a rewrite
keeping the first `-m` and taking a second target in place of the first, a
carried revision reporting the identifier of the one it supersedes, a
merge let onto an abandoned run, a reword that drops what the revision stated, an edited file
diffed against nothing, the bookmarks on every change but a parent's moved,
only the first bookmark on a parent's change moved, a parent's identifier
read as its change, the bookmarks on the first parent's change alone moved,
a name no held revision has extended, an acceptance nothing contests let
through, only the first attachment accepted checked, a path the survey
refused written, a contested file of lines left empty written, `carry`
taking a change for the revision named, a rename moving the path named rather than the file at it,
every `--at` taken for nothing, a restriction taking one end of a rename, a merge of two restricted, a
skipped name nothing answers to let through, a dry run giving an arriving
file a `link` line, `carry --fields` naming a revision twice, `amend
--fields` leaving out what it carried, a file with no NUL taken for text, only the first file `--lines` names read, the kind
of the last path named checked alone, the position read as empty, an
amendment changing the identifier of a file it added, `amend` without a
target taking a superseded head, `amend` rewriting the head whatever
target is named, `abandon` going on with no target named, a flag taken for
`abandon`'s target, a dry run let ask for `--fields`, a reason of spaces,
and an `abandon` dry run naming the run in reverse or each revision by its
whole digest; and one stand-in
break: a document taken as standing in whatever its header forgets; and
eight forgetting breaks: a stand-in that resets a forgotten item's
terminator, one that writes an empty line where the marker goes, a line's
stand-in written for the revision that wrote it rather than the document it
names, a payload's length written where its digest goes, a file destroyed
without asking whether its bytes are forgotten, the span after `--lines`
taken as a word too, every file of `cache/` but its note cleared, and the
version forgotten counted among the others; and six arrange breaks: a rename planned onto a
name that is taken, a revision refiled without `--refile`, a dry run's
count leaving out the files it would leave, a store opened past a
revision that does not parse, a taken set that forgets the listing, and
renames carried out backwards; and eight prune breaks: a revision let go
that work still stands on, every revision read as superseded, content
removed that a kept revision names, a payload a revision names by `bytes`
read as unneeded, a forgetting document standing in for named content
removed, a dry run that removes what it lists, every file of `cache/`
cleared, and a plan and a statement taken at once; and eight receive breaks: a
document taken that this store already holds, a payload copied that it
already holds, a revision taken that it already holds, its own revisions
filed as the source's, a source refused whose revisions this store builds
on, a bookmark moved to where
the source has it, an original destroyed that nothing forgets, and every
payload file this store holds removed with it; and four offer
breaks: a private bookmark named, a private rule named, a payload's
stand-in read as an operation document, and nothing written where a line
forgets nothing; and four
export breaks: a link laid somewhere other than where it sits, a
private bookmark given to the copy, a bookmark pointing past the target
given to it, and a private rule written into it; and two breaks of an
export onto its copy: a file nothing recorded written over, and a stray
file removed; and eight more export breaks: a word it does not know taken, a directory holding no
store updated, a file of lines laid out plain whatever its mode, a payload
copied from a file named for it rather than the one holding it, a payload
carried from a file the store does not hold, a revision the copy holds
renamed, a path a rule of the copy covers laid out, and every original the
copy holds destroyed; and fourteen breaks of what an export proves of a copy
and of what it says: a link's target counted as bytes the copy records, a
copy's file kept whose mode is not the target's, a folder with a file to
write taken for the export's own untouched output, a copy refused that
holds a revision the origin pruned but names, private rules planned to
travel, only the revisions a copy already holds written into it, a
revision file withdrawn that the target's history holds, a file of
`claims/` carried over the copy's own, a dry run naming a path twice where
two files claim it and a withdrawn file outside `history/`, a link's
target read as an entry of a directory, a file's mode and size read as its
name, `--files-only -n` planning to write a link as a file, and the size
the host states for a file read as its digest; and two receive breaks: a store the check calls
broken planned from, and a plan and a statement taken at once; and one
offer break: a directory that starts like a flag taken; and one offer
digest break: a file named by its path rather than its digest; and the
breaks the laws that say what is written, destroyed and trusted in plain
facts catch where the laws they replaced, which asked through the code's
own helpers, did not: the check that every revision parses reading the
first alone, a document's own digest read as what it forgets by `receive`
and by `export`, and the first record of a copy read whatever path it is
of; and seven more word breaks: a word `arrange` does not know taken,
`--refile` read as a dry run too, `--fields` heard by `prune` only as the
first word, `export`'s target read as its directory, a second source
taken by `receive` over the first, `--fields` read by `receive` as
joining unrelated histories, and the first of two directories taken by
`offer`; and seventeen fetch breaks: a document filed whose text is not the
digest offered, a payload landed whatever it hashes to, a payload filed
under the name it was staged at, a path asked for beside the one the
manifest names, a URL's last slash cut off its directory, a second URL
taken over the first, `--fields` read as joining unrelated histories, a
bookmark's line discarded as a kind the reader does not know, a revision
the two sides share found only where all are, unrelated histories joined
unasked, every original held destroyed, what a manifest's lines say they
forget ignored, one bookmark written twice in a pass, a revision taken
named twice, a byte escaped in lowercase hex, a space asked for as it is,
and a `~` escaped that need not be;
and fifteen update breaks:
bytes no revision records written over, a file kept whose mode is not the
one recorded, a file nobody recorded taken away, a file of lines written
without its tree's mode, a link pointed at the path it names rather than
from where it stands, history taken to hold every file of lines empty,
the folder said to hold the target while a link is still to point, the
folder not said to hold it while a file is left alone, a dry run that
names no mode it would set, a mode the plan sets left unset, a path the
target holds taken for one it does not, a file the walk took read by
another path's digest, a settled update forgetting the files it leaves
alone, a revision named that is not a head laid out, and the first of
several heads taken when none is named; and three resolution
breaks: a name run into a `keep` it does not continue, a line the person
deleted kept, and a `keep` read from one item past where it starts; and two
rendering breaks: a run nothing met labelled, and a region meeting at a
file's end left uncounted; and seventeen merge breaks: the current heads nobody
named left out, a head joined by its spelling rather than the revision it
names, text nobody recorded written over, a payload laid over work
nobody recorded, a file written at its identifier rather than its path,
the folder asked about a file's own path rather than where it is written,
what a head leaves a file of lines as taken from its tree's payload, a
file of lines written without its tree's mode, the file that keeps a
path written beside it too, a file set aside written at the path its
first claimant keeps, only the first file of the tree laid out, a link
pointed again where it already points, a run labelled in words the marker
search does not look for, a line of the merged file itself counted as a
marker, a head named in the `record` line by its digest rather than as
typed, a path settled there the other way round, and a contested file of
bytes left out of the files where work met; and three breaks of a stand-in beside a held original:
one that rewrites a line it does not forget, the text of a forgotten line
taken from whichever stand-in folds in last, and one that forgets nothing; and two map breaks: the digest map `status`
builds from the host's answers left empty, and the survey's arriving
paths taken as none; and eight normal-form
breaks: a mark put on its run unsorted, a run of marks dropped where a
starter closes it, a class lookup that stops at a run beginning with the
character, both of two names that are one path kept, the file kept for a
path dropped, a read that opens any name its listing has, a name that
cannot be spelled passed over, and a quick check that passes too little; and three command-line
breaks: `-C` counting the first directory rather than the last, `-V`
not read as the version, and `-h` not read as help; and two
dispatch breaks: any word looked up on `PATH`, and `[` let into the
alphabet; and one header break: a note under the format line read as a
layout; and seven identity breaks: the default author forgotten, an empty
`$HISTORICA_AUTHOR` taken for an author, an empty
`$XDG_CONFIG_HOME` taken for a directory, the directory `identity` makes
keeping its slash, a block let state two authors, a block's refusal said
at its last line, and a directory's second block taken; and three editor
breaks: an empty editor run, an editor a signal ended taken to have saved,
and its file put a directory down; and six more forgetting breaks:
`--fields` stating only the first digest gone, `--dry-run` saying it
destroyed what it would destroy, a payload's stand-in filed beside it
whatever is there, a file of lines that will not replay forgotten whole,
the sweep removing `operations/` itself, and a resolution's copy replacing
the span rather than joining it; and one opening break: a revision's
headers read past the blank line; and nine `check` breaks: a new store's note read
as a layout, only the last word read as asking for `--complete`, a note
counted among the errors, a head it cannot produce failing it unasked, a
bookmark to a file only a `bytes` header names or to a revision here not
followed, a link's target line read as an entry, a file's size taken for
its name, and a text payload read from where another digest is stored; and
eight `init` breaks: the header written where the store does not look for
it, a note written beside the store rather than in it, a note written
into a directory it does not make, the notes written where `init` runs
rather than under the store, the cache note's last newline lost, a line
of a note ended by a carriage return, an absolute path joined under the
base, and a `/` doubled after a base that ends with one; and seven
UTF-8 breaks: a three-byte character's middle byte kept to five bits, a
three-byte lead read as a two-byte one, the first character past the
surrogates taken for one, and a validator that refuses `9F` after `ED`,
`90` after `F0`, `F4` as a lead, or `BF` as a continuation; and fourteen `skip` breaks: rule equality blind to privacy, a directory's rule
written without its slash, a private name read back as shared, a
directory's rule that does not skip the directory or that skips what only
begins with its name, a listing that forgets the rule it just kept, a rule
asked about against the rules written before the last, `--name` taken for
the name it matches, a flag it does not take read as a path, a
`--private` after a path forgotten, a rule written that covers what
history holds, the refusal passing over the first rule asked, a rule's
path spelled from the root rather than past the repository, and the
repository itself taken for a path to skip; and eight breaks of reading what the host
answers: a digest the store lacks read at `-`, one it lacks taken as held,
one it holds taken as lacking, a forgetting document read for a digest
the store lacks and read at its line less a character, the answers read a
line late, a digest the store holds taken as unsettled, and a program's
arguments run together; and eight breaks of the folder's walk: a link's
target read in normal form C, a directory listed where its name's normal
form spells it, each directory paired with another's spelling, a file's
name read as the folder spells it, every file found empty, a file that
runs read as one that does not, the files sorted by path backwards, and
every file found at a path yielded; and four pattern breaks: a run found a
character short of where it stands, the last run asked to open the rest
of the name, a middle run found and not passed, and the first run asked to
end the name; and four breaks of reading what the host hashed: its answer
split at spaces, a size filed by `forget` as a digest, one path's line
read again for the next, and a payload named by `arrange` by its whole
line; and two stand-in breaks: a stand-in taken for a digest its own
begins with, and every document read taken as one. The
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

- **Forgetting**, at one edge: a resolution's stand-in beside a held resolution
  is not read, which is the Rust tool's first reading of it and not its
  later ones (above). And where the Rust tool's catalogue in `cache/` is
  stale — a stand-in copied in after it was written — the Rust store
  believes it for a document it holds and misses the stand-in, where the
  host here reads every path the catalogue does not account for and finds
  it. A directory under `operations/` whose name is not UTF-8, which no
  writer makes, is never swept: the host lists it as a name that cannot be
  spelled, not as a directory, where the Rust sweep removes it if empty.
- **`cache/`** is never written, which any reader rebuilds.
- **A file the filesystem will not hand over** is not `check`'s
  `Unreadable`: the port's host reads what it is asked for or stops, and
  run as root, as `check.py` is, nothing refuses a read. A file of names
  or rules, or the identity file, whose bytes are not UTF-8 is refused
  and reported as the Rust tool does.
- **A revision that reads only as far as opening** is in the graph and
  refused where `log`, `show`, `files`, `cat`, `blame`, `status` and
  `diff` ask what it did; `record`, `amend`, `abandon`, `carry`, `name`,
  `skip`, `update` and `merge` read only the revisions that read whole, or
  whose only fault is a path not in normal form C, as before.
- **Which refusal a walk names** where two events of one walk each
  contradict their views: the port names the first in its own causal
  order, which need not be the one `merge.rs`'s order meets first.
- **Two directories that are one path** in normal form C are walked as
  the last of them, where the Rust walk walks both and keeps, file by
  file, the last it met.
- **`fetch`'s edges**: a file that arrives whole and does not parse is
  refused in the port's parsers' words. A path with `..` in it is asked
  for as the Rust tool asks for it, escaped byte by byte with `/` kept,
  and what the host makes of it is the host's.
- **`export`'s edges**: the folder a copy is caught up to is read from
  this store's documents rather than the copy's, which differ only where
  the copy lacks bytes this store holds; and a path the tree places under a
  file the folder holds is refused in the port's words. The copy's
  documents are written as they were read, not rewritten from what they
  parse to, which is the same bytes in any store `check` passes.

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
