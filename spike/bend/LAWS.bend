# What the port promises, as claims Bend can check. Each is proven in
# PROOF.bend by a def of the same name; `bend PROOF.bend` fails while any
# is open or false.

import Base
import ./sha256.bend as Sha
import ./ops.bend as Ops
import ./text.bend as T
import ./revision.bend as Rev
import ./replay_spec.bend as Spec
import ./cursor_spec.bend as Cursor
import ./semantic_replay.bend as Block
import ./merge.bend as Merge
import ./tree.bend as Tree
import ./commands.bend as Main
import ./similar.bend as Sim
import ./folder.bend as Folder
import ./bookmark.bend as Bm
import ./store.bend as Store
import ./survey.bend as Sv
import ./standin.bend as Stand
import ./forget.bend as Fg
import ./resolution.bend as Res
import ./sort_lemmas.bend as SortL
import ./naming.bend as Naming
import ./fulls_lemmas.bend as FullsL
import ./fetch_lemmas.bend as FetchL
import ./update.bend as Upd
import ./conflict.bend as Conflict
import ./merging.bend as Merging
import ./argv.bend as Argv
import ./shell.bend as Shell
import ./identity.bend as Identity
import ./check.bend as Check
import ./skip.bend as Skip
import ./notes.bend as Notes
import ./arrange.bend as Arrange
import ./prune.bend as Prune
import ./receive.bend as Receive
import ./offer.bend as Offer
import ./export.bend as Export
import ./nfc.bend as Nfc
import ./nfc_tables.bend as Tab
import ./nfc_lemmas.bend as NfcL
import ./fetch.bend as Fetch
import ./utf8.bend as Utf8

# LAW: every digest is sixty-four characters, whatever the bytes — the
# shape a `result`, a `parent`, or a filename in the store relies on.
law digest_length:
  for bs: List<&2, U32>
  {String.length(Sha.digest(bs)) == 64n : Nat}

# LAW: an insert removes nothing, so its end is where it begins; that is
# what lets two inserts sit at one position without overlapping a run.
law insert_removes_nothing:
  for at: Nat
  for items: List<&2, Ops.Item>
  {Ops.end(Ops.Op{Ops.Insert{}, at, items}) == at : Nat}

# LAW: a delete's end is its position plus what it removes.
law delete_end:
  for at: Nat
  for items: List<&2, Ops.Item>
  {Ops.end(Ops.Op{Ops.Delete{}, at, items}) == Nat.add(at, List.length(&2, Ops.Item, items)) : Nat}

# LAW: forgetting discards text, not the newline. The old unconditional
# claim disagreed with Rust/Verus replay for an unterminated parent item.
law forgotten_agrees:
  for text: String
  for terminated: Bool
  for forgotten: Bool
  {Ops.agrees(Ops.forgotten(), Ops.Item{text, terminated, forgotten}) == terminated : Bool}

# LAW: and a forgotten item is nobody's line: the diff never keeps one.
law forgotten_is_nobodys:
  for b: Ops.Item
  {Ops.same(Ops.forgotten(), b) == False{} : Bool}

# LAW: a verb is itself.
law verb_refl:
  for v: Ops.Verb
  {Ops.verb_is(v, v) == True{} : Bool}

# LAW: the first operation of a document has nothing to be ordered after.
law ordered_first:
  for op: Ops.Op
  {Ops.ordered(None{}, op) == None{} : Maybe<&2, String>}

# LAW: advancing nowhere changes nothing.
law advance_nothing:
  for state: List<&2, Ops.Item>
  for acc: List<&2, Ops.Item>
  {Ops.advance(0n, state, acc) == Ops.Advanced{acc, state} : Ops.Advanced}

# LAW: advancing never loses an item: what is kept and what is left add
# up to what there was, for every distance.
law advance_keeps_everything:
  for n: Nat
  for +state: List<&2, Ops.Item>
  for +acc: List<&2, Ops.Item>
  {Ops.advance_width(Ops.advance(n, state, acc)) == Nat.add(List.length(&2, Ops.Item, acc), List.length(&2, Ops.Item, state)) : Nat}

# LAW: a delete that quotes nothing removes nothing and cannot disagree.
law drop_nothing:
  for state: List<&2, Ops.Item>
  for ok: Bool
  {Ops.drop_checked(Nil{}, state, ok) == Ops.Dropped{state, ok} : Ops.Dropped}

# LAW: a document with no operations leaves the parent as it was, and a
# state has one text: a single terminated line is that line and a newline.
law text_of_line:
  for s: String
  {Ops.text([Ops.line(s)]) == String.append(s, "\n") : String}

# LAW: the empty history has no heads, and nothing superseded or missing.
law empty_history_heads:
  {Rev.heads(Rev.empty()) == Nil{} : List<&2, String>}

# LAW: a root revision alone is its history's one head.
law root_is_head:
  for id: String
  for change: String
  for message: String
  {Rev.heads(Rev.insert(Rev.empty(), Rev.Revision{id, change, Nil{}, Nil{}, message})) == [id] : List<&2, String>}

# LAW: a change nobody has recorded is unknown, in any history.
law no_revisions_unknown:
  for any: Bool
  {Rev.change_state.of(False{}, Nil{}) == Rev.UnknownChange{} : Rev.ChangeState}

# The Verus replay contract, starting with its executable primitives.
law agreement_matches_spec:
  for a: Ops.Item
  for b: Ops.Item
  {Ops.agrees(a, b) == Spec.matches(a, b) : Bool}

# Exact contents, not only width: advance transfers the prefix in reverse
# onto the accumulator and leaves precisely the suffix.
law advance_exact:
  for n: Nat
  for +state: List<&2, Ops.Item>
  for acc: List<&2, Ops.Item>
  {Ops.advance(n, state, acc) == Ops.Advanced{List.reverse.go(&2, Ops.Item, List.take(&2, Ops.Item, state, n), acc), List.drop(&2, Ops.Item, state, n)} : Ops.Advanced}

# A delete drops exactly its quoted width (clamped at the end), and its
# success flag means every quote matched, preserving an earlier failure.
law drop_checked_exact:
  for +recorded: List<&2, Ops.Item>
  for +state: List<&2, Ops.Item>
  for +ok: Bool
  {Ops.drop_checked(recorded, state, ok) == Ops.Dropped{List.drop(&2, Ops.Item, state, List.length(&2, Ops.Item, recorded)), Bool.and(ok, Spec.prefix_matches(recorded, state))} : Ops.Dropped}

law result_no_operations:
  for +parent: List<&2, Ops.Item>
  for p: Nat
  {Spec.result_from(parent, Nil{}, p) == parent : List<&2, Ops.Item>}

# Full cursor invariant: the implementation's reversed accumulator is the
# forward prefix of the specification, and an earlier error stays first.
law cursor_walk_equivalent:
  for +ops: List<&2, Ops.Op>
  for +pos: Nat
  for +state: List<&2, Ops.Item>
  for +acc: List<&2, Ops.Item>
  for +error: Maybe<&2, String>
  {Ops.apply.go(ops, Ops.land(ops, pos, state, acc), pos, error) == Cursor.combine(error, List.reverse(&2, Ops.Item, acc), Cursor.walk(ops, pos, state)) : Result<&2, &2, String, List<&2, Ops.Item>>}

# Lift the invariant through the public range/newline/digest checks.
law cursor_apply_equivalent:
  for +state: List<&2, Ops.Item>
  for +doc: Ops.Doc
  {Ops.apply(state, doc) == Cursor.apply(state, doc) : Result<&2, &2, String, List<&2, Ops.Item>>}


# Absolute coordinate changes do not alter positional replay. No ordering,
# range or quote-agreement assumptions are needed for this model theorem.
law positional_translation:
  for +parent: List<&2, Ops.Item>
  for +ops: List<&2, Ops.Op>
  for +offset: Nat
  for +position: Nat
  {Spec.result_from(parent, Spec.shift(ops, offset), Nat.add(offset, position)) == Spec.result_from(parent, ops, position) : List<&2, Ops.Item>}

# A parent split witnesses ANY valid gap. Insertions, deletions and same-gap
# replacements use the independent positional output, with checks retained.
# This quantifies over arbitrary item lists, not a bounded fixture set.
law edit_block_semantics:
  for +before: List<&2, Ops.Item>
  for +after: List<&2, Ops.Item>
  for +stated: Maybe<&2, String>
  for +edit: Ops.Edit
  {Ops.apply(List.append(&2, Ops.Item, before, after), Ops.Doc{None{}, stated, Ops.operations(List.length(&2, Ops.Item, before), edit)}) == Block.apply(before, after, stated, edit) : Result<&2, &2, String, List<&2, Ops.Item>>}

# A whole script of blocks — each starting a stated gap past where the last
# finished, which is every shape the parser's ordering rules admit — replays
# to the positional result of its operations, or to the first delete whose
# quote the parent does not hold at that delete's own coordinate. Nothing
# about the cursor appears on the right-hand side.
law script_semantics:
  for +parent: List<&2, Ops.Item>
  for +stated: Maybe<&2, String>
  for +steps: List<&2, Ops.Step>
  {Ops.apply(parent, Ops.Doc{None{}, stated, Ops.script(steps, 0n)}) == Block.replay(parent, stated, steps) : Result<&2, &2, String, List<&2, Ops.Item>>}

# Raw operations are a script when each sits at or past where the last
# finished, an insert at a delete's own position being that delete's
# replacement (`Block.ordered`); `Block.steps_of` reads the script off them.
law ordered_operations_are_scripts:
  for +ops: List<&2, Ops.Op>
  for +pos: Nat
  for +e: {Block.ordered(ops, pos) == True{} : Bool}
  {Ops.script(Block.steps_of(ops, pos), pos) == ops : List<&2, Ops.Op>}

# So any ordered document replays to its positional result, stated over the
# operations themselves.
law ordered_document_semantics:
  for +parent: List<&2, Ops.Item>
  for +stated: Maybe<&2, String>
  for +ops: List<&2, Ops.Op>
  for +e: {Block.ordered(ops, 0n) == True{} : Bool}
  {Ops.apply(parent, Ops.Doc{None{}, stated, ops}) == Block.replay_ops(parent, stated, ops) : Result<&2, &2, String, List<&2, Ops.Item>>}

# The parser only accepts ordered documents: whatever `Ops.parse` returns
# as a document has operations `Block.ordered` admits from position zero.
law parser_accepts_ordered:
  for +s: String
  for -forgets: Maybe<&2, String>
  for -result: Maybe<&2, String>
  for +ops: List<&2, Ops.Op>
  for e: {Ops.parse(s) == Done{Ops.Doc{forgets, result, ops}} : Result<&2, &2, String, Ops.Doc>}
  {Block.ordered(ops, 0n) == True{} : Bool}

# So every document the parser accepts replays to its positional result:
# applying it is `Block.replay_ops`, with no cursor in the statement.
law parsed_document_semantics:
  for +parent: List<&2, Ops.Item>
  for +stated: Maybe<&2, String>
  for +s: String
  for -forgets: Maybe<&2, String>
  for +ops: List<&2, Ops.Op>
  for e: {Ops.parse(s) == Done{Ops.Doc{forgets, stated, ops}} : Result<&2, &2, String, Ops.Doc>}
  {Ops.apply(parent, Ops.Doc{None{}, stated, ops}) == Block.replay_ops(parent, stated, ops) : Result<&2, &2, String, List<&2, Ops.Item>>}

# A decimal number is spelled as it was read: `T.number` admits one
# spelling per value, and `T.spell` produces it.
law spell_number:
  for +s: String
  for +n: Nat
  for e: {T.number(s) == Some{n} : Maybe<&2, Nat>}
  {T.spell(n) == s : String}

# The writer reproduces every document the parser accepts, byte for byte.
# There is one spelling of each set of facts, and the parser admits only it.
law write_parse:
  for +s: String
  for doc: Ops.Doc
  for e: {Ops.parse(s) == Done{doc} : Result<&2, &2, String, Ops.Doc>}
  {Ops.write(doc) == s : String}

# So does the revision writer: every revision document the parser accepts
# is the one `Rev.write` spells from what it read. The headers come in one
# order and a key that may not repeat comes once, so the parser admits one
# spelling of each revision.
law revision_write_parse:
  for +s: String
  for +r: Rev.Rev
  for e: {Rev.parse(s) == Done{r} : Result<&2, &2, String, Rev.Rev>}
  {Rev.write(r) == s : String}

# The diff replays: whatever document `Ops.diff` writes for a parent and a
# child, applying it to the parent produces the child. A child that is a
# file has a newline on every item but the last.
law diff_applies:
  for +parent: List<&2, Ops.Item>
  for +child: List<&2, Ops.Item>
  for tbl: {Ops.terminated_but_last(child) == True{} : Bool}
  for +doc: Ops.Doc
  for e: {Ops.diff(parent, child) == Some{doc} : Maybe<&2, Ops.Doc>}
  {Ops.apply(parent, doc) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}

# Refusals are justified: whenever an ordered document is refused, one of
# four causes holds, each read off the parent and the operations alone —
# an operation past the end, a delete quoting what the parent does not
# hold at its own coordinate, an item without a newline that is not last,
# or a stated digest the result does not have (`Block.cause`).
law refusal_has_cause:
  for +parent: List<&2, Ops.Item>
  for +stated: Maybe<&2, String>
  for +ops: List<&2, Ops.Op>
  for +e: {Block.ordered(ops, 0n) == True{} : Bool}
  for -msg: String
  for r: {Ops.apply(parent, Ops.Doc{None{}, stated, ops}) == Fail{msg} : Result<&2, &2, String, List<&2, Ops.Item>>}
  {Block.cause(parent, stated, ops) == True{} : Bool}

# And with no cause, the replay is the positional result.
law no_cause_replays:
  for +parent: List<&2, Ops.Item>
  for +stated: Maybe<&2, String>
  for +ops: List<&2, Ops.Op>
  for +e: {Block.ordered(ops, 0n) == True{} : Bool}
  for c: {Block.cause(parent, stated, ops) == False{} : Bool}
  {Ops.apply(parent, Ops.Doc{None{}, stated, ops}) == Done{Spec.result(parent, ops)} : Result<&2, &2, String, List<&2, Ops.Item>>}

# The merge converges: one graph replayed in any two causal orders — each
# event once, the same events in both, none before an event it had seen —
# merges to one file, or is refused in both. `Merge.merged` is the model
# of `merge.rs`: Eg-walker over Fugue, each event decided on the view its
# author had, its elements placed by name among their siblings.
law merge_converges:
  for +g: List<&2, Merge.Rev>
  for +a: List<&2, Nat>
  for +b: List<&2, Nat>
  for +e: {Merge.orders(g, a, b) == True{} : Bool}
  {Merge.merged(g, a) == Merge.merged(g, b) : Maybe<&2, List<&2, Ops.Item>>}

# A merge revision that records nothing changes nothing: an event with no
# document, walked last, leaves the file the events before it made. This
# is `historica merge` on one head, and a merge recorded with nothing said
# about this file; `merge_converges` says the events before it read the
# same in any causal order, so the merge revision adds nothing of its own.
law merge_records_nothing:
  for +g: List<&2, Merge.Rev>
  for +o: List<&2, Nat>
  for +past: List<&2, Nat>
  for b: {Merge.below(o, List.length(&2, Merge.Rev, g)) == True{} : Bool}
  {Merge.merged(List.append(&2, Merge.Rev, g, [Merge.Rev{past, None{}}]), List.append(&2, Nat, o, [List.length(&2, Merge.Rev, g)])) == Merge.merged(g, o) : Maybe<&2, List<&2, Ops.Item>>}

# On one line of history the merge is plain replay (decision 0007): a
# chain of documents — each an event that has seen every event before it,
# each ordered as the parser orders operations — that applies link by link
# from the empty file merges, walked in its own order, to the file the
# replay made. The parser's order matters: two inserts at one position in
# one document replay in the order written, where Fugue reads the second
# before the first.
law merge_linear:
  for +docs: List<&2, List<&2, Ops.Op>>
  for -f: List<&2, Ops.Item>
  for +o: {Block.each_ordered(docs) == True{} : Bool}
  for e: {Merge.replay(docs, Done{Nil{}}) == Done{f} : Result<&2, &2, String, List<&2, Ops.Item>>}
  {Merge.merged(Merge.chain(docs), Merge.upto(List.length(&2, List<&2, Ops.Op>, docs))) == Some{f} : Maybe<&2, List<&2, Ops.Item>>}

# Every merge keeps the invariant. `insert_at_gap` assumes of an author's
# view that its reading finishes within its fuel and reads no element
# twice; this is that assumption discharged for every tree a walk builds,
# in any order that names each event once, however concurrent its events.
# An element a concurrent event attached may sit among siblings anywhere
# in name order, and the reading is still the old one with it spliced in
# once, where its parent's list is read.
law merge_walk_invariant:
  for +g: List<&2, Merge.Rev>
  for +o: List<&2, Nat>
  for +t: List<&2, Merge.Node>
  for +d: {Merge.distinct(o) == True{} : Bool}
  for e: {Merge.walk(o, g, Some{Nil{}}) == Some{t} : Maybe<&2, List<&2, Merge.Node>>}
  {Merge.invariant(t) == True{} : Bool}

# Every view keeps the invariant. An author's view is the tree restricted
# to the events they had seen; walked after events they had not, the tree
# holds more than the view. Restricted to any set of events that holds the
# past of each — as what an author had seen does — a tree a walk built is
# the tree the set's own events walk to, in the same order, so it keeps
# the invariant too, and `insert_at_gap` applies to every event of every
# merge, however concurrent.
law view_keeps_invariant:
  for +g: List<&2, Merge.Rev>
  for +o: List<&2, Nat>
  for +t: List<&2, Merge.Node>
  for +s: List<&2, Nat>
  for +d: {Merge.distinct(o) == True{} : Bool}
  for +c: {Merge.closed(s, g, s) == True{} : Bool}
  for e: {Merge.walk(o, g, Some{Nil{}}) == Some{t} : Maybe<&2, List<&2, Merge.Node>>}
  {Merge.invariant(Merge.restrict(t, s)) == True{} : Bool}

# An event that had seen everything before it applies its document. Walk
# any history `p` to `f0`; an event `e` outside it that had seen every one
# of its events, and states a document the parser would accept, walked
# next leaves exactly what `Ops.apply` makes of that document on `f0`.
# This is `merge_linear` without the line: the history may be as
# concurrent as the graph likes — the event's view is the whole tree, and
# the tree keeps the invariant however it was built.
law merge_extends:
  for +g: List<&2, Merge.Rev>
  for +p: List<&2, Nat>
  for +e: Nat
  for +past: List<&2, Nat>
  for +d: List<&2, Ops.Op>
  for +f0: List<&2, Ops.Item>
  for +f1: List<&2, Ops.Item>
  for +hd: {Merge.distinct(p) == True{} : Bool}
  for +he: {Merge.has(p, e) == False{} : Bool}
  for +hs: {Merge.subset(p, past) == True{} : Bool}
  for +hg: {List.get(&2, Merge.Rev, g, e) == Some{Merge.Rev{past, Some{Merge.Edits{d}}}} : Maybe<&2, Merge.Rev>}
  for +ho: {Block.ordered_all(d, None{}, None{}) == True{} : Bool}
  for +hm: {Merge.merged(g, p) == Some{f0} : Maybe<&2, List<&2, Ops.Item>>}
  for +ha: {Ops.apply(f0, Ops.Doc{None{}, None{}, d}) == Done{f1} : Result<&2, &2, String, List<&2, Ops.Item>>}
  {Merge.merged(g, List.append(&2, Nat, p, [e])) == Some{f1} : Maybe<&2, List<&2, Ops.Item>>}

# An event applies its document to what its author saw. Walk any history
# `p` to `t`; an event outside it had seen the closed set `past`, and saw
# the file of `t` restricted to it. If its document applies to that file,
# then once the event is walked, the author's view — `past` and the event
# itself — reads what the document made of it, whatever `p` holds that the
# author had not seen. `merge_extends` is the case where `past` holds all
# of `p`; this is Eg-walker's promise for every event of every merge.
law merge_intent:
  for +g: List<&2, Merge.Rev>
  for +p: List<&2, Nat>
  for +e: Nat
  for +past: List<&2, Nat>
  for +d: List<&2, Ops.Op>
  for +t: List<&2, Merge.Node>
  for +f1: List<&2, Ops.Item>
  for +hd: {Merge.distinct(p) == True{} : Bool}
  for +he: {Merge.has(p, e) == False{} : Bool}
  for +hc: {Merge.closed(past, g, past) == True{} : Bool}
  for +hg: {List.get(&2, Merge.Rev, g, e) == Some{Merge.Rev{past, Some{Merge.Edits{d}}}} : Maybe<&2, Merge.Rev>}
  for +ho: {Block.ordered_all(d, None{}, None{}) == True{} : Bool}
  for +hw: {Merge.walk(p, g, Some{Nil{}}) == Some{t} : Maybe<&2, List<&2, Merge.Node>>}
  for +ha: {Ops.apply(Merge.file(Merge.restrict(t, past)), Ops.Doc{None{}, None{}, d}) == Done{f1} : Result<&2, &2, String, List<&2, Ops.Item>>}
  {Merge.seen_file(Merge.walk(List.append(&2, Nat, p, [e]), g, Some{Nil{}}), e <> past) == Some{f1} : Maybe<&2, List<&2, Ops.Item>>}

# One insertion lands at the gap its author asked for. `Merge.invariant`
# is what holds of an author's view as their run grows it — the reading
# of every sibling list finishes within the fuel `order` gives it, and no
# element is read twice — and `Merge.fresh` is a name the view neither
# holds nor hangs anything under, which is what an event mints. An
# element anchored by Fugue's rule after the visible element at `at`
# (`left_of`, over the view with its tombstones left out) is read, once
# the tombstones are left out again, exactly at that gap: `attach`
# places it by name among siblings, but the anchor gives it none — the
# element it follows had no right child, or the descent through the
# first right child's left children, tombstones included, landed on an
# element with no left child. The anchor that skips tombstones, or a
# descent that does, is what `check.py` breaks.
law insert_at_gap:
  for +t: List<&2, Merge.Node>
  for at: Nat
  for +nm: Merge.Name
  for +it: Ops.Item
  for +left: Maybe<&2, Merge.Name>
  for +inv: {Merge.invariant(t) == True{} : Bool}
  for +fr: {Merge.fresh(t, nm) == True{} : Bool}
  for lo: {Merge.left_of(Merge.visible(t), at) == Some{left} : Maybe<&2, Maybe<&2, Merge.Name>>}
  {Merge.visible(Merge.attach(t, Merge.Node{nm, it, Merge.anchor(t, left), Nil{}})) == List.append(&2, Merge.Node, List.take(&2, Merge.Node, Merge.visible(t), at), Merge.Node{nm, it, Merge.anchor(t, left), Nil{}} <> List.drop(&2, Merge.Node, Merge.visible(t), at)) : List<&2, Merge.Node>}

# The invariant is a fact about reachable views: the empty view has it,
# an anchored attach of a fresh element after a visible one (or at the
# front) keeps it, and a mark keeps it. `inserts` and `deletes` do
# nothing else to the view.
law invariant_empty:
  {Merge.invariant(Nil{}) == True{} : Bool}

law insert_keeps_invariant:
  for +t: List<&2, Merge.Node>
  for +nm: Merge.Name
  for +it: Ops.Item
  for +left: Maybe<&2, Merge.Name>
  for +inv: {Merge.invariant(t) == True{} : Bool}
  for +fr: {Merge.fresh(t, nm) == True{} : Bool}
  for lo: {Merge.in_view(t, left) == True{} : Bool}
  {Merge.invariant(Merge.attach(t, Merge.Node{nm, it, Merge.anchor(t, left), Nil{}})) == True{} : Bool}

law mark_keeps_invariant:
  for +t: List<&2, Merge.Node>
  for +target: Merge.Name
  for +by: Nat
  for inv: {Merge.invariant(t) == True{} : Bool}
  {Merge.invariant(Merge.mark(t, target, by)) == True{} : Bool}

# The tree: what a revision leaves behind, whatever file set it is
# applied to. `Tree.apply` is `tree.rs`'s linear case; a `Done` from it
# is a tree the store will show.

# One line of history never puts two files at one path: every path in
# the tree a revision leaves names at most one file.
law one_file_per_path:
  for +t: Tree.Tree()
  for r: Rev.Rev
  for +t2: Tree.Tree()
  for +q: String
  for e: {Tree.apply(t, r) == Done{t2} : Result<&2, &2, Tree.Fault, Tree.Tree()>}
  {Tree.at_most_one(Tree.at(t2, q)) == True{} : Bool}

# No link is left dangling: every `file:` reference in the tree a
# revision leaves names a file that tree holds (decision 0040). The
# check runs before the payloads are restated; the law says restating
# them keeps it.
law no_link_dangles:
  for +t: Tree.Tree()
  for r: Rev.Rev
  for +t2: Tree.Tree()
  for e: {Tree.apply(t, r) == Done{t2} : Result<&2, &2, Tree.Fault, Tree.Tree()>}
  {Tree.dangling(t2, t2) == Done{Unit{}} : Result<&2, &2, Tree.Fault, Unit>}

# A file's kind is fixed when it is added (decision 0017): at every
# revision it survives, it holds the kind it was added with. No `move`,
# `mode`, `link`, `bytes` or second `add` changes it.
law kind_fixed:
  for +t: Tree.Tree()
  for r: Rev.Rev
  for +t2: Tree.Tree()
  for +x: String
  for +k: Tree.FileKind
  for e: {Tree.apply(t, r) == Done{t2} : Result<&2, &2, Tree.Fault, Tree.Tree()>}
  for h: {Tree.kind(t, x) == Some{k} : Maybe<&2, Tree.FileKind>}
  {Tree.kind_kept(k, Tree.kind(t2, x)) == True{} : Bool}

# And so for a whole chain replayed from nothing.
law replay_one_file_per_path:
  for +rs: List<&2, Rev.Rev>
  for +t: Tree.Tree()
  for +q: String
  for e: {Tree.replay(rs) == Done{t} : Result<&2, &2, Tree.Fault, Tree.Tree()>}
  {Tree.at_most_one(Tree.at(t, q)) == True{} : Bool}

law replay_no_link_dangles:
  for +rs: List<&2, Rev.Rev>
  for +t: Tree.Tree()
  for e: {Tree.replay(rs) == Done{t} : Result<&2, &2, Tree.Fault, Tree.Tree()>}
  {Tree.dangling(t, t) == Done{Unit{}} : Result<&2, &2, Tree.Fault, Unit>}

# A move a drop follows is a drop: restating where an entry sits and
# then removing its file leaves what removing its file leaves.
law move_then_drop:
  for t: Tree.Tree()
  for e: Tree.Entry
  for p: String
  {Tree.remove(Tree.insert(t, Tree.with_path(e, p)), Tree.entry_file(e)) == Tree.remove(t, Tree.entry_file(e)) : Tree.Tree()}

# The merge is a function of what each revision's parents are, not the
# order it lists them: two graphs alike but for that order — the same
# revisions in the same order, each with the same digest and facts, each
# naming the same parents as a set — merge to one file set, with one
# report of what was contested. `Tree.merge` is `tree.rs`'s graph case.
# A refusal is not a merge, and the fault may name another parent, so the
# law is stated of the merge that succeeded.
law merge_parents_unordered:
  for +es: List<&2, Tree.Ev>
  for +es2: List<&2, Tree.Ev>
  for m: Tree.Merged
  for +a: {Tree.alike(es, es2) == True{} : Bool}
  for e: {Tree.merge(es) == Done{m} : Result<&2, &2, Tree.Fault, Tree.Merged>}
  {Tree.merge(es2) == Done{m} : Result<&2, &2, Tree.Fault, Tree.Merged>}

# The order the tool walks a merge in. `cat`, `diff` and `blame` walk a
# target's ancestry sorted by how many events each had seen; where every
# event had seen more than any event it had seen (`Main.deepens`), that is
# a causal order: nothing comes before an event it had seen.
law walked_order_causal:
  for +g: List<&2, Merge.Rev>
  for +h: {Main.deepens(g) == True{} : Bool}
  {Merge.causal(Main.walked.order(g), g) == True{} : Bool}

# And what the tool reads from its walk is what any causal order of the
# graph's events reads, by `merge_converges`: which of them the tool picks
# is not something a reader can see.
law walked_reads_every_order:
  for +head: String
  for +file: String
  for +names: List<&2, String>
  for +g: List<&2, Merge.Rev>
  for +b: List<&2, Nat>
  for +w: Main.Walked
  for +hb: {Merge.distinct(b) == True{} : Bool}
  for +hc: {Merge.causal(b, g) == True{} : Bool}
  for +hs: {Merge.subset(b, Merge.upto(List.length(&2, Merge.Rev, g))) == True{} : Bool}
  for +ht: {Merge.subset(Merge.upto(List.length(&2, Merge.Rev, g)), b) == True{} : Bool}
  for e: {Main.walked.causal(head, file, names, g, Main.deepens(g)) == Done{w} : Result<&2, &2, String, Main.Walked>}
  {Some{Main.walked.file(w)} == Merge.merged(g, b) : Maybe<&2, List<&2, Ops.Item>>}

# The same of the whole reading: the file `cat`, `diff` and `blame` take
# from the walk of a target's ancestry is what every causal order of the
# graph it builds from the store reads — each revision an event, its
# ancestors its past, what it stated about the file its statement.
law walked_file_every_order:
  for +fs: List<&2, Main.Full>
  for +ds: List<&2, Store.Doc>
  for +head: String
  for +file: String
  for +ss: List<&2, Tree.Seen>
  for +g: List<&2, Merge.Rev>
  for +b: List<&2, Nat>
  for +w: Main.Walked
  for +hs: {Tree.seen(List.length(&2, Main.Full, Main.walked.ancestry(fs, head)), Main.events_of(Main.walked.ancestry(fs, head)), Nil{}) == Done{ss} : Result<&2, &2, Tree.Fault, List<&2, Tree.Seen>>}
  for +hg: {Main.walked.revs(Main.walked.ancestry(fs, head), Main.ids(Main.walked.ancestry(fs, head)), Main.minted_digests(Main.walked.ancestry(fs, head), file), ss, ds, file) == Done{g} : Result<&2, &2, String, List<&2, Merge.Rev>>}
  for +hb: {Merge.distinct(b) == True{} : Bool}
  for +hc: {Merge.causal(b, g) == True{} : Bool}
  for +hu: {Merge.subset(b, Merge.upto(List.length(&2, Merge.Rev, g))) == True{} : Bool}
  for +ht: {Merge.subset(Merge.upto(List.length(&2, Merge.Rev, g)), b) == True{} : Bool}
  for e: {Main.walked.of(fs, ds, head, file) == Done{w} : Result<&2, &2, String, Main.Walked>}
  {Some{Main.walked.file(w)} == Merge.merged(g, b) : Maybe<&2, List<&2, Ops.Item>>}

# The diff the commands draw takes one side to the other. `diff` and
# `blame` over the folder and across `--onto` compare with `similar`'s
# Histogram search, as the Rust tool does; whatever it finds, the document
# written from it applies to the parent and gives the child.
law similar_diff_applies:
  for +parent: List<&2, Ops.Item>
  for +child: List<&2, Ops.Item>
  for tbl: {Ops.terminated_but_last(child) == True{} : Bool}
  for +doc: Ops.Doc
  for e: {Sim.diff(parent, child) == Some{doc} : Maybe<&2, Ops.Doc>}
  {Ops.apply(parent, doc) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}

# Emphasis changes no character. Where two lines were replaced one for one,
# each is cut into words, compared with `similar`'s Myers, and drawn with
# the runs that differ in inverse video; the runs of either side, read in
# order, are that side's line, whatever the comparison found.
law emphasis_keeps_was:
  for +was: String
  for +now: String
  for -w: List<&2, Main.Piece>
  for -n: List<&2, Main.Piece>
  for e: {Main.apart(was, now) == Some{Main.Marked{w, n}} : Maybe<&2, Main.Marked>}
  {Main.pieces.text(w) == was : String}

law emphasis_keeps_now:
  for +was: String
  for +now: String
  for -w: List<&2, Main.Piece>
  for -n: List<&2, Main.Piece>
  for e: {Main.apart(was, now) == Some{Main.Marked{w, n}} : Maybe<&2, Main.Marked>}
  {Main.pieces.text(n) == now : String}

# And each mark falls on its own line. A run of removals replaced one for
# one by as many arrivals pairs each removal with the arrival at the same
# place in its run; every mark emphasis computes, over any lines, draws runs
# that read as the line it is drawn on, and only a removal or an arrival
# has one.
law emphasis_marks_its_own_line:
  for +ns: List<&2, Main.Numbered>
  for paint: Bool
  {Main.marks.fit(ns, Main.emph(ns, paint)) == True{} : Bool}

# The folder's walk takes nothing a rule in `skipped/` skips. Reading one
# directory's listing, a line an entry as the host hands it over, adds a
# file or a link only where no rule skips its path, and a directory to walk
# next only where no rule skips it whole; `walk` reads each listing onto
# what the last left, from nothing, so no file it returns is skipped.
law listing_skips_nothing:
  for +ls: List<&2, String>
  for +prefix: String
  for +rules: List<&2, Folder.Scope>
  for +l: Folder.Listing
  for h: {Folder.listing.ok(rules, l) == True{} : Bool}
  {Folder.listing.ok(rules, Folder.listing.go(ls, prefix, rules, l)) == True{} : Bool}

# `replay` keeps a refusal. Once a document in the chain is refused, what
# follows it — another operation document, or a payload that would start a
# file afresh — leaves that refusal as it was: a chain with a document that
# does not apply makes no file.
law replay_keeps_a_refusal:
  for ds: List<&2, Store.Doc>
  for +e: String
  {Main.replay.go(ds, Fail{e}) == Fail{e} : Result<&2, &2, String, List<&2, Ops.Item>>}

# What `opdiff` prints replays: the document it finds between two files,
# applied to the first as `replay` applies a document, makes the second.
law opdiff_replays_to_the_child:
  for +parent: String
  for +child: String
  for +doc: Ops.Doc
  for e: {Ops.diff(Ops.from_text(parent), Ops.from_text(child)) == Some{doc} : Maybe<&2, Ops.Doc>}
  {Main.replay.step(Done{Ops.from_text(parent)}, Done{doc}) == Done{Ops.from_text(child)} : Result<&2, &2, String, List<&2, Ops.Item>>}

# `status` reads its words as they say: the word after a flag is its
# value, the last `--onto` is where the folder is compared from, and every
# `--merge` names one more revision joined, in the order given.
law status_reads_its_words:
  for +args: List<&2, String>
  for +cmd: Main.StatusCmd
  for e: {Main.status.args.r(args) == Done{cmd} : Result<&2, &2, Main.Refused, Main.StatusCmd>}
  {cmd == Main.StatusCmd{Main.sargs.onto(args, None{}, Main.sword(args)), Main.sargs.merges(args, Main.sword(args))} : Main.StatusCmd}

# Every revision `status` joins is one the store holds: what `--onto` and
# each `--merge` resolve to, and the head where it is taken — neither named
# twice, sorted, and each once.
law status_joins_held_revisions:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for +onto: Maybe<&2, String>
  for +ms: List<&2, String>
  for +ps: List<&2, String>
  for e: {Main.status.parents.r(fs, bs, onto, ms) == Done{ps} : Result<&2, &2, Main.Refused, List<&2, String>>}
  {Main.all_held(Main.ids(fs), ps) == True{} : Bool}

# `status` refuses no path a rule skips: a rule is how a person silences
# one. Each listing line is refused only once the rules have let its path
# through, and a refusal names the path that was asked about, so reading a
# directory's listing onto refusals that name no skipped path leaves none.
law walk_refuses_nothing_skipped:
  for +ls: List<&2, String>
  for +prefix: String
  for +rules: List<&2, Folder.Scope>
  for after: Bool
  for +acc: List<&2, T.Split>
  for h: {Folder.refused_kept(rules, acc) == True{} : Bool}
  {Folder.refused_kept(rules, Folder.refusals.go(ls, prefix, rules, after, acc)) == True{} : Bool}

# `status` says a file is arriving once. Whatever the survey observed, a
# line of its report other than `added` or `dropped` names no path being
# added: an arrival carries its content, mode and target in with it.
law status_says_an_arrival_once:
  for +os: List<&2, Sv.Obs>
  for +links: List<&2, String>
  {Sv.arrives_once.list(Sv.added(os), Sv.facts(os, links)) == True{} : Bool}

# Every target names a revision the store holds. A bookmark, `head`, a
# digest prefix or a change prefix: whichever a spelling is read as, the
# revision it resolves to is one of the store's — through the history's
# heads and changes too, since that history holds only the store's
# revisions.
law target_is_held:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for +spelling: String
  for +id: String
  for e: {Main.resolve(fs, bs, spelling) == Done{id} : Result<&2, &2, String, String>}
  {Rev.member(Main.ids(fs), id) == True{} : Bool}

# `log` lists only what every filter admits. Whatever it is handed and
# whatever the limit, each revision it lists has the author and message
# asked for, falls between `--since` and `--until`, and touches the file
# `--path` follows.
law log_lists_what_it_asks:
  for +fl: Main.Filter
  for fs: List<&2, Main.Full>
  for limit: Maybe<&2, Nat>
  {Main.all_kept(fl, Main.limited(Main.kept(fl, fs), limit)) == True{} : Bool}

# A file argument names a file the revision holds: a path, `path:` and a
# path, `file:` and a file bookmark, or `file:` and an identifier's prefix,
# whichever an argument is read as, the file it resolves to is in the tree.
law file_is_held:
  for +id: String
  for +bs: List<&2, Bm.Bookmark>
  for +path: String
  for +t: Tree.Tree()
  for +f: String
  for e: {Main.file_in.r(id, bs, path, t) == Done{f} : Result<&2, &2, Main.Refused, String>}
  {Tree.holds(t, f) == True{} : Bool}

# What `diff` and `blame` lay out is both sides. A comparison is laid over
# the parent line by line, walking the document's operations as the cursor
# does: the lines that are context or removals are the parent, whatever the
# document says, and where the document applies, the lines that are context
# or arrivals are the child.
law laid_keeps_parent:
  for +parent: List<&2, Ops.Item>
  for doc: Ops.Doc
  {Main.laid.old(Main.laid(parent, doc)) == parent : List<&2, Ops.Item>}

law laid_reads_child:
  for +parent: List<&2, Ops.Item>
  for +doc: Ops.Doc
  for +child: List<&2, Ops.Item>
  for e: {Ops.apply(parent, doc) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}
  {Main.laid.new(Main.laid(parent, doc)) == child : List<&2, Ops.Item>}

# What `diff` prints, `patch` reads back. The comparison is grouped into
# hunks — each run of lines within three of a change, a line counted on
# each side it is on — and read as `patch` reads a unified diff, without
# fuzz: each hunk found at the line its header names on both sides, the
# parent's lines before it copied, its context and removals read off the
# parent there, its context and arrivals written, and its header's counts
# the lines each side holds. Whatever the document, its hunks take the
# parent to the child.
law diff_hunks_apply:
  for +parent: List<&2, Ops.Item>
  for +doc: Ops.Doc
  for +child: List<&2, Ops.Item>
  for e: {Ops.apply(parent, doc) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}
  {Main.patch(parent, Main.hunks.made(Main.laid(parent, doc))) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}

# `blame <path>` prints the folder's file. Its rows are laid over the lines
# history holds, a line that stayed keeping its author and one that arrived
# the folder's own; whatever the folder holds, the lines of the rows are
# the lines of its text, each once and in order.
law blame_shows_the_folder:
  for +rows: List<&2, Main.Row>
  for +text: String
  {Main.rows.items(Main.wc.overlay(rows, Ops.from_text(text))) == Ops.from_text(text) : List<&2, Ops.Item>}

# Every rule a file in `skipped/` states is well formed: a path with a
# value, or a name that is one component, not empty and not only `*`.
law rules_are_well_formed:
  for +text: String
  {Folder.stated.ok(Folder.rule_in(text)) == True{} : Bool}

# A bookmark file reads back as the bookmark it was written for: the target
# line and, where the name stays out of an export, `private` below it —
# wherever the identifier is spelled as its kind is.
law bookmark_reads_back:
  for +t: Bm.Target
  for p: Bool
  for +h: {Bm.target_ok(t) == True{} : Bool}
  {Bm.parse(Bm.write(Bm.Stated{t, p})) == Done{Bm.Stated{t, p}} : Result<&2, &2, String, Bm.Stated>}

# An abbreviated digest names one revision: it is a prefix of the digest,
# and no other digest of the same length among those it was abbreviated
# against starts with it, however they share their prefixes.
law abbreviation_is_a_prefix:
  for +id: String
  for +among: List<&2, String>
  {String.starts_with(id, Main.abbreviate(id, among)) == True{} : Bool}

law abbreviation_names_one:
  for +id: String
  for +among: List<&2, String>
  for +other: String
  for m: {Rev.member(among, other) == True{} : Bool}
  for +ne: {String.eq(other, id) == False{} : Bool}
  for len: {String.length(other) == String.length(id) : Nat}
  {String.starts_with(other, Main.abbreviate(id, among)) == False{} : Bool}

# `blame <target> <path>` attributes the file the walk reads. Its rows are
# what the walk of the target's ancestry leaves standing, each with the
# revision that wrote it; read without their authors, they are the file
# `walked` reads — the one every causal order of the graph reads, by
# `walked_file_every_order`.
law blame_reads_the_walk:
  for +oldest: List<&2, Main.Full>
  for +ds: List<&2, Store.Doc>
  for +id: String
  for +file: String
  for +rs: List<&2, Main.Row>
  for e: {Main.blame.rows.r(oldest, ds, id, file) == Done{rs} : Result<&2, &2, Main.Refused, List<&2, Main.Row>>}
  {Main.walked(oldest, ds, id, file) == Done{Main.rows.items(rs)} : Result<&2, &2, String, List<&2, Ops.Item>>}

# `blame` numbers each line as the file numbers it, and prints the span
# asked and nothing else. Of the file's lines, each with its number
# counting from one, it prints every one without `--lines`, and with a span
# exactly those whose number falls in it — wherever the span begins, since
# one that begins past the end is refused.
law blame_numbers_its_lines:
  for +rs: List<&2, Main.Row>
  for +span: Maybe<&2, Main.Wanted>
  for +bl: List<&2, Main.Blamed>
  for e: {Main.blame.span.r(rs, span) == Done{bl} : Result<&2, &2, Main.Refused, List<&2, Main.Blamed>>}
  {Main.blamed.lines(bl) == Main.lines.asked(Main.lines.numbered(Main.rows.items(rs), 1n), span) : List<&2, Main.NLine>}

# And what `blame` prints of them is one line for each line of the span, in
# order, ending with the line as `Ops.shown` spells it — whatever the
# columns before it say — and after a line without a newline, the marker
# saying so.
law blame_prints_each_line:
  for +fs: List<&2, Main.Full>
  for +cs: List<&2, String>
  for +rs: List<&2, Main.Row>
  for +span: Maybe<&2, Main.Wanted>
  for +out: List<&2, String>
  for e: {Main.blame.limited.r(fs, cs, rs, span) == Done{out} : Result<&2, &2, Main.Refused, List<&2, String>>}
  {Main.ends_all(out, Main.blame.ends(Main.lines.items(Main.lines.asked(Main.lines.numbered(Main.rows.items(rs), 1n), span)))) == True{} : Bool}

# `blame <path>` compares the folder with a revision the store holds — the
# one head, or none in an empty store — and the file the argument names is
# one that revision's tree holds, or the tree holds nothing at the path and
# every line is the folder's own. Whether it is spelled as a path, `path:`
# and a path, or `file:` and an identifier or a bookmark.
law blame_reads_the_position:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for +sp: String
  for +p: Main.Position
  for e: {Main.wcf.position.r(fs, bs, sp) == Done{p} : Result<&2, &2, Main.Refused, Main.Position>}
  {Main.position.ok(fs, p) == True{} : Bool}

# `blame <target> <path>` reads a revision the store holds, and a file its
# tree holds that has lines: not a file of bytes, and not a link.
law blame_reads_a_held_file:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for +target: String
  for +sp: String
  for +p: Main.Picked
  for e: {Main.blame.picked.r(fs, bs, target, sp) == Done{p} : Result<&2, &2, Main.Refused, Main.Picked>}
  {Main.picked.ok(fs, p) == True{} : Bool}

# What `blame <target> <path>` prints is the file the walk of the target's
# ancestry reads: one line for each line of the span, in order, ending with
# it.
law blame_prints_the_walk:
  for +fs: List<&2, Main.Full>
  for +all: List<&2, Store.Doc>
  for +id: String
  for +file: String
  for +span: Maybe<&2, Main.Wanted>
  for +out: List<&2, String>
  for e: {Main.blame.recorded.r(fs, all, id, file, span) == Done{out} : Result<&2, &2, Main.Refused, List<&2, String>>}
  for +w: List<&2, Ops.Item>
  for +ew: {Main.walked(Main.oldest_of(fs, Some{id}), all, id, file) == Done{w} : Result<&2, &2, String, List<&2, Ops.Item>>}
  {Main.ends_all(out, Main.blame.ends(Main.lines.items(Main.lines.asked(Main.lines.numbered(w, 1n), span)))) == True{} : Bool}

# What `blame <path>` prints is the folder's text: a file with lines, by
# the kind the position gave it or by the recorder's reckoning, and one
# line for each line of the span, in order, ending with it.
law blame_prints_the_folder:
  for +fs: List<&2, Main.Full>
  for +path: String
  for +k: Maybe<&2, Tree.FileKind>
  for +bs: List<&2, U32>
  for +rows: List<&2, Main.Row>
  for +span: Maybe<&2, Main.Wanted>
  for +out: List<&2, String>
  for e: {Main.blame.folder.r(fs, path, k, bs, rows, span) == Done{out} : Result<&2, &2, Main.Refused, List<&2, String>>}
  {Bool.and(Main.folder.has_lines(k, bs), Main.ends_all(out, Main.blame.ends(Main.lines.items(Main.lines.asked(Main.lines.numbered(Ops.from_text(Folder.lossy(bs)), 1n), span))))) == True{} : Bool}

# `blame` reads its arguments as their plain reading says: each `--lines`
# takes the word after it, the last counting, and the span is what that
# word spells; every other word is the target or the path, in order.
law blame_reads_its_words:
  for +bs: List<&2, Bm.Bookmark>
  for +args: List<&2, String>
  for +b: Main.Blame
  for e: {Main.blame.args.r(bs, args) == Done{b} : Result<&2, &2, Main.Refused, Main.Blame>}
  {Main.bargs.said(args) == Main.blame.said(b) : Main.BSaid}

# `blame <path>` reads a file the folder holds at the path rather than a
# link, and goes on with the kind the position gives it, one with lines.
law blame_reads_a_folder_file:
  for +path: String
  for +t: Tree.Tree()
  for +file: Maybe<&2, String>
  for +found: List<&2, Folder.Found>
  for +k: Maybe<&2, Tree.FileKind>
  for e: {Main.wcf.checked.r(path, t, file, found) == Done{k} : Result<&2, &2, Main.Refused, Maybe<&2, Tree.FileKind>>}
  {Main.checked.ok(found, path, t, file, k) == True{} : Bool}

# `diff` reads its arguments as their plain reading says: `--onto` and
# `--color` take the word after them and `--color=` spells a colour in the
# word itself, the last of each counting; every other word is the target
# or the path, in order.
law diff_reads_its_words:
  for +bs: List<&2, Bm.Bookmark>
  for +args: List<&2, String>
  for +cmd: Main.DiffCmd
  for e: {Main.diff.args.r(bs, args) == Done{cmd} : Result<&2, &2, Main.Refused, Main.DiffCmd>}
  {Main.dargs.said(args) == Main.diff.said(cmd) : Main.DSaid}

# `diff <target>` compares the target with what `--onto` names, a revision
# the store holds, or else with its one parent — nothing for a root; a
# merge, having several, is refused.
law diff_compares_with_the_parent:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for right: Main.Full
  for onto: Maybe<&2, String>
  for +l: Maybe<&2, String>
  for e: {Main.diff.left.r(fs, bs, right, onto) == Done{l} : Result<&2, &2, Main.Refused, Maybe<&2, String>>}
  {Main.diff.left.ok(fs, right, onto, l) == True{} : Bool}

# `diff` over the folder compares it with what `--onto` names or the head:
# a revision the store holds, or none in an empty store.
law diff_folder_compares_with_a_held_revision:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for onto: Maybe<&2, String>
  for +l: Maybe<&2, String>
  for e: {Main.wc.left.r(fs, bs, onto) == Done{l} : Result<&2, &2, Main.Refused, Maybe<&2, String>>}
  {Main.left.ok(fs, l) == True{} : Bool}

# A file `diff <target>` is limited to is one the target's tree holds, and
# one `diff` over the folder is limited to, one the position's tree holds.
law diff_limits_to_a_held_file:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for +right: String
  for only: Maybe<&2, String>
  for +lim: Main.Limit
  for e: {Main.diff.limit.r(fs, bs, right, only) == Done{lim} : Result<&2, &2, Main.Refused, Main.Limit>}
  {Main.limit.held(fs, lim, Some{right}) == True{} : Bool}

law diff_folder_limits_to_a_held_file:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for +left: Maybe<&2, String>
  for only: Maybe<&2, String>
  for +lim: Main.Limit
  for e: {Main.wc.limit.r(fs, bs, left, only) == Done{lim} : Result<&2, &2, Main.Refused, Main.Limit>}
  {Main.limit.held(fs, lim, left) == True{} : Bool}

# `diff` compares each file with itself. It sorts each side by file with
# `List.sort` — which returns every entry, those under each file in the
# order they came, and each no smaller than the one before — and walks the
# two together: for any file, the pairs it goes on with under that file are
# the entries each side holds under it, paired in order as far as either
# goes. So where each side holds a file once, it is compared once, with each
# side's entry for it, and a file one side lacks is paired with nothing.
law diff_pairs_each_file:
  for +xs: Tree.Tree()
  for +ys: Tree.Tree()
  for +f: String
  {Main.both.at(f, Main.both(xs, ys)) == Main.both.zip(f, Main.entries.at(f, xs), Main.entries.at(f, ys)) : List<&2, Main.Both>}

# `diff` shows only files whose two sides differ — in path, mode, link
# target, presence or content — and under a path limit only a file at
# that path on one side or the other.
law diff_shows_what_differs:
  for +sd: Main.Sides
  for +l: Main.Limit
  for files: List<&2, Main.Both>
  for +cs: List<&2, Main.Compared>
  for e: {Main.compare(sd, l, files) == Done{cs} : Result<&2, &2, String, List<&2, Main.Compared>>}
  {Main.all.shown(l, cs) == True{} : Bool}

# `diff` over the folder goes on only with paths the limit wants, and
# shows only those whose two sides — the position's and the folder's —
# differ.
law diff_folder_keeps_what_the_limit_wants:
  for +t: Tree.Tree()
  for +found: List<&2, Folder.Found>
  for +l: Main.Limit
  {Main.all.wanted(l, Main.heres(t, found, l)) == True{} : Bool}

law diff_folder_shows_what_differs:
  for +t: Tree.Tree()
  for +older: List<&2, Main.Full>
  for +ds: List<&2, Store.Doc>
  for +left: String
  for +reads: Map<&2, List<&2, U32>>
  for ps: List<&2, Main.Planned>
  for +cs: List<&2, Main.Compared>
  for e: {Main.wc.compare(t, older, ds, left, reads, ps) == Done{cs} : Result<&2, &2, String, List<&2, Main.Compared>>}
  {Main.all.shown(Main.Limit.None{}, cs) == True{} : Bool}

# Colour changes no character of what `diff` prints. With colour, each line
# is drawn in its colour, and where two lines were replaced one for one the
# runs that differ are marked inside it; read without the colour — as a
# line is printed where there is none — the lines are the very lines `diff`
# prints without colour, one for one, whatever the files compared.
law diff_colour_changes_no_character:
  for +cs: List<&2, Main.Compared>
  {T.map(~Main.Painted, ~String, ~(p => Main.painted(False{}, p)), Main.diff.rendered(True{}, cs)) == T.map(~Main.Painted, ~String, ~(p => Main.painted(False{}, p)), Main.diff.rendered(False{}, cs)) : List<&2, String>}

# `diff` over the folder believes the digest a statement gives a file of
# lines. It replays at the position exactly the files of lines whose digest
# no statement settles — not one the folder holds, as a regular file, with
# the digest the file's nearest statement leaves — and never a file of
# bytes or a link.
law diff_folder_replays_what_is_unsettled:
  for +dg: Map<&2, String>
  for +os: Map<&2, T.Split>
  for +eds: List<&2, Store.Doc>
  for +hs: List<&2, Main.Here>
  {Main.planned.replayed(Main.plans(dg, os, eds, hs)) == Main.unsettled.files(dg, os, eds, hs) : List<&2, String>}

# And it reads from the folder exactly the regular files nothing at the
# position settles: a path the position does not hold, or holds as a file
# of lines whose stated digest is not the folder's — never one the position
# holds as a file of bytes or a link, whose digest or target is compared
# instead.
law diff_folder_reads_what_is_unsettled:
  for +dg: Map<&2, String>
  for +os: Map<&2, T.Split>
  for +eds: List<&2, Store.Doc>
  for +hs: List<&2, Main.Here>
  {Main.planned.read(Main.plans(dg, os, eds, hs)) == Main.unsettled.paths(dg, os, eds, hs) : List<&2, String>}

# `diff` gives a file of bytes the size the host stated for its payload, and
# nothing else. Sizing what it compares changes no side but one whose size
# was unknown, which keeps its digest and has a size only where the host's
# line for the bytes it found names that very digest — not where those
# bytes hash to another.
law diff_sizes_what_the_host_stated:
  for +found: List<&2, T.Split>
  for +stats: List<&2, String>
  for +cs: List<&2, Main.Compared>
  {Main.sizes.told(stats, cs, Main.sized(Main.sizes.read(found, stats), cs)) == True{} : Bool}

# `diff <target>` asks the store for everything it replays. For every file
# it compares whose content it reads — one side lacks it, or the two sides
# were stated by different revisions — every document a revision states for
# the file is among the documents it fetches.
law diff_fetches_what_it_replays:
  for +fs: List<&2, Main.Full>
  for +ws: Map<&2, List<&2, String>>
  for +ns: Map<&2, List<&2, String>>
  for +files: List<&2, Main.Both>
  {FetchL.fetched.each(fs, ws, ns, Main.compare.wanted_docs(fs, ws, ns, files), files) == True{} : Bool}

# And over the folder: every document a revision states for a file of lines
# no statement settles is among those `diff` fetches.
law diff_folder_fetches_what_it_replays:
  for +fs: List<&2, Main.Full>
  for +dg: Map<&2, String>
  for +os: Map<&2, T.Split>
  for +eds: List<&2, Store.Doc>
  for +hs: List<&2, Main.Here>
  {FetchL.fetched.files(fs, Main.wanted_all(fs, Main.planned.replayed(Main.plans(dg, os, eds, hs))), Main.unsettled.files(dg, os, eds, hs)) == True{} : Bool}

# And before any of it, `diff` over the folder asks for the `edit`
# document of every file of lines its folder holds a regular file for,
# where the file's nearest statement is an `edit`: the result that document
# states is the digest that can settle the file.
law diff_folder_fetches_the_edits_it_believes:
  for +os: Map<&2, T.Split>
  for +hs: List<&2, Main.Here>
  {FetchL.edits.each(os, Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), Main.edits_of(os, hs))), hs) == True{} : Bool}

# `diff` asks the host about the payload of every file of bytes it shows,
# each once, so that each can be shown with its size.
law diff_asks_every_payload_it_shows:
  for +cs: List<&2, Main.Compared>
  {FetchL.payloads.each(Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), Main.payloads_of(cs))), cs) == True{} : Bool}

# And it asks the stat of a payload only at the path the host located that
# payload at — never of one the host could not find, which it answers `-`
# for — so that each size it then believes is looked for where it is.
law diff_stats_where_each_payload_was_found:
  for +root: String
  for +ds: List<&2, String>
  for +at: List<&2, String>
  {FetchL.located.each(ds, at, Main.sizes.of(root, ds, at)) == True{} : Bool}

# What a resolution keeps is fetched too. After the documents a reading
# command asks for, it asks for every document a resolution among them
# keeps lines of, which assembling the resolution reads.
law reading_fetches_what_resolutions_keep:
  for +ds: List<&2, Store.Doc>
  {FetchL.kept.each(ds, Main.kept_digests(ds)) == True{} : Bool}

# The digest a statement gives a file is read along the first-parent line
# back from the folder's position, the nearest revision on it to state the
# file being the one believed. That line is what `chain` walks: it begins
# at the revision named, and each revision after is the first parent of the
# one before — every one a revision the store holds.
law chain_follows_first_parents:
  for +fs: List<&2, Main.Full>
  for +id: String
  {Main.first_parents(fs, Main.chain(fs, Some{id}), Some{id}) == True{} : Bool}

# Every revision a command reads is one a document of `revisions/` spells:
# filed there under the digest the revision is known by, and what
# `Rev.write` writes, byte for byte, from what the revision says — or,
# where a path it states is not in normal form C, which the Rust tool
# refuses only once something reads the whole of it, the refusal every
# such reader meets, in place of its facts. Reading a store's revisions
# takes nothing that is not such a document, and nothing of one is lost or
# added in the reading.
law revisions_read_are_their_documents:
  for +root: String
  for +ds: List<&2, Store.Doc>
  {FullsL.all_filed(root, ds, Main.fulls(root, ds)) == True{} : Bool}

# `log` lists only what its span names: with a target, revisions the
# target reaches; with `a..b`, revisions `b` reaches and `a` does not —
# every one a revision the store holds.
law log_lists_its_span:
  for +fs: List<&2, Main.Full>
  for +sp: Main.Span
  {Main.span.all_in(fs, sp, Main.span.shown(fs, sp)) == True{} : Bool}

# `log` reads its arguments as their plain reading says: the word after a
# flag that takes a value is that flag's value, the last counting, and
# `--limit`, `--since` and `--until` are read as a count and as bounds;
# `--fields` is asked for if it is there; the other word is the target.
law log_reads_its_words:
  for +args: List<&2, String>
  for +a: Main.Asked
  for e: {Main.asked(args) == Done{a} : Result<&2, &2, String, Main.Asked>}
  {Main.asked.of(Main.largs.raw(args)) == Done{a} : Result<&2, &2, String, Main.Asked>}

# `check` reports each payload with the digest asked for it. The host is
# asked for one digest per payload, in the order the walk found them; given
# one for each, every payload is paired with its own, in order, and no
# operation document takes one.
law check_pairs_each_payload:
  for fs: List<&2, Check.OpFiled>
  for stats: List<&2, String>
  for h: {List.length(&2, String, stats) == List.length(&2, String, Check.payload.paths(fs)) : Nat}
  {Check.payload.pairs(Check.attach(fs, stats)) == Check.zip.pairs(Check.payload.paths(fs), stats) : List<&2, T.Split>}

# `cat <target> <path>` reads a revision the store holds, and a file its
# tree holds that is not a link.
law cat_reads_a_held_file:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for +target: String
  for +path: String
  for +p: Main.Picked
  for e: {Main.cat.picked.r(fs, bs, target, path) == Done{p} : Result<&2, &2, Main.Refused, Main.Picked>}
  {Main.cat.ok(fs, p) == True{} : Bool}

# `show <target> <path>` names a file the target's tree holds, and what
# `show` prints is a document the store holds under the digest named — the
# revision's own, or the one it states for the file. Where a forgetting
# destroyed the one it states (decisions 0014, 0050, 0066), what it prints
# is what stands in for it: documents the store holds, each whole and in
# the store's order, each saying in its first header that it `forgets` the
# digest named — never a document of its own making.
law show_names_a_held_file:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for +id: String
  for +p: String
  for +file: String
  for e: {Main.show.file.r(fs, bs, id, p) == Done{file} : Result<&2, &2, Main.Refused, String>}
  {Main.tree.holds.r(Main.tree.r(fs, id), file) == True{} : Bool}

law show_prints_a_held_document:
  for +id: String
  for +d: String
  for +ds: List<&2, Store.Doc>
  for +text: String
  for e: {Main.show.doc.r(id, d, Main.doc_by_id(ds, d)) == Done{text} : Result<&2, &2, Main.Refused, String>}
  {Main.doc.holds(ds, d, text) == True{} : Bool}

law show_prints_what_the_revision_states:
  for +id: String
  for +file: String
  for +ds: List<&2, Store.Doc>
  for s: Main.Said
  for +text: String
  for e: {Main.show.said.r(id, file, ds, s) == Done{text} : Result<&2, &2, Main.Refused, String>}
  {Bool.or(Main.doc.holds(ds, Main.said.digest(s), text), Stand.made_of(ds, Main.said.digest(s), text)) == True{} : Bool}

# `name` writes where its name puts it, under `names/`: a name it takes is
# never absolute and never climbs out with `..`, since a bookmark whose
# name did would be a name choosing where its file goes.
law name_stays_in_names:
  for +n: String
  for e: {Main.name.checked.r(n) == Done{Unit{}} : Result<&2, &2, Main.Refused, Unit>}
  {Main.escapes(n) == False{} : Bool}

# A forgetting document states what it stands in for with only text
# destroyed (decisions 0014 and 0050): every operation at its position with
# its count and each item's terminator, every `keep` as it was and each
# `insert` at its own length. So `standin.bend`'s union rule, which sets
# aside a stand-in whose shape disagrees, folds in every one `forget`
# writes.
law forgetting_keeps_shape:
  for ops: List<&2, Ops.Op>
  for +ps: List<&2, Fg.FgPick>
  for +t: String
  for +i: Nat
  {Stand.ops.shape(ops, Fg.forget.ops(ops, ps, t, i)) == True{} : Bool}

law forgetting_a_resolution_keeps_shape:
  for pieces: List<&2, Res.Piece>
  for +ps: List<&2, Fg.FgPick>
  for +t: String
  for +i: Nat
  {Stand.pieces.shape(pieces, Fg.forget.pieces(pieces, ps, t, i)) == True{} : Bool}

# Every document `forget --lines` writes a stand-in for, and so every
# digest whose bytes it destroys, is one a revision states for that file —
# its `edit`'s, or the payload its `text` states: forgetting lines of one
# file rewrites no other file's documents, however far the walk goes to
# find a delete quoting them or a resolution's copy.
law forget_rewrites_only_the_files_documents:
  for +fs: List<&2, Main.Full>
  for +ds: List<&2, Store.Doc>
  for +id: String
  for +file: String
  for +first: String
  for +last: String
  for +ts: List<&2, String>
  for +ws: List<&2, Fg.FgWrite>
  for +a: Nat
  for +n: Nat
  for e: {Fg.lines.plan.r(fs, ds, id, file, first, last) == Done{Fg.Fg.Plan{ts, ws, a, n}} : Result<&2, &2, Main.Refused, Fg.FgPlan>}
  {Main.all_held(Fg.named.docs(Fg.named(fs, file)), ts) == True{} : Bool}

# Forgetting a file of bytes forgets the payload its tree holds for it at
# the revision named, or nothing: another version of the file is another
# payload (decision 0066), counted and left alone.
law forget_whole_takes_one_payload:
  for +file: String
  for +payload: Maybe<&2, String>
  for +files: List<&2, Fg.FgFiled>
  for +stood: List<&2, Store.Doc>
  for +n: Nat
  for +ts: List<&2, String>
  for +ws: List<&2, Fg.FgWrite>
  for +a: Nat
  for +m: Nat
  for e: {Fg.whole.plan.r(file, payload, files, stood, n) == Done{Fg.Fg.Plan{ts, ws, a, m}} : Result<&2, &2, Main.Refused, Fg.FgPlan>}
  {Main.all_held(Fg.payload.list(payload), ts) == True{} : Bool}

# And the versions it says the file holds "elsewhere in its history, each
# forgotten on its own" are other payloads than the one it forgets: the
# count never includes the content it has just destroyed.
law forget_counts_only_other_versions:
  for +fs: List<&2, Main.Full>
  for +file: String
  for +t: String
  {Rev.member(Fg.others(fs, file, t), t) == False{} : Bool}

# `forget` destroys a file only where its bytes are one of the digests it
# forgets: found by content, as everything in a store is, and nothing else
# under `operations/` touched.
law forget_destroys_only_what_it_forgets:
  for +fs: List<&2, Fg.FgFiled>
  for +ts: List<&2, String>
  for +p: String
  for e: {Rev.member(Fg.destroyed(fs, ts), p) == True{} : Bool}
  {Rev.member(Fg.holding(fs, ts), p) == True{} : Bool}

# `forget` reads its arguments as their plain reading says: every flag it
# knows set aside, and with `--lines` the word after it, whatever that word
# is; what is left, in order, is the target and the path.
law forget_reads_its_words:
  for +ws: List<&2, String>
  for +t: String
  for +p: String
  for +sp: Maybe<&2, Fg.FgSpan>
  for +d: Bool
  for +f: Bool
  for e: {Fg.asked.r(ws) == Done{Fg.Fg.Asked{t, p, sp, d, f}} : Result<&2, &2, Main.Refused, Fg.FgAsked>}
  {Fg.plain(ws, False{}) == [t, p] : List<&2, String>}

# What `forget` removes from `cache/` is an entry named by a digest — a
# copy of some file's content, which may be a copy of what went — and
# nothing else there: the note `init` writes and the catalogues survive.
law forget_clears_only_copies:
  for ps: List<&2, String>
  for +p: String
  for e: {Rev.member(Fg.cached(ps), p) == True{} : Bool}
  {T.is_digest(String.drop(p, 6n)) == True{} : Bool}

# Decision 0014: replay does not consult payload. A document whose every
# item is the one written or that item forgotten — a stand-in, which states
# no result — applied to a file whose every line is the original parent's
# or that line forgotten, makes a file wherever the original makes one, and
# each of its lines is the original's line or that line forgotten. A
# forgotten item agrees with whatever its terminator allows, and nothing
# else the walk does reads text.
law standin_replays_like_what_it_stands_in_for:
  for +st1: List<&2, Ops.Item>
  for +st2: List<&2, Ops.Item>
  for f: Maybe<&2, String>
  for +r: Maybe<&2, String>
  for +ops1: List<&2, Ops.Op>
  for f2: Maybe<&2, String>
  for +ops2: List<&2, Ops.Op>
  for +hs: {Stand.items.like(st1, st2) == True{} : Bool}
  for +hops: {Stand.ops.like(ops1, ops2) == True{} : Bool}
  {Stand.result.like(Ops.apply(st1, Ops.Doc{f, r, ops1}), Ops.apply(st2, Ops.Doc{f2, None{}, ops2})) == True{} : Bool}

# So a file's history replayed through stand-ins — any of its documents
# forgotten, in any part — reads the forgotten lines as forgotten items and
# every other line as it was, wherever the history replays.
law chain_replays_like_through_standins:
  for ds1: List<&2, List<&2, Ops.Op>>
  for ds2: List<&2, List<&2, Ops.Op>>
  for r1: Result<&2, &2, String, List<&2, Ops.Item>>
  for r2: Result<&2, &2, String, List<&2, Ops.Item>>
  for +hd: {Stand.docs.like(ds1, ds2) == True{} : Bool}
  for +hr: {Stand.result.like(r1, r2) == True{} : Bool}
  {Stand.result.like(Merge.replay(ds1, r1), Merge.replay(ds2, r2)) == True{} : Bool}

# And what `forget` writes is such a stand-in: the document it stands in
# for, with the text of the items picked destroyed and nothing else.
law forgetting_destroys_only_text:
  for ops: List<&2, Ops.Op>
  for +ps: List<&2, Fg.FgPick>
  for +t: String
  for +i: Nat
  {Stand.ops.like(ops, Fg.forget.ops(ops, ps, t, i)) == True{} : Bool}

# Decision 0014 with the original still held — a sync brought it back, or
# a stand-in arrived from a replica that complied: whatever documents say
# they forget it, what a reader reads is the held document with each item
# as it was or forgotten, its terminator kept, every operation where it
# was. A stand-in redacts; it never rewrites.
law standins_beside_only_forget:
  for ds: List<&2, Ops.Doc>
  for +ops: List<&2, Ops.Op>
  {Stand.ops.like(ops, Stand.ops.folded(ds, ops)) == True{} : Bool}

# And it redacts all it says: every item a stand-in of the held shape
# forgets is forgotten in what is read, whatever stand-ins are folded in
# after it, so a stale replica's narrower redaction brings nothing back.
law standins_beside_forget_all_they_say:
  for f: Maybe<&2, String>
  for r: Maybe<&2, String>
  for +stated: List<&2, Ops.Op>
  for rest: List<&2, Ops.Doc>
  for +held: List<&2, Ops.Op>
  for +e: {Stand.ops.shape(held, stated) == True{} : Bool}
  {Stand.ops.covers(stated, Stand.ops.folded(Ops.Doc{f, r, stated} <> rest, held)) == True{} : Bool}

# Replicas redact independently, and the order their stand-ins arrive in
# changes nothing: two neighbours swapped fold to the same document, so
# every order does — and so, with the law above, a stand-in anywhere among
# them has all it forgets forgotten.
law standins_fold_in_any_order:
  for a: Ops.Doc
  for b: Ops.Doc
  for rest: List<&2, Ops.Doc>
  for +held: List<&2, Ops.Op>
  {Stand.ops.folded(a <> b <> rest, held) == Stand.ops.folded(b <> a <> rest, held) : List<&2, Ops.Op>}

# `name` reads its words as their plain reading says: a flag counts
# wherever it stands, the last of `--revision` and `--change` and the last
# of `--private` and `--shared` deciding, `--delete` and `--fields` asked
# for if they are there; the flags shaping a target are kept as typed, in
# order, for `--delete` to refuse; and every other word is the bookmark,
# the target and the path, in order.
law name_reads_its_words:
  for +ws: List<&2, String>
  {Main.name.args(ws, Main.NameCmd{False{}, None{}, False{}, False{}, Nil{}, Nil{}}) == Main.nargs.said(ws) : Main.NameCmd}

# What `name` sets out to do, decided before anything is opened, is what
# its words say. A bookmark is deleted only where `--delete` was said, and
# then it is the one other word, with no flag shaping a target beside it;
# otherwise a bookmark is set, the other words being the bookmark, the
# target and at most one path, in order, with `--revision`, `--private` or
# `--shared` and `--fields` as they were read. A file bookmark is never
# pinned, and the header `--fields` asks for goes out before the store is
# opened only where `--fields` asked for it.
law name_does_what_it_reads:
  for c: Main.NameCmd
  for +p: Main.NamePlan
  for e: {Main.name.plan.r(c) == Done{p} : Result<&2, &2, Main.Refused, Main.NamePlan>}
  {Main.name.plan.meant(c, p) == True{} : Bool}

# The bookmark `name` sets is the one asked for. It has the name given,
# which stays under `names/`; it points at a revision the store holds where
# `--revision` pins it, at a change one of the store's revisions carries
# where a target alone is given, and at a file one of those revisions'
# trees holds where a path is; and it is private as `--private` or
# `--shared` says, or else as the bookmark of that name already was — the
# one `--delete` would find — or shared where there was none.
law name_points_where_asked:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for +n: String
  for +spelling: String
  for +path: Maybe<&2, String>
  for +pin: Bool
  for +axis: Maybe<&2, Bool>
  for +b: Bm.Bookmark
  for e: {Main.name.stated.r(fs, bs, n, spelling, path, pin, axis) == Done{b} : Result<&2, &2, Main.Refused, Bm.Bookmark>}
  {Main.name.points(fs, bs, n, path, pin, axis, b) == True{} : Bool}

# `name --delete` removes the bookmark named: it is refused exactly where
# the store has no bookmark of that name, and the bookmark it says it
# deleted is one the store holds under that name, as it was.
law name_deletes_the_bookmark_named:
  for bs: List<&2, Bm.Bookmark>
  for +n: String
  {Main.name.gone(bs, n, Main.name.present.r(n, Main.found_of(bs, n))) == True{} : Bool}

# Asked for `--fields`, a bookmark set says what it wrote in decision
# 0074's words: `historica-wrote-1` once — before the store is opened where
# the command line cannot yet prove wrong, and after the bookmark is
# written where it can — and then `name` with the bookmark's name.
law name_states_what_it_set:
  for +n: String
  for b: Bm.Bookmark
  for early: Bool
  for shared: Bool
  {List.append(&2, String, Main.name.head(early), Main.name.said.lines(n, b, True{}, early, shared)) == [Main.WROTE(), "name " ++ n] : List<&2, String>}

# `files` lists each file of the tree once, in path order. The entries it
# prints are each no smaller than the one before, by path and then by file
# identifier, and each line it prints ends with the identifier of the entry
# it lists — or says there are none.
law files_lists_in_path_order:
  for +t: Tree.Tree()
  {Bool.and(SortL.sorted(~Tree.Entry, ~(e => Main.files.key(e)), Main.files.listed(t)), Main.ends_all(Main.files.said(t), Main.files.ends(t))) == True{} : Bool}

# And the entries it lists are the tree's: under each path and file, the
# ones the tree holds there, as many and in the order it holds them.
law files_lists_the_tree:
  for +t: Tree.Tree()
  for +k: String
  {SortL.keyed(~Tree.Entry, ~(e => Main.files.key(e)), k, Main.files.listed(t)) == SortL.keyed(~Tree.Entry, ~(e => Main.files.key(e)), k, t) : Tree.Tree()}

# `names` lists every bookmark once, in name order: the store's bookmarks
# are read sorted by name, and `names` prints a line for each, in the
# order read, beginning with its name — or says there are none.
law bookmarks_read_in_name_order:
  for +ps: List<&2, String>
  {SortL.sorted(~Main.Named, ~(n => Main.named.name(n)), Main.bookmarks.order(ps)) == True{} : Bool}

law names_lists_each_bookmark:
  for +fs: List<&2, Main.Full>
  for bs: List<&2, Bm.Bookmark>
  {Main.names.begun(bs, Main.names.said(fs, bs)) == True{} : Bool}

# Where `names` says a revision pin or a change resolves is a revision the
# store holds: an abbreviation of its digest — for a change, of its one
# current revision — or else, in parentheses, why there is none.
law names_resolves_to_held:
  for +fs: List<&2, Main.Full>
  for +here: Maybe<&2, Tree.Tree()>
  for t: Bm.Target
  {Main.names.held(fs, t, Main.names.resolution(Main.history(fs), Main.ids(fs), here, t)) == True{} : Bool}

# `log --fields` names exactly what it lists: its header, and then a line
# for each revision it keeps — those every filter admits, as
# `log_lists_what_it_asks` says, in the order the walk presents them and
# as far as the limit — beginning with that revision's digest, whole.
law log_fields_lists_what_it_keeps:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for +sp: Main.Span
  for +shown: List<&2, Main.Full>
  for +fl: Main.Filter
  for limit: Maybe<&2, Nat>
  {Main.log.fields.ok(Main.log.shown.lines(fs, bs, sp, shown, fl, True{}, limit), Main.limited(Main.kept(fl, Main.presentation(shown)), limit)) == True{} : Bool}

# A log entry counts what its revision did to the file set as the revision
# states it: the files added, moved, dropped and edited are how many `add`,
# `move`, `drop` and `edit` facts it states, each counted once and none set
# aside for the files it added — only modes, links and bytes are.
law log_counts_each_fact:
  for facts: List<&2, Rev.Header>
  for +key: String
  for +added: Set()
  {Main.count_facts(facts, key, added, False{}) == List.length(&2, String, Rev.values_of(facts, key)) : Nat}

# The file `log --path` follows is one the tree holds at the revision the
# path is read at — the far end of the span named, or the one head — so
# what the log then lists is that file's history, whatever it was called.
law log_follows_a_held_file:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for +sp: Main.Span
  for +path: String
  for +at: String
  for +file: String
  for ea: {Main.read_at.r(fs, bs, path, sp) == Done{at} : Result<&2, &2, Main.Refused, String>}
  for e: {Main.followed.r(fs, bs, sp, Some{path}) == Done{Some{file}} : Result<&2, &2, Main.Refused, Maybe<&2, String>>}
  {Main.tree.holds.r(Main.tree.r(fs, at), file) == True{} : Bool}

# `status` says everything its survey of the folder found, in the order
# found, each on a line of its own that names it: each fact on a line
# beginning with its kind and ending with its path, then each path refused
# or claimed on a line beginning `refused` or `claimed` and the path, each
# file the renderer's lines still stand in on one beginning `marked` and
# the path, and each accept on one beginning `accept` and the path and
# ending with it again.
law status_says_what_it_found:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for +ps: List<&2, String>
  for +cs: List<&2, Tree.Contest>
  for sv: Sv.Survey
  {Main.expect.in(Main.status.report(fs, bs, ps, cs, sv), Main.status.expects(sv)) == True{} : Bool}

# Where work is joined, `status` says each contest the tree merge found,
# once and in its order, on a line opening with the file contested — a
# path several files claim is said as `claimed` instead; where one
# revision or none is the position, it says none, since a contest deeper
# in the graph was settled when its merge was recorded.
law status_says_each_contest:
  for +ps: List<&2, String>
  for +cs: List<&2, Tree.Contest>
  {Main.contests.shown(ps, cs, Main.contests.said(ps, cs)) == True{} : Bool}

# Against one revision, `status` compares the folder with the very tree
# `files`, `cat` and `diff` read there — the file set the revision's
# ancestry merges to — or refuses as they do.
law status_compares_with_the_revisions_tree:
  for +fs: List<&2, Main.Full>
  for +p: String
  {Result.map(&2, &2, Main.Refused, Tree.Merged, Tree.Tree(), m => Tree.merged_tree(m), Main.status.tree.r(fs, [p])) == Main.tree.r(fs, p) : Result<&2, &2, Main.Refused, Tree.Tree()>}

# `status` reads from the folder, and replays at the position, only files
# of lines the position holds — never a file of bytes or a link, whose
# digest or target settles it: every path it asks the host to read, and
# every file whose content it replays, is among the files of lines it
# compares.
law status_reads_only_lines:
  for +dg: Map<&2, String>
  for +bf: Map<&2, String>
  for +eds: List<&2, Store.Doc>
  for +os: Map<&2, T.Split>
  for +hs: List<&2, Main.Here>
  {Bool.and(Main.all_held(T.map(~Main.Here, ~String, ~(x => Main.here.path(x)), Main.status.lined(hs)), Main.status.reads(dg, bf, hs)), Main.all_held(T.map(~Main.Here, ~String, ~(x => Main.here.file(x)), Main.status.lined(hs)), Main.status.unknown(eds, os, hs))) == True{} : Bool}

# `status` tells its survey of each path it compares once, in order; where
# the parents being joined leave a file of lines differently, it gives the
# survey no digest to compare the folder's with, since there is none —
# `record::joined_content`'s `-`; and the folder's digest it gives for each
# path is the host's answer for that path, from the answers the host gave
# for the files it was asked about, and none for a path it was not.
law status_surveys_each_path:
  for +t: Tree.Tree()
  for +stats: List<&2, String>
  for +bf: Map<&2, String>
  for +reads: Map<&2, List<&2, U32>>
  for +props: List<&2, Main.Proposal>
  for +hs: List<&2, Main.Here>
  {Main.status.surveys(Main.regular_paths(hs), stats, hs, Main.status.seens(t, Main.stats.map(Main.regular_paths(hs), stats, Map.new(&2, String)), bf, reads, props, hs)) == True{} : Bool}

# Against one revision, `status` believes the digest a statement gives a
# file of lines and replays only where none does: it is refused only where
# a file of lines it compares, whose digest no statement gives, cannot be
# replayed, and then with that file's refusal.
law status_believes_what_is_stated:
  for +older: List<&2, Main.Full>
  for +ds: List<&2, Store.Doc>
  for +left: String
  for +eds: List<&2, Store.Doc>
  for +os: Map<&2, T.Split>
  for +hs: List<&2, Main.Here>
  for +m: Map<&2, String>
  for +e: String
  for h: {Main.status.befores(older, ds, left, eds, os, hs, m) == Fail{e} : Result<&2, &2, String, Map<&2, String>>}
  {Main.status.replay_fails(older, ds, left, eds, os, Main.status.lined(hs), e) == True{} : Bool}

# Where several parents are joined, `status` reads each file of lines it
# compares at each of them, and is refused only where some parent's
# reading of some such file is, and then with that refusal.
law status_joins_what_it_reads:
  for hs: List<&2, Main.Here>
  for +fs: List<&2, Main.Full>
  for +ds: List<&2, Store.Doc>
  for +ps: List<&2, String>
  for +m: Map<&2, String>
  for +e: String
  for h: {Main.status.joined.go(fs, ds, ps, hs, m) == Fail{e} : Result<&2, &2, String, Map<&2, String>>}
  {Main.status.joined_fails(fs, ds, ps, hs, e) == True{} : Bool}
# `record` refuses a link left dangling, exactly where one would be. A
# link the position holds that names a file this record drops would be a
# reference to nothing once the revision is written, so the plan goes on
# only where every such link is going too, or sits at a path whose link in
# the folder the record observes and writes down afresh.
law record_refuses_a_dangling_link:
  for +t: Tree.Tree()
  for +looked: Tree.Tree()
  for +held: Set()
  for +walked: List<&2, T.Split>
  for +ss: List<&2, Sv.Seen>
  for +moves: List<&2, T.Split>
  {Maybe.is_none(&2, String, Sv.planned.dangles(Sv.planned(t, looked, held, walked, ss, moves))) == Sv.anchored(t, Sv.planned.gone(Sv.planned(t, looked, held, walked, ss, moves)), Sv.planned.pointing(Sv.planned(t, looked, held, walked, ss, moves))) : Bool}

# `status` refuses only what the folder holds. What its walk could not
# take is refused as the walk found it; past that, a path is refused only
# where the folder holds something there that the position cannot take — a
# link whose target this format cannot hold, or a file recorded as lines
# that is no longer text — and never a path only the position holds.
law status_refuses_what_the_folder_holds:
  for +t: Tree.Tree()
  for +held: Set()
  for +walked: List<&2, T.Split>
  for +ss: List<&2, Sv.Seen>
  {Sv.refuses_found(walked, ss, Sv.survey.refused(Sv.survey(t, held, walked, ss))) == True{} : Bool}

# A kind is stated only for a file arriving. Decision 0017 fixes a file's
# kind when it is added, so `record` goes on with a `--lines` or a
# `--bytes` exactly where each names a path it is looking at that no file of
# the position holds: a kind for a file already there is refused, since it
# would restate what was fixed at the add.
law record_states_a_kind_only_for_an_arrival:
  for +only: List<&2, String>
  for +t: Tree.Tree()
  for +ks: List<&2, T.Split>
  {Maybe.is_none(&2, String, Sv.kind_fault(only, t, ks)) == Sv.kinds_fresh(only, t, ks) : Bool}

# `record` writes one `move` line for each file moved. However the
# renames a person stated follow one another, each line is for a file this
# record is not dropping, says the last place the renames put it, and no
# file has a second.
law record_moves_each_file_once:
  for +ms: List<&2, T.Split>
  for +gone: Set()
  {Sv.moves_ok(ms, gone, Sv.moved.final(ms, gone)) == True{} : Bool}

# A revision is filed one directory deep, under its month. Whatever its
# message says, the name it has in that directory holds nothing a
# filesystem reserves — no separator of any platform's, none of
# `:*?"<>|`, and no control character — where its date, its change and
# its digest hold none either: the message's first line gave all of them up
# to spaces before a word of it was kept.
law a_revision_is_filed_under_its_month:
  for +when: String
  for +message: String
  for +change: String
  for +id: String
  for +ns: List<&2, Naming.Named>
  for hw: {Naming.plain(String.take(when, 10n)) == True{} : Bool}
  for hc: {Naming.plain(change) == True{} : Bool}
  for hi: {Naming.plain(id) == True{} : Bool}
  {Naming.in_month(String.take(when, 7n), Naming.stem(when, message, change, id, ns)) == True{} : Bool}

# Content is filed under a name a filesystem can hold. Whatever paths a
# revision's files had, the name each is written under in the revision's
# directory — its path with every control character a space, with the
# digest's first letters where two names meet, or the digest alone where
# its path is another's directory — holds no control character, where no
# digest does.
law content_is_filed_under_a_name_a_filesystem_holds:
  for +fs: List<&2, Naming.Filing>
  for +held: String
  for hf: {Naming.helds_controlless(fs) == True{} : Bool}
  for hh: {Naming.controlless(held) == True{} : Bool}
  {Naming.controlless(Naming.filed_as(Naming.filed(fs), held)) == True{} : Bool}

# `record` compares this machine's clock with the latest work the store
# holds. Of the timestamps it is handed, the one `newest` answers is one of
# them, and none of the others is later, however their offsets spell them.
law record_compares_with_the_latest:
  for +ws: List<&2, String>
  for +w: String
  for e: {Naming.newest(ws, None{}) == Some{w} : Maybe<&2, String>}
  {Naming.latest(ws, w) == True{} : Bool}

# `abandon` takes a reason exactly where it says something. The reason is
# the only thing a tombstone carries, so one that is empty or nothing but
# whitespace is refused, and any other is taken.
law abandon_takes_a_reason_that_says_something:
  for +m: String
  {Result.is_done(&2, &2, Main.Refused, Unit, Main.reason.r(m)) == Bool.not(Naming.every(~Naming.is_space, m)) : Bool}

# `record` restricted to some paths names only what is there. It goes on
# only where each path a person names answers to something — a file the
# folder holds, one the position holds, or one the stated renames put there,
# at the path or beneath it as a directory — since a path a rule keeps out
# is refused as kept out, and any other that answers to nothing as absent.
law record_names_only_what_is_there:
  for +rules: List<&2, Folder.Scope>
  for +named: List<&2, String>
  for +folder: List<&2, String>
  for +was: List<&2, String>
  for +placed: List<&2, String>
  for e: {Main.named.r(rules, named, folder, was, placed) == Done{Unit{}} : Result<&2, &2, Main.Refused, Unit>}
  {Sv.answered(named, folder, was, placed) == True{} : Bool}

# `--at` and `--move` keep each file once. However a person places files,
# the position `record` goes on with holds the files it held, each once and
# in the same order: a rename moves a file and never makes or loses one.
law a_rename_keeps_each_file_once:
  for +t: Tree.Tree()
  for +ats: List<&2, T.Split>
  for +ms: List<&2, T.Split>
  for +t2: Tree.Tree()
  for +moved: List<&2, T.Split>
  for e: {Main.placed.r(t, ats, ms) == Done{Main.Placed{t2, moved}} : Result<&2, &2, Main.Refused, Main.Placed>}
  {Sv.files(t2) == Sv.files(t) : List<&2, String>}

# And each file is where a person said. Of the renames `record` goes on
# with — every `--at`, then every `--move`, each by the file it moves — a
# file of the position is at the last place one put it, and a file none
# moved is where it was; so `--at` settles each file it names at its path.
law a_rename_puts_each_file_where_it_was_said:
  for +t: Tree.Tree()
  for +ats: List<&2, T.Split>
  for +ms: List<&2, T.Split>
  for +t2: Tree.Tree()
  for +moved: List<&2, T.Split>
  for e: {Main.placed.r(t, ats, ms) == Done{Main.Placed{t2, moved}} : Result<&2, &2, Main.Refused, Main.Placed>}
  for +g: String
  for hg: {Tree.holds(t, g) == True{} : Bool}
  {Tree.path(t2, g) == Maybe.or(&2, String, Sv.last_move(moved, g), Tree.path(t, g)) : Maybe<&2, String>}

# `record` restricted to some paths refuses only among them. Naming paths
# narrows what the survey pairs, from the position and the folder alike,
# and what the walk refused, so whatever the folder and the store answer,
# every path the plan refuses is one the restriction covers: a file the
# format cannot take elsewhere does not stop a record of the paths named.
law record_refuses_only_what_it_looks_at:
  for +only: List<&2, String>
  for +t: Tree.Tree()
  for +t0: Tree.Tree()
  for +found: List<&2, Folder.Found>
  for +walked: List<&2, T.Split>
  for +held: Set()
  for +dg: Map<&2, String>
  for +bf: Map<&2, String>
  for +reads: Map<&2, List<&2, U32>>
  for +props: List<&2, Main.Proposal>
  for +moves: List<&2, T.Split>
  {Sv.all_covered(only, Sv.planned.refused(Sv.planned(t, Sv.only.tree(only, t), held, Sv.only.refused(only, walked), Main.status.seens(t0, dg, bf, reads, props, Main.heres(Sv.unclaimed(Sv.only.tree(only, t), Sv.claims(Sv.only.tree(only, t))), Sv.unclaimed_found(Sv.only.found(only, found), Sv.claims(Sv.only.tree(only, t))), Main.Limit.None{})), moves))) == True{} : Bool}

# A revision's summary is sixty characters at most. However long the first
# line of its message, the name keeps as much of it as fits, cut between
# words where a space allows it and shorter again for the dots and spaces
# it gives up at the end, so a name leaves room within any filesystem's
# limit for its date, its suffixes and its extension.
law a_summary_fits_its_limit:
  for +message: String
  for +change: String
  {Nat.is_le(String.length(Naming.summary(message, change)), Naming.SUMMARY_CHARS()) == True{} : Bool}

# A revision's summary gives up a dot or a space at either end. It never
# begins with a dot, so it neither hides a name nor spends its budget on
# one, and never ends with a dot or a space, which some filesystems drop
# from a directory's name without saying so — whatever the message, where
# the change's letters, which stand in for a message that says nothing,
# are neither.
law a_summary_gives_up_its_ends:
  for +message: String
  for +change: String
  for hc: {Naming.bare(change) == True{} : Bool}
  {Naming.trimmed(Naming.summary(message, change)) == True{} : Bool}

# `status` offers a rename only where the bytes make one. Decision 0011
# observes no rename, so the survey says it noticed one only where some
# bytes, not nothing, left exactly one path and arrived at exactly one
# other: each rename it offers is from the one path that held them to the
# one that holds them now.
law status_offers_a_rename_the_bytes_make:
  for +t: Tree.Tree()
  for +held: Set()
  for +walked: List<&2, T.Split>
  for +ss: List<&2, Sv.Seen>
  {Sv.renames_ok(Sv.departed(List.append(&2, Sv.Obs, Sv.seens(ss), Sv.claimed_drops(t, Sv.claims(t), held))), Sv.arrived(List.append(&2, Sv.Obs, Sv.seens(ss), Sv.claimed_drops(t, Sv.claims(t), held))), Sv.survey.renames(Sv.survey(t, held, walked, ss))) == True{} : Bool}

# `record` plans from the position in file order, the order a revision
# states its files in, whatever order the renames left it in; and under
# each file it holds the entries the renames left, in the order they had.
law record_plans_in_file_order:
  for +t: Tree.Tree()
  {Sv.in_file_order(Sv.by_file(t)) == True{} : Bool}

law record_plans_every_file:
  for +t: Tree.Tree()
  for +f: String
  {Main.entries.at(f, Sv.by_file(t)) == Main.entries.at(f, t) : Tree.Tree()}

# A link in the folder is written as a reference only to what the revision
# states. Its target, folded against the link's own directory, is spelled
# as the path it lands on only where that path is one the revision states —
# a file the position keeps there, or one arriving; anywhere else the link
# keeps the string it spells.
law a_link_refers_only_to_what_the_revision_states:
  for +t: Tree.Tree()
  for +gone: Set()
  for +arriving: Set()
  for +path: String
  for +target: String
  for +at: String
  for e: {Sv.observed(t, gone, arriving, path, target) == "r" ++ at : String}
  {Sv.lands_on(t, gone, arriving, path, target, at) == True{} : Bool}

# `record` goes on only where each path it looks at holds one file.
# Decision 0008 lets a merge leave two files at one path, and `--at` is how
# a person settles them: whatever the position, the plan goes on only where
# no path of it holds more than one, however the paths sort.
law record_goes_on_where_each_path_holds_one_file:
  for +t: Tree.Tree()
  for +looked: Tree.Tree()
  for +held: Set()
  for +walked: List<&2, T.Split>
  for +ss: List<&2, Sv.Seen>
  for +moves: List<&2, T.Split>
  for +accepted: List<&2, String>
  for +done: Sv.Planned
  for e: {Main.planned.r(looked, Sv.planned(t, looked, held, walked, ss, moves), accepted) == Done{done} : Result<&2, &2, Main.Refused, Sv.Planned>}
  for +p: String
  {Tree.at_most_one(Tree.at(looked, p)) == True{} : Bool}

# A link resolves inside the folder. Wherever a link sits at a path the
# format holds, its target, folded against the link's own directory, is
# either no path at all or one that is not absolute and never climbs out
# with `..`: a link is never written as a reference to anything outside
# what the folder holds. The fold is then spelled in normal form C, which
# moves no `/` and no `.` (`nfc_leaves_separators_alone`).
law a_link_resolves_inside_the_folder:
  for +link: String
  for +target: String
  for +p: String
  for h: {Sv.path_check(link) == None{} : Maybe<&2, String>}
  for e: {Sv.resolution(link, target) == Some{p} : Maybe<&2, String>}
  {Main.escapes(p) == False{} : Bool}

# `record` reads its words as their plain reading says: the word after a
# flag that takes a value is that value, whatever it is; the last `-m` and
# the last `--onto` count; each `--merge`, `--at`, `--move`, `--bytes` and
# `--lines` counts, in the order given, an `--at` or a `--move` cut at its
# first `=`; `-n` and `--fields` are asked for if they are there; and
# every other word is a path, the slashes a shell leaves on a directory
# taken off. Each `--accept` and each path is kept, the last first.
law record_reads_its_words:
  for +args: List<&2, String>
  for +cmd: Main.RecordCmd
  for e: {Main.record.args.r(args) == Done{cmd} : Result<&2, &2, Main.Refused, Main.RecordCmd>}
  {cmd == Main.rargs.said(Main.rargs.read(args, Main.rword(args))) : Main.RecordCmd}

# `amend`, `abandon` and `carry` read their words as their plain reading
# says: the word after `-m`, `--move` or `--onto`, where the command takes
# it, is its value, whatever it is; the last `-m` and the last `--onto`
# count, and each `--move`, in order, cut at its first `=`; `-n`,
# `--fields` and `--only` are asked for if they are there; and the one
# other word is the target.
law rewrite_reads_its_words:
  for +cmd: String
  for +args: List<&2, String>
  for +c: Main.RwCmd
  for e: {Main.rw.args.r(cmd, args) == Done{c} : Result<&2, &2, Main.Refused, Main.RwCmd>}
  {c == Main.wargs.said(Main.wargs.read(cmd, args, Main.wword(cmd, args))) : Main.RwCmd}

# A carry restates work without changing whose it is or when it was done.
# Whatever it is asked to carry, each revision a plan would write has the
# change, author, moment and message of the revision the store holds under
# the identifier it supersedes, supersedes that one alone, and is named by
# the digest of its own text: the identifier `carry` reports is the one
# the store will find the revision under.
law carry_keeps_what_it_restates:
  for +fs: List<&2, Main.Full>
  for +ds: List<&2, Store.Doc>
  for +c: Main.Carrying
  for steps: List<&2, Main.Step>
  for e: {Main.carry.plan(fs, ds, c) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}
  {Main.steps.kept(fs, steps) == True{} : Bool}

# What `abandon` abandons is a line of work nothing has rewritten yet. It
# begins at the revision named, and each revision after that stands on the
# one before it and on nothing else, so the tombstone standing where the
# first stood takes no other line's work out of the history; and with
# `--only` it is the revision named alone, which joins no other line.
law abandon_takes_a_line:
  for +fs: List<&2, Main.Full>
  for +id: String
  for only: Bool
  for run: List<&2, String>
  for e: {Main.abandon.plan.r(fs, id, only) == Done{run} : Result<&2, &2, Main.Refused, List<&2, String>>}
  {Main.abandon.line(fs, id, only, run) == True{} : Bool}

# A reword changes the message alone. Where work stands on a revision,
# `amend` may only reword it: the message it writes is the one `-m` gave
# and not the one the revision had, it supersedes that revision alone, and
# with the old message put back it says exactly what that revision said.
law reword_changes_only_the_message:
  for +fs: List<&2, Main.Full>
  for prev: Main.Full
  for +standing: List<&2, String>
  for +m: Maybe<&2, String>
  for +reviser: String
  for +revised: String
  for doc: Rev.Rev
  for e: {Main.reword.r(fs, prev, standing, m, reviser, revised) == Done{doc} : Result<&2, &2, Main.Refused, Rev.Rev>}
  {Main.reword.ok(prev, m, doc) == True{} : Bool}

# What `record` states a file holds is what the folder holds there. Of
# each file it drafts content for, an edit is the written form of the
# document that replays the position's lines of that file to the lines
# the folder holds — `befores` being the position's — text is the bytes
# the folder holds, a payload is named by the digest of the folder's, and
# where the parents being joined leave the file differently, a resolution
# is the written form of the one the walk's proposal and the folder's lines
# make, which `merge_resolution_reads_back` assembles back to those lines.
law record_states_the_folder:
  for +befores: List<&2, Main.Before>
  for +t: Tree.Tree()
  for +hs: List<&2, Main.Here>
  for +dg: Map<&2, String>
  for +reads: Map<&2, List<&2, U32>>
  for +ks: List<&2, T.Split>
  for +moves: List<&2, T.Split>
  for +obs: List<&2, Sv.Obs>
  for +ls: List<&2, String>
  for +mint: List<&2, T.Split>
  {Main.contents.state(befores, dg, reads, Main.drafted.contents(Main.drafted.of(befores, t, hs, dg, reads, ks, moves, obs, ls, mint))) == True{} : Bool}

# What `record` writes is named as it says. Each file arriving is added
# under the identifier minted for it, in path order; the revision is named
# by the digest of its own text, and filed under the name decision 0019
# composes from its moment, its message and its change, extended only
# where the store already holds a revision of that name; and each
# bookmark it moves names the change of one of its parents.
law record_names_what_it_writes:
  for w: Main.Writing
  for +hex: String
  for +befores: List<&2, Main.Before>
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for +ps: List<&2, String>
  for +t: Tree.Tree()
  for +hs: List<&2, Main.Here>
  for +dg: Map<&2, String>
  for +reads: Map<&2, List<&2, U32>>
  for +ks: List<&2, T.Split>
  for +moves: List<&2, T.Split>
  for +obs: List<&2, Sv.Obs>
  for +ls: List<&2, String>
  {Main.record.named(w, Sv.sorted(Sv.added(obs)), Main.parents.changes(fs, ps), Main.record.planned(w, hex, befores, fs, bs, ps, t, hs, dg, reads, ks, moves, obs, ls)) == True{} : Bool}

# What `record` goes on to write is a plan the survey settled. Where it
# is not refused, no path is claimed by several files, nothing is there
# that the format cannot record, no file still holds a line the renderer
# wrote, nothing a merge would leave empty, no link dangles, and the
# attachments accepted are exactly the ones concurrent work states
# different bytes for.
law record_writes_only_what_is_settled:
  for +looked: Tree.Tree()
  for pl: Sv.Planned
  for +accepted: List<&2, String>
  for pl2: Sv.Planned
  for e: {Main.planned.r(looked, pl, accepted) == Done{pl2} : Result<&2, &2, Main.Refused, Sv.Planned>}
  {Main.planned.settled(pl2, accepted) == True{} : Bool}

# What `amend` rewrites is a revision the store holds: the target named,
# or else the one head there is.
law amend_rewrites_a_held_revision:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for named: Maybe<&2, String>
  for +f: Main.Full
  for e: {Main.amend.target.r(fs, bs, named) == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}
  {Rev.member(Main.ids(fs), Main.id_of(f)) == True{} : Bool}

# What `carry` is asked to carry, where a target is named, is a revision
# the store holds.
law carry_carries_a_held_revision:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for named: Maybe<&2, String>
  for +id: String
  for e: {Main.carry.target.r(fs, bs, named) == Done{Some{id}} : Result<&2, &2, Main.Refused, Maybe<&2, String>>}
  {Rev.member(Main.ids(fs), id) == True{} : Bool}

# Every file `record` moves by a stated rename is one the position holds:
# `--at` names a file the history holds, and `--move` a path where one
# file alone is, so no rename moves a file from nowhere.
law record_moves_only_held_files:
  for +t: Tree.Tree()
  for +ats: List<&2, T.Split>
  for +ms: List<&2, T.Split>
  for p: Main.Placed
  for e: {Main.placed.r(t, ats, ms) == Done{p} : Result<&2, &2, Main.Refused, Main.Placed>}
  {Main.moved.held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t), Main.placed.moved(p)) == True{} : Bool}

# A record restricted to some paths is no merge, since a merge states
# every contested file, and every rename it states is among those paths
# at both its ends, since recording one end alone would spell the other as
# a file appearing or disappearing.
law record_restricts_no_merge_and_no_half_rename:
  for +named: List<&2, String>
  for +ps: List<&2, String>
  for +moves: List<&2, T.Split>
  for u: Unit
  for e: {Main.restricted.r(named, ps, moves) == Done{u} : Result<&2, &2, Main.Refused, Unit>}
  {Main.restriction.whole(named, ps, moves) == True{} : Bool}

# `record --dry-run` says a file arriving once. Whatever the survey
# observed, of the facts the plan it prints states, only an `added` line,
# and a `moved` or `dropped` one, names a path being added: an arrival
# carries its content, mode and target in with it.
law record_says_an_arrival_once:
  for +t: Tree.Tree()
  for +looked: Tree.Tree()
  for +held: Set()
  for +walked: List<&2, T.Split>
  for +ss: List<&2, Sv.Seen>
  for +moves: List<&2, T.Split>
  {Main.recorded.once.list(Sv.added(Main.planned.obs(Sv.planned(t, looked, held, walked, ss, moves))), Main.planned.facts(Sv.planned(t, looked, held, walked, ss, moves))) == True{} : Bool}

# Asked for `--fields`, what `record`, `amend`, `abandon` and `carry` say
# of what they wrote is decision 0074's: `historica-wrote-1` first, and
# then a `revision` line for each revision the act wrote — each named
# once, in digest order, and none named that it did not write.
law writes_say_what_they_wrote:
  for +a: String
  for +when: String
  for +m: String
  for +facts: List<&2, T.Split>
  for +change: String
  for +id: String
  for +names: List<&2, String>
  for +ps: List<&2, String>
  for +prev: String
  for +carrying: List<&2, String>
  for +steps: List<&2, Main.Step>
  for +run: List<&2, String>
  for +dry: Bool
  {Bool.and(Main.fields.ok([id], Main.record.said.lines(Main.Writing{a, when, m, True{}}, facts, change, id, names, ps)), Bool.and(Main.fields.ok(id <> Main.carried.ids(steps), Main.amend.said.lines(True{}, False{}, facts, prev, change, id, carrying, steps)), Bool.and(Main.fields.ok(id <> Main.carried.ids(steps), Main.abandon.said.lines(True{}, id, change, run, names, steps)), Main.fields.ok(Main.carried.ids(steps), Main.carry.said.lines(True{}, dry, steps))))) == True{} : Bool}

# A file arriving that a person said is lines is read to be sure it is
# text, and where `record` goes on it is: every file it reads because
# `--lines` named it has bytes that are UTF-8.
law record_reads_lines_as_text:
  for +ks: List<&2, T.Split>
  for +reads: Map<&2, List<&2, U32>>
  for hs: List<&2, Main.Here>
  for e: {Main.not_lines(ks, reads, hs) == None{} : Maybe<&2, String>}
  {Main.utf8.all(reads, Main.lined_added(ks, hs)) == True{} : Bool}

# What `record` reads of the position, to state an edit against it, is
# the store's replay of each file of lines it edits: one reading of each
# file, in the order asked, where every replay succeeds.
law record_reads_the_position:
  for +older: List<&2, Main.Full>
  for +ds: List<&2, Store.Doc>
  for +left: String
  for files: List<&2, String>
  for bs: List<&2, Main.Before>
  for e: {Main.befores.r(older, ds, left, files) == Done{bs} : Result<&2, &2, Main.Refused, List<&2, Main.Before>>}
  {Main.befores.read(older, ds, left, files, bs) == True{} : Bool}

# An amendment keeps the identifiers it minted. Of the files arriving
# against the amended revision's parents, each is given an identifier, in
# path order, and each the amended revision added keeps the identifier it
# was added under: only a path it did not add is minted one afresh.
law amend_keeps_what_it_added:
  for +arriving: List<&2, String>
  for +kept: List<&2, T.Split>
  for +hex: String
  {Main.amend.minted.ok(arriving, kept, Main.amend.minted(arriving, kept, hex)) == True{} : Bool}

# `abandon` is asked for a revision and a reason. Where it goes on, a
# target was named, a dry run did not also ask for `--fields`, and the
# reason, the one thing a tombstone carries, is not blank.
law abandon_asks_for_a_revision_and_a_reason:
  for c: Main.RwCmd
  for +m: String
  for u1: Unit
  for u2: Unit
  for u3: Unit
  for e1: {Main.abandon.named.r(Main.rw.named(c)) == Done{u1} : Result<&2, &2, Main.Refused, Unit>}
  for e2: {Main.rw.plan.r("abandon", Main.rw.dry_of(c), Main.rw.fields_of(c)) == Done{u2} : Result<&2, &2, Main.Refused, Unit>}
  for e3: {Main.reason.r(m) == Done{u3} : Result<&2, &2, Main.Refused, Unit>}
  {Main.abandon.asked(c, m) == True{} : Bool}

# A kind is a fact about a file: where `record` goes on, every path
# `--bytes` or `--lines` names is a file the folder holds.
law record_gives_kinds_only_to_files:
  for ks: List<&2, T.Split>
  for +found: Set()
  for u: Unit
  for e: {Main.kinds.unheld.r(ks, found) == Done{u} : Result<&2, &2, Main.Refused, Unit>}
  {Main.kinds.found(ks, found) == True{} : Bool}

# A dry run of `abandon` begins by naming, in order, each revision of the
# run it would abandon, by the first twelve letters of its digest.
law abandon_dry_run_names_the_run:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for +id: String
  for +only: Bool
  for +run: List<&2, String>
  {Main.said.first(run, Main.abandon.dry.lines(fs, bs, id, only, run), "would abandon ") == True{} : Bool}

# `update` reads its words as they say: a dry run where `-n` or
# `--dry-run` is among them, and the target the one word that does not
# begin with `-`.
law update_reads_its_words:
  for +ws: List<&2, String>
  for +c: Upd.UpdateCmd
  for e: {Upd.args.r(ws) == Done{c} : Result<&2, &2, Main.Refused, Upd.UpdateCmd>}
  {c == Upd.UpdateCmd{Upd.uargs.target(ws), Upd.uargs.dry(ws)} : Upd.UpdateCmd}

# Where `update` plans at all, the folder it leaves holds the target as the
# store reads it: once the plan is carried out, every path the target's
# tree holds one file at holds, for a file of lines, the bytes `cat
# <target> <path>` prints; for a file of bytes, the payload the tree names;
# each with the tree's mode; and for a link, a link pointing where `cat`
# says it points — whatever the folder held there before, since anything
# else refuses the whole update. `id` and `t` are the target and its tree,
# `found`, `dg` and `ls` the walk's files, digests and links, and `ds` the
# store's documents.
law update_lands:
  for +fs: List<&2, Main.Full>
  for +id: String
  for +t: Tree.Tree()
  for +rs: List<&2, Folder.Scope>
  for +walked: List<&2, T.Split>
  for +found: List<&2, Folder.Found>
  for +dg: Map<&2, String>
  for +ls: Map<&2, String>
  for +located: Map<&2, String>
  for +ds: List<&2, Store.Doc>
  for +more: List<&2, Store.Doc>
  for -p: Upd.Plan
  for +e: {Upd.plan.from(fs, id, t, rs, walked, found, dg, ls, located, ds, more) == Done{p} : Result<&2, &2, List<&2, T.Split>, Upd.Plan>}
  {Upd.holds(fs, ds, id, t, p) == True{} : Bool}

# Decision 0030's rule, in the store's own terms: every file `update`
# writes over, or takes away, holds bytes that `cat` of some revision the
# store holds reads for some file of it, or that its tree names as a
# file's payload — so nothing it touches is the only copy of anything.
# (`more` is what it fetched to read history with.) A link it takes away
# is read from the revisions' link statements, as the Rust tool reads it,
# and is not asked about here.
law update_spares_the_unrecorded:
  for +fs: List<&2, Main.Full>
  for +id: String
  for +t: Tree.Tree()
  for +rs: List<&2, Folder.Scope>
  for +walked: List<&2, T.Split>
  for +found: List<&2, Folder.Found>
  for +dg: Map<&2, String>
  for +ls: Map<&2, String>
  for +located: Map<&2, String>
  for +ds: List<&2, Store.Doc>
  for +more: List<&2, Store.Doc>
  for -p: Upd.Plan
  for +e: {Upd.plan.from(fs, id, t, rs, walked, found, dg, ls, located, ds, more) == Done{p} : Result<&2, &2, List<&2, T.Split>, Upd.Plan>}
  {Upd.touches.recorded(fs, List.append(&2, Store.Doc, ds, more), p) == True{} : Bool}

# Decision 0032's promise: the resolution `record --merge` writes for a
# file of lines, assembled as `cat` assembles one, is exactly the file the
# person left in the folder — every line they kept named back from the
# document that minted it, every line they wrote stated, and the digest it
# states the one `cat` finds — wherever the store's documents mint each
# element the walk stands under as the walk read them.
law merge_resolution_reads_back:
  for +ds: List<&2, Store.Doc>
  for +j: Conflict.Joined
  for +s: String
  for hm: {Main.all_mint(ds, Conflict.named(j)) == True{} : Bool}
  for doc: Res.Doc
  for e: {Conflict.resolve(j, Ops.from_text(s)) == Some{doc} : Maybe<&2, Res.Doc>}
  {Main.assemble(ds, doc) == Done{Ops.from_text(s)} : Result<&2, &2, String, List<&2, Ops.Item>>}

# `merge` writes what the walk reads into the folder, fenced where
# concurrent work met; a file where nothing met — no region, and no line
# but the last without a newline — is written as the walk's file, byte for
# byte, with no line in it a person must find and delete.
law merge_renders_the_uncontested_as_itself:
  for j: Conflict.Joined
  for e: {Conflict.met(j) == False{} : Bool}
  {Conflict.render(j) == Conflict.plain(j) : String}

# `merge` joins only revisions the store holds: each head a person names
# resolves to one, and each it joins unnamed is a current head, so no
# spelling can make it lay out work the store does not have.
law merge_joins_held_revisions:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for +ss: List<&2, String>
  for +xs: List<&2, T.Split>
  for e: {Merging.joined.r(fs, bs, ss) == Done{xs} : Result<&2, &2, Main.Refused, List<&2, T.Split>>}
  {Main.all_held(Main.ids(fs), Merging.typed.ids(xs)) == True{} : Bool}

# Decision 0012's rule, what is named and every current head that is not:
# whatever a person names, and in whatever order, `merge` joins every
# current head of the store, which is what makes the `record` line it
# prints record the merge it laid out.
law merge_joins_every_head:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for +ss: List<&2, String>
  for +xs: List<&2, T.Split>
  for e: {Merging.joined.r(fs, bs, ss) == Done{xs} : Result<&2, &2, Main.Refused, List<&2, T.Split>>}
  {Main.all_held(Merging.typed.ids(xs), Upd.heads.sorted(fs)) == True{} : Bool}

# Decision 0012's safety, in what the store and the folder read: every
# act `merge` performs is accounted for by some file of the merged tree.
# It writes at the path that file holds, or at the name `beside` gives
# it, with the mode the tree records: a file of lines as the walk of the
# heads joined renders it, a payload the tree names, a link pointing where
# `cat` says. And it writes a file only over what the folder's walk read
# there as nothing, bytes the folder says are not text, what it is
# writing, the walk's reading unfenced, or what one of the heads reads for
# the file — its ancestry walked for a file of lines, its tree's payload
# for a file of bytes. Work nobody recorded is never written over.
law merge_spares_the_unrecorded:
  for +fs: List<&2, Main.Full>
  for +ds: List<&2, Store.Doc>
  for +heads: List<&2, String>
  for +bs: List<&2, T.Split>
  for +t: Tree.Tree()
  for +dg: Map<&2, String>
  for +texts: Map<&2, String>
  for +ls: Map<&2, String>
  for +cs: List<&2, Tree.Contest>
  for +located: Map<&2, String>
  for es: List<&2, Tree.Entry>
  {Merging.laid.every(fs, ds, heads, bs, t, dg, texts, es, Merging.lay.acts(Merging.lay.all(t, cs, located, Merging.places(fs, ds, heads, bs, dg, ls, texts, es)))) == True{} : Bool}

# The order `check` walks a merged file's events in places each event after
# every event its author had seen, whatever it is given to place and
# however many rounds it takes: what makes the walk a reading of the
# history and not of some other one.
law check_walks_causally:
  for fuel: Nat
  for +g: List<&2, Merge.Rev>
  for +ixs: List<&2, Nat>
  {Check.causal(g, Check.kahn(fuel, g, ixs, Nil{})) == True{} : Bool}

# The command line reads `-C <dir>` as often as it is given, the last
# counting, and hands the command word and every word after it to the
# command as written — a `-C` after the command word is the command's.
law argv_reads_its_words:
  for ds: List<&2, String>
  for +w: String
  for +rest: List<&2, String>
  for e: {Argv.lead.of(w) == Argv.Lead.Word{} : Argv.Lead}
  {Argv.read(Argv.spelled(ds, w, rest)) == Argv.Asked.Command{Argv.last(ds, None{}), w, rest} : Argv.Asked}

# `-V` and `--version` read as the version asked for, and `help`, `-h` and
# `--help` as the usage, wherever the `-C`s before them point and whatever
# follows them.
law argv_reads_the_version:
  for ds: List<&2, String>
  for +v: String
  for +rest: List<&2, String>
  for h: {Bool.or(String.eq(v, "-V"), String.eq(v, "--version")) == True{} : Bool}
  {Argv.read(Argv.spelled(ds, v, rest)) == Argv.Asked.Version{} : Argv.Asked}

law argv_reads_help:
  for ds: List<&2, String>
  for +v: String
  for +rest: List<&2, String>
  for h: {Bool.or(String.eq(v, "help"), Bool.or(String.eq(v, "-h"), String.eq(v, "--help"))) == True{} : Bool}
  {Argv.read(Argv.spelled(ds, v, rest)) == Argv.Asked.Usage{} : Argv.Asked}

# Decision 0072: the program a word no command here has is dispatched to
# holds no `/`, so it is looked up on `PATH` and never run from where a
# path would put it.
law dispatch_runs_no_path:
  for +base: String
  for +w: String
  for args: List<&2, String>
  for +d: String
  for +p: String
  for as: List<&2, String>
  for e: {Shell.plan(base, w, args) == Shell.Plan.Run{d, p, as} : Shell.Plan}
  {T.has_char(p, '/') == False{} : Bool}

# A store's header opens whatever its note says, once a blank line sets the
# note apart from the format line (decision 0069) — the header `init`
# writes among them.
law header_opens_under_a_note:
  for +note: String
  {Store.header.r("historica\n\n" ++ note) == Done{Unit{}} : Result<&2, &2, String, Unit>}

# The file `identity` writes reads back as the author it was written for,
# for work in any directory, wherever that author is one a revision can
# hold.
law identity_reads_back:
  for +file: String
  for +a: String
  for +directory: String
  for +home: Maybe<&2, String>
  for h: {Identity.unusable(a) == False{} : Bool}
  {Identity.from_text(file, Identity.wanted(a), directory, home) == Done{a} : Result<&2, &2, String, String>}

# `check` reads `--complete` wherever it stands, and every other word, in
# order, as a directory to check.
law check_reads_its_words:
  for +ws: List<&2, String>
  {Check.asked(ws) == Check.Asked{Rev.member(ws, "--complete"), Check.words.other(ws)} : Check.Asked}

# What `check` gathers from the store `init` makes — the header under its
# note, `skipped/` holding only its note, and nothing else — it finds
# nothing wrong with, wherever the store is.
law check_finds_nothing_in_a_new_store:
  for +root: String
  {Check.found(Check.Gathered{root, Some{Notes.HEADER_NOTE()}, Check.Walked{Nil{}, Nil{}}, Nil{}, Check.Walked{Nil{}, Nil{}}, Nil{}, Check.Texts{Nil{}, Nil{}}, False{}, Check.skipped.read(root ++ "/skipped/README.txt", Done{Notes.SKIPPED_NOTE()}), Check.Walked{Nil{}, Nil{}}, Nil{}}) == Nil{} : List<&2, Check.Finding>}

# `skip`'s rules are equal only when they are one rule, and each is equal
# to itself: what `held` asks is membership.
law skip_rules_equal_only_when_equal:
  for a: Skip.Rule
  for b: Skip.Rule
  for e: {Skip.rule.eq(a, b) == True{} : Bool}
  {a == b : Skip.Rule}

law skip_rule_equals_itself:
  for a: Skip.Rule
  {Skip.rule.eq(a, a) == True{} : Bool}

# The file `skip <path>` writes for a path it accepts — spelled with no
# `/` at its end, as `skip` spells one — is read back by the reader of
# `skipped/` as exactly the rule it meant: the path or the directory, and
# private or not.
law skip_path_rule_reads_back:
  for +file: String
  for +v: String
  for +directory: Bool
  for +private: Bool
  for +sc: Folder.Scope
  for e: {Skip.path.scoped(v, directory) == Done{sc} : Result<&2, &2, Main.Refused, Folder.Scope>}
  for +h: {String.ends_with(v, "/") == False{} : Bool}
  {Skip.stated.of(file, Skip.file.text(Skip.Rule{sc, private}), Folder.rule_in(Skip.file.text(Skip.Rule{sc, private}))) == [Skip.Stating{Skip.Rule{sc, private}, file}] : List<&2, Skip.Stating>}

# And the file `skip --name <name>` writes for a name it accepts, the same.
law skip_name_rule_reads_back:
  for +file: String
  for +n: String
  for +private: Bool
  for +sc: Folder.Scope
  for e: {Skip.name.scope.r(n) == Done{sc} : Result<&2, &2, Main.Refused, Folder.Scope>}
  {Skip.stated.of(file, Skip.file.text(Skip.Rule{sc, private}), Folder.rule_in(Skip.file.text(Skip.Rule{sc, private}))) == [Skip.Stating{Skip.Rule{sc, private}, file}] : List<&2, Skip.Stating>}

# The rule `skip <path>` makes skips that file, or that directory and a
# file under it, and nothing whose path does not start with the one named.
law skip_path_rule_skips_under_its_path:
  for +v: String
  for +directory: Bool
  for +sc: Folder.Scope
  for e: {Skip.path.scoped(v, directory) == Done{sc} : Result<&2, &2, Main.Refused, Folder.Scope>}
  for +x: String
  for +q: String
  {Bool.and(Bool.pick(Bool, directory, Bool.and(Folder.skips_directory([sc], v), Folder.skips([sc], String.append(v ++ "/", x))), Folder.skips([sc], v)), Bool.or(Bool.not(Folder.skips([sc], q)), String.starts_with(q, v))) == True{} : Bool}

# `skip` with no arguments lists every rule the files of `skipped/` state,
# and no rule twice.
law skip_lists_each_rule_once:
  for +ss: List<&2, Skip.Stating>
  {Bool.and(Skip.nodup(Skip.stated.rules(Skip.once(ss, Nil{}, Skip.once.dup(ss, Nil{})))), Skip.all.held(Skip.stated.rules(ss), Skip.stated.rules(Skip.once(ss, Nil{}, Skip.once.dup(ss, Nil{}))))) == True{} : Bool}

# What `skip <path>...` writes is no rule the store already states and no
# rule twice, and every rule asked for is written or was already there.
law skip_writes_what_is_new:
  for +rs: List<&2, Skip.Rule>
  for +had: List<&2, Skip.Rule>
  {Bool.and(Bool.and(Skip.none.held(Skip.sorted.fresh(Skip.sorted.go(rs, had, Nil{}, Nil{}, Skip.sorted.dup(rs, had, Nil{}))), had), Skip.nodup(Skip.sorted.fresh(Skip.sorted.go(rs, had, Nil{}, Nil{}, Skip.sorted.dup(rs, had, Nil{}))))), Skip.all.held(rs, List.append(&2, Skip.Rule, Skip.sorted.fresh(Skip.sorted.go(rs, had, Nil{}, Nil{}, Skip.sorted.dup(rs, had, Nil{}))), had))) == True{} : Bool}

# `update` run again from what it left keeps every path it stepped
# through: where it decides a path anything but a refusal, the path, once
# that step is done, is one the same want keeps — whatever history is said
# to record there the second time. So a second update of the same
# target, from the same store, writes nothing over what the first wrote,
# points no link again and sets no mode.
law update_again_keeps:
  for +w: Upd.Wants
  for +h: Upd.Held
  for +rs: List<&2, String>
  for +rs2: List<&2, String>
  for e: {Upd.refuses(Upd.decide(w, h, rs)) == False{} : Bool}
  {Upd.decide(w, Upd.after(w, h, Upd.decide(w, h, rs)), rs2) == Upd.Step.Keep{} : Upd.Step}

# `update` says the folder already holds the target, and carries nothing
# out, only where carrying its plan out would change nothing: every path it
# steps through would hold what it held, and nothing would be taken away.
law update_settles_only_what_stays:
  for p: Upd.Plan
  for +e: {Upd.settled(p) == True{} : Bool}
  {Upd.unchanged(p) == True{} : Bool}

# Decision 0008 forbids the format inventing a name, so `merge` keeps a
# path several files claim for the first of them and writes each other
# beside it. The files it writes beside a path are exactly those: each is
# one a contest names after the first, and each one a contest names after
# the first is written beside.
law merge_sets_aside_the_claims:
  for +cs: List<&2, Tree.Contest>
  {Bool.and(Merging.besides.claimed(cs, Merging.typed.ids(Merging.beside(cs))), Merging.contests.written(cs, Merging.typed.ids(Merging.beside(cs)))) == True{} : Bool}

# `arrange` reads its words as their plain reading says: it accepts a
# command line exactly where every word is `-n`, `--dry-run` or
# `--refile`, wherever each stands, and then it plans rather than acts
# exactly where `-n` or `--dry-run` is among them, and refiles exactly
# where `--refile` is. No word typed to it is passed over.
law arrange_reads_its_words:
  for +ws: List<&2, String>
  {Arrange.accepted(Arrange.ArrangeCmd, Arrange.args.r(ws)) == Bool.pick(Maybe<&2, Arrange.ArrangeCmd>, List.all(~&2, ~String, ~(w => Rev.member(["-n", "--dry-run", "--refile"], w)), ws), Some{Arrange.ArrangeCmd{Bool.or(Rev.member(ws, "-n"), Rev.member(ws, "--dry-run")), Rev.member(ws, "--refile")}}, None{}) : Maybe<&2, Arrange.ArrangeCmd>}

# `arrange` never plans to write over a file: every rename its plan holds,
# in `revisions/` and in `operations/`, goes from one path to a different
# one that nothing in the store was at. Two files holding one document
# want one name, and the second finds it taken when its turn comes.
law arrange_plans_no_overwrite:
  for +refile: Bool
  for +fs: List<&2, Main.Full>
  for +revs: List<&2, T.Split>
  for +ops: List<&2, T.Split>
  for +ls: List<&2, String>
  for +a: Arrange.Arrangement
  for e: {Arrange.arrangement.r(refile, fs, revs, ops, ls) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}
  {Arrange.plan_safe(Arrange.taken(ls), a) == True{} : Bool}

# Without `--refile`, `arrange` renames a revision document only within
# the directory it sits in: a folder a person filed one in is one they
# meant, and the stem's month is `--refile`'s to apply.
law arrange_keeps_a_revision_where_it_sits:
  for +fs: List<&2, Main.Full>
  for +revs: List<&2, T.Split>
  for +ops: List<&2, T.Split>
  for +ls: List<&2, String>
  for +a: Arrange.Arrangement
  for e: {Arrange.arrangement.r(False{}, fs, revs, ops, ls) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}
  {Arrange.all_in_place(Arrange.arrangement.revs(a)) == True{} : Bool}

# `arrange` opens no store holding a revision document whose text does not
# parse, wherever among the store's files it stands, as the Rust tool
# refuses to; the others here pass such a document over. So nothing is
# renamed over a history read only in part.
law arrange_opens_what_parses:
  for +pre: List<&2, Store.Doc>
  for +path: String
  for +id: String
  for +size: Nat
  for +text: String
  for +post: List<&2, Store.Doc>
  for +msg: String
  for hp: {String.ends_with(path, ".rev.txt") == True{} : Bool}
  for hf: {Rev.parse(text) == Fail{msg} : Result<&2, &2, String, Rev.Rev>}
  {Result.is_done(&2, &2, Main.Refused, Unit, Arrange.opened.r(List.append(&2, Store.Doc, pre, Store.Doc{path, id, size, text} <> post))) == False{} : Bool}

# Every file `arrange` walks is counted once in what it prints for its
# directory: renamed, already arranged, left because its name is taken, or
# named by no revision. Nothing it looked at goes unsaid.
law arrange_counts_every_file:
  for +refile: Bool
  for +fs: List<&2, Main.Full>
  for +revs: List<&2, T.Split>
  for +ops: List<&2, T.Split>
  for +ls: List<&2, String>
  for +a: Arrange.Arrangement
  for e: {Arrange.arrangement.r(refile, fs, revs, ops, ls) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}
  {Arrange.accounted(a, revs, ops) == True{} : Bool}

# `prune` reads its words as their plain reading says: it accepts a
# command line exactly where every word is `-n`, `--dry-run` or
# `--fields` and it does not hold both a flag asking for a plan and
# `--fields` — a plan is not on disk, so `--fields` has nothing to say of
# one; and then it plans exactly where `-n` or `--dry-run` is among them,
# and states what is on disk exactly where `--fields` is.
law prune_reads_its_words:
  for +ws: List<&2, String>
  {Arrange.accepted(Prune.PruneCmd, Prune.args.r(ws)) == Bool.pick(Maybe<&2, Prune.PruneCmd>, Bool.and(List.all(~&2, ~String, ~(w => Rev.member(["-n", "--dry-run", "--fields"], w)), ws), Bool.not(Bool.and(Bool.or(Rev.member(ws, "-n"), Rev.member(ws, "--dry-run")), Rev.member(ws, "--fields")))), Some{Prune.PruneCmd{Bool.or(Rev.member(ws, "-n"), Rev.member(ws, "--dry-run")), Rev.member(ws, "--fields")}}, None{}) : Maybe<&2, Prune.PruneCmd>}

# `prune` never removes a revision that work it keeps stands on: of the
# revisions a store holds, one pruning does not keep is named as a parent
# by nothing it keeps — however many passes the fixed point takes, and in
# whatever order a pass let revisions go.
law prune_keeps_what_work_stands_on:
  for +fs: List<&2, Main.Full>
  for +id: String
  for hf: {Rev.member(Main.ids(fs), id) == True{} : Bool}
  for hk: {Rev.member(Main.ids(Prune.kept(fs)), id) == False{} : Bool}
  {Prune.stood_on(Prune.kept(fs), id) == False{} : Bool}

# Every operation document and payload `prune` removes holds a digest
# nothing it keeps needs: named by no revision it keeps, and no forgetting
# document standing in for one that is.
law prune_removes_only_unneeded_content:
  for +fs: List<&2, Main.Full>
  for +revs: List<&2, T.Split>
  for +bs: List<&2, Prune.Body>
  for +ps: List<&2, T.Split>
  {Prune.unneeded(Prune.pruned.content(Prune.plan(fs, revs, bs, ps)), Prune.referenced(Prune.kept(fs), bs)) == True{} : Bool}

# `receive` takes only what this store lacks: every revision it plans to
# write is one this store does not hold, and every document and payload
# one it has nothing under the digest of — and that neither store forgets,
# so a forgetting document is never undone by an arriving original.
law receive_takes_only_what_is_missing:
  for +here: Receive.Side
  for +there: Receive.Side
  {Receive.fresh(here, there, Receive.plan.of(here, there)) == True{} : Bool}

# `receive` moves no bookmark this store has: each it writes is one this
# store lacks, or one it holds at the same target, whose axis joins. Two
# targets for one name is a disagreement, and writes nothing.
law receive_moves_no_bookmark:
  for +here: Receive.Side
  for +there: Receive.Side
  {Receive.names_kept(Receive.rplan.names(Receive.plan.of(here, there)), Receive.side.marks(here)) == True{} : Bool}

# Every original `receive` destroys is one a forgetting document of this
# store or of the source stands in for (decision 0014): among the
# documents themselves, one whose header forgets that very digest.
law receive_destroys_only_what_is_forgotten:
  for +here: Receive.Side
  for +there: Receive.Side
  for +d: String
  for h: {Rev.member(Receive.rplan.destroys(Receive.plan.of(here, there)), d) == True{} : Bool}
  {Bool.or(Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(here)), d), Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(there)), d)) == True{} : Bool}

# `offer` names no private bookmark: the manifest is the one a store with
# none would write, so the file a private key exists to keep back never
# leaves the store as a `name` line.
law offer_names_no_private_bookmark:
  for +prefix: String
  for +s: Prune.Stored
  for +bs: List<&2, Bm.Bookmark>
  for +claims: List<&2, T.Split>
  for +rids: List<&2, T.Split>
  for +nids: List<&2, T.Split>
  {Offer.manifest(prefix, s, bs, claims, rids, nids) == Offer.manifest(prefix, s, Offer.shared(bs), claims, rids, nids) : List<&2, String>}

# `offer` names no private rule either: the manifest is the one a store
# whose `private` rules were never written would have.
law offer_names_no_private_rule:
  for +prefix: String
  for +s: Prune.Stored
  for +bs: List<&2, Bm.Bookmark>
  for +claims: List<&2, T.Split>
  for +rids: List<&2, T.Split>
  for +nids: List<&2, T.Split>
  {Offer.manifest(prefix, s, bs, claims, rids, nids) == Offer.manifest(prefix, Offer.shared_rules(s), bs, claims, rids, nids) : List<&2, String>}

# `export` lays out every path the target's tree places, each once and at
# its own path, whatever kind of file it is: one outcome a path, in path
# order, so a folder laid out without a refusal holds exactly the tree's
# paths — a link where it sits, not where it points.
law export_lays_out_every_path:
  for +ps: List<&2, Export.Placed>
  for +t: Tree.Tree()
  for +fs: List<&2, Main.Full>
  for +ds: List<&2, Store.Doc>
  for +id: String
  for +pays: List<&2, T.Split>
  for +bs: List<&2, Prune.Body>
  {Export.outcome.paths(Export.lay(ps, t, fs, ds, id, pays, bs)) == Export.placed.paths(ps) : List<&2, String>}

# Every bookmark a copy is given is shared, and finds in the copy what it
# names (decision 0062): an export never discloses a private name, and
# never manufactures a dangling bookmark the origin did not have.
law export_names_only_what_travels:
  for +bs: List<&2, Bm.Bookmark>
  for +pt: Export.Pointed
  {Export.travels(Export.travel.names(Export.travel.of(bs, pt)), pt) == True{} : Bool}

# Every rule file a copy is given states a shared rule (decision 0051),
# whatever label it is filed under.
law export_states_no_private_rule:
  for +rs: List<&2, Receive.Ruled>
  {Export.lines.shared(Export.rules.files(rs)) == True{} : Bool}

# Bringing a copy's folder up to date writes over no work nothing has
# recorded: every write or link its plan makes over a regular file is over
# bytes some revision of the copy records, or over the export's own output
# (decision 0030, as 0052 meets it).
law export_writes_over_no_unrecorded_work:
  for +os: List<&2, Export.Outcome>
  for +ss: List<&2, Export.Seen>
  for +dirs: Set()
  for +others: Set()
  for +whole: Bool
  for +rs: List<&2, Export.Rec>
  {Export.steps.safe(Export.steps(os, ss, dirs, others, whole, rs), ss, whole, rs) == True{} : Bool}

# And removes only what the walk found there that some revision records:
# a stray file nobody recorded stays where it is.
law export_removes_only_recorded_files:
  for +ss: List<&2, Export.Seen>
  for +placed: Set()
  for +whole: Bool
  for +rs: List<&2, Export.Rec>
  {Export.removed.ok(Export.removes(ss, placed, whole, rs), ss, whole, rs) == True{} : Bool}

# `export` reads its words as their plain reading says: it accepts a
# command line exactly where the words starting `-` are all `-n`,
# `--dry-run` or `--files-only`, wherever each stands, and one or two words
# do not start `-`; and then it plans exactly where `-n` or `--dry-run` is
# among them, writes the files alone exactly where `--files-only` is, and
# its directory and target, written back as words, are those other words
# in the order they were typed.
law export_reads_its_words:
  for +ws: List<&2, String>
  {Export.args.read(Export.args.r(ws)) == Bool.pick(Maybe<&2, Export.Said>, Bool.and(List.all(~&2, ~String, ~(w => Rev.member(["-n", "--dry-run", "--files-only"], w)), List.filter(~String, ~(w => String.starts_with(w, "-")), ws)), Bool.and(Nat.is_le(1n, List.length(&2, String, List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws))), Nat.is_le(List.length(&2, String, List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws)), 2n))), Some{Export.Said{Bool.or(Rev.member(ws, "-n"), Rev.member(ws, "--dry-run")), Rev.member(ws, "--files-only"), List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws)}}, None{}) : Maybe<&2, Export.Said>}

# An export makes a fresh copy only where nothing is, or where a directory
# holds nothing, and updates only a directory holding something that is a
# store: it never writes into somebody's files.
law export_writes_only_where_a_copy_may_go:
  for +into: String
  for +l: Export.Lst
  for +store: Bool
  {Export.dest.ok(l, store, Export.dest.decide(into, l, store)) == True{} : Bool}

# Every file an export lays out is as the target's tree has it: a file of
# lines holds exactly what `cat` prints there, a file of bytes the payload
# its entry names, copied from a file of the store holding that payload, a
# link is spelled as decision 0040 materialises it, and each runs exactly
# where the tree says it can be run.
law export_lays_each_file_as_the_tree_has_it:
  for +ps: List<&2, Export.Placed>
  for +t: Tree.Tree()
  for +fs: List<&2, Main.Full>
  for +ds: List<&2, Store.Doc>
  for +id: String
  for +pays: List<&2, T.Split>
  for +bs: List<&2, Prune.Body>
  {Export.laid.all(ps, Export.lay(ps, t, fs, ds, id, pays, bs), t, fs, ds, id, pays) == True{} : Bool}

# A copy is assembled from this store's own files: every document and
# forgetting document it carries is one this store holds under that
# digest, and every payload a file of this store holding it.
law export_carries_only_this_stores_files:
  for +held: List<&2, Main.Full>
  for +t: Tree.Tree()
  for +ds: List<&2, Store.Doc>
  for +ps: List<&2, T.Split>
  for +bodies: List<&2, Prune.Body>
  for +rs: List<&2, Receive.Ruled>
  for +bs: List<&2, Bm.Bookmark>
  for +claims: List<&2, T.Split>
  {Export.plan.from(Export.plan.of(held, t, ds, ps, bodies, rs, bs, claims), ds, ps) == True{} : Bool}

# Updating a copy renames none of its revisions (decision 0052): each one
# the copy already holds keeps the stem it was written under, whatever the
# newcomers are called.
law export_renames_nothing_a_copy_holds:
  for +fs: List<&2, Main.Full>
  for +held: List<&2, T.Split>
  for +ex: List<&2, Naming.Named>
  for +id: String
  for +s: String
  for +e: {Arrange.lookup(held, id) == Some{s} : Maybe<&2, String>}
  for m: {Rev.member(Main.ids(fs), id) == True{} : Bool}
  {Arrange.lookup(Export.stems.around(fs, held, ex), id) == Some{s} : Maybe<&2, String>}

# `receive` plans nothing from a store holding a revision document whose
# text does not parse, wherever among its files it stands and whatever
# else it holds — neither into such a store nor out of one — since the part
# of `check` it asks first calls that store broken.
law receive_trusts_what_it_plans_from:
  for +other: Receive.Side
  for +root: String
  for +pre: List<&2, Store.Doc>
  for +path: String
  for +id: String
  for +size: Nat
  for +text: String
  for +post: List<&2, Store.Doc>
  for +revs: List<&2, T.Split>
  for +od: List<&2, Store.Doc>
  for +bs: List<&2, Prune.Body>
  for +ps: List<&2, T.Split>
  for +names: List<&2, String>
  for +rules: List<&2, T.Split>
  for +marks: List<&2, Bm.Bookmark>
  for +claims: List<&2, T.Split>
  for +join: Bool
  for +msg: String
  for +hp: {String.ends_with(path, ".rev.txt") == True{} : Bool}
  for +hf: {Rev.parse(text) == Fail{msg} : Result<&2, &2, String, Rev.Rev>}
  {Bool.or(Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.r(Receive.Side{root, Prune.Stored{List.append(&2, Store.Doc, pre, Store.Doc{path, id, size, text} <> post), revs, od, bs, ps, names, rules}, marks, claims}, other, join)), Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.r(other, Receive.Side{root, Prune.Stored{List.append(&2, Store.Doc, pre, Store.Doc{path, id, size, text} <> post), revs, od, bs, ps, names, rules}, marks, claims}, join))) == False{} : Bool}

# `receive` reads its words as their plain reading says, though it reads
# them in one pass: it accepts a command line exactly where the words
# starting `-` are all `-n`, `--dry-run`, `--fields` or `--join-unrelated`,
# wherever each stands, one word does not start `-`, and it does not hold
# both a flag asking for a plan and `--fields`; and then it plans exactly
# where `-n` or `--dry-run` is among them, states what is on disk exactly
# where `--fields` is, joins unrelated histories only where
# `--join-unrelated` is, and its source is that one other word.
law receive_reads_its_words:
  for +ws: List<&2, String>
  {Receive.args.read(Receive.args.r(ws)) == Bool.pick(Maybe<&2, Receive.Said>, Bool.and(List.all(~&2, ~String, ~(w => Rev.member(["-n", "--dry-run", "--fields", "--join-unrelated"], w)), List.filter(~String, ~(w => String.starts_with(w, "-")), ws)), Bool.and(Nat.is_eq(List.length(&2, String, List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws)), 1n), Bool.not(Bool.and(Bool.or(Rev.member(ws, "-n"), Rev.member(ws, "--dry-run")), Rev.member(ws, "--fields"))))), Some{Receive.Said{Bool.or(Rev.member(ws, "-n"), Rev.member(ws, "--dry-run")), Rev.member(ws, "--fields"), Rev.member(ws, "--join-unrelated"), List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws)}}, None{}) : Maybe<&2, Receive.Said>}

# `offer` accepts a command line exactly where it is one word that does
# not start `-`, and then that word is the directory.
law offer_reads_its_words:
  for +ws: List<&2, String>
  {Offer.args.read(Offer.args.r(ws)) == Bool.pick(Maybe<&2, List<&2, String>>, Bool.and(List.all(~&2, ~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws), Nat.is_eq(List.length(&2, String, ws), 1n)), Some{ws}, None{}) : Maybe<&2, List<&2, String>>}

# Every file an export lays out sits at a path a folder may be given:
# outside the store, not a directory another of the tree's files needs,
# and none a rule of the copy covers, so the copy's own walk offers back
# every file it was given.
law export_lays_out_only_what_the_walk_offers_back:
  for +t: Tree.Tree()
  for +fs: List<&2, Main.Full>
  for +ds: List<&2, Store.Doc>
  for +id: String
  for +pays: List<&2, T.Split>
  for +bs: List<&2, Prune.Body>
  for +rules: List<&2, Folder.Scope>
  {Export.folder.clear(t, rules, Export.folder.r(t, fs, ds, id, pays, bs, rules)) == True{} : Bool}

# Updating a copy destroys only originals a forgetting document of this
# store, or of the copy, stands in for (decision 0014): among the documents
# themselves, one whose header forgets that very digest.
law export_destroys_only_what_is_forgotten:
  for +p: Export.Plan
  for +here: List<&2, Prune.Body>
  for +cst: Prune.Stored
  for +marks: List<&2, Bm.Bookmark>
  for +d: String
  for h: {Rev.member(Export.onto.destroys(Export.onto.of(p, here, cst, marks)), d) == True{} : Bool}
  {Bool.or(Receive.forgot.by(here, d), Receive.forgot.by(Receive.stored.bodies(cst), d)) == True{} : Bool}

# Catching a copy's folder up writes over, and takes away, only bytes the
# copy's own history can give back (decision 0030, as 0052 meets it): every
# file one of its steps writes or links over, and every file it removes,
# holds what `cat` of some revision of the copy reads for some file of its
# tree, or the payload that tree names — `update`'s promise, asked of what
# the copy's revisions record at each path the walk found there. A link it
# takes away is read from the revisions' link statements, as the Rust tool
# reads it, and is not asked about here; nor is a folder that is the
# export's own last output, untouched since, which it rewrites whole.
law export_spares_the_unrecorded:
  for +t: Tree.Tree()
  for +fs: List<&2, Main.Full>
  for +ds: List<&2, Store.Doc>
  for +id: String
  for +pays: List<&2, T.Split>
  for +bs: List<&2, Prune.Body>
  for +rules: List<&2, Folder.Scope>
  for +seen: List<&2, Export.Seen>
  for +walk: List<&2, T.Split>
  for +dirs: Set()
  for +others: Set()
  for +cfs: List<&2, Main.Full>
  for +cds: List<&2, Store.Doc>
  {Export.caught.spares(seen, cfs, cds, Export.caught.r(t, fs, ds, id, pays, bs, rules, seen, walk, dirs, others, False{}, Export.recs(Export.seen.paths(seen), cfs, cds))) == True{} : Bool}

# Every line of an `offer` manifest names a file by the digest the store's
# listing gives the file at that path: each payload, document, revision,
# rule, file of `claims/` and bookmark, group by group, so a fetcher that
# checks a file against its line checks it against what the store holds.
law offer_names_each_file_by_its_digest:
  for +prefix: String
  for +s: Prune.Stored
  for +marks: List<&2, Bm.Bookmark>
  for +claims: List<&2, T.Split>
  for +rids: List<&2, T.Split>
  for +nids: List<&2, T.Split>
  {Offer.manifest.from(prefix, s, marks, claims, rids, nids) == True{} : Bool}

# A path of ASCII is its own normal form C: normalising it, at every
# boundary where a path arrives, changes nothing — which is very nearly
# every path there is.
law nfc_leaves_ascii:
  for +s: String
  for h: {Nfc.ascii(s) == True{} : Bool}
  {Nfc.nfc(s) == s : String}

# Canonical ordering puts every run of marks in order of class: in what
# `order` makes of a decomposed string, no mark follows one of a higher
# class with no starter between them — Unicode's canonical order, stated
# over classes alone rather than by the insertion sort that makes it.
law nfc_orders_marks_by_class:
  for +ms: List<&2, Nfc.Mark>
  {Nfc.canonical.go(Nfc.order(ms), 0) == True{} : Bool}

# And moves no mark past another of its class: for every class, the marks
# of that class in what `order` makes are the ones it was given, in the
# order given — none lost, none added, starters kept in their order. With
# the law above, that is what makes two orders of the same marks one
# string before composition reads them.
law nfc_ordering_keeps_every_mark:
  for +ms: List<&2, Nfc.Mark>
  for +k: U32
  {NfcL.of_class(Nfc.order(ms), k) == NfcL.of_class(ms, k) : List<&2, Nfc.Mark>}

# A character's class is the class of the run that holds it: the lookup
# stops at the first run of the crate's table past the character, and
# finds what a search of every run finds, since the table is in order.
law nfc_class_misses_nothing:
  for +c: U32
  {Nfc.class(Tab.classes(), c) == Nfc.class.scan(Tab.classes(), c) : U32}

# In the crate's tables, neither `/` nor `.` has a combining class, is
# either half of a composition pair or what one makes, or is in any
# character's decomposition. Normalising a path a name at a time, as the
# walk does, is normalising the whole of it only because of this, and a
# link's target resolved inside the folder keeps its shape once
# normalised for the same reason; the law is the tables' part of that.
law nfc_leaves_separators_alone:
  {Bool.and(Nfc.inert(47), Nfc.inert(46)) == True{} : Bool}

# The walk yields a path once and loses none. Two names a filesystem tells
# apart can be one path in normal form C, and the walk keeps one file for
# it: no two files it yields in a row share a path — and it yields them in
# path order — and every path a file it found is at, a file it yields is
# at.
law the_walk_yields_a_path_once:
  for +fs: List<&2, Folder.Found>
  {Bool.and(Folder.apart(Folder.distinct(fs)), NfcL.paths_held(fs, Folder.distinct(fs))) == True{} : Bool}

# A file is opened where the folder spells it. The walk names a path in
# normal form C, and the filesystem may spell it otherwise, so a read asks
# the listing: the name it opens is one whose normal form is the path, or,
# where the listing gives none, the path as it is.
law the_folder_spells_what_is_opened:
  for +ls: List<&2, String>
  for +want: String
  {Bool.or(String.eq(Folder.spelling(ls, want), want), String.eq(Nfc.nfc(Folder.spelling(ls, want)), want)) == True{} : Bool}

# A name that cannot be spelled is refused. Whatever a directory holds —
# directories, files, links whatever their targets say, the rest — the
# lines the host writes for it, read back, refuse each name that is not
# UTF-8 once, where it is on disk under the directory, in
# `WorkingError::NotUtf8`'s words, and nothing else; no rule is asked,
# since none can name it.
law a_name_that_cannot_be_spelled_is_refused:
  for es: List<&2, NfcL.Listed>
  for +prefix: String
  for +dir: String
  {Folder.unkeyed(Folder.unspelled(NfcL.listed.lines(es), prefix, dir)) == List.reverse(&2, T.Split, NfcL.listed.refused(es, dir)) : List<&2, T.Split>}

# `fetch` reads its words as their plain reading says, though it reads them
# in one pass: it accepts a command line exactly where the words starting
# `-` are all `--join-unrelated` or `--fields`, wherever each stands, and
# one word does not start `-`; and then it joins unrelated histories
# exactly where `--join-unrelated` is among them, states what it wrote
# exactly where `--fields` is, and the URL is that one other word.
law fetch_reads_its_words:
  for +ws: List<&2, String>
  {Fetch.args.read(Fetch.args.r(ws)) == Bool.pick(Maybe<&2, Fetch.Said>, Bool.and(List.all(~&2, ~String, ~(w => Rev.member(["--join-unrelated", "--fields"], w)), List.filter(~String, ~(w => String.starts_with(w, "-")), ws)), Nat.is_eq(List.length(&2, String, List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws)), 1n)), Some{Fetch.Said{Rev.member(ws, "--join-unrelated"), Rev.member(ws, "--fields"), List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws)}}, None{}) : Maybe<&2, Fetch.Said>}

# A URL `fetch` accepts is cut into the directory the manifest sits in and
# the manifest's own name: put back together they are the URL, the
# directory ends with `/`, and the name is not empty and holds no `/`. So
# the directory every path of the manifest is asked for under is the URL up
# to its last `/`, that included (decision 0052), and nothing after it.
law fetch_asks_under_the_manifests_directory:
  for +url: String
  for r: String
  for m: String
  for e: {Fetch.addressed.r(url) == Done{Fetch.Addressed{r, m}} : Result<&2, &2, Main.Refused, Fetch.Addressed>}
  {Bool.and(String.eq(String.append(r, m), url), Bool.and(String.ends_with(r, "/"), Bool.and(Bool.not(String.is_empty(m)), List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(m))))) == True{} : Bool}

# Every path a pass of `fetch` asks the host for is one the manifest names:
# nothing it asks for is a path it made up.
law fetch_asks_only_for_what_the_manifest_names:
  for h: Fetch.Here
  for +os: List<&2, Offer.Offered>
  {Main.all_held(T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), os), Fetch.asked(Fetch.steps.of(Fetch.plan.of(h, os)))) == True{} : Bool}

# A document of text is filed only where the text that arrived hashes to
# the digest the manifest's line gave it (decision 0048): whatever the host
# answered, what `fetch` files is what was offered.
law fetch_files_only_text_that_hashes_to_its_line:
  for +root: String
  for +held: List<&2, String>
  for +o: Offer.Offered
  for g: Fetch.Got
  for at: String
  for t: String
  for e: {Fetch.got.text(root, held, o, g) == Fetch.Land.File{at, t} : Fetch.Land}
  {Sha.digest(Utf8.encode(t)) == Fetch.entry.digest(o) : String}

# And a file that arrives whole — a payload, or another tool's — is renamed
# from where it was staged into the store only where the host found its
# bytes to hash to the digest its line gave.
law fetch_lands_a_file_only_where_it_hashes_to_its_line:
  for +folder: String
  for +name: String
  for +o: Offer.Offered
  for g: Fetch.Got
  for f: String
  for a: String
  for b: String
  for e: {Fetch.got.pull(folder, name, o, g) == Fetch.Land.Move{f, a, b} : Fetch.Land}
  {g == Fetch.Got.Pulled{Fetch.entry.digest(o)} : Fetch.Got}

# A payload lands under the very digest the host found its bytes to have:
# its name here is what it is, and never a name the publisher gave it.
law fetch_files_a_payload_under_what_it_hashes_to:
  for +root: String
  for +o: Offer.Offered
  for +g: Fetch.Got
  for f: String
  for a: String
  for b: String
  for +e: {Fetch.pay.land(root, o, g) == Fetch.Land.Move{f, a, b} : Fetch.Land}
  {Fetch.Got.Pulled{b} == g : Fetch.Got}
