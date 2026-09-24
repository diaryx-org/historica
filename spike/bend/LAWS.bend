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
import ./main.bend as Main
import ./similar.bend as Sim
import ./folder.bend as Folder
import ./bookmark.bend as Bm
import ./store.bend as Store

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
