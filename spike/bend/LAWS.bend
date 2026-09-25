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
import ./arrange_lemmas.bend as ArrangeL
import ./prune_lemmas.bend as PruneL
import ./receive_lemmas.bend as ReceiveL
import ./offer_lemmas.bend as OfferL
import ./utf8.bend as Utf8
import ./manifest_lemmas.bend as ManL
import ./fetching_lemmas.bend as FetchingL
import ./fetchplan_lemmas.bend as FPlanL
import ./escape_lemmas.bend as EscL
import ./init_lemmas.bend as InitL
import ./utf8_lemmas.bend as Utf8L
import ./finding_lemmas.bend as FindL
import ./skip_lemmas.bend as SkipL

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

# And it gives a file of bytes the size the host stated for its payload.
# The host answers one stat line for each payload it located; where it
# located a payload `d` — sixty-four characters with no space among them,
# as a digest is — after others, and answered its stat with `d`, a space
# and a size, a file of bytes with that payload whose size was unknown, one
# that went or one that came, is shown with that size, and nothing else
# about it changes.
law diff_sizes_what_the_host_stated:
  for +f1: List<&2, T.Split>
  for +s1: List<&2, String>
  for hl: {List.length(&2, T.Split, f1) == List.length(&2, String, s1) : Nat}
  for +d: String
  for hn: {Rev.member(T.map(~T.Split, ~String, ~(x => Main.split.head(x)), f1), d) == False{} : Bool}
  for hd: {String.length(d) == 64n : Nat}
  for hs: {T.all_chars(~(c => Bool.not(Char.is_eq(c, ' '))), d) == True{} : Bool}
  for +p: String
  for +f2: List<&2, T.Split>
  for +size: String
  for +n: Nat
  for hz: {Nat.read(size) == Some{n} : Maybe<&2, Nat>}
  for +s2: List<&2, String>
  for +from: Maybe<&2, String>
  for +to: Maybe<&2, String>
  for +modes: Maybe<&2, T.Split>
  for +targets: Maybe<&2, Main.Retarget>
  {Main.sized(Main.sizes.read(List.append(&2, T.Split, f1, T.Split{d, p} <> f2), List.append(&2, String, s1, (d ++ (" " ++ size)) <> s2)), [Main.Compared{from, to, Some{Main.Side.Whole{d, None{}}}, None{}, modes, targets}, Main.Compared{from, to, None{}, Some{Main.Side.Whole{d, None{}}}, modes, targets}]) == [Main.Compared{from, to, Some{Main.Side.Whole{d, Some{n}}}, None{}, modes, targets}, Main.Compared{from, to, None{}, Some{Main.Side.Whole{d, Some{n}}}, modes, targets}] : List<&2, Main.Compared>}

# `diff` over the folder plans each path — whether the position's file is
# replayed, whether the folder's is read — from nothing the store holds but
# the `edit` documents it asks for before it plans: any documents that
# answer each digest it asks for as all of the store's do, with the same
# text under it or with none, give the plan all of the store's give.
law diff_folder_plans_by_the_edits_it_fetches:
  for +dg: Map<&2, String>
  for +os: Map<&2, T.Split>
  for +eds: List<&2, Store.Doc>
  for +all: List<&2, Store.Doc>
  for +hs: List<&2, Main.Here>
  for +h: {FetchL.agree(eds, all, Main.edits.asked(os, hs)) == True{} : Bool}
  {Main.plans(dg, os, eds, hs) == Main.plans(dg, os, all, hs) : List<&2, Main.Planned>}

# `diff` asks the host about the payloads it shows and nothing else: a
# digest is among those it asks about exactly where a comparison it shows
# has a side that is a file of bytes with that payload.
law diff_asks_every_payload_it_shows:
  for +cs: List<&2, Main.Compared>
  for +d: String
  {Rev.member(Main.payloads.asked(cs), d) == FetchL.shows.bytes(cs, d) : Bool}

# And it asks about each once: no payload is among them twice.
law diff_asks_each_payload_once:
  for +cs: List<&2, Main.Compared>
  {FetchL.each_once(Main.payloads.asked(cs)) == True{} : Bool}

# And it asks the stat of a payload only at the path the host located that
# payload at — never of one the host could not find, which it answers `-`
# for — so that each size it then believes is looked for where it is.
law diff_stats_where_each_payload_was_found:
  for +root: String
  for +ds: List<&2, String>
  for +at: List<&2, String>
  {FetchL.located.each(ds, at, Main.sizes.of(root, ds, at)) == True{} : Bool}

# What a resolution keeps is found. After the documents a reading command
# fetches, it asks for the ones `kept_digests` names; and where the store
# answers each of those with a document under that very digest, every
# `keep` of every document among the first that reads as a resolution
# finds a document under the digest it names, so assembling one against
# all of them never refuses for want of a document it keeps.
law reading_finds_what_resolutions_keep:
  for +ds: List<&2, Store.Doc>
  for +more: List<&2, Store.Doc>
  for +h: {Main.all_held(FetchL.doc_ids(more), Main.kept_digests(ds)) == True{} : Bool}
  {FetchL.kept.found(List.append(&2, Store.Doc, ds, more), ds) == True{} : Bool}

# The digest a statement gives a file is read along the first-parent line
# back from the folder's position, the nearest revision on it to state the
# file being the one believed. That line is what `chain` walks, whole: it
# begins at the revision named, each revision after is the first parent of
# the one before — every one a revision the store holds — and it stops
# where the line does, after a revision with no parent or a first parent
# the store does not hold; of a name the store does not hold it walks none.
# The one other place it may stop is after 1 + n revisions of a store of n,
# which only a line that comes back round to itself could reach.
law chain_follows_first_parents:
  for +fs: List<&2, Main.Full>
  for +id: String
  {Bool.and(Main.first_parents(fs, Main.chain(fs, Some{id}), Some{id}), Bool.or(Main.line.stops(fs, Main.chain(fs, Some{id}), Some{id}), Nat.is_eq(List.length(&2, Main.Full, Main.chain(fs, Some{id})), 1n+List.length(&2, Main.Full, fs)))) == True{} : Bool}

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

# `log` lists what its span names — the revisions it goes on with before
# `--author`, `--grep`, `--since`, `--until` and `--limit` narrow them.
# With a target, every one is a revision the store holds: the target,
# wherever the store holds it, and otherwise only parents of revisions it
# lists, so that in a store whose parents run back without a cycle it
# lists only the target's ancestry. And where the store files each
# revision under a digest no other has, it leaves out no parent the store
# holds of a revision it lists, however many parents a merge joins, so
# that it lists every revision a line of parents the store holds leads
# back to from the target. With `a..b`, it lists what `log b` lists and
# `log a` does not: nothing `log a` lists, `a` itself among them, and
# everything else `log b` lists.
law log_lists_its_span:
  for +fs: List<&2, Main.Full>
  for +a: String
  for +b: String
  {Bool.and(Main.span.from_ok(fs, b, Main.span.shown(fs, Main.Span.From{b})), Main.span.range_ok(fs, a, b, Main.span.shown(fs, Main.Span.Between{a, b}))) == True{} : Bool}

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

# `name` reads its words as their plain reading says, whatever order they
# come in. `--delete` and `--fields` are asked for where they are among the
# words. The bookmark is pinned where the last of the `--revision` and
# `--change` among them is `--revision`; it is asked to be private or
# shared as the last of the `--private` and `--shared` among them says, and
# neither where there is neither. Those four flags are kept as they were
# typed, in order, for `--delete` to refuse; and every word that is none of
# the six — one beginning `-` too — is kept, in order, for the bookmark,
# the target and the path.
law name_reads_its_words:
  for +ws: List<&2, String>
  {Main.name.args(ws, Main.NameCmd{False{}, None{}, False{}, False{}, Nil{}, Nil{}}) == Main.NameCmd{String.eq(Maybe.default(&2, String, List.last(&2, String, List.filter(~String, ~(w => Rev.member(["--revision", "--change"], w)), ws)), ""), "--revision"), Maybe.map(&2, String, Bool, x => String.eq(x, "--private"), List.last(&2, String, List.filter(~String, ~(w => Rev.member(["--private", "--shared"], w)), ws))), Rev.member(ws, "--delete"), Rev.member(ws, "--fields"), List.filter(~String, ~(w => Rev.member(["--revision", "--change", "--private", "--shared"], w)), ws), List.filter(~String, ~(w => Bool.not(Rev.member(["--revision", "--change", "--private", "--shared", "--delete", "--fields"], w))), ws)} : Main.NameCmd}

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

# The bookmark `name` sets points where it was asked to: at what its
# target names as every command reads it — the revision `resolve` gives
# for the spelling. Pinned with `--revision`, it points at that revision;
# given a target alone, at the change that revision carries; given a path,
# at the file `show` names at that revision and path. It has the name
# given, which stays under `names/`; and it is private as `--private` or
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
  for +id: String
  for ei: {Main.resolve(fs, bs, spelling) == Done{id} : Result<&2, &2, String, String>}
  {Main.name.points(fs, bs, n, id, path, pin, axis, b) == True{} : Bool}

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

# A bookmark's file is `names/`, its name and `.txt` — where `name` writes
# it — and that path reads back as the bookmark it is: for any name
# `Bm.name_ok` accepts, `Bm.name` cuts off the directory and the suffix and
# nothing of the name.
law bookmark_file_reads_back:
  for +n: String
  for ok: {Bm.name_ok(n) == True{} : Bool}
  {Bm.name("names/" ++ n ++ ".txt") == Some{n} : Maybe<&2, String>}

# `names` lists every bookmark once, in name order. The store's bookmarks
# are read sorted by name, each no smaller than the one before it.
law bookmarks_read_in_name_order:
  for +ps: List<&2, String>
  {SortL.sorted(~Main.Named, ~(n => Main.named.name(n)), Main.bookmarks.order(ps)) == True{} : Bool}

# And none is dropped, repeated or made up on the way: under each name are
# exactly the paths the store lists under `names/` that `Bm.name` reads as
# that name, each paired with its own path, as many and in the order the
# store lists them — any other path it lists is passed over.
law bookmarks_read_each_once:
  for +ps: List<&2, String>
  for +k: String
  {SortL.keyed(~Main.Named, ~(n => Main.named.name(n)), k, Main.bookmarks.order(ps)) == Main.bookmark_files(ps, k) : List<&2, Main.Named>}

# `names` prints a line for each bookmark it read, in the order read, each
# beginning with the bookmark's name and two spaces, and, for a revision
# pin or a change, ending with `  ->  ` and where it resolves; with no
# bookmark, it says `no bookmarks here yet`.
law names_lists_each_bookmark:
  for +fs: List<&2, Main.Full>
  for bs: List<&2, Bm.Bookmark>
  {Main.names.begun(fs, bs, Main.names.said(fs, bs)) == True{} : Bool}

# Where `names` says a revision pin resolves, where the store holds the
# revision, is an abbreviation of that revision's digest: a prefix of it,
# its first eight characters at least, that no other digest the store holds
# of the same length begins with. A pin the store lacks is `(not here
# yet)`. A change with one current revision is the same abbreviation of
# that revision, which the store holds; any other, a reason in parentheses.
law names_resolves_to_held:
  for +fs: List<&2, Main.Full>
  for +here: Maybe<&2, Tree.Tree()>
  for t: Bm.Target
  {Main.names.held(fs, t, Main.names.resolution(Main.history(fs), Main.ids(fs), here, t)) == True{} : Bool}

# `log --fields` lists only what it was asked for: its first line is its
# header, `historica-log-1`, and each line after it begins with the whole
# digest, and a space, of a revision the span shows that every filter
# admits — never more of them than `--limit` allows. The walk that orders
# them never lists a revision it was not shown.
law log_fields_lists_what_it_keeps:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for +sp: Main.Span
  for +shown: List<&2, Main.Full>
  for +fl: Main.Filter
  for +limit: Maybe<&2, Nat>
  {Main.log.fields.ok(Main.log.shown.lines(fs, bs, sp, shown, fl, True{}, limit), Main.log.admitted(fl, shown), limit) == True{} : Bool}

# A log entry counts what its revision did to the file set as the revision
# states it: the files added, moved, dropped and edited are how many `add`,
# `move`, `drop` and `edit` facts it states, and the modes, links and bytes
# stored are how many `mode`, `link` and `bytes` facts it states about a
# file no `add` fact names — each under its own word, in that order. The
# files it added are asked of a `Set` built from them, which this takes, as
# its one assumption, to hold exactly the strings it was built from.
law log_counts_each_fact:
  for ~sets: @xs: List<&2, String> -> @x: String -> {Main.was_added(Set.from_list(xs), x) == Rev.member(xs, x) : Bool}
  for +facts: List<&2, Rev.Header>
  {Main.tree_facts.figures(facts) == [Main.Figure{"added", Main.facts.stated(facts, "add")}, Main.Figure{"moved", Main.facts.stated(facts, "move")}, Main.Figure{"mode", Main.facts.unadded(facts, "mode")}, Main.Figure{"link", Main.facts.unadded(facts, "link")}, Main.Figure{"dropped", Main.facts.stated(facts, "drop")}, Main.Figure{"edited", Main.facts.stated(facts, "edit")}, Main.Figure{"stored", Main.facts.unadded(facts, "bytes")}] : List<&2, Main.Figure>}

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

# Where work is joined, `status` says each contest the tree merge found
# but a path several files claim, once and in its order, on a line of its
# own naming the file contested by the first eight characters of its name;
# where one revision or none is the position, it says none, since a
# contest deeper in the graph was settled when its merge was recorded.
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

# `status` tells its survey of each path it compares once, in order, and
# the folder's digest it gives for each path is the host's answer for that
# path, from the answers the host gave for the files it was asked about,
# and none for a path it was not. What it tells of a file the parents
# being joined leave differently is `status_leaves_a_disputed_file_unsettled`.
law status_surveys_each_path:
  for +t: Tree.Tree()
  for +stats: List<&2, String>
  for +bf: Map<&2, String>
  for +reads: Map<&2, List<&2, U32>>
  for +props: List<&2, Main.Proposal>
  for +hs: List<&2, Main.Here>
  {Main.status.surveys(Main.regular_paths(hs), stats, hs, Main.status.seens(t, Main.stats.map(Main.regular_paths(hs), stats, Map.new(&2, String)), bf, reads, props, hs)) == True{} : Bool}

# Where the parents being joined leave a file of lines differently —
# `record::joined_content`'s `-` — there is no digest to settle it by,
# whatever the folder holds. Of a file at its path the survey is told it
# is edited, emptied, refused or still holding lines the renderer wrote —
# emptied only where the file holds no bytes, and edited only where it
# holds some; of a link or nothing there, that the file is dropped, with
# no content an arrival could be matched to as its move. These are what
# `record` states or refuses the merge by. `status` prints the edit, the
# refusal and the drop, but its report, like the Rust tool's, has no line
# for an emptied file, so a disputed file left empty is shown as nothing
# differing; `docs/tasks` has that.
law status_leaves_a_disputed_file_unsettled:
  for +t: Tree.Tree()
  for +dg: Map<&2, String>
  for +bf: Map<&2, String>
  for -bf2: Map<&2, String>
  for +reads: Map<&2, List<&2, U32>>
  for +props: List<&2, Main.Proposal>
  for +path: String
  for +f: String
  for +q: String
  for +y: Maybe<&2, String>
  for +g: Maybe<&2, Tree.Target>
  for +m: Tree.Mode
  for found: Maybe<&2, Folder.Found>
  for h: {Map.get(String, SNil{}, bf, f) == (bf2, "-") : Map<&2, String> & String}
  {Main.disputed.said(path, f, found, Sv.seen(Main.status.seen(t, dg, bf, reads, props, Main.Here{path, Some{Tree.Entry{f, q, Tree.Lines{}, y, g, m}}, found}))) == True{} : Bool}

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

# Where several parents are joined, `status` compares each file with what
# the parents' readings of it join to, as `record::joined_content` joins
# them: the digest every parent that mentions the file reads, the empty
# digest where none mentions it, and `-` where two read it differently —
# one digest for each file it compares, in the order compared.
law status_joins_what_it_reads:
  for hs: List<&2, Main.Here>
  for +fs: List<&2, Main.Full>
  for +ds: List<&2, Store.Doc>
  for +ps: List<&2, String>
  for +xs: List<&2, T.Split>
  for h: {Main.status.joined.pairs(fs, ds, ps, hs) == Done{xs} : Result<&2, &2, String, List<&2, T.Split>>}
  {Main.joined.files(fs, ds, ps, hs, xs) == True{} : Bool}
# `record` refuses a link left dangling. Wherever a link of the position
# stands among its files, if the record goes on, keeps that link and drops
# the file it names, the folder holds a link at the link's path, one this
# format can hold: a link the record keeps that names a file it drops, with
# no such link in the folder, is refused.
law record_refuses_a_dangling_link:
  for +t: Tree.Tree()
  for +looked: Tree.Tree()
  for +held: Set()
  for +walked: List<&2, T.Split>
  for +ss: List<&2, Sv.Seen>
  for +moves: List<&2, T.Split>
  for hd: {Sv.planned.dangles(Sv.planned(t, looked, held, walked, ss, moves)) == None{} : Maybe<&2, String>}
  for +pre: Tree.Tree()
  for +post: Tree.Tree()
  for +f: String
  for +p: String
  for +k: Tree.FileKind
  for +y: Maybe<&2, String>
  for +named: String
  for +m: Tree.Mode
  for ht: {t == List.append(&2, Tree.Entry, pre, Tree.Entry{f, p, k, y, Some{Tree.Reference{named}}, m} <> post) : Tree.Tree()}
  for hn: {Sv.has(Sv.planned.gone(Sv.planned(t, looked, held, walked, ss, moves)), named) == True{} : Bool}
  for hf: {Sv.has(Sv.planned.gone(Sv.planned(t, looked, held, walked, ss, moves)), f) == False{} : Bool}
  {Sv.link_found(ss, p) == True{} : Bool}

# `status` refuses only what the folder holds that the position cannot
# take. What its walk could not take comes first, as the walk found it and
# in its order; after that, a path is refused only where the folder holds
# a link there whose target this format cannot hold, or a file the
# position recorded as lines whose bytes are no longer text, and the
# refusal says which — never a path only the position holds, and never a
# file of bytes or a link it can hold.
law status_refuses_what_the_folder_holds:
  for +t: Tree.Tree()
  for +held: Set()
  for +walked: List<&2, T.Split>
  for +ss: List<&2, Sv.Seen>
  {Sv.refused_after(walked, ss, Sv.survey.refused(Sv.survey(t, held, walked, ss))) == True{} : Bool}

# A kind is stated only for a file arriving. Decision 0017 fixes a file's
# kind when it is added, so where `record` goes on, every `--lines` and
# `--bytes`, wherever it stands among them, names a path the restriction
# covers, and no file of the position is at that path: a kind for a file
# already there is refused, since it would restate what was fixed at the
# add, and so is one for a path the record is not looking at.
law record_states_a_kind_only_for_an_arrival:
  for +only: List<&2, String>
  for +t: Tree.Tree()
  for +pre: List<&2, T.Split>
  for +p: String
  for +k: String
  for +post: List<&2, T.Split>
  for e: {Sv.kind_fault(only, t, List.append(&2, T.Split, pre, T.Split{p, k} <> post)) == None{} : Maybe<&2, String>}
  for +g: String
  {Bool.and(Sv.covers(only, p), Bool.not(Sv.maybe_eq(Tree.path(t, g), Some{p}))) == True{} : Bool}

# `record` writes one `move` line for each file moved. However the
# renames a person stated follow one another, the lines give a file the
# renames moved and this record keeps exactly one place, the last one the
# renames put it, and give a file it drops, or one no rename moved, none.
law record_moves_each_file_once:
  for +ms: List<&2, T.Split>
  for +gone: Set()
  for +f: String
  {Sv.moves_of(Sv.moved.final(ms, gone), f) == Bool.pick(List<&2, String>, Sv.has(gone, f), Nil{}, Sv.maybe_list(Sv.last_move(ms, f))) : List<&2, String>}

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
# holds (decision 0010). Of the timestamps it is handed, it warns exactly
# where one of them names a later instant than the clock reads, whichever
# of them that is; and it says nothing otherwise, as where it is handed
# none.
law record_compares_with_the_latest:
  for +now: String
  for +ws: List<&2, String>
  {Maybe.is_some(&2, String, Main.clock.warning(now, Naming.newest(ws, None{}))) == Naming.later_than(ws, now) : Bool}

# `abandon` takes a reason exactly where it says something. The reason is
# the only thing a tombstone carries, so one that is empty or nothing but
# whitespace is refused, and any other is taken.
law abandon_takes_a_reason_that_says_something:
  for +m: String
  {Result.is_done(&2, &2, Main.Refused, Unit, Main.reason.r(m)) == Bool.not(Naming.every(~Naming.is_space, m)) : Bool}

# `record` restricted to some paths names only what is there. It goes on
# exactly where each path a person names covers, as a restriction to it
# alone would, something the folder holds, the position holds or the
# stated renames put there — the path itself, or one beneath it as a
# directory — whatever the rules in `history/skipped/` say.
law record_names_only_what_is_there:
  for +rules: List<&2, Folder.Scope>
  for +named: List<&2, String>
  for +folder: List<&2, String>
  for +was: List<&2, String>
  for +placed: List<&2, String>
  {Result.is_done(&2, &2, Main.Refused, Unit, Main.named.r(rules, named, folder, was, placed)) == Sv.each_covers(named, List.append(&2, String, folder, List.append(&2, String, was, placed))) : Bool}

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

# And `--at` puts each file where a person said. Where `record` goes on
# with `--at` and no `--move` — which, naming a path rather than a file,
# could move one again — each file of the position is at the path the last
# `--at` naming it gave, and a file none names is where it was.
law a_rename_puts_each_file_where_it_was_said:
  for +t: Tree.Tree()
  for +ats: List<&2, T.Split>
  for +t2: Tree.Tree()
  for +moved: List<&2, T.Split>
  for e: {Main.placed.r(t, ats, Nil{}) == Done{Main.Placed{t2, moved}} : Result<&2, &2, Main.Refused, Main.Placed>}
  for +g: String
  for hg: {Tree.holds(t, g) == True{} : Bool}
  {Tree.path(t2, g) == Maybe.or(&2, String, Sv.last_move(ats, g), Tree.path(t, g)) : Maybe<&2, String>}

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
# holds where it lands. Where its target is one this format can hold, and
# lands, folded against the link's own directory and put in normal form C,
# on a path no two files of the position share and where any arrival has
# its identifier minted, `record` writes the link as `file:` and an
# identifier only for the file minted there, or for the one file of the
# position there that the record keeps — never for a file it drops, nor
# for any other.
law a_link_refers_only_to_what_the_revision_states:
  for +mint: List<&2, T.Split>
  for +t: Tree.Tree()
  for +gone: Set()
  for +arriving: Set()
  for +path: String
  for +target: String
  for +at: String
  for +f: String
  for hr: {Sv.resolved(path, target) == Some{at} : Maybe<&2, String>}
  for hl: {Sv.link_fault(target) == None{} : Maybe<&2, String>}
  for ho: {Tree.at_most_one(Tree.at(t, at)) == True{} : Bool}
  for hm: {Bool.or(Bool.not(Sv.has(arriving, at)), Maybe.is_some(&2, String, Main.lookup(mint, at))) == True{} : Bool}
  for e: {Main.link.spelled(mint, t, Sv.observed(t, gone, arriving, path, target)) == "file:" ++ f : String}
  {Bool.or(Sv.maybe_eq(Main.lookup(mint, at), Some{f}), Bool.and(Rev.member(Tree.at(t, at), f), Bool.not(Sv.has(gone, f)))) == True{} : Bool}

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

# `record` reads its words as their plain reading says, one at a time.
# Whatever words it has read, one flag more says one thing more and leaves
# the rest as it was: `-m` or `--message` and the word after it is the
# message, and `--onto` and the word after it what to record onto, the
# last of each counting; `--merge` adds a revision to merge, and `--bytes`
# and `--lines` a path given that kind, after those before it; `--accept`
# adds a path accepted; and `-n`, `--dry-run` and `--fields` ask for
# what they name. The word after a flag that takes one is its value,
# whatever it is, and such a flag with no word after it is refused.
law record_reads_its_words:
  for +args: List<&2, String>
  for +o: Maybe<&2, String>
  for +ms: List<&2, String>
  for +ac: List<&2, String>
  for +at: List<&2, T.Split>
  for +mv: List<&2, T.Split>
  for +ks: List<&2, T.Split>
  for +ns: List<&2, String>
  for +d: Bool
  for +f: Bool
  for +mg: Maybe<&2, String>
  for +e: {Main.record.args.r(args) == Done{Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}} : Result<&2, &2, Main.Refused, Main.RecordCmd>}
  for +v: String
  {[Main.record.args.r(List.append(&2, String, args, ["-m", v])), Main.record.args.r(List.append(&2, String, args, ["--message", v])), Main.record.args.r(List.append(&2, String, args, ["--onto", v])), Main.record.args.r(List.append(&2, String, args, ["--merge", v])), Main.record.args.r(List.append(&2, String, args, ["--accept", v])), Main.record.args.r(List.append(&2, String, args, ["--bytes", v])), Main.record.args.r(List.append(&2, String, args, ["--lines", v])), Main.record.args.r(List.append(&2, String, args, ["-n"])), Main.record.args.r(List.append(&2, String, args, ["--dry-run"])), Main.record.args.r(List.append(&2, String, args, ["--fields"])), Main.record.args.r(List.append(&2, String, args, ["-m"])), Main.record.args.r(List.append(&2, String, args, ["--onto"])), Main.record.args.r(List.append(&2, String, args, ["--merge"])), Main.record.args.r(List.append(&2, String, args, ["--accept"])), Main.record.args.r(List.append(&2, String, args, ["--at"])), Main.record.args.r(List.append(&2, String, args, ["--move"])), Main.record.args.r(List.append(&2, String, args, ["--bytes"])), Main.record.args.r(List.append(&2, String, args, ["--lines"]))] == [Done{Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, Some{v}}}, Done{Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, Some{v}}}, Done{Main.RecordCmd{Some{v}, ms, ac, at, mv, ks, ns, d, f, mg}}, Done{Main.RecordCmd{o, List.append(&2, String, ms, [v]), ac, at, mv, ks, ns, d, f, mg}}, Done{Main.RecordCmd{o, ms, v <> ac, at, mv, ks, ns, d, f, mg}}, Done{Main.RecordCmd{o, ms, ac, at, mv, List.append(&2, T.Split, ks, [T.Split{v, "bytes"}]), ns, d, f, mg}}, Done{Main.RecordCmd{o, ms, ac, at, mv, List.append(&2, T.Split, ks, [T.Split{v, "lines"}]), ns, d, f, mg}}, Done{Main.RecordCmd{o, ms, ac, at, mv, ks, ns, True{}, f, mg}}, Done{Main.RecordCmd{o, ms, ac, at, mv, ks, ns, True{}, f, mg}}, Done{Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, True{}, mg}}, Fail{Main.Refused{2, "`-m` wants a value"}}, Fail{Main.Refused{2, "`--onto` wants a value"}}, Fail{Main.Refused{2, "`--merge` wants a value"}}, Fail{Main.Refused{2, "`--accept` wants a value"}}, Fail{Main.Refused{2, "`--at` wants a value"}}, Fail{Main.Refused{2, "`--move` wants a value"}}, Fail{Main.Refused{2, "`--bytes` wants a value"}}, Fail{Main.Refused{2, "`--lines` wants a value"}}] : List<&2, Result<&2, &2, Main.Refused, Main.RecordCmd>>}

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

# What `record` states a file holds is what the folder holds there. Where
# it reads what it edits of the position, of each file it drafts content
# for, an edit applied to the store's replay of that file at the position
# gives the lines the folder holds, text is the bytes the folder holds,
# and a payload is named by the digest the folder's walk gave its path; a
# record from one position states no resolution. Where the parents being
# joined leave a file differently, `record_resolves_as_the_walk_proposes`.
law record_states_the_folder:
  for +older: List<&2, Main.Full>
  for +ds: List<&2, Store.Doc>
  for +left: String
  for +dg: Map<&2, String>
  for +reads: Map<&2, List<&2, U32>>
  for +t: Tree.Tree()
  for +hs: List<&2, Main.Here>
  for +ks: List<&2, T.Split>
  for +moves: List<&2, T.Split>
  for +obs: List<&2, Sv.Obs>
  for +ls: List<&2, String>
  for +mint: List<&2, T.Split>
  for +bs: List<&2, Main.Before>
  for +e: {Main.befores.r(older, ds, left, Main.edited.lines(Sv.edited(obs), hs)) == Done{bs} : Result<&2, &2, Main.Refused, List<&2, Main.Before>>}
  {Main.contents.state(older, ds, left, dg, reads, Main.drafted.contents(Main.drafted.of(bs, t, hs, dg, reads, ks, moves, obs, ls, mint))) == True{} : Bool}

# Decision 0032: where the parents being joined leave a file of lines
# differently, what `record` states of it is the written form of the
# resolution `Conflict.resolve` makes of the walk of those parents — the
# reading `merge` lays out, `Main.joined` — and the lines the folder
# holds, which `merge_resolution_reads_back` assembles back to those lines.
law record_resolves_as_the_walk_proposes:
  for +fs: List<&2, Main.Full>
  for +ds: List<&2, Store.Doc>
  for +ps: List<&2, String>
  for +reads: Map<&2, List<&2, U32>>
  for +dg: Map<&2, String>
  for +t: Tree.Tree()
  for +hs: List<&2, Main.Here>
  for +ks: List<&2, T.Split>
  for +moves: List<&2, T.Split>
  for +obs: List<&2, Sv.Obs>
  for +ls: List<&2, String>
  for +mint: List<&2, T.Split>
  for +bs: List<&2, Main.Before>
  for +e: {Main.joinings.r(fs, ds, ps, Main.edited.lines(Sv.edited(obs), hs)) == Done{bs} : Result<&2, &2, Main.Refused, List<&2, Main.Before>>}
  {Main.contents.resolve(fs, ds, ps, reads, Main.drafted.contents(Main.drafted.of(bs, t, hs, dg, reads, ks, moves, obs, ls, mint))) == True{} : Bool}

# What `record` writes is named as it says. The revision is filed under
# the name decision 0019 composes from its moment, its message and its
# change, or a longer one beginning with it, and under that name exactly
# where no revision the store holds has it.
law record_names_what_it_writes:
  for +a: String
  for +when: String
  for +message: String
  for +fl: Bool
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
  {(String.starts_with(Main.recorded.stem(Main.record.planned(Main.Writing{a, when, message, fl}, hex, befores, fs, bs, ps, t, hs, dg, reads, ks, moves, obs, ls)), Naming.compose(when, message, Main.recorded.change(Main.record.planned(Main.Writing{a, when, message, fl}, hex, befores, fs, bs, ps, t, hs, dg, reads, ks, moves, obs, ls)))), String.eq(Main.recorded.stem(Main.record.planned(Main.Writing{a, when, message, fl}, hex, befores, fs, bs, ps, t, hs, dg, reads, ks, moves, obs, ls)), Naming.compose(when, message, Main.recorded.change(Main.record.planned(Main.Writing{a, when, message, fl}, hex, befores, fs, bs, ps, t, hs, dg, reads, ks, moves, obs, ls))))) == (True{}, Bool.not(Rev.member(T.map(~Main.Full, ~String, ~(f => Naming.base_of(Main.full.named(f))), fs), Naming.compose(when, message, Main.recorded.change(Main.record.planned(Main.Writing{a, when, message, fl}, hex, befores, fs, bs, ps, t, hs, dg, reads, ks, moves, obs, ls)))))) : Bool & Bool}

# What `record` goes on to write is the plan the survey made, as the
# survey made it, and one the survey settled. Where the plan is not
# refused, neither the walk nor the survey refused any path it looked at,
# the survey observed no file still holding a line the renderer wrote and
# no contested file of lines left empty, every link the position holds is
# anchored — naming no file the record drops, unless the link goes too or
# the folder holds a link at its path that this format can hold — and a
# path is among those `--accept` names exactly where the survey observed
# that concurrent work states different bytes for it.
# That no path it looks at holds two files is
# `record_goes_on_where_each_path_holds_one_file`.
law record_writes_only_what_is_settled:
  for +t: Tree.Tree()
  for +looked: Tree.Tree()
  for +held: Set()
  for +walked: List<&2, T.Split>
  for +ss: List<&2, Sv.Seen>
  for +moves: List<&2, T.Split>
  for +accepted: List<&2, String>
  for pl2: Sv.Planned
  for +e: {Main.planned.r(looked, Sv.planned(t, looked, held, walked, ss, moves), accepted) == Done{pl2} : Result<&2, &2, Main.Refused, Sv.Planned>}
  for +x: String
  {(pl2, (walked, (Sv.refusals(Main.planned.obs(Sv.planned(t, looked, held, walked, ss, moves))), (Sv.marked(Main.planned.obs(Sv.planned(t, looked, held, walked, ss, moves))), (Sv.emptied(Main.planned.obs(Sv.planned(t, looked, held, walked, ss, moves))), (Sv.anchored(t, Sv.planned.gone(Sv.planned(t, looked, held, walked, ss, moves)), ss), Rev.member(accepted, x))))))) == (Sv.planned(t, looked, held, walked, ss, moves), (Nil{}, (Nil{}, (Nil{}, (Nil{}, (True{}, Rev.member(Sv.accepts(Main.planned.obs(Sv.planned(t, looked, held, walked, ss, moves))), x))))))) : Sv.Planned & (List<&2, T.Split> & (List<&2, T.Split> & (List<&2, T.Split> & (List<&2, String> & (Bool & Bool)))))}

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
# every contested file, and every rename it is asked to make is among
# those paths at both its ends, since recording one end alone would spell
# the other as a file appearing or disappearing. `record` goes on past its
# check of the restriction exactly where no path is named, or where it has
# one parent at most and the path each `--move` moves from, and the one it
# moves to, is among the paths named or beneath one of them.
law record_restricts_no_merge_and_no_half_rename:
  for +named: List<&2, String>
  for +ps: List<&2, String>
  for +moves: List<&2, T.Split>
  {Result.is_done(&2, &2, Main.Refused, Unit, Main.restricted.r(named, ps, moves)) == Bool.or(List.is_empty(&2, String, named), Bool.and(Bool.not(Nat.is_gt(List.length(&2, String, ps), 1n)), Bool.and(Sv.all_covered(named, moves), Sv.all_covered(named, Main.swapped(moves))))) : Bool}

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
# then `revision` lines which, read back, name exactly the revisions each
# is handed as written — `record` its revision, `amend` and `abandon`
# theirs and each they carried, `carry` each it carried — every one of
# them, each once, in digest order, and nothing else.
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
# text, and where `record` goes on it is. Of the paths it looks at, one
# where the position holds nothing and the folder a regular file, and that
# `--lines` names, is among the files it reads because `--lines` named
# them, and the bytes read there are UTF-8.
law record_reads_lines_as_text:
  for +ks: List<&2, T.Split>
  for +reads: Map<&2, List<&2, U32>>
  for +hs: List<&2, Main.Here>
  for +e: {Main.not_lines(ks, reads, hs) == None{} : Maybe<&2, String>}
  for +i: Nat
  for +p: String
  for +q: String
  for +r: Bool
  for +n: Nat
  for hi: {List.get(&2, Main.Here, hs, i) == Some{Main.Here{p, None{}, Some{Folder.Found.File{q, r, n}}}} : Maybe<&2, Main.Here>}
  for +j: Nat
  for hj: {List.get(&2, T.Split, ks, j) == Some{T.Split{p, "lines"}} : Maybe<&2, T.Split>}
  {Bool.and(Rev.member(Main.lined_added(ks, hs), p), Folder.is_utf8(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p)))) == True{} : Bool}

# An amendment keeps the identifiers it minted. Of the files arriving
# against the amended revision's parents, each is given an identifier, in
# path order, and each the amended revision added keeps the identifier it
# was added under: only a path it did not add is minted one afresh.
law amend_keeps_what_it_added:
  for +arriving: List<&2, String>
  for +kept: List<&2, T.Split>
  for +hex: String
  {Main.amend.minted.ok(arriving, kept, Main.amend.minted(arriving, kept, hex)) == True{} : Bool}

# A kind is a fact about a file. Where `record` goes on past its check of
# the kinds a person stated, every path `--bytes` or `--lines` named is a
# file the folder holds.
law record_gives_kinds_only_to_files:
  for +ks: List<&2, T.Split>
  for +found: Set()
  for u: Unit
  for +e: {Main.kinds.unheld.r(Main.kinds.of(ks), found) == Done{u} : Result<&2, &2, Main.Refused, Unit>}
  for +j: Nat
  for +p: String
  for k: String
  for hj: {List.get(&2, T.Split, ks, j) == Some{T.Split{p, k}} : Maybe<&2, T.Split>}
  {Sv.has(found, p) == True{} : Bool}

# A dry run of `abandon` says what it would do, and nothing else: a
# `would abandon` line for each revision of the run, in order, naming it
# by the first twelve letters of its digest with nothing after them but
# what begins with two spaces, as the bookmarks there are named; then a
# line saying a tombstone would supersede them; and after that only
# `would carry` lines.
law abandon_dry_run_names_the_run:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for +id: String
  for +only: Bool
  for +run: List<&2, String>
  {Main.dry.said(run, Main.abandon.dry.lines(fs, bs, id, only, run)) == True{} : Bool}

# `update` reads its words as they say: a dry run where `-n` or
# `--dry-run` is among them, and the target the one word that does not
# begin with `-`.
law update_reads_its_words:
  for +ws: List<&2, String>
  for +c: Upd.UpdateCmd
  for e: {Upd.args.r(ws) == Done{c} : Result<&2, &2, Main.Refused, Upd.UpdateCmd>}
  {c == Upd.UpdateCmd{Upd.uargs.target(ws), Upd.uargs.dry(ws)} : Upd.UpdateCmd}

# The folder is only ever given a head, decision 0030's rule: whatever
# `update` is told, the revision it goes on to lay out is a current head of
# the store; and told nothing, it is the store's only head — every current
# head is that one.
law update_holds_only_a_head:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for +t: Maybe<&2, String>
  for +id: String
  for -u: Unit
  for e1: {Upd.target.r(fs, bs, t) == Done{id} : Result<&2, &2, Main.Refused, String>}
  for e2: {Upd.head.r(fs, bs, id) == Done{u} : Result<&2, &2, Main.Refused, Unit>}
  {Bool.and(Rev.member(Main.current_heads(Main.history(fs)), id), Bool.or(Maybe.is_some(&2, String, t), Main.all_held([id], Main.current_heads(Main.history(fs))))) == True{} : Bool}

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

# Decision 0012's safety, in what the store and the folder read. `merge`
# lays each file of the merged tree out in turn — `lay.all` gives each its
# acts, and `lay.acts` runs them together in file order for `perform` — and
# every act laid for a file is accounted for by that very file. It writes
# at the name `beside` gives the file where it gives one, and otherwise at
# the file's own path, never at the path another claimant keeps; with the
# mode the tree records; a file of lines as the walk of the heads joined
# renders it, a payload the tree names, a link pointing where `cat` says.
# And it writes a file only over what the folder's walk read there as
# nothing, bytes the folder says are not text, what it is writing, the
# walk's reading unfenced, or what one of the heads reads for the file —
# its ancestry walked for a file of lines, its tree's payload for a file of
# bytes. Work nobody recorded is never written over.
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
  {Merging.laid.files(fs, ds, heads, bs, t, dg, texts, es, Merging.lay.all(t, cs, located, Merging.places(fs, ds, heads, bs, dg, ls, texts, es))) == True{} : Bool}

# Where the merged trees contest nothing and the folder already holds the
# merge — at every file's path, the walk's reading of a file of lines in
# which nothing met, the payload the tree names for a file of bytes, a link
# pointing where `cat` says — `merge` changes no byte: every file it writes
# it writes with the bytes the folder's walk read there, and it points no
# link. (It sets each file's mode as the tree records it, and says so
# where that changes anything.)
law merge_rewrites_nothing_merged:
  for +fs: List<&2, Main.Full>
  for +ds: List<&2, Store.Doc>
  for +heads: List<&2, String>
  for +t: Tree.Tree()
  for +dg: Map<&2, String>
  for +texts: Map<&2, String>
  for +ls: Map<&2, String>
  for +located: Map<&2, String>
  for +es: List<&2, Tree.Entry>
  for +h: {Merging.already(fs, ds, heads, t, dg, ls, es) == True{} : Bool}
  {Merging.rewrites.same(dg, Merging.lay.acts(Merging.lay.all(t, Nil{}, located, Merging.places(fs, ds, heads, Nil{}, dg, ls, texts, es)))) == True{} : Bool}

# The number of files `merge` says hold work that met is the number of
# files of the merged tree where concurrent work met, counted from the
# store: each file of lines whose walk of the heads met — a region, or a
# line but the last without its newline — and each file of bytes no side's
# payload wins. A link is never counted, and no file twice.
law merge_counts_the_files_that_met:
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
  {Merging.lay.met(Merging.lay.all(t, cs, located, Merging.places(fs, ds, heads, bs, dg, ls, texts, es))) == Merging.met.count(fs, ds, heads, es) : Nat}

# The markers `merge` writes are the ones `status` counts and `record
# --merge` refuses to find standing: both read a file of lines through
# `status.marked.of`, the marker search scoped to one merge. In the file
# `merge` renders, a line the renderer writes on its own account — a label
# naming the revision that wrote a run, or the line closing a fence —
# standing on a line of its own that the walk's own reading does not hold,
# is counted, so the file is marked.
law merge_counts_what_it_fences:
  for j: Conflict.Joined
  for +x: String
  for +a: Nat
  for +h1: {Rev.member(Conflict.lines(Conflict.render(j)), x) == True{} : Bool}
  for h2: {Rev.member(Conflict.lines(Conflict.plain(j)), x) == False{} : Bool}
  for h3: {Bool.or(String.eq(x, Conflict.closing.line()), String.eq(x, Conflict.label.line(Conflict.joined.names(j), a))) == True{} : Bool}
  {Nat.is_gt(Main.status.marked.of(Conflict.render(j), Some{Done{j}}), 0n) == True{} : Bool}

# And the walk's reading unfenced — what `merge` writes where nothing met —
# the same search counts as marked nowhere, even where the file's own lines
# look like the renderer's: a document about markers is ordinary content.
law merge_counts_nothing_unfenced:
  for j: Conflict.Joined
  {Main.status.marked.of(Conflict.plain(j), Some{Done{j}}) == 0n : Nat}

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

# The store `init` lays down holds no document, and what `check` gathers
# from it — `historica.txt` and each file of `skipped/` read back from the
# bytes written there, as the pass reads them, and whether `skipped.txt`
# is there — it finds nothing wrong with, wherever the store is.
law check_finds_nothing_in_a_new_store:
  for +root: String
  {InitL.passes(root, Main.init.laid()) == True{} : Bool}

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

# The rule `skip <path>` makes skips that file, or that directory whole
# and every file under it.
law skip_path_rule_skips_under_its_path:
  for +v: String
  for +directory: Bool
  for +sc: Folder.Scope
  for e: {Skip.path.scoped(v, directory) == Done{sc} : Result<&2, &2, Main.Refused, Folder.Scope>}
  for +x: String
  {Bool.pick(Bool, directory, Bool.and(Folder.skips_directory([sc], v), Folder.skips([sc], String.append(v ++ "/", x))), Folder.skips([sc], v)) == True{} : Bool}

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
# out, exactly where carrying its plan out would change nothing. Where it
# says so, every path it steps through would hold what it held, and nothing
# would be taken away; and where that is so — the folder holds the target
# already at every path the tree holds, and no file history records stands
# where the target holds nothing — it says so, rather than writing a file
# over itself. What a step would leave is `after`'s model of the host's
# writes.
law update_settles_exactly_what_stays:
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
  {Upd.settled(p) == Upd.unchanged(p) : Bool}

# `update` reaches nowhere in the folder the target does not say to.
# Every file it writes, every mode it sets and every link it makes is at
# a path the target's tree holds; and every path it takes anything away
# from is one that tree does not hold, where the walk found a file whose
# bytes some revision records for a file history put at that path — `cat`
# of that revision reads them for it, or its tree names them as its
# payload — or found a link. A stray nobody recorded, at a path the target
# does not hold, is never touched.
law update_touches_only_the_target:
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
  {Upd.confined(fs, List.append(&2, Store.Doc, ds, more), t, found, dg, Upd.effects(p)) == True{} : Bool}

# Where there is nothing to do, `update` and `update --dry-run` say the
# same thing, as the Rust tool's do: each file it leaves alone, and that
# the folder already holds the target.
law update_says_settled_as_its_dry_run:
  for p: Upd.Plan
  for +s: String
  for +e: {Upd.settled(p) == True{} : Bool}
  {Upd.said.settled(s, p) == Upd.said.dry(s, p) : List<&2, String>}

# `update --dry-run` plans exactly what `update` does. Its lines, read back
# by the verb each begins with, name each file `update` writes, each it
# removes, each whose mode it sets and to what, and each link it makes and
# where it points — the effects `apply` performs, one host write each, in
# the order it performs each kind — and nothing else; and it says the
# folder already holds the target exactly where there is nothing to
# perform, which is where `update` itself performs nothing and says so.
law update_dry_run_names_what_it_does:
  for p: Upd.Plan
  for +s: String
  {Upd.dry.read(Upd.said.dry(s, p)) == Upd.effects.read(s, Upd.effects(p)) : Upd.Named}

# The `record` line `merge` prints records the merge it laid out — what
# makes the pending merge live in a person's terminal (decision 0012). Its
# words, read by `record`'s own parser, are a merge of every head `merge`
# joined, each as the person typed it, in the order joined; settling each
# file written beside a path at the path `merge` wrote it, in file order;
# with the message still to write, and nothing else. (That is, where no
# file's identifier holds an `=`, which `--at` cuts at and none the store
# mints does.)
law merge_prints_the_record_that_records_it:
  for +typed: List<&2, T.Split>
  for +bs: List<&2, T.Split>
  for +h: {SortL.all_ok(~T.Split, ~(x => Merging.id.plain(x)), bs) == True{} : Bool}
  {Main.record.args.r(Merging.record.words(typed, bs)) == Done{Main.RecordCmd{None{}, Merging.typed.spellings(typed), Nil{}, List.sort(~T.Split, ~(a => b => Merging.typed.le(a, b)), bs), Nil{}, Nil{}, Nil{}, False{}, False{}, Some{"<message>"}}} : Result<&2, &2, Main.Refused, Main.RecordCmd>}

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

# `arrange` never writes over a file: every rename it carries out, in
# `revisions/` and in `operations/`, goes from one path to a different one
# that the store's listing does not hold. Two files holding one document
# want one name, and the second finds it taken when its turn comes.
law arrange_plans_no_overwrite:
  for +refile: Bool
  for +fs: List<&2, Main.Full>
  for +revs: List<&2, T.Split>
  for +ops: List<&2, T.Split>
  for +ls: List<&2, String>
  for +a: Arrange.Arrangement
  for e: {Arrange.arrangement.r(refile, fs, revs, ops, ls) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}
  for +from: String
  for +to: String
  for h: {ArrangeL.moves(List.append(&2, T.Split, Arrange.done.renamed(Arrange.arrangement.revs(a)), Arrange.done.renamed(Arrange.arrangement.ops(a))), from, to) == True{} : Bool}
  {Bool.or(String.eq(from, to), Rev.member(ls, to)) == False{} : Bool}

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

# `arrange` moves each file once: of each directory, a path is renamed
# from no more often than the walk found a file there, so a file the walk
# lists once is moved at most once, and a path it does not list, never.
law arrange_moves_each_file_once:
  for +refile: Bool
  for +fs: List<&2, Main.Full>
  for +revs: List<&2, T.Split>
  for +ops: List<&2, T.Split>
  for +ls: List<&2, String>
  for +a: Arrange.Arrangement
  for e: {Arrange.arrangement.r(refile, fs, revs, ops, ls) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}
  for +x: String
  {Bool.and(Nat.is_le(ArrangeL.times(T.map(~T.Split, ~String, ~(s => ArrangeL.first(s)), Arrange.done.renamed(Arrange.arrangement.revs(a))), x), ArrangeL.times(T.map(~T.Split, ~String, ~(s => ArrangeL.first(s)), revs), x)), Nat.is_le(ArrangeL.times(T.map(~T.Split, ~String, ~(s => ArrangeL.first(s)), Arrange.done.renamed(Arrange.arrangement.ops(a))), x), ArrangeL.times(T.map(~T.Split, ~String, ~(s => ArrangeL.first(s)), ops), x))) == True{} : Bool}

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

# `prune` lets a revision of the store go only where a revision of the
# store says, in its own `supersedes`, that it supersedes it: one prune
# keeps, or one it lets go of too, since a superseded run clears in one
# pruning. Nothing a revision it keeps stands on goes either
# (prune_keeps_what_work_stands_on), so no head is ever pruned.
law prune_lets_go_only_what_is_superseded:
  for +fs: List<&2, Main.Full>
  for +id: String
  for hf: {Rev.member(Main.ids(fs), id) == True{} : Bool}
  for hk: {Rev.member(Main.ids(Prune.kept(fs)), id) == False{} : Bool}
  {PruneL.supersedes_any(fs, id) == True{} : Bool}

# `prune --dry-run` and `prune` plan the same: of any store, the dry run
# removes nothing and names, a line each and in the order they would go,
# exactly the files the real run removes, and the real run names the same
# files as it removes them; where nothing is prunable, both say so.
law prune_dry_run_names_what_prune_removes:
  for +s: Prune.Stored
  {(Prune.act.says(Prune.act.of(True{}, False{}, Prune.stored.plan(s))), (Prune.act.says(Prune.act.of(False{}, False{}, Prune.stored.plan(s))), Prune.act.removes(Prune.act.of(True{}, False{}, Prune.stored.plan(s))))) == (PruneL.report(Prune.act.removes(Prune.act.of(False{}, False{}, Prune.stored.plan(s))), T.map(~String, ~String, ~(f => "would remove history/" ++ f), Prune.act.removes(Prune.act.of(False{}, False{}, Prune.stored.plan(s))))), (PruneL.report(Prune.act.removes(Prune.act.of(False{}, False{}, Prune.stored.plan(s))), T.map(~String, ~String, ~(f => "removed history/" ++ f), Prune.act.removes(Prune.act.of(False{}, False{}, Prune.stored.plan(s))))), Nil{})) : List<&2, String> & (List<&2, String> & List<&2, String>)}

# `prune` clears from `cache/` only files named by a digest — what any
# reader rebuilds, and what may hold content it has just destroyed; the
# note `init` writes there, or anything else a person put there, stays.
law prune_clears_only_derived_files:
  for +ls: List<&2, String>
  for +x: String
  for h: {Rev.member(Prune.cached(ls), x) == True{} : Bool}
  {T.is_digest(x) == True{} : Bool}

# Every operation document and payload `prune` removes holds a digest no
# revision it keeps names — read from that revision's own `edit`, `text`
# and `bytes` facts — and is no forgetting document standing in for a
# digest a revision it keeps names (decision 0014).
law prune_removes_only_unneeded_content:
  for +fs: List<&2, Main.Full>
  for +revs: List<&2, T.Split>
  for +bs: List<&2, Prune.Body>
  for +ps: List<&2, T.Split>
  for +d: String
  for h: {Rev.member(Prune.pruned.content(Prune.plan(fs, revs, bs, ps)), d) == True{} : Bool}
  {Bool.or(PruneL.named(Prune.kept(fs), d), PruneL.stands_in(bs, Prune.kept(fs), d)) == False{} : Bool}

# `receive` files as a revision only one of the source's revision
# documents, its digest and its text, and only under a digest no revision
# document of this store has — this store's revisions all parse, or no
# plan is made (receive_trusts_what_it_plans_from).
law receive_takes_only_revisions_it_lacks:
  for +here: Receive.Side
  for +there: Receive.Side
  for +join: Bool
  for +p: Receive.RPlan
  for e: {Receive.plan.r(here, there, join) == Done{p} : Result<&2, &2, Main.Refused, Receive.RPlan>}
  for +id: String
  for +text: String
  for h: {ReceiveL.holds(Receive.rplan.revisions(p), id, text) == True{} : Bool}
  {Bool.and(Bool.not(Rev.member(T.map(~Store.Doc, ~String, ~(d => Store.id_of(d)), Arrange.revision_docs(Receive.stored.docs(Receive.stored.of(here)))), id)), ReceiveL.holds(Arrange.revision_docs(Receive.stored.docs(Receive.stored.of(there))), id, text)) == True{} : Bool}

# `receive` files as an operation document only one of the source's, its
# digest and its text, and only under a digest this store holds no
# document under and that no forgetting document of either store forgets,
# so a forgetting document is never undone by an arriving original.
law receive_takes_only_documents_it_lacks:
  for +here: Receive.Side
  for +there: Receive.Side
  for +id: String
  for +text: String
  for h: {ReceiveL.holds(ReceiveL.rplan.documents(Receive.plan.of(here, there)), id, text) == True{} : Bool}
  {Bool.and(Bool.not(Bool.or(Rev.member(T.map(~Prune.Body, ~String, ~(b => Prune.body.id(b)), Receive.stored.bodies(Receive.stored.of(here))), id), Bool.or(Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(here)), id), Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(there)), id)))), ReceiveL.holds(Receive.stored.odocs(Receive.stored.of(there)), id, text)) == True{} : Bool}

# `receive` copies only a payload the source lists, from the path it
# lists it at, and only under a digest this store holds no payload under
# and that neither store forgets.
law receive_takes_only_payloads_it_lacks:
  for +here: Receive.Side
  for +there: Receive.Side
  for +path: String
  for +d: String
  for h: {ReceiveL.lists(ReceiveL.rplan.payloads(Receive.plan.of(here, there)), path, d) == True{} : Bool}
  {Bool.and(Bool.not(Bool.or(Rev.member(T.map(~T.Split, ~String, ~(s => Receive.split.digest(s)), Receive.stored.payloads(Receive.stored.of(here))), d), Bool.or(Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(here)), d), Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(there)), d)))), ReceiveL.lists(Receive.stored.payloads(Receive.stored.of(there)), path, d)) == True{} : Bool}

# Between two stores the check passes, `receive` plans exactly where it
# was given `--join-unrelated` or the histories are related as decision
# 0029 has it, read from the revisions themselves: one store is empty, or
# they share a revision, or a revision of either names one of the other's
# as a parent or as what it supersedes. Anything else is refused.
law receive_joins_only_related_histories:
  for +here: Receive.Side
  for +there: Receive.Side
  for +join: Bool
  for hh: {Prune.sound(Receive.stored.of(here)) == True{} : Bool}
  for ht: {Prune.sound(Receive.stored.of(there)) == True{} : Bool}
  {Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.r(here, there, join)) == Bool.or(join, ReceiveL.related(Receive.side.fulls(here), Receive.side.fulls(there))) : Bool}

# `receive` moves no bookmark this store has, though it may add one: each
# it writes, by name and by the target it spells, is one this store has
# none of by that name, or has at that very target — a bookmark's name is
# its file's, so a store holds one of each. Two targets for one name is a
# disagreement, and writes nothing.
law receive_moves_no_bookmark:
  for +here: Receive.Side
  for +there: Receive.Side
  for +n: String
  for +at: String
  for h: {ReceiveL.marks_at(Receive.rplan.names(Receive.plan.of(here, there)), n, at) == True{} : Bool}
  {Bool.or(Bool.not(ReceiveL.named(Receive.side.marks(here), n)), ReceiveL.marks_at(Receive.side.marks(here), n, at)) == True{} : Bool}

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

# `fetch` reads the line `offer` writes for a file back as that file: its
# kind, its digest, what it forgets and its path, whatever spaces the path
# holds — for every kind a reader of `historica-offer-1` knows, a digest
# that is one, and nothing forgotten or a forgotten digest that is one. So
# a fetcher checks each file against the digest offer_names_each_file_by_its_digest
# says its line carries.
law offer_lines_read_back:
  for +k: String
  for +d: String
  for +g: Maybe<&2, String>
  for +p: String
  for +rest: List<&2, String>
  for +nh: Bool
  for +hk: {Rev.member(Fetch.KINDS(), k) == True{} : Bool}
  for +hd: {T.is_digest(d) == True{} : Bool}
  for +hg: {OfferL.forgets_ok(g) == True{} : Bool}
  {Fetch.line.at(Offer.offered.line(Offer.Offered{k, d, g, p}) <> rest, nh) == Fetch.LRead.Entry{Offer.Offered{k, d, g, p}} : Fetch.LRead}

# `offer` lists what a document of `operations/` forgets as `prune`,
# `receive` and `export` read it: a stand-in for a payload, and an
# operation document, by the `forgets` line of its own grammar — save a
# resolution that is no stand-in, which the Rust tool's catalogue does not
# parse, so its manifest lists one as forgetting nothing.
law offer_lists_forgetting_as_prune_reads_it:
  for +path: String
  for +id: String
  for +text: String
  {Offer.catalogue.forgets(text) == Bool.pick(Maybe<&2, String>, Bool.and(Res.is_resolution(text), Bool.not(Prune.forgotten.payload(T.lines(text)))), None{}, OfferL.forgets_of(Prune.body.of(path, id, text, Prune.forgotten.payload(T.lines(text))))) : Maybe<&2, String>}

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

# The files `receive` removes, for the digests it destroys, are this
# store's own: each an operation document or a payload file here, at that
# path, holding one of those digests — so, with
# receive_destroys_only_what_is_forgotten, every file it removes holds what
# a forgetting document stands in for.
law receive_removes_only_the_originals:
  for +bs: List<&2, Prune.Body>
  for +ps: List<&2, T.Split>
  for +des: List<&2, String>
  for +x: String
  for h: {Rev.member(Receive.destroyed(bs, ps, des), x) == True{} : Bool}
  {Bool.or(ReceiveL.gone_at(T.map(~Prune.Body, ~T.Split, ~(b => Prune.body.split(b)), bs), x, des), ReceiveL.gone_at(ps, x, des)) == True{} : Bool}

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

# `export` knows what a directory holds by reading the host's listing of
# it (`Store.folder`), and reads it back as the host writes it: the names
# it finds are the entries' own, one each and in the order listed, whatever
# the entries are — a directory, a file of any mode and size, a link (whose
# target, on the line after it, is no entry of its own), or anything else.
law export_reads_a_directory_listing_back:
  for +es: List<&2, Export.Listed>
  for +h: {Export.listed.ok(es) == True{} : Bool}
  {Export.dir.names(Export.listing(es)) == Export.listed.names(es) : List<&2, String>}

# And so an export writes only into a directory holding nothing: it lays a
# folder out alone (`--files-only`) exactly where the host's listing names
# no entry, and makes a fresh copy exactly there too. A directory holding
# anything is refused, or, holding a copy, brought up to date.
law export_writes_only_into_nothing:
  for +into: String
  for +es: List<&2, Export.Listed>
  for header: Result<&1, &1, U32 & String, String>
  for +h: {Export.listed.ok(es) == True{} : Bool}
  {Bool.and(Export.bool.same(Result.is_done(&2, &2, Main.Refused, Unit, Export.empty.r(into, Done{Export.listing(es)})), List.is_empty(&2, Export.Listed, es)), Export.bool.same(Export.dest.fresh(Export.dest.r(into, Done{Export.listing(es)}, header)), List.is_empty(&2, Export.Listed, es))) == True{} : Bool}

# A folder laid out alone is refused as folding paths the tree holds apart
# (decision 0027) exactly where some file it wrote reads back as other
# bytes than it laid there: reading the host's line for each file it wrote,
# a digest and a size, it goes on exactly where every digest is that of
# what was laid at that path.
law export_calls_a_folder_folded_exactly_where_it_reads_back_otherwise:
  for +qs: List<&2, Export.Put>
  for +ds: List<&2, T.Split>
  for +hs: {Export.stats.ok(ds) == True{} : Bool}
  for hl: {List.length(&2, Export.Put, qs) == List.length(&2, T.Split, ds) : Nat}
  {Result.is_done(&2, &2, Main.Refused, Unit, Export.folded.r(Export.folded(qs, Export.stat.lines(ds)))) == Export.reads.back(qs, ds) : Bool}

# What `export -n` names, read back from its lines: a `would withdraw` line
# for each file a copy being updated gives up, in the order they go, and a
# `write` line for each path the target's tree places — every one of them,
# none other, once each and in path order — whatever it counts, and no
# line of the rest reads as either.
law export_dry_run_names_what_it_would_write:
  for +held: List<&2, Main.Full>
  for +t: Tree.Tree()
  for +ds: List<&2, Store.Doc>
  for +ps: List<&2, T.Split>
  for +bodies: List<&2, Prune.Body>
  for +rs: List<&2, Receive.Ruled>
  for +bs: List<&2, Bm.Bookmark>
  for +claims: List<&2, T.Split>
  for +c: Export.Counts
  for +ws: List<&2, String>
  for +n: Nat
  for +u: Bool
  for +spelled: String
  for +into: String
  for +x: String
  {Bool.and(Main.strings.same(Export.said.after(Export.said.plan(Export.plan.of(held, t, ds, ps, bodies, rs, bs, claims), c, ws, n, u, spelled, into), "would withdraw history/"), ws), Bool.and(Main.rising(Export.said.after(Export.said.plan(Export.plan.of(held, t, ds, ps, bodies, rs, bs, claims), c, ws, n, u, spelled, into), "write   ")), Export.bool.same(Rev.member(Export.said.after(Export.said.plan(Export.plan.of(held, t, ds, ps, bodies, rs, bs, claims), c, ws, n, u, spelled, into), "write   "), x), Export.tree.holds(t, x)))) == True{} : Bool}

# What `export --files-only -n` says it would do is what the real run then
# says it did: read back, its `write` lines name, in order, exactly the
# files the real run names as `wrote`, and its `link` lines exactly the
# links, each with where it points, that the real run names as `linked` —
# whatever modes it went on to set.
law export_files_only_dry_run_names_what_it_lays_out:
  for +ps: List<&2, Export.Put>
  for +set: List<&2, String>
  for +spelled: String
  for +into: String
  for +at: String
  {Bool.and(Main.strings.same(Export.said.after(Export.said.folder(ps, spelled, into), "write   "), Export.said.after(Export.said.laid(ps, set, spelled, at), "wrote   ")), Main.strings.same(Export.said.after(Export.said.folder(ps, spelled, into), "link    "), Export.said.after(Export.said.laid(ps, set, spelled, at), "linked  "))) == True{} : Bool}

# An export updates a copy only where the copy is its own to update
# (decision 0052): it goes on exactly where the copy is related to this
# store (decision 0029) and every revision the copy holds is one this store
# holds, or names as some revision's parent or as one it supersedes. A
# revision it has not heard of was recorded in the copy, and combining that
# is `receive`'s.
law export_updates_only_a_copy_it_could_have_made:
  for +into: String
  for +fs: List<&2, Main.Full>
  for +cfs: List<&2, Main.Full>
  {Result.is_done(&2, &2, Main.Refused, Unit, Export.copy.r(into, fs, cfs)) == Bool.and(Receive.related(fs, cfs), Export.heard.all(cfs, fs)) : Bool}

# Bringing a copy up to date leaves it holding the whole set a fresh
# export of the target gives (decision 0052): every revision, document,
# forgetting document and payload the set names is one the copy's store
# already holds a file of, one the update writes into it, or one a
# forgetting document of this store or of the copy says is gone — which is
# never handed back (decision 0014).
law export_update_leaves_the_copy_the_whole_set:
  for +p: Export.Plan
  for +here: List<&2, Prune.Body>
  for +cst: Prune.Stored
  for +marks: List<&2, Bm.Bookmark>
  for +d: String
  for h: {Rev.member(Export.set.named(p), d) == True{} : Bool}
  {Bool.or(Export.copy.has(cst, d), Bool.or(Export.writes.has(Export.onto.writes(p, Export.onto.of(p, here, cst, marks)), d), Bool.or(Receive.forgot.by(here, d), Receive.forgot.by(Receive.stored.bodies(cst), d)))) == True{} : Bool}

# And it gives up only what the set no longer names (decisions 0052, 0051
# and 0062): every file an update withdraws from a copy, or retires, is a
# revision file of a revision the target's history does not hold, a
# document or payload file of one the set does not carry, a rule file
# stating a rule the origin does not share, or a bookmark file of a
# bookmark that does not travel.
law export_update_gives_up_only_what_the_set_no_longer_names:
  for +p: Export.Plan
  for +here: List<&2, Prune.Body>
  for +cst: Prune.Stored
  for +marks: List<&2, Bm.Bookmark>
  for +w: String
  for h: {Rev.member(Export.onto.all(Export.onto.of(p, here, cst, marks)), w) == True{} : Bool}
  {Export.given.up(p, cst, marks, w) == True{} : Bool}

# Bringing a copy up to date carries into it the files of `claims/` it
# lacks, and no others (decisions 0053 and 0054): a file travels exactly
# where the origin has it and the copy has none of that name, so what the
# copy already holds there, whoever wrote it, is never written over.
law export_update_carries_only_the_claims_a_copy_lacks:
  for +cs: List<&2, T.Split>
  for +cc: List<&2, T.Split>
  for +l: String
  {Export.claim.named(Export.claims.fresh(cs, Set.from_list(Export.split.labels(cc))), l) == Bool.and(Export.claim.named(cs, l), Bool.not(Export.claim.named(cc, l))) : Bool}

# Bringing a copy up to date gives it no private rule either (decision
# 0051): every rule file an update adds to the copy states a shared rule,
# whatever the copy already states and whatever label each is filed under.
law export_update_states_no_private_rule:
  for +held: List<&2, Main.Full>
  for +t: Tree.Tree()
  for +ds: List<&2, Store.Doc>
  for +ps: List<&2, T.Split>
  for +bodies: List<&2, Prune.Body>
  for +rs: List<&2, Receive.Ruled>
  for +bs: List<&2, Bm.Bookmark>
  for +claims: List<&2, T.Split>
  for +cst: Prune.Stored
  for +retired: Set()
  {Export.lines.shared(Export.rules.added(Export.plan.of(held, t, ds, ps, bodies, rs, bs, claims), cst, retired)) == True{} : Bool}

# Catching a copy's folder up leaves it holding what a fresh export of the
# same target lays out (decision 0052): wherever the folder's plan is made,
# the fresh folder can be laid out too, and once each of the plan's steps is
# taken — a file written or linked, a mode set, a file kept — every path
# the fresh folder has holds exactly its file there: the bytes of a file of
# lines or the payload of a file of bytes, with its mode, or a link
# pointing where the fresh one points. One step is taken for each of those
# files, and nothing the plan removes is one of them.
law export_catches_up_to_a_fresh_copy:
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
  for +whole: Bool
  for +rs: List<&2, Export.Rec>
  {Export.caught.lands(seen, Export.caught.r(t, fs, ds, id, pays, bs, rules, seen, walk, dirs, others, whole, rs), Export.folder.r(t, fs, ds, id, pays, bs, rules)) == True{} : Bool}

# An export takes a copy's folder for its own untouched output — the one
# case it may rewrite whole (decisions 0030 and 0052 meeting) — only where
# the walk found there what a fresh export of that revision lays out: a
# folder its plan settles holds, at every path of the fresh folder, that
# path's file, by digest and mode or by where its link points.
law export_settles_only_on_what_it_laid_out:
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
  for +whole: Bool
  for +rs: List<&2, Export.Rec>
  for h: {Export.caught.settled(Export.caught.r(t, fs, ds, id, pays, bs, rules, seen, walk, dirs, others, whole, rs)) == True{} : Bool}
  {Export.fresh.held(seen, Export.folder.r(t, fs, ds, id, pays, bs, rules)) == True{} : Bool}

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

# `record` cuts `--at` and `--move` at their first `=`. Whatever words it
# has read, `--at <file>=<path>` adds one more file to put at a path, and
# `--move <old>=<new>` one more path to move, after those before it, what
# follows the first `=` kept whole whatever `=` it holds; a value with no
# `=` is refused. And a word that does not begin with `-` is a path to
# record: kept as it was typed where it does not end in `/`, and the `/`
# a shell leaves after a directory changes nothing.
law record_reads_renames_and_paths:
  for +args: List<&2, String>
  for +o: Maybe<&2, String>
  for +ms: List<&2, String>
  for +ac: List<&2, String>
  for +at: List<&2, T.Split>
  for +mv: List<&2, T.Split>
  for +ks: List<&2, T.Split>
  for +ns: List<&2, String>
  for +d: Bool
  for +f: Bool
  for +mg: Maybe<&2, String>
  for +e: {Main.record.args.r(args) == Done{Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}} : Result<&2, &2, Main.Refused, Main.RecordCmd>}
  for +a: String
  for +b: String
  for +ha: {T.all_chars(~(c => Bool.not(Char.is_eq(c, '='))), a) == True{} : Bool}
  for +p: String
  for +hp: {String.starts_with(p, "-") == False{} : Bool}
  for +hn: {String.is_empty(p) == False{} : Bool}
  for +hs: {String.ends_with(p, "/") == False{} : Bool}
  {[Main.record.args.r(List.append(&2, String, args, ["--at", a ++ ("=" ++ b)])), Main.record.args.r(List.append(&2, String, args, ["--move", a ++ ("=" ++ b)])), Main.record.args.r(List.append(&2, String, args, ["--at", a])), Main.record.args.r(List.append(&2, String, args, ["--move", a])), Main.record.args.r(List.append(&2, String, args, [p])), Main.record.args.r(List.append(&2, String, args, [p ++ "/"]))] == [Done{Main.RecordCmd{o, ms, ac, List.append(&2, T.Split, at, [T.Split{a, b}]), mv, ks, ns, d, f, mg}}, Done{Main.RecordCmd{o, ms, ac, at, List.append(&2, T.Split, mv, [T.Split{a, b}]), ks, ns, d, f, mg}}, Fail{Main.Refused{2, "`--at` is spelled `--at <file>=<path>`"}}, Fail{Main.Refused{2, "`--move` is spelled `--move <old>=<new>`"}}, Done{Main.RecordCmd{o, ms, ac, at, mv, ks, p <> ns, d, f, mg}}, Done{Main.RecordCmd{o, ms, ac, at, mv, ks, p <> ns, d, f, mg}}] : List<&2, Result<&2, &2, Main.Refused, Main.RecordCmd>>}

# `amend` reads its words as their plain reading says, one at a time.
# Whatever words it has read, `-m` or `--message` and the word after it
# is the message, the last counting; `--move <old>=<new>` adds one more
# rename after those before it, cut at its first `=`, and one with no `=`
# is refused; `-n`, `--dry-run` and `--fields` ask for what they name;
# `--onto` and `--only` are refused; so is a flag with no word after it
# for its value; and a word that does not begin with `-` is the revision
# to amend where none is named yet, and refused as a second where one is.
law amend_reads_its_words:
  for +args: List<&2, String>
  for +m: Maybe<&2, String>
  for +mv: List<&2, T.Split>
  for +o: Maybe<&2, String>
  for +n: Maybe<&2, String>
  for +d: Bool
  for +f: Bool
  for +y: Bool
  for +e: {Main.rw.args.r("amend", args) == Done{Main.RwCmd{m, mv, o, n, d, f, y}} : Result<&2, &2, Main.Refused, Main.RwCmd>}
  for +v: String
  for +a: String
  for +b: String
  for +ha: {T.all_chars(~(c => Bool.not(Char.is_eq(c, '='))), a) == True{} : Bool}
  for +w: String
  for +hw: {String.starts_with(w, "-") == False{} : Bool}
  {[Main.rw.args.r("amend", List.append(&2, String, args, ["-m", v])), Main.rw.args.r("amend", List.append(&2, String, args, ["--message", v])), Main.rw.args.r("amend", List.append(&2, String, args, ["--move", a ++ ("=" ++ b)])), Main.rw.args.r("amend", List.append(&2, String, args, ["--move", a])), Main.rw.args.r("amend", List.append(&2, String, args, ["-n"])), Main.rw.args.r("amend", List.append(&2, String, args, ["--dry-run"])), Main.rw.args.r("amend", List.append(&2, String, args, ["--fields"])), Main.rw.args.r("amend", List.append(&2, String, args, ["--onto", v])), Main.rw.args.r("amend", List.append(&2, String, args, ["--only"])), Main.rw.args.r("amend", List.append(&2, String, args, ["-m"])), Main.rw.args.r("amend", List.append(&2, String, args, ["--move"])), Main.rw.args.r("amend", List.append(&2, String, args, [w]))] == [Done{Main.RwCmd{Some{v}, mv, o, n, d, f, y}}, Done{Main.RwCmd{Some{v}, mv, o, n, d, f, y}}, Done{Main.RwCmd{m, List.append(&2, T.Split, mv, [T.Split{a, b}]), o, n, d, f, y}}, Fail{Main.Refused{2, "`--move` is spelled `--move <old>=<new>`"}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, d, True{}, y}}, Fail{Main.Refused{2, "`--onto` is not an argument `amend` takes"}}, Fail{Main.Refused{2, "`--only` is not an argument `amend` takes"}}, Fail{Main.Refused{2, "`-m` wants a value"}}, Fail{Main.Refused{2, "`--move` wants a value"}}, Bool.pick(Result<&2, &2, Main.Refused, Main.RwCmd>, Maybe.is_none(&2, String, n), Done{Main.RwCmd{m, mv, o, Some{w}, d, f, y}}, Fail{Main.Refused{2, "`amend` rewrites one revision, and `" ++ w ++ "` is a second"}})] : List<&2, Result<&2, &2, Main.Refused, Main.RwCmd>>}

# `abandon` reads its words the same way. Whatever words it has read, `-m`
# or `--message` and the word after it is the reason, the last counting;
# `--only`, `-n`, `--dry-run` and `--fields` ask for what they name;
# `--move` and `--onto` are refused, and so is `-m` with no word after
# it; and a word that does not begin with `-` is the revision to abandon
# from where none is named yet, and refused as a second where one is.
law abandon_reads_its_words:
  for +args: List<&2, String>
  for +m: Maybe<&2, String>
  for +mv: List<&2, T.Split>
  for +o: Maybe<&2, String>
  for +n: Maybe<&2, String>
  for +d: Bool
  for +f: Bool
  for +y: Bool
  for +e: {Main.rw.args.r("abandon", args) == Done{Main.RwCmd{m, mv, o, n, d, f, y}} : Result<&2, &2, Main.Refused, Main.RwCmd>}
  for +v: String
  for +a: String
  for +b: String
  for +ha: {T.all_chars(~(c => Bool.not(Char.is_eq(c, '='))), a) == True{} : Bool}
  for +w: String
  for +hw: {String.starts_with(w, "-") == False{} : Bool}
  {[Main.rw.args.r("abandon", List.append(&2, String, args, ["-m", v])), Main.rw.args.r("abandon", List.append(&2, String, args, ["--message", v])), Main.rw.args.r("abandon", List.append(&2, String, args, ["--only"])), Main.rw.args.r("abandon", List.append(&2, String, args, ["-n"])), Main.rw.args.r("abandon", List.append(&2, String, args, ["--dry-run"])), Main.rw.args.r("abandon", List.append(&2, String, args, ["--fields"])), Main.rw.args.r("abandon", List.append(&2, String, args, ["--move", v])), Main.rw.args.r("abandon", List.append(&2, String, args, ["--onto", v])), Main.rw.args.r("abandon", List.append(&2, String, args, ["-m"])), Main.rw.args.r("abandon", List.append(&2, String, args, [w]))] == [Done{Main.RwCmd{Some{v}, mv, o, n, d, f, y}}, Done{Main.RwCmd{Some{v}, mv, o, n, d, f, y}}, Done{Main.RwCmd{m, mv, o, n, d, f, True{}}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, d, True{}, y}}, Fail{Main.Refused{2, "`--move` is not an argument `abandon` takes"}}, Fail{Main.Refused{2, "`--onto` is not an argument `abandon` takes"}}, Fail{Main.Refused{2, "`-m` wants a value"}}, Bool.pick(Result<&2, &2, Main.Refused, Main.RwCmd>, Maybe.is_none(&2, String, n), Done{Main.RwCmd{m, mv, o, Some{w}, d, f, y}}, Fail{Main.Refused{2, "`abandon` abandons one run of work, and `" ++ w ++ "` is a second"}})] : List<&2, Result<&2, &2, Main.Refused, Main.RwCmd>>}

# And `carry`. Whatever words it has read, `--onto` and the word after it
# is where to carry onto, the last counting; `-n`, `--dry-run` and
# `--fields` ask for what they name; `-m`, `--message`, `--move` and
# `--only` are refused, and so is `--onto` with no word after it; and a
# word that does not begin with `-` is the work to carry where none is
# named yet, and refused as a second where one is.
law carry_reads_its_words:
  for +args: List<&2, String>
  for +m: Maybe<&2, String>
  for +mv: List<&2, T.Split>
  for +o: Maybe<&2, String>
  for +n: Maybe<&2, String>
  for +d: Bool
  for +f: Bool
  for +y: Bool
  for +e: {Main.rw.args.r("carry", args) == Done{Main.RwCmd{m, mv, o, n, d, f, y}} : Result<&2, &2, Main.Refused, Main.RwCmd>}
  for +v: String
  for +a: String
  for +b: String
  for +ha: {T.all_chars(~(c => Bool.not(Char.is_eq(c, '='))), a) == True{} : Bool}
  for +w: String
  for +hw: {String.starts_with(w, "-") == False{} : Bool}
  {[Main.rw.args.r("carry", List.append(&2, String, args, ["--onto", v])), Main.rw.args.r("carry", List.append(&2, String, args, ["-n"])), Main.rw.args.r("carry", List.append(&2, String, args, ["--dry-run"])), Main.rw.args.r("carry", List.append(&2, String, args, ["--fields"])), Main.rw.args.r("carry", List.append(&2, String, args, ["-m", v])), Main.rw.args.r("carry", List.append(&2, String, args, ["--message", v])), Main.rw.args.r("carry", List.append(&2, String, args, ["--move", v])), Main.rw.args.r("carry", List.append(&2, String, args, ["--only"])), Main.rw.args.r("carry", List.append(&2, String, args, ["--onto"])), Main.rw.args.r("carry", List.append(&2, String, args, [w]))] == [Done{Main.RwCmd{m, mv, Some{v}, n, d, f, y}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, d, True{}, y}}, Fail{Main.Refused{2, "`-m` is not an argument `carry` takes"}}, Fail{Main.Refused{2, "`--message` is not an argument `carry` takes"}}, Fail{Main.Refused{2, "`--move` is not an argument `carry` takes"}}, Fail{Main.Refused{2, "`--only` is not an argument `carry` takes"}}, Fail{Main.Refused{2, "`--onto` wants a value"}}, Bool.pick(Result<&2, &2, Main.Refused, Main.RwCmd>, Maybe.is_none(&2, String, n), Done{Main.RwCmd{m, mv, o, Some{w}, d, f, y}}, Fail{Main.Refused{2, "`carry` carries one line of work, and `" ++ w ++ "` is a second"}})] : List<&2, Result<&2, &2, Main.Refused, Main.RwCmd>>}

# Every bookmark on the change of a revision `record` records onto moves
# with the work. Where one of the parents named is the identifier of a
# revision the store holds, and no revision the store lists before that one
# has the identifier, every bookmark the store holds on that revision's
# change is among those it moves, its name and its privacy as they were.
law record_moves_the_bookmarks_on_its_parents:
  for +a: String
  for +when: String
  for +message: String
  for +fl: Bool
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
  for +k: Nat
  for +p: String
  for hp: {List.get(&2, String, ps, k) == Some{p} : Maybe<&2, String>}
  for +m: Nat
  for +f: Main.Full
  for hf: {List.get(&2, Main.Full, fs, m) == Some{f} : Maybe<&2, Main.Full>}
  for hid: {Main.id_of(f) == p : String}
  for hfirst: {Rev.member(Main.ids(List.take(&2, Main.Full, fs, m)), p) == False{} : Bool}
  for +i: Nat
  for +n: String
  for +pr: Bool
  for hi: {List.get(&2, Bm.Bookmark, bs, i) == Some{Bm.Bookmark{n, Bm.Target.Change{Main.change_of(f)}, pr}} : Maybe<&2, Bm.Bookmark>}
  exs j: Nat
  {List.get(&2, Bm.Bookmark, Main.recorded.moving(Main.record.planned(Main.Writing{a, when, message, fl}, hex, befores, fs, bs, ps, t, hs, dg, reads, ks, moves, obs, ls)), j) == Some{Bm.Bookmark{n, Bm.Target.Change{Main.change_of(f)}, pr}} : Maybe<&2, Bm.Bookmark>}

# And no other moves: each bookmark `record` moves is one the store holds,
# on the change of a revision the store holds whose identifier is one of
# the parents named, no revision the store lists before that one having
# the identifier.
law record_moves_only_the_bookmarks_on_its_parents:
  for +a: String
  for +when: String
  for +message: String
  for +fl: Bool
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
  for +j: Nat
  for b: Bm.Bookmark
  for hj: {List.get(&2, Bm.Bookmark, Main.recorded.moving(Main.record.planned(Main.Writing{a, when, message, fl}, hex, befores, fs, bs, ps, t, hs, dg, reads, ks, moves, obs, ls)), j) == Some{b} : Maybe<&2, Bm.Bookmark>}
  exs i: Nat
  exs k: Nat
  exs m: Nat
  exs f: Main.Full
  {(List.get(&2, Bm.Bookmark, bs, i), (Bm.target_of(b), (List.get(&2, String, ps, k), (List.get(&2, Main.Full, fs, m), Rev.member(Main.ids(List.take(&2, Main.Full, fs, m)), Main.id_of(f)))))) == (Some{b}, (Bm.Target.Change{Main.change_of(f)}, (Some{Main.id_of(f)}, (Some{f}, False{})))) : Maybe<&2, Bm.Bookmark> & (Bm.Target & (Maybe<&2, String> & (Maybe<&2, Main.Full> & Bool)))}

# What `carry` says it wrote is what it files, named as the store will
# name it. Whatever it is asked to carry, with `--fields` it says
# `historica-wrote-1` and then, in its `revision` lines read back, exactly
# the revisions it files — each once, in digest order — each by the name
# the store reads it back under: the digest of the bytes `carry` files for
# it, wherever they are filed.
law carry_says_what_it_files:
  for +fs: List<&2, Main.Full>
  for +ds: List<&2, Store.Doc>
  for +c: Main.Carrying
  for +steps: List<&2, Main.Step>
  for e: {Main.carry.plan(fs, ds, c) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}
  for +path: String
  {Main.fields.ok(Main.steps.filed(path, steps), Main.carry.said.lines(True{}, False{}, steps)) == True{} : Bool}

# What `amend` rewrites, where a target is named, is the revision that
# target names: the one every command resolves the same spelling to.
law amend_rewrites_the_revision_named:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for +s: String
  for f: Main.Full
  for e: {Main.amend.target.r(fs, bs, Some{s}) == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}
  {Main.resolve(fs, bs, s) == Done{Main.id_of(f)} : Result<&2, &2, String, String>}

# With no target named, `amend` rewrites the one current head: where it
# goes on, the store's current heads are that revision and no other, so a
# store with several, or none, is refused rather than guessed at.
law amend_rewrites_the_one_head:
  for +fs: List<&2, Main.Full>
  for +bs: List<&2, Bm.Bookmark>
  for f: Main.Full
  for e: {Main.amend.target.r(fs, bs, None{}) == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}
  {Main.current_heads(Main.history(fs)) == [Main.id_of(f)] : List<&2, String>}

# `abandon` is asked which revision to abandon. It goes on only where its
# words name one, and what they name is one of the words it was given and
# not a flag: nothing is abandoned by default, and no flag is taken for a
# target.
law abandon_abandons_only_a_word_it_was_given:
  for +args: List<&2, String>
  for c: Main.RwCmd
  for e: {Main.abandon.words.r(args) == Done{c} : Result<&2, &2, Main.Refused, Main.RwCmd>}
  {Main.abandon.target.ok(args, Main.rw.named(c)) == True{} : Bool}

# A dry run is a plan, and `--fields` states what is on disk. Whatever
# words `abandon` reads, the check it makes of them before it reads any
# revision refuses `--dry-run --fields` after them as a usage error, with
# exit code 2.
law abandon_refuses_a_dry_run_with_fields:
  for +args: List<&2, String>
  for c: Main.RwCmd
  for e: {Main.rw.args.r("abandon", args) == Done{c} : Result<&2, &2, Main.Refused, Main.RwCmd>}
  {Main.refused.code(Main.RwCmd, Main.abandon.words.r(List.append(&2, String, args, ["--dry-run", "--fields"]))) == 2 : U32}

# `diff` over the folder compares like with like. For each path it plans,
# what it replays at the position and what it reads from the folder follow
# from what each side holds there. A file the position does not hold is
# read where the folder holds a regular file, and otherwise not, and
# nothing is replayed; a file of bytes or a link the position holds is
# neither replayed nor read, its digest or target compared instead; a file
# of lines the folder does not hold as a regular file is replayed and
# nothing read; and a file of lines the folder does hold as one is
# replayed exactly where the folder's file is read — so where one side is
# left an empty stand-in, so is the other.
law diff_folder_compares_like_with_like:
  for +dg: Map<&2, String>
  for +os: Map<&2, T.Split>
  for +eds: List<&2, Store.Doc>
  for +hs: List<&2, Main.Here>
  {Main.plans.like(Main.plans(dg, os, eds, hs)) == True{} : Bool}

# And it believes the digest a statement gives a file of lines. Where the
# file's nearest statement is `text` and a digest, and the host answered,
# for the regular file the folder holds at its path, a word with no space
# in it, a space and more, the folder's digest is that word; and the file
# is replayed at the position and read from the folder exactly where that
# word is not the digest the statement gives.
law diff_folder_believes_a_stated_digest:
  for +dg: Map<&2, String>
  for +os: Map<&2, T.Split>
  for +eds: List<&2, Store.Doc>
  for +path: String
  for +file: String
  for +at: String
  for +y: Maybe<&2, String>
  for +g: Maybe<&2, Tree.Target>
  for +m: Tree.Mode
  for +fp: String
  for +runs: Bool
  for +size: Nat
  for +d: String
  for +os2: Map<&2, T.Split>
  for ho: {Map.get(T.Split, T.Split{SNil{}, SNil{}}, os, file) == (os2, T.Split{"text", d}) : Map<&2, T.Split> & T.Split}
  for +w: String
  for hw: {T.all_chars(~(c => Bool.not(Char.is_eq(c, ' '))), w) == True{} : Bool}
  for +more: String
  for +dg2: Map<&2, String>
  for hd: {Map.get(String, SNil{}, dg, path) == (dg2, w ++ (" " ++ more)) : Map<&2, String> & String}
  {Main.plan(dg, os, eds, Main.Here{path, Some{Tree.Entry{file, at, Tree.Lines{}, y, g, m}}, Some{Folder.Found.File{fp, runs, size}}}) == Main.Planned{Main.Here{path, Some{Tree.Entry{file, at, Tree.Lines{}, y, g, m}}, Some{Folder.Found.File{fp, runs, size}}}, w, Bool.not(String.eq(d, w)), Bool.not(String.eq(d, w))} : Main.Planned}

# `diff` sizes a file of bytes only as the host stated. Sizing what it
# compares changes neither side of any comparison but a file of bytes whose
# size was unknown, which keeps its digest and is given a size only where a
# line the host answered begins with that very digest — not where the bytes
# it found at a path hash to another — and that size is the one the line
# states.
law diff_sizes_only_what_the_host_stated:
  for +found: List<&2, T.Split>
  for +stats: List<&2, String>
  for +cs: List<&2, Main.Compared>
  {Main.sizes.told(stats, cs, Main.sized(Main.sizes.read(found, stats), cs)) == True{} : Bool}

# And the work it compares the clock with, and names in that warning, is
# the latest it is handed: the one `newest` answers is one of them, and
# none of the others names a later instant.
law record_names_the_latest_work:
  for +ws: List<&2, String>
  for +w: String
  for e: {Naming.newest(ws, None{}) == Some{w} : Maybe<&2, String>}
  {Naming.latest(ws, w) == True{} : Bool}

# The instant a timestamp names is read at the offset it spells. The same
# nineteen characters of local time name, at an offset `+HH:MM` east of
# UTC, an instant that many hours and minutes before the one they name at
# UTC, spelled `Z`; and at `-HH:MM` west of it, that much after — for any
# offset of up to a day.
law a_timestamp_is_read_at_its_offset:
  for +base: String
  for hb: {String.length(base) == 19n : Nat}
  for +hh: String
  for hh2: {String.length(hh) == 2n : Nat}
  for +h: Nat
  for eh: {Nat.read(hh) == Some{h} : Maybe<&2, Nat>}
  for +mm: String
  for hm2: {String.length(mm) == 2n : Nat}
  for +m: Nat
  for em: {Nat.read(mm) == Some{m} : Maybe<&2, Nat>}
  for hd: {Nat.is_le(Nat.add(Nat.mul(h, 3600n), Nat.mul(m, 60n)), 86400n) == True{} : Bool}
  {[Nat.add(Nat.add(Nat.mul(h, 3600n), Nat.mul(m, 60n)), Naming.instant(base ++ ("+" ++ (hh ++ (":" ++ mm))))), Naming.instant(base ++ ("-" ++ (hh ++ (":" ++ mm))))] == [Naming.instant(base ++ "Z"), Nat.add(Naming.instant(base ++ "Z"), Nat.add(Nat.mul(h, 3600n), Nat.mul(m, 60n)))] : List<&2, Nat>}

# The manifest `offer` writes is the manifest `fetch` reads (decisions 0048
# and 0056). `offer` prints the lines `Offer.rendered` makes of a copy's
# heads and files, each with a newline after it; handed that text by the
# host as the document at the manifest's URL, `fetch` reads back every
# head, in order, and every file, in order — its kind, its digest, what it
# forgets and its path, spaces and all — wherever each head is a digest and
# each file is one `offer` can name: one of the six kinds, a digest, what
# it forgets a digest or nothing, and a path with no newline in it that
# does not end with a carriage return.
law fetch_reads_the_manifest_offer_writes:
  for +url: String
  for +hs: List<&2, String>
  for +os: List<&2, Offer.Offered>
  for +hh: {List.all(~&2, ~String, ~(d => T.is_digest(d)), hs) == True{} : Bool}
  for +ho: {List.all(~&2, ~Offer.Offered, ~(o => ManL.writable(o)), os) == True{} : Bool}
  {Fetch.manifest.got(url, Fetch.got.of(Done{"text\n" ++ ManL.printed(Offer.rendered(hs, os))})) == Done{Fetch.Manifest{hs, os}} : Result<&2, &2, Main.Refused, Fetch.Manifest>}

# `fetch` refuses a copy as unrelated only where decision 0052 says it
# must: joining was not asked, this store holds a revision, the manifest
# lists one, and no revision it lists is one this store holds or one a
# revision here names as a parent or as what it supersedes — the two of
# decision 0029's arms a listing of digests can answer.
law fetch_refuses_only_what_shares_no_revision:
  for +h: Fetch.Here
  for +os: List<&2, Offer.Offered>
  for +join: Bool
  for +x: String
  for r: Main.Refused
  for +e: {Fetch.plan.r(h, os, join) == Fail{r} : Result<&2, &2, Main.Refused, Fetch.FPlan>}
  {Bool.and(Bool.not(join), Bool.and(Bool.not(List.is_empty(&2, Main.Full, Fetch.here.revs(h))), Bool.and(Bool.not(List.is_empty(&2, String, FPlanL.theirs(os))), Bool.not(Bool.and(Rev.member(FPlanL.theirs(os), x), Rev.member(FPlanL.ours(Fetch.here.revs(h)), x)))))) == True{} : Bool}

# And it does refuse there, in the Rust tool's words: where joining is not
# asked, each side holds a revision, and no revision the manifest lists is
# one this store holds or names.
law fetch_refuses_what_shares_no_revision:
  for +h: Fetch.Here
  for +os: List<&2, Offer.Offered>
  for hr: {List.is_empty(&2, Main.Full, Fetch.here.revs(h)) == False{} : Bool}
  for +ht: {List.is_empty(&2, String, FPlanL.theirs(os)) == False{} : Bool}
  for hn: @x: String -> {Rev.member(FPlanL.theirs(os), x) == True{} : Bool} -> {Rev.member(FPlanL.ours(Fetch.here.revs(h)), x) == False{} : Bool}
  {Fetch.plan.r(h, os, False{}) == Fail{Main.Refused{1, Fetch.UNRELATED()}} : Result<&2, &2, Main.Refused, Fetch.FPlan>}

# Every original `fetch` destroys is one a forgetting document of this
# store stands in for, or one a line of the manifest says its file forgets
# (decision 0014): said of the documents and the lines themselves, not of
# the list of digests the plan draws up from them.
law fetch_destroys_only_what_is_forgotten:
  for +s: Receive.Side
  for +os: List<&2, Offer.Offered>
  for +d: String
  for h: {Rev.member(Fetch.plan.destroys(Fetch.plan.of(Fetch.here.of(s), os)), d) == True{} : Bool}
  {Bool.or(Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(s)), d), FPlanL.forgot.listed(os, d)) == True{} : Bool}

# In one pass `fetch` writes a bookmark once (decision 0062): once it has
# written bookmark `n`, whatever the host answers for a later line naming
# `n`, it writes no bookmark for it — though two lines of a manifest may
# name one bookmark with different bytes, and the plan takes both.
law fetch_writes_a_bookmark_once_a_pass:
  for +o: Offer.Offered
  for +n: String
  for +at: String
  for +text: String
  for +t: Fetch.Tally
  for +rules: List<&2, Receive.Ruled>
  for +held: List<&2, String>
  for +moved: Maybe<&2, String>
  for +landed: Bool
  for +root: String
  for +o2: Offer.Offered
  for g: Fetch.Got
  for +h: {Fetch.named_by(Offer.offered.path(o2)) == Some{n} : Maybe<&2, String>}
  {FetchingL.writes_a_bookmark(Fetch.got.text(root, Fetch.state.held(Fetch.land.after(o, Fetch.Land.Name{n, at, text}, t, rules, held, moved, landed)), o2, g)) == False{} : Bool}

# `fetch` asks only for what this store lacks: every payload it asks for is
# one this store holds no payload under the digest of, and one neither a
# forgetting document here nor a line of the manifest forgets — so no
# original a forgetting document stands in for is fetched back.
law fetch_asks_for_no_payload_held_or_forgotten:
  for +s: Receive.Side
  for +os: List<&2, Offer.Offered>
  for +d: String
  for m: {Rev.member(FPlanL.digests(Fetch.plan.payloads(Fetch.plan.of(Fetch.here.of(s), os))), d) == True{} : Bool}
  {Bool.or(Rev.member(FPlanL.pays.of(s), d), Bool.or(Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(s)), d), FPlanL.forgot.listed(os, d))) == False{} : Bool}

# And every document of `operations/` it asks for, the same: none this
# store holds a document under the digest of, and none either side
# forgets.
law fetch_asks_for_no_document_held_or_forgotten:
  for +s: Receive.Side
  for +os: List<&2, Offer.Offered>
  for +d: String
  for m: {Rev.member(FPlanL.digests(Fetch.plan.documents(Fetch.plan.of(Fetch.here.of(s), os))), d) == True{} : Bool}
  {Bool.or(Rev.member(FPlanL.docs.of(s), d), Bool.or(Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(s)), d), FPlanL.forgot.listed(os, d))) == False{} : Bool}

# And every revision it asks for is one this store does not hold.
law fetch_asks_for_no_revision_it_holds:
  for +s: Receive.Side
  for +os: List<&2, Offer.Offered>
  for +d: String
  for m: {Rev.member(FPlanL.digests(Fetch.plan.revisions(Fetch.plan.of(Fetch.here.of(s), os))), d) == True{} : Bool}
  {Rev.member(Main.ids(Receive.side.fulls(s)), d) == False{} : Bool}

# Asked for `--fields`, what `fetch` says of what it took is decision
# 0074's: `historica-wrote-1` first, and then a `revision` line for each
# revision it took — each named once, in digest order, and none named that
# it did not take.
law fetch_says_what_it_took:
  for +rs: List<&2, String>
  for +ds: Nat
  for +ps: Nat
  for +rus: Nat
  for +res: Nat
  for +ns: List<&2, String>
  for +k: Nat
  for +dec: List<&2, Fetch.Declined>
  for +des: Nat
  for +re: Nat
  {Main.fields.ok(rs, Fetch.said.done(True{}, Fetch.Tally{rs, ds, ps, rus, res, ns, k, dec, des, re})) == True{} : Bool}

# `fetch` asks for a manifest's path by its bytes, as the Rust tool spells
# them: whatever the bytes, what it asks for decodes — each escape read as
# RFC 3986 asks a producer to spell one, `%` and two uppercase hex digits
# — back to exactly those bytes.
law fetch_asks_for_a_path_by_its_bytes:
  for +bs: List<&2, U32>
  for +h: {List.all(~&2, ~U32, ~(b => U32.is_lt(b, 256)), bs) == True{} : Bool}
  {EscL.unescaped(Fetch.escaped.bytes(bs)) == Some{bs} : Maybe<&2, List<&2, U32>>}

# And what it asks for holds nothing a URL's path may not hold as it is:
# every character is one RFC 3986 leaves unreserved, `/`, or the `%` that
# opens an escape.
law fetch_asks_in_characters_a_url_may_hold:
  for +bs: List<&2, U32>
  for +h: {List.all(~&2, ~U32, ~(b => U32.is_lt(b, 256)), bs) == True{} : Bool}
  {T.all_chars(~(c => EscL.url_char(c)), Fetch.escaped.bytes(bs)) == True{} : Bool}

# And it escapes nothing it need not: each character RFC 3986 leaves
# unreserved, and `/`, is asked for as itself. With the two laws above,
# that is the whole of how a byte of a path is spelled.
law fetch_asks_for_what_is_unreserved_as_itself:
  {List.all(~&2, ~Char, ~(c => String.eq(Fetch.escaped.byte(Char.to_u32(c)), SCon{c, SNil{}})), String.to_list("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-._~/")) == True{} : Bool}

# `init` lays down nothing outside the store it names: every directory it
# makes and every note it writes is the root, a `/`, and components none
# of them empty, `.` or `..`; and each note goes in the root or in a
# directory it makes — whatever the root is.
law init_lays_down_only_its_store:
  for +root: String
  {InitL.within(root, Main.init.layout(root)) == True{} : Bool}

# Every note `init` writes is text as the format holds it — `format.txt`'s
# "UTF-8 text with Unix line endings": lines, each ended by a newline, of
# Unicode scalar values none of which is a control character.
law init_writes_text:
  for +root: String
  {InitL.texts(Main.init.layout(root)) == True{} : Bool}

# `init` joins `<dir>` to the directory it runs in as `Path::join` joins
# it. An absolute `<dir>` is where the store goes, wherever `init` runs.
law init_takes_an_absolute_dir_as_it_is:
  for +base: String
  for +other: String
  for +d: String
  {Main.init.root(base, Some{"/" ++ d}) == Main.init.root(other, Some{"/" ++ d}) : String}

# A `/` after `<dir>` is not doubled: `init sub/` makes the store
# `init sub` makes.
law init_doubles_no_slash:
  for +base: String
  for +d: String
  for +e: {String.is_empty(d) == False{} : Bool}
  for +f: {String.ends_with(d, "/") == False{} : Bool}
  {Main.init.root(base, Some{d ++ "/"}) == Main.init.root(base, Some{d}) : String}

# And `.` is joined, not resolved: `init .` names `<base>/./history`, as
# the Rust tool says it.
law init_keeps_a_dot:
  for +base: String
  for e: {String.is_empty(base) == False{} : Bool}
  for f: {String.ends_with(base, "/") == False{} : Bool}
  {Main.init.root(base, Some{"."}) == base ++ "/./history" : String}

# What the port writes as bytes the store reads back as what it wrote: a
# string of Unicode scalar values, encoded as UTF-8 and read as the store
# reads a file as text — `read_to_string`, which refuses bytes that are not
# UTF-8 — is itself, every character at every one of its four widths.
law utf8_reads_back:
  for +s: String
  for +h: {Utf8L.scalars(s) == True{} : Bool}
  {Store.utf8.of(Utf8.encode(s)) == Done{s} : Result<&2, &2, String, String>}

# And nothing else: a file it skips is the path named, or, for a
# directory, the path named, a `/`, and the rest — so the rule for `v`
# skips neither `vx` nor, for a file, anything under `v/` — and a
# directory it skips whole is the one named.
law skip_path_rule_skips_nothing_else:
  for +v: String
  for +directory: Bool
  for +sc: Folder.Scope
  for e: {Skip.path.scoped(v, directory) == Done{sc} : Result<&2, &2, Main.Refused, Folder.Scope>}
  for +q: String
  for s: {Folder.skips([sc], q) == True{} : Bool}
  {q == Bool.pick(String, directory, String.append(v ++ "/", String.drop(q, String.length(v ++ "/"))), v) : String}

law skip_path_rule_skips_no_other_directory:
  for +v: String
  for +directory: Bool
  for +sc: Folder.Scope
  for e: {Skip.path.scoped(v, directory) == Done{sc} : Result<&2, &2, Main.Refused, Folder.Scope>}
  for +p: String
  for s: {Folder.skips_directory([sc], p) == True{} : Bool}
  {p == v : String}

# `skip` reads every word it is given, in order: spelled back — a
# `--private` as itself, a `--name` and the word after it, a path as
# itself, and, where reading stopped, the words from the one refused on —
# what it read is the words.
law skip_reads_its_words:
  for +ws: List<&2, String>
  {SkipL.spelled(Skip.read(ws)) == ws : List<&2, String>}

# And it takes each word for what it is: no word it reads as a path is a
# flag, and it stops only at a flag it does not take — anything opening
# `--` but `--private`, and `--name` only with nothing after it to name.
law skip_reads_flags_as_flags:
  for +ws: List<&2, String>
  {SkipL.plain(Skip.read(ws)) == True{} : Bool}

# `--private` makes every rule `skip` writes private wherever it stands
# among words read without a refusal: the rules are each scope asked for,
# in order, and private.
law skip_private_wherever_it_stands:
  for +before: List<&2, String>
  for +after: List<&2, String>
  for c: {SkipL.clean(Skip.read(before)) == True{} : Bool}
  for +ss: List<&2, Folder.Scope>
  {Skip.wanted(Skip.Asked{ss, Skip.private.of(Skip.read(List.append(&2, String, before, "--private" <> after)))}) == T.map(~Folder.Scope, ~Skip.Rule, ~(sc => Skip.Rule{sc, True{}}), ss) : List<&2, Skip.Rule>}

# And where no word is `--private`, every rule it writes is shared.
law skip_shares_without_private:
  for +ws: List<&2, String>
  for h: {Rev.member(ws, "--private") == False{} : Bool}
  for +ss: List<&2, Folder.Scope>
  {Skip.wanted(Skip.Asked{ss, Skip.private.of(Skip.read(ws))}) == T.map(~Folder.Scope, ~Skip.Rule, ~(sc => Skip.Rule{sc, False{}}), ss) : List<&2, Skip.Rule>}

# `skip <path>` reads the rule's path as what lies past the repository, as
# the path really is: where its components are the repository's and more,
# the first of those not empty, the rule's path is the further components
# joined by `/`.
law skip_reads_the_path_past_the_repository:
  for +path: String
  for +repo: String
  for +settled: String
  for +x: String
  for +more: List<&2, String>
  for e: {Identity.components(settled) == List.append(&2, String, Identity.components(repo), x <> more) : List<&2, String>}
  for hx: {String.is_empty(x) == False{} : Bool}
  {Skip.inside.r(path, repo, settled) == Done{String.join(x <> more, "/")} : Result<&2, &2, Main.Refused, String>}

# It refuses the repository itself, since a rule for all of it would leave
# history nothing to hold ...
law skip_refuses_the_repository_itself:
  for +path: String
  for +repo: String
  for +settled: String
  for e: {Identity.components(settled) == Identity.components(repo) : List<&2, String>}
  {Skip.inside.r(path, repo, settled) == Fail{Main.Refused{1, "that is the repository itself, and skipping all of it would leave history nothing to hold"}} : Result<&2, &2, Main.Refused, String>}

# ... and a path that stops, or turns aside, before the repository's
# components end, which is not inside it.
law skip_refuses_a_path_outside_the_repository:
  for +path: String
  for +repo: String
  for +settled: String
  for +pre: List<&2, String>
  for +y: String
  for +r1: List<&2, String>
  for +zs: List<&2, String>
  for er: {Identity.components(repo) == List.append(&2, String, pre, y <> r1) : List<&2, String>}
  for es: {Identity.components(settled) == List.append(&2, String, pre, zs) : List<&2, String>}
  for h: {SkipL.turns(y, zs) == True{} : Bool}
  {Skip.inside.r(path, repo, settled) == Fail{Main.Refused{1, "`" ++ path ++ "` is not inside this repository, and a rule names what history would otherwise take"}} : Result<&2, &2, Main.Refused, String>}

# Where `skip` goes on to write its rules, no rule it writes skips a file
# any head holds, read with the loader's own `skips`: decision 0011, a rule
# cannot take back what is recorded — so wherever some head's tree holds a
# file a rule asked for covers, `skip` refuses.
law skip_covers_nothing_history_holds:
  for +fs: List<&2, Main.Full>
  for +rs: List<&2, Skip.Rule>
  for e: {Skip.covered.r(fs, rs) == Done{Unit{}} : Result<&2, &2, Main.Refused, Unit>}
  for +h: String
  for hh: {Rev.member(Rev.heads(Main.history(fs)), h) == True{} : Bool}
  for +t: Tree.Tree()
  for +et: {Main.tree.r(fs, h) == Done{t} : Result<&2, &2, Main.Refused, Tree.Tree()>}
  for +p: String
  for +hp: {Rev.member(SkipL.paths(t), p) == True{} : Bool}
  {Folder.skips(SkipL.scopes(rs), p) == False{} : Bool}

# `check`'s report is every error it found, in the order found, then every
# note, each on its own line under its word — so each finding once — then
# how many of each, `nothing to report` only where it found nothing at
# all; and, where a head cannot be produced from what is here, how many,
# naming `--complete` to a caller who did not ask for it.
law check_reports_errors_then_notes:
  for +fs: List<&2, Check.Finding>
  for +shown: String
  for +complete: Bool
  {Check.report(fs, shown, complete) == FindL.reported(fs, shown, complete) : String}

# `check` reads a bookmark file `name` wrote for a well-formed target as
# that bookmark: it finds nothing wrong where what it points at is here —
# the revision by its digest, a revision of the change, or a revision
# stating a fact about the file (decision 0024) — and otherwise notes, and
# only notes, that it is not here yet.
law check_follows_the_bookmarks_name_writes:
  for +docs: List<&2, Main.Full>
  for +path: String
  for +n: String
  for +t: Bm.Target
  for +p: Bool
  for +h: {Bm.target_ok(t) == True{} : Bool}
  {Check.name.text(docs, path, n, Done{Bm.write(Bm.Stated{t, p})}) == Bool.pick(List<&2, Check.Finding>, FindL.here(docs, t), Nil{}, [Check.note("`" ++ n ++ "` points at `" ++ Bm.show_target(t) ++ "`, which is not here yet")]) : List<&2, Check.Finding>}

# `check` reads each line of a directory's listing as the host writes it,
# whatever it found before and whatever follows: a directory is the one
# to walk next, a file is found by its name, spaces and all, a link is
# found and the line of its target passed over whatever it says — never
# followed — a link whose target cannot be spelled is found all the same,
# and a name that is not UTF-8, or anything else, is passed over; each
# under the directory listed.
law check_reads_each_line_of_a_listing:
  for +ds: List<&2, String>
  for +fs: List<&2, String>
  for +ls: List<&2, String>
  for t: Bool
  for +dir: String
  for e: FindL.Listed
  for +rest: String
  for +h: {FindL.spelt(e) == True{} : Bool}
  {Check.walk.step(Check.Seen{ds, fs, ls, t}, dir, Done{FindL.line(e) ++ "\n" ++ rest}) == Check.seen.go(String.split(rest, '\n'), dir, FindL.found(e, dir, fs, ls)) : Check.Seen}

# `check` reads as a file's lines only payloads the store holds under a
# digest some revision's `text` header names, each from where the store
# holds it.
law check_reads_only_held_text:
  for +docs: List<&2, Main.Full>
  for +ps: List<&2, Check.Stored>
  {FindL.reads_held(Check.texts.plan(Check.set.of(Check.text.ids(docs)), ps), ps, Check.text.ids(docs)) == True{} : Bool}

# `check` fails exactly where it found an error, `check --complete` also
# where it found a head it cannot produce, and a note alone fails neither.
law check_fails_on_an_error:
  for +fs: List<&2, Check.Finding>
  for complete: Bool
  {Check.fails(fs, complete) == Bool.or(List.any(~&2, ~Check.Finding, ~(f => Check.is_error(f)), fs), Bool.and(complete, List.any(~&2, ~Check.Finding, ~(f => Check.is_head(f)), fs))) : Bool}
