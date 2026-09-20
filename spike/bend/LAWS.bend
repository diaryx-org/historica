# What the port promises, as claims Bend can check. Each is proven in
# PROOF.bend by a def of the same name; `bend PROOF.bend` fails while any
# is open or false.

import Base
import ./sha256.bend as Sha
import ./ops.bend as Ops
import ./revision.bend as Rev
import ./replay_spec.bend as Spec
import ./cursor_spec.bend as Cursor
import ./semantic_replay.bend as Block

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
  for +edit: Block.Edit
  {Ops.apply(List.append(&2, Ops.Item, before, after), Ops.Doc{None{}, stated, Block.operations(List.length(&2, Ops.Item, before), edit)}) == Block.apply(before, after, stated, edit) : Result<&2, &2, String, List<&2, Ops.Item>>}

# A whole script of blocks — each starting a stated gap past where the last
# finished, which is every shape the parser's ordering rules admit — replays
# to the positional result of its operations, or to the first delete whose
# quote the parent does not hold at that delete's own coordinate. Nothing
# about the cursor appears on the right-hand side.
law script_semantics:
  for +parent: List<&2, Ops.Item>
  for +stated: Maybe<&2, String>
  for +steps: List<&2, Block.Step>
  {Ops.apply(parent, Ops.Doc{None{}, stated, Block.script(steps, 0n)}) == Block.replay(parent, stated, steps) : Result<&2, &2, String, List<&2, Ops.Item>>}

# Raw operations are a script when each sits at or past where the last
# finished, an insert at a delete's own position being that delete's
# replacement (`Block.ordered`); `Block.steps_of` reads the script off them.
law ordered_operations_are_scripts:
  for +ops: List<&2, Ops.Op>
  for +pos: Nat
  for +e: {Block.ordered(ops, pos) == True{} : Bool}
  {Block.script(Block.steps_of(ops, pos), pos) == ops : List<&2, Ops.Op>}

# So any ordered document replays to its positional result, stated over the
# operations themselves. What is left for the parser is that it only
# accepts ordered documents.
law ordered_document_semantics:
  for +parent: List<&2, Ops.Item>
  for +stated: Maybe<&2, String>
  for +ops: List<&2, Ops.Op>
  for +e: {Block.ordered(ops, 0n) == True{} : Bool}
  {Ops.apply(parent, Ops.Doc{None{}, stated, ops}) == Block.replay_ops(parent, stated, ops) : Result<&2, &2, String, List<&2, Ops.Item>>}
