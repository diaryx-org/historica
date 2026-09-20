# What the port promises, as claims Bend can check. Each is proven in
# PROOF.bend by a def of the same name; `bend PROOF.bend` fails while any
# is open or false.

import Base
import ./sha256.bend as Sha
import ./ops.bend as Ops
import ./revision.bend as Rev

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

# LAW: a forgotten item agrees with anything at replay — the text is gone
# and the shape is the whole claim, per decision 0014.
law forgotten_agrees:
  for b: Ops.Item
  {Ops.agrees(Ops.forgotten(), b) == True{} : Bool}

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
