# Semantic replay of one edit block at an arbitrary valid parent gap.
# The parent split witnesses the gap; deletion range and quote agreement
# remain checked, and the output comes only from the positional model.
import Base
import ./ops.bend as Ops
import ./replay_spec.bend as Spec
import ./cursor_spec.bend as Cursor

type Edit is Data:
  Insertion{items: List<&2, Ops.Item>}
  Deletion{recorded: List<&2, Ops.Item>}
  Replacement{recorded: List<&2, Ops.Item>, inserted: List<&2, Ops.Item>}

def operations(+at: Nat, edit: Edit) -> List<&2, Ops.Op>:
  match edit:
    case Insertion{items}:
      [Ops.Op{Ops.Insert{}, at, items}]
    case Deletion{recorded}:
      [Ops.Op{Ops.Delete{}, at, recorded}]
    case Replacement{recorded, inserted}:
      [Ops.Op{Ops.Delete{}, at, recorded}, Ops.Op{Ops.Insert{}, at, inserted}]

def agrees(edit: Edit, after: List<&2, Ops.Item>) -> Bool:
  match edit:
    case Insertion{items}:
      True{}
    case Deletion{recorded}:
      Spec.prefix_matches(recorded, after)
    case Replacement{recorded, inserted}:
      Spec.prefix_matches(recorded, after)

def raw(+before: List<&2, Ops.Item>, +after: List<&2, Ops.Item>, +edit: Edit) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  +at = List.length(&2, Ops.Item, before)
  Cursor.combine(Cursor.disagreement(at, agrees(edit, after)), Nil{},
    Done{Spec.result(List.append(&2, Ops.Item, before, after), operations(at, edit))})

# Range, newline and digest validators are shared with Ops.apply. This
# specification independently assembles the output, not those validators.
def apply(+before: List<&2, Ops.Item>, +after: List<&2, Ops.Item>, stated: Maybe<&2, String>, +edit: Edit) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  Cursor.checked(Ops.in_range(operations(List.length(&2, Ops.Item, before), edit), List.length(&2, Ops.Item, List.append(&2, Ops.Item, before, after))), stated, raw(before, after, edit))
