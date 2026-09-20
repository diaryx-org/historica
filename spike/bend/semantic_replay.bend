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

# A document as a script of blocks. Each block sits `gap` parent items past
# where the previous block finished, so the blocks never overlap and never
# run backwards: the shape the parser's ordering rules admit.
type Step is Data:
  Step{gap: Nat, edit: Edit}

# How many parent items a block removes; the next block counts from there.
def consumed(edit: Edit) -> Nat:
  match edit:
    case Insertion{items}:
      0n
    case Deletion{recorded}:
      List.length(&2, Ops.Item, recorded)
    case Replacement{recorded, inserted}:
      List.length(&2, Ops.Item, recorded)

# What a block puts where the consumed items were.
def inserted(edit: Edit) -> List<&2, Ops.Item>:
  match edit:
    case Insertion{items}:
      items
    case Deletion{recorded}:
      Nil{}
    case Replacement{recorded, items}:
      items

def script(steps: List<&2, Step>, +at: Nat) -> List<&2, Ops.Op>:
  match steps:
    case Nil{}:
      Nil{}
    case Step{gap, +edit} <> rest:
      +here = Nat.add(at, gap)
      List.append(&2, Ops.Op, operations(here, edit), script(rest, Nat.add(here, consumed(edit))))

# Every delete read at its own absolute coordinate in the parent; the first
# that quotes what the parent does not hold there is the refusal.
def quote_error(+parent: List<&2, Ops.Item>, ops: List<&2, Ops.Op>) -> Maybe<&2, String>:
  match ops:
    case Nil{}:
      None{}
    case Ops.Op{Ops.Insert{}, at, items} <> rest:
      quote_error(parent, rest)
    case Ops.Op{Ops.Delete{}, +at, items} <> rest:
      Maybe.or(&2, String, Cursor.disagreement(at, Spec.prefix_matches(items, List.drop(&2, Ops.Item, parent, at))), quote_error(parent, rest))

# A whole script: the positional result, refused where a quote disagrees,
# behind the same range, newline and digest validators as Ops.apply.
def replay(+parent: List<&2, Ops.Item>, stated: Maybe<&2, String>, steps: List<&2, Step>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  +ops = script(steps, 0n)
  Cursor.checked(Ops.in_range(ops, List.length(&2, Ops.Item, parent)), stated,
    Cursor.combine(quote_error(parent, ops), Nil{}, Done{Spec.result(parent, ops)}))
