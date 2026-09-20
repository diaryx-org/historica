# Semantic replay of one edit block at an arbitrary valid parent gap.
# The parent split witnesses the gap; deletion range and quote agreement
# remain checked, and the output comes only from the positional model.
import Base
import ./ops.bend as Ops
import ./replay_spec.bend as Spec
import ./cursor_spec.bend as Cursor

def agrees(edit: Ops.Edit, after: List<&2, Ops.Item>) -> Bool:
  match edit:
    case Ops.Insertion{items}:
      True{}
    case Ops.Deletion{recorded}:
      Spec.prefix_matches(recorded, after)
    case Ops.Replacement{recorded, inserted}:
      Spec.prefix_matches(recorded, after)

def raw(+before: List<&2, Ops.Item>, +after: List<&2, Ops.Item>, +edit: Ops.Edit) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  +at = List.length(&2, Ops.Item, before)
  Cursor.combine(Cursor.disagreement(at, agrees(edit, after)), Nil{},
    Done{Spec.result(List.append(&2, Ops.Item, before, after), Ops.operations(at, edit))})

# Range, newline and digest validators are shared with Ops.apply. This
# specification independently assembles the output, not those validators.
def apply(+before: List<&2, Ops.Item>, +after: List<&2, Ops.Item>, stated: Maybe<&2, String>, +edit: Ops.Edit) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  Cursor.checked(Ops.in_range(Ops.operations(List.length(&2, Ops.Item, before), edit), List.length(&2, Ops.Item, List.append(&2, Ops.Item, before, after))), stated, raw(before, after, edit))

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

# A whole ordered document, by its operations rather than its script.
def replay_ops(+parent: List<&2, Ops.Item>, stated: Maybe<&2, String>, +ops: List<&2, Ops.Op>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  Cursor.checked(Ops.in_range(ops, List.length(&2, Ops.Item, parent)), stated,
    Cursor.combine(quote_error(parent, ops), Nil{}, Done{Spec.result(parent, ops)}))

# A whole script: the positional result, refused where a quote disagrees,
# behind the same range, newline and digest validators as Ops.apply.
def replay(+parent: List<&2, Ops.Item>, stated: Maybe<&2, String>, steps: List<&2, Ops.Step>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  replay_ops(parent, stated, Ops.script(steps, 0n))

# Whether raw operations are a script: each sits at or past where the last
# finished, except an insert at a delete's own position, which is that
# delete's replacement. The parser refuses more than this; the theorem
# needs no more than this.
def ordered(ops: List<&2, Ops.Op>, +pos: Nat) -> Bool:
  match ops:
    case Nil{}:
      True{}
    case Ops.Op{Ops.Insert{}, +at, items} <> rest:
      Bool.and(Nat.is_le(pos, at), ordered(rest, at))
    case Ops.Op{Ops.Delete{}, +at, +items} <> rest:
      match rest:
        case Nil{}:
          Nat.is_le(pos, at)
        case Ops.Op{Ops.Insert{}, +at2, items2} <> +more:
          +stop = Nat.add(at, List.length(&2, Ops.Item, items))
          Bool.and(Nat.is_le(pos, at), Bool.pick(Bool, Nat.is_eq(at2, at), ordered(more, stop), Bool.and(Nat.is_le(stop, at2), ordered(more, at2))))
        case Ops.Op{Ops.Delete{}, +at2, +items2} <> +more:
          Bool.and(Nat.is_le(pos, at), ordered(Ops.Op{Ops.Delete{}, at2, items2} <> more, Nat.add(at, List.length(&2, Ops.Item, items))))

# The script an ordered operation list is, read from `pos`.
def steps_of(ops: List<&2, Ops.Op>, +pos: Nat) -> List<&2, Ops.Step>:
  match ops:
    case Nil{}:
      Nil{}
    case Ops.Op{Ops.Insert{}, +at, items} <> rest:
      Ops.Step{Nat.sub(at, pos), Ops.Insertion{items}} <> steps_of(rest, at)
    case Ops.Op{Ops.Delete{}, +at, +items} <> rest:
      match rest:
        case Nil{}:
          [Ops.Step{Nat.sub(at, pos), Ops.Deletion{items}}]
        case Ops.Op{Ops.Insert{}, +at2, +items2} <> +more:
          +stop = Nat.add(at, List.length(&2, Ops.Item, items))
          Bool.pick(List<&2, Ops.Step>, Nat.is_eq(at2, at),
            Ops.Step{Nat.sub(at, pos), Ops.Replacement{items, items2}} <> steps_of(more, stop),
            Ops.Step{Nat.sub(at, pos), Ops.Deletion{items}} <> Ops.Step{Nat.sub(at2, stop), Ops.Insertion{items2}} <> steps_of(more, at2))
        case Ops.Op{Ops.Delete{}, +at2, +items2} <> +more:
          Ops.Step{Nat.sub(at, pos), Ops.Deletion{items}} <> steps_of(Ops.Op{Ops.Delete{}, at2, items2} <> more, Nat.add(at, List.length(&2, Ops.Item, items)))
