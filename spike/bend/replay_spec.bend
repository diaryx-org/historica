# An executable specification transcribed from spike/verus/replay.rs.
# It reads facts at each parent position, independently of Ops.apply's
# cursor and reversed accumulator. This is an oracle, not the fast path.
import Base
import ./ops.bend as Ops
import ./text.bend as T

# A forgotten payload cannot erase a disagreement about its terminator.
def matches_text(a: String, f: Bool, b: String, g: Bool) -> Bool:
  match f g:
    case True{} _:
      True{}
    case False{} True{}:
      True{}
    case False{} False{}:
      T.same(a, b)

def matches_shape(n: Bool, m: Bool, a: String, f: Bool, b: String, g: Bool) -> Bool:
  match n m:
    case False{} True{}:
      False{}
    case True{} False{}:
      False{}
    case False{} False{}:
      matches_text(a, f, b, g)
    case True{} True{}:
      matches_text(a, f, b, g)

def matches(recorded: Ops.Item, found: Ops.Item) -> Bool:
  match recorded found:
    case Ops.Item{a, n, f} Ops.Item{b, m, g}:
      matches_shape(n, m, a, f, b, g)

# Every quoted item has a corresponding, matching parent item.
def prefix_matches(recorded: List<&2, Ops.Item>, parent: List<&2, Ops.Item>) -> Bool:
  match recorded parent:
    case Nil{} _:
      True{}
    case r <> rs Nil{}:
      False{}
    case r <> rs p <> ps:
      Bool.and(matches(r, p), prefix_matches(rs, ps))

def deleted_at(ops: List<&2, Ops.Op>, +p: Nat) -> Bool:
  match ops:
    case Nil{}:
      False{}
    case Ops.Op{Ops.Insert{}, at, items} <> rest:
      deleted_at(rest, p)
    case Ops.Op{Ops.Delete{}, +at, items} <> rest:
      Bool.or(Bool.and(Nat.is_le(at, p), Nat.is_lt(p, Nat.add(at, List.length(&2, Ops.Item, items)))), deleted_at(rest, p))

def inserts_at(ops: List<&2, Ops.Op>, +p: Nat) -> List<&2, Ops.Item>:
  match ops:
    case Nil{}:
      Nil{}
    case Ops.Op{Ops.Delete{}, at, items} <> rest:
      inserts_at(rest, p)
    case Ops.Op{Ops.Insert{}, at, items} <> rest:
      List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Nat.is_eq(at, p), items, Nil{}), inserts_at(rest, p))

def result_from(parent: List<&2, Ops.Item>, +ops: List<&2, Ops.Op>, +p: Nat) -> List<&2, Ops.Item>:
  match parent:
    case Nil{}:
      inserts_at(ops, p)
    case it <> rest:
      List.append(&2, Ops.Item, inserts_at(ops, p),
        List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, deleted_at(ops, p), Nil{}, [it]), result_from(rest, ops, 1n+p)))

# Like Verus result, this states output only: range, agreement, newline and
# digest validity are separate conditions, not silently checked here.
def result(parent: List<&2, Ops.Item>, ops: List<&2, Ops.Op>) -> List<&2, Ops.Item>:
  result_from(parent, ops, 0n)

# Translate document coordinates without changing the items or their order.
# This is a proof tool: the executable replay still receives absolute offsets.
def shift(ops: List<&2, Ops.Op>, +offset: Nat) -> List<&2, Ops.Op>:
  match ops:
    case Nil{}:
      Nil{}
    case Ops.Op{verb, at, items} <> rest:
      Ops.Op{verb, Nat.add(offset, at), items} <> shift(rest, offset)
