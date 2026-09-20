# A forward-order specification of the complete cursor walk. This removes
# Ops.apply's reversed accumulator as an intermediate proof step; equality
# to the position-based replay_spec.result remains a separate theorem.
# No advance, drop_checked, land, or apply.go is used here.
import Base
import ./ops.bend as Ops
import ./replay_spec.bend as Spec

def prefix(state: List<&2, Ops.Item>, at: Nat, pos: Nat) -> List<&2, Ops.Item>:
  List.take(&2, Ops.Item, state, Nat.sub(at, pos))

def suffix(state: List<&2, Ops.Item>, at: Nat, pos: Nat) -> List<&2, Ops.Item>:
  List.drop(&2, Ops.Item, state, Nat.sub(at, pos))

def disagreement(at: Nat, ok: Bool) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, ok, None{}, Some{"a delete at " ++ Nat.show(at) ++ " quotes lines the parent does not hold"})

# Prepend an earlier successful segment, or preserve the earliest error.
def combine(error: Maybe<&2, String>, front: List<&2, Ops.Item>, later: Result<&2, &2, String, List<&2, Ops.Item>>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match error later:
    case Some{e} _:
      Fail{e}
    case None{} Fail{e}:
      Fail{e}
    case None{} Done{items}:
      Done{List.append(&2, Ops.Item, front, items)}

# Each operation contributes a forward prefix; recursion contributes the
# remainder. Saturating subtraction deliberately describes even raw,
# noncanonical Docs exactly as the implementation executes them.
def walk(ops: List<&2, Ops.Op>, +pos: Nat, +state: List<&2, Ops.Item>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match ops:
    case Nil{}:
      Done{state}
    case Ops.Op{Ops.Insert{}, +at, items} <> rest:
      combine(None{}, List.append(&2, Ops.Item, prefix(state, at, pos), items),
        walk(rest, Nat.max(pos, at), suffix(state, at, pos)))
    case Ops.Op{Ops.Delete{}, +at, +items} <> rest:
      combine(disagreement(at, Spec.prefix_matches(items, suffix(state, at, pos))), prefix(state, at, pos),
        walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, suffix(state, at, pos), List.length(&2, Ops.Item, items))))

# The public boundary uses the same range, termination and digest validators.
# Equality to this spec proves the cursor wiring, not those validators.
def checked(in_range: Bool, result: Maybe<&2, String>, replayed: Result<&2, &2, String, List<&2, Ops.Item>>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  do Result<&2, &2, String, List<&2, Ops.Item>>:
    Bool.pick(Result<&2, &2, String, Unit>, in_range, Done{Unit{}}, Fail{"an operation counts past the end of the parent"})
    items : List<&2, Ops.Item> <- replayed
    Ops.apply.checked(result, items)

def apply(+state: List<&2, Ops.Item>, doc: Ops.Doc) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match doc:
    case Ops.Doc{forgets, result, +ops}:
      checked(Ops.in_range(ops, List.length(&2, Ops.Item, state)), result, walk(ops, 0n, state))
