# Arithmetic and coordinate invariance for the independent replay model.
import Base
import ./ops.bend as Ops
import ./replay_spec.bend as Spec
import ./replay_lemmas.bend as L
import ./cursor_spec.bend as Cursor
import ./semantic_replay.bend as Block

def add_succ(n: Nat, -m: Nat) -> {Nat.add(n, 1n+m) == 1n+Nat.add(n, m) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, m) : {1n+Nat.add(p, 1n+m) == 1n+_ : Nat}
      {==}

def add_assoc(n: Nat, -m: Nat, -k: Nat) -> {Nat.add(Nat.add(n, m), k) == Nat.add(n, Nat.add(m, k)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, m, k) : {1n+Nat.add(Nat.add(p, m), k) == 1n+_ : Nat}
      {==}

def cmp_shift(n: Nat, -a: Nat, -b: Nat) -> {Nat.cmp(Nat.add(n, a), Nat.add(n, b)) == Nat.cmp(a, b) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      cmp_shift(p, a, b)

def deleted_shift(ops: List<&2, Ops.Op>, +n: Nat, +p: Nat) -> {Spec.deleted_at(Spec.shift(ops, n), Nat.add(n, p)) == Spec.deleted_at(ops, p) : Bool}:
  match ops:
    case Nil{}:
      {==}
    case Ops.Op{Ops.Insert{}, at, items} <> rest:
      deleted_shift(rest, n, p)
    case Ops.Op{Ops.Delete{}, at, items} <> rest:
      %deleted_shift(rest, n, p) : {Bool.or(Bool.and(Nat.is_le(Nat.add(n, at), Nat.add(n, p)), Nat.is_lt(Nat.add(n, p), Nat.add(Nat.add(n, at), List.length(&2, Ops.Item, items)))), Spec.deleted_at(Spec.shift(rest, n), Nat.add(n, p))) == Bool.or(Bool.and(Nat.is_le(at, p), Nat.is_lt(p, Nat.add(at, List.length(&2, Ops.Item, items)))), _) : Bool}
      %cmp_shift(n, at, p) : {Bool.or(Bool.and(Nat.is_le(Nat.add(n, at), Nat.add(n, p)), Nat.is_lt(Nat.add(n, p), Nat.add(Nat.add(n, at), List.length(&2, Ops.Item, items)))), Spec.deleted_at(Spec.shift(rest, n), Nat.add(n, p))) == Bool.or(Bool.and(Cmp.is_le(_), Nat.is_lt(p, Nat.add(at, List.length(&2, Ops.Item, items)))), Spec.deleted_at(Spec.shift(rest, n), Nat.add(n, p))) : Bool}
      %cmp_shift(n, p, Nat.add(at, List.length(&2, Ops.Item, items))) : {Bool.or(Bool.and(Nat.is_le(Nat.add(n, at), Nat.add(n, p)), Nat.is_lt(Nat.add(n, p), Nat.add(Nat.add(n, at), List.length(&2, Ops.Item, items)))), Spec.deleted_at(Spec.shift(rest, n), Nat.add(n, p))) == Bool.or(Bool.and(Nat.is_le(Nat.add(n, at), Nat.add(n, p)), Cmp.is_lt(_)), Spec.deleted_at(Spec.shift(rest, n), Nat.add(n, p))) : Bool}
      %add_assoc(n, at, List.length(&2, Ops.Item, items)) : {Bool.or(Bool.and(Nat.is_le(Nat.add(n, at), Nat.add(n, p)), Nat.is_lt(Nat.add(n, p), Nat.add(Nat.add(n, at), List.length(&2, Ops.Item, items)))), Spec.deleted_at(Spec.shift(rest, n), Nat.add(n, p))) == Bool.or(Bool.and(Nat.is_le(Nat.add(n, at), Nat.add(n, p)), Nat.is_lt(Nat.add(n, p), _)), Spec.deleted_at(Spec.shift(rest, n), Nat.add(n, p))) : Bool}
      {==}

def inserts_shift(ops: List<&2, Ops.Op>, +n: Nat, +p: Nat) -> {Spec.inserts_at(Spec.shift(ops, n), Nat.add(n, p)) == Spec.inserts_at(ops, p) : List<&2, Ops.Item>}:
  match ops:
    case Nil{}:
      {==}
    case Ops.Op{Ops.Delete{}, at, items} <> rest:
      inserts_shift(rest, n, p)
    case Ops.Op{Ops.Insert{}, at, items} <> rest:
      %inserts_shift(rest, n, p) : {List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Nat.is_eq(Nat.add(n, at), Nat.add(n, p)), items, Nil{}), Spec.inserts_at(Spec.shift(rest, n), Nat.add(n, p))) == List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Nat.is_eq(at, p), items, Nil{}), _) : List<&2, Ops.Item>}
      %cmp_shift(n, at, p) : {List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Nat.is_eq(Nat.add(n, at), Nat.add(n, p)), items, Nil{}), Spec.inserts_at(Spec.shift(rest, n), Nat.add(n, p))) == List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Cmp.is_eq(_), items, Nil{}), Spec.inserts_at(Spec.shift(rest, n), Nat.add(n, p))) : List<&2, Ops.Item>}
      {==}

def result_shift(parent: List<&2, Ops.Item>, +ops: List<&2, Ops.Op>, +n: Nat, +p: Nat) -> {Spec.result_from(parent, Spec.shift(ops, n), Nat.add(n, p)) == Spec.result_from(parent, ops, p) : List<&2, Ops.Item>}:
  match parent:
    case Nil{}:
      inserts_shift(ops, n, p)
    case it <> rest:
      %inserts_shift(ops, n, p) : {Spec.result_from(it <> rest, Spec.shift(ops, n), Nat.add(n, p)) == List.append(&2, Ops.Item, _, List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Spec.deleted_at(ops, p), Nil{}, [it]), Spec.result_from(rest, ops, 1n+p))) : List<&2, Ops.Item>}
      %deleted_shift(ops, n, p) : {Spec.result_from(it <> rest, Spec.shift(ops, n), Nat.add(n, p)) == List.append(&2, Ops.Item, Spec.inserts_at(Spec.shift(ops, n), Nat.add(n, p)), List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, _, Nil{}, [it]), Spec.result_from(rest, ops, 1n+p))) : List<&2, Ops.Item>}
      %result_shift(rest, ops, n, 1n+p) : {Spec.result_from(it <> rest, Spec.shift(ops, n), Nat.add(n, p)) == List.append(&2, Ops.Item, Spec.inserts_at(Spec.shift(ops, n), Nat.add(n, p)), List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Spec.deleted_at(Spec.shift(ops, n), Nat.add(n, p)), Nil{}, [it]), _)) : List<&2, Ops.Item>}
      %Equal.sym(Nat, Nat.add(n, 1n+p), 1n+Nat.add(n, p), add_succ(n, p)) : {Spec.result_from(it <> rest, Spec.shift(ops, n), Nat.add(n, p)) == List.append(&2, Ops.Item, Spec.inserts_at(Spec.shift(ops, n), Nat.add(n, p)), List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Spec.deleted_at(Spec.shift(ops, n), Nat.add(n, p)), Nil{}, [it]), Spec.result_from(rest, Spec.shift(ops, n), _))) : List<&2, Ops.Item>}
      {==}

# An insertion at zero has no effect on later parent positions.
def past_insert(parent: List<&2, Ops.Item>, +items: List<&2, Ops.Item>, p: Nat) -> {Spec.result_from(parent, [Ops.Op{Ops.Insert{}, 0n, items}], 1n+p) == parent : List<&2, Ops.Item>}:
  match parent:
    case Nil{}:
      {==}
    case it <> rest:
      %past_insert(rest, items, 1n+p) : {it <> Spec.result_from(rest, [Ops.Op{Ops.Insert{}, 0n, items}], 1n+1n+p) == it <> _ : List<&2, Ops.Item>}
      {==}

def insert_zero(parent: List<&2, Ops.Item>, +items: List<&2, Ops.Item>) -> {Spec.result(parent, [Ops.Op{Ops.Insert{}, 0n, items}]) == List.append(&2, Ops.Item, items, parent) : List<&2, Ops.Item>}:
  match parent:
    case Nil{}:
      {==}
    case it <> rest:
      %L.append_nil(items) : {Spec.result(it <> rest, [Ops.Op{Ops.Insert{}, 0n, items}]) == List.append(&2, Ops.Item, _, it <> rest) : List<&2, Ops.Item>}
      %past_insert(rest, items, 0n) : {Spec.result(it <> rest, [Ops.Op{Ops.Insert{}, 0n, items}]) == List.append(&2, Ops.Item, List.append(&2, Ops.Item, items, Nil{}), it <> _) : List<&2, Ops.Item>}
      {==}

# Every valid gap is represented by splitting the parent into before/after.
# This includes insertion into an empty parent and into the trailing gap.
def result_insert(+before: List<&2, Ops.Item>, +after: List<&2, Ops.Item>, +items: List<&2, Ops.Item>) -> {Spec.result(List.append(&2, Ops.Item, before, after), [Ops.Op{Ops.Insert{}, List.length(&2, Ops.Item, before), items}]) == List.append(&2, Ops.Item, before, List.append(&2, Ops.Item, items, after)) : List<&2, Ops.Item>}:
  match before:
    case Nil{}:
      insert_zero(after, items)
    case it <> rest:
      %result_insert(rest, after, items) : {Spec.result(it <> List.append(&2, Ops.Item, rest, after), [Ops.Op{Ops.Insert{}, 1n+List.length(&2, Ops.Item, rest), items}]) == it <> _ : List<&2, Ops.Item>}
      %result_shift(List.append(&2, Ops.Item, rest, after), [Ops.Op{Ops.Insert{}, List.length(&2, Ops.Item, rest), items}], 1n, 0n) : {Spec.result(it <> List.append(&2, Ops.Item, rest, after), [Ops.Op{Ops.Insert{}, 1n+List.length(&2, Ops.Item, rest), items}]) == it <> _ : List<&2, Ops.Item>}
      {==}

def sub_zero(n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def take_prefix(before: List<&2, Ops.Item>, after: List<&2, Ops.Item>) -> {List.take(&2, Ops.Item, List.append(&2, Ops.Item, before, after), List.length(&2, Ops.Item, before)) == before : List<&2, Ops.Item>}:
  match before after:
    case Nil{} Nil{}:
      {==}
    case Nil{} h <> t:
      {==}
    case h <> t _:
      %take_prefix(t, after) : {h <> List.take(&2, Ops.Item, List.append(&2, Ops.Item, t, after), List.length(&2, Ops.Item, t)) == h <> _ : List<&2, Ops.Item>}
      {==}

def drop_prefix(before: List<&2, Ops.Item>, after: List<&2, Ops.Item>) -> {List.drop(&2, Ops.Item, List.append(&2, Ops.Item, before, after), List.length(&2, Ops.Item, before)) == after : List<&2, Ops.Item>}:
  match before after:
    case Nil{} Nil{}:
      {==}
    case Nil{} h <> t:
      {==}
    case h <> t _:
      drop_prefix(t, after)

def zero_le(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def cursor_insert(+before: List<&2, Ops.Item>, +after: List<&2, Ops.Item>, +items: List<&2, Ops.Item>) -> {Cursor.walk([Ops.Op{Ops.Insert{}, List.length(&2, Ops.Item, before), items}], 0n, List.append(&2, Ops.Item, before, after)) == Done{List.append(&2, Ops.Item, before, List.append(&2, Ops.Item, items, after))} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  +parent = List.append(&2, Ops.Item, before, after)
  +at = List.length(&2, Ops.Item, before)
  %L.append_assoc(before, items, after) : {Cursor.walk([Ops.Op{Ops.Insert{}, at, items}], 0n, parent) == Done{_} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %take_prefix(before, after) : {Cursor.walk([Ops.Op{Ops.Insert{}, at, items}], 0n, parent) == Done{List.append(&2, Ops.Item, List.append(&2, Ops.Item, _, items), after)} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %drop_prefix(before, after) : {Cursor.walk([Ops.Op{Ops.Insert{}, at, items}], 0n, parent) == Done{List.append(&2, Ops.Item, List.append(&2, Ops.Item, List.take(&2, Ops.Item, parent, at), items), _)} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %sub_zero(at) : {Cursor.walk([Ops.Op{Ops.Insert{}, at, items}], 0n, parent) == Done{List.append(&2, Ops.Item, List.append(&2, Ops.Item, List.take(&2, Ops.Item, parent, _), items), List.drop(&2, Ops.Item, parent, _))} : Result<&2, &2, String, List<&2, Ops.Item>>}
  {==}

# Deleting no items contributes no deletion at any coordinate.
def empty_delete_at(p: Nat) -> {Spec.deleted_at([Ops.Op{Ops.Delete{}, 0n, Nil{}}], p) == False{} : Bool}:
  match p:
    case 0n:
      {==}
    case 1n+k:
      {==}

def empty_delete(parent: List<&2, Ops.Item>, +p: Nat) -> {Spec.result_from(parent, [Ops.Op{Ops.Delete{}, 0n, Nil{}}], p) == parent : List<&2, Ops.Item>}:
  match parent:
    case Nil{}:
      {==}
    case it <> rest:
      %empty_delete(rest, 1n+p) : {Spec.result_from(it <> rest, [Ops.Op{Ops.Delete{}, 0n, Nil{}}], p) == it <> _ : List<&2, Ops.Item>}
      %empty_delete_at(p) : {Spec.result_from(it <> rest, [Ops.Op{Ops.Delete{}, 0n, Nil{}}], p) == List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, _, Nil{}, [it]), Spec.result_from(rest, [Ops.Op{Ops.Delete{}, 0n, Nil{}}], 1n+p)) : List<&2, Ops.Item>}
      {==}

def delete_at_step(-head: Ops.Item, -tail: List<&2, Ops.Item>, p: Nat) -> {Spec.deleted_at([Ops.Op{Ops.Delete{}, 0n, head <> tail}], 1n+p) == Spec.deleted_at([Ops.Op{Ops.Delete{}, 0n, tail}], p) : Bool}:
  %Equal.sym(Bool, Nat.is_le(0n, p), True{}, zero_le(p)) : {Spec.deleted_at([Ops.Op{Ops.Delete{}, 0n, head <> tail}], 1n+p) == Bool.or(Bool.and(_, Nat.is_lt(p, List.length(&2, Ops.Item, tail))), False{}) : Bool}
  {==}

def delete_step(parent: List<&2, Ops.Item>, +head: Ops.Item, +tail: List<&2, Ops.Item>, +p: Nat) -> {Spec.result_from(parent, [Ops.Op{Ops.Delete{}, 0n, head <> tail}], 1n+p) == Spec.result_from(parent, [Ops.Op{Ops.Delete{}, 0n, tail}], p) : List<&2, Ops.Item>}:
  match parent:
    case Nil{}:
      {==}
    case it <> rest:
      %delete_at_step(head, tail, p) : {Spec.result_from(it <> rest, [Ops.Op{Ops.Delete{}, 0n, head <> tail}], 1n+p) == List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, _, Nil{}, [it]), Spec.result_from(rest, [Ops.Op{Ops.Delete{}, 0n, tail}], 1n+p)) : List<&2, Ops.Item>}
      %delete_step(rest, head, tail, 1n+p) : {Spec.result_from(it <> rest, [Ops.Op{Ops.Delete{}, 0n, head <> tail}], 1n+p) == List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Spec.deleted_at([Ops.Op{Ops.Delete{}, 0n, head <> tail}], 1n+p), Nil{}, [it]), _) : List<&2, Ops.Item>}
      {==}

def delete_zero(recorded: List<&2, Ops.Item>, parent: List<&2, Ops.Item>) -> {Spec.result(parent, [Ops.Op{Ops.Delete{}, 0n, recorded}]) == List.drop(&2, Ops.Item, parent, List.length(&2, Ops.Item, recorded)) : List<&2, Ops.Item>}:
  match recorded parent:
    case Nil{} Nil{}:
      {==}
    case Nil{} it <> rest:
      empty_delete(it <> rest, 0n)
    case h <> t Nil{}:
      {==}
    case +h <> +t it <> +rest:
      %delete_zero(t, rest) : {Spec.result(it <> rest, [Ops.Op{Ops.Delete{}, 0n, h <> t}]) == _ : List<&2, Ops.Item>}
      delete_step(rest, h, t, 0n)

def result_delete(+before: List<&2, Ops.Item>, +after: List<&2, Ops.Item>, +recorded: List<&2, Ops.Item>) -> {Spec.result(List.append(&2, Ops.Item, before, after), [Ops.Op{Ops.Delete{}, List.length(&2, Ops.Item, before), recorded}]) == List.append(&2, Ops.Item, before, List.drop(&2, Ops.Item, after, List.length(&2, Ops.Item, recorded))) : List<&2, Ops.Item>}:
  match before:
    case Nil{}:
      delete_zero(recorded, after)
    case it <> rest:
      %result_delete(rest, after, recorded) : {Spec.result(it <> List.append(&2, Ops.Item, rest, after), [Ops.Op{Ops.Delete{}, 1n+List.length(&2, Ops.Item, rest), recorded}]) == it <> _ : List<&2, Ops.Item>}
      %result_shift(List.append(&2, Ops.Item, rest, after), [Ops.Op{Ops.Delete{}, List.length(&2, Ops.Item, rest), recorded}], 1n, 0n) : {Spec.result(it <> List.append(&2, Ops.Item, rest, after), [Ops.Op{Ops.Delete{}, 1n+List.length(&2, Ops.Item, rest), recorded}]) == it <> _ : List<&2, Ops.Item>}
      {==}

def cursor_delete(+before: List<&2, Ops.Item>, +after: List<&2, Ops.Item>, +recorded: List<&2, Ops.Item>) -> {Cursor.walk([Ops.Op{Ops.Delete{}, List.length(&2, Ops.Item, before), recorded}], 0n, List.append(&2, Ops.Item, before, after)) == Cursor.combine(Cursor.disagreement(List.length(&2, Ops.Item, before), Spec.prefix_matches(recorded, after)), before, Done{List.drop(&2, Ops.Item, after, List.length(&2, Ops.Item, recorded))}) : Result<&2, &2, String, List<&2, Ops.Item>>}:
  +parent = List.append(&2, Ops.Item, before, after)
  +at = List.length(&2, Ops.Item, before)
  %take_prefix(before, after) : {Cursor.walk([Ops.Op{Ops.Delete{}, at, recorded}], 0n, parent) == Cursor.combine(Cursor.disagreement(at, Spec.prefix_matches(recorded, after)), _, Done{List.drop(&2, Ops.Item, after, List.length(&2, Ops.Item, recorded))}) : Result<&2, &2, String, List<&2, Ops.Item>>}
  %drop_prefix(before, after) : {Cursor.walk([Ops.Op{Ops.Delete{}, at, recorded}], 0n, parent) == Cursor.combine(Cursor.disagreement(at, Spec.prefix_matches(recorded, _)), List.take(&2, Ops.Item, parent, at), Done{List.drop(&2, Ops.Item, _, List.length(&2, Ops.Item, recorded))}) : Result<&2, &2, String, List<&2, Ops.Item>>}
  %sub_zero(at) : {Cursor.walk([Ops.Op{Ops.Delete{}, at, recorded}], 0n, parent) == Cursor.combine(Cursor.disagreement(at, Spec.prefix_matches(recorded, List.drop(&2, Ops.Item, parent, _))), List.take(&2, Ops.Item, parent, _), Done{List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, parent, _), List.length(&2, Ops.Item, recorded))}) : Result<&2, &2, String, List<&2, Ops.Item>>}
  {==}

# Past position zero, a replacement's insertion contributes nothing further.
def past_replacement(parent: List<&2, Ops.Item>, +old: List<&2, Ops.Item>, +new: List<&2, Ops.Item>, p: Nat) -> {Spec.result_from(parent, [Ops.Op{Ops.Delete{}, 0n, old}, Ops.Op{Ops.Insert{}, 0n, new}], 1n+p) == Spec.result_from(parent, [Ops.Op{Ops.Delete{}, 0n, old}], 1n+p) : List<&2, Ops.Item>}:
  match parent:
    case Nil{}:
      {==}
    case it <> rest:
      %past_replacement(rest, old, new, 1n+p) : {Spec.result_from(it <> rest, [Ops.Op{Ops.Delete{}, 0n, old}, Ops.Op{Ops.Insert{}, 0n, new}], 1n+p) == List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Spec.deleted_at([Ops.Op{Ops.Delete{}, 0n, old}], 1n+p), Nil{}, [it]), _) : List<&2, Ops.Item>}
      {==}

def replace_zero(parent: List<&2, Ops.Item>, +old: List<&2, Ops.Item>, +new: List<&2, Ops.Item>) -> {Spec.result(parent, [Ops.Op{Ops.Delete{}, 0n, old}, Ops.Op{Ops.Insert{}, 0n, new}]) == List.append(&2, Ops.Item, new, Spec.result(parent, [Ops.Op{Ops.Delete{}, 0n, old}])) : List<&2, Ops.Item>}:
  match parent:
    case Nil{}:
      {==}
    case it <> rest:
      %L.append_nil(new) : {Spec.result(it <> rest, [Ops.Op{Ops.Delete{}, 0n, old}, Ops.Op{Ops.Insert{}, 0n, new}]) == List.append(&2, Ops.Item, _, Spec.result(it <> rest, [Ops.Op{Ops.Delete{}, 0n, old}])) : List<&2, Ops.Item>}
      %past_replacement(rest, old, new, 0n) : {Spec.result(it <> rest, [Ops.Op{Ops.Delete{}, 0n, old}, Ops.Op{Ops.Insert{}, 0n, new}]) == List.append(&2, Ops.Item, List.append(&2, Ops.Item, new, Nil{}), List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Spec.deleted_at([Ops.Op{Ops.Delete{}, 0n, old}], 0n), Nil{}, [it]), _)) : List<&2, Ops.Item>}
      {==}

def result_replace(+before: List<&2, Ops.Item>, +after: List<&2, Ops.Item>, +old: List<&2, Ops.Item>, +new: List<&2, Ops.Item>) -> {Spec.result(List.append(&2, Ops.Item, before, after), [Ops.Op{Ops.Delete{}, List.length(&2, Ops.Item, before), old}, Ops.Op{Ops.Insert{}, List.length(&2, Ops.Item, before), new}]) == List.append(&2, Ops.Item, before, List.append(&2, Ops.Item, new, List.drop(&2, Ops.Item, after, List.length(&2, Ops.Item, old)))) : List<&2, Ops.Item>}:
  match before:
    case Nil{}:
      %delete_zero(old, after) : {Spec.result(after, [Ops.Op{Ops.Delete{}, 0n, old}, Ops.Op{Ops.Insert{}, 0n, new}]) == List.append(&2, Ops.Item, new, _) : List<&2, Ops.Item>}
      replace_zero(after, old, new)
    case it <> rest:
      %result_replace(rest, after, old, new) : {Spec.result(it <> List.append(&2, Ops.Item, rest, after), [Ops.Op{Ops.Delete{}, 1n+List.length(&2, Ops.Item, rest), old}, Ops.Op{Ops.Insert{}, 1n+List.length(&2, Ops.Item, rest), new}]) == it <> _ : List<&2, Ops.Item>}
      %result_shift(List.append(&2, Ops.Item, rest, after), [Ops.Op{Ops.Delete{}, List.length(&2, Ops.Item, rest), old}, Ops.Op{Ops.Insert{}, List.length(&2, Ops.Item, rest), new}], 1n, 0n) : {Spec.result(it <> List.append(&2, Ops.Item, rest, after), [Ops.Op{Ops.Delete{}, 1n+List.length(&2, Ops.Item, rest), old}, Ops.Op{Ops.Insert{}, 1n+List.length(&2, Ops.Item, rest), new}]) == it <> _ : List<&2, Ops.Item>}
      {==}

def zero_sub(n: Nat) -> {Nat.sub(0n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def sub_past(n: Nat, k: Nat) -> {Nat.sub(n, Nat.add(n, k)) == 0n : Nat}:
  match n:
    case 0n:
      zero_sub(k)
    case 1n+p:
      sub_past(p, k)

def take_zero(xs: List<&2, Ops.Item>) -> {List.take(&2, Ops.Item, xs, 0n) == Nil{} : List<&2, Ops.Item>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

def drop_zero(xs: List<&2, Ops.Item>) -> {List.drop(&2, Ops.Item, xs, 0n) == xs : List<&2, Ops.Item>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

def insert_behind(+state: List<&2, Ops.Item>, +at: Nat, +count: Nat, +items: List<&2, Ops.Item>) -> {Cursor.walk([Ops.Op{Ops.Insert{}, at, items}], Nat.add(at, count), state) == Done{List.append(&2, Ops.Item, items, state)} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  %take_zero(state) : {Cursor.walk([Ops.Op{Ops.Insert{}, at, items}], Nat.add(at, count), state) == Done{List.append(&2, Ops.Item, List.append(&2, Ops.Item, _, items), state)} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %drop_zero(state) : {Cursor.walk([Ops.Op{Ops.Insert{}, at, items}], Nat.add(at, count), state) == Done{List.append(&2, Ops.Item, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, 0n), items), _)} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %sub_past(at, count) : {Cursor.walk([Ops.Op{Ops.Insert{}, at, items}], Nat.add(at, count), state) == Done{List.append(&2, Ops.Item, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, _), items), List.drop(&2, Ops.Item, state, _))} : Result<&2, &2, String, List<&2, Ops.Item>>}
  {==}

def cursor_replace(+before: List<&2, Ops.Item>, +after: List<&2, Ops.Item>, +old: List<&2, Ops.Item>, +new: List<&2, Ops.Item>) -> {Cursor.walk([Ops.Op{Ops.Delete{}, List.length(&2, Ops.Item, before), old}, Ops.Op{Ops.Insert{}, List.length(&2, Ops.Item, before), new}], 0n, List.append(&2, Ops.Item, before, after)) == Cursor.combine(Cursor.disagreement(List.length(&2, Ops.Item, before), Spec.prefix_matches(old, after)), before, Done{List.append(&2, Ops.Item, new, List.drop(&2, Ops.Item, after, List.length(&2, Ops.Item, old)))}) : Result<&2, &2, String, List<&2, Ops.Item>>}:
  +parent = List.append(&2, Ops.Item, before, after)
  +at = List.length(&2, Ops.Item, before)
  +ops = {[Ops.Op{Ops.Delete{}, at, old}, Ops.Op{Ops.Insert{}, at, new}] : List<&2, Ops.Op>}
  +remaining = List.drop(&2, Ops.Item, after, List.length(&2, Ops.Item, old))
  %insert_behind(remaining, at, List.length(&2, Ops.Item, old), new) : {Cursor.walk(ops, 0n, parent) == Cursor.combine(Cursor.disagreement(at, Spec.prefix_matches(old, after)), before, _) : Result<&2, &2, String, List<&2, Ops.Item>>}
  %take_prefix(before, after) : {Cursor.walk(ops, 0n, parent) == Cursor.combine(Cursor.disagreement(at, Spec.prefix_matches(old, after)), _, Cursor.walk([Ops.Op{Ops.Insert{}, at, new}], Nat.add(at, List.length(&2, Ops.Item, old)), remaining)) : Result<&2, &2, String, List<&2, Ops.Item>>}
  %drop_prefix(before, after) : {Cursor.walk(ops, 0n, parent) == Cursor.combine(Cursor.disagreement(at, Spec.prefix_matches(old, _)), List.take(&2, Ops.Item, parent, at), Cursor.walk([Ops.Op{Ops.Insert{}, at, new}], Nat.add(at, List.length(&2, Ops.Item, old)), List.drop(&2, Ops.Item, _, List.length(&2, Ops.Item, old)))) : Result<&2, &2, String, List<&2, Ops.Item>>}
  %sub_zero(at) : {Cursor.walk(ops, 0n, parent) == Cursor.combine(Cursor.disagreement(at, Spec.prefix_matches(old, List.drop(&2, Ops.Item, parent, _))), List.take(&2, Ops.Item, parent, _), Cursor.walk([Ops.Op{Ops.Insert{}, at, new}], Nat.add(at, List.length(&2, Ops.Item, old)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, parent, _), List.length(&2, Ops.Item, old)))) : Result<&2, &2, String, List<&2, Ops.Item>>}
  {==}

# Replace the constructed success payload by an equal positional result;
# disagreement remains the same error, including its absolute position.
def project_block(error: Maybe<&2, String>, -before: List<&2, Ops.Item>, -body: List<&2, Ops.Item>, -expected: List<&2, Ops.Item>, e: {expected == List.append(&2, Ops.Item, before, body) : List<&2, Ops.Item>}) -> {Cursor.combine(error, before, Done{body}) == Cursor.combine(error, Nil{}, Done{expected}) : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match error:
    case None{}:
      Equal.cong(List<&2, Ops.Item>, Result<&2, &2, String, List<&2, Ops.Item>>, xs => Done{xs}, List.append(&2, Ops.Item, before, body), expected, Equal.sym(List<&2, Ops.Item>, expected, List.append(&2, Ops.Item, before, body), e))
    case Some{msg}:
      {==}

def cursor_block(+before: List<&2, Ops.Item>, +after: List<&2, Ops.Item>, +edit: Ops.Edit) -> {Cursor.walk(Ops.operations(List.length(&2, Ops.Item, before), edit), 0n, List.append(&2, Ops.Item, before, after)) == Block.raw(before, after, edit) : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match edit:
    case Ops.Insertion{items}:
      +parent = List.append(&2, Ops.Item, before, after)
      +at = List.length(&2, Ops.Item, before)
      +ops = Ops.operations(at, Ops.Insertion{items})
      +body = List.append(&2, Ops.Item, items, after)
      Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.walk(ops, 0n, parent), Cursor.combine(None{}, before, Done{body}), Block.raw(before, after, Ops.Insertion{items}),
        cursor_insert(before, after, items), project_block(None{}, before, body, Spec.result(parent, ops), result_insert(before, after, items)))
    case Ops.Deletion{recorded}:
      +parent = List.append(&2, Ops.Item, before, after)
      +at = List.length(&2, Ops.Item, before)
      +ops = Ops.operations(at, Ops.Deletion{recorded})
      +body = List.drop(&2, Ops.Item, after, List.length(&2, Ops.Item, recorded))
      +error = Cursor.disagreement(at, Spec.prefix_matches(recorded, after))
      Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.walk(ops, 0n, parent), Cursor.combine(error, before, Done{body}), Block.raw(before, after, Ops.Deletion{recorded}),
        cursor_delete(before, after, recorded), project_block(error, before, body, Spec.result(parent, ops), result_delete(before, after, recorded)))
    case Ops.Replacement{recorded, inserted}:
      +parent = List.append(&2, Ops.Item, before, after)
      +at = List.length(&2, Ops.Item, before)
      +ops = Ops.operations(at, Ops.Replacement{recorded, inserted})
      +body = List.append(&2, Ops.Item, inserted, List.drop(&2, Ops.Item, after, List.length(&2, Ops.Item, recorded)))
      +error = Cursor.disagreement(at, Spec.prefix_matches(recorded, after))
      Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.walk(ops, 0n, parent), Cursor.combine(error, before, Done{body}), Block.raw(before, after, Ops.Replacement{recorded, inserted}),
        cursor_replace(before, after, recorded, inserted), project_block(error, before, body, Spec.result(parent, ops), result_replace(before, after, recorded, inserted)))
