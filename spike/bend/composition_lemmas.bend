# Composing edit blocks: a script of blocks replays, block by block, to the
# positional result. The arithmetic here is about where a block starts and
# where it leaves the cursor; nothing in it inspects an item.
import Base
import ./ops.bend as Ops
import ./replay_spec.bend as Spec
import ./replay_lemmas.bend as L
import ./position_lemmas.bend as Pos
import ./cursor_spec.bend as Cursor
import ./semantic_replay.bend as Block

# Refuting a boolean hypothesis that computed to the wrong constructor.
def disc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def false_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : {disc(_) : Type}
  Unit{}

def and_left(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_true(e))

def and_right(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, false_true(e))

def and_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def or_assoc(e: Maybe<&2, String>, -f: Maybe<&2, String>, -g: Maybe<&2, String>) -> {Maybe.or(&2, String, Maybe.or(&2, String, e, f), g) == Maybe.or(&2, String, e, Maybe.or(&2, String, f, g)) : Maybe<&2, String>}:
  match e:
    case None{}:
      {==}
    case Some{x}:
      {==}

# Nat
# ---

def add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

def eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      eq_refl(p)

# is_le(a, b) implies is_le(a, 1n+b)
def le_succ(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+ap, 1n+0n) == True{} : Bool}, false_true(e))
    case 1n+ap 1n+bp:
      le_succ(ap, bp, e)

# is_le(1n+a, b) implies is_le(a, b)
def le_pred(a: Nat, b: Nat, e: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_le(0n, 0n) == True{} : Bool}, false_true(e))
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, false_true(e))
    case 0n 1n+bp:
      {==}
    case 1n+ap 1n+bp:
      le_pred(ap, bp, e)

# is_le(q, a) implies is_le(q, a + k)
def le_add(q: Nat, a: Nat, k: Nat, e: {Nat.is_le(q, a) == True{} : Bool}) -> {Nat.is_le(q, Nat.add(a, k)) == True{} : Bool}:
  match q a:
    case 0n _:
      Pos.zero_le(Nat.add(a, k))
    case 1n+qp 0n:
      Empty.absurd({Nat.is_le(1n+qp, Nat.add(0n, k)) == True{} : Bool}, false_true(e))
    case 1n+qp 1n+ap:
      le_add(qp, ap, k, e)

# is_le(a + k, b) implies is_le(a, b)
def le_add_left(a: Nat, -k: Nat, b: Nat, e: {Nat.is_le(Nat.add(a, k), b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n _:
      Pos.zero_le(b)
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, false_true(e))
    case 1n+ap 1n+bp:
      le_add_left(ap, k, bp, e)

def lt_add_succ(a: Nat, -k: Nat) -> {Nat.is_lt(a, Nat.add(a, 1n+k)) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      lt_add_succ(ap, k)

# is_lt(a, b) implies is_lt(a, 1n+b)
def lt_succ(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 1n+0n) == True{} : Bool}, false_true(e))
    case 1n+ap 1n+bp:
      lt_succ(ap, bp, e)

# is_lt(p, q) and is_le(q, at) place at strictly past p.
def gt_of_lt_le(p: Nat, q: Nat, at: Nat, lt: {Nat.is_lt(p, q) == True{} : Bool}, le: {Nat.is_le(q, at) == True{} : Bool}) -> {Nat.cmp(at, p) == GT{} : Cmp}:
  match p q at:
    case 0n 0n _:
      Empty.absurd({Nat.cmp(at, 0n) == GT{} : Cmp}, false_true(lt))
    case 1n+pp 0n _:
      Empty.absurd({Nat.cmp(at, 1n+pp) == GT{} : Cmp}, false_true(lt))
    case _ 1n+qp 0n:
      Empty.absurd({Nat.cmp(0n, p) == GT{} : Cmp}, false_true(le))
    case 0n 1n+qp 1n+ap:
      {==}
    case 1n+pp 1n+qp 1n+ap:
      gt_of_lt_le(pp, qp, ap, lt, le)

def lt_not_eq(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, false_true(e))
    case 1n+ap 0n:
      Empty.absurd({Nat.is_eq(1n+ap, 0n) == False{} : Bool}, false_true(e))
    case 0n 1n+bp:
      {==}
    case 1n+ap 1n+bp:
      lt_not_eq(ap, bp, e)

def le_lt_contra(a: Nat, b: Nat) -> {Bool.and(Nat.is_le(a, b), Nat.is_lt(b, a)) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      le_lt_contra(ap, bp)

def sub_add(pos: Nat, gap: Nat) -> {Nat.sub(Nat.add(pos, gap), pos) == gap : Nat}:
  match pos:
    case 0n:
      Pos.sub_zero(gap)
    case 1n+p:
      sub_add(p, gap)

def max_add(pos: Nat, gap: Nat) -> {Nat.max(pos, Nat.add(pos, gap)) == Nat.add(pos, gap) : Nat}:
  match pos:
    case 0n:
      {==}
    case 1n+p:
      %max_add(p, gap) : {1n+Nat.max(p, Nat.add(p, gap)) == 1n+_ : Nat}
      {==}

def max_add_left(at: Nat, n: Nat) -> {Nat.max(Nat.add(at, n), at) == Nat.add(at, n) : Nat}:
  match at:
    case 0n:
      match n:
        case 0n:
          {==}
        case 1n+np:
          {==}
    case 1n+p:
      %max_add_left(p, n) : {1n+Nat.max(Nat.add(p, n), p) == 1n+_ : Nat}
      {==}

# Lists
# -----

def drop_drop(n: Nat, xs: List<&2, Ops.Item>, m: Nat) -> {List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, xs, n), m) == List.drop(&2, Ops.Item, xs, Nat.add(n, m)) : List<&2, Ops.Item>}:
  match n xs:
    case 0n Nil{}:
      {==}
    case 0n h <> t:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p h <> t:
      drop_drop(p, t, m)

# A gap that fits the parent past `pos` fits what is left of it.
def gap_fits(gap: Nat, pos: Nat, parent: List<&2, Ops.Item>, e: {Nat.is_le(Nat.add(pos, gap), List.length(&2, Ops.Item, parent)) == True{} : Bool}) -> {Nat.is_le(gap, List.length(&2, Ops.Item, List.drop(&2, Ops.Item, parent, pos))) == True{} : Bool}:
  match pos parent:
    case 0n Nil{}:
      e
    case 0n h <> t:
      e
    case 1n+p Nil{}:
      Empty.absurd({Nat.is_le(gap, 0n) == True{} : Bool}, false_true(e))
    case 1n+p h <> t:
      gap_fits(gap, p, t, e)

# Operations that all sit at or past `q`
# ------------------------------------

def below(ops: List<&2, Ops.Op>, +q: Nat) -> Bool:
  match ops:
    case Nil{}:
      True{}
    case Ops.Op{verb, at, items} <> rest:
      Bool.and(Nat.is_le(q, at), below(rest, q))

def below_at(ops: List<&2, Ops.Op>, -q: Nat, -r: Nat, e: {q == r : Nat}, lb: {below(ops, q) == True{} : Bool}) -> {below(ops, r) == True{} : Bool}:
  %e : {below(ops, _) == True{} : Bool}
  lb

def below_join(+a: List<&2, Ops.Op>, +b: List<&2, Ops.Op>, +q: Nat, +ea: {below(a, q) == True{} : Bool}, eb: {below(b, q) == True{} : Bool}) -> {below(List.append(&2, Ops.Op, a, b), q) == True{} : Bool}:
  match a:
    case Nil{}:
      eb
    case Ops.Op{verb, +at, items} <> +rest:
      %Equal.sym(Bool, Nat.is_le(q, at), True{}, and_left(Nat.is_le(q, at), below(rest, q), ea)) : {Bool.and(_, below(List.append(&2, Ops.Op, rest, b), q)) == True{} : Bool}
      %Equal.sym(Bool, below(List.append(&2, Ops.Op, rest, b), q), True{}, below_join(rest, b, q, and_right(Nat.is_le(q, at), below(rest, q), ea), eb)) : {Bool.and(True{}, _) == True{} : Bool}
      {==}

# Nothing sitting at or past q inserts at, or deletes, a position before q.
def no_insert_below(ops: List<&2, Ops.Op>, +q: Nat, +p: Nat, +lb: {below(ops, q) == True{} : Bool}, +lt: {Nat.is_lt(p, q) == True{} : Bool}) -> {Spec.inserts_at(ops, p) == Nil{} : List<&2, Ops.Item>}:
  match ops:
    case Nil{}:
      {==}
    case Ops.Op{Ops.Delete{}, +at, items} <> +rest:
      no_insert_below(rest, q, p, and_right(Nat.is_le(q, at), below(rest, q), lb), lt)
    case Ops.Op{Ops.Insert{}, +at, items} <> +rest:
      %Equal.sym(Cmp, Nat.cmp(at, p), GT{}, gt_of_lt_le(p, q, at, lt, and_left(Nat.is_le(q, at), below(rest, q), lb))) : {List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Cmp.is_eq(_), items, Nil{}), Spec.inserts_at(rest, p)) == Nil{} : List<&2, Ops.Item>}
      no_insert_below(rest, q, p, and_right(Nat.is_le(q, at), below(rest, q), lb), lt)

def no_delete_below(ops: List<&2, Ops.Op>, +q: Nat, +p: Nat, +lb: {below(ops, q) == True{} : Bool}, +lt: {Nat.is_lt(p, q) == True{} : Bool}) -> {Spec.deleted_at(ops, p) == False{} : Bool}:
  match ops:
    case Nil{}:
      {==}
    case Ops.Op{Ops.Insert{}, +at, items} <> +rest:
      no_delete_below(rest, q, p, and_right(Nat.is_le(q, at), below(rest, q), lb), lt)
    case Ops.Op{Ops.Delete{}, +at, items} <> +rest:
      %Equal.sym(Cmp, Nat.cmp(at, p), GT{}, gt_of_lt_le(p, q, at, lt, and_left(Nat.is_le(q, at), below(rest, q), lb))) : {Bool.or(Bool.and(Cmp.is_le(_), Nat.is_lt(p, Nat.add(at, List.length(&2, Ops.Item, items)))), Spec.deleted_at(rest, p)) == False{} : Bool}
      no_delete_below(rest, q, p, and_right(Nat.is_le(q, at), below(rest, q), lb), lt)

def result_nil(state: List<&2, Ops.Item>, +p: Nat) -> {Spec.result_from(state, Nil{}, p) == state : List<&2, Ops.Item>}:
  match state:
    case Nil{}:
      {==}
    case it <> rest:
      %result_nil(rest, 1n+p) : {it <> Spec.result_from(rest, Nil{}, 1n+p) == it <> _ : List<&2, Ops.Item>}
      {==}

# The parent items before the first operation pass through untouched.
def skip(+gap: Nat, +state: List<&2, Ops.Item>, +ops: List<&2, Ops.Op>, +pos: Nat, +lb: {below(ops, Nat.add(pos, gap)) == True{} : Bool}, fits: {Nat.is_le(gap, List.length(&2, Ops.Item, state)) == True{} : Bool}) -> {Spec.result_from(state, ops, pos) == List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, gap), Spec.result_from(List.drop(&2, Ops.Item, state, gap), ops, Nat.add(pos, gap))) : List<&2, Ops.Item>}:
  match gap state:
    case 0n Nil{}:
      %Equal.sym(Nat, Nat.add(pos, 0n), pos, add_zero(pos)) : {Spec.result_from(Nil{}, ops, pos) == Spec.result_from(Nil{}, ops, _) : List<&2, Ops.Item>}
      {==}
    case 0n it <> rest:
      %Equal.sym(Nat, Nat.add(pos, 0n), pos, add_zero(pos)) : {Spec.result_from(it <> rest, ops, pos) == Spec.result_from(it <> rest, ops, _) : List<&2, Ops.Item>}
      {==}
    case 1n+g Nil{}:
      Empty.absurd({Spec.result_from(Nil{}, ops, pos) == List.append(&2, Ops.Item, List.take(&2, Ops.Item, Nil{}, 1n+g), Spec.result_from(List.drop(&2, Ops.Item, Nil{}, 1n+g), ops, Nat.add(pos, 1n+g))) : List<&2, Ops.Item>}, false_true(fits))
    case 1n+g it <> +rest:
      +here = Nat.add(pos, 1n+g)
      +tail = List.append(&2, Ops.Item, List.take(&2, Ops.Item, rest, g), Spec.result_from(List.drop(&2, Ops.Item, rest, g), ops, here))
      %Equal.sym(List<&2, Ops.Item>, Spec.inserts_at(ops, pos), Nil{}, no_insert_below(ops, here, pos, lb, lt_add_succ(pos, g))) : {List.append(&2, Ops.Item, _, List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Spec.deleted_at(ops, pos), Nil{}, [it]), Spec.result_from(rest, ops, 1n+pos))) == it <> tail : List<&2, Ops.Item>}
      %Equal.sym(Bool, Spec.deleted_at(ops, pos), False{}, no_delete_below(ops, here, pos, lb, lt_add_succ(pos, g))) : {List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, _, Nil{}, [it]), Spec.result_from(rest, ops, 1n+pos)) == it <> tail : List<&2, Ops.Item>}
      %Equal.sym(List<&2, Ops.Item>, Spec.result_from(rest, ops, 1n+pos), List.append(&2, Ops.Item, List.take(&2, Ops.Item, rest, g), Spec.result_from(List.drop(&2, Ops.Item, rest, g), ops, Nat.add(1n+pos, g))), skip(g, rest, ops, 1n+pos, below_at(ops, here, Nat.add(1n+pos, g), Pos.add_succ(pos, g), lb), fits)) : {it <> _ == it <> tail : List<&2, Ops.Item>}
      %Equal.sym(Nat, here, 1n+Nat.add(pos, g), Pos.add_succ(pos, g)) : {it <> List.append(&2, Ops.Item, List.take(&2, Ops.Item, rest, g), Spec.result_from(List.drop(&2, Ops.Item, rest, g), ops, Nat.add(1n+pos, g))) == it <> List.append(&2, Ops.Item, List.take(&2, Ops.Item, rest, g), Spec.result_from(List.drop(&2, Ops.Item, rest, g), ops, _)) : List<&2, Ops.Item>}
      {==}

# One block at the head of the operations, read at its own position
# ------------------------------------------------------------------

def lt_succ_self(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      lt_succ_self(p)

# An insert is invisible past its position.
def insert_invisible(state: List<&2, Ops.Item>, +at: Nat, +items: List<&2, Ops.Item>, +more: List<&2, Ops.Op>, +q: Nat, +lt: {Nat.is_lt(at, q) == True{} : Bool}) -> {Spec.result_from(state, Ops.Op{Ops.Insert{}, at, items} <> more, q) == Spec.result_from(state, more, q) : List<&2, Ops.Item>}:
  match state:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(at, q), False{}, lt_not_eq(at, q, lt)) : {List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, _, items, Nil{}), Spec.inserts_at(more, q)) == Spec.inserts_at(more, q) : List<&2, Ops.Item>}
      {==}
    case it <> rest:
      %Equal.sym(Bool, Nat.is_eq(at, q), False{}, lt_not_eq(at, q, lt)) : {List.append(&2, Ops.Item, List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, _, items, Nil{}), Spec.inserts_at(more, q)), List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Spec.deleted_at(more, q), Nil{}, [it]), Spec.result_from(rest, Ops.Op{Ops.Insert{}, at, items} <> more, 1n+q))) == Spec.result_from(it <> rest, more, q) : List<&2, Ops.Item>}
      %Equal.sym(List<&2, Ops.Item>, Spec.result_from(rest, Ops.Op{Ops.Insert{}, at, items} <> more, 1n+q), Spec.result_from(rest, more, 1n+q), insert_invisible(rest, at, items, more, 1n+q, lt_succ(at, q, lt))) : {List.append(&2, Ops.Item, Spec.inserts_at(more, q), List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Spec.deleted_at(more, q), Nil{}, [it]), _)) == Spec.result_from(it <> rest, more, q) : List<&2, Ops.Item>}
      {==}

# An insert at the position being read contributes its items first.
def insert_head(state: List<&2, Ops.Item>, +at: Nat, +items: List<&2, Ops.Item>, +more: List<&2, Ops.Op>) -> {Spec.result_from(state, Ops.Op{Ops.Insert{}, at, items} <> more, at) == List.append(&2, Ops.Item, items, Spec.result_from(state, more, at)) : List<&2, Ops.Item>}:
  match state:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(at, at), True{}, eq_refl(at)) : {List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, _, items, Nil{}), Spec.inserts_at(more, at)) == List.append(&2, Ops.Item, items, Spec.inserts_at(more, at)) : List<&2, Ops.Item>}
      {==}
    case +it <> +rest:
      +later = List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Spec.deleted_at(more, at), Nil{}, [it]), Spec.result_from(rest, more, 1n+at))
      %Equal.sym(Bool, Nat.is_eq(at, at), True{}, eq_refl(at)) : {List.append(&2, Ops.Item, List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, _, items, Nil{}), Spec.inserts_at(more, at)), List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Spec.deleted_at(more, at), Nil{}, [it]), Spec.result_from(rest, Ops.Op{Ops.Insert{}, at, items} <> more, 1n+at))) == List.append(&2, Ops.Item, items, Spec.result_from(it <> rest, more, at)) : List<&2, Ops.Item>}
      %Equal.sym(List<&2, Ops.Item>, Spec.result_from(rest, Ops.Op{Ops.Insert{}, at, items} <> more, 1n+at), Spec.result_from(rest, more, 1n+at), insert_invisible(rest, at, items, more, 1n+at, lt_succ_self(at))) : {List.append(&2, Ops.Item, List.append(&2, Ops.Item, items, Spec.inserts_at(more, at)), List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Spec.deleted_at(more, at), Nil{}, [it]), _)) == List.append(&2, Ops.Item, items, Spec.result_from(it <> rest, more, at)) : List<&2, Ops.Item>}
      L.append_assoc(items, Spec.inserts_at(more, at), later)

# A delete quoting nothing marks no position.
def empty_delete_invisible(state: List<&2, Ops.Item>, +at: Nat, +more: List<&2, Ops.Op>, +q: Nat) -> {Spec.result_from(state, Ops.Op{Ops.Delete{}, at, Nil{}} <> more, q) == Spec.result_from(state, more, q) : List<&2, Ops.Item>}:
  match state:
    case Nil{}:
      {==}
    case it <> rest:
      %Equal.sym(Nat, Nat.add(at, 0n), at, add_zero(at)) : {List.append(&2, Ops.Item, Spec.inserts_at(more, q), List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Bool.or(Bool.and(Nat.is_le(at, q), Nat.is_lt(q, _)), Spec.deleted_at(more, q)), Nil{}, [it]), Spec.result_from(rest, Ops.Op{Ops.Delete{}, at, Nil{}} <> more, 1n+q))) == Spec.result_from(it <> rest, more, q) : List<&2, Ops.Item>}
      %Equal.sym(Bool, Bool.and(Nat.is_le(at, q), Nat.is_lt(q, at)), False{}, le_lt_contra(at, q)) : {List.append(&2, Ops.Item, Spec.inserts_at(more, q), List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Bool.or(_, Spec.deleted_at(more, q)), Nil{}, [it]), Spec.result_from(rest, Ops.Op{Ops.Delete{}, at, Nil{}} <> more, 1n+q))) == Spec.result_from(it <> rest, more, q) : List<&2, Ops.Item>}
      %Equal.sym(List<&2, Ops.Item>, Spec.result_from(rest, Ops.Op{Ops.Delete{}, at, Nil{}} <> more, 1n+q), Spec.result_from(rest, more, 1n+q), empty_delete_invisible(rest, at, more, 1n+q)) : {List.append(&2, Ops.Item, Spec.inserts_at(more, q), List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Spec.deleted_at(more, q), Nil{}, [it]), _)) == Spec.result_from(it <> rest, more, q) : List<&2, Ops.Item>}
      {==}

# Past the first quoted item, a delete reads as one starting a position later.
def delete_shrink(state: List<&2, Ops.Item>, +at: Nat, +head: Ops.Item, +tail: List<&2, Ops.Item>, +more: List<&2, Ops.Op>, +q: Nat, +le: {Nat.is_le(1n+at, q) == True{} : Bool}) -> {Spec.result_from(state, Ops.Op{Ops.Delete{}, at, head <> tail} <> more, q) == Spec.result_from(state, Ops.Op{Ops.Delete{}, 1n+at, tail} <> more, q) : List<&2, Ops.Item>}:
  match state:
    case Nil{}:
      {==}
    case +it <> +rest:
      +n = List.length(&2, Ops.Item, tail)
      +right = Spec.result_from(it <> rest, Ops.Op{Ops.Delete{}, 1n+at, tail} <> more, q)
      %Equal.sym(Nat, Nat.add(at, 1n+n), 1n+Nat.add(at, n), Pos.add_succ(at, n)) : {List.append(&2, Ops.Item, Spec.inserts_at(more, q), List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Bool.or(Bool.and(Nat.is_le(at, q), Nat.is_lt(q, _)), Spec.deleted_at(more, q)), Nil{}, [it]), Spec.result_from(rest, Ops.Op{Ops.Delete{}, at, head <> tail} <> more, 1n+q))) == right : List<&2, Ops.Item>}
      %Equal.sym(Bool, Nat.is_le(at, q), True{}, le_pred(at, q, le)) : {List.append(&2, Ops.Item, Spec.inserts_at(more, q), List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Bool.or(Bool.and(_, Nat.is_lt(q, 1n+Nat.add(at, n))), Spec.deleted_at(more, q)), Nil{}, [it]), Spec.result_from(rest, Ops.Op{Ops.Delete{}, at, head <> tail} <> more, 1n+q))) == right : List<&2, Ops.Item>}
      %Equal.sym(List<&2, Ops.Item>, Spec.result_from(rest, Ops.Op{Ops.Delete{}, at, head <> tail} <> more, 1n+q), Spec.result_from(rest, Ops.Op{Ops.Delete{}, 1n+at, tail} <> more, 1n+q), delete_shrink(rest, at, head, tail, more, 1n+q, le_succ(1n+at, q, le))) : {List.append(&2, Ops.Item, Spec.inserts_at(more, q), List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Bool.or(Nat.is_lt(q, 1n+Nat.add(at, n)), Spec.deleted_at(more, q)), Nil{}, [it]), _)) == right : List<&2, Ops.Item>}
      %Equal.sym(Bool, Nat.is_le(1n+at, q), True{}, le) : {List.append(&2, Ops.Item, Spec.inserts_at(more, q), List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Bool.or(Nat.is_lt(q, 1n+Nat.add(at, n)), Spec.deleted_at(more, q)), Nil{}, [it]), Spec.result_from(rest, Ops.Op{Ops.Delete{}, 1n+at, tail} <> more, 1n+q))) == List.append(&2, Ops.Item, Spec.inserts_at(more, q), List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Bool.or(Bool.and(_, Nat.is_lt(q, 1n+Nat.add(at, n))), Spec.deleted_at(more, q)), Nil{}, [it]), Spec.result_from(rest, Ops.Op{Ops.Delete{}, 1n+at, tail} <> more, 1n+q))) : List<&2, Ops.Item>}
      {==}

# A delete whose quote the parent holds removes exactly that many items,
# provided what follows sits past the removed run.
def delete_head(recorded: List<&2, Ops.Item>, +state: List<&2, Ops.Item>, +at: Nat, +more: List<&2, Ops.Op>, +lb: {below(more, Nat.add(at, List.length(&2, Ops.Item, recorded))) == True{} : Bool}, +ok: {Spec.prefix_matches(recorded, state) == True{} : Bool}) -> {Spec.result_from(state, Ops.Op{Ops.Delete{}, at, recorded} <> more, at) == Spec.result_from(List.drop(&2, Ops.Item, state, List.length(&2, Ops.Item, recorded)), more, Nat.add(at, List.length(&2, Ops.Item, recorded))) : List<&2, Ops.Item>}:
  match recorded state:
    case Nil{} Nil{}:
      %Equal.sym(Nat, Nat.add(at, 0n), at, add_zero(at)) : {Spec.result_from(Nil{}, Ops.Op{Ops.Delete{}, at, Nil{}} <> more, at) == Spec.result_from(Nil{}, more, _) : List<&2, Ops.Item>}
      {==}
    case Nil{} it <> rest:
      %Equal.sym(Nat, Nat.add(at, 0n), at, add_zero(at)) : {Spec.result_from(it <> rest, Ops.Op{Ops.Delete{}, at, Nil{}} <> more, at) == Spec.result_from(it <> rest, more, _) : List<&2, Ops.Item>}
      empty_delete_invisible(it <> rest, at, more, at)
    case h <> t Nil{}:
      Empty.absurd({Spec.result_from(Nil{}, Ops.Op{Ops.Delete{}, at, h <> t} <> more, at) == Spec.result_from(List.drop(&2, Ops.Item, Nil{}, List.length(&2, Ops.Item, h <> t)), more, Nat.add(at, List.length(&2, Ops.Item, h <> t))) : List<&2, Ops.Item>}, false_true(ok))
    case +h <> +t +it <> +rest:
      +n = List.length(&2, Ops.Item, t)
      +stop = Nat.add(at, 1n+n)
      +right = Spec.result_from(List.drop(&2, Ops.Item, rest, n), more, stop)
      %Equal.sym(List<&2, Ops.Item>, Spec.inserts_at(more, at), Nil{}, no_insert_below(more, stop, at, lb, lt_add_succ(at, n))) : {List.append(&2, Ops.Item, _, List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Bool.or(Bool.and(Nat.is_le(at, at), Nat.is_lt(at, stop)), Spec.deleted_at(more, at)), Nil{}, [it]), Spec.result_from(rest, Ops.Op{Ops.Delete{}, at, h <> t} <> more, 1n+at))) == right : List<&2, Ops.Item>}
      %Equal.sym(Bool, Nat.is_le(at, at), True{}, le_refl(at)) : {List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Bool.or(Bool.and(_, Nat.is_lt(at, stop)), Spec.deleted_at(more, at)), Nil{}, [it]), Spec.result_from(rest, Ops.Op{Ops.Delete{}, at, h <> t} <> more, 1n+at)) == right : List<&2, Ops.Item>}
      %Equal.sym(Bool, Nat.is_lt(at, stop), True{}, lt_add_succ(at, n)) : {List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Bool.or(_, Spec.deleted_at(more, at)), Nil{}, [it]), Spec.result_from(rest, Ops.Op{Ops.Delete{}, at, h <> t} <> more, 1n+at)) == right : List<&2, Ops.Item>}
      %Equal.sym(List<&2, Ops.Item>, Spec.result_from(rest, Ops.Op{Ops.Delete{}, at, h <> t} <> more, 1n+at), Spec.result_from(rest, Ops.Op{Ops.Delete{}, 1n+at, t} <> more, 1n+at), delete_shrink(rest, at, h, t, more, 1n+at, le_refl(at))) : {_ == right : List<&2, Ops.Item>}
      %Equal.sym(List<&2, Ops.Item>, Spec.result_from(rest, Ops.Op{Ops.Delete{}, 1n+at, t} <> more, 1n+at), Spec.result_from(List.drop(&2, Ops.Item, rest, n), more, Nat.add(1n+at, n)), delete_head(t, rest, 1n+at, more, below_at(more, stop, Nat.add(1n+at, n), Pos.add_succ(at, n), lb), and_right(Spec.matches(h, it), Spec.prefix_matches(t, rest), ok))) : {_ == right : List<&2, Ops.Item>}
      %Equal.sym(Nat, stop, 1n+Nat.add(at, n), Pos.add_succ(at, n)) : {Spec.result_from(List.drop(&2, Ops.Item, rest, n), more, Nat.add(1n+at, n)) == Spec.result_from(List.drop(&2, Ops.Item, rest, n), more, _) : List<&2, Ops.Item>}
      {==}

# A delete and an insert read the same in either order.
def swap_delete_insert(state: List<&2, Ops.Item>, +at: Nat, +recorded: List<&2, Ops.Item>, +at2: Nat, +items: List<&2, Ops.Item>, +more: List<&2, Ops.Op>, +q: Nat) -> {Spec.result_from(state, Ops.Op{Ops.Delete{}, at, recorded} <> Ops.Op{Ops.Insert{}, at2, items} <> more, q) == Spec.result_from(state, Ops.Op{Ops.Insert{}, at2, items} <> Ops.Op{Ops.Delete{}, at, recorded} <> more, q) : List<&2, Ops.Item>}:
  match state:
    case Nil{}:
      {==}
    case it <> rest:
      %Equal.sym(List<&2, Ops.Item>, Spec.result_from(rest, Ops.Op{Ops.Delete{}, at, recorded} <> Ops.Op{Ops.Insert{}, at2, items} <> more, 1n+q), Spec.result_from(rest, Ops.Op{Ops.Insert{}, at2, items} <> Ops.Op{Ops.Delete{}, at, recorded} <> more, 1n+q), swap_delete_insert(rest, at, recorded, at2, items, more, 1n+q)) : {List.append(&2, Ops.Item, List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Nat.is_eq(at2, q), items, Nil{}), Spec.inserts_at(more, q)), List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, Bool.or(Bool.and(Nat.is_le(at, q), Nat.is_lt(q, Nat.add(at, List.length(&2, Ops.Item, recorded)))), Spec.deleted_at(more, q)), Nil{}, [it]), _)) == Spec.result_from(it <> rest, Ops.Op{Ops.Insert{}, at2, items} <> Ops.Op{Ops.Delete{}, at, recorded} <> more, q) : List<&2, Ops.Item>}
      {==}

# Any block at the head, read at its own position: its inserted items, then
# the rest read past what it consumed.
def result_block(edit: Ops.Edit, +after: List<&2, Ops.Item>, +here: Nat, +more: List<&2, Ops.Op>, +lb: {below(more, Nat.add(here, Ops.consumed(edit))) == True{} : Bool}, +ok: {Block.agrees(edit, after) == True{} : Bool}) -> {Spec.result_from(after, List.append(&2, Ops.Op, Ops.operations(here, edit), more), here) == List.append(&2, Ops.Item, Ops.inserted(edit), Spec.result_from(List.drop(&2, Ops.Item, after, Ops.consumed(edit)), more, Nat.add(here, Ops.consumed(edit)))) : List<&2, Ops.Item>}:
  match edit:
    case Ops.Insertion{+items}:
      %Equal.sym(List<&2, Ops.Item>, List.drop(&2, Ops.Item, after, 0n), after, Pos.drop_zero(after)) : {Spec.result_from(after, Ops.Op{Ops.Insert{}, here, items} <> more, here) == List.append(&2, Ops.Item, items, Spec.result_from(_, more, Nat.add(here, 0n))) : List<&2, Ops.Item>}
      %Equal.sym(Nat, Nat.add(here, 0n), here, add_zero(here)) : {Spec.result_from(after, Ops.Op{Ops.Insert{}, here, items} <> more, here) == List.append(&2, Ops.Item, items, Spec.result_from(after, more, _)) : List<&2, Ops.Item>}
      insert_head(after, here, items, more)
    case Ops.Deletion{+recorded}:
      delete_head(recorded, after, here, more, lb, ok)
    case Ops.Replacement{+recorded, +items}:
      +n = List.length(&2, Ops.Item, recorded)
      +right = List.append(&2, Ops.Item, items, Spec.result_from(List.drop(&2, Ops.Item, after, n), more, Nat.add(here, n)))
      %Equal.sym(List<&2, Ops.Item>, Spec.result_from(after, Ops.Op{Ops.Delete{}, here, recorded} <> Ops.Op{Ops.Insert{}, here, items} <> more, here), Spec.result_from(after, Ops.Op{Ops.Insert{}, here, items} <> Ops.Op{Ops.Delete{}, here, recorded} <> more, here), swap_delete_insert(after, here, recorded, here, items, more, here)) : {_ == right : List<&2, Ops.Item>}
      %Equal.sym(List<&2, Ops.Item>, Spec.result_from(after, Ops.Op{Ops.Insert{}, here, items} <> Ops.Op{Ops.Delete{}, here, recorded} <> more, here), List.append(&2, Ops.Item, items, Spec.result_from(after, Ops.Op{Ops.Delete{}, here, recorded} <> more, here)), insert_head(after, here, items, Ops.Op{Ops.Delete{}, here, recorded} <> more)) : {_ == right : List<&2, Ops.Item>}
      %Equal.sym(List<&2, Ops.Item>, Spec.result_from(after, Ops.Op{Ops.Delete{}, here, recorded} <> more, here), Spec.result_from(List.drop(&2, Ops.Item, after, n), more, Nat.add(here, n)), delete_head(recorded, after, here, more, lb, ok)) : {List.append(&2, Ops.Item, items, _) == right : List<&2, Ops.Item>}
      {==}

# The refusal, read block by block
# --------------------------------

def error_block(edit: Ops.Edit, +parent: List<&2, Ops.Item>, +here: Nat, +more: List<&2, Ops.Op>) -> {Block.quote_error(parent, List.append(&2, Ops.Op, Ops.operations(here, edit), more)) == Maybe.or(&2, String, Cursor.disagreement(here, Block.agrees(edit, List.drop(&2, Ops.Item, parent, here))), Block.quote_error(parent, more)) : Maybe<&2, String>}:
  match edit:
    case Ops.Insertion{items}:
      {==}
    case Ops.Deletion{recorded}:
      {==}
    case Ops.Replacement{recorded, items}:
      {==}

# Range and lower bounds of a script
# ----------------------------------

def in_range_left(+a: List<&2, Ops.Op>, +b: List<&2, Ops.Op>, +len: Nat, +e: {Ops.in_range(List.append(&2, Ops.Op, a, b), len) == True{} : Bool}) -> {Ops.in_range(a, len) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case +op <> +rest:
      %Equal.sym(Bool, Nat.is_le(Ops.end(op), len), True{}, and_left(Nat.is_le(Ops.end(op), len), Ops.in_range(List.append(&2, Ops.Op, rest, b), len), e)) : {Bool.and(_, Ops.in_range(rest, len)) == True{} : Bool}
      %Equal.sym(Bool, Ops.in_range(rest, len), True{}, in_range_left(rest, b, len, and_right(Nat.is_le(Ops.end(op), len), Ops.in_range(List.append(&2, Ops.Op, rest, b), len), e))) : {Bool.and(True{}, _) == True{} : Bool}
      {==}

def in_range_right(+a: List<&2, Ops.Op>, +b: List<&2, Ops.Op>, +len: Nat, +e: {Ops.in_range(List.append(&2, Ops.Op, a, b), len) == True{} : Bool}) -> {Ops.in_range(b, len) == True{} : Bool}:
  match a:
    case Nil{}:
      e
    case +op <> +rest:
      in_range_right(rest, b, len, and_right(Nat.is_le(Ops.end(op), len), Ops.in_range(List.append(&2, Ops.Op, rest, b), len), e))

# A block in range starts within the parent.
def block_start(edit: Ops.Edit, +here: Nat, +len: Nat, +e: {Ops.in_range(Ops.operations(here, edit), len) == True{} : Bool}) -> {Nat.is_le(here, len) == True{} : Bool}:
  match edit:
    case Ops.Insertion{items}:
      and_left(Nat.is_le(here, len), True{}, e)
    case Ops.Deletion{+recorded}:
      le_add_left(here, List.length(&2, Ops.Item, recorded), len, and_left(Nat.is_le(Nat.add(here, List.length(&2, Ops.Item, recorded)), len), True{}, e))
    case Ops.Replacement{+recorded, items}:
      and_left(Nat.is_le(here, len), True{}, and_right(Nat.is_le(Nat.add(here, List.length(&2, Ops.Item, recorded)), len), Bool.and(Nat.is_le(here, len), True{}), e))

def block_below(edit: Ops.Edit, +here: Nat, +q: Nat, +le: {Nat.is_le(q, here) == True{} : Bool}) -> {below(Ops.operations(here, edit), q) == True{} : Bool}:
  match edit:
    case Ops.Insertion{items}:
      %Equal.sym(Bool, Nat.is_le(q, here), True{}, le) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case Ops.Deletion{recorded}:
      %Equal.sym(Bool, Nat.is_le(q, here), True{}, le) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case Ops.Replacement{recorded, items}:
      %Equal.sym(Bool, Nat.is_le(q, here), True{}, le) : {Bool.and(_, Bool.and(_, True{})) == True{} : Bool}
      {==}

def script_below(steps: List<&2, Ops.Step>, +at: Nat, +q: Nat, +le: {Nat.is_le(q, at) == True{} : Bool}) -> {below(Ops.script(steps, at), q) == True{} : Bool}:
  match steps:
    case Nil{}:
      {==}
    case Ops.Step{+gap, +edit} <> +rest:
      +here = Nat.add(at, gap)
      +next = Nat.add(here, Ops.consumed(edit))
      below_join(Ops.operations(here, edit), Ops.script(rest, next), q, block_below(edit, here, q, le_add(q, at, gap, le)), script_below(rest, next, q, le_add(q, here, Ops.consumed(edit), le_add(q, at, gap, le))))

# The cursor over one block at the head
# -------------------------------------

def walk_block(edit: Ops.Edit, +pos: Nat, +gap: Nat, +state: List<&2, Ops.Item>, +more: List<&2, Ops.Op>) -> {Cursor.walk(List.append(&2, Ops.Op, Ops.operations(Nat.add(pos, gap), edit), more), pos, state) == Cursor.combine(Cursor.disagreement(Nat.add(pos, gap), Block.agrees(edit, List.drop(&2, Ops.Item, state, gap))), List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, gap), Ops.inserted(edit)), Cursor.walk(more, Nat.add(Nat.add(pos, gap), Ops.consumed(edit)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, gap), Ops.consumed(edit)))) : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match edit:
    case Ops.Insertion{+items}:
      +here = Nat.add(pos, gap)
      +after = List.drop(&2, Ops.Item, state, gap)
      %Equal.sym(Nat, Nat.sub(here, pos), gap, sub_add(pos, gap)) : {Cursor.combine(None{}, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, _), items), Cursor.walk(more, Nat.max(pos, here), List.drop(&2, Ops.Item, state, _))) == Cursor.combine(None{}, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, gap), items), Cursor.walk(more, Nat.add(here, 0n), List.drop(&2, Ops.Item, after, 0n))) : Result<&2, &2, String, List<&2, Ops.Item>>}
      %Equal.sym(Nat, Nat.max(pos, here), here, max_add(pos, gap)) : {Cursor.combine(None{}, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, gap), items), Cursor.walk(more, _, after)) == Cursor.combine(None{}, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, gap), items), Cursor.walk(more, Nat.add(here, 0n), List.drop(&2, Ops.Item, after, 0n))) : Result<&2, &2, String, List<&2, Ops.Item>>}
      %Equal.sym(Nat, Nat.add(here, 0n), here, add_zero(here)) : {Cursor.combine(None{}, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, gap), items), Cursor.walk(more, here, after)) == Cursor.combine(None{}, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, gap), items), Cursor.walk(more, _, List.drop(&2, Ops.Item, after, 0n))) : Result<&2, &2, String, List<&2, Ops.Item>>}
      %Equal.sym(List<&2, Ops.Item>, List.drop(&2, Ops.Item, after, 0n), after, Pos.drop_zero(after)) : {Cursor.combine(None{}, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, gap), items), Cursor.walk(more, here, after)) == Cursor.combine(None{}, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, gap), items), Cursor.walk(more, here, _)) : Result<&2, &2, String, List<&2, Ops.Item>>}
      {==}
    case Ops.Deletion{+recorded}:
      +here = Nat.add(pos, gap)
      +after = List.drop(&2, Ops.Item, state, gap)
      +n = List.length(&2, Ops.Item, recorded)
      %Equal.sym(Nat, Nat.sub(here, pos), gap, sub_add(pos, gap)) : {Cursor.combine(Cursor.disagreement(here, Spec.prefix_matches(recorded, List.drop(&2, Ops.Item, state, _))), List.take(&2, Ops.Item, state, _), Cursor.walk(more, Nat.add(here, n), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, _), n))) == Cursor.combine(Cursor.disagreement(here, Spec.prefix_matches(recorded, after)), List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, gap), Nil{}), Cursor.walk(more, Nat.add(here, n), List.drop(&2, Ops.Item, after, n))) : Result<&2, &2, String, List<&2, Ops.Item>>}
      %L.append_nil(List.take(&2, Ops.Item, state, gap)) : {Cursor.combine(Cursor.disagreement(here, Spec.prefix_matches(recorded, after)), _, Cursor.walk(more, Nat.add(here, n), List.drop(&2, Ops.Item, after, n))) == Cursor.combine(Cursor.disagreement(here, Spec.prefix_matches(recorded, after)), List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, gap), Nil{}), Cursor.walk(more, Nat.add(here, n), List.drop(&2, Ops.Item, after, n))) : Result<&2, &2, String, List<&2, Ops.Item>>}
      {==}
    case Ops.Replacement{+recorded, +items}:
      +here = Nat.add(pos, gap)
      +after = List.drop(&2, Ops.Item, state, gap)
      +n = List.length(&2, Ops.Item, recorded)
      +stop = Nat.add(here, n)
      +left = List.drop(&2, Ops.Item, after, n)
      +failure = Cursor.disagreement(here, Spec.prefix_matches(recorded, after))
      +front = List.take(&2, Ops.Item, state, gap)
      +right = Cursor.combine(failure, List.append(&2, Ops.Item, front, items), Cursor.walk(more, stop, left))
      %Equal.sym(Nat, Nat.sub(here, pos), gap, sub_add(pos, gap)) : {Cursor.combine(Cursor.disagreement(here, Spec.prefix_matches(recorded, List.drop(&2, Ops.Item, state, _))), List.take(&2, Ops.Item, state, _), Cursor.walk(Ops.Op{Ops.Insert{}, here, items} <> more, stop, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, _), n))) == right : Result<&2, &2, String, List<&2, Ops.Item>>}
      %Equal.sym(Nat, Nat.sub(here, stop), 0n, Pos.sub_past(here, n)) : {Cursor.combine(failure, front, Cursor.combine(None{}, List.append(&2, Ops.Item, List.take(&2, Ops.Item, left, _), items), Cursor.walk(more, Nat.max(stop, here), List.drop(&2, Ops.Item, left, _)))) == right : Result<&2, &2, String, List<&2, Ops.Item>>}
      %Equal.sym(List<&2, Ops.Item>, List.take(&2, Ops.Item, left, 0n), Nil{}, Pos.take_zero(left)) : {Cursor.combine(failure, front, Cursor.combine(None{}, List.append(&2, Ops.Item, _, items), Cursor.walk(more, Nat.max(stop, here), List.drop(&2, Ops.Item, left, 0n)))) == right : Result<&2, &2, String, List<&2, Ops.Item>>}
      %Equal.sym(List<&2, Ops.Item>, List.drop(&2, Ops.Item, left, 0n), left, Pos.drop_zero(left)) : {Cursor.combine(failure, front, Cursor.combine(None{}, items, Cursor.walk(more, Nat.max(stop, here), _))) == right : Result<&2, &2, String, List<&2, Ops.Item>>}
      %Equal.sym(Nat, Nat.max(stop, here), stop, max_add_left(here, n)) : {Cursor.combine(failure, front, Cursor.combine(None{}, items, Cursor.walk(more, _, left))) == right : Result<&2, &2, String, List<&2, Ops.Item>>}
      %L.or_none(failure) : {Cursor.combine(failure, front, Cursor.combine(None{}, items, Cursor.walk(more, stop, left))) == Cursor.combine(_, List.append(&2, Ops.Item, front, items), Cursor.walk(more, stop, left)) : Result<&2, &2, String, List<&2, Ops.Item>>}
      L.combine_assoc(failure, None{}, front, items, Cursor.walk(more, stop, left))

# The whole script
# ----------------

# Once a delete disagrees the payload is irrelevant: both sides are that refusal.
def settle(+here: Nat, ok: Bool, +error: Maybe<&2, String>, -x: List<&2, Ops.Item>, -y: List<&2, Ops.Item>, f: {ok == True{} : Bool} -> {x == y : List<&2, Ops.Item>}) -> {Cursor.combine(Maybe.or(&2, String, Cursor.disagreement(here, ok), error), Nil{}, Done{x}) == Cursor.combine(Maybe.or(&2, String, Cursor.disagreement(here, ok), error), Nil{}, Done{y}) : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match ok:
    case True{}:
      %f({==}) : {Cursor.combine(error, Nil{}, Done{x}) == Cursor.combine(error, Nil{}, Done{_}) : Result<&2, &2, String, List<&2, Ops.Item>>}
      {==}
    case False{}:
      {==}

# When the block's quote agrees, the cursor's front and the positional
# remainder are the positional result of the whole.
def block_payload(+edit: Ops.Edit, +pos: Nat, +gap: Nat, +parent: List<&2, Ops.Item>, +rest: List<&2, Ops.Step>, okp: {Block.agrees(edit, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, parent, pos), gap)) == True{} : Bool}) -> {List.append(&2, Ops.Item, List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, parent, pos), gap), Ops.inserted(edit)), Spec.result_from(List.drop(&2, Ops.Item, parent, Nat.add(Nat.add(pos, gap), Ops.consumed(edit))), Ops.script(rest, Nat.add(Nat.add(pos, gap), Ops.consumed(edit))), Nat.add(Nat.add(pos, gap), Ops.consumed(edit)))) == List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, parent, pos), gap), Spec.result_from(List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, parent, pos), gap), List.append(&2, Ops.Op, Ops.operations(Nat.add(pos, gap), edit), Ops.script(rest, Nat.add(Nat.add(pos, gap), Ops.consumed(edit)))), Nat.add(pos, gap))) : List<&2, Ops.Item>}:
  +here = Nat.add(pos, gap)
  +n = Ops.consumed(edit)
  +next = Nat.add(here, n)
  +state = List.drop(&2, Ops.Item, parent, pos)
  +after = List.drop(&2, Ops.Item, state, gap)
  +front = List.take(&2, Ops.Item, state, gap)
  +more = Ops.script(rest, next)
  +remainder = Spec.result_from(List.drop(&2, Ops.Item, parent, next), more, next)
  +left = List.append(&2, Ops.Item, List.append(&2, Ops.Item, front, Ops.inserted(edit)), remainder)
  %Equal.sym(List<&2, Ops.Item>, Spec.result_from(after, List.append(&2, Ops.Op, Ops.operations(here, edit), more), here), List.append(&2, Ops.Item, Ops.inserted(edit), Spec.result_from(List.drop(&2, Ops.Item, after, n), more, next)), result_block(edit, after, here, more, script_below(rest, next, next, le_refl(next)), okp)) : {left == List.append(&2, Ops.Item, front, _) : List<&2, Ops.Item>}
  %Equal.sym(List<&2, Ops.Item>, after, List.drop(&2, Ops.Item, parent, here), drop_drop(pos, parent, gap)) : {left == List.append(&2, Ops.Item, front, List.append(&2, Ops.Item, Ops.inserted(edit), Spec.result_from(List.drop(&2, Ops.Item, _, n), more, next))) : List<&2, Ops.Item>}
  %Equal.sym(List<&2, Ops.Item>, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, parent, here), n), List.drop(&2, Ops.Item, parent, next), drop_drop(here, parent, n)) : {left == List.append(&2, Ops.Item, front, List.append(&2, Ops.Item, Ops.inserted(edit), Spec.result_from(_, more, next))) : List<&2, Ops.Item>}
  L.append_assoc(front, Ops.inserted(edit), remainder)

def walk_script.front(error: Maybe<&2, String>, +moved: List<&2, Ops.Item>, +remainder: List<&2, Ops.Item>) -> {Cursor.combine(error, List.append(&2, Ops.Item, moved, Nil{}), Done{remainder}) == Cursor.combine(error, Nil{}, Done{List.append(&2, Ops.Item, moved, remainder)}) : Result<&2, &2, String, List<&2, Ops.Item>>}:
  %Equal.sym(List<&2, Ops.Item>, List.append(&2, Ops.Item, moved, Nil{}), moved, L.append_nil(moved)) : {Cursor.combine(error, _, Done{remainder}) == Cursor.combine(error, Nil{}, Done{List.append(&2, Ops.Item, moved, remainder)}) : Result<&2, &2, String, List<&2, Ops.Item>>}
  Pos.project_block(error, moved, remainder, List.append(&2, Ops.Item, moved, remainder), {==})

def walk_script.positional(+edit: Ops.Edit, +pos: Nat, +gap: Nat, +parent: List<&2, Ops.Item>, +rest: List<&2, Ops.Step>, +bound: {below(List.append(&2, Ops.Op, Ops.operations(Nat.add(pos, gap), edit), Ops.script(rest, Nat.add(Nat.add(pos, gap), Ops.consumed(edit)))), Nat.add(pos, gap)) == True{} : Bool}, fits: {Nat.is_le(gap, List.length(&2, Ops.Item, List.drop(&2, Ops.Item, parent, pos))) == True{} : Bool}) -> {Cursor.combine(Maybe.or(&2, String, Cursor.disagreement(Nat.add(pos, gap), Block.agrees(edit, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, parent, pos), gap))), Block.quote_error(parent, Ops.script(rest, Nat.add(Nat.add(pos, gap), Ops.consumed(edit))))), Nil{}, Done{List.append(&2, Ops.Item, List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, parent, pos), gap), Ops.inserted(edit)), Spec.result_from(List.drop(&2, Ops.Item, parent, Nat.add(Nat.add(pos, gap), Ops.consumed(edit))), Ops.script(rest, Nat.add(Nat.add(pos, gap), Ops.consumed(edit))), Nat.add(Nat.add(pos, gap), Ops.consumed(edit))))}) == Cursor.combine(Block.quote_error(parent, List.append(&2, Ops.Op, Ops.operations(Nat.add(pos, gap), edit), Ops.script(rest, Nat.add(Nat.add(pos, gap), Ops.consumed(edit))))), Nil{}, Done{Spec.result_from(List.drop(&2, Ops.Item, parent, pos), List.append(&2, Ops.Op, Ops.operations(Nat.add(pos, gap), edit), Ops.script(rest, Nat.add(Nat.add(pos, gap), Ops.consumed(edit)))), pos)}) : Result<&2, &2, String, List<&2, Ops.Item>>}:
  +here = Nat.add(pos, gap)
  +n = Ops.consumed(edit)
  +next = Nat.add(here, n)
  +state = List.drop(&2, Ops.Item, parent, pos)
  +after = List.drop(&2, Ops.Item, state, gap)
  +front = List.take(&2, Ops.Item, state, gap)
  +block = Ops.operations(here, edit)
  +more = Ops.script(rest, next)
  +ops = List.append(&2, Ops.Op, block, more)
  +moved = List.append(&2, Ops.Item, front, Ops.inserted(edit))
  +later = Block.quote_error(parent, more)
  +remainder = Spec.result_from(List.drop(&2, Ops.Item, parent, next), more, next)
  +settled = Cursor.combine(Maybe.or(&2, String, Cursor.disagreement(here, Block.agrees(edit, after)), later), Nil{}, Done{List.append(&2, Ops.Item, moved, remainder)})
  %Equal.sym(Maybe<&2, String>, Block.quote_error(parent, ops), Maybe.or(&2, String, Cursor.disagreement(here, Block.agrees(edit, List.drop(&2, Ops.Item, parent, here))), later), error_block(edit, parent, here, more)) : {settled == Cursor.combine(_, Nil{}, Done{Spec.result_from(state, ops, pos)}) : Result<&2, &2, String, List<&2, Ops.Item>>}
  %drop_drop(pos, parent, gap) : {settled == Cursor.combine(Maybe.or(&2, String, Cursor.disagreement(here, Block.agrees(edit, _)), later), Nil{}, Done{Spec.result_from(state, ops, pos)}) : Result<&2, &2, String, List<&2, Ops.Item>>}
  %Equal.sym(List<&2, Ops.Item>, Spec.result_from(state, ops, pos), List.append(&2, Ops.Item, front, Spec.result_from(after, ops, here)), skip(gap, state, ops, pos, bound, fits)) : {settled == Cursor.combine(Maybe.or(&2, String, Cursor.disagreement(here, Block.agrees(edit, after)), later), Nil{}, Done{_}) : Result<&2, &2, String, List<&2, Ops.Item>>}
  settle(here, Block.agrees(edit, after), later, List.append(&2, Ops.Item, moved, remainder), List.append(&2, Ops.Item, front, Spec.result_from(after, ops, here)), okp => block_payload(edit, pos, gap, parent, rest, okp))

def walk_script.cursor(+edit: Ops.Edit, +pos: Nat, +gap: Nat, +parent: List<&2, Ops.Item>, +rest: List<&2, Ops.Step>, ih: {Cursor.walk(Ops.script(rest, Nat.add(Nat.add(pos, gap), Ops.consumed(edit))), Nat.add(Nat.add(pos, gap), Ops.consumed(edit)), List.drop(&2, Ops.Item, parent, Nat.add(Nat.add(pos, gap), Ops.consumed(edit)))) == Cursor.combine(Block.quote_error(parent, Ops.script(rest, Nat.add(Nat.add(pos, gap), Ops.consumed(edit)))), Nil{}, Done{Spec.result_from(List.drop(&2, Ops.Item, parent, Nat.add(Nat.add(pos, gap), Ops.consumed(edit))), Ops.script(rest, Nat.add(Nat.add(pos, gap), Ops.consumed(edit))), Nat.add(Nat.add(pos, gap), Ops.consumed(edit)))}) : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Cursor.walk(List.append(&2, Ops.Op, Ops.operations(Nat.add(pos, gap), edit), Ops.script(rest, Nat.add(Nat.add(pos, gap), Ops.consumed(edit)))), pos, List.drop(&2, Ops.Item, parent, pos)) == Cursor.combine(Maybe.or(&2, String, Cursor.disagreement(Nat.add(pos, gap), Block.agrees(edit, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, parent, pos), gap))), Block.quote_error(parent, Ops.script(rest, Nat.add(Nat.add(pos, gap), Ops.consumed(edit))))), Nil{}, Done{List.append(&2, Ops.Item, List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, parent, pos), gap), Ops.inserted(edit)), Spec.result_from(List.drop(&2, Ops.Item, parent, Nat.add(Nat.add(pos, gap), Ops.consumed(edit))), Ops.script(rest, Nat.add(Nat.add(pos, gap), Ops.consumed(edit))), Nat.add(Nat.add(pos, gap), Ops.consumed(edit))))}) : Result<&2, &2, String, List<&2, Ops.Item>>}:
  +here = Nat.add(pos, gap)
  +n = Ops.consumed(edit)
  +next = Nat.add(here, n)
  +state = List.drop(&2, Ops.Item, parent, pos)
  +after = List.drop(&2, Ops.Item, state, gap)
  +front = List.take(&2, Ops.Item, state, gap)
  +block = Ops.operations(here, edit)
  +more = Ops.script(rest, next)
  +ops = List.append(&2, Ops.Op, block, more)
  +failure = Cursor.disagreement(here, Block.agrees(edit, after))
  +moved = List.append(&2, Ops.Item, front, Ops.inserted(edit))
  +later = Block.quote_error(parent, more)
  +remainder = Spec.result_from(List.drop(&2, Ops.Item, parent, next), more, next)
  +settled = Cursor.combine(Maybe.or(&2, String, failure, later), Nil{}, Done{List.append(&2, Ops.Item, moved, remainder)})
  +tail = Cursor.combine(later, Nil{}, Done{remainder})
  %Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.walk(ops, pos, state), Cursor.combine(failure, moved, Cursor.walk(more, next, List.drop(&2, Ops.Item, after, n))), walk_block(edit, pos, gap, state, more)) : {_ == settled : Result<&2, &2, String, List<&2, Ops.Item>>}
  %Equal.sym(List<&2, Ops.Item>, after, List.drop(&2, Ops.Item, parent, here), drop_drop(pos, parent, gap)) : {Cursor.combine(failure, moved, Cursor.walk(more, next, List.drop(&2, Ops.Item, _, n))) == settled : Result<&2, &2, String, List<&2, Ops.Item>>}
  %Equal.sym(List<&2, Ops.Item>, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, parent, here), n), List.drop(&2, Ops.Item, parent, next), drop_drop(here, parent, n)) : {Cursor.combine(failure, moved, Cursor.walk(more, next, _)) == settled : Result<&2, &2, String, List<&2, Ops.Item>>}
  %Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.walk(more, next, List.drop(&2, Ops.Item, parent, next)), tail, ih) : {Cursor.combine(failure, moved, _) == settled : Result<&2, &2, String, List<&2, Ops.Item>>}
  Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.combine(failure, moved, tail), Cursor.combine(Maybe.or(&2, String, failure, later), List.append(&2, Ops.Item, moved, Nil{}), Done{remainder}), settled,
    L.combine_assoc(failure, later, moved, Nil{}, Done{remainder}),
    walk_script.front(Maybe.or(&2, String, failure, later), moved, remainder))

# The cursor over a script that fits the parent is the positional result of
# that script, or the first quote disagreement, whichever the script reaches.
def walk_script(steps: List<&2, Ops.Step>, +pos: Nat, +parent: List<&2, Ops.Item>, +range: {Ops.in_range(Ops.script(steps, pos), List.length(&2, Ops.Item, parent)) == True{} : Bool}) -> {Cursor.walk(Ops.script(steps, pos), pos, List.drop(&2, Ops.Item, parent, pos)) == Cursor.combine(Block.quote_error(parent, Ops.script(steps, pos)), Nil{}, Done{Spec.result_from(List.drop(&2, Ops.Item, parent, pos), Ops.script(steps, pos), pos)}) : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match steps:
    case Nil{}:
      +state = List.drop(&2, Ops.Item, parent, pos)
      %Equal.sym(List<&2, Ops.Item>, Spec.result_from(state, Nil{}, pos), state, result_nil(state, pos)) : {Done{state} == Done{_} : Result<&2, &2, String, List<&2, Ops.Item>>}
      {==}
    case Ops.Step{+gap, +edit} <> +rest:
      +here = Nat.add(pos, gap)
      +n = Ops.consumed(edit)
      +next = Nat.add(here, n)
      +len = List.length(&2, Ops.Item, parent)
      +state = List.drop(&2, Ops.Item, parent, pos)
      +after = List.drop(&2, Ops.Item, state, gap)
      +front = List.take(&2, Ops.Item, state, gap)
      +block = Ops.operations(here, edit)
      +more = Ops.script(rest, next)
      +ops = List.append(&2, Ops.Op, block, more)
      +failure = Cursor.disagreement(here, Block.agrees(edit, after))
      +moved = List.append(&2, Ops.Item, front, Ops.inserted(edit))
      +later = Block.quote_error(parent, more)
      +remainder = Spec.result_from(List.drop(&2, Ops.Item, parent, next), more, next)
      +settled = Cursor.combine(Maybe.or(&2, String, failure, later), Nil{}, Done{List.append(&2, Ops.Item, moved, remainder)})
      +range_more = in_range_right(block, more, len, range)
      +bound = below_join(block, more, here, block_below(edit, here, here, le_refl(here)), script_below(rest, next, here, le_add(here, here, n, le_refl(here))))
      +fits = gap_fits(gap, pos, parent, block_start(edit, here, len, in_range_left(block, more, len, range)))
      Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.walk(ops, pos, state), settled, Cursor.combine(Block.quote_error(parent, ops), Nil{}, Done{Spec.result_from(state, ops, pos)}),
        walk_script.cursor(edit, pos, gap, parent, rest, walk_script(rest, next, parent, range_more)),
        walk_script.positional(edit, pos, gap, parent, rest, bound, fits))

# Ordered operations are a script
# -------------------------------

def add_sub(pos: Nat, at: Nat, e: {Nat.is_le(pos, at) == True{} : Bool}) -> {Nat.add(pos, Nat.sub(at, pos)) == at : Nat}:
  match pos at:
    case 0n _:
      Pos.sub_zero(at)
    case 1n+p 0n:
      Empty.absurd({1n+Nat.add(p, Nat.sub(0n, 1n+p)) == 0n : Nat}, false_true(e))
    case 1n+p 1n+a:
      %add_sub(p, a, e) : {1n+Nat.add(p, Nat.sub(a, p)) == 1n+_ : Nat}
      {==}

def eq_of_is_eq(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, false_true(e))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, false_true(e))
    case 1n+ap 1n+bp:
      Equal.cong(Nat, Nat, n => 1n+n, ap, bp, eq_of_is_eq(ap, bp, e))

# A delete followed by an insert: the insert is its replacement when it sits
# at the delete's own position, and a block of its own otherwise.
def is_script.replacement(+pos: Nat, +at: Nat, +items: List<&2, Ops.Item>, +at2: Nat, +items2: List<&2, Ops.Item>, +more: List<&2, Ops.Op>, same: Bool, +eq: {Nat.is_eq(at2, at) == same : Bool}, +e: {Bool.and(Nat.is_le(pos, at), Bool.pick(Bool, same, Block.ordered(more, Nat.add(at, List.length(&2, Ops.Item, items))), Bool.and(Nat.is_le(Nat.add(at, List.length(&2, Ops.Item, items)), at2), Block.ordered(more, at2)))) == True{} : Bool}, ih_stop: {Block.ordered(more, Nat.add(at, List.length(&2, Ops.Item, items))) == True{} : Bool} -> {Ops.script(Block.steps_of(more, Nat.add(at, List.length(&2, Ops.Item, items))), Nat.add(at, List.length(&2, Ops.Item, items))) == more : List<&2, Ops.Op>}, ih_at2: {Block.ordered(more, at2) == True{} : Bool} -> {Ops.script(Block.steps_of(more, at2), at2) == more : List<&2, Ops.Op>}) -> {Ops.script(Block.steps_of(Ops.Op{Ops.Delete{}, at, items} <> Ops.Op{Ops.Insert{}, at2, items2} <> more, pos), pos) == Ops.Op{Ops.Delete{}, at, items} <> Ops.Op{Ops.Insert{}, at2, items2} <> more : List<&2, Ops.Op>}:
  match same:
    case True{}:
      +n = List.length(&2, Ops.Item, items)
      +stop = Nat.add(at, n)
      +here = Nat.add(pos, Nat.sub(at, pos))
      +rhs = {Ops.Op{Ops.Delete{}, at, items} <> Ops.Op{Ops.Insert{}, at2, items2} <> more : List<&2, Ops.Op>}
      %Equal.sym(Bool, Nat.is_eq(at2, at), True{}, eq) : {Ops.script(Bool.pick(List<&2, Ops.Step>, _, Ops.Step{Nat.sub(at, pos), Ops.Replacement{items, items2}} <> Block.steps_of(more, stop), Ops.Step{Nat.sub(at, pos), Ops.Deletion{items}} <> Ops.Step{Nat.sub(at2, stop), Ops.Insertion{items2}} <> Block.steps_of(more, at2)), pos) == rhs : List<&2, Ops.Op>}
      %Equal.sym(Nat, at2, at, eq_of_is_eq(at2, at, eq)) : {Ops.Op{Ops.Delete{}, here, items} <> Ops.Op{Ops.Insert{}, here, items2} <> Ops.script(Block.steps_of(more, stop), Nat.add(here, n)) == Ops.Op{Ops.Delete{}, at, items} <> Ops.Op{Ops.Insert{}, _, items2} <> more : List<&2, Ops.Op>}
      %Equal.sym(Nat, here, at, add_sub(pos, at, and_left(Nat.is_le(pos, at), Block.ordered(more, stop), e))) : {Ops.Op{Ops.Delete{}, _, items} <> Ops.Op{Ops.Insert{}, _, items2} <> Ops.script(Block.steps_of(more, stop), Nat.add(_, n)) == Ops.Op{Ops.Delete{}, at, items} <> Ops.Op{Ops.Insert{}, at, items2} <> more : List<&2, Ops.Op>}
      %Equal.sym(List<&2, Ops.Op>, Ops.script(Block.steps_of(more, stop), stop), more, ih_stop(and_right(Nat.is_le(pos, at), Block.ordered(more, stop), e))) : {Ops.Op{Ops.Delete{}, at, items} <> Ops.Op{Ops.Insert{}, at, items2} <> _ == Ops.Op{Ops.Delete{}, at, items} <> Ops.Op{Ops.Insert{}, at, items2} <> more : List<&2, Ops.Op>}
      {==}
    case False{}:
      +n = List.length(&2, Ops.Item, items)
      +stop = Nat.add(at, n)
      +here = Nat.add(pos, Nat.sub(at, pos))
      +there = Nat.add(stop, Nat.sub(at2, stop))
      +rhs = {Ops.Op{Ops.Delete{}, at, items} <> Ops.Op{Ops.Insert{}, at2, items2} <> more : List<&2, Ops.Op>}
      +past = Bool.and(Nat.is_le(stop, at2), Block.ordered(more, at2))
      %Equal.sym(Bool, Nat.is_eq(at2, at), False{}, eq) : {Ops.script(Bool.pick(List<&2, Ops.Step>, _, Ops.Step{Nat.sub(at, pos), Ops.Replacement{items, items2}} <> Block.steps_of(more, stop), Ops.Step{Nat.sub(at, pos), Ops.Deletion{items}} <> Ops.Step{Nat.sub(at2, stop), Ops.Insertion{items2}} <> Block.steps_of(more, at2)), pos) == rhs : List<&2, Ops.Op>}
      %Equal.sym(Nat, here, at, add_sub(pos, at, and_left(Nat.is_le(pos, at), past, e))) : {Ops.Op{Ops.Delete{}, _, items} <> Ops.Op{Ops.Insert{}, Nat.add(Nat.add(_, n), Nat.sub(at2, stop)), items2} <> Ops.script(Block.steps_of(more, at2), Nat.add(Nat.add(Nat.add(_, n), Nat.sub(at2, stop)), 0n)) == rhs : List<&2, Ops.Op>}
      %Equal.sym(Nat, there, at2, add_sub(stop, at2, and_left(Nat.is_le(stop, at2), Block.ordered(more, at2), and_right(Nat.is_le(pos, at), past, e)))) : {Ops.Op{Ops.Delete{}, at, items} <> Ops.Op{Ops.Insert{}, _, items2} <> Ops.script(Block.steps_of(more, at2), Nat.add(_, 0n)) == rhs : List<&2, Ops.Op>}
      %Equal.sym(Nat, Nat.add(at2, 0n), at2, add_zero(at2)) : {Ops.Op{Ops.Delete{}, at, items} <> Ops.Op{Ops.Insert{}, at2, items2} <> Ops.script(Block.steps_of(more, at2), _) == rhs : List<&2, Ops.Op>}
      %Equal.sym(List<&2, Ops.Op>, Ops.script(Block.steps_of(more, at2), at2), more, ih_at2(and_right(Nat.is_le(stop, at2), Block.ordered(more, at2), and_right(Nat.is_le(pos, at), past, e)))) : {Ops.Op{Ops.Delete{}, at, items} <> Ops.Op{Ops.Insert{}, at2, items2} <> _ == rhs : List<&2, Ops.Op>}
      {==}

# Every ordered operation list is the script `steps_of` reads from it.
def is_script(ops: List<&2, Ops.Op>, +pos: Nat, +e: {Block.ordered(ops, pos) == True{} : Bool}) -> {Ops.script(Block.steps_of(ops, pos), pos) == ops : List<&2, Ops.Op>}:
  match ops:
    case Nil{}:
      {==}
    case Ops.Op{Ops.Insert{}, +at, +items} <> +rest:
      +here = Nat.add(pos, Nat.sub(at, pos))
      %Equal.sym(Nat, here, at, add_sub(pos, at, and_left(Nat.is_le(pos, at), Block.ordered(rest, at), e))) : {Ops.Op{Ops.Insert{}, _, items} <> Ops.script(Block.steps_of(rest, at), Nat.add(_, 0n)) == Ops.Op{Ops.Insert{}, at, items} <> rest : List<&2, Ops.Op>}
      %Equal.sym(Nat, Nat.add(at, 0n), at, add_zero(at)) : {Ops.Op{Ops.Insert{}, at, items} <> Ops.script(Block.steps_of(rest, at), _) == Ops.Op{Ops.Insert{}, at, items} <> rest : List<&2, Ops.Op>}
      %Equal.sym(List<&2, Ops.Op>, Ops.script(Block.steps_of(rest, at), at), rest, is_script(rest, at, and_right(Nat.is_le(pos, at), Block.ordered(rest, at), e))) : {Ops.Op{Ops.Insert{}, at, items} <> _ == Ops.Op{Ops.Insert{}, at, items} <> rest : List<&2, Ops.Op>}
      {==}
    case Ops.Op{Ops.Delete{}, +at, +items} <> rest:
      match rest:
        case Nil{}:
          +here = Nat.add(pos, Nat.sub(at, pos))
          %Equal.sym(Nat, here, at, add_sub(pos, at, e)) : {[Ops.Op{Ops.Delete{}, _, items}] == [Ops.Op{Ops.Delete{}, at, items}] : List<&2, Ops.Op>}
          {==}
        case Ops.Op{Ops.Insert{}, +at2, +items2} <> +more:
          +stop = Nat.add(at, List.length(&2, Ops.Item, items))
          is_script.replacement(pos, at, items, at2, items2, more, Nat.is_eq(at2, at), {==}, e, x => is_script(more, stop, x), x => is_script(more, at2, x))
        case Ops.Op{Ops.Delete{}, +at2, +items2} <> +more:
          +n = List.length(&2, Ops.Item, items)
          +here = Nat.add(pos, Nat.sub(at, pos))
          +tail = {Ops.Op{Ops.Delete{}, at2, items2} <> more : List<&2, Ops.Op>}
          %Equal.sym(Nat, here, at, add_sub(pos, at, and_left(Nat.is_le(pos, at), Block.ordered(tail, Nat.add(at, n)), e))) : {Ops.Op{Ops.Delete{}, _, items} <> Ops.script(Block.steps_of(tail, Nat.add(at, n)), Nat.add(_, n)) == Ops.Op{Ops.Delete{}, at, items} <> tail : List<&2, Ops.Op>}
          %Equal.sym(List<&2, Ops.Op>, Ops.script(Block.steps_of(tail, Nat.add(at, n)), Nat.add(at, n)), tail, is_script(tail, Nat.add(at, n), and_right(Nat.is_le(pos, at), Block.ordered(tail, Nat.add(at, n)), e))) : {Ops.Op{Ops.Delete{}, at, items} <> _ == Ops.Op{Ops.Delete{}, at, items} <> tail : List<&2, Ops.Op>}
          {==}

def main() -> Unit:
  Unit{}
