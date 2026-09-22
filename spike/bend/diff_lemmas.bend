# The diff replays: `Ops.apply(parent, doc) == Done{child}` whenever
# `Ops.diff(parent, child) == Some{doc}`. The backtrack over the LCS table
# yields an edit script that takes the parent to the child — its verdicts
# only need to be consistent with the items they name, not optimal — and
# the runs of that script are blocks the cursor walks to the child.
import Base
import ./ops.bend as Ops
import ./text.bend as T
import ./replay_spec.bend as Spec
import ./cursor_spec.bend as Cursor
import ./semantic_replay.bend as Block
import ./composition_lemmas.bend as Comp
import ./position_lemmas.bend as Pos
import ./replay_lemmas.bend as L
import ./equality_lemmas.bend as Eq
import ./decimal_lemmas.bend as Dec
import ./parser_lemmas.bend as Parse

# Agreement is reflexive
# ----------------------

def word_cmp_refl.fin(b: Bool, c: Cmp, e: {c == EQ{} : Cmp}) -> {Word.cmp.fin(b, b, c) == EQ{} : Cmp}:
  match b:
    case False{}:
      %Equal.sym(Cmp, c, EQ{}, e) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
      {==}
    case True{}:
      %Equal.sym(Cmp, c, EQ{}, e) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
      {==}

def word_cmp_refl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n++p:
      match w:
        case WCon{b, +t}:
          word_cmp_refl.fin(b, Word.cmp(p, t, t), word_cmp_refl(p, t))

def char_eq_refl(c: Char) -> {Char.is_eq(c, c) == True{} : Bool}:
  match c:
    case Chr{x}:
      match x:
        case U32{+w}:
          %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, word_cmp_refl(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
          {==}

def same_refl(s: String) -> {T.same(s, s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym(Bool, Char.is_eq(h, h), True{}, char_eq_refl(h)) : {Bool.and(_, T.same(t, t)) == True{} : Bool}
      same_refl(t)

def agrees_refl(x: Ops.Item) -> {Ops.agrees(x, x) == True{} : Bool}:
  match x:
    case Ops.Item{+t, n, f}:
      match n f:
        case False{} False{}:
          same_refl(t)
        case False{} True{}:
          {==}
        case True{} False{}:
          same_refl(t)
        case True{} True{}:
          {==}

# Two items the diff calls the same are equal.
def same_items(a: Ops.Item, b: Ops.Item, e: {Ops.same(a, b) == True{} : Bool}) -> {a == b : Ops.Item}:
  match a b:
    case Ops.Item{t1, n1, True{}} Ops.Item{t2, n2, f2}:
      Empty.absurd({Ops.Item{t1, n1, True{}} == Ops.Item{t2, n2, f2} : Ops.Item}, Comp.false_true(e))
    case Ops.Item{t1, n1, False{}} Ops.Item{t2, n2, True{}}:
      Empty.absurd({Ops.Item{t1, n1, False{}} == Ops.Item{t2, n2, True{}} : Ops.Item}, Comp.false_true(e))
    case Ops.Item{+t1, False{}, False{}} Ops.Item{+t2, False{}, False{}}:
      %Equal.sym(String, t1, t2, Eq.same_eq(t1, t2, Comp.and_left(T.same(t1, t2), True{}, e))) : {Ops.Item{_, False{}, False{}} == Ops.Item{t2, False{}, False{}} : Ops.Item}
      {==}
    case Ops.Item{+t1, True{}, False{}} Ops.Item{+t2, True{}, False{}}:
      %Equal.sym(String, t1, t2, Eq.same_eq(t1, t2, Comp.and_left(T.same(t1, t2), True{}, e))) : {Ops.Item{_, True{}, False{}} == Ops.Item{t2, True{}, False{}} : Ops.Item}
      {==}
    case Ops.Item{+t1, False{}, False{}} Ops.Item{+t2, True{}, False{}}:
      Empty.absurd({Ops.Item{t1, False{}, False{}} == Ops.Item{t2, True{}, False{}} : Ops.Item}, Comp.false_true(Comp.and_right(T.same(t1, t2), False{}, e)))
    case Ops.Item{+t1, True{}, False{}} Ops.Item{+t2, False{}, False{}}:
      Empty.absurd({Ops.Item{t1, True{}, False{}} == Ops.Item{t2, False{}, False{}} : Ops.Item}, Comp.false_true(Comp.and_right(T.same(t1, t2), False{}, e)))

def agrees_matches(a: Ops.Item, b: Ops.Item) -> {Ops.agrees(a, b) == Spec.matches(a, b) : Bool}:
  match a b:
    case Ops.Item{a, False{}, f} Ops.Item{b, True{}, g}:
      {==}
    case Ops.Item{a, True{}, f} Ops.Item{b, False{}, g}:
      {==}
    case Ops.Item{a, False{}, True{}} Ops.Item{b, False{}, g}:
      {==}
    case Ops.Item{a, True{}, True{}} Ops.Item{b, True{}, g}:
      {==}
    case Ops.Item{a, False{}, False{}} Ops.Item{b, False{}, True{}}:
      {==}
    case Ops.Item{a, True{}, False{}} Ops.Item{b, True{}, True{}}:
      {==}
    case Ops.Item{a, False{}, False{}} Ops.Item{b, False{}, False{}}:
      {==}
    case Ops.Item{a, True{}, False{}} Ops.Item{b, True{}, False{}}:
      {==}

# Edit scripts
# ------------

def map_cons(x: Ops.Item, r: Maybe<&2, List<&2, Ops.Item>>) -> Maybe<&2, List<&2, Ops.Item>>:
  match r:
    case None{}:
      None{}
    case Some{xs}:
      Some{x <> xs}

# What an edit script does to a state: a kept line is copied, a deleted
# line must agree with the line it deletes, an inserted line is added.
def edits_apply(es: List<&2, Ops.Move>, old: List<&2, Ops.Item>) -> Maybe<&2, List<&2, Ops.Item>>:
  match es old:
    case Nil{} Nil{}:
      Some{Nil{}}
    case Nil{} x <> xs:
      None{}
    case Ops.Keep{} <> r Nil{}:
      None{}
    case Ops.Keep{} <> r +x <> xs:
      map_cons(x, edits_apply(r, xs))
    case Ops.Del{d} <> r Nil{}:
      None{}
    case Ops.Del{d} <> r y <> ys:
      Bool.pick(Maybe<&2, List<&2, Ops.Item>>, Ops.agrees(d, y), edits_apply(r, ys), None{})
    case Ops.Ins{y} <> r old:
      map_cons(y, edits_apply(r, old))

def mdisc(m: Maybe<&2, List<&2, Ops.Item>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some(-x: List<&2, Ops.Item>, e: {None{} == Some{x} : Maybe<&2, List<&2, Ops.Item>>}) -> Empty:
  %e : {mdisc(_) : Type}
  Unit{}

def maybe_items(m: Maybe<&2, List<&2, Ops.Item>>) -> List<&2, Ops.Item>:
  match m:
    case None{}:
      Nil{}
    case Some{x}:
      x

def some_inj(-x: List<&2, Ops.Item>, -y: List<&2, Ops.Item>, e: {Some{x} == Some{y} : Maybe<&2, List<&2, Ops.Item>>}) -> {x == y : List<&2, Ops.Item>}:
  Equal.cong(Maybe<&2, List<&2, Ops.Item>>, List<&2, Ops.Item>, maybe_items, Some{x}, Some{y}, e)

# Positions
# ---------

def add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+b), 1n+Nat.add(p, b), add_succ(p, b)) : {1n+_ == 1n+1n+Nat.add(p, b) : Nat}
      {==}

# An index within a list splits it at the item there.
def drop_cons(xs: List<&2, Ops.Item>, p: Nat, lt: {Nat.is_lt(p, List.length(&2, Ops.Item, xs)) == True{} : Bool}) -> {List.drop(&2, Ops.Item, xs, p) == Ops.item_at(xs, p) <> List.drop(&2, Ops.Item, xs, 1n+p) : List<&2, Ops.Item>}:
  match xs p:
    case Nil{} 0n:
      Empty.absurd({Nil{} == Ops.forgotten() <> Nil{} : List<&2, Ops.Item>}, Comp.false_true(lt))
    case Nil{} 1n+q:
      Empty.absurd({Nil{} == Ops.forgotten() <> Nil{} : List<&2, Ops.Item>}, Comp.false_true(lt))
    case h <> +t 0n:
      %Equal.sym(List<&2, Ops.Item>, List.drop(&2, Ops.Item, t, 0n), t, Pos.drop_zero(t)) : {h <> t == h <> _ : List<&2, Ops.Item>}
      {==}
    case h <> t 1n+q:
      drop_cons(t, q, lt)

def drop_all(xs: List<&2, Ops.Item>) -> {List.drop(&2, Ops.Item, xs, List.length(&2, Ops.Item, xs)) == Nil{} : List<&2, Ops.Item>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      drop_all(t)

# The backtrack
# -------------


# A kept line: the item at both indices, which the diff found the same.
def back.keep(+p: Nat, +q: Nat, +old: List<&2, Ops.Item>, +new: List<&2, Ops.Item>, +sc: List<&2, Ops.Move>, em: {Ops.same(Ops.item_at(old, p), Ops.item_at(new, q)) == True{} : Bool}, ltp: {Nat.is_lt(p, List.length(&2, Ops.Item, old)) == True{} : Bool}, ltq: {Nat.is_lt(q, List.length(&2, Ops.Item, new)) == True{} : Bool}, h: {edits_apply(sc, List.drop(&2, Ops.Item, old, 1n+p)) == Some{List.drop(&2, Ops.Item, new, 1n+q)} : Maybe<&2, List<&2, Ops.Item>>}) -> {edits_apply(Ops.Keep{} <> sc, List.drop(&2, Ops.Item, old, p)) == Some{List.drop(&2, Ops.Item, new, q)} : Maybe<&2, List<&2, Ops.Item>>}:
  %Equal.sym(List<&2, Ops.Item>, List.drop(&2, Ops.Item, old, p), Ops.item_at(old, p) <> List.drop(&2, Ops.Item, old, 1n+p), drop_cons(old, p, ltp)) : {edits_apply(Ops.Keep{} <> sc, _) == Some{List.drop(&2, Ops.Item, new, q)} : Maybe<&2, List<&2, Ops.Item>>}
  %Equal.sym(List<&2, Ops.Item>, List.drop(&2, Ops.Item, new, q), Ops.item_at(new, q) <> List.drop(&2, Ops.Item, new, 1n+q), drop_cons(new, q, ltq)) : {map_cons(Ops.item_at(old, p), edits_apply(sc, List.drop(&2, Ops.Item, old, 1n+p))) == Some{_} : Maybe<&2, List<&2, Ops.Item>>}
  %Equal.sym(Maybe<&2, List<&2, Ops.Item>>, edits_apply(sc, List.drop(&2, Ops.Item, old, 1n+p)), Some{List.drop(&2, Ops.Item, new, 1n+q)}, h) : {map_cons(Ops.item_at(old, p), _) == Some{Ops.item_at(new, q) <> List.drop(&2, Ops.Item, new, 1n+q)} : Maybe<&2, List<&2, Ops.Item>>}
  %Equal.sym(Ops.Item, Ops.item_at(old, p), Ops.item_at(new, q), same_items(Ops.item_at(old, p), Ops.item_at(new, q), em)) : {Some{_ <> List.drop(&2, Ops.Item, new, 1n+q)} == Some{Ops.item_at(new, q) <> List.drop(&2, Ops.Item, new, 1n+q)} : Maybe<&2, List<&2, Ops.Item>>}
  {==}

# A deleted line: the parent's own item, which agrees with itself.
def back.del(+p: Nat, +j: Nat, +old: List<&2, Ops.Item>, +new: List<&2, Ops.Item>, +sc: List<&2, Ops.Move>, ltp: {Nat.is_lt(p, List.length(&2, Ops.Item, old)) == True{} : Bool}, h: {edits_apply(sc, List.drop(&2, Ops.Item, old, 1n+p)) == Some{List.drop(&2, Ops.Item, new, j)} : Maybe<&2, List<&2, Ops.Item>>}) -> {edits_apply(Ops.Del{Ops.item_at(old, p)} <> sc, List.drop(&2, Ops.Item, old, p)) == Some{List.drop(&2, Ops.Item, new, j)} : Maybe<&2, List<&2, Ops.Item>>}:
  %Equal.sym(List<&2, Ops.Item>, List.drop(&2, Ops.Item, old, p), Ops.item_at(old, p) <> List.drop(&2, Ops.Item, old, 1n+p), drop_cons(old, p, ltp)) : {edits_apply(Ops.Del{Ops.item_at(old, p)} <> sc, _) == Some{List.drop(&2, Ops.Item, new, j)} : Maybe<&2, List<&2, Ops.Item>>}
  %Equal.sym(Bool, Ops.agrees(Ops.item_at(old, p), Ops.item_at(old, p)), True{}, agrees_refl(Ops.item_at(old, p))) : {Bool.pick(Maybe<&2, List<&2, Ops.Item>>, _, edits_apply(sc, List.drop(&2, Ops.Item, old, 1n+p)), None{}) == Some{List.drop(&2, Ops.Item, new, j)} : Maybe<&2, List<&2, Ops.Item>>}
  h

# An inserted line: the child's own item.
def back.ins(+i: Nat, +q: Nat, +old: List<&2, Ops.Item>, +new: List<&2, Ops.Item>, +sc: List<&2, Ops.Move>, ltq: {Nat.is_lt(q, List.length(&2, Ops.Item, new)) == True{} : Bool}, h: {edits_apply(sc, List.drop(&2, Ops.Item, old, i)) == Some{List.drop(&2, Ops.Item, new, 1n+q)} : Maybe<&2, List<&2, Ops.Item>>}) -> {edits_apply(Ops.Ins{Ops.item_at(new, q)} <> sc, List.drop(&2, Ops.Item, old, i)) == Some{List.drop(&2, Ops.Item, new, q)} : Maybe<&2, List<&2, Ops.Item>>}:
  %Equal.sym(List<&2, Ops.Item>, List.drop(&2, Ops.Item, new, q), Ops.item_at(new, q) <> List.drop(&2, Ops.Item, new, 1n+q), drop_cons(new, q, ltq)) : {map_cons(Ops.item_at(new, q), edits_apply(sc, List.drop(&2, Ops.Item, old, i))) == Some{_} : Maybe<&2, List<&2, Ops.Item>>}
  %Equal.sym(Maybe<&2, List<&2, Ops.Item>>, edits_apply(sc, List.drop(&2, Ops.Item, old, i)), Some{List.drop(&2, Ops.Item, new, 1n+q)}, h) : {map_cons(Ops.item_at(new, q), _) == Some{Ops.item_at(new, q) <> List.drop(&2, Ops.Item, new, 1n+q)} : Maybe<&2, List<&2, Ops.Item>>}
  {==}

# The verdict at (1+p, 1+q), decided: each way the walk goes, the script
# it builds still takes the parent to the child.
def back.of(f: Nat, +p: Nat, +q: Nat, +old: List<&2, Ops.Item>, +new: List<&2, Ops.Item>, +tbl: List<&2, List<&2, U32>>, +sc: List<&2, Ops.Move>, m: Bool, u: Bool, +em: {Ops.same(Ops.item_at(old, p), Ops.item_at(new, q)) == m : Bool}, +ltp: {Nat.is_lt(p, List.length(&2, Ops.Item, old)) == True{} : Bool}, +ltq: {Nat.is_lt(q, List.length(&2, Ops.Item, new)) == True{} : Bool}, +h: {edits_apply(sc, List.drop(&2, Ops.Item, old, 1n+p)) == Some{List.drop(&2, Ops.Item, new, 1n+q)} : Maybe<&2, List<&2, Ops.Item>>}, ih_diag: @+sc2: List<&2, Ops.Move> -> {edits_apply(sc2, List.drop(&2, Ops.Item, old, p)) == Some{List.drop(&2, Ops.Item, new, q)} : Maybe<&2, List<&2, Ops.Item>>} -> {edits_apply(Ops.backtrack(f, Ops.step(old, new, tbl, p, q), p, q, old, new, tbl, sc2), old) == Some{new} : Maybe<&2, List<&2, Ops.Item>>}, ih_up: @+sc2: List<&2, Ops.Move> -> {edits_apply(sc2, List.drop(&2, Ops.Item, old, p)) == Some{List.drop(&2, Ops.Item, new, 1n+q)} : Maybe<&2, List<&2, Ops.Item>>} -> {edits_apply(Ops.backtrack(f, Ops.step(old, new, tbl, p, 1n+q), p, 1n+q, old, new, tbl, sc2), old) == Some{new} : Maybe<&2, List<&2, Ops.Item>>}, ih_left: @+sc2: List<&2, Ops.Move> -> {edits_apply(sc2, List.drop(&2, Ops.Item, old, 1n+p)) == Some{List.drop(&2, Ops.Item, new, q)} : Maybe<&2, List<&2, Ops.Item>>} -> {edits_apply(Ops.backtrack(f, Ops.step(old, new, tbl, 1n+p, q), 1n+p, q, old, new, tbl, sc2), old) == Some{new} : Maybe<&2, List<&2, Ops.Item>>}) -> {edits_apply(Ops.backtrack(1n+f, Ops.step.of(m, u), 1n+p, 1n+q, old, new, tbl, sc), old) == Some{new} : Maybe<&2, List<&2, Ops.Item>>}:
  match m:
    case True{}:
      +sc2 = {Ops.Keep{} <> sc : List<&2, Ops.Move>}
      %Equal.sym(Nat, Nat.sub(p, 0n), p, Pos.sub_zero(p)) : {edits_apply(Ops.backtrack(f, Ops.step(old, new, tbl, _, Nat.sub(q, 0n)), _, Nat.sub(q, 0n), old, new, tbl, sc2), old) == Some{new} : Maybe<&2, List<&2, Ops.Item>>}
      %Equal.sym(Nat, Nat.sub(q, 0n), q, Pos.sub_zero(q)) : {edits_apply(Ops.backtrack(f, Ops.step(old, new, tbl, p, _), p, _, old, new, tbl, sc2), old) == Some{new} : Maybe<&2, List<&2, Ops.Item>>}
      ih_diag(sc2, back.keep(p, q, old, new, sc, em, ltp, ltq, h))
    case False{}:
      match u:
        case True{}:
          %Equal.sym(Nat, Nat.sub(p, 0n), p, Pos.sub_zero(p)) : {edits_apply(Ops.backtrack(f, Ops.step(old, new, tbl, _, 1n+q), _, 1n+q, old, new, tbl, Ops.Del{Ops.item_at(old, _)} <> sc), old) == Some{new} : Maybe<&2, List<&2, Ops.Item>>}
          ih_up(Ops.Del{Ops.item_at(old, p)} <> sc, back.del(p, 1n+q, old, new, sc, ltp, h))
        case False{}:
          %Equal.sym(Nat, Nat.sub(q, 0n), q, Pos.sub_zero(q)) : {edits_apply(Ops.backtrack(f, Ops.step(old, new, tbl, 1n+p, _), 1n+p, _, old, new, tbl, Ops.Ins{Ops.item_at(new, _)} <> sc), old) == Some{new} : Maybe<&2, List<&2, Ops.Item>>}
          ih_left(Ops.Ins{Ops.item_at(new, q)} <> sc, back.ins(1n+p, q, old, new, sc, ltq, h))

def le_cast(-a: Nat, -b: Nat, -f: Nat, eq: {a == b : Nat}, e: {Nat.is_le(a, f) == True{} : Bool}) -> {Nat.is_le(b, f) == True{} : Bool}:
  %eq : {Nat.is_le(_, f) == True{} : Bool}
  e

def fits_diag(+p: Nat, +q: Nat, f: Nat, e: {Nat.is_le(Nat.add(1n+p, 1n+q), 1n+f) == True{} : Bool}) -> {Nat.is_le(Nat.add(p, q), f) == True{} : Bool}:
  Comp.le_pred(Nat.add(p, q), f, le_cast(Nat.add(p, 1n+q), 1n+Nat.add(p, q), f, add_succ(p, q), e))

def fits_left(+p: Nat, +q: Nat, f: Nat, e: {Nat.is_le(Nat.add(1n+p, 1n+q), 1n+f) == True{} : Bool}) -> {Nat.is_le(Nat.add(1n+p, q), f) == True{} : Bool}:
  le_cast(Nat.add(p, 1n+q), 1n+Nat.add(p, q), f, add_succ(p, q), e)

# With fuel for every step, the backtrack from (i, j) prepends to `sc` a
# script from the first i parent items to the first j child items.
def back(fuel: Nat, i: Nat, j: Nat, +old: List<&2, Ops.Item>, +new: List<&2, Ops.Item>, +tbl: List<&2, List<&2, U32>>, +sc: List<&2, Ops.Move>, +fits: {Nat.is_le(Nat.add(i, j), fuel) == True{} : Bool}, +li: {Nat.is_le(i, List.length(&2, Ops.Item, old)) == True{} : Bool}, +lj: {Nat.is_le(j, List.length(&2, Ops.Item, new)) == True{} : Bool}, +h: {edits_apply(sc, List.drop(&2, Ops.Item, old, i)) == Some{List.drop(&2, Ops.Item, new, j)} : Maybe<&2, List<&2, Ops.Item>>}) -> {edits_apply(Ops.backtrack(fuel, Ops.step(old, new, tbl, i, j), i, j, old, new, tbl, sc), old) == Some{new} : Maybe<&2, List<&2, Ops.Item>>}:
  match fuel i j:
    case 0n 0n 0n:
      %Pos.drop_zero(old) : {edits_apply(sc, _) == Some{new} : Maybe<&2, List<&2, Ops.Item>>}
      %Pos.drop_zero(new) : {edits_apply(sc, List.drop(&2, Ops.Item, old, 0n)) == Some{_} : Maybe<&2, List<&2, Ops.Item>>}
      h
    case 0n 0n 1n+q:
      Empty.absurd({edits_apply(Ops.backtrack(0n, Ops.step(old, new, tbl, 0n, 1n+q), 0n, 1n+q, old, new, tbl, sc), old) == Some{new} : Maybe<&2, List<&2, Ops.Item>>}, Comp.false_true(fits))
    case 0n 1n+p j:
      Empty.absurd({edits_apply(Ops.backtrack(0n, Ops.step(old, new, tbl, 1n+p, j), 1n+p, j, old, new, tbl, sc), old) == Some{new} : Maybe<&2, List<&2, Ops.Item>>}, Comp.false_true(fits))
    case 1n+f 0n 0n:
      %Pos.drop_zero(old) : {edits_apply(sc, _) == Some{new} : Maybe<&2, List<&2, Ops.Item>>}
      %Pos.drop_zero(new) : {edits_apply(sc, List.drop(&2, Ops.Item, old, 0n)) == Some{_} : Maybe<&2, List<&2, Ops.Item>>}
      h
    case 1n++f 0n 1n++q:
      %Equal.sym(Nat, Nat.sub(q, 0n), q, Pos.sub_zero(q)) : {edits_apply(Ops.backtrack(f, Ops.step(old, new, tbl, 0n, _), 0n, _, old, new, tbl, Ops.Ins{Ops.item_at(new, _)} <> sc), old) == Some{new} : Maybe<&2, List<&2, Ops.Item>>}
      back(f, 0n, q, old, new, tbl, Ops.Ins{Ops.item_at(new, q)} <> sc, fits, li, Comp.le_pred(q, List.length(&2, Ops.Item, new), lj), back.ins(0n, q, old, new, sc, Dec.lt_of_le_succ(q, List.length(&2, Ops.Item, new), lj), h))
    case 1n++f 1n++p 0n:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, Pos.sub_zero(p)) : {edits_apply(Ops.backtrack(f, Ops.step(old, new, tbl, _, 0n), _, 0n, old, new, tbl, Ops.Del{Ops.item_at(old, _)} <> sc), old) == Some{new} : Maybe<&2, List<&2, Ops.Item>>}
      back(f, p, 0n, old, new, tbl, Ops.Del{Ops.item_at(old, p)} <> sc, fits, Comp.le_pred(p, List.length(&2, Ops.Item, old), li), lj, back.del(p, 0n, old, new, sc, Dec.lt_of_le_succ(p, List.length(&2, Ops.Item, old), li), h))
    case 1n++f 1n++p 1n++q:
      +n = List.length(&2, Ops.Item, old)
      +m = List.length(&2, Ops.Item, new)
      back.of(f, p, q, old, new, tbl, sc, Ops.same(Ops.item_at(old, p), Ops.item_at(new, q)), U32.is_ge(Ops.cell(tbl, p, 1n+q), Ops.cell(tbl, 1n+p, q)), {==}, Dec.lt_of_le_succ(p, n, li), Dec.lt_of_le_succ(q, m, lj), h,
        sc2 => h2 => back(f, p, q, old, new, tbl, sc2, fits_diag(p, q, f, fits), Comp.le_pred(p, n, li), Comp.le_pred(q, m, lj), h2),
        sc2 => h2 => back(f, p, 1n+q, old, new, tbl, sc2, fits, Comp.le_pred(p, n, li), lj, h2),
        sc2 => h2 => back(f, 1n+p, q, old, new, tbl, sc2, fits_left(p, q, f, fits), li, Comp.le_pred(q, m, lj), h2))

# The diff's script takes the parent to the child.
def edits_ok.base(old: List<&2, Ops.Item>, new: List<&2, Ops.Item>) -> {edits_apply(Nil{}, List.drop(&2, Ops.Item, old, List.length(&2, Ops.Item, old))) == Some{List.drop(&2, Ops.Item, new, List.length(&2, Ops.Item, new))} : Maybe<&2, List<&2, Ops.Item>>}:
  %Equal.sym(List<&2, Ops.Item>, List.drop(&2, Ops.Item, old, List.length(&2, Ops.Item, old)), Nil{}, drop_all(old)) : {edits_apply(Nil{}, _) == Some{List.drop(&2, Ops.Item, new, List.length(&2, Ops.Item, new))} : Maybe<&2, List<&2, Ops.Item>>}
  %Equal.sym(List<&2, Ops.Item>, List.drop(&2, Ops.Item, new, List.length(&2, Ops.Item, new)), Nil{}, drop_all(new)) : {edits_apply(Nil{}, Nil{}) == Some{_} : Maybe<&2, List<&2, Ops.Item>>}
  {==}

def edits_ok(+old: List<&2, Ops.Item>, +new: List<&2, Ops.Item>) -> {edits_apply(Ops.edits(old, new), old) == Some{new} : Maybe<&2, List<&2, Ops.Item>>}:
  +n = List.length(&2, Ops.Item, old)
  +m = List.length(&2, Ops.Item, new)
  back(Nat.add(n, m), n, m, old, new, Ops.table(old, new), Nil{}, Comp.le_refl(Nat.add(n, m)), Comp.le_refl(n), Comp.le_refl(m), edits_ok.base(old, new))

# Runs of edits as blocks
# -----------------------

def map_app(front: List<&2, Ops.Item>, r: Maybe<&2, List<&2, Ops.Item>>) -> Maybe<&2, List<&2, Ops.Item>>:
  match r:
    case None{}:
      None{}
    case Some{xs}:
      Some{List.append(&2, Ops.Item, front, xs)}

# What a script of blocks does to a state: each block a stated gap on,
# quoting what is there, replacing it with what it inserts.
def steps_apply(steps: List<&2, Ops.Step>, +state: List<&2, Ops.Item>) -> Maybe<&2, List<&2, Ops.Item>>:
  match steps:
    case Nil{}:
      Some{state}
    case Ops.Step{+gap, +edit} <> rest:
      +after = List.drop(&2, Ops.Item, state, gap)
      Bool.pick(Maybe<&2, List<&2, Ops.Item>>, Bool.and(Nat.is_le(gap, List.length(&2, Ops.Item, state)), Block.agrees(edit, after)),
        map_app(List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, gap), Ops.inserted(edit)), steps_apply(rest, List.drop(&2, Ops.Item, after, Ops.consumed(edit)))),
        None{})

# Recorded lines against the lines they were recorded from, one to one.
def agree(recorded: List<&2, Ops.Item>, actual: List<&2, Ops.Item>) -> Bool:
  match recorded actual:
    case Nil{} Nil{}:
      True{}
    case r <> rs a <> as:
      Bool.and(Ops.agrees(r, a), agree(rs, as))
    case _ _:
      False{}

def agree_nil(actual: List<&2, Ops.Item>, e: {agree(Nil{}, actual) == True{} : Bool}) -> {actual == Nil{} : List<&2, Ops.Item>}:
  match actual:
    case Nil{}:
      {==}
    case a <> as:
      Empty.absurd({a <> as == Nil{} : List<&2, Ops.Item>}, Comp.false_true(e))

def agree_len(recorded: List<&2, Ops.Item>, actual: List<&2, Ops.Item>, e: {agree(recorded, actual) == True{} : Bool}) -> {List.length(&2, Ops.Item, recorded) == List.length(&2, Ops.Item, actual) : Nat}:
  match recorded actual:
    case Nil{} Nil{}:
      {==}
    case Nil{} a <> as:
      Empty.absurd({0n == 1n+List.length(&2, Ops.Item, as) : Nat}, Comp.false_true(e))
    case r <> rs Nil{}:
      Empty.absurd({1n+List.length(&2, Ops.Item, rs) == 0n : Nat}, Comp.false_true(e))
    case r <> rs a <> as:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Ops.Item, rs), List.length(&2, Ops.Item, as), agree_len(rs, as, Comp.and_right(Ops.agrees(r, a), agree(rs, as), e)))

def agree_snoc(recorded: List<&2, Ops.Item>, actual: List<&2, Ops.Item>, +d: Ops.Item, +y: Ops.Item, +e: {agree(recorded, actual) == True{} : Bool}, +dy: {Ops.agrees(d, y) == True{} : Bool}) -> {agree(List.append(&2, Ops.Item, recorded, [d]), List.append(&2, Ops.Item, actual, [y])) == True{} : Bool}:
  match recorded actual:
    case Nil{} Nil{}:
      %Equal.sym(Bool, Ops.agrees(d, y), True{}, dy) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case Nil{} a <> as:
      Empty.absurd({agree([d], List.append(&2, Ops.Item, a <> as, [y])) == True{} : Bool}, Comp.false_true(e))
    case r <> rs Nil{}:
      Empty.absurd({agree(List.append(&2, Ops.Item, r <> rs, [d]), [y]) == True{} : Bool}, Comp.false_true(e))
    case +r <> +rs +a <> +as:
      Parse.and_intro(Ops.agrees(r, a), agree(List.append(&2, Ops.Item, rs, [d]), List.append(&2, Ops.Item, as, [y])), Comp.and_left(Ops.agrees(r, a), agree(rs, as), e), agree_snoc(rs, as, d, y, Comp.and_right(Ops.agrees(r, a), agree(rs, as), e), dy))

# Recorded lines that agree with the lines in front of a state match there.
def prefix_of_agree(recorded: List<&2, Ops.Item>, actual: List<&2, Ops.Item>, +s: List<&2, Ops.Item>, +e: {agree(recorded, actual) == True{} : Bool}) -> {Spec.prefix_matches(recorded, List.append(&2, Ops.Item, actual, s)) == True{} : Bool}:
  match recorded actual:
    case Nil{} Nil{}:
      {==}
    case Nil{} a <> as:
      {==}
    case r <> rs Nil{}:
      Empty.absurd({Spec.prefix_matches(r <> rs, s) == True{} : Bool}, Comp.false_true(e))
    case +r <> +rs +a <> +as:
      %agrees_matches(r, a) : {Bool.and(_, Spec.prefix_matches(rs, List.append(&2, Ops.Item, as, s))) == True{} : Bool}
      Parse.and_intro(Ops.agrees(r, a), Spec.prefix_matches(rs, List.append(&2, Ops.Item, as, s)), Comp.and_left(Ops.agrees(r, a), agree(rs, as), e), prefix_of_agree(rs, as, s, Comp.and_right(Ops.agrees(r, a), agree(rs, as), e)))

def consumed_block(dels: List<&2, Ops.Item>, ins: List<&2, Ops.Item>) -> {Ops.consumed(Ops.block(dels, ins)) == List.length(&2, Ops.Item, dels) : Nat}:
  match dels ins:
    case Nil{} ins:
      {==}
    case d <> ds Nil{}:
      {==}
    case d <> ds i <> it:
      {==}

def inserted_block(dels: List<&2, Ops.Item>, ins: List<&2, Ops.Item>) -> {Ops.inserted(Ops.block(dels, ins)) == ins : List<&2, Ops.Item>}:
  match dels ins:
    case Nil{} ins:
      {==}
    case d <> ds Nil{}:
      {==}
    case d <> ds i <> it:
      {==}

def block_agrees(dels: List<&2, Ops.Item>, ins: List<&2, Ops.Item>, +after: List<&2, Ops.Item>, pm: {Spec.prefix_matches(dels, after) == True{} : Bool}) -> {Block.agrees(Ops.block(dels, ins), after) == True{} : Bool}:
  match dels ins:
    case Nil{} ins:
      {==}
    case d <> ds Nil{}:
      pm
    case d <> ds i <> it:
      pm

def len_append(xs: List<&2, Ops.Item>, -ys: List<&2, Ops.Item>) -> {List.length(&2, Ops.Item, List.append(&2, Ops.Item, xs, ys)) == Nat.add(List.length(&2, Ops.Item, xs), List.length(&2, Ops.Item, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Equal.sym(Nat, List.length(&2, Ops.Item, List.append(&2, Ops.Item, t, ys)), Nat.add(List.length(&2, Ops.Item, t), List.length(&2, Ops.Item, ys)), len_append(t, ys)) : {1n+_ == 1n+Nat.add(List.length(&2, Ops.Item, t), List.length(&2, Ops.Item, ys)) : Nat}
      {==}

def snoc_app(xs: List<&2, Ops.Item>, -x: Ops.Item, -ys: List<&2, Ops.Item>) -> {List.append(&2, Ops.Item, List.append(&2, Ops.Item, xs, [x]), ys) == List.append(&2, Ops.Item, xs, x <> ys) : List<&2, Ops.Item>}:
  L.append_assoc(xs, [x], ys)

def len_snoc(+xs: List<&2, Ops.Item>, -x: Ops.Item) -> {List.length(&2, Ops.Item, List.append(&2, Ops.Item, xs, [x])) == 1n+List.length(&2, Ops.Item, xs) : Nat}:
  %Equal.sym(Nat, List.length(&2, Ops.Item, List.append(&2, Ops.Item, xs, [x])), Nat.add(List.length(&2, Ops.Item, xs), 1n), len_append(xs, [x])) : {_ == 1n+List.length(&2, Ops.Item, xs) : Nat}
  %Equal.sym(Nat, Nat.add(List.length(&2, Ops.Item, xs), 1n+0n), 1n+Nat.add(List.length(&2, Ops.Item, xs), 0n), add_succ(List.length(&2, Ops.Item, xs), 0n)) : {_ == 1n+List.length(&2, Ops.Item, xs) : Nat}
  %Equal.sym(Nat, Nat.add(List.length(&2, Ops.Item, xs), 0n), List.length(&2, Ops.Item, xs), Comp.add_zero(List.length(&2, Ops.Item, xs))) : {1n+_ == 1n+List.length(&2, Ops.Item, xs) : Nat}
  {==}

# One block, applied where its run began: the kept lines stay, the deleted
# lines agree with the lines they quote, the inserted lines take their place.
def block_apply.fits(+kept: List<&2, Ops.Item>, +rest: List<&2, Ops.Item>) -> {Nat.is_le(List.length(&2, Ops.Item, kept), List.length(&2, Ops.Item, List.append(&2, Ops.Item, kept, rest))) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Ops.Item, List.append(&2, Ops.Item, kept, rest)), Nat.add(List.length(&2, Ops.Item, kept), List.length(&2, Ops.Item, rest)), len_append(kept, rest)) : {Nat.is_le(List.length(&2, Ops.Item, kept), _) == True{} : Bool}
  Comp.le_add(List.length(&2, Ops.Item, kept), List.length(&2, Ops.Item, kept), List.length(&2, Ops.Item, rest), Comp.le_refl(List.length(&2, Ops.Item, kept)))

def block_apply(+gap: Nat, +dr: List<&2, Ops.Item>, +ir: List<&2, Ops.Item>, +kept: List<&2, Ops.Item>, +taken: List<&2, Ops.Item>, +s: List<&2, Ops.Item>, +more: List<&2, Ops.Step>, +out: List<&2, Ops.Item>, lk: {List.length(&2, Ops.Item, kept) == gap : Nat}, +ag: {agree(dr, taken) == True{} : Bool}, ih: {steps_apply(more, s) == Some{out} : Maybe<&2, List<&2, Ops.Item>>}) -> {steps_apply(Ops.Step{gap, Ops.block(dr, ir)} <> more, List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, taken, s))) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, ir, out))} : Maybe<&2, List<&2, Ops.Item>>}:
  +rest = List.append(&2, Ops.Item, taken, s)
  +whole = List.append(&2, Ops.Item, kept, rest)
  %lk : {steps_apply(Ops.Step{_, Ops.block(dr, ir)} <> more, whole) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, ir, out))} : Maybe<&2, List<&2, Ops.Item>>}
  %Equal.sym(List<&2, Ops.Item>, List.drop(&2, Ops.Item, whole, List.length(&2, Ops.Item, kept)), rest, Pos.drop_prefix(kept, rest)) : {Bool.pick(Maybe<&2, List<&2, Ops.Item>>, Bool.and(Nat.is_le(List.length(&2, Ops.Item, kept), List.length(&2, Ops.Item, whole)), Block.agrees(Ops.block(dr, ir), _)), map_app(List.append(&2, Ops.Item, List.take(&2, Ops.Item, whole, List.length(&2, Ops.Item, kept)), Ops.inserted(Ops.block(dr, ir))), steps_apply(more, List.drop(&2, Ops.Item, _, Ops.consumed(Ops.block(dr, ir))))), None{}) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, ir, out))} : Maybe<&2, List<&2, Ops.Item>>}
  %Equal.sym(List<&2, Ops.Item>, List.take(&2, Ops.Item, whole, List.length(&2, Ops.Item, kept)), kept, Pos.take_prefix(kept, rest)) : {Bool.pick(Maybe<&2, List<&2, Ops.Item>>, Bool.and(Nat.is_le(List.length(&2, Ops.Item, kept), List.length(&2, Ops.Item, whole)), Block.agrees(Ops.block(dr, ir), rest)), map_app(List.append(&2, Ops.Item, _, Ops.inserted(Ops.block(dr, ir))), steps_apply(more, List.drop(&2, Ops.Item, rest, Ops.consumed(Ops.block(dr, ir))))), None{}) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, ir, out))} : Maybe<&2, List<&2, Ops.Item>>}
  %Equal.sym(Bool, Nat.is_le(List.length(&2, Ops.Item, kept), List.length(&2, Ops.Item, whole)), True{}, block_apply.fits(kept, rest)) : {Bool.pick(Maybe<&2, List<&2, Ops.Item>>, Bool.and(_, Block.agrees(Ops.block(dr, ir), rest)), map_app(List.append(&2, Ops.Item, kept, Ops.inserted(Ops.block(dr, ir))), steps_apply(more, List.drop(&2, Ops.Item, rest, Ops.consumed(Ops.block(dr, ir))))), None{}) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, ir, out))} : Maybe<&2, List<&2, Ops.Item>>}
  %Equal.sym(Bool, Block.agrees(Ops.block(dr, ir), rest), True{}, block_agrees(dr, ir, rest, prefix_of_agree(dr, taken, s, ag))) : {Bool.pick(Maybe<&2, List<&2, Ops.Item>>, Bool.and(True{}, _), map_app(List.append(&2, Ops.Item, kept, Ops.inserted(Ops.block(dr, ir))), steps_apply(more, List.drop(&2, Ops.Item, rest, Ops.consumed(Ops.block(dr, ir))))), None{}) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, ir, out))} : Maybe<&2, List<&2, Ops.Item>>}
  %Equal.sym(List<&2, Ops.Item>, Ops.inserted(Ops.block(dr, ir)), ir, inserted_block(dr, ir)) : {map_app(List.append(&2, Ops.Item, kept, _), steps_apply(more, List.drop(&2, Ops.Item, rest, Ops.consumed(Ops.block(dr, ir))))) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, ir, out))} : Maybe<&2, List<&2, Ops.Item>>}
  %Equal.sym(Nat, Ops.consumed(Ops.block(dr, ir)), List.length(&2, Ops.Item, dr), consumed_block(dr, ir)) : {map_app(List.append(&2, Ops.Item, kept, ir), steps_apply(more, List.drop(&2, Ops.Item, rest, _))) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, ir, out))} : Maybe<&2, List<&2, Ops.Item>>}
  %Equal.sym(Nat, List.length(&2, Ops.Item, dr), List.length(&2, Ops.Item, taken), agree_len(dr, taken, ag)) : {map_app(List.append(&2, Ops.Item, kept, ir), steps_apply(more, List.drop(&2, Ops.Item, rest, _))) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, ir, out))} : Maybe<&2, List<&2, Ops.Item>>}
  %Equal.sym(List<&2, Ops.Item>, List.drop(&2, Ops.Item, rest, List.length(&2, Ops.Item, taken)), s, Pos.drop_prefix(taken, s)) : {map_app(List.append(&2, Ops.Item, kept, ir), steps_apply(more, _)) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, ir, out))} : Maybe<&2, List<&2, Ops.Item>>}
  %Equal.sym(Maybe<&2, List<&2, Ops.Item>>, steps_apply(more, s), Some{out}, ih) : {map_app(List.append(&2, Ops.Item, kept, ir), _) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, ir, out))} : Maybe<&2, List<&2, Ops.Item>>}
  %Equal.sym(List<&2, Ops.Item>, List.append(&2, Ops.Item, List.append(&2, Ops.Item, kept, ir), out), List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, ir, out)), L.append_assoc(kept, ir, out)) : {Some{_} == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, ir, out))} : Maybe<&2, List<&2, Ops.Item>>}
  {==}

def edits_nil(s: List<&2, Ops.Item>, -out: List<&2, Ops.Item>, e: {edits_apply(Nil{}, s) == Some{out} : Maybe<&2, List<&2, Ops.Item>>}) -> {s == Nil{} : List<&2, Ops.Item>}:
  match s:
    case Nil{}:
      {==}
    case x <> xs:
      Empty.absurd({x <> xs == Nil{} : List<&2, Ops.Item>}, none_some(out, e))

def rev_snoc(+x: Ops.Item, +acc: List<&2, Ops.Item>) -> {List.reverse(&2, Ops.Item, x <> acc) == List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, acc), [x]) : List<&2, Ops.Item>}:
  L.reverse_move([x], acc)

def runs_apply.closed(+gap: Nat, rd: List<&2, Ops.Item>, ri: List<&2, Ops.Item>, +kept: List<&2, Ops.Item>, +taken: List<&2, Ops.Item>, lk: {List.length(&2, Ops.Item, kept) == gap : Nat}, +ag: {agree(List.reverse(&2, Ops.Item, rd), taken) == True{} : Bool}) -> {steps_apply(Ops.runs.close(gap, rd, ri, Nil{}), List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, taken, Nil{}))) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, ri), Nil{}))} : Maybe<&2, List<&2, Ops.Item>>}:
  match rd ri:
    case Nil{} Nil{}:
      %Equal.sym(List<&2, Ops.Item>, taken, Nil{}, agree_nil(taken, ag)) : {steps_apply(Nil{}, List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, _, Nil{}))) == Some{List.append(&2, Ops.Item, kept, Nil{})} : Maybe<&2, List<&2, Ops.Item>>}
      {==}
    case Nil{} +i <> +it:
      block_apply(gap, List.reverse(&2, Ops.Item, Nil{}), List.reverse(&2, Ops.Item, i <> it), kept, taken, Nil{}, Nil{}, Nil{}, lk, ag, {==})
    case +d <> +ds Nil{}:
      block_apply(gap, List.reverse(&2, Ops.Item, d <> ds), List.reverse(&2, Ops.Item, Nil{}), kept, taken, Nil{}, Nil{}, Nil{}, lk, ag, {==})
    case +d <> +ds +i <> +it:
      block_apply(gap, List.reverse(&2, Ops.Item, d <> ds), List.reverse(&2, Ops.Item, i <> it), kept, taken, Nil{}, Nil{}, Nil{}, lk, ag, {==})

# A closed run at the end of the script: nothing is left of the state.
def runs_apply.close(+gap: Nat, +rd: List<&2, Ops.Item>, +ri: List<&2, Ops.Item>, +kept: List<&2, Ops.Item>, +taken: List<&2, Ops.Item>, s: List<&2, Ops.Item>, +out: List<&2, Ops.Item>, lk: {List.length(&2, Ops.Item, kept) == gap : Nat}, +ag: {agree(List.reverse(&2, Ops.Item, rd), taken) == True{} : Bool}, h: {edits_apply(Nil{}, s) == Some{out} : Maybe<&2, List<&2, Ops.Item>>}) -> {steps_apply(Ops.runs(Nil{}, gap, rd, ri), List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, taken, s))) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, ri), out))} : Maybe<&2, List<&2, Ops.Item>>}:
  match s:
    case x <> xs:
      Empty.absurd({steps_apply(Ops.runs(Nil{}, gap, rd, ri), List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, taken, x <> xs))) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, ri), out))} : Maybe<&2, List<&2, Ops.Item>>}, none_some(out, h))
    case Nil{}:
      %some_inj(Nil{}, out, h) : {steps_apply(Ops.runs(Nil{}, gap, rd, ri), List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, taken, Nil{}))) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, ri), _))} : Maybe<&2, List<&2, Ops.Item>>}
      runs_apply.closed(gap, rd, ri, kept, taken, lk, ag)

def runs_apply.del.rest(-d: Ops.Item, -y: Ops.Item, -r: List<&2, Ops.Move>, -ys: List<&2, Ops.Item>, -out: List<&2, Ops.Item>, c: Bool, eq: {Ops.agrees(d, y) == c : Bool}, h: {Bool.pick(Maybe<&2, List<&2, Ops.Item>>, c, edits_apply(r, ys), None{}) == Some{out} : Maybe<&2, List<&2, Ops.Item>>}) -> {edits_apply(r, ys) == Some{out} : Maybe<&2, List<&2, Ops.Item>>}:
  match c:
    case True{}:
      h
    case False{}:
      Empty.absurd({edits_apply(r, ys) == Some{out} : Maybe<&2, List<&2, Ops.Item>>}, none_some(out, h))

def runs_apply.del.agree(+rd: List<&2, Ops.Item>, +taken: List<&2, Ops.Item>, +d: Ops.Item, +y: Ops.Item, ag: {agree(List.reverse(&2, Ops.Item, rd), taken) == True{} : Bool}, dy: {Ops.agrees(d, y) == True{} : Bool}) -> {agree(List.reverse(&2, Ops.Item, d <> rd), List.append(&2, Ops.Item, taken, [y])) == True{} : Bool}:
  %Equal.sym(List<&2, Ops.Item>, List.reverse(&2, Ops.Item, d <> rd), List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, rd), [d]), rev_snoc(d, rd)) : {agree(_, List.append(&2, Ops.Item, taken, [y])) == True{} : Bool}
  agree_snoc(List.reverse(&2, Ops.Item, rd), taken, d, y, ag, dy)

# A deleted line joins the open run, quoting the line it deletes.
def runs_apply.del(+r: List<&2, Ops.Move>, +gap: Nat, +rd: List<&2, Ops.Item>, +ri: List<&2, Ops.Item>, +kept: List<&2, Ops.Item>, +taken: List<&2, Ops.Item>, +y: Ops.Item, +ys: List<&2, Ops.Item>, +out: List<&2, Ops.Item>, +d: Ops.Item, lk: {List.length(&2, Ops.Item, kept) == gap : Nat}, +ag: {agree(List.reverse(&2, Ops.Item, rd), taken) == True{} : Bool}, c: Bool, eq: {Ops.agrees(d, y) == c : Bool}, h: {Bool.pick(Maybe<&2, List<&2, Ops.Item>>, c, edits_apply(r, ys), None{}) == Some{out} : Maybe<&2, List<&2, Ops.Item>>}, ih: @+taken2: List<&2, Ops.Item> -> {agree(List.reverse(&2, Ops.Item, d <> rd), taken2) == True{} : Bool} -> {steps_apply(Ops.runs(r, gap, d <> rd, ri), List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, taken2, ys))) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, ri), out))} : Maybe<&2, List<&2, Ops.Item>>}) -> {steps_apply(Ops.runs(r, gap, d <> rd, ri), List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, taken, y <> ys))) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, ri), out))} : Maybe<&2, List<&2, Ops.Item>>}:
  match c:
    case False{}:
      Empty.absurd({steps_apply(Ops.runs(r, gap, d <> rd, ri), List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, taken, y <> ys))) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, ri), out))} : Maybe<&2, List<&2, Ops.Item>>}, none_some(out, h))
    case True{}:
      %snoc_app(taken, y, ys) : {steps_apply(Ops.runs(r, gap, d <> rd, ri), List.append(&2, Ops.Item, kept, _)) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, ri), out))} : Maybe<&2, List<&2, Ops.Item>>}
      ih(List.append(&2, Ops.Item, taken, [y]), runs_apply.del.agree(rd, taken, d, y, ag, eq))

# An inserted line joins the open run.
def runs_apply.ins(-r: List<&2, Ops.Move>, -gap: Nat, -rd: List<&2, Ops.Item>, +ri: List<&2, Ops.Item>, +kept: List<&2, Ops.Item>, -taken: List<&2, Ops.Item>, -s: List<&2, Ops.Item>, +y: Ops.Item, +o: List<&2, Ops.Item>, ih: {steps_apply(Ops.runs(r, gap, rd, y <> ri), List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, taken, s))) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, y <> ri), o))} : Maybe<&2, List<&2, Ops.Item>>}) -> {steps_apply(Ops.runs(r, gap, rd, y <> ri), List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, taken, s))) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, ri), [y]), o))} : Maybe<&2, List<&2, Ops.Item>>}:
  %rev_snoc(y, ri) : {steps_apply(Ops.runs(r, gap, rd, y <> ri), List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, taken, s))) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, _, o))} : Maybe<&2, List<&2, Ops.Item>>}
  ih

def cons_out(+x: Ops.Item, m: Maybe<&2, List<&2, Ops.Item>>, -out: List<&2, Ops.Item>, e: {map_cons(x, m) == Some{out} : Maybe<&2, List<&2, Ops.Item>>}) -> {out == x <> maybe_items(m) : List<&2, Ops.Item>}:
  match m:
    case None{}:
      Empty.absurd({out == x <> Nil{} : List<&2, Ops.Item>}, none_some(out, e))
    case Some{o}:
      Equal.sym(List<&2, Ops.Item>, x <> o, out, some_inj(x <> o, out, e))

def cons_rest(+x: Ops.Item, m: Maybe<&2, List<&2, Ops.Item>>, -out: List<&2, Ops.Item>, e: {map_cons(x, m) == Some{out} : Maybe<&2, List<&2, Ops.Item>>}) -> {m == Some{maybe_items(m)} : Maybe<&2, List<&2, Ops.Item>>}:
  match m:
    case None{}:
      Empty.absurd({None{} == Some{Nil{}} : Maybe<&2, List<&2, Ops.Item>>}, none_some(out, e))
    case Some{o}:
      {==}

def runs_apply.keep.len(+kept: List<&2, Ops.Item>, -x: Ops.Item, -gap: Nat, lk: {List.length(&2, Ops.Item, kept) == gap : Nat}) -> {List.length(&2, Ops.Item, List.append(&2, Ops.Item, kept, [x])) == 1n+gap : Nat}:
  %Equal.sym(Nat, List.length(&2, Ops.Item, List.append(&2, Ops.Item, kept, [x])), 1n+List.length(&2, Ops.Item, kept), len_snoc(kept, x)) : {_ == 1n+gap : Nat}
  %lk : {1n+List.length(&2, Ops.Item, kept) == 1n+_ : Nat}
  {==}

# A kept line, with an open run or without one.
def runs_apply.keep(+r: List<&2, Ops.Move>, +gap: Nat, rd: List<&2, Ops.Item>, ri: List<&2, Ops.Item>, +kept: List<&2, Ops.Item>, +taken: List<&2, Ops.Item>, +x: Ops.Item, +xs: List<&2, Ops.Item>, +o: List<&2, Ops.Item>, lk: {List.length(&2, Ops.Item, kept) == gap : Nat}, +ag: {agree(List.reverse(&2, Ops.Item, rd), taken) == True{} : Bool}, +h: {edits_apply(r, xs) == Some{o} : Maybe<&2, List<&2, Ops.Item>>}, ih: @+gap2: Nat -> @+kept2: List<&2, Ops.Item> -> {List.length(&2, Ops.Item, kept2) == gap2 : Nat} -> {edits_apply(r, xs) == Some{o} : Maybe<&2, List<&2, Ops.Item>>} -> {steps_apply(Ops.runs(r, gap2, Nil{}, Nil{}), List.append(&2, Ops.Item, kept2, xs)) == Some{List.append(&2, Ops.Item, kept2, o)} : Maybe<&2, List<&2, Ops.Item>>}) -> {steps_apply(Ops.runs(Ops.Keep{} <> r, gap, rd, ri), List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, taken, x <> xs))) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, ri), x <> o))} : Maybe<&2, List<&2, Ops.Item>>}:
  match rd ri:
    case Nil{} Nil{}:
      %Equal.sym(List<&2, Ops.Item>, taken, Nil{}, agree_nil(taken, ag)) : {steps_apply(Ops.runs(r, 1n+gap, Nil{}, Nil{}), List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, _, x <> xs))) == Some{List.append(&2, Ops.Item, kept, x <> o)} : Maybe<&2, List<&2, Ops.Item>>}
      %snoc_app(kept, x, xs) : {steps_apply(Ops.runs(r, 1n+gap, Nil{}, Nil{}), _) == Some{List.append(&2, Ops.Item, kept, x <> o)} : Maybe<&2, List<&2, Ops.Item>>}
      %snoc_app(kept, x, o) : {steps_apply(Ops.runs(r, 1n+gap, Nil{}, Nil{}), List.append(&2, Ops.Item, List.append(&2, Ops.Item, kept, [x]), xs)) == Some{_} : Maybe<&2, List<&2, Ops.Item>>}
      ih(1n+gap, List.append(&2, Ops.Item, kept, [x]), runs_apply.keep.len(kept, x, gap, lk), h)
    case Nil{} +i <> +it:
      block_apply(gap, List.reverse(&2, Ops.Item, Nil{}), List.reverse(&2, Ops.Item, i <> it), kept, taken, x <> xs, Ops.runs(r, 1n, Nil{}, Nil{}), x <> o, lk, ag, ih(1n, [x], {==}, h))
    case +d <> +ds Nil{}:
      block_apply(gap, List.reverse(&2, Ops.Item, d <> ds), List.reverse(&2, Ops.Item, Nil{}), kept, taken, x <> xs, Ops.runs(r, 1n, Nil{}, Nil{}), x <> o, lk, ag, ih(1n, [x], {==}, h))
    case +d <> +ds +i <> +it:
      block_apply(gap, List.reverse(&2, Ops.Item, d <> ds), List.reverse(&2, Ops.Item, i <> it), kept, taken, x <> xs, Ops.runs(r, 1n, Nil{}, Nil{}), x <> o, lk, ag, ih(1n, [x], {==}, h))

# The runs of a script, from any point in a run: the kept lines so far,
# the lines the open run has quoted, and what the script still does.
def runs_apply(es: List<&2, Ops.Move>, +gap: Nat, +rd: List<&2, Ops.Item>, +ri: List<&2, Ops.Item>, +kept: List<&2, Ops.Item>, +taken: List<&2, Ops.Item>, +s: List<&2, Ops.Item>, +out: List<&2, Ops.Item>, +lk: {List.length(&2, Ops.Item, kept) == gap : Nat}, +ag: {agree(List.reverse(&2, Ops.Item, rd), taken) == True{} : Bool}, +h: {edits_apply(es, s) == Some{out} : Maybe<&2, List<&2, Ops.Item>>}) -> {steps_apply(Ops.runs(es, gap, rd, ri), List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, taken, s))) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, ri), out))} : Maybe<&2, List<&2, Ops.Item>>}:
  match es s:
    case Nil{} s:
      runs_apply.close(gap, rd, ri, kept, taken, s, out, lk, ag, h)
    case Ops.Keep{} <> r Nil{}:
      Empty.absurd({steps_apply(Ops.runs(Ops.Keep{} <> r, gap, rd, ri), List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, taken, Nil{}))) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, ri), out))} : Maybe<&2, List<&2, Ops.Item>>}, none_some(out, h))
    case Ops.Keep{} <> +r +x <> +xs:
      %Equal.sym(List<&2, Ops.Item>, out, x <> maybe_items(edits_apply(r, xs)), cons_out(x, edits_apply(r, xs), out, h)) : {steps_apply(Ops.runs(Ops.Keep{} <> r, gap, rd, ri), List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, taken, x <> xs))) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, ri), _))} : Maybe<&2, List<&2, Ops.Item>>}
      runs_apply.keep(r, gap, rd, ri, kept, taken, x, xs, maybe_items(edits_apply(r, xs)), lk, ag, cons_rest(x, edits_apply(r, xs), out, h), gap2 => kept2 => lk2 => h2 => runs_apply(r, gap2, Nil{}, Nil{}, kept2, Nil{}, xs, maybe_items(edits_apply(r, xs)), lk2, {==}, h2))
    case Ops.Del{d} <> r Nil{}:
      Empty.absurd({steps_apply(Ops.runs(Ops.Del{d} <> r, gap, rd, ri), List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, taken, Nil{}))) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, ri), out))} : Maybe<&2, List<&2, Ops.Item>>}, none_some(out, h))
    case Ops.Del{+d} <> +r +y <> +ys:
      runs_apply.del(r, gap, rd, ri, kept, taken, y, ys, out, d, lk, ag, Ops.agrees(d, y), {==}, h, taken2 => ag2 => runs_apply(r, gap, d <> rd, ri, kept, taken2, ys, out, lk, ag2, runs_apply.del.rest(d, y, r, ys, out, Ops.agrees(d, y), {==}, h)))
    case Ops.Ins{+y} <> +r s:
      %Equal.sym(List<&2, Ops.Item>, out, y <> maybe_items(edits_apply(r, s)), cons_out(y, edits_apply(r, s), out, h)) : {steps_apply(Ops.runs(Ops.Ins{y} <> r, gap, rd, ri), List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, taken, s))) == Some{List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, ri), _))} : Maybe<&2, List<&2, Ops.Item>>}
      %snoc_app(List.reverse(&2, Ops.Item, ri), y, maybe_items(edits_apply(r, s))) : {steps_apply(Ops.runs(r, gap, rd, y <> ri), List.append(&2, Ops.Item, kept, List.append(&2, Ops.Item, taken, s))) == Some{List.append(&2, Ops.Item, kept, _)} : Maybe<&2, List<&2, Ops.Item>>}
      runs_apply.ins(r, gap, rd, ri, kept, taken, s, y, maybe_items(edits_apply(r, s)), runs_apply(r, gap, rd, y <> ri, kept, taken, s, maybe_items(edits_apply(r, s)), lk, ag, cons_rest(y, edits_apply(r, s), out, h)))

# The cursor over a script of blocks
# ----------------------------------

def app_out(+front: List<&2, Ops.Item>, m: Maybe<&2, List<&2, Ops.Item>>, -out: List<&2, Ops.Item>, e: {map_app(front, m) == Some{out} : Maybe<&2, List<&2, Ops.Item>>}) -> {out == List.append(&2, Ops.Item, front, maybe_items(m)) : List<&2, Ops.Item>}:
  match m:
    case None{}:
      Empty.absurd({out == List.append(&2, Ops.Item, front, Nil{}) : List<&2, Ops.Item>}, none_some(out, e))
    case Some{o}:
      Equal.sym(List<&2, Ops.Item>, List.append(&2, Ops.Item, front, o), out, some_inj(List.append(&2, Ops.Item, front, o), out, e))

def app_rest(+front: List<&2, Ops.Item>, m: Maybe<&2, List<&2, Ops.Item>>, -out: List<&2, Ops.Item>, e: {map_app(front, m) == Some{out} : Maybe<&2, List<&2, Ops.Item>>}) -> {m == Some{maybe_items(m)} : Maybe<&2, List<&2, Ops.Item>>}:
  match m:
    case None{}:
      Empty.absurd({None{} == Some{Nil{}} : Maybe<&2, List<&2, Ops.Item>>}, none_some(out, e))
    case Some{o}:
      {==}

def step_ok(c: Bool, +r: Maybe<&2, List<&2, Ops.Item>>, -out: List<&2, Ops.Item>, e: {Bool.pick(Maybe<&2, List<&2, Ops.Item>>, c, r, None{}) == Some{out} : Maybe<&2, List<&2, Ops.Item>>}) -> {c == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, none_some(out, e))

def step_rest(c: Bool, +r: Maybe<&2, List<&2, Ops.Item>>, -out: List<&2, Ops.Item>, e: {Bool.pick(Maybe<&2, List<&2, Ops.Item>>, c, r, None{}) == Some{out} : Maybe<&2, List<&2, Ops.Item>>}) -> {r == Some{out} : Maybe<&2, List<&2, Ops.Item>>}:
  match c:
    case True{}:
      e
    case False{}:
      Empty.absurd({r == Some{out} : Maybe<&2, List<&2, Ops.Item>>}, none_some(out, e))

# A block the script applies is one the cursor walks to the same place.
def steps_walk.step(+gap: Nat, +edit: Ops.Edit, +rest: List<&2, Ops.Step>, +pos: Nat, +state: List<&2, Ops.Item>, +out: List<&2, Ops.Item>, +h: {Bool.pick(Maybe<&2, List<&2, Ops.Item>>, Bool.and(Nat.is_le(gap, List.length(&2, Ops.Item, state)), Block.agrees(edit, List.drop(&2, Ops.Item, state, gap))), map_app(List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, gap), Ops.inserted(edit)), steps_apply(rest, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, gap), Ops.consumed(edit)))), None{}) == Some{out} : Maybe<&2, List<&2, Ops.Item>>}, ih: @+o: List<&2, Ops.Item> -> {steps_apply(rest, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, gap), Ops.consumed(edit))) == Some{o} : Maybe<&2, List<&2, Ops.Item>>} -> {Cursor.walk(Ops.script(rest, Nat.add(Nat.add(pos, gap), Ops.consumed(edit))), Nat.add(Nat.add(pos, gap), Ops.consumed(edit)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, gap), Ops.consumed(edit))) == Done{o} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Cursor.walk(List.append(&2, Ops.Op, Ops.operations(Nat.add(pos, gap), edit), Ops.script(rest, Nat.add(Nat.add(pos, gap), Ops.consumed(edit)))), pos, state) == Done{out} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  +front = List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, gap), Ops.inserted(edit))
  +later = steps_apply(rest, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, gap), Ops.consumed(edit)))
  +c = Bool.and(Nat.is_le(gap, List.length(&2, Ops.Item, state)), Block.agrees(edit, List.drop(&2, Ops.Item, state, gap)))
  +ok = step_ok(c, map_app(front, later), out, h)
  +o = maybe_items(later)
  +more = Ops.script(rest, Nat.add(Nat.add(pos, gap), Ops.consumed(edit)))
  %Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.walk(List.append(&2, Ops.Op, Ops.operations(Nat.add(pos, gap), edit), more), pos, state), Cursor.combine(Cursor.disagreement(Nat.add(pos, gap), Block.agrees(edit, List.drop(&2, Ops.Item, state, gap))), front, Cursor.walk(more, Nat.add(Nat.add(pos, gap), Ops.consumed(edit)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, gap), Ops.consumed(edit)))), Comp.walk_block(edit, pos, gap, state, more)) : {_ == Done{out} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %Equal.sym(Bool, Block.agrees(edit, List.drop(&2, Ops.Item, state, gap)), True{}, Comp.and_right(Nat.is_le(gap, List.length(&2, Ops.Item, state)), Block.agrees(edit, List.drop(&2, Ops.Item, state, gap)), ok)) : {Cursor.combine(Cursor.disagreement(Nat.add(pos, gap), _), front, Cursor.walk(Ops.script(rest, Nat.add(Nat.add(pos, gap), Ops.consumed(edit))), Nat.add(Nat.add(pos, gap), Ops.consumed(edit)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, gap), Ops.consumed(edit)))) == Done{out} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.walk(Ops.script(rest, Nat.add(Nat.add(pos, gap), Ops.consumed(edit))), Nat.add(Nat.add(pos, gap), Ops.consumed(edit)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, gap), Ops.consumed(edit))), Done{o}, ih(o, app_rest(front, later, out, step_rest(c, map_app(front, later), out, h)))) : {Cursor.combine(None{}, front, _) == Done{out} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %Equal.sym(List<&2, Ops.Item>, out, List.append(&2, Ops.Item, front, o), app_out(front, later, out, step_rest(c, map_app(front, later), out, h))) : {Done{List.append(&2, Ops.Item, front, o)} == Done{_} : Result<&2, &2, String, List<&2, Ops.Item>>}
  {==}

# The cursor walks a script of blocks the script applies to its result.
def steps_walk(steps: List<&2, Ops.Step>, +pos: Nat, +state: List<&2, Ops.Item>, +out: List<&2, Ops.Item>, +h: {steps_apply(steps, state) == Some{out} : Maybe<&2, List<&2, Ops.Item>>}) -> {Cursor.walk(Ops.script(steps, pos), pos, state) == Done{out} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match steps:
    case Nil{}:
      %some_inj(state, out, h) : {Done{state} == Done{_} : Result<&2, &2, String, List<&2, Ops.Item>>}
      {==}
    case Ops.Step{+gap, +edit} <> +rest:
      steps_walk.step(gap, edit, rest, pos, state, out, h, o => h2 => steps_walk(rest, Nat.add(Nat.add(pos, gap), Ops.consumed(edit)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, gap), Ops.consumed(edit)), o, h2))

# Range
# -----

def in_range_join(a: List<&2, Ops.Op>, +b: List<&2, Ops.Op>, +len: Nat, +ea: {Ops.in_range(a, len) == True{} : Bool}, eb: {Ops.in_range(b, len) == True{} : Bool}) -> {Ops.in_range(List.append(&2, Ops.Op, a, b), len) == True{} : Bool}:
  match a:
    case Nil{}:
      eb
    case +op <> +rest:
      Parse.and_intro(Nat.is_le(Ops.end(op), len), Ops.in_range(List.append(&2, Ops.Op, rest, b), len), Comp.and_left(Nat.is_le(Ops.end(op), len), Ops.in_range(rest, len), ea), in_range_join(rest, b, len, Comp.and_right(Nat.is_le(Ops.end(op), len), Ops.in_range(rest, len), ea), eb))

def range_cast(-ops: List<&2, Ops.Op>, -a: Nat, -b: Nat, eq: {a == b : Nat}, e: {Ops.in_range(ops, a) == True{} : Bool}) -> {Ops.in_range(ops, b) == True{} : Bool}:
  %eq : {Ops.in_range(ops, _) == True{} : Bool}
  e

# A block whose end is in range is in range.
def block_range(edit: Ops.Edit, +here: Nat, +len: Nat, +e: {Nat.is_le(Nat.add(here, Ops.consumed(edit)), len) == True{} : Bool}) -> {Ops.in_range(Ops.operations(here, edit), len) == True{} : Bool}:
  match edit:
    case Ops.Insertion{items}:
      %Equal.sym(Bool, Nat.is_le(here, len), True{}, Comp.le_add_left(here, 0n, len, e)) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case Ops.Deletion{+recorded}:
      %Equal.sym(Bool, Nat.is_le(Nat.add(here, List.length(&2, Ops.Item, recorded)), len), True{}, e) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case Ops.Replacement{+recorded, inserted}:
      %Equal.sym(Bool, Nat.is_le(Nat.add(here, List.length(&2, Ops.Item, recorded)), len), True{}, e) : {Bool.and(_, Bool.and(Nat.is_le(here, len), True{})) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_le(here, len), True{}, Comp.le_add_left(here, List.length(&2, Ops.Item, recorded), len, e)) : {Bool.and(True{}, Bool.and(_, True{})) == True{} : Bool}
      {==}

def prefix_len(recorded: List<&2, Ops.Item>, after: List<&2, Ops.Item>, e: {Spec.prefix_matches(recorded, after) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Ops.Item, recorded), List.length(&2, Ops.Item, after)) == True{} : Bool}:
  match recorded after:
    case Nil{} Nil{}:
      {==}
    case Nil{} a <> as:
      {==}
    case r <> rs Nil{}:
      Empty.absurd({Nat.is_le(1n+List.length(&2, Ops.Item, rs), 0n) == True{} : Bool}, Comp.false_true(e))
    case r <> rs a <> as:
      prefix_len(rs, as, Comp.and_right(Spec.matches(r, a), Spec.prefix_matches(rs, as), e))

def consumed_le(edit: Ops.Edit, +after: List<&2, Ops.Item>, e: {Block.agrees(edit, after) == True{} : Bool}) -> {Nat.is_le(Ops.consumed(edit), List.length(&2, Ops.Item, after)) == True{} : Bool}:
  match edit:
    case Ops.Insertion{items}:
      Pos.zero_le(List.length(&2, Ops.Item, after))
    case Ops.Deletion{recorded}:
      prefix_len(recorded, after, e)
    case Ops.Replacement{recorded, inserted}:
      prefix_len(recorded, after, e)

def len_drop(xs: List<&2, Ops.Item>, n: Nat, le: {Nat.is_le(n, List.length(&2, Ops.Item, xs)) == True{} : Bool}) -> {List.length(&2, Ops.Item, xs) == Nat.add(n, List.length(&2, Ops.Item, List.drop(&2, Ops.Item, xs, n))) : Nat}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      Empty.absurd({0n == Nat.add(1n+p, 0n) : Nat}, Comp.false_true(le))
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Ops.Item, t), Nat.add(p, List.length(&2, Ops.Item, List.drop(&2, Ops.Item, t, p))), len_drop(t, p, le))

def le_shift(+n: Nat, -a: Nat, -b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(n, a), Nat.add(n, b)) == True{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(Nat.add(n, a), Nat.add(n, b)), Nat.cmp(a, b), Pos.cmp_shift(n, a, b)) : {Cmp.is_le(_) == True{} : Bool}
  e

# The length of the state, seen past a block: gap, consumed, and the rest.
def len_past(+state: List<&2, Ops.Item>, +gap: Nat, +edit: Ops.Edit, +le: {Nat.is_le(gap, List.length(&2, Ops.Item, state)) == True{} : Bool}, +ag: {Block.agrees(edit, List.drop(&2, Ops.Item, state, gap)) == True{} : Bool}) -> {List.length(&2, Ops.Item, state) == Nat.add(gap, Nat.add(Ops.consumed(edit), List.length(&2, Ops.Item, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, gap), Ops.consumed(edit))))) : Nat}:
  +after = List.drop(&2, Ops.Item, state, gap)
  %len_drop(after, Ops.consumed(edit), consumed_le(edit, after, ag)) : {List.length(&2, Ops.Item, state) == Nat.add(gap, _) : Nat}
  len_drop(state, gap, le)

def steps_range.step(+gap: Nat, +edit: Ops.Edit, +rest: List<&2, Ops.Step>, +pos: Nat, +state: List<&2, Ops.Item>, +out: List<&2, Ops.Item>, +h: {Bool.pick(Maybe<&2, List<&2, Ops.Item>>, Bool.and(Nat.is_le(gap, List.length(&2, Ops.Item, state)), Block.agrees(edit, List.drop(&2, Ops.Item, state, gap))), map_app(List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, gap), Ops.inserted(edit)), steps_apply(rest, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, gap), Ops.consumed(edit)))), None{}) == Some{out} : Maybe<&2, List<&2, Ops.Item>>}, ih: @+o: List<&2, Ops.Item> -> {steps_apply(rest, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, gap), Ops.consumed(edit))) == Some{o} : Maybe<&2, List<&2, Ops.Item>>} -> {Ops.in_range(Ops.script(rest, Nat.add(Nat.add(pos, gap), Ops.consumed(edit))), Nat.add(Nat.add(Nat.add(pos, gap), Ops.consumed(edit)), List.length(&2, Ops.Item, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, gap), Ops.consumed(edit))))) == True{} : Bool}) -> {Ops.in_range(List.append(&2, Ops.Op, Ops.operations(Nat.add(pos, gap), edit), Ops.script(rest, Nat.add(Nat.add(pos, gap), Ops.consumed(edit)))), Nat.add(pos, List.length(&2, Ops.Item, state))) == True{} : Bool}:
  +front = List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, gap), Ops.inserted(edit))
  +after = List.drop(&2, Ops.Item, state, gap)
  +later = steps_apply(rest, List.drop(&2, Ops.Item, after, Ops.consumed(edit)))
  +c = Bool.and(Nat.is_le(gap, List.length(&2, Ops.Item, state)), Block.agrees(edit, after))
  +ok = step_ok(c, map_app(front, later), out, h)
  +le = Comp.and_left(Nat.is_le(gap, List.length(&2, Ops.Item, state)), Block.agrees(edit, after), ok)
  +ag = Comp.and_right(Nat.is_le(gap, List.length(&2, Ops.Item, state)), Block.agrees(edit, after), ok)
  +ldd = List.length(&2, Ops.Item, List.drop(&2, Ops.Item, after, Ops.consumed(edit)))
  +here = Nat.add(pos, gap)
  +next = Nat.add(here, Ops.consumed(edit))
  %Equal.sym(Nat, List.length(&2, Ops.Item, state), Nat.add(gap, Nat.add(Ops.consumed(edit), ldd)), len_past(state, gap, edit, le, ag)) : {Ops.in_range(List.append(&2, Ops.Op, Ops.operations(here, edit), Ops.script(rest, next)), Nat.add(pos, _)) == True{} : Bool}
  %Pos.add_assoc(pos, gap, Nat.add(Ops.consumed(edit), ldd)) : {Ops.in_range(List.append(&2, Ops.Op, Ops.operations(here, edit), Ops.script(rest, next)), _) == True{} : Bool}
  %Pos.add_assoc(here, Ops.consumed(edit), ldd) : {Ops.in_range(List.append(&2, Ops.Op, Ops.operations(here, edit), Ops.script(rest, next)), _) == True{} : Bool}
  in_range_join(Ops.operations(here, edit), Ops.script(rest, next), Nat.add(next, ldd), block_range(edit, here, Nat.add(next, ldd), Comp.le_add(next, next, ldd, Comp.le_refl(next))), ih(maybe_items(later), app_rest(front, later, out, step_rest(c, map_app(front, later), out, h))))

# Every block of a script that applies is in the state's range.
def steps_range(steps: List<&2, Ops.Step>, +pos: Nat, +state: List<&2, Ops.Item>, +out: List<&2, Ops.Item>, +h: {steps_apply(steps, state) == Some{out} : Maybe<&2, List<&2, Ops.Item>>}) -> {Ops.in_range(Ops.script(steps, pos), Nat.add(pos, List.length(&2, Ops.Item, state))) == True{} : Bool}:
  match steps:
    case Nil{}:
      {==}
    case Ops.Step{+gap, +edit} <> +rest:
      steps_range.step(gap, edit, rest, pos, state, out, h, o => h2 => steps_range(rest, Nat.add(Nat.add(pos, gap), Ops.consumed(edit)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, gap), Ops.consumed(edit)), o, h2))

# The theorem
# -----------

def ddisc(m: Maybe<&2, Ops.Doc>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{d}:
      Empty

def none_doc(-d: Ops.Doc, e: {None{} == Some{d} : Maybe<&2, Ops.Doc>}) -> Empty:
  %e : {ddisc(_) : Type}
  Unit{}

def maybe_doc(m: Maybe<&2, Ops.Doc>) -> Ops.Doc:
  match m:
    case None{}:
      Ops.Doc{None{}, None{}, Nil{}}
    case Some{d}:
      d

# `Ops.apply.checked`, with the two decisions it makes as arguments, so
# that each can be rewritten.
def after_checks(+child: List<&2, Ops.Item>, tb: Bool, dig: Result<&2, &2, String, Unit>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  do Result<&2, &2, String, List<&2, Ops.Item>>:
    Ops.ensure(tb, 0n, "an item without a newline that is not the last")
    dig
    return child

def checked_is(+child: List<&2, Ops.Item>) -> {Cursor.checked(True{}, Some{Ops.state_digest(child)}, Done{child}) == after_checks(child, Ops.terminated_but_last(child), Ops.check_result.of(Ops.state_digest(child), Ops.any_forgotten(child), Ops.state_digest(child))) : Result<&2, &2, String, List<&2, Ops.Item>>}:
  {==}

# A digest checked against itself passes, forgotten items or not.
def digest_ok(+d: String, forgot: Bool) -> {Ops.check_result.of(d, forgot, d) == Done{Unit{}} : Result<&2, &2, String, Unit>}:
  match forgot:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, T.same(d, d), True{}, same_refl(d)) : {Bool.pick(Result<&2, &2, String, Unit>, _, Done{Unit{}}, Fail{"the result stated is " ++ d ++ " but the replay produced " ++ d}) == Done{Unit{}} : Result<&2, &2, String, Unit>}
      {==}

# Past the range and cursor checks, the stated digest is the child's own.
def checked_child(+child: List<&2, Ops.Item>, tbl: {Ops.terminated_but_last(child) == True{} : Bool}) -> {Cursor.checked(True{}, Some{Ops.state_digest(child)}, Done{child}) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  +sd = Ops.state_digest(child)
  +dig = Ops.check_result.of(sd, Ops.any_forgotten(child), sd)
  %Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.checked(True{}, Some{sd}, Done{child}), after_checks(child, Ops.terminated_but_last(child), dig), checked_is(child)) : {_ == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %Equal.sym(Bool, Ops.terminated_but_last(child), True{}, tbl) : {after_checks(child, _, dig) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %Equal.sym(Result<&2, &2, String, Unit>, dig, Done{Unit{}}, digest_ok(sd, Ops.any_forgotten(child))) : {after_checks(child, True{}, _) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}
  {==}

# The operations the diff emits, applied by the cursor, are the child.
def diff_walks(+parent: List<&2, Ops.Item>, +child: List<&2, Ops.Item>, +ops: List<&2, Ops.Op>, eq: {Ops.script(Ops.runs(Ops.edits(parent, child), 0n, Nil{}, Nil{}), 0n) == ops : List<&2, Ops.Op>}, tbl: {Ops.terminated_but_last(child) == True{} : Bool}) -> {Cursor.apply(parent, Ops.Doc{None{}, Some{Ops.state_digest(child)}, ops}) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  +steps = Ops.runs(Ops.edits(parent, child), 0n, Nil{}, Nil{})
  +applied = runs_apply(Ops.edits(parent, child), 0n, Nil{}, Nil{}, Nil{}, Nil{}, parent, child, {==}, {==}, edits_ok(parent, child))
  %eq : {Cursor.apply(parent, Ops.Doc{None{}, Some{Ops.state_digest(child)}, _}) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %Equal.sym(Bool, Ops.in_range(Ops.script(steps, 0n), List.length(&2, Ops.Item, parent)), True{}, steps_range(steps, 0n, parent, child, applied)) : {Cursor.checked(_, Some{Ops.state_digest(child)}, Cursor.walk(Ops.script(steps, 0n), 0n, parent)) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.walk(Ops.script(steps, 0n), 0n, parent), Done{child}, steps_walk(steps, 0n, parent, child, applied)) : {Cursor.checked(True{}, Some{Ops.state_digest(child)}, _) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}
  checked_child(child, tbl)

def diff_applies.of(+parent: List<&2, Ops.Item>, +child: List<&2, Ops.Item>, ops: List<&2, Ops.Op>, +eq: {Ops.script(Ops.runs(Ops.edits(parent, child), 0n, Nil{}, Nil{}), 0n) == ops : List<&2, Ops.Op>}, tbl: {Ops.terminated_but_last(child) == True{} : Bool}, -doc: Ops.Doc, e: {Ops.diff.of(ops, Ops.state_digest(child)) == Some{doc} : Maybe<&2, Ops.Doc>}) -> {Cursor.apply(parent, doc) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match ops:
    case Nil{}:
      Empty.absurd({Cursor.apply(parent, doc) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}, none_doc(doc, e))
    case +op <> +rest:
      %Equal.cong(Maybe<&2, Ops.Doc>, Ops.Doc, maybe_doc, Some{Ops.Doc{None{}, Some{Ops.state_digest(child)}, op <> rest}}, Some{doc}, e) : {Cursor.apply(parent, _) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}
      diff_walks(parent, child, op <> rest, eq, tbl)

# The theorem, over the cursor specification; PROOF.bend carries it to
# `Ops.apply` through the cursor refinement.
def diff_applies(+parent: List<&2, Ops.Item>, +child: List<&2, Ops.Item>, tbl: {Ops.terminated_but_last(child) == True{} : Bool}, -doc: Ops.Doc, e: {Ops.diff(parent, child) == Some{doc} : Maybe<&2, Ops.Doc>}) -> {Cursor.apply(parent, doc) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  diff_applies.of(parent, child, Ops.script(Ops.runs(Ops.edits(parent, child), 0n, Nil{}, Nil{}), 0n), {==}, tbl, doc, e)

def main() -> Unit:
  Unit{}
