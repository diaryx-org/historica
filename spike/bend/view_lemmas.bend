# Every view keeps the invariant. `insert_at_gap` assumes of an author's
# view that its reading finishes within its fuel and reads no element
# twice; `walk_lemmas` shows every tree a walk builds has that, and so the
# view of an event that had seen all of it. This file shows it of every
# view: the tree restricted to a set of events that holds the past of each
# is the tree those events alone walk to, in the order the whole walk took
# them, and that tree keeps the invariant by `merge_walk_invariant`.
#
# Restriction commutes with an event's step when the event is in the set:
# its actions are decided on a view the set already holds, and an attach
# or a mark applied to the whole tree and then restricted is the same one
# applied to the restriction. The attach needs the tree in name order —
# an element placed before one the restriction drops must still come
# before everything after it — and the mark needs each removal list in
# index order, for the same reason; every tree a walk builds is both.
import Base
import ./ops.bend as Ops
import ./merge.bend as M
import ./composition_lemmas.bend as Comp
import ./equality_lemmas.bend as Eq
import ./merge_lemmas.bend as ML
import ./anchor_lemmas.bend as AL
import ./linear_lemmas.bend as Lin
import ./walk_lemmas.bend as Walk
import ./cursor_spec.bend as Cursor
import ./semantic_replay.bend as Block

# Order
# -----

def rname(x: M.Node, S: List<&2, Nat>) -> {M.Node.name(M.Node.restrict(x, S)) == M.Node.name(x) : M.Name}:
  match x:
    case M.Node{nm, it, pl, d}:
      {==}

def le_disc(e: {Cmp.is_le(GT{}) == True{} : Bool}) -> Empty:
  Comp.false_true(e)

def name_eq_of.of(+a1: Nat, +a2: Nat, +b1: Nat, +b2: Nat, c: Cmp, ec: {Nat.cmp(a1, b1) == c : Cmp}, e: {M.Name.cmp.of(c, a2, b2) == EQ{} : Cmp}) -> {M.Name{a1, a2} == M.Name{b1, b2} : M.Name}:
  match c:
    case LT{}:
      Empty.absurd({M.Name{a1, a2} == M.Name{b1, b2} : M.Name}, Eq.lt_eq(e))
    case GT{}:
      Empty.absurd({M.Name{a1, a2} == M.Name{b1, b2} : M.Name}, Eq.gt_eq(e))
    case EQ{}:
      %ML.cmp_eq(a1, b1, ec) : {M.Name{a1, a2} == M.Name{_, b2} : M.Name}
      %ML.cmp_eq(a2, b2, e) : {M.Name{a1, a2} == M.Name{a1, _} : M.Name}
      {==}

def name_eq_of(a: M.Name, b: M.Name, e: {M.Name.cmp(a, b) == EQ{} : Cmp}) -> {a == b : M.Name}:
  match a b:
    case M.Name{+a1, +a2} M.Name{+b1, +b2}:
      name_eq_of.of(a1, a2, b1, b2, Nat.cmp(a1, b1), {==}, e)

# a < x and x ≤ y give a < y.
def lt_le.of(+a: M.Name, +x: M.Name, +y: M.Name, c: Cmp, ec: {M.Name.cmp(x, y) == c : Cmp}, h1: {M.Name.cmp(a, x) == LT{} : Cmp}, h2: {Cmp.is_le(c) == True{} : Bool}) -> {M.Name.cmp(a, y) == LT{} : Cmp}:
  match c:
    case LT{}:
      ML.name_trans(a, x, y, h1, ec)
    case EQ{}:
      %name_eq_of(x, y, ec) : {M.Name.cmp(a, _) == LT{} : Cmp}
      h1
    case GT{}:
      Empty.absurd({M.Name.cmp(a, y) == LT{} : Cmp}, Comp.false_true(h2))

def lt_le(+a: M.Name, +x: M.Name, +y: M.Name, h1: {M.Name.cmp(a, x) == LT{} : Cmp}, h2: {Cmp.is_le(M.Name.cmp(x, y)) == True{} : Bool}) -> {M.Name.cmp(a, y) == LT{} : Cmp}:
  lt_le.of(a, x, y, M.Name.cmp(x, y), {==}, h1, h2)

def nlt_le.of(c: Cmp, e: {Cmp.is_lt(c) == False{} : Bool}) -> {Cmp.is_le(ML.flip(c)) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Cmp.is_le(GT{}) == True{} : Bool}, ML.true_false(e))
    case EQ{}:
      {==}
    case GT{}:
      {==}

# Not a < x gives x ≤ a.
def nlt_le(+a: M.Name, +x: M.Name, e: {Cmp.is_lt(M.Name.cmp(a, x)) == False{} : Bool}) -> {Cmp.is_le(M.Name.cmp(x, a)) == True{} : Bool}:
  %Equal.sym(Cmp, M.Name.cmp(x, a), ML.flip(M.Name.cmp(a, x)), ML.name_flip(a, x)) : {Cmp.is_le(_) == True{} : Bool}
  nlt_le.of(M.Name.cmp(a, x), e)

def nat_nlt_le(+a: Nat, +b: Nat, e: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(b, a), ML.flip(Nat.cmp(a, b)), ML.cmp_flip(a, b)) : {Cmp.is_le(_) == True{} : Bool}
  nlt_le.of(Nat.cmp(a, b), e)

def lt_true(c: Cmp, e: {c == LT{} : Cmp}) -> {Cmp.is_lt(c) == True{} : Bool}:
  %Equal.sym(Cmp, c, LT{}, e) : {Cmp.is_lt(_) == True{} : Bool}
  {==}

def le_of_lt(c: Cmp, e: {Cmp.is_lt(c) == True{} : Bool}) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_le(EQ{}) == True{} : Bool}, Comp.false_true(e))
    case GT{}:
      Empty.absurd({Cmp.is_le(GT{}) == True{} : Bool}, Comp.false_true(e))

# The tree in name order
# ----------------------
#
# Each element's name is at most every name after it. Equal names are
# allowed: nothing here needs them distinct.
def nlow(+a: M.Name, l: List<&2, M.Node>) -> Bool:
  match l:
    case Nil{}:
      True{}
    case y <> ys:
      Bool.and(Cmp.is_le(M.Name.cmp(a, M.Node.name(y))), nlow(a, ys))

def nbelow(+a: M.Name, l: List<&2, M.Node>) -> Bool:
  match l:
    case Nil{}:
      True{}
    case y <> ys:
      Bool.and(Cmp.is_lt(M.Name.cmp(a, M.Node.name(y))), nbelow(a, ys))

def sorted(t: List<&2, M.Node>) -> Bool:
  match t:
    case Nil{}:
      True{}
    case x <> +xs:
      Bool.and(nlow(M.Node.name(x), xs), sorted(xs))

def below_of_lt(+a: M.Name, +x: M.Name, l: List<&2, M.Node>, +h1: {M.Name.cmp(a, x) == LT{} : Cmp}, +h2: {nlow(x, l) == True{} : Bool}) -> {nbelow(a, l) == True{} : Bool}:
  match l:
    case Nil{}:
      {==}
    case +y <> +ys:
      AL.and_intro(Cmp.is_lt(M.Name.cmp(a, M.Node.name(y))), nbelow(a, ys),
        lt_true(M.Name.cmp(a, M.Node.name(y)), lt_le(a, x, M.Node.name(y), h1, Comp.and_left(Cmp.is_le(M.Name.cmp(x, M.Node.name(y))), nlow(x, ys), h2))),
        below_of_lt(a, x, ys, h1, Comp.and_right(Cmp.is_le(M.Name.cmp(x, M.Node.name(y))), nlow(x, ys), h2)))

def low_of_below(+a: M.Name, l: List<&2, M.Node>, +h: {nbelow(a, l) == True{} : Bool}) -> {nlow(a, l) == True{} : Bool}:
  match l:
    case Nil{}:
      {==}
    case +y <> +ys:
      AL.and_intro(Cmp.is_le(M.Name.cmp(a, M.Node.name(y))), nlow(a, ys),
        le_of_lt(M.Name.cmp(a, M.Node.name(y)), Comp.and_left(Cmp.is_lt(M.Name.cmp(a, M.Node.name(y))), nbelow(a, ys), h)),
        low_of_below(a, ys, Comp.and_right(Cmp.is_lt(M.Name.cmp(a, M.Node.name(y))), nbelow(a, ys), h)))

# An element below everything in a list is attached at its front.
def below_attach(l: List<&2, M.Node>, +n: M.Node, h: {nbelow(M.Node.name(n), l) == True{} : Bool}) -> {M.attach(l, n) == n <> l : List<&2, M.Node>}:
  match l:
    case Nil{}:
      {==}
    case +y <> +ys:
      %Equal.sym(Bool, Cmp.is_lt(M.Name.cmp(M.Node.name(n), M.Node.name(y))), True{}, Comp.and_left(Cmp.is_lt(M.Name.cmp(M.Node.name(n), M.Node.name(y))), nbelow(M.Node.name(n), ys), h)) : {M.attach.put(n, y, ys, M.attach(ys, n), _) == n <> y <> ys : List<&2, M.Node>}
      {==}

def attach_nlt(+y: M.Node, +ys: List<&2, M.Node>, +n: M.Node, e: {Cmp.is_lt(M.Name.cmp(M.Node.name(n), M.Node.name(y))) == False{} : Bool}) -> {M.attach(y <> ys, n) == y <> M.attach(ys, n) : List<&2, M.Node>}:
  %Equal.sym(Bool, Cmp.is_lt(M.Name.cmp(M.Node.name(n), M.Node.name(y))), False{}, e) : {M.attach.put(n, y, ys, M.attach(ys, n), _) == y <> M.attach(ys, n) : List<&2, M.Node>}
  {==}

def below_restrict.at(+a: M.Name, +x: M.Node, +xs: List<&2, M.Node>, +S: List<&2, Nat>, h: Bool, hx: {Cmp.is_lt(M.Name.cmp(a, M.Node.name(x))) == True{} : Bool}, ih: {nbelow(a, M.restrict(xs, S)) == True{} : Bool}) -> {nbelow(a, List.filter.put(M.Node, M.Node.restrict(x, S), M.restrict(xs, S), h)) == True{} : Bool}:
  match h:
    case True{}:
      AL.and_intro(Cmp.is_lt(M.Name.cmp(a, M.Node.name(M.Node.restrict(x, S)))), nbelow(a, M.restrict(xs, S)),
        (%Equal.sym(M.Name, M.Node.name(M.Node.restrict(x, S)), M.Node.name(x), rname(x, S)) : {Cmp.is_lt(M.Name.cmp(a, _)) == True{} : Bool}
          hx),
        ih)
    case False{}:
      ih

def below_restrict(l: List<&2, M.Node>, +a: M.Name, +S: List<&2, Nat>, +h: {nbelow(a, l) == True{} : Bool}) -> {nbelow(a, M.restrict(l, S)) == True{} : Bool}:
  match l:
    case Nil{}:
      {==}
    case +x <> +xs:
      below_restrict.at(a, x, xs, S, M.has(S, M.Node.author(x)),
        Comp.and_left(Cmp.is_lt(M.Name.cmp(a, M.Node.name(x))), nbelow(a, xs), h),
        below_restrict(xs, a, S, Comp.and_right(Cmp.is_lt(M.Name.cmp(a, M.Node.name(x))), nbelow(a, xs), h)))

def low_attach.at(+a: M.Name, +y: M.Node, +ys: List<&2, M.Node>, +n: M.Node, lt: Bool, +hn: {Cmp.is_le(M.Name.cmp(a, M.Node.name(n))) == True{} : Bool}, +h: {nlow(a, y <> ys) == True{} : Bool}, ih: {nlow(a, M.attach(ys, n)) == True{} : Bool}) -> {nlow(a, M.attach.put(n, y, ys, M.attach(ys, n), lt)) == True{} : Bool}:
  match lt:
    case True{}:
      AL.and_intro(Cmp.is_le(M.Name.cmp(a, M.Node.name(n))), nlow(a, y <> ys), hn, h)
    case False{}:
      AL.and_intro(Cmp.is_le(M.Name.cmp(a, M.Node.name(y))), nlow(a, M.attach(ys, n)), Comp.and_left(Cmp.is_le(M.Name.cmp(a, M.Node.name(y))), nlow(a, ys), h), ih)

def low_attach(l: List<&2, M.Node>, +a: M.Name, +n: M.Node, +hn: {Cmp.is_le(M.Name.cmp(a, M.Node.name(n))) == True{} : Bool}, +h: {nlow(a, l) == True{} : Bool}) -> {nlow(a, M.attach(l, n)) == True{} : Bool}:
  match l:
    case Nil{}:
      AL.and_intro(Cmp.is_le(M.Name.cmp(a, M.Node.name(n))), True{}, hn, {==})
    case +y <> +ys:
      low_attach.at(a, y, ys, n, Cmp.is_lt(M.Name.cmp(M.Node.name(n), M.Node.name(y))), hn, h,
        low_attach(ys, a, n, hn, Comp.and_right(Cmp.is_le(M.Name.cmp(a, M.Node.name(y))), nlow(a, ys), h)))

def sorted_attach.at(+x: M.Node, +xs: List<&2, M.Node>, +n: M.Node, lt: Bool, +e: {Cmp.is_lt(M.Name.cmp(M.Node.name(n), M.Node.name(x))) == lt : Bool}, +h: {sorted(x <> xs) == True{} : Bool}, ih: {sorted(M.attach(xs, n)) == True{} : Bool}) -> {sorted(M.attach.put(n, x, xs, M.attach(xs, n), lt)) == True{} : Bool}:
  match lt:
    case True{}:
      AL.and_intro(nlow(M.Node.name(n), x <> xs), sorted(x <> xs),
        low_of_below(M.Node.name(n), x <> xs,
          AL.and_intro(Cmp.is_lt(M.Name.cmp(M.Node.name(n), M.Node.name(x))), nbelow(M.Node.name(n), xs), e,
            below_of_lt(M.Node.name(n), M.Node.name(x), xs, ML.cmp_of_is_lt(M.Name.cmp(M.Node.name(n), M.Node.name(x)), e), Comp.and_left(nlow(M.Node.name(x), xs), sorted(xs), h)))),
        h)
    case False{}:
      AL.and_intro(nlow(M.Node.name(x), M.attach(xs, n)), sorted(M.attach(xs, n)),
        low_attach(xs, M.Node.name(x), n, nlt_le(M.Node.name(n), M.Node.name(x), e), Comp.and_left(nlow(M.Node.name(x), xs), sorted(xs), h)),
        ih)

def sorted_attach(t: List<&2, M.Node>, +n: M.Node, +h: {sorted(t) == True{} : Bool}) -> {sorted(M.attach(t, n)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +x <> +xs:
      sorted_attach.at(x, xs, n, Cmp.is_lt(M.Name.cmp(M.Node.name(n), M.Node.name(x))), {==}, h,
        sorted_attach(xs, n, Comp.and_right(nlow(M.Node.name(x), xs), sorted(xs), h)))

def low_mark(l: List<&2, M.Node>, +a: M.Name, +tg: M.Name, +by: Nat) -> {nlow(a, M.mark(l, tg, by)) == nlow(a, l) : Bool}:
  match l:
    case Nil{}:
      {==}
    case +y <> +ys:
      %Equal.sym(M.Name, M.Node.name(M.Node.mark(y, tg, by)), M.Node.name(y), ML.mark_name(y, tg, by)) : {Bool.and(Cmp.is_le(M.Name.cmp(a, _)), nlow(a, M.mark(ys, tg, by))) == Bool.and(Cmp.is_le(M.Name.cmp(a, M.Node.name(y))), nlow(a, ys)) : Bool}
      Equal.cong(Bool, Bool, b => Bool.and(Cmp.is_le(M.Name.cmp(a, M.Node.name(y))), b), nlow(a, M.mark(ys, tg, by)), nlow(a, ys), low_mark(ys, a, tg, by))

def sorted_mark(t: List<&2, M.Node>, +tg: M.Name, +by: Nat, +h: {sorted(t) == True{} : Bool}) -> {sorted(M.mark(t, tg, by)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +x <> +xs:
      %Equal.sym(M.Name, M.Node.name(M.Node.mark(x, tg, by)), M.Node.name(x), ML.mark_name(x, tg, by)) : {Bool.and(nlow(_, M.mark(xs, tg, by)), sorted(M.mark(xs, tg, by))) == True{} : Bool}
      %Equal.sym(Bool, nlow(M.Node.name(x), M.mark(xs, tg, by)), nlow(M.Node.name(x), xs), low_mark(xs, M.Node.name(x), tg, by)) : {Bool.and(_, sorted(M.mark(xs, tg, by))) == True{} : Bool}
      AL.and_intro(nlow(M.Node.name(x), xs), sorted(M.mark(xs, tg, by)),
        Comp.and_left(nlow(M.Node.name(x), xs), sorted(xs), h),
        sorted_mark(xs, tg, by, Comp.and_right(nlow(M.Node.name(x), xs), sorted(xs), h)))

# Removals in index order
# -----------------------

def dlow(+a: Nat, l: List<&2, Nat>) -> Bool:
  match l:
    case Nil{}:
      True{}
    case y <> ys:
      Bool.and(Nat.is_le(a, y), dlow(a, ys))

def dbelow(+a: Nat, l: List<&2, Nat>) -> Bool:
  match l:
    case Nil{}:
      True{}
    case y <> ys:
      Bool.and(Nat.is_lt(a, y), dbelow(a, ys))

def dsorted(d: List<&2, Nat>) -> Bool:
  match d:
    case Nil{}:
      True{}
    case y <> +ys:
      Bool.and(dlow(y, ys), dsorted(ys))

def dbelow_of_lt(+a: Nat, +x: Nat, l: List<&2, Nat>, +h1: {Nat.is_lt(a, x) == True{} : Bool}, +h2: {dlow(x, l) == True{} : Bool}) -> {dbelow(a, l) == True{} : Bool}:
  match l:
    case Nil{}:
      {==}
    case +y <> +ys:
      AL.and_intro(Nat.is_lt(a, y), dbelow(a, ys),
        Lin.lt_le_trans(a, x, y, h1, Comp.and_left(Nat.is_le(x, y), dlow(x, ys), h2)),
        dbelow_of_lt(a, x, ys, h1, Comp.and_right(Nat.is_le(x, y), dlow(x, ys), h2)))

def dlow_of_below(+a: Nat, l: List<&2, Nat>, +h: {dbelow(a, l) == True{} : Bool}) -> {dlow(a, l) == True{} : Bool}:
  match l:
    case Nil{}:
      {==}
    case +y <> +ys:
      AL.and_intro(Nat.is_le(a, y), dlow(a, ys),
        Lin.lt_le(a, y, Comp.and_left(Nat.is_lt(a, y), dbelow(a, ys), h)),
        dlow_of_below(a, ys, Comp.and_right(Nat.is_lt(a, y), dbelow(a, ys), h)))

def dbelow_ins(l: List<&2, Nat>, +by: Nat, h: {dbelow(by, l) == True{} : Bool}) -> {M.ins(l, by) == by <> l : List<&2, Nat>}:
  match l:
    case Nil{}:
      {==}
    case +y <> +ys:
      %Equal.sym(Bool, Nat.is_lt(by, y), True{}, Comp.and_left(Nat.is_lt(by, y), dbelow(by, ys), h)) : {M.ins.put(by, y, ys, M.ins(ys, by), _) == by <> y <> ys : List<&2, Nat>}
      {==}

def dbelow_keep.at(+a: Nat, +y: Nat, +r: List<&2, Nat>, k: Bool, hy: {Nat.is_lt(a, y) == True{} : Bool}, ih: {dbelow(a, r) == True{} : Bool}) -> {dbelow(a, List.filter.put(Nat, y, r, k)) == True{} : Bool}:
  match k:
    case True{}:
      AL.and_intro(Nat.is_lt(a, y), dbelow(a, r), hy, ih)
    case False{}:
      ih

def dbelow_keep(l: List<&2, Nat>, +a: Nat, +S: List<&2, Nat>, +h: {dbelow(a, l) == True{} : Bool}) -> {dbelow(a, M.keep(l, S)) == True{} : Bool}:
  match l:
    case Nil{}:
      {==}
    case +y <> +ys:
      dbelow_keep.at(a, y, M.keep(ys, S), M.has(S, y),
        Comp.and_left(Nat.is_lt(a, y), dbelow(a, ys), h),
        dbelow_keep(ys, a, S, Comp.and_right(Nat.is_lt(a, y), dbelow(a, ys), h)))

def dlow_ins.at(+a: Nat, +y: Nat, +ys: List<&2, Nat>, +by: Nat, lt: Bool, +hn: {Nat.is_le(a, by) == True{} : Bool}, +h: {dlow(a, y <> ys) == True{} : Bool}, ih: {dlow(a, M.ins(ys, by)) == True{} : Bool}) -> {dlow(a, M.ins.put(by, y, ys, M.ins(ys, by), lt)) == True{} : Bool}:
  match lt:
    case True{}:
      AL.and_intro(Nat.is_le(a, by), dlow(a, y <> ys), hn, h)
    case False{}:
      AL.and_intro(Nat.is_le(a, y), dlow(a, M.ins(ys, by)), Comp.and_left(Nat.is_le(a, y), dlow(a, ys), h), ih)

def dlow_ins(l: List<&2, Nat>, +a: Nat, +by: Nat, +hn: {Nat.is_le(a, by) == True{} : Bool}, +h: {dlow(a, l) == True{} : Bool}) -> {dlow(a, M.ins(l, by)) == True{} : Bool}:
  match l:
    case Nil{}:
      AL.and_intro(Nat.is_le(a, by), True{}, hn, {==})
    case +y <> +ys:
      dlow_ins.at(a, y, ys, by, Nat.is_lt(by, y), hn, h,
        dlow_ins(ys, a, by, hn, Comp.and_right(Nat.is_le(a, y), dlow(a, ys), h)))

def dsorted_ins.at(+y: Nat, +ys: List<&2, Nat>, +by: Nat, lt: Bool, +e: {Nat.is_lt(by, y) == lt : Bool}, +h: {dsorted(y <> ys) == True{} : Bool}, ih: {dsorted(M.ins(ys, by)) == True{} : Bool}) -> {dsorted(M.ins.put(by, y, ys, M.ins(ys, by), lt)) == True{} : Bool}:
  match lt:
    case True{}:
      AL.and_intro(dlow(by, y <> ys), dsorted(y <> ys),
        dlow_of_below(by, y <> ys,
          AL.and_intro(Nat.is_lt(by, y), dbelow(by, ys), e,
            dbelow_of_lt(by, y, ys, e, Comp.and_left(dlow(y, ys), dsorted(ys), h)))),
        h)
    case False{}:
      AL.and_intro(dlow(y, M.ins(ys, by)), dsorted(M.ins(ys, by)),
        dlow_ins(ys, y, by, nat_nlt_le(by, y, e), Comp.and_left(dlow(y, ys), dsorted(ys), h)),
        ih)

def dsorted_ins(d: List<&2, Nat>, +by: Nat, +h: {dsorted(d) == True{} : Bool}) -> {dsorted(M.ins(d, by)) == True{} : Bool}:
  match d:
    case Nil{}:
      {==}
    case +y <> +ys:
      dsorted_ins.at(y, ys, by, Nat.is_lt(by, y), {==}, h,
        dsorted_ins(ys, by, Comp.and_right(dlow(y, ys), dsorted(ys), h)))

def dsorted_ins_if(d: List<&2, Nat>, +by: Nat, hit: Bool, h: {dsorted(d) == True{} : Bool}) -> {dsorted(M.ins.if(d, by, hit)) == True{} : Bool}:
  match hit:
    case True{}:
      dsorted_ins(d, by, h)
    case False{}:
      h

def ndels(x: M.Node) -> List<&2, Nat>:
  match x:
    case M.Node{nm, it, pl, d}:
      d

def dall(t: List<&2, M.Node>) -> Bool:
  match t:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(dsorted(ndels(x)), dall(rest))

# What a walk keeps: names in order, and removals in order.
def wf(+t: List<&2, M.Node>) -> Bool:
  Bool.and(sorted(t), dall(t))

def dall_attach.at(+x: M.Node, +xs: List<&2, M.Node>, +n: M.Node, lt: Bool, +hn: {dsorted(ndels(n)) == True{} : Bool}, +h: {dall(x <> xs) == True{} : Bool}, ih: {dall(M.attach(xs, n)) == True{} : Bool}) -> {dall(M.attach.put(n, x, xs, M.attach(xs, n), lt)) == True{} : Bool}:
  match lt:
    case True{}:
      AL.and_intro(dsorted(ndels(n)), dall(x <> xs), hn, h)
    case False{}:
      AL.and_intro(dsorted(ndels(x)), dall(M.attach(xs, n)), Comp.and_left(dsorted(ndels(x)), dall(xs), h), ih)

def dall_attach(t: List<&2, M.Node>, +n: M.Node, +hn: {dsorted(ndels(n)) == True{} : Bool}, +h: {dall(t) == True{} : Bool}) -> {dall(M.attach(t, n)) == True{} : Bool}:
  match t:
    case Nil{}:
      AL.and_intro(dsorted(ndels(n)), True{}, hn, {==})
    case +x <> +xs:
      dall_attach.at(x, xs, n, Cmp.is_lt(M.Name.cmp(M.Node.name(n), M.Node.name(x))), hn, h,
        dall_attach(xs, n, hn, Comp.and_right(dsorted(ndels(x)), dall(xs), h)))

def nmark_dels(x: M.Node, +tg: M.Name, +by: Nat, h: {dsorted(ndels(x)) == True{} : Bool}) -> {dsorted(ndels(M.Node.mark(x, tg, by))) == True{} : Bool}:
  match x:
    case M.Node{+nm, it, pl, d}:
      dsorted_ins_if(d, by, M.Name.eq(nm, tg), h)

def dall_mark(t: List<&2, M.Node>, +tg: M.Name, +by: Nat, +h: {dall(t) == True{} : Bool}) -> {dall(M.mark(t, tg, by)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +x <> +xs:
      AL.and_intro(dsorted(ndels(M.Node.mark(x, tg, by))), dall(M.mark(xs, tg, by)),
        nmark_dels(x, tg, by, Comp.and_left(dsorted(ndels(x)), dall(xs), h)),
        dall_mark(xs, tg, by, Comp.and_right(dsorted(ndels(x)), dall(xs), h)))

def wf_one(+t: List<&2, M.Node>, +by: Nat, act: M.Action, +hw: {wf(t) == True{} : Bool}) -> {wf(M.one(t, by, act)) == True{} : Bool}:
  match act:
    case M.Attach{+m, +it, +pl}:
      AL.and_intro(sorted(M.attach(t, M.Node{M.Name{by, m}, it, pl, Nil{}})), dall(M.attach(t, M.Node{M.Name{by, m}, it, pl, Nil{}})),
        sorted_attach(t, M.Node{M.Name{by, m}, it, pl, Nil{}}, Comp.and_left(sorted(t), dall(t), hw)),
        dall_attach(t, M.Node{M.Name{by, m}, it, pl, Nil{}}, {==}, Comp.and_right(sorted(t), dall(t), hw)))
    case M.Delete{+tg}:
      AL.and_intro(sorted(M.mark(t, tg, by)), dall(M.mark(t, tg, by)),
        sorted_mark(t, tg, by, Comp.and_left(sorted(t), dall(t), hw)),
        dall_mark(t, tg, by, Comp.and_right(sorted(t), dall(t), hw)))

def wf_apply(acts: List<&2, M.Action>, +t: List<&2, M.Node>, +by: Nat, +hw: {wf(t) == True{} : Bool}) -> {wf(M.apply(acts, t, by)) == True{} : Bool}:
  match acts:
    case Nil{}:
      hw
    case +a <> +rest:
      wf_apply(rest, M.one(t, by, a), by, wf_one(t, by, a, hw))

# Restriction commutes with an event's own actions
# -----------------------------------------------

def ncons(+x: M.Node, +y: M.Node, +xs: List<&2, M.Node>, +ys: List<&2, M.Node>, ex: {x == y : M.Node}, ers: {xs == ys : List<&2, M.Node>}) -> {x <> xs == y <> ys : List<&2, M.Node>}:
  Equal.trans(List<&2, M.Node>, x <> xs, y <> xs, y <> ys,
    Equal.cong(M.Node, List<&2, M.Node>, n => n <> xs, x, y, ex),
    Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => y <> l, xs, ys, ers))

def restrict_attach_in.f(+x: M.Node, +xs: List<&2, M.Node>, +a: M.Node, +S: List<&2, Nat>, hx: Bool, e: {Cmp.is_lt(M.Name.cmp(M.Node.name(a), M.Node.name(x))) == False{} : Bool}, ih: {M.restrict(M.attach(xs, a), S) == M.attach(M.restrict(xs, S), M.Node.restrict(a, S)) : List<&2, M.Node>}) -> {List.filter.put(M.Node, M.Node.restrict(x, S), M.restrict(M.attach(xs, a), S), hx) == M.attach(List.filter.put(M.Node, M.Node.restrict(x, S), M.restrict(xs, S), hx), M.Node.restrict(a, S)) : List<&2, M.Node>}:
  match hx:
    case True{}:
      Equal.trans(List<&2, M.Node>, M.Node.restrict(x, S) <> M.restrict(M.attach(xs, a), S), M.Node.restrict(x, S) <> M.attach(M.restrict(xs, S), M.Node.restrict(a, S)), M.attach(M.Node.restrict(x, S) <> M.restrict(xs, S), M.Node.restrict(a, S)),
        Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => M.Node.restrict(x, S) <> l, M.restrict(M.attach(xs, a), S), M.attach(M.restrict(xs, S), M.Node.restrict(a, S)), ih),
        Equal.sym(List<&2, M.Node>, M.attach(M.Node.restrict(x, S) <> M.restrict(xs, S), M.Node.restrict(a, S)), M.Node.restrict(x, S) <> M.attach(M.restrict(xs, S), M.Node.restrict(a, S)),
          attach_nlt(M.Node.restrict(x, S), M.restrict(xs, S), M.Node.restrict(a, S),
            (%Equal.sym(M.Name, M.Node.name(M.Node.restrict(a, S)), M.Node.name(a), rname(a, S)) : {Cmp.is_lt(M.Name.cmp(_, M.Node.name(M.Node.restrict(x, S)))) == False{} : Bool}
              (%Equal.sym(M.Name, M.Node.name(M.Node.restrict(x, S)), M.Node.name(x), rname(x, S)) : {Cmp.is_lt(M.Name.cmp(M.Node.name(a), _)) == False{} : Bool}
                e)))))
    case False{}:
      ih

def restrict_attach_in.at(+x: M.Node, +xs: List<&2, M.Node>, +a: M.Node, +S: List<&2, Nat>, lt: Bool, +e: {Cmp.is_lt(M.Name.cmp(M.Node.name(a), M.Node.name(x))) == lt : Bool}, +ha: {M.has(S, M.Node.author(a)) == True{} : Bool}, +h: {sorted(x <> xs) == True{} : Bool}, ih: {M.restrict(M.attach(xs, a), S) == M.attach(M.restrict(xs, S), M.Node.restrict(a, S)) : List<&2, M.Node>}) -> {M.restrict(M.attach.put(a, x, xs, M.attach(xs, a), lt), S) == M.attach(M.restrict(x <> xs, S), M.Node.restrict(a, S)) : List<&2, M.Node>}:
  match lt:
    case True{}:
      %Equal.sym(Bool, M.has(S, M.Node.author(a)), True{}, ha) : {List.filter.put(M.Node, M.Node.restrict(a, S), M.restrict(x <> xs, S), _) == M.attach(M.restrict(x <> xs, S), M.Node.restrict(a, S)) : List<&2, M.Node>}
      Equal.sym(List<&2, M.Node>, M.attach(M.restrict(x <> xs, S), M.Node.restrict(a, S)), M.Node.restrict(a, S) <> M.restrict(x <> xs, S),
        below_attach(M.restrict(x <> xs, S), M.Node.restrict(a, S),
          below_restrict(x <> xs, M.Node.name(M.Node.restrict(a, S)), S,
            (%Equal.sym(M.Name, M.Node.name(M.Node.restrict(a, S)), M.Node.name(a), rname(a, S)) : {nbelow(_, x <> xs) == True{} : Bool}
              AL.and_intro(Cmp.is_lt(M.Name.cmp(M.Node.name(a), M.Node.name(x))), nbelow(M.Node.name(a), xs), e,
                below_of_lt(M.Node.name(a), M.Node.name(x), xs, ML.cmp_of_is_lt(M.Name.cmp(M.Node.name(a), M.Node.name(x)), e), Comp.and_left(nlow(M.Node.name(x), xs), sorted(xs), h)))))))
    case False{}:
      restrict_attach_in.f(x, xs, a, S, M.has(S, M.Node.author(x)), e, ih)

# An element of an event in the set, attached and then restricted, is
# the restricted element attached to the restriction.
def restrict_attach_in(t: List<&2, M.Node>, +a: M.Node, +S: List<&2, Nat>, +ha: {M.has(S, M.Node.author(a)) == True{} : Bool}, +h: {sorted(t) == True{} : Bool}) -> {M.restrict(M.attach(t, a), S) == M.attach(M.restrict(t, S), M.Node.restrict(a, S)) : List<&2, M.Node>}:
  match t:
    case Nil{}:
      %Equal.sym(Bool, M.has(S, M.Node.author(a)), True{}, ha) : {List.filter.put(M.Node, M.Node.restrict(a, S), Nil{}, _) == M.attach(Nil{}, M.Node.restrict(a, S)) : List<&2, M.Node>}
      {==}
    case +x <> +xs:
      restrict_attach_in.at(x, xs, a, S, Cmp.is_lt(M.Name.cmp(M.Node.name(a), M.Node.name(x))), {==}, ha, h,
        restrict_attach_in(xs, a, S, ha, Comp.and_right(nlow(M.Node.name(x), xs), sorted(xs), h)))

def keep_ins_in.f(+y: Nat, +ys: List<&2, Nat>, +by: Nat, +S: List<&2, Nat>, hy: Bool, e: {Nat.is_lt(by, y) == False{} : Bool}, ih: {M.keep(M.ins(ys, by), S) == M.ins(M.keep(ys, S), by) : List<&2, Nat>}) -> {List.filter.put(Nat, y, M.keep(M.ins(ys, by), S), hy) == M.ins(List.filter.put(Nat, y, M.keep(ys, S), hy), by) : List<&2, Nat>}:
  match hy:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(by, y), False{}, e) : {y <> M.keep(M.ins(ys, by), S) == M.ins.put(by, y, M.keep(ys, S), M.ins(M.keep(ys, S), by), _) : List<&2, Nat>}
      Equal.cong(List<&2, Nat>, List<&2, Nat>, l => y <> l, M.keep(M.ins(ys, by), S), M.ins(M.keep(ys, S), by), ih)
    case False{}:
      ih

def keep_ins_in.at(+y: Nat, +ys: List<&2, Nat>, +by: Nat, +S: List<&2, Nat>, lt: Bool, +e: {Nat.is_lt(by, y) == lt : Bool}, +hb: {M.has(S, by) == True{} : Bool}, +h: {dsorted(y <> ys) == True{} : Bool}, ih: {M.keep(M.ins(ys, by), S) == M.ins(M.keep(ys, S), by) : List<&2, Nat>}) -> {M.keep(M.ins.put(by, y, ys, M.ins(ys, by), lt), S) == M.ins(M.keep(y <> ys, S), by) : List<&2, Nat>}:
  match lt:
    case True{}:
      %Equal.sym(Bool, M.has(S, by), True{}, hb) : {List.filter.put(Nat, by, M.keep(y <> ys, S), _) == M.ins(M.keep(y <> ys, S), by) : List<&2, Nat>}
      Equal.sym(List<&2, Nat>, M.ins(M.keep(y <> ys, S), by), by <> M.keep(y <> ys, S),
        dbelow_ins(M.keep(y <> ys, S), by,
          dbelow_keep(y <> ys, by, S,
            AL.and_intro(Nat.is_lt(by, y), dbelow(by, ys), e,
              dbelow_of_lt(by, y, ys, e, Comp.and_left(dlow(y, ys), dsorted(ys), h))))))
    case False{}:
      keep_ins_in.f(y, ys, by, S, M.has(S, y), e, ih)

# A removal by an event in the set, joined and then restricted, is joined
# to the restriction.
def keep_ins_in(d: List<&2, Nat>, +by: Nat, +S: List<&2, Nat>, +hb: {M.has(S, by) == True{} : Bool}, +h: {dsorted(d) == True{} : Bool}) -> {M.keep(M.ins(d, by), S) == M.ins(M.keep(d, S), by) : List<&2, Nat>}:
  match d:
    case Nil{}:
      %Equal.sym(Bool, M.has(S, by), True{}, hb) : {List.filter.put(Nat, by, Nil{}, _) == M.ins(Nil{}, by) : List<&2, Nat>}
      {==}
    case +y <> +ys:
      keep_ins_in.at(y, ys, by, S, Nat.is_lt(by, y), {==}, hb, h,
        keep_ins_in(ys, by, S, hb, Comp.and_right(dlow(y, ys), dsorted(ys), h)))

def keep_ins_if_in(+d: List<&2, Nat>, +by: Nat, hit: Bool, +S: List<&2, Nat>, hb: {M.has(S, by) == True{} : Bool}, h: {dsorted(d) == True{} : Bool}) -> {M.keep(M.ins.if(d, by, hit), S) == M.ins.if(M.keep(d, S), by, hit) : List<&2, Nat>}:
  match hit:
    case True{}:
      keep_ins_in(d, by, S, hb, h)
    case False{}:
      {==}

def nmark_restrict(x: M.Node, +tg: M.Name, +by: Nat, +S: List<&2, Nat>, hb: {M.has(S, by) == True{} : Bool}, h: {dsorted(ndels(x)) == True{} : Bool}) -> {M.Node.restrict(M.Node.mark(x, tg, by), S) == M.Node.mark(M.Node.restrict(x, S), tg, by) : M.Node}:
  match x:
    case M.Node{+nm, +it, +pl, +d}:
      Equal.cong(List<&2, Nat>, M.Node, l => M.Node{nm, it, pl, l}, M.keep(M.ins.if(d, by, M.Name.eq(nm, tg)), S), M.ins.if(M.keep(d, S), by, M.Name.eq(nm, tg)), keep_ins_if_in(d, by, M.Name.eq(nm, tg), S, hb, h))

def restrict_mark_in.at(+x: M.Node, +xs: List<&2, M.Node>, +tg: M.Name, +by: Nat, +S: List<&2, Nat>, hx: Bool, ex: {M.Node.restrict(M.Node.mark(x, tg, by), S) == M.Node.mark(M.Node.restrict(x, S), tg, by) : M.Node}, ih: {M.restrict(M.mark(xs, tg, by), S) == M.mark(M.restrict(xs, S), tg, by) : List<&2, M.Node>}) -> {List.filter.put(M.Node, M.Node.restrict(M.Node.mark(x, tg, by), S), M.restrict(M.mark(xs, tg, by), S), hx) == M.mark(List.filter.put(M.Node, M.Node.restrict(x, S), M.restrict(xs, S), hx), tg, by) : List<&2, M.Node>}:
  match hx:
    case True{}:
      ncons(M.Node.restrict(M.Node.mark(x, tg, by), S), M.Node.mark(M.Node.restrict(x, S), tg, by), M.restrict(M.mark(xs, tg, by), S), M.mark(M.restrict(xs, S), tg, by), ex, ih)
    case False{}:
      ih

def restrict_mark_in(t: List<&2, M.Node>, +tg: M.Name, +by: Nat, +S: List<&2, Nat>, +hb: {M.has(S, by) == True{} : Bool}, +h: {dall(t) == True{} : Bool}) -> {M.restrict(M.mark(t, tg, by), S) == M.mark(M.restrict(t, S), tg, by) : List<&2, M.Node>}:
  match t:
    case Nil{}:
      {==}
    case +x <> +xs:
      %Equal.sym(Nat, M.Node.author(M.Node.mark(x, tg, by)), M.Node.author(x), ML.mark_author(x, tg, by)) : {List.filter.put(M.Node, M.Node.restrict(M.Node.mark(x, tg, by), S), M.restrict(M.mark(xs, tg, by), S), M.has(S, _)) == M.mark(M.restrict(x <> xs, S), tg, by) : List<&2, M.Node>}
      restrict_mark_in.at(x, xs, tg, by, S, M.has(S, M.Node.author(x)),
        nmark_restrict(x, tg, by, S, hb, Comp.and_left(dsorted(ndels(x)), dall(xs), h)),
        restrict_mark_in(xs, tg, by, S, hb, Comp.and_right(dsorted(ndels(x)), dall(xs), h)))

def restrict_one_in(+t: List<&2, M.Node>, +by: Nat, act: M.Action, +S: List<&2, Nat>, +hb: {M.has(S, by) == True{} : Bool}, +hw: {wf(t) == True{} : Bool}) -> {M.restrict(M.one(t, by, act), S) == M.one(M.restrict(t, S), by, act) : List<&2, M.Node>}:
  match act:
    case M.Attach{+m, +it, +pl}:
      restrict_attach_in(t, M.Node{M.Name{by, m}, it, pl, Nil{}}, S, hb, Comp.and_left(sorted(t), dall(t), hw))
    case M.Delete{+tg}:
      restrict_mark_in(t, tg, by, S, hb, Comp.and_right(sorted(t), dall(t), hw))

# An event in the set: applying its actions and restricting is restricting
# and applying them.
def restrict_apply_in(acts: List<&2, M.Action>, +t: List<&2, M.Node>, +by: Nat, +S: List<&2, Nat>, +hb: {M.has(S, by) == True{} : Bool}, +hw: {wf(t) == True{} : Bool}) -> {M.restrict(M.apply(acts, t, by), S) == M.apply(acts, M.restrict(t, S), by) : List<&2, M.Node>}:
  match acts:
    case Nil{}:
      {==}
    case +a <> +rest:
      Equal.trans(List<&2, M.Node>, M.restrict(M.apply(rest, M.one(t, by, a), by), S), M.apply(rest, M.restrict(M.one(t, by, a), S), by), M.apply(rest, M.one(M.restrict(t, S), by, a), by),
        restrict_apply_in(rest, M.one(t, by, a), by, S, hb, wf_one(t, by, a, hw)),
        Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => M.apply(rest, l, by), M.restrict(M.one(t, by, a), S), M.one(M.restrict(t, S), by, a), restrict_one_in(t, by, a, S, hb, hw)))

# Restricting twice
# -----------------
#
# To a set and then to a subset of it is to the subset: an event's view of
# the restriction is its view of the tree.
def keep_keep.at(+y: Nat, +ys: List<&2, Nat>, +S: List<&2, Nat>, +seen: List<&2, Nat>, hS: Bool, eS: {M.has(S, y) == hS : Bool}, hq: Bool, eq: {M.has(seen, y) == hq : Bool}, +sub: {M.subset(seen, S) == True{} : Bool}, ih: {M.keep(M.keep(ys, S), seen) == M.keep(ys, seen) : List<&2, Nat>}) -> {M.keep(List.filter.put(Nat, y, M.keep(ys, S), hS), seen) == List.filter.put(Nat, y, M.keep(ys, seen), hq) : List<&2, Nat>}:
  match hS hq:
    case True{} True{}:
      %Equal.sym(Bool, M.has(seen, y), True{}, eq) : {List.filter.put(Nat, y, M.keep(M.keep(ys, S), seen), _) == y <> M.keep(ys, seen) : List<&2, Nat>}
      Equal.cong(List<&2, Nat>, List<&2, Nat>, l => y <> l, M.keep(M.keep(ys, S), seen), M.keep(ys, seen), ih)
    case True{} False{}:
      %Equal.sym(Bool, M.has(seen, y), False{}, eq) : {List.filter.put(Nat, y, M.keep(M.keep(ys, S), seen), _) == M.keep(ys, seen) : List<&2, Nat>}
      ih
    case False{} True{}:
      Empty.absurd({M.keep(M.keep(ys, S), seen) == y <> M.keep(ys, seen) : List<&2, Nat>}, Comp.false_true(Equal.trans(Bool, False{}, M.has(S, y), True{}, Equal.sym(Bool, M.has(S, y), False{}, eS), Lin.has_sub(seen, S, y, sub, eq))))
    case False{} False{}:
      ih

def keep_keep(d: List<&2, Nat>, +S: List<&2, Nat>, +seen: List<&2, Nat>, +sub: {M.subset(seen, S) == True{} : Bool}) -> {M.keep(M.keep(d, S), seen) == M.keep(d, seen) : List<&2, Nat>}:
  match d:
    case Nil{}:
      {==}
    case +y <> +ys:
      keep_keep.at(y, ys, S, seen, M.has(S, y), {==}, M.has(seen, y), {==}, sub, keep_keep(ys, S, seen, sub))

def nrr(x: M.Node, +S: List<&2, Nat>, +seen: List<&2, Nat>, +sub: {M.subset(seen, S) == True{} : Bool}) -> {M.Node.restrict(M.Node.restrict(x, S), seen) == M.Node.restrict(x, seen) : M.Node}:
  match x:
    case M.Node{+nm, +it, +pl, +d}:
      Equal.cong(List<&2, Nat>, M.Node, l => M.Node{nm, it, pl, l}, M.keep(M.keep(d, S), seen), M.keep(d, seen), keep_keep(d, S, seen, sub))

def rr.at(+x: M.Node, +xs: List<&2, M.Node>, +S: List<&2, Nat>, +seen: List<&2, Nat>, hS: Bool, eS: {M.has(S, M.Node.author(x)) == hS : Bool}, hq: Bool, eq: {M.has(seen, M.Node.author(x)) == hq : Bool}, +sub: {M.subset(seen, S) == True{} : Bool}, ih: {M.restrict(M.restrict(xs, S), seen) == M.restrict(xs, seen) : List<&2, M.Node>}) -> {M.restrict(List.filter.put(M.Node, M.Node.restrict(x, S), M.restrict(xs, S), hS), seen) == List.filter.put(M.Node, M.Node.restrict(x, seen), M.restrict(xs, seen), hq) : List<&2, M.Node>}:
  match hS hq:
    case True{} True{}:
      %Equal.sym(Nat, M.Node.author(M.Node.restrict(x, S)), M.Node.author(x), ML.restrict_author(x, S)) : {List.filter.put(M.Node, M.Node.restrict(M.Node.restrict(x, S), seen), M.restrict(M.restrict(xs, S), seen), M.has(seen, _)) == M.Node.restrict(x, seen) <> M.restrict(xs, seen) : List<&2, M.Node>}
      %Equal.sym(Bool, M.has(seen, M.Node.author(x)), True{}, eq) : {List.filter.put(M.Node, M.Node.restrict(M.Node.restrict(x, S), seen), M.restrict(M.restrict(xs, S), seen), _) == M.Node.restrict(x, seen) <> M.restrict(xs, seen) : List<&2, M.Node>}
      ncons(M.Node.restrict(M.Node.restrict(x, S), seen), M.Node.restrict(x, seen), M.restrict(M.restrict(xs, S), seen), M.restrict(xs, seen), nrr(x, S, seen, sub), ih)
    case True{} False{}:
      %Equal.sym(Nat, M.Node.author(M.Node.restrict(x, S)), M.Node.author(x), ML.restrict_author(x, S)) : {List.filter.put(M.Node, M.Node.restrict(M.Node.restrict(x, S), seen), M.restrict(M.restrict(xs, S), seen), M.has(seen, _)) == M.restrict(xs, seen) : List<&2, M.Node>}
      %Equal.sym(Bool, M.has(seen, M.Node.author(x)), False{}, eq) : {List.filter.put(M.Node, M.Node.restrict(M.Node.restrict(x, S), seen), M.restrict(M.restrict(xs, S), seen), _) == M.restrict(xs, seen) : List<&2, M.Node>}
      ih
    case False{} True{}:
      Empty.absurd({M.restrict(M.restrict(xs, S), seen) == M.Node.restrict(x, seen) <> M.restrict(xs, seen) : List<&2, M.Node>}, Comp.false_true(Equal.trans(Bool, False{}, M.has(S, M.Node.author(x)), True{}, Equal.sym(Bool, M.has(S, M.Node.author(x)), False{}, eS), Lin.has_sub(seen, S, M.Node.author(x), sub, eq))))
    case False{} False{}:
      ih

def restrict_restrict(t: List<&2, M.Node>, +S: List<&2, Nat>, +seen: List<&2, Nat>, +sub: {M.subset(seen, S) == True{} : Bool}) -> {M.restrict(M.restrict(t, S), seen) == M.restrict(t, seen) : List<&2, M.Node>}:
  match t:
    case Nil{}:
      {==}
    case +x <> +xs:
      rr.at(x, xs, S, seen, M.has(S, M.Node.author(x)), {==}, M.has(seen, M.Node.author(x)), {==}, sub, restrict_restrict(xs, S, seen, sub))

def actions_restrict(+t: List<&2, M.Node>, +S: List<&2, Nat>, +seen: List<&2, Nat>, +e: Nat, +ops: List<&2, Ops.Op>, +sub: {M.subset(seen, S) == True{} : Bool}) -> {M.actions(M.restrict(t, S), seen, e, ops) == M.actions(t, seen, e, ops) : Maybe<&2, List<&2, M.Action>>}:
  Equal.cong(List<&2, M.Node>, Maybe<&2, List<&2, M.Action>>, +v => M.run.acts(M.run(ops, Some{M.Running{v, 0n, Nil{}}}, e, M.visible(v))), M.restrict(M.restrict(t, S), seen), M.restrict(t, seen), restrict_restrict(t, S, seen, sub))

# The set's own walk
# ------------------
#
# The events of an order that are in the set, in the order's order.
def only(o: List<&2, Nat>, +S: List<&2, Nat>) -> List<&2, Nat>:
  match o:
    case Nil{}:
      Nil{}
    case +x <> xs:
      List.filter.put(Nat, x, only(xs, S), M.has(S, x))

def has_only.at(+y: Nat, +ys: List<&2, Nat>, +S: List<&2, Nat>, +x: Nat, k: Bool, hy: {Nat.is_eq(y, x) == False{} : Bool}, ih: {M.has(only(ys, S), x) == False{} : Bool}) -> {M.has(List.filter.put(Nat, y, only(ys, S), k), x) == False{} : Bool}:
  match k:
    case True{}:
      AL.or_false(Nat.is_eq(y, x), M.has(only(ys, S), x), hy, ih)
    case False{}:
      ih

def has_only_false(xs: List<&2, Nat>, +S: List<&2, Nat>, +x: Nat, +h: {M.has(xs, x) == False{} : Bool}) -> {M.has(only(xs, S), x) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +ys:
      has_only.at(y, ys, S, x, M.has(S, y), AL.or_false_l(Nat.is_eq(y, x), M.has(ys, x), h), has_only_false(ys, S, x, AL.or_false_r(Nat.is_eq(y, x), M.has(ys, x), h)))

def distinct_only.at(+x: Nat, +xs: List<&2, Nat>, +S: List<&2, Nat>, k: Bool, nx: {M.has(xs, x) == False{} : Bool}, ih: {M.distinct(only(xs, S)) == True{} : Bool}) -> {M.distinct(List.filter.put(Nat, x, only(xs, S), k)) == True{} : Bool}:
  match k:
    case True{}:
      AL.and_intro(Bool.not(M.has(only(xs, S), x)), M.distinct(only(xs, S)), AL.not_true(M.has(only(xs, S), x), has_only_false(xs, S, x, nx)), ih)
    case False{}:
      ih

def distinct_only(o: List<&2, Nat>, +S: List<&2, Nat>, +h: {M.distinct(o) == True{} : Bool}) -> {M.distinct(only(o, S)) == True{} : Bool}:
  match o:
    case Nil{}:
      {==}
    case +x <> +xs:
      distinct_only.at(x, xs, S, M.has(S, x),
        AL.not_of_true(M.has(xs, x), Comp.and_left(Bool.not(M.has(xs, x)), M.distinct(xs), h)),
        distinct_only(xs, S, Comp.and_right(Bool.not(M.has(xs, x)), M.distinct(xs), h)))

def closed_has.at(+y: Nat, +ys: List<&2, Nat>, +g: List<&2, M.Rev>, +s: List<&2, Nat>, +x: Nat, b: Bool, eb: {Nat.is_eq(y, x) == b : Bool}, +hc: {Bool.and(M.subset(M.past(g, y), s), M.closed(ys, g, s)) == True{} : Bool}, h: {Bool.or(b, M.has(ys, x)) == True{} : Bool}, ih: {M.has(ys, x) == True{} : Bool} -> {M.subset(M.past(g, x), s) == True{} : Bool}) -> {M.subset(M.past(g, x), s) == True{} : Bool}:
  match b:
    case True{}:
      %ML.nat_eq(y, x, eb) : {M.subset(M.past(g, _), s) == True{} : Bool}
      Comp.and_left(M.subset(M.past(g, y), s), M.closed(ys, g, s), hc)
    case False{}:
      ih(h)

# An event of a closed set had seen only events in it.
def closed_has(xs: List<&2, Nat>, +g: List<&2, M.Rev>, +s: List<&2, Nat>, +x: Nat, +hc: {M.closed(xs, g, s) == True{} : Bool}, h: {M.has(xs, x) == True{} : Bool}) -> {M.subset(M.past(g, x), s) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({M.subset(M.past(g, x), s) == True{} : Bool}, Comp.false_true(h))
    case +y <> +ys:
      closed_has.at(y, ys, g, s, x, Nat.is_eq(y, x), {==}, hc, h,
        h2 => closed_has(ys, g, s, x, Comp.and_right(M.subset(M.past(g, y), s), M.closed(ys, g, s), hc), h2))

def mdisc(m: Maybe<&2, List<&2, M.Node>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{t}:
      Empty

def walk_refused(+rest: List<&2, Nat>, +g: List<&2, M.Rev>, -t: List<&2, M.Node>, e: {M.walk(rest, g, None{}) == Some{t} : Maybe<&2, List<&2, M.Node>>}) -> Empty:
  %Equal.trans(Maybe<&2, List<&2, M.Node>>, None{}, M.walk(rest, g, None{}), Some{t}, Equal.sym(Maybe<&2, List<&2, M.Node>>, M.walk(rest, g, None{}), None{}, Walk.walk_none(rest, g)), e) : {mdisc(_) : Type}
  Unit{}

def mtree(m: Maybe<&2, List<&2, M.Node>>) -> List<&2, M.Node>:
  match m:
    case None{}:
      Nil{}
    case Some{t}:
      t

# An event that stated something: in the set, it decides on the restriction
# what it decided on the tree, and its actions commute with restricting; out
# of it, the restriction does not see them.
def wr.acts(m: Maybe<&2, List<&2, M.Action>>, hs: Bool, +rest: List<&2, Nat>, +g: List<&2, M.Rev>, +S: List<&2, Nat>, +x: Nat, +t0: List<&2, M.Node>, +t: List<&2, M.Node>, +seen: List<&2, Nat>, +ops: List<&2, Ops.Op>, +eqev: {List.get(&2, M.Rev, g, x) == Some{M.Rev{seen, Some{ops}}} : Maybe<&2, M.Rev>}, +eqm: {M.actions(t0, seen, x, ops) == m : Maybe<&2, List<&2, M.Action>>}, +eqs: {M.has(S, x) == hs : Bool}, +hw: {wf(t0) == True{} : Bool}, +hc: {M.closed(S, g, S) == True{} : Bool}, e: {M.walk(rest, g, M.step.of(t0, x, m)) == Some{t} : Maybe<&2, List<&2, M.Node>>}, ih: @u: List<&2, M.Node> -> {wf(u) == True{} : Bool} -> {M.walk(rest, g, Some{u}) == Some{t} : Maybe<&2, List<&2, M.Node>>} -> {M.walk(only(rest, S), g, Some{M.restrict(u, S)}) == Some{M.restrict(t, S)} : Maybe<&2, List<&2, M.Node>>}) -> {M.walk(List.filter.put(Nat, x, only(rest, S), hs), g, Some{M.restrict(t0, S)}) == Some{M.restrict(t, S)} : Maybe<&2, List<&2, M.Node>>}:
  match m hs:
    case None{} True{}:
      Empty.absurd({M.walk(x <> only(rest, S), g, Some{M.restrict(t0, S)}) == Some{M.restrict(t, S)} : Maybe<&2, List<&2, M.Node>>}, walk_refused(rest, g, t, e))
    case None{} False{}:
      Empty.absurd({M.walk(only(rest, S), g, Some{M.restrict(t0, S)}) == Some{M.restrict(t, S)} : Maybe<&2, List<&2, M.Node>>}, walk_refused(rest, g, t, e))
    case Some{+acts} True{}:
      %Equal.sym(Maybe<&2, M.Rev>, List.get(&2, M.Rev, g, x), Some{M.Rev{seen, Some{ops}}}, eqev) : {M.walk(only(rest, S), g, M.step.m(Some{M.restrict(t0, S)}, _, x)) == Some{M.restrict(t, S)} : Maybe<&2, List<&2, M.Node>>}
      %Equal.sym(Maybe<&2, List<&2, M.Action>>, M.actions(M.restrict(t0, S), seen, x, ops), Some{acts},
        Equal.trans(Maybe<&2, List<&2, M.Action>>, M.actions(M.restrict(t0, S), seen, x, ops), M.actions(t0, seen, x, ops), Some{acts},
          actions_restrict(t0, S, seen, x, ops,
            (%eqev : {M.subset(M.Rev.past(_), S) == True{} : Bool}
              closed_has(S, g, S, x, hc, eqs))),
          eqm)) : {M.walk(only(rest, S), g, M.step.of(M.restrict(t0, S), x, _)) == Some{M.restrict(t, S)} : Maybe<&2, List<&2, M.Node>>}
      %restrict_apply_in(acts, t0, x, S, eqs, hw) : {M.walk(only(rest, S), g, Some{_}) == Some{M.restrict(t, S)} : Maybe<&2, List<&2, M.Node>>}
      ih(M.apply(acts, t0, x), wf_apply(acts, t0, x, hw), e)
    case Some{+acts} False{}:
      %ML.restrict_apply(acts, t0, x, S, eqs) : {M.walk(only(rest, S), g, Some{_}) == Some{M.restrict(t, S)} : Maybe<&2, List<&2, M.Node>>}
      ih(M.apply(acts, t0, x), wf_apply(acts, t0, x, hw), e)

def wr.none(hs: Bool, +rest: List<&2, Nat>, +g: List<&2, M.Rev>, +S: List<&2, Nat>, +x: Nat, +t0: List<&2, M.Node>, +t: List<&2, M.Node>, +seen: List<&2, Nat>, +eqev: {List.get(&2, M.Rev, g, x) == Some{M.Rev{seen, None{}}} : Maybe<&2, M.Rev>}, +hw: {wf(t0) == True{} : Bool}, e: {M.walk(rest, g, Some{t0}) == Some{t} : Maybe<&2, List<&2, M.Node>>}, ih: @u: List<&2, M.Node> -> {wf(u) == True{} : Bool} -> {M.walk(rest, g, Some{u}) == Some{t} : Maybe<&2, List<&2, M.Node>>} -> {M.walk(only(rest, S), g, Some{M.restrict(u, S)}) == Some{M.restrict(t, S)} : Maybe<&2, List<&2, M.Node>>}) -> {M.walk(List.filter.put(Nat, x, only(rest, S), hs), g, Some{M.restrict(t0, S)}) == Some{M.restrict(t, S)} : Maybe<&2, List<&2, M.Node>>}:
  match hs:
    case True{}:
      %Equal.sym(Maybe<&2, M.Rev>, List.get(&2, M.Rev, g, x), Some{M.Rev{seen, None{}}}, eqev) : {M.walk(only(rest, S), g, M.step.m(Some{M.restrict(t0, S)}, _, x)) == Some{M.restrict(t, S)} : Maybe<&2, List<&2, M.Node>>}
      ih(t0, hw, e)
    case False{}:
      ih(t0, hw, e)

def wr.ev(ev: Maybe<&2, M.Rev>, hs: Bool, +rest: List<&2, Nat>, +g: List<&2, M.Rev>, +S: List<&2, Nat>, +x: Nat, +t0: List<&2, M.Node>, +t: List<&2, M.Node>, +eqev: {List.get(&2, M.Rev, g, x) == ev : Maybe<&2, M.Rev>}, eqs: {M.has(S, x) == hs : Bool}, +hw: {wf(t0) == True{} : Bool}, +hc: {M.closed(S, g, S) == True{} : Bool}, e: {M.walk(rest, g, M.step(ev, t0, x)) == Some{t} : Maybe<&2, List<&2, M.Node>>}, ih: @u: List<&2, M.Node> -> {wf(u) == True{} : Bool} -> {M.walk(rest, g, Some{u}) == Some{t} : Maybe<&2, List<&2, M.Node>>} -> {M.walk(only(rest, S), g, Some{M.restrict(u, S)}) == Some{M.restrict(t, S)} : Maybe<&2, List<&2, M.Node>>}) -> {M.walk(List.filter.put(Nat, x, only(rest, S), hs), g, Some{M.restrict(t0, S)}) == Some{M.restrict(t, S)} : Maybe<&2, List<&2, M.Node>>}:
  match ev:
    case None{}:
      Empty.absurd({M.walk(List.filter.put(Nat, x, only(rest, S), hs), g, Some{M.restrict(t0, S)}) == Some{M.restrict(t, S)} : Maybe<&2, List<&2, M.Node>>}, walk_refused(rest, g, t, e))
    case Some{M.Rev{+seen, None{}}}:
      wr.none(hs, rest, g, S, x, t0, t, seen, eqev, hw, e, ih)
    case Some{M.Rev{+seen, Some{+ops}}}:
      wr.acts(M.actions(t0, seen, x, ops), hs, rest, g, S, x, t0, t, seen, ops, eqev, {==}, eqs, hw, hc, e, ih)

# Walking only the set's events, from the restriction of where the walk
# started, reaches the restriction of where it ended.
def wr(o: List<&2, Nat>, +g: List<&2, M.Rev>, +S: List<&2, Nat>, +t0: List<&2, M.Node>, +t: List<&2, M.Node>, +hw: {wf(t0) == True{} : Bool}, +hc: {M.closed(S, g, S) == True{} : Bool}, e: {M.walk(o, g, Some{t0}) == Some{t} : Maybe<&2, List<&2, M.Node>>}) -> {M.walk(only(o, S), g, Some{M.restrict(t0, S)}) == Some{M.restrict(t, S)} : Maybe<&2, List<&2, M.Node>>}:
  match o:
    case Nil{}:
      Equal.cong(List<&2, M.Node>, Maybe<&2, List<&2, M.Node>>, l => Some{M.restrict(l, S)}, t0, t,
        Equal.cong(Maybe<&2, List<&2, M.Node>>, List<&2, M.Node>, m => mtree(m), Some{t0}, Some{t}, e))
    case +x <> +rest:
      wr.ev(List.get(&2, M.Rev, g, x), M.has(S, x), rest, g, S, x, t0, t, {==}, {==}, hw, hc, e,
        u => hu => eu => wr(rest, g, S, u, t, hu, hc, eu))

# The theorem: restricted to a set of events that holds the past of each,
# any tree a walk builds keeps the invariant.
def view_invariant(+g: List<&2, M.Rev>, +o: List<&2, Nat>, +t: List<&2, M.Node>, +S: List<&2, Nat>, +hd: {M.distinct(o) == True{} : Bool}, +hc: {M.closed(S, g, S) == True{} : Bool}, e: {M.walk(o, g, Some{Nil{}}) == Some{t} : Maybe<&2, List<&2, M.Node>>}) -> {M.invariant(M.restrict(t, S)) == True{} : Bool}:
  Walk.walk_invariant_c(g, only(o, S), M.restrict(t, S), distinct_only(o, S, hd), wr(o, g, S, Nil{}, t, {==}, hc, e))

# An event applies its document to what its author saw
# -----------------------------------------------------

def subset_only.at(+x: Nat, +xs: List<&2, Nat>, +S: List<&2, Nat>, k: Bool, ek: {M.has(S, x) == k : Bool}, ih: {M.subset(only(xs, S), S) == True{} : Bool}) -> {M.subset(List.filter.put(Nat, x, only(xs, S), k), S) == True{} : Bool}:
  match k:
    case True{}:
      AL.and_intro(M.has(S, x), M.subset(only(xs, S), S), ek, ih)
    case False{}:
      ih

def subset_only(o: List<&2, Nat>, +S: List<&2, Nat>) -> {M.subset(only(o, S), S) == True{} : Bool}:
  match o:
    case Nil{}:
      {==}
    case +x <> +xs:
      subset_only.at(x, xs, S, M.has(S, x), {==}, subset_only(xs, S))

def wf_m(m: Maybe<&2, List<&2, M.Action>>, +rest: List<&2, Nat>, +g: List<&2, M.Rev>, +t0: List<&2, M.Node>, +x: Nat, +t: List<&2, M.Node>, +hw: {wf(t0) == True{} : Bool}, e: {M.walk(rest, g, M.step.of(t0, x, m)) == Some{t} : Maybe<&2, List<&2, M.Node>>}, ih: @u: List<&2, M.Node> -> {wf(u) == True{} : Bool} -> {M.walk(rest, g, Some{u}) == Some{t} : Maybe<&2, List<&2, M.Node>>} -> {wf(t) == True{} : Bool}) -> {wf(t) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({wf(t) == True{} : Bool}, walk_refused(rest, g, t, e))
    case Some{+acts}:
      ih(M.apply(acts, t0, x), wf_apply(acts, t0, x, hw), e)

def wf_ev(ev: Maybe<&2, M.Rev>, +rest: List<&2, Nat>, +g: List<&2, M.Rev>, +t0: List<&2, M.Node>, +x: Nat, +t: List<&2, M.Node>, +hw: {wf(t0) == True{} : Bool}, e: {M.walk(rest, g, M.step(ev, t0, x)) == Some{t} : Maybe<&2, List<&2, M.Node>>}, ih: @u: List<&2, M.Node> -> {wf(u) == True{} : Bool} -> {M.walk(rest, g, Some{u}) == Some{t} : Maybe<&2, List<&2, M.Node>>} -> {wf(t) == True{} : Bool}) -> {wf(t) == True{} : Bool}:
  match ev:
    case None{}:
      Empty.absurd({wf(t) == True{} : Bool}, walk_refused(rest, g, t, e))
    case Some{M.Rev{seen, None{}}}:
      ih(t0, hw, e)
    case Some{M.Rev{+seen, Some{+ops}}}:
      wf_m(M.actions(t0, seen, x, ops), rest, g, t0, x, t, hw, e, ih)

# Every tree a walk builds is in name order, its removals in index order.
def walk_wf(o: List<&2, Nat>, +g: List<&2, M.Rev>, +t0: List<&2, M.Node>, +t: List<&2, M.Node>, +hw: {wf(t0) == True{} : Bool}, e: {M.walk(o, g, Some{t0}) == Some{t} : Maybe<&2, List<&2, M.Node>>}) -> {wf(t) == True{} : Bool}:
  match o:
    case Nil{}:
      (%Equal.cong(Maybe<&2, List<&2, M.Node>>, List<&2, M.Node>, m => mtree(m), Some{t0}, Some{t}, e) : {wf(_) == True{} : Bool}
        hw)
    case +x <> +rest:
      wf_ev(List.get(&2, M.Rev, g, x), rest, g, t0, x, t, hw, e,
        u => hu => eu => walk_wf(rest, g, u, t, hu, eu))

# A tree no element or removal of which is by `e`: restricting it to a set
# with `e` added is restricting it to the set.
def keep_absent(d: List<&2, Nat>, +W: List<&2, Nat>, +e: Nat, +S: List<&2, Nat>, +hk: {M.has(W, e) == False{} : Bool}, +h: {Lin.all_has(d, W) == True{} : Bool}) -> {M.keep(d, e <> S) == M.keep(d, S) : List<&2, Nat>}:
  match d:
    case Nil{}:
      {==}
    case +y <> +ys:
      %Equal.sym(Bool, Nat.is_eq(e, y), False{}, ML.ne_of_has(W, e, y, hk, Comp.and_left(M.has(W, y), Lin.all_has(ys, W), h))) : {List.filter.put(Nat, y, M.keep(ys, e <> S), Bool.or(_, M.has(S, y))) == List.filter.put(Nat, y, M.keep(ys, S), M.has(S, y)) : List<&2, Nat>}
      Equal.cong(List<&2, Nat>, List<&2, Nat>, l => List.filter.put(Nat, y, l, M.has(S, y)), M.keep(ys, e <> S), M.keep(ys, S), keep_absent(ys, W, e, S, hk, Comp.and_right(M.has(W, y), Lin.all_has(ys, W), h)))

def node_absent(x: M.Node, +W: List<&2, Nat>, +e: Nat, +S: List<&2, Nat>, +hk: {M.has(W, e) == False{} : Bool}, h: {Lin.inw.node(x, W) == True{} : Bool}) -> {M.Node.restrict(x, e <> S) == M.Node.restrict(x, S) : M.Node}:
  match x:
    case M.Node{+nm, +it, M.Place{+p, +r}, +d}:
      Equal.cong(List<&2, Nat>, M.Node, l => M.Node{nm, it, M.Place{p, r}, l}, M.keep(d, e <> S), M.keep(d, S),
        keep_absent(d, W, e, S, hk, Comp.and_right(Lin.inw.m(p, W), Lin.all_has(d, W), Comp.and_right(Lin.inw.n(nm, W), Bool.and(Lin.inw.m(p, W), Lin.all_has(d, W)), h))))

def author_absent(x: M.Node, +W: List<&2, Nat>, +e: Nat, +hk: {M.has(W, e) == False{} : Bool}, h: {Lin.inw.node(x, W) == True{} : Bool}) -> {Nat.is_eq(e, M.Node.author(x)) == False{} : Bool}:
  match x:
    case M.Node{M.Name{+a, +o}, it, M.Place{+p, r}, +d}:
      ML.ne_of_has(W, e, a, hk, Comp.and_left(Lin.inw.n(M.Name{a, o}, W), Bool.and(Lin.inw.m(p, W), Lin.all_has(d, W)), h))

def restrict_absent(t: List<&2, M.Node>, +W: List<&2, Nat>, +e: Nat, +S: List<&2, Nat>, +hk: {M.has(W, e) == False{} : Bool}, +h: {Lin.inw(t, W) == True{} : Bool}) -> {M.restrict(t, e <> S) == M.restrict(t, S) : List<&2, M.Node>}:
  match t:
    case Nil{}:
      {==}
    case +x <> +xs:
      %Equal.sym(Bool, Nat.is_eq(e, M.Node.author(x)), False{}, author_absent(x, W, e, hk, Comp.and_left(Lin.inw.node(x, W), Lin.inw(xs, W), h))) : {List.filter.put(M.Node, M.Node.restrict(x, e <> S), M.restrict(xs, e <> S), Bool.or(_, M.has(S, M.Node.author(x)))) == M.restrict(x <> xs, S) : List<&2, M.Node>}
      %Equal.sym(M.Node, M.Node.restrict(x, e <> S), M.Node.restrict(x, S), node_absent(x, W, e, S, hk, Comp.and_left(Lin.inw.node(x, W), Lin.inw(xs, W), h))) : {List.filter.put(M.Node, _, M.restrict(xs, e <> S), M.has(S, M.Node.author(x))) == M.restrict(x <> xs, S) : List<&2, M.Node>}
      Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => List.filter.put(M.Node, M.Node.restrict(x, S), l, M.has(S, M.Node.author(x))), M.restrict(xs, e <> S), M.restrict(xs, S), restrict_absent(xs, W, e, S, hk, Comp.and_right(Lin.inw.node(x, W), Lin.inw(xs, W), h)))

def intent_at(m: Maybe<&2, List<&2, M.Action>>, +t: List<&2, M.Node>, +e: Nat, +past: List<&2, Nat>, +f1: List<&2, Ops.Item>, +hw: {wf(t) == True{} : Bool}, +hr: {M.restrict(t, e <> past) == M.restrict(t, past) : List<&2, M.Node>}, ext: {M.merged.of(M.step.of(M.restrict(t, past), e, m)) == Some{f1} : Maybe<&2, List<&2, Ops.Item>>}) -> {M.seen_file(M.step.of(t, e, m), e <> past) == Some{f1} : Maybe<&2, List<&2, Ops.Item>>}:
  match m:
    case None{}:
      Empty.absurd({M.seen_file(None{}, e <> past) == Some{f1} : Maybe<&2, List<&2, Ops.Item>>}, Comp.false_true(Equal.cong(Maybe<&2, List<&2, Ops.Item>>, Bool, x => Walk.mis(x), None{}, Some{f1}, ext)))
    case Some{+acts}:
      %Equal.sym(List<&2, M.Node>, M.restrict(M.apply(acts, t, e), e <> past), M.apply(acts, M.restrict(t, e <> past), e), restrict_apply_in(acts, t, e, e <> past, AL.or_left(Nat.is_eq(e, e), M.has(past, e), Comp.eq_refl(e)), hw)) : {Some{M.file(_)} == Some{f1} : Maybe<&2, List<&2, Ops.Item>>}
      %Equal.sym(List<&2, M.Node>, M.restrict(t, e <> past), M.restrict(t, past), hr) : {Some{M.file(M.apply(acts, _, e))} == Some{f1} : Maybe<&2, List<&2, Ops.Item>>}
      ext

# The theorem. Walk any history `p` to `t`, and an event outside it whose
# author had seen the closed set `past`: what that author saw is the file
# of `t` restricted to `past`, and if their document applies to it, their
# view once the event is walked reads what it applied to — whatever else
# `p` holds that they had not seen.
def merge_intent_c(+g: List<&2, M.Rev>, +p: List<&2, Nat>, +e: Nat, +past: List<&2, Nat>, +d: List<&2, Ops.Op>, +t: List<&2, M.Node>, +f1: List<&2, Ops.Item>, +hd: {M.distinct(p) == True{} : Bool}, +he: {M.has(p, e) == False{} : Bool}, +hc: {M.closed(past, g, past) == True{} : Bool}, +hg: {List.get(&2, M.Rev, g, e) == Some{M.Rev{past, Some{d}}} : Maybe<&2, M.Rev>}, +ho: {Block.ordered_all(d, None{}, None{}) == True{} : Bool}, +hw: {M.walk(p, g, Some{Nil{}}) == Some{t} : Maybe<&2, List<&2, M.Node>>}, +ha: {Cursor.apply(M.file(M.restrict(t, past)), Ops.Doc{None{}, None{}, d}) == Done{f1} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {M.seen_file(M.walk(List.append(&2, Nat, p, [e]), g, Some{Nil{}}), e <> past) == Some{f1} : Maybe<&2, List<&2, Ops.Item>>}:
  %Equal.sym(Maybe<&2, List<&2, M.Node>>, M.walk(List.append(&2, Nat, p, [e]), g, Some{Nil{}}), M.step.m(M.walk(p, g, Some{Nil{}}), List.get(&2, M.Rev, g, e), e), ML.walk_append(p, e, g, Some{Nil{}})) : {M.seen_file(_, e <> past) == Some{f1} : Maybe<&2, List<&2, Ops.Item>>}
  %Equal.sym(Maybe<&2, List<&2, M.Node>>, M.walk(p, g, Some{Nil{}}), Some{t}, hw) : {M.seen_file(M.step.m(_, List.get(&2, M.Rev, g, e), e), e <> past) == Some{f1} : Maybe<&2, List<&2, Ops.Item>>}
  %Equal.sym(Maybe<&2, M.Rev>, List.get(&2, M.Rev, g, e), Some{M.Rev{past, Some{d}}}, hg) : {M.seen_file(M.step.m(Some{t}, _, e), e <> past) == Some{f1} : Maybe<&2, List<&2, Ops.Item>>}
  intent_at(M.actions(t, past, e, d), t, e, past, f1,
    walk_wf(p, g, Nil{}, t, {==}, hw),
    restrict_absent(t, Walk.revapp(p, Nil{}), e, past, Walk.has_revapp_false(p, Nil{}, e, he, {==}),
      Comp.and_right(M.invariant(t), Lin.inw(t, Walk.revapp(p, Nil{})),
        (%hw : {Walk.wok(_, Walk.revapp(p, Nil{})) == True{} : Bool}
          Walk.walk_ok(p, g, Nil{}, Nil{}, AL.invariant_nil(), {==}, hd, Walk.nk_nil(p))))),
    (%actions_restrict(t, past, past, e, d, Walk.subset_refl_n(past)) : {M.merged.of(M.step.of(M.restrict(t, past), e, _)) == Some{f1} : Maybe<&2, List<&2, Ops.Item>>}
      (%hg : {M.merged.of(M.step.m(Some{M.restrict(t, past)}, _, e)) == Some{f1} : Maybe<&2, List<&2, Ops.Item>>}
        (%wr(p, g, past, Nil{}, t, {==}, hc, hw) : {M.merged.of(M.step.m(_, List.get(&2, M.Rev, g, e), e)) == Some{f1} : Maybe<&2, List<&2, Ops.Item>>}
          (%ML.walk_append(only(p, past), e, g, Some{Nil{}}) : {M.merged.of(_) == Some{f1} : Maybe<&2, List<&2, Ops.Item>>}
            Walk.merge_extends_c(g, only(p, past), e, past, d, M.file(M.restrict(t, past)), f1,
              distinct_only(p, past, hd), has_only_false(p, past, e, he), subset_only(p, past), hg, ho,
              Equal.cong(Maybe<&2, List<&2, M.Node>>, Maybe<&2, List<&2, Ops.Item>>, m => M.merged.of(m), M.walk(only(p, past), g, Some{Nil{}}), Some{M.restrict(t, past)}, wr(p, g, past, Nil{}, t, {==}, hc, hw)),
              ha))))))

def main() -> Unit:
  Unit{}
