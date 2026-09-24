# The anchor: one fresh insertion, placed by Fugue's rule on a view that
# satisfies the reachable-state invariant, is read at the visible gap its
# author asked for — tombstones or not. The argument: the anchor's place
# has no child yet, so the attach adds one element and changes no other
# sibling list; the reading of the new tree is the old reading with that
# element spliced beside its parent; and the parent is either the element
# the insert follows or the next element read after it, which is where
# the tombstone-aware descent (`leftmost`) put it.
import Base
import ./ops.bend as Ops
import ./merge.bend as M
import ./composition_lemmas.bend as Comp
import ./string_lemmas.bend as S
import ./merge_lemmas.bend as ML

# Bool and names
# --------------

def bool_cases(-R: Type, b: Bool, t: {b == True{} : Bool} -> R, f: {b == False{} : Bool} -> R) -> R:
  match b:
    case True{}:
      t({==})
    case False{}:
      f({==})

def or_cases(-R: Type, a: Bool, b: Bool, e: {Bool.or(a, b) == True{} : Bool}, l: {a == True{} : Bool} -> R, r: {b == True{} : Bool} -> R) -> R:
  match a:
    case True{}:
      l({==})
    case False{}:
      r(e)

def or_left(a: Bool, b: Bool, e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Bool.or(False{}, b) == True{} : Bool}, S.false_true(e))

def or_right(a: Bool, b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def or_false_l(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, S.true_false(e))
    case False{}:
      {==}

def or_false_r(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, S.true_false(e))
    case False{}:
      e

def or_false(a: Bool, -b: Bool, ea: {a == False{} : Bool}, eb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({Bool.or(True{}, b) == False{} : Bool}, S.true_false(ea))
    case False{}:
      eb

def and_intro(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, S.false_true(ea))

def not_true(b: Bool, e: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, S.true_false(e))
    case False{}:
      {==}

def not_of_true(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, S.false_true(e))
    case False{}:
      {==}

def cmp_refl(n: Nat) -> {Nat.cmp(n, n) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      cmp_refl(p)

def name_eq_refl(a: M.Name) -> {M.Name.eq(a, a) == True{} : Bool}:
  match a:
    case M.Name{a1, a2}:
      %Equal.sym(Cmp, Nat.cmp(a1, a1), EQ{}, cmp_refl(a1)) : {Cmp.is_eq(M.Name.cmp.of(_, a2, a2)) == True{} : Bool}
      %Equal.sym(Cmp, Nat.cmp(a2, a2), EQ{}, cmp_refl(a2)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

def name_eq_sym(+a: M.Name, +b: M.Name) -> {M.Name.eq(b, a) == M.Name.eq(a, b) : Bool}:
  %Equal.sym(Cmp, M.Name.cmp(b, a), ML.flip(M.Name.cmp(a, b)), ML.name_flip(a, b)) : {Cmp.is_eq(_) == Cmp.is_eq(M.Name.cmp(a, b)) : Bool}
  ML.is_eq_flip(M.Name.cmp(a, b))

def name_ne_sym(+a: M.Name, +b: M.Name, e: {M.Name.eq(a, b) == False{} : Bool}) -> {M.Name.eq(b, a) == False{} : Bool}:
  %Equal.sym(Bool, M.Name.eq(b, a), M.Name.eq(a, b), name_eq_sym(a, b)) : {_ == False{} : Bool}
  e

def name_eq_equal.of(c: Cmp, +a1: Nat, +b1: Nat, +a2: Nat, +b2: Nat, ec: {Nat.cmp(a1, b1) == c : Cmp}, e: {Cmp.is_eq(M.Name.cmp.of(c, a2, b2)) == True{} : Bool}) -> {M.Name{a1, a2} == M.Name{b1, b2} : M.Name}:
  match c:
    case LT{}:
      Empty.absurd({M.Name{a1, a2} == M.Name{b1, b2} : M.Name}, S.false_true(e))
    case GT{}:
      Empty.absurd({M.Name{a1, a2} == M.Name{b1, b2} : M.Name}, S.false_true(e))
    case EQ{}:
      %ML.cmp_eq(a1, b1, ec) : {M.Name{a1, a2} == M.Name{_, b2} : M.Name}
      %ML.cmp_eq(a2, b2, S.is_eq_true(Nat.cmp(a2, b2), e)) : {M.Name{a1, a2} == M.Name{a1, _} : M.Name}
      {==}

def name_eq_equal(a: M.Name, b: M.Name, e: {M.Name.eq(a, b) == True{} : Bool}) -> {a == b : M.Name}:
  match a b:
    case M.Name{+a1, a2} M.Name{+b1, b2}:
      name_eq_equal.of(Nat.cmp(a1, b1), a1, b1, a2, b2, {==}, e)

# Names in a list
# ---------------

def or_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def named_append(xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +nm: M.Name) -> {M.named(List.append(&2, M.Node, xs, ys), nm) == Bool.or(M.named(xs, nm), M.named(ys, nm)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      %Equal.sym(Bool, M.named(List.append(&2, M.Node, rest, ys), nm), Bool.or(M.named(rest, nm), M.named(ys, nm)), named_append(rest, ys, nm)) : {Bool.or(M.Name.eq(M.Node.name(x), nm), _) == Bool.or(Bool.or(M.Name.eq(M.Node.name(x), nm), M.named(rest, nm)), M.named(ys, nm)) : Bool}
      or_assoc(M.Name.eq(M.Node.name(x), nm), M.named(rest, nm), M.named(ys, nm))

def named_split(+xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +nm: M.Name) -> {Bool.or(M.named(xs, nm), M.named(ys, nm)) == M.named(List.append(&2, M.Node, xs, ys), nm) : Bool}:
  Equal.sym(Bool, M.named(List.append(&2, M.Node, xs, ys), nm), Bool.or(M.named(xs, nm), M.named(ys, nm)), named_append(xs, ys, nm))

def named_append_false(+xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +nm: M.Name, hx: {M.named(xs, nm) == False{} : Bool}, hy: {M.named(ys, nm) == False{} : Bool}) -> {M.named(List.append(&2, M.Node, xs, ys), nm) == False{} : Bool}:
  %named_split(xs, ys, nm) : {_ == False{} : Bool}
  or_false(M.named(xs, nm), M.named(ys, nm), hx, hy)

def named_filter(x: M.Node, +xs: List<&2, M.Node>, +nm: M.Name, keep: Bool, h: {M.named(x <> xs, nm) == False{} : Bool}) -> {M.named(List.filter.put(M.Node, x, xs, keep), nm) == False{} : Bool}:
  match keep:
    case True{}:
      h
    case False{}:
      or_false_r(M.Name.eq(M.Node.name(x), nm), M.named(xs, nm), h)

# The children of any place are among the tree's elements.
def children_sub(t: List<&2, M.Node>, +q: Maybe<&2, M.Name>, +r: Bool, +nm: M.Name, +h: {M.named(t, nm) == False{} : Bool}) -> {M.named(M.children(t, q, r), nm) == False{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +x <> +xs:
      named_filter(x, M.children(xs, q, r), nm, M.Node.hangs(x, q, r), or_false(M.Name.eq(M.Node.name(x), nm), M.named(M.children(xs, q, r), nm), or_false_l(M.Name.eq(M.Node.name(x), nm), M.named(xs, nm), h), children_sub(xs, q, r, nm, or_false_r(M.Name.eq(M.Node.name(x), nm), M.named(xs, nm), h))))

def named_in(t: List<&2, M.Node>, +nm: M.Name, +sub: List<&2, M.Node>, f: {M.named(t, nm) == False{} : Bool} -> {M.named(sub, nm) == False{} : Bool}, h: {M.named(sub, nm) == True{} : Bool}) -> {M.named(t, nm) == True{} : Bool}:
  bool_cases({M.named(t, nm) == True{} : Bool}, M.named(t, nm), e => e, e => Empty.absurd({M.named(t, nm) == True{} : Bool}, S.false_true(Equal.trans(Bool, False{}, M.named(sub, nm), True{}, Equal.sym(Bool, M.named(sub, nm), False{}, f(e)), h))))

def children_named(+t: List<&2, M.Node>, +q: Maybe<&2, M.Name>, +r: Bool, +nm: M.Name, h: {M.named(M.children(t, q, r), nm) == True{} : Bool}) -> {M.named(t, nm) == True{} : Bool}:
  named_in(t, nm, M.children(t, q, r), e => children_sub(t, q, r, nm, e), h)

# What is read is in the tree.
def read_sub(fuel: Nat, +t: List<&2, M.Node>, siblings: List<&2, M.Node>, +nm: M.Name, +ht: {M.named(t, nm) == False{} : Bool}, +hs: {M.named(siblings, nm) == False{} : Bool}) -> {M.named(M.read_all(fuel, t, siblings), nm) == False{} : Bool}:
  match fuel:
    case 0n:
      {==}
    case 1n++p:
      match siblings:
        case Nil{}:
          {==}
        case +s <> +rest:
          named_append_false(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), nm,
            read_sub(p, t, M.children(t, Some{M.Node.name(s)}, False{}), nm, ht, children_sub(t, Some{M.Node.name(s)}, False{}, nm, ht)),
            or_false(M.Name.eq(M.Node.name(s), nm), M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), nm),
              or_false_l(M.Name.eq(M.Node.name(s), nm), M.named(rest, nm), hs),
              named_append_false(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), nm,
                read_sub(p, t, M.children(t, Some{M.Node.name(s)}, True{}), nm, ht, children_sub(t, Some{M.Node.name(s)}, True{}, nm, ht)),
                read_sub(p, t, rest, nm, ht, or_false_r(M.Name.eq(M.Node.name(s), nm), M.named(rest, nm), hs)))))

def order_sub(+t: List<&2, M.Node>, +nm: M.Name, +e: {M.named(t, nm) == False{} : Bool}) -> {M.named(M.order(t), nm) == False{} : Bool}:
  read_sub(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}), nm, e, children_sub(t, None{}, True{}, nm, e))

def order_named(+t: List<&2, M.Node>, +nm: M.Name, h: {M.named(M.order(t), nm) == True{} : Bool}) -> {M.named(t, nm) == True{} : Bool}:
  named_in(t, nm, M.order(t), e => order_sub(t, nm, e), h)

def standing_sub(ns: List<&2, M.Node>, +nm: M.Name, +h: {M.named(ns, nm) == False{} : Bool}) -> {M.named(M.standing(ns), nm) == False{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +x <> +rest:
      named_filter(x, M.standing(rest), nm, M.Node.standing(x), or_false(M.Name.eq(M.Node.name(x), nm), M.named(M.standing(rest), nm), or_false_l(M.Name.eq(M.Node.name(x), nm), M.named(rest, nm), h), standing_sub(rest, nm, or_false_r(M.Name.eq(M.Node.name(x), nm), M.named(rest, nm), h))))

def standing_named(+ns: List<&2, M.Node>, +nm: M.Name, h: {M.named(M.standing(ns), nm) == True{} : Bool}) -> {M.named(ns, nm) == True{} : Bool}:
  named_in(ns, nm, M.standing(ns), e => standing_sub(ns, nm, e), h)

def get_named(xs: List<&2, M.Node>, p: Nat, +x: M.Node, e: {List.get(&2, M.Node, xs, p) == Some{x} : Maybe<&2, M.Node>}) -> {M.named(xs, M.Node.name(x)) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, ML.none_some(x, e))
    case +h <> +rest:
      match p:
        case 0n:
          %Equal.sym(M.Node, h, x, ML.some_node(h, x, e)) : {Bool.or(M.Name.eq(M.Node.name(_), M.Node.name(x)), M.named(rest, M.Node.name(x))) == True{} : Bool}
          or_left(M.Name.eq(M.Node.name(x), M.Node.name(x)), M.named(rest, M.Node.name(x)), name_eq_refl(M.Node.name(x)))
        case 1n+q:
          or_right(M.Name.eq(M.Node.name(h), M.Node.name(x)), M.named(rest, M.Node.name(x)), get_named(rest, q, x, e))

# A name in the tree differs from one not in it.
def named_ne.here(x: M.Node, a: M.Name, +b: M.Name, e: {M.Node.name(x) == a : M.Name}, f: {M.Name.eq(M.Node.name(x), b) == False{} : Bool}) -> {M.Name.eq(a, b) == False{} : Bool}:
  %e : {M.Name.eq(_, b) == False{} : Bool}
  f

def named_ne(t: List<&2, M.Node>, +a: M.Name, +b: M.Name, h: {M.named(t, a) == True{} : Bool}, +f: {M.named(t, b) == False{} : Bool}) -> {M.Name.eq(a, b) == False{} : Bool}:
  match t:
    case Nil{}:
      Empty.absurd({M.Name.eq(a, b) == False{} : Bool}, S.false_true(h))
    case +x <> +rest:
      or_cases({M.Name.eq(a, b) == False{} : Bool}, M.Name.eq(M.Node.name(x), a), M.named(rest, a), h,
        e => named_ne.here(x, a, b, name_eq_equal(M.Node.name(x), a, e), or_false_l(M.Name.eq(M.Node.name(x), b), M.named(rest, b), f)),
        e => named_ne(rest, a, b, e, or_false_r(M.Name.eq(M.Node.name(x), b), M.named(rest, b), f)))

# Lists
# -----

def ldisc(xs: List<&2, M.Node>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case x <> rest:
      Empty

def cons_nil(x: M.Node, xs: List<&2, M.Node>, e: {x <> xs == Nil{} : List<&2, M.Node>}) -> Empty:
  %Equal.sym(List<&2, M.Node>, x <> xs, Nil{}, e) : {ldisc(_) : Type}
  Unit{}

def nil_of_is_nil(xs: List<&2, M.Node>, e: {M.is_nil(xs) == True{} : Bool}) -> {xs == Nil{} : List<&2, M.Node>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Empty.absurd({x <> rest == Nil{} : List<&2, M.Node>}, S.false_true(e))

def append_cong(-a: List<&2, M.Node>, -a2: List<&2, M.Node>, -b: List<&2, M.Node>, -b2: List<&2, M.Node>, ea: {a == a2 : List<&2, M.Node>}, eb: {b == b2 : List<&2, M.Node>}) -> {List.append(&2, M.Node, a, b) == List.append(&2, M.Node, a2, b2) : List<&2, M.Node>}:
  %ea : {List.append(&2, M.Node, a, b) == List.append(&2, M.Node, _, b2) : List<&2, M.Node>}
  %eb : {List.append(&2, M.Node, a, b) == List.append(&2, M.Node, a, _) : List<&2, M.Node>}
  {==}

def cons_cong(-x: M.Node, -a: List<&2, M.Node>, -b: List<&2, M.Node>, e: {a == b : List<&2, M.Node>}) -> {x <> a == x <> b : List<&2, M.Node>}:
  %e : {x <> a == x <> _ : List<&2, M.Node>}
  {==}

def read_nil(fuel: Nat, t: List<&2, M.Node>) -> {M.read_all(fuel, t, Nil{}) == Nil{} : List<&2, M.Node>}:
  match fuel:
    case 0n:
      {==}
    case 1n+p:
      {==}

def append_nil(xs: List<&2, M.Node>) -> {List.append(&2, M.Node, xs, Nil{}) == xs : List<&2, M.Node>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      cons_cong(x, List.append(&2, M.Node, rest, Nil{}), rest, append_nil(rest))

# Attaching an only child
# -----------------------
#
# The attach adds one element to the sibling list of its place, which
# was empty, and changes no other.

def hangs_of_under(x: M.Node, +nm: M.Name, r: Bool, u: {M.Node.under(x, nm) == False{} : Bool}) -> {M.Node.hangs(x, Some{nm}, r) == False{} : Bool}:
  match x:
    case M.Node{x1, it, M.Place{pl, rr}, d}:
      %Equal.sym(Bool, M.Name.same(pl, Some{nm}), False{}, u) : {Bool.and(_, Bool.not(Bool.xor(rr, r))) == False{} : Bool}
      {==}

def children_none(t: List<&2, M.Node>, +nm: M.Name, +r: Bool, +hu: {M.hangs_under(t, nm) == False{} : Bool}) -> {M.children(t, Some{nm}, r) == Nil{} : List<&2, M.Node>}:
  match t:
    case Nil{}:
      {==}
    case +x <> +xs:
      %Equal.sym(Bool, M.Node.hangs(x, Some{nm}, r), False{}, hangs_of_under(x, nm, r, or_false_l(M.Node.under(x, nm), M.hangs_under(xs, nm), hu))) : {List.filter.put(M.Node, x, M.children(xs, Some{nm}, r), _) == Nil{} : List<&2, M.Node>}
      children_none(xs, nm, r, or_false_r(M.Node.under(x, nm), M.hangs_under(xs, nm), hu))

def children_attach_other.at(+x: M.Node, +xs: List<&2, M.Node>, +n: M.Node, +q: Maybe<&2, M.Name>, +r: Bool, lt: Bool, ne: {M.Node.hangs(n, q, r) == False{} : Bool}, ih: {M.children(M.attach(xs, n), q, r) == M.children(xs, q, r) : List<&2, M.Node>}) -> {M.children(M.attach.put(n, x, xs, M.attach(xs, n), lt), q, r) == M.children(x <> xs, q, r) : List<&2, M.Node>}:
  match lt:
    case True{}:
      %Equal.sym(Bool, M.Node.hangs(n, q, r), False{}, ne) : {List.filter.put(M.Node, n, M.children(x <> xs, q, r), _) == M.children(x <> xs, q, r) : List<&2, M.Node>}
      {==}
    case False{}:
      %Equal.sym(List<&2, M.Node>, M.children(M.attach(xs, n), q, r), M.children(xs, q, r), ih) : {List.filter.put(M.Node, x, _, M.Node.hangs(x, q, r)) == M.children(x <> xs, q, r) : List<&2, M.Node>}
      {==}

def children_attach_other(t: List<&2, M.Node>, +n: M.Node, +q: Maybe<&2, M.Name>, +r: Bool, +ne: {M.Node.hangs(n, q, r) == False{} : Bool}) -> {M.children(M.attach(t, n), q, r) == M.children(t, q, r) : List<&2, M.Node>}:
  match t:
    case Nil{}:
      %Equal.sym(Bool, M.Node.hangs(n, q, r), False{}, ne) : {List.filter.put(M.Node, n, Nil{}, _) == Nil{} : List<&2, M.Node>}
      {==}
    case +x <> +xs:
      children_attach_other.at(x, xs, n, q, r, Cmp.is_lt(M.Name.cmp(M.Node.name(n), M.Node.name(x))), ne, children_attach_other(xs, n, q, r, ne))

def children_attach_here.at(+x: M.Node, +xs: List<&2, M.Node>, +n: M.Node, +q: Maybe<&2, M.Name>, +r: Bool, hx: Bool, ehx: {M.Node.hangs(x, q, r) == hx : Bool}, lt: Bool, h: {M.Node.hangs(n, q, r) == True{} : Bool}, e: {List.filter.put(M.Node, x, M.children(xs, q, r), hx) == Nil{} : List<&2, M.Node>}, ih: {M.children(xs, q, r) == Nil{} : List<&2, M.Node>} -> {M.children(M.attach(xs, n), q, r) == [n] : List<&2, M.Node>}) -> {M.children(M.attach.put(n, x, xs, M.attach(xs, n), lt), q, r) == [n] : List<&2, M.Node>}:
  match hx:
    case True{}:
      Empty.absurd({M.children(M.attach.put(n, x, xs, M.attach(xs, n), lt), q, r) == [n] : List<&2, M.Node>}, cons_nil(x, M.children(xs, q, r), e))
    case False{}:
      match lt:
        case True{}:
          %Equal.sym(Bool, M.Node.hangs(n, q, r), True{}, h) : {List.filter.put(M.Node, n, List.filter.put(M.Node, x, M.children(xs, q, r), M.Node.hangs(x, q, r)), _) == [n] : List<&2, M.Node>}
          %Equal.sym(Bool, M.Node.hangs(x, q, r), False{}, ehx) : {List.filter.put(M.Node, n, List.filter.put(M.Node, x, M.children(xs, q, r), _), True{}) == [n] : List<&2, M.Node>}
          %Equal.sym(List<&2, M.Node>, M.children(xs, q, r), Nil{}, e) : {List.filter.put(M.Node, n, List.filter.put(M.Node, x, _, False{}), True{}) == [n] : List<&2, M.Node>}
          {==}
        case False{}:
          %Equal.sym(Bool, M.Node.hangs(x, q, r), False{}, ehx) : {List.filter.put(M.Node, x, M.children(M.attach(xs, n), q, r), _) == [n] : List<&2, M.Node>}
          ih(e)

def children_attach_here(t: List<&2, M.Node>, +n: M.Node, +q: Maybe<&2, M.Name>, +r: Bool, +h: {M.Node.hangs(n, q, r) == True{} : Bool}, e: {M.children(t, q, r) == Nil{} : List<&2, M.Node>}) -> {M.children(M.attach(t, n), q, r) == [n] : List<&2, M.Node>}:
  match t:
    case Nil{}:
      %Equal.sym(Bool, M.Node.hangs(n, q, r), True{}, h) : {List.filter.put(M.Node, n, Nil{}, _) == [n] : List<&2, M.Node>}
      {==}
    case +x <> +xs:
      children_attach_here.at(x, xs, n, q, r, M.Node.hangs(x, q, r), {==}, Cmp.is_lt(M.Name.cmp(M.Node.name(n), M.Node.name(x))), h, e, e2 => children_attach_here(xs, n, q, r, h, e2))

def attach_length.at(+x: M.Node, +xs: List<&2, M.Node>, +n: M.Node, lt: Bool, ih: {List.length(&2, M.Node, M.attach(xs, n)) == 1n+List.length(&2, M.Node, xs) : Nat}) -> {List.length(&2, M.Node, M.attach.put(n, x, xs, M.attach(xs, n), lt)) == 2n+List.length(&2, M.Node, xs) : Nat}:
  match lt:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Nat, List.length(&2, M.Node, M.attach(xs, n)), 1n+List.length(&2, M.Node, xs), ih) : {1n+_ == 2n+List.length(&2, M.Node, xs) : Nat}
      {==}

def attach_length(t: List<&2, M.Node>, +n: M.Node) -> {List.length(&2, M.Node, M.attach(t, n)) == 1n+List.length(&2, M.Node, t) : Nat}:
  match t:
    case Nil{}:
      {==}
    case +x <> +xs:
      attach_length.at(x, xs, n, Cmp.is_lt(M.Name.cmp(M.Node.name(n), M.Node.name(x))), attach_length(xs, n))

# The element attached, `Node{_, _, Place{Some{par}, right}, Nil{}}` as
# `inserts` mints it: where it hangs, and where it does not.
def and_false_r(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def xor_self(b: Bool) -> {Bool.not(Bool.xor(b, b)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def hangs_eq(n: M.Node, +par: M.Name, +right: Bool, +ns: M.Name, +r: Bool, hp: {M.Node.place(n) == M.Place{Some{par}, right} : M.Place}) -> {Bool.and(M.Name.eq(par, ns), Bool.not(Bool.xor(right, r))) == M.Node.hangs(n, Some{ns}, r) : Bool}:
  match n:
    case M.Node{x, it, pl, d}:
      %Equal.sym(M.Place, pl, M.Place{Some{par}, right}, hp) : {Bool.and(M.Name.eq(par, ns), Bool.not(Bool.xor(right, r))) == M.Node.hangs(M.Node{x, it, _, d}, Some{ns}, r) : Bool}
      {==}

def hangs_not(+n: M.Node, +par: M.Name, +right: Bool, +ns: M.Name, +r: Bool, hp: {M.Node.place(n) == M.Place{Some{par}, right} : M.Place}, ne: {M.Name.eq(ns, par) == False{} : Bool}) -> {M.Node.hangs(n, Some{ns}, r) == False{} : Bool}:
  %hangs_eq(n, par, right, ns, r, hp) : {_ == False{} : Bool}
  %Equal.sym(Bool, M.Name.eq(par, ns), M.Name.eq(ns, par), name_eq_sym(ns, par)) : {Bool.and(_, Bool.not(Bool.xor(right, r))) == False{} : Bool}
  %Equal.sym(Bool, M.Name.eq(ns, par), False{}, ne) : {Bool.and(_, Bool.not(Bool.xor(right, r))) == False{} : Bool}
  {==}

def hangs_other_side(+n: M.Node, +par: M.Name, right: Bool, +ns: M.Name, r: Bool, hp: {M.Node.place(n) == M.Place{Some{par}, right} : M.Place}, x: {Bool.xor(right, r) == True{} : Bool}) -> {M.Node.hangs(n, Some{ns}, r) == False{} : Bool}:
  %hangs_eq(n, par, right, ns, r, hp) : {_ == False{} : Bool}
  %Equal.sym(Bool, Bool.xor(right, r), True{}, x) : {Bool.and(M.Name.eq(par, ns), Bool.not(_)) == False{} : Bool}
  and_false_r(M.Name.eq(par, ns))

def hangs_here(+n: M.Node, +par: M.Name, +right: Bool, +ns: M.Name, hp: {M.Node.place(n) == M.Place{Some{par}, right} : M.Place}, eq: {M.Name.eq(ns, par) == True{} : Bool}) -> {M.Node.hangs(n, Some{ns}, right) == True{} : Bool}:
  %hangs_eq(n, par, right, ns, right, hp) : {_ == True{} : Bool}
  %Equal.sym(Bool, M.Name.eq(par, ns), M.Name.eq(ns, par), name_eq_sym(ns, par)) : {Bool.and(_, Bool.not(Bool.xor(right, right))) == True{} : Bool}
  %Equal.sym(Bool, M.Name.eq(ns, par), True{}, eq) : {Bool.and(_, Bool.not(Bool.xor(right, right))) == True{} : Bool}
  xor_self(right)

def hangs_root(n: M.Node, +par: M.Name, +right: Bool, r: Bool, hp: {M.Node.place(n) == M.Place{Some{par}, right} : M.Place}) -> {M.Node.hangs(n, None{}, r) == False{} : Bool}:
  match n:
    case M.Node{x, it, pl, d}:
      %Equal.sym(M.Place, pl, M.Place{Some{par}, right}, hp) : {M.Node.hangs(M.Node{x, it, _, d}, None{}, r) == False{} : Bool}
      {==}

# Nothing hangs under the new element: not the tree's elements, which
# are fresh of its name, and not itself, whose parent the tree names.
def children_attach_fresh(+t: List<&2, M.Node>, +n: M.Node, +par: M.Name, +right: Bool, +r: Bool, +hp: {M.Node.place(n) == M.Place{Some{par}, right} : M.Place}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, pn: {M.named(t, par) == True{} : Bool}) -> {M.children(M.attach(t, n), Some{M.Node.name(n)}, r) == Nil{} : List<&2, M.Node>}:
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(n)}, r), M.children(t, Some{M.Node.name(n)}, r), children_attach_other(t, n, Some{M.Node.name(n)}, r, hangs_not(n, par, right, M.Node.name(n), r, hp, name_ne_sym(par, M.Node.name(n), named_ne(t, par, M.Node.name(n), pn, not_of_true(M.named(t, M.Node.name(n)), Comp.and_left(Bool.not(M.named(t, M.Node.name(n))), Bool.not(M.hangs_under(t, M.Node.name(n))), fr))))))) : {_ == Nil{} : List<&2, M.Node>}
  children_none(t, M.Node.name(n), r, not_of_true(M.hangs_under(t, M.Node.name(n)), Comp.and_right(Bool.not(M.named(t, M.Node.name(n))), Bool.not(M.hangs_under(t, M.Node.name(n))), fr)))

def read_only(p: Nat, +t: List<&2, M.Node>, +n: M.Node, +par: M.Name, +right: Bool, +hp: {M.Node.place(n) == M.Place{Some{par}, right} : M.Place}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +pn: {M.named(t, par) == True{} : Bool}) -> {M.read_all(1n+p, M.attach(t, n), [n]) == [n] : List<&2, M.Node>}:
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(n)}, False{}), Nil{}, children_attach_fresh(t, n, par, right, False{}, hp, fr, pn)) : {List.append(&2, M.Node, M.read_all(p, M.attach(t, n), _), n <> List.append(&2, M.Node, M.read_all(p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(n)}, True{})), M.read_all(p, M.attach(t, n), Nil{}))) == [n] : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(n)}, True{}), Nil{}, children_attach_fresh(t, n, par, right, True{}, hp, fr, pn)) : {List.append(&2, M.Node, M.read_all(p, M.attach(t, n), Nil{}), n <> List.append(&2, M.Node, M.read_all(p, M.attach(t, n), _), M.read_all(p, M.attach(t, n), Nil{}))) == [n] : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.read_all(p, M.attach(t, n), Nil{}), Nil{}, read_nil(p, M.attach(t, n))) : {List.append(&2, M.Node, _, n <> List.append(&2, M.Node, _, _)) == [n] : List<&2, M.Node>}
  {==}

# The splice
# ----------
#
# The new element beside every element of its parent's name: after it
# when it is a right child, before it when a left one. The reading of
# the tree with the element attached is the old reading spliced.
def splice.at(x: M.Node, rest: List<&2, M.Node>, n: M.Node, hit: Bool, right: Bool) -> List<&2, M.Node>:
  match hit:
    case False{}:
      x <> rest
    case True{}:
      match right:
        case True{}:
          x <> n <> rest
        case False{}:
          n <> x <> rest

def splice(xs: List<&2, M.Node>, +par: M.Name, +right: Bool, +n: M.Node) -> List<&2, M.Node>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      splice.at(x, splice(rest, par, right, n), n, M.Name.eq(M.Node.name(x), par), right)

def splice_at_append(x: M.Node, rest: List<&2, M.Node>, ys: List<&2, M.Node>, n: M.Node, hit: Bool, right: Bool) -> {splice.at(x, List.append(&2, M.Node, rest, ys), n, hit, right) == List.append(&2, M.Node, splice.at(x, rest, n, hit, right), ys) : List<&2, M.Node>}:
  match hit:
    case False{}:
      {==}
    case True{}:
      match right:
        case True{}:
          {==}
        case False{}:
          {==}

def splice_append(xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +par: M.Name, +right: Bool, +n: M.Node) -> {splice(List.append(&2, M.Node, xs, ys), par, right, n) == List.append(&2, M.Node, splice(xs, par, right, n), splice(ys, par, right, n)) : List<&2, M.Node>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(List<&2, M.Node>, splice(List.append(&2, M.Node, rest, ys), par, right, n), List.append(&2, M.Node, splice(rest, par, right, n), splice(ys, par, right, n)), splice_append(rest, ys, par, right, n)) : {splice.at(x, _, n, M.Name.eq(M.Node.name(x), par), right) == List.append(&2, M.Node, splice.at(x, splice(rest, par, right, n), n, M.Name.eq(M.Node.name(x), par), right), splice(ys, par, right, n)) : List<&2, M.Node>}
      splice_at_append(x, splice(rest, par, right, n), splice(ys, par, right, n), n, M.Name.eq(M.Node.name(x), par), right)

# The reading of a sibling list in the tree with the element attached,
# with one more fuel than the old reading needed. Induction on the fuel;
# at a sibling of the parent's name the empty list of the place has
# become the one-element list, which reads as the element.
def read_attach.miss(+p: Nat, +t: List<&2, M.Node>, +s: M.Node, +rest: List<&2, M.Node>, +n: M.Node, +par: M.Name, +right: Bool, +hp: {M.Node.place(n) == M.Place{Some{par}, right} : M.Place}, +eh: {M.Name.eq(M.Node.name(s), par) == False{} : Bool}, ihL: {M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})) == splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par, right, n) : List<&2, M.Node>}, ihR: {M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})) == splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par, right, n) : List<&2, M.Node>}, ihrest: {M.read_all(1n+p, M.attach(t, n), rest) == splice(M.read_all(p, t, rest), par, right, n) : List<&2, M.Node>}) -> {M.read_all(2n+p, M.attach(t, n), s <> rest) == splice(M.read_all(1n+p, t, s <> rest), par, right, n) : List<&2, M.Node>}:
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, False{}), M.children(t, Some{M.Node.name(s)}, False{}), children_attach_other(t, n, Some{M.Node.name(s)}, False{}, hangs_not(n, par, right, M.Node.name(s), False{}, hp, eh))) : {List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), _), s <> List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.read_all(1n+p, M.attach(t, n), rest))) == splice(M.read_all(1n+p, t, s <> rest), par, right, n) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, True{}), M.children(t, Some{M.Node.name(s)}, True{}), children_attach_other(t, n, Some{M.Node.name(s)}, True{}, hangs_not(n, par, right, M.Node.name(s), True{}, hp, eh))) : {List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), _), M.read_all(1n+p, M.attach(t, n), rest))) == splice(M.read_all(1n+p, t, s <> rest), par, right, n) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, splice(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), par, right, n), List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par, right, n), splice(s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par, right, n)), splice_append(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par, right, n)) : {List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(1n+p, M.attach(t, n), rest))) == _ : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, splice(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par, right, n), List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par, right, n), splice(M.read_all(p, t, rest), par, right, n)), splice_append(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), par, right, n)) : {List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(1n+p, M.attach(t, n), rest))) == List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par, right, n), splice.at(s, _, n, M.Name.eq(M.Node.name(s), par), right)) : List<&2, M.Node>}
  %Equal.sym(Bool, M.Name.eq(M.Node.name(s), par), False{}, eh) : {List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(1n+p, M.attach(t, n), rest))) == List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par, right, n), splice.at(s, List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par, right, n), splice(M.read_all(p, t, rest), par, right, n)), n, _, right)) : List<&2, M.Node>}
  append_cong(M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par, right, n), s <> List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(1n+p, M.attach(t, n), rest)), s <> List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par, right, n), splice(M.read_all(p, t, rest), par, right, n)), ihL,
    cons_cong(s, List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(1n+p, M.attach(t, n), rest)), List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par, right, n), splice(M.read_all(p, t, rest), par, right, n)),
      append_cong(M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par, right, n), M.read_all(1n+p, M.attach(t, n), rest), splice(M.read_all(p, t, rest), par, right, n), ihR, ihrest)))

def read_attach.hitR(+p: Nat, +t: List<&2, M.Node>, +s: M.Node, +rest: List<&2, M.Node>, +n: M.Node, +par: M.Name, +hp: {M.Node.place(n) == M.Place{Some{par}, True{}} : M.Place}, +eh: {M.Name.eq(M.Node.name(s), par) == True{} : Bool}, +e: {M.children(t, Some{M.Node.name(s)}, True{}) == Nil{} : List<&2, M.Node>}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +pn: {M.named(t, par) == True{} : Bool}, ihO: {M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})) == splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par, True{}, n) : List<&2, M.Node>}, ihrest: {M.read_all(1n+p, M.attach(t, n), rest) == splice(M.read_all(p, t, rest), par, True{}, n) : List<&2, M.Node>}) -> {M.read_all(2n+p, M.attach(t, n), s <> rest) == splice(M.read_all(1n+p, t, s <> rest), par, True{}, n) : List<&2, M.Node>}:
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, False{}), M.children(t, Some{M.Node.name(s)}, False{}), children_attach_other(t, n, Some{M.Node.name(s)}, False{}, hangs_other_side(n, par, True{}, M.Node.name(s), False{}, hp, {==}))) : {List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), _), s <> List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.read_all(1n+p, M.attach(t, n), rest))) == splice(M.read_all(1n+p, t, s <> rest), par, True{}, n) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, True{}), [n], children_attach_here(t, n, Some{M.Node.name(s)}, True{}, hangs_here(n, par, True{}, M.Node.name(s), hp, eh), e)) : {List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), _), M.read_all(1n+p, M.attach(t, n), rest))) == splice(M.read_all(1n+p, t, s <> rest), par, True{}, n) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.read_all(1n+p, M.attach(t, n), [n]), [n], read_only(p, t, n, par, True{}, hp, fr, pn)) : {List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, _, M.read_all(1n+p, M.attach(t, n), rest))) == splice(M.read_all(1n+p, t, s <> rest), par, True{}, n) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par, True{}, n), ihO) : {List.append(&2, M.Node, _, s <> List.append(&2, M.Node, [n], M.read_all(1n+p, M.attach(t, n), rest))) == splice(M.read_all(1n+p, t, s <> rest), par, True{}, n) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.read_all(1n+p, M.attach(t, n), rest), splice(M.read_all(p, t, rest), par, True{}, n), ihrest) : {List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par, True{}, n), s <> List.append(&2, M.Node, [n], _)) == splice(M.read_all(1n+p, t, s <> rest), par, True{}, n) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, splice(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), par, True{}, n), List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par, True{}, n), splice(s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par, True{}, n)), splice_append(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par, True{}, n)) : {List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par, True{}, n), s <> List.append(&2, M.Node, [n], splice(M.read_all(p, t, rest), par, True{}, n))) == _ : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, splice(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par, True{}, n), List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par, True{}, n), splice(M.read_all(p, t, rest), par, True{}, n)), splice_append(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), par, True{}, n)) : {List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par, True{}, n), s <> List.append(&2, M.Node, [n], splice(M.read_all(p, t, rest), par, True{}, n))) == List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par, True{}, n), splice.at(s, _, n, M.Name.eq(M.Node.name(s), par), True{})) : List<&2, M.Node>}
  %Equal.sym(Bool, M.Name.eq(M.Node.name(s), par), True{}, eh) : {List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par, True{}, n), s <> List.append(&2, M.Node, [n], splice(M.read_all(p, t, rest), par, True{}, n))) == List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par, True{}, n), splice.at(s, List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par, True{}, n), splice(M.read_all(p, t, rest), par, True{}, n)), n, _, True{})) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.children(t, Some{M.Node.name(s)}, True{}), Nil{}, e) : {List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par, True{}, n), s <> List.append(&2, M.Node, [n], splice(M.read_all(p, t, rest), par, True{}, n))) == List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par, True{}, n), s <> n <> List.append(&2, M.Node, splice(M.read_all(p, t, _), par, True{}, n), splice(M.read_all(p, t, rest), par, True{}, n))) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.read_all(p, t, Nil{}), Nil{}, read_nil(p, t)) : {List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par, True{}, n), s <> List.append(&2, M.Node, [n], splice(M.read_all(p, t, rest), par, True{}, n))) == List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par, True{}, n), s <> n <> List.append(&2, M.Node, splice(_, par, True{}, n), splice(M.read_all(p, t, rest), par, True{}, n))) : List<&2, M.Node>}
  {==}

def read_attach.hitL(+p: Nat, +t: List<&2, M.Node>, +s: M.Node, +rest: List<&2, M.Node>, +n: M.Node, +par: M.Name, +hp: {M.Node.place(n) == M.Place{Some{par}, False{}} : M.Place}, +eh: {M.Name.eq(M.Node.name(s), par) == True{} : Bool}, +e: {M.children(t, Some{M.Node.name(s)}, False{}) == Nil{} : List<&2, M.Node>}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +pn: {M.named(t, par) == True{} : Bool}, ihO: {M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})) == splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par, False{}, n) : List<&2, M.Node>}, ihrest: {M.read_all(1n+p, M.attach(t, n), rest) == splice(M.read_all(p, t, rest), par, False{}, n) : List<&2, M.Node>}) -> {M.read_all(2n+p, M.attach(t, n), s <> rest) == splice(M.read_all(1n+p, t, s <> rest), par, False{}, n) : List<&2, M.Node>}:
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, True{}), M.children(t, Some{M.Node.name(s)}, True{}), children_attach_other(t, n, Some{M.Node.name(s)}, True{}, hangs_other_side(n, par, False{}, M.Node.name(s), True{}, hp, {==}))) : {List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), _), M.read_all(1n+p, M.attach(t, n), rest))) == splice(M.read_all(1n+p, t, s <> rest), par, False{}, n) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, False{}), [n], children_attach_here(t, n, Some{M.Node.name(s)}, False{}, hangs_here(n, par, False{}, M.Node.name(s), hp, eh), e)) : {List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), _), s <> List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(1n+p, M.attach(t, n), rest))) == splice(M.read_all(1n+p, t, s <> rest), par, False{}, n) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.read_all(1n+p, M.attach(t, n), [n]), [n], read_only(p, t, n, par, False{}, hp, fr, pn)) : {List.append(&2, M.Node, _, s <> List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(1n+p, M.attach(t, n), rest))) == splice(M.read_all(1n+p, t, s <> rest), par, False{}, n) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par, False{}, n), ihO) : {List.append(&2, M.Node, [n], s <> List.append(&2, M.Node, _, M.read_all(1n+p, M.attach(t, n), rest))) == splice(M.read_all(1n+p, t, s <> rest), par, False{}, n) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.read_all(1n+p, M.attach(t, n), rest), splice(M.read_all(p, t, rest), par, False{}, n), ihrest) : {List.append(&2, M.Node, [n], s <> List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par, False{}, n), _)) == splice(M.read_all(1n+p, t, s <> rest), par, False{}, n) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, splice(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), par, False{}, n), List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par, False{}, n), splice(s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par, False{}, n)), splice_append(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par, False{}, n)) : {List.append(&2, M.Node, [n], s <> List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par, False{}, n), splice(M.read_all(p, t, rest), par, False{}, n))) == _ : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, splice(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par, False{}, n), List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par, False{}, n), splice(M.read_all(p, t, rest), par, False{}, n)), splice_append(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), par, False{}, n)) : {List.append(&2, M.Node, [n], s <> List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par, False{}, n), splice(M.read_all(p, t, rest), par, False{}, n))) == List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par, False{}, n), splice.at(s, _, n, M.Name.eq(M.Node.name(s), par), False{})) : List<&2, M.Node>}
  %Equal.sym(Bool, M.Name.eq(M.Node.name(s), par), True{}, eh) : {List.append(&2, M.Node, [n], s <> List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par, False{}, n), splice(M.read_all(p, t, rest), par, False{}, n))) == List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par, False{}, n), splice.at(s, List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par, False{}, n), splice(M.read_all(p, t, rest), par, False{}, n)), n, _, False{})) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.children(t, Some{M.Node.name(s)}, False{}), Nil{}, e) : {List.append(&2, M.Node, [n], s <> List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par, False{}, n), splice(M.read_all(p, t, rest), par, False{}, n))) == List.append(&2, M.Node, splice(M.read_all(p, t, _), par, False{}, n), n <> s <> List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par, False{}, n), splice(M.read_all(p, t, rest), par, False{}, n))) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.read_all(p, t, Nil{}), Nil{}, read_nil(p, t)) : {List.append(&2, M.Node, [n], s <> List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par, False{}, n), splice(M.read_all(p, t, rest), par, False{}, n))) == List.append(&2, M.Node, splice(_, par, False{}, n), n <> s <> List.append(&2, M.Node, splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par, False{}, n), splice(M.read_all(p, t, rest), par, False{}, n))) : List<&2, M.Node>}
  {==}

def children_transport(+t: List<&2, M.Node>, +a: M.Name, +b: M.Name, +r: Bool, eq: {a == b : M.Name}, e: {M.children(t, Some{b}, r) == Nil{} : List<&2, M.Node>}) -> {M.children(t, Some{a}, r) == Nil{} : List<&2, M.Node>}:
  %Equal.sym(M.Name, a, b, eq) : {M.children(t, Some{_}, r) == Nil{} : List<&2, M.Node>}
  e

def read_attach.at(+p: Nat, +t: List<&2, M.Node>, +s: M.Node, +rest: List<&2, M.Node>, +n: M.Node, +par: M.Name, hit: Bool, +eh: {M.Name.eq(M.Node.name(s), par) == hit : Bool}, right: Bool, +hp: {M.Node.place(n) == M.Place{Some{par}, right} : M.Place}, +e: {M.children(t, Some{par}, right) == Nil{} : List<&2, M.Node>}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +pn: {M.named(t, par) == True{} : Bool}, ihL: {M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})) == splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par, right, n) : List<&2, M.Node>}, ihR: {M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})) == splice(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par, right, n) : List<&2, M.Node>}, ihrest: {M.read_all(1n+p, M.attach(t, n), rest) == splice(M.read_all(p, t, rest), par, right, n) : List<&2, M.Node>}) -> {M.read_all(2n+p, M.attach(t, n), s <> rest) == splice(M.read_all(1n+p, t, s <> rest), par, right, n) : List<&2, M.Node>}:
  match hit:
    case False{}:
      read_attach.miss(p, t, s, rest, n, par, right, hp, eh, ihL, ihR, ihrest)
    case True{}:
      match right:
        case True{}:
          read_attach.hitR(p, t, s, rest, n, par, hp, eh, children_transport(t, M.Node.name(s), par, True{}, name_eq_equal(M.Node.name(s), par, eh), e), fr, pn, ihL, ihrest)
        case False{}:
          read_attach.hitL(p, t, s, rest, n, par, hp, eh, children_transport(t, M.Node.name(s), par, False{}, name_eq_equal(M.Node.name(s), par, eh), e), fr, pn, ihR, ihrest)

def read_attach(f: Nat, +t: List<&2, M.Node>, siblings: List<&2, M.Node>, +n: M.Node, +par: M.Name, +right: Bool, +hp: {M.Node.place(n) == M.Place{Some{par}, right} : M.Place}, +e: {M.children(t, Some{par}, right) == Nil{} : List<&2, M.Node>}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +pn: {M.named(t, par) == True{} : Bool}, +h: {M.fits(f, t, siblings) == True{} : Bool}) -> {M.read_all(1n+f, M.attach(t, n), siblings) == splice(M.read_all(f, t, siblings), par, right, n) : List<&2, M.Node>}:
  match f:
    case 0n:
      %Equal.sym(List<&2, M.Node>, siblings, Nil{}, nil_of_is_nil(siblings, h)) : {M.read_all(1n, M.attach(t, n), _) == splice(M.read_all(0n, t, _), par, right, n) : List<&2, M.Node>}
      {==}
    case 1n++p:
      match siblings:
        case Nil{}:
          {==}
        case +s <> +rest:
          read_attach.at(p, t, s, rest, n, par, M.Name.eq(M.Node.name(s), par), {==}, right, hp, e, fr, pn,
            read_attach(p, t, M.children(t, Some{M.Node.name(s)}, False{}), n, par, right, hp, e, fr, pn, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h)),
            read_attach(p, t, M.children(t, Some{M.Node.name(s)}, True{}), n, par, right, hp, e, fr, pn, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h))),
            read_attach(p, t, rest, n, par, right, hp, e, fr, pn, Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h))))

# The fuel
# --------
#
# `fits` is kept, not derived: it holds of the empty tree, and an attach
# at an empty place needs one more fuel than the reading had, which is
# what `order` gives it once the tree is one element longer.
def fits_nil(fuel: Nat, t: List<&2, M.Node>) -> {M.fits(fuel, t, Nil{}) == True{} : Bool}:
  match fuel:
    case 0n:
      {==}
    case 1n+p:
      {==}

def fits_mono(fuel: Nat, +t: List<&2, M.Node>, siblings: List<&2, M.Node>, +h: {M.fits(fuel, t, siblings) == True{} : Bool}) -> {M.fits(1n+fuel, t, siblings) == True{} : Bool}:
  match fuel:
    case 0n:
      %Equal.sym(List<&2, M.Node>, siblings, Nil{}, nil_of_is_nil(siblings, h)) : {M.fits(1n, t, _) == True{} : Bool}
      {==}
    case 1n++p:
      match siblings:
        case Nil{}:
          {==}
        case +s <> +rest:
          and_intro(M.fits(1n+p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(1n+p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(1n+p, t, rest)),
            fits_mono(p, t, M.children(t, Some{M.Node.name(s)}, False{}), Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h)),
            and_intro(M.fits(1n+p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(1n+p, t, rest),
              fits_mono(p, t, M.children(t, Some{M.Node.name(s)}, True{}), Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h))),
              fits_mono(p, t, rest, Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h)))))

def fits_only(p: Nat, +t: List<&2, M.Node>, +n: M.Node, +par: M.Name, +right: Bool, +hp: {M.Node.place(n) == M.Place{Some{par}, right} : M.Place}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +pn: {M.named(t, par) == True{} : Bool}) -> {M.fits(1n+p, M.attach(t, n), [n]) == True{} : Bool}:
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(n)}, False{}), Nil{}, children_attach_fresh(t, n, par, right, False{}, hp, fr, pn)) : {Bool.and(M.fits(p, M.attach(t, n), _), Bool.and(M.fits(p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(n)}, True{})), M.fits(p, M.attach(t, n), Nil{}))) == True{} : Bool}
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(n)}, True{}), Nil{}, children_attach_fresh(t, n, par, right, True{}, hp, fr, pn)) : {Bool.and(M.fits(p, M.attach(t, n), Nil{}), Bool.and(M.fits(p, M.attach(t, n), _), M.fits(p, M.attach(t, n), Nil{}))) == True{} : Bool}
  %Equal.sym(Bool, M.fits(p, M.attach(t, n), Nil{}), True{}, fits_nil(p, M.attach(t, n))) : {Bool.and(_, Bool.and(_, _)) == True{} : Bool}
  {==}

def fits_attach.hitR(+p: Nat, +t: List<&2, M.Node>, +s: M.Node, +rest: List<&2, M.Node>, +n: M.Node, +par: M.Name, +hp: {M.Node.place(n) == M.Place{Some{par}, True{}} : M.Place}, +eh: {M.Name.eq(M.Node.name(s), par) == True{} : Bool}, e: {M.children(t, Some{M.Node.name(s)}, True{}) == Nil{} : List<&2, M.Node>}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +pn: {M.named(t, par) == True{} : Bool}, ihO: {M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})) == True{} : Bool}, ihrest: {M.fits(1n+p, M.attach(t, n), rest) == True{} : Bool}) -> {M.fits(2n+p, M.attach(t, n), s <> rest) == True{} : Bool}:
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, False{}), M.children(t, Some{M.Node.name(s)}, False{}), children_attach_other(t, n, Some{M.Node.name(s)}, False{}, hangs_other_side(n, par, True{}, M.Node.name(s), False{}, hp, {==}))) : {Bool.and(M.fits(1n+p, M.attach(t, n), _), Bool.and(M.fits(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.fits(1n+p, M.attach(t, n), rest))) == True{} : Bool}
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, True{}), [n], children_attach_here(t, n, Some{M.Node.name(s)}, True{}, hangs_here(n, par, True{}, M.Node.name(s), hp, eh), e)) : {Bool.and(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(1n+p, M.attach(t, n), _), M.fits(1n+p, M.attach(t, n), rest))) == True{} : Bool}
  and_intro(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(1n+p, M.attach(t, n), [n]), M.fits(1n+p, M.attach(t, n), rest)), ihO, and_intro(M.fits(1n+p, M.attach(t, n), [n]), M.fits(1n+p, M.attach(t, n), rest), fits_only(p, t, n, par, True{}, hp, fr, pn), ihrest))

def fits_attach.hitL(+p: Nat, +t: List<&2, M.Node>, +s: M.Node, +rest: List<&2, M.Node>, +n: M.Node, +par: M.Name, +hp: {M.Node.place(n) == M.Place{Some{par}, False{}} : M.Place}, +eh: {M.Name.eq(M.Node.name(s), par) == True{} : Bool}, e: {M.children(t, Some{M.Node.name(s)}, False{}) == Nil{} : List<&2, M.Node>}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +pn: {M.named(t, par) == True{} : Bool}, ihO: {M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})) == True{} : Bool}, ihrest: {M.fits(1n+p, M.attach(t, n), rest) == True{} : Bool}) -> {M.fits(2n+p, M.attach(t, n), s <> rest) == True{} : Bool}:
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, True{}), M.children(t, Some{M.Node.name(s)}, True{}), children_attach_other(t, n, Some{M.Node.name(s)}, True{}, hangs_other_side(n, par, False{}, M.Node.name(s), True{}, hp, {==}))) : {Bool.and(M.fits(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{})), Bool.and(M.fits(1n+p, M.attach(t, n), _), M.fits(1n+p, M.attach(t, n), rest))) == True{} : Bool}
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, False{}), [n], children_attach_here(t, n, Some{M.Node.name(s)}, False{}, hangs_here(n, par, False{}, M.Node.name(s), hp, eh), e)) : {Bool.and(M.fits(1n+p, M.attach(t, n), _), Bool.and(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.fits(1n+p, M.attach(t, n), rest))) == True{} : Bool}
  and_intro(M.fits(1n+p, M.attach(t, n), [n]), Bool.and(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.fits(1n+p, M.attach(t, n), rest)), fits_only(p, t, n, par, False{}, hp, fr, pn), and_intro(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.fits(1n+p, M.attach(t, n), rest), ihO, ihrest))

def fits_attach.miss(+p: Nat, +t: List<&2, M.Node>, +s: M.Node, +rest: List<&2, M.Node>, +n: M.Node, +par: M.Name, +right: Bool, +hp: {M.Node.place(n) == M.Place{Some{par}, right} : M.Place}, +eh: {M.Name.eq(M.Node.name(s), par) == False{} : Bool}, ihL: {M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})) == True{} : Bool}, ihR: {M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})) == True{} : Bool}, ihrest: {M.fits(1n+p, M.attach(t, n), rest) == True{} : Bool}) -> {M.fits(2n+p, M.attach(t, n), s <> rest) == True{} : Bool}:
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, False{}), M.children(t, Some{M.Node.name(s)}, False{}), children_attach_other(t, n, Some{M.Node.name(s)}, False{}, hangs_not(n, par, right, M.Node.name(s), False{}, hp, eh))) : {Bool.and(M.fits(1n+p, M.attach(t, n), _), Bool.and(M.fits(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.fits(1n+p, M.attach(t, n), rest))) == True{} : Bool}
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, True{}), M.children(t, Some{M.Node.name(s)}, True{}), children_attach_other(t, n, Some{M.Node.name(s)}, True{}, hangs_not(n, par, right, M.Node.name(s), True{}, hp, eh))) : {Bool.and(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(1n+p, M.attach(t, n), _), M.fits(1n+p, M.attach(t, n), rest))) == True{} : Bool}
  and_intro(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.fits(1n+p, M.attach(t, n), rest)), ihL, and_intro(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.fits(1n+p, M.attach(t, n), rest), ihR, ihrest))

def fits_attach.at(+p: Nat, +t: List<&2, M.Node>, +s: M.Node, +rest: List<&2, M.Node>, +n: M.Node, +par: M.Name, hit: Bool, +eh: {M.Name.eq(M.Node.name(s), par) == hit : Bool}, right: Bool, +hp: {M.Node.place(n) == M.Place{Some{par}, right} : M.Place}, +e: {M.children(t, Some{par}, right) == Nil{} : List<&2, M.Node>}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +pn: {M.named(t, par) == True{} : Bool}, ihL: {M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})) == True{} : Bool}, ihR: {M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})) == True{} : Bool}, ihrest: {M.fits(1n+p, M.attach(t, n), rest) == True{} : Bool}) -> {M.fits(2n+p, M.attach(t, n), s <> rest) == True{} : Bool}:
  match hit:
    case False{}:
      fits_attach.miss(p, t, s, rest, n, par, right, hp, eh, ihL, ihR, ihrest)
    case True{}:
      match right:
        case True{}:
          fits_attach.hitR(p, t, s, rest, n, par, hp, eh, children_transport(t, M.Node.name(s), par, True{}, name_eq_equal(M.Node.name(s), par, eh), e), fr, pn, ihL, ihrest)
        case False{}:
          fits_attach.hitL(p, t, s, rest, n, par, hp, eh, children_transport(t, M.Node.name(s), par, False{}, name_eq_equal(M.Node.name(s), par, eh), e), fr, pn, ihR, ihrest)

def fits_attach(f: Nat, +t: List<&2, M.Node>, siblings: List<&2, M.Node>, +n: M.Node, +par: M.Name, +right: Bool, +hp: {M.Node.place(n) == M.Place{Some{par}, right} : M.Place}, +e: {M.children(t, Some{par}, right) == Nil{} : List<&2, M.Node>}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +pn: {M.named(t, par) == True{} : Bool}, +h: {M.fits(f, t, siblings) == True{} : Bool}) -> {M.fits(1n+f, M.attach(t, n), siblings) == True{} : Bool}:
  match f:
    case 0n:
      %Equal.sym(List<&2, M.Node>, siblings, Nil{}, nil_of_is_nil(siblings, h)) : {M.fits(1n, M.attach(t, n), _) == True{} : Bool}
      {==}
    case 1n++p:
      match siblings:
        case Nil{}:
          {==}
        case +s <> +rest:
          fits_attach.at(p, t, s, rest, n, par, M.Name.eq(M.Node.name(s), par), {==}, right, hp, e, fr, pn,
            fits_attach(p, t, M.children(t, Some{M.Node.name(s)}, False{}), n, par, right, hp, e, fr, pn, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h)),
            fits_attach(p, t, M.children(t, Some{M.Node.name(s)}, True{}), n, par, right, hp, e, fr, pn, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h))),
            fits_attach(p, t, rest, n, par, right, hp, e, fr, pn, Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h))))

# The descent
# -----------
#
# `leftmost` follows first left children with the element count as fuel.
# `lchain` says the chain below a sibling list ends within the fuel; the
# reading's fuel bound gives it, and it is what makes the descent land on
# an element with no left child — the one the new element becomes the
# only left child of — and makes the fuel not matter past that.
def lchain(fuel: Nat, +t: List<&2, M.Node>, cs: List<&2, M.Node>) -> Bool:
  match fuel:
    case 0n:
      M.is_nil(cs)
    case 1n+p:
      match cs:
        case Nil{}:
          True{}
        case c <> more:
          lchain(p, t, M.children(t, Some{M.Node.name(c)}, False{}))

def lchain_of_fits(fuel: Nat, +t: List<&2, M.Node>, cs: List<&2, M.Node>, h: {M.fits(fuel, t, cs) == True{} : Bool}) -> {lchain(fuel, t, cs) == True{} : Bool}:
  match fuel:
    case 0n:
      h
    case 1n++p:
      match cs:
        case Nil{}:
          {==}
        case +c <> rest:
          lchain_of_fits(p, t, M.children(t, Some{M.Node.name(c)}, False{}), Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(c)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(c)}, True{})), M.fits(p, t, rest)), h))

def leftmost_stay(fuel: Nat, +t: List<&2, M.Node>, +nm: M.Name, +e: {M.children(t, Some{nm}, False{}) == Nil{} : List<&2, M.Node>}) -> {M.leftmost(fuel, t, nm) == nm : M.Name}:
  match fuel:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(List<&2, M.Node>, M.children(t, Some{nm}, False{}), Nil{}, e) : {M.leftmost(p, t, M.head_name(_, nm)) == nm : M.Name}
      leftmost_stay(p, t, nm, e)

def leftmost_lands.at(p: Nat, +t: List<&2, M.Node>, +nm: M.Name, cs: List<&2, M.Node>, +ecs: {M.children(t, Some{nm}, False{}) == cs : List<&2, M.Node>}, h: {lchain(1n+p, t, cs) == True{} : Bool}, ih: @c: M.Node -> {lchain(p, t, M.children(t, Some{M.Node.name(c)}, False{})) == True{} : Bool} -> {M.children(t, Some{M.leftmost(p, t, M.Node.name(c))}, False{}) == Nil{} : List<&2, M.Node>}) -> {M.children(t, Some{M.leftmost(p, t, M.head_name(cs, nm))}, False{}) == Nil{} : List<&2, M.Node>}:
  match cs:
    case Nil{}:
      %Equal.sym(M.Name, M.leftmost(p, t, nm), nm, leftmost_stay(p, t, nm, ecs)) : {M.children(t, Some{_}, False{}) == Nil{} : List<&2, M.Node>}
      ecs
    case c <> more:
      ih(c, h)

def leftmost_lands(fuel: Nat, +t: List<&2, M.Node>, +nm: M.Name, h: {lchain(fuel, t, M.children(t, Some{nm}, False{})) == True{} : Bool}) -> {M.children(t, Some{M.leftmost(fuel, t, nm)}, False{}) == Nil{} : List<&2, M.Node>}:
  match fuel:
    case 0n:
      nil_of_is_nil(M.children(t, Some{nm}, False{}), h)
    case 1n++p:
      leftmost_lands.at(p, t, nm, M.children(t, Some{nm}, False{}), {==}, h, c => h2 => leftmost_lands(p, t, M.Node.name(c), h2))

def le_zero(p: Nat, le: {Nat.is_le(1n+p, 0n) == True{} : Bool}) -> Empty:
  S.false_true(le)

def leftmost_stable.at(+p: Nat, +q: Nat, +t: List<&2, M.Node>, +nm: M.Name, cs: List<&2, M.Node>, +ecs: {M.children(t, Some{nm}, False{}) == cs : List<&2, M.Node>}, h: {lchain(1n+p, t, cs) == True{} : Bool}, le: {Nat.is_le(p, q) == True{} : Bool}, ih: @c: M.Node -> {lchain(p, t, M.children(t, Some{M.Node.name(c)}, False{})) == True{} : Bool} -> {Nat.is_le(p, q) == True{} : Bool} -> {M.leftmost(q, t, M.Node.name(c)) == M.leftmost(p, t, M.Node.name(c)) : M.Name}) -> {M.leftmost(q, t, M.head_name(cs, nm)) == M.leftmost(p, t, M.head_name(cs, nm)) : M.Name}:
  match cs:
    case Nil{}:
      %Equal.sym(M.Name, M.leftmost(q, t, nm), nm, leftmost_stay(q, t, nm, ecs)) : {_ == M.leftmost(p, t, nm) : M.Name}
      %Equal.sym(M.Name, M.leftmost(p, t, nm), nm, leftmost_stay(p, t, nm, ecs)) : {nm == _ : M.Name}
      {==}
    case c <> more:
      ih(c, h, le)

def leftmost_stable(f: Nat, g: Nat, +t: List<&2, M.Node>, +nm: M.Name, +h: {lchain(f, t, M.children(t, Some{nm}, False{})) == True{} : Bool}, le: {Nat.is_le(f, g) == True{} : Bool}) -> {M.leftmost(g, t, nm) == M.leftmost(f, t, nm) : M.Name}:
  match f g:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      %Equal.sym(List<&2, M.Node>, M.children(t, Some{nm}, False{}), Nil{}, nil_of_is_nil(M.children(t, Some{nm}, False{}), h)) : {M.leftmost(q, t, M.head_name(_, nm)) == nm : M.Name}
      leftmost_stay(q, t, nm, nil_of_is_nil(M.children(t, Some{nm}, False{}), h))
    case 1n+p 0n:
      Empty.absurd({M.leftmost(0n, t, nm) == M.leftmost(1n+p, t, nm) : M.Name}, le_zero(p, le))
    case 1n++p 1n++q:
      leftmost_stable.at(p, q, t, nm, M.children(t, Some{nm}, False{}), {==}, h, le, c => h2 => le2 => leftmost_stable(p, q, t, M.Node.name(c), h2, le2))

def leftmost_named.head(+t: List<&2, M.Node>, +nm: M.Name, +c: M.Node, more: List<&2, M.Node>, ecs: {M.children(t, Some{nm}, False{}) == c <> more : List<&2, M.Node>}) -> {M.named(M.children(t, Some{nm}, False{}), M.Node.name(c)) == True{} : Bool}:
  %Equal.sym(List<&2, M.Node>, M.children(t, Some{nm}, False{}), c <> more, ecs) : {M.named(_, M.Node.name(c)) == True{} : Bool}
  or_left(M.Name.eq(M.Node.name(c), M.Node.name(c)), M.named(more, M.Node.name(c)), name_eq_refl(M.Node.name(c)))

def leftmost_named.at(p: Nat, +t: List<&2, M.Node>, +nm: M.Name, cs: List<&2, M.Node>, ecs: {M.children(t, Some{nm}, False{}) == cs : List<&2, M.Node>}, h: {M.named(t, nm) == True{} : Bool}, ih: @x: M.Name -> {M.named(t, x) == True{} : Bool} -> {M.named(t, M.leftmost(p, t, x)) == True{} : Bool}) -> {M.named(t, M.leftmost(p, t, M.head_name(cs, nm))) == True{} : Bool}:
  match cs:
    case Nil{}:
      ih(nm, h)
    case +c <> more:
      ih(M.Node.name(c), children_named(t, Some{nm}, False{}, M.Node.name(c), leftmost_named.head(t, nm, c, more, ecs)))

def leftmost_named(fuel: Nat, +t: List<&2, M.Node>, +nm: M.Name, h: {M.named(t, nm) == True{} : Bool}) -> {M.named(t, M.leftmost(fuel, t, nm)) == True{} : Bool}:
  match fuel:
    case 0n:
      h
    case 1n++p:
      leftmost_named.at(p, t, nm, M.children(t, Some{nm}, False{}), {==}, h, x => h2 => leftmost_named(p, t, x, h2))

# What a reading starts with: the landing of the descent from its first
# sibling.
def starts(xs: List<&2, M.Node>, nm: M.Name) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      M.Name.eq(M.Node.name(x), nm)

def starts_append(xs: List<&2, M.Node>, ys: List<&2, M.Node>, nm: M.Name, h: {starts(xs, nm) == True{} : Bool}) -> {starts(List.append(&2, M.Node, xs, ys), nm) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({starts(ys, nm) == True{} : Bool}, S.false_true(h))
    case x <> rest:
      h

def head_read.at(+p: Nat, +t: List<&2, M.Node>, +c: M.Node, +more: List<&2, M.Node>, cs: List<&2, M.Node>, +ecs: {M.children(t, Some{M.Node.name(c)}, False{}) == cs : List<&2, M.Node>}, h: {M.fits(p, t, cs) == True{} : Bool}, ih: @c1: M.Node -> @m1: List<&2, M.Node> -> {M.fits(p, t, c1 <> m1) == True{} : Bool} -> {starts(M.read_all(p, t, c1 <> m1), M.leftmost(p, t, M.Node.name(c1))) == True{} : Bool}) -> {starts(List.append(&2, M.Node, M.read_all(p, t, cs), c <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(c)}, True{})), M.read_all(p, t, more))), M.leftmost(p, t, M.head_name(cs, M.Node.name(c)))) == True{} : Bool}:
  match cs:
    case Nil{}:
      %Equal.sym(List<&2, M.Node>, M.read_all(p, t, Nil{}), Nil{}, read_nil(p, t)) : {starts(List.append(&2, M.Node, _, c <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(c)}, True{})), M.read_all(p, t, more))), M.leftmost(p, t, M.Node.name(c))) == True{} : Bool}
      %Equal.sym(M.Name, M.leftmost(p, t, M.Node.name(c)), M.Node.name(c), leftmost_stay(p, t, M.Node.name(c), ecs)) : {M.Name.eq(M.Node.name(c), _) == True{} : Bool}
      name_eq_refl(M.Node.name(c))
    case +c1 <> +m1:
      starts_append(M.read_all(p, t, c1 <> m1), c <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(c)}, True{})), M.read_all(p, t, more)), M.leftmost(p, t, M.Node.name(c1)), ih(c1, m1, h))

def head_read(fuel: Nat, +t: List<&2, M.Node>, +c: M.Node, +more: List<&2, M.Node>, h: {M.fits(fuel, t, c <> more) == True{} : Bool}) -> {starts(M.read_all(fuel, t, c <> more), M.leftmost(fuel, t, M.Node.name(c))) == True{} : Bool}:
  match fuel:
    case 0n:
      Empty.absurd({starts(Nil{}, M.leftmost(0n, t, M.Node.name(c))) == True{} : Bool}, S.false_true(h))
    case 1n++p:
      head_read.at(p, t, c, more, M.children(t, Some{M.Node.name(c)}, False{}), {==}, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(c)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(c)}, True{})), M.fits(p, t, more)), h), c1 => m1 => h2 => head_read(p, t, c1, m1, h2))

# An element read has its children's readings within the fuel.
def fits_both(+fuel: Nat, +t: List<&2, M.Node>, +nm: M.Name) -> Bool:
  Bool.and(M.fits(fuel, t, M.children(t, Some{nm}, False{})), M.fits(fuel, t, M.children(t, Some{nm}, True{})))

def fits_both_mono(+fuel: Nat, +t: List<&2, M.Node>, +nm: M.Name, +h: {fits_both(fuel, t, nm) == True{} : Bool}) -> {fits_both(1n+fuel, t, nm) == True{} : Bool}:
  and_intro(M.fits(1n+fuel, t, M.children(t, Some{nm}, False{})), M.fits(1n+fuel, t, M.children(t, Some{nm}, True{})),
    fits_mono(fuel, t, M.children(t, Some{nm}, False{}), Comp.and_left(M.fits(fuel, t, M.children(t, Some{nm}, False{})), M.fits(fuel, t, M.children(t, Some{nm}, True{})), h)),
    fits_mono(fuel, t, M.children(t, Some{nm}, True{}), Comp.and_right(M.fits(fuel, t, M.children(t, Some{nm}, False{})), M.fits(fuel, t, M.children(t, Some{nm}, True{})), h)))

def fits_both_at(+p: Nat, +t: List<&2, M.Node>, +s: M.Node, +nm: M.Name, eq: {M.Node.name(s) == nm : M.Name}, hL: {M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})) == True{} : Bool}, hR: {M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})) == True{} : Bool}) -> {fits_both(p, t, nm) == True{} : Bool}:
  %eq : {fits_both(p, t, _) == True{} : Bool}
  and_intro(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), hL, hR)

def fits_in.at(+p: Nat, +t: List<&2, M.Node>, +s: M.Node, +rest: List<&2, M.Node>, +nm: M.Name, +hL: {M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})) == True{} : Bool}, +hR: {M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})) == True{} : Bool}, hrest: {M.fits(p, t, rest) == True{} : Bool}, b1: Bool, e1: {M.named(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), nm) == b1 : Bool}, b2: Bool, e2: {M.Name.eq(M.Node.name(s), nm) == b2 : Bool}, b3: Bool, e3: {M.named(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), nm) == b3 : Bool}, b4: Bool, e4: {M.named(M.read_all(p, t, rest), nm) == b4 : Bool}, m: {Bool.or(b1, Bool.or(b2, Bool.or(b3, b4))) == True{} : Bool}, ih: @x: List<&2, M.Node> -> {M.fits(p, t, x) == True{} : Bool} -> {M.named(M.read_all(p, t, x), nm) == True{} : Bool} -> {fits_both(p, t, nm) == True{} : Bool}) -> {fits_both(p, t, nm) == True{} : Bool}:
  match b1:
    case True{}:
      ih(M.children(t, Some{M.Node.name(s)}, False{}), hL, e1)
    case False{}:
      match b2:
        case True{}:
          fits_both_at(p, t, s, nm, name_eq_equal(M.Node.name(s), nm, e2), hL, hR)
        case False{}:
          match b3:
            case True{}:
              ih(M.children(t, Some{M.Node.name(s)}, True{}), hR, e3)
            case False{}:
              match b4:
                case True{}:
                  ih(rest, hrest, e4)
                case False{}:
                  Empty.absurd({fits_both(p, t, nm) == True{} : Bool}, S.false_true(m))

def named_read_split(+p: Nat, +t: List<&2, M.Node>, +s: M.Node, +rest: List<&2, M.Node>, +nm: M.Name, m: {M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), nm) == True{} : Bool}) -> {Bool.or(M.named(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), nm), Bool.or(M.Name.eq(M.Node.name(s), nm), Bool.or(M.named(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), nm), M.named(M.read_all(p, t, rest), nm)))) == True{} : Bool}:
  %named_append(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), nm) : {Bool.or(M.named(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), nm), Bool.or(M.Name.eq(M.Node.name(s), nm), _)) == True{} : Bool}
  %named_append(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), nm) : {_ == True{} : Bool}
  m

def fits_in(fuel: Nat, +t: List<&2, M.Node>, siblings: List<&2, M.Node>, +nm: M.Name, +h: {M.fits(fuel, t, siblings) == True{} : Bool}, m: {M.named(M.read_all(fuel, t, siblings), nm) == True{} : Bool}) -> {fits_both(fuel, t, nm) == True{} : Bool}:
  match fuel:
    case 0n:
      Empty.absurd({fits_both(0n, t, nm) == True{} : Bool}, S.false_true(m))
    case 1n++p:
      match siblings:
        case Nil{}:
          Empty.absurd({fits_both(1n+p, t, nm) == True{} : Bool}, S.false_true(m))
        case +s <> +rest:
          fits_both_mono(p, t, nm, fits_in.at(p, t, s, rest, nm,
            Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h),
            Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h)),
            Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h)),
            M.named(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), nm), {==}, M.Name.eq(M.Node.name(s), nm), {==}, M.named(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), nm), {==}, M.named(M.read_all(p, t, rest), nm), {==},
            named_read_split(p, t, s, rest, nm, m), x => hx => mx => fits_in(p, t, x, nm, hx, mx)))

# The next element read
# ---------------------
#
# After an element with a right child, the reading continues with the
# landing of the descent from its first right child: `next_is` says every
# element of the parent's name is followed by one of the landing's.
def follows(hit: Bool, rest: List<&2, M.Node>, l: M.Name) -> Bool:
  match hit:
    case False{}:
      True{}
    case True{}:
      starts(rest, l)

def next_is(xs: List<&2, M.Node>, +par: M.Name, +l: M.Name) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> +rest:
      Bool.and(follows(M.Name.eq(M.Node.name(x), par), rest, l), next_is(rest, par, l))

def follows_append(hit: Bool, rest: List<&2, M.Node>, ys: List<&2, M.Node>, l: M.Name, h: {follows(hit, rest, l) == True{} : Bool}) -> {follows(hit, List.append(&2, M.Node, rest, ys), l) == True{} : Bool}:
  match hit:
    case False{}:
      {==}
    case True{}:
      starts_append(rest, ys, l, h)

def next_is_append(xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +par: M.Name, +l: M.Name, +h1: {next_is(xs, par, l) == True{} : Bool}, h2: {next_is(ys, par, l) == True{} : Bool}) -> {next_is(List.append(&2, M.Node, xs, ys), par, l) == True{} : Bool}:
  match xs:
    case Nil{}:
      h2
    case +x <> +rest:
      and_intro(follows(M.Name.eq(M.Node.name(x), par), List.append(&2, M.Node, rest, ys), l), next_is(List.append(&2, M.Node, rest, ys), par, l),
        follows_append(M.Name.eq(M.Node.name(x), par), rest, ys, l, Comp.and_left(follows(M.Name.eq(M.Node.name(x), par), rest, l), next_is(rest, par, l), h1)),
        next_is_append(rest, ys, par, l, Comp.and_right(follows(M.Name.eq(M.Node.name(x), par), rest, l), next_is(rest, par, l), h1), h2))

def lchain_mono(fuel: Nat, +t: List<&2, M.Node>, cs: List<&2, M.Node>, h: {lchain(fuel, t, cs) == True{} : Bool}) -> {lchain(1n+fuel, t, cs) == True{} : Bool}:
  match fuel:
    case 0n:
      %Equal.sym(List<&2, M.Node>, cs, Nil{}, nil_of_is_nil(cs, h)) : {lchain(1n, t, _) == True{} : Bool}
      {==}
    case 1n++p:
      match cs:
        case Nil{}:
          {==}
        case +c <> more:
          lchain_mono(p, t, M.children(t, Some{M.Node.name(c)}, False{}), h)

# A reading from `c` starts with the descent's landing, at any fuel the
# chain fits in.
def head_read_at(p: Nat, +g: Nat, +t: List<&2, M.Node>, +c: M.Node, +more: List<&2, M.Node>, +h: {M.fits(p, t, c <> more) == True{} : Bool}, le: {Nat.is_le(p, g) == True{} : Bool}) -> {starts(M.read_all(p, t, c <> more), M.leftmost(g, t, M.Node.name(c))) == True{} : Bool}:
  match p:
    case 0n:
      Empty.absurd({starts(Nil{}, M.leftmost(g, t, M.Node.name(c))) == True{} : Bool}, S.false_true(h))
    case 1n++q:
      %Equal.sym(M.Name, M.leftmost(g, t, M.Node.name(c)), M.leftmost(1n+q, t, M.Node.name(c)), leftmost_stable(1n+q, g, t, M.Node.name(c), lchain_mono(q, t, M.children(t, Some{M.Node.name(c)}, False{}), lchain_of_fits(q, t, M.children(t, Some{M.Node.name(c)}, False{}), Comp.and_left(M.fits(q, t, M.children(t, Some{M.Node.name(c)}, False{})), Bool.and(M.fits(q, t, M.children(t, Some{M.Node.name(c)}, True{})), M.fits(q, t, more)), h))), le)) : {starts(M.read_all(1n+q, t, c <> more), _) == True{} : Bool}
      head_read(1n+q, t, c, more, h)

def children_transport2(+t: List<&2, M.Node>, +a: M.Name, +b: M.Name, +r: Bool, +cs: List<&2, M.Node>, eq: {a == b : M.Name}, e: {M.children(t, Some{b}, r) == cs : List<&2, M.Node>}) -> {M.children(t, Some{a}, r) == cs : List<&2, M.Node>}:
  %Equal.sym(M.Name, a, b, eq) : {M.children(t, Some{_}, r) == cs : List<&2, M.Node>}
  e

def fits_transport(+p: Nat, +t: List<&2, M.Node>, +a: List<&2, M.Node>, +b: List<&2, M.Node>, e: {a == b : List<&2, M.Node>}, h: {M.fits(p, t, a) == True{} : Bool}) -> {M.fits(p, t, b) == True{} : Bool}:
  %e : {M.fits(p, t, _) == True{} : Bool}
  h

def next_is_read.follow(+p: Nat, +g: Nat, +t: List<&2, M.Node>, +s: M.Node, +rest: List<&2, M.Node>, +par: M.Name, +c: M.Node, +more: List<&2, M.Node>, hit: Bool, +eh: {M.Name.eq(M.Node.name(s), par) == hit : Bool}, +e: {M.children(t, Some{par}, True{}) == c <> more : List<&2, M.Node>}, hR: {M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})) == True{} : Bool}, le: {Nat.is_le(p, g) == True{} : Bool}) -> {follows(hit, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.leftmost(g, t, M.Node.name(c))) == True{} : Bool}:
  match hit:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(List<&2, M.Node>, M.children(t, Some{M.Node.name(s)}, True{}), c <> more, children_transport2(t, M.Node.name(s), par, True{}, c <> more, name_eq_equal(M.Node.name(s), par, eh), e)) : {starts(List.append(&2, M.Node, M.read_all(p, t, _), M.read_all(p, t, rest)), M.leftmost(g, t, M.Node.name(c))) == True{} : Bool}
      starts_append(M.read_all(p, t, c <> more), M.read_all(p, t, rest), M.leftmost(g, t, M.Node.name(c)), head_read_at(p, g, t, c, more, fits_transport(p, t, M.children(t, Some{M.Node.name(s)}, True{}), c <> more, children_transport2(t, M.Node.name(s), par, True{}, c <> more, name_eq_equal(M.Node.name(s), par, eh), e), hR), le))

def next_is_read(f: Nat, +t: List<&2, M.Node>, siblings: List<&2, M.Node>, +par: M.Name, +c: M.Node, +more: List<&2, M.Node>, +g: Nat, +h: {M.fits(f, t, siblings) == True{} : Bool}, +e: {M.children(t, Some{par}, True{}) == c <> more : List<&2, M.Node>}, +le: {Nat.is_le(f, 1n+g) == True{} : Bool}) -> {next_is(M.read_all(f, t, siblings), par, M.leftmost(g, t, M.Node.name(c))) == True{} : Bool}:
  match f:
    case 0n:
      {==}
    case 1n++p:
      match siblings:
        case Nil{}:
          {==}
        case +s <> +rest:
          next_is_append(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par, M.leftmost(g, t, M.Node.name(c)),
            next_is_read(p, t, M.children(t, Some{M.Node.name(s)}, False{}), par, c, more, g, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h), e, Comp.le_succ(p, g, le)),
            and_intro(follows(M.Name.eq(M.Node.name(s), par), List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.leftmost(g, t, M.Node.name(c))), next_is(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par, M.leftmost(g, t, M.Node.name(c))),
              next_is_read.follow(p, g, t, s, rest, par, c, more, M.Name.eq(M.Node.name(s), par), {==}, e, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h)), le),
              next_is_append(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), par, M.leftmost(g, t, M.Node.name(c)),
                next_is_read(p, t, M.children(t, Some{M.Node.name(s)}, True{}), par, c, more, g, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h)), e, Comp.le_succ(p, g, le)),
                next_is_read(p, t, rest, par, c, more, g, Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h)), e, Comp.le_succ(p, g, le)))))

# Splicing a reading that reads no element twice
# ----------------------------------------------

def named_transport(+xs: List<&2, M.Node>, +a: M.Name, +b: M.Name, eq: {a == b : M.Name}, h: {M.named(xs, a) == False{} : Bool}) -> {M.named(xs, b) == False{} : Bool}:
  %eq : {M.named(xs, _) == False{} : Bool}
  h

def named_transport_true(+xs: List<&2, M.Node>, +a: M.Name, +b: M.Name, eq: {a == b : M.Name}, h: {M.named(xs, a) == True{} : Bool}) -> {M.named(xs, b) == True{} : Bool}:
  %eq : {M.named(xs, _) == True{} : Bool}
  h

def named_splice_at(+x: M.Node, +rest: List<&2, M.Node>, +n: M.Node, hit: Bool, right: Bool, +nm: M.Name, hx: {M.Name.eq(M.Node.name(x), nm) == False{} : Bool}, hr: {M.named(rest, nm) == False{} : Bool}, ne: {M.Name.eq(M.Node.name(n), nm) == False{} : Bool}) -> {M.named(splice.at(x, rest, n, hit, right), nm) == False{} : Bool}:
  match hit:
    case False{}:
      or_false(M.Name.eq(M.Node.name(x), nm), M.named(rest, nm), hx, hr)
    case True{}:
      match right:
        case True{}:
          or_false(M.Name.eq(M.Node.name(x), nm), M.named(n <> rest, nm), hx, or_false(M.Name.eq(M.Node.name(n), nm), M.named(rest, nm), ne, hr))
        case False{}:
          or_false(M.Name.eq(M.Node.name(n), nm), M.named(x <> rest, nm), ne, or_false(M.Name.eq(M.Node.name(x), nm), M.named(rest, nm), hx, hr))

def named_splice_not(xs: List<&2, M.Node>, +par: M.Name, +right: Bool, +n: M.Node, +nm: M.Name, +h: {M.named(xs, nm) == False{} : Bool}, +ne: {M.Name.eq(M.Node.name(n), nm) == False{} : Bool}) -> {M.named(splice(xs, par, right, n), nm) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      named_splice_at(x, splice(rest, par, right, n), n, M.Name.eq(M.Node.name(x), par), right, nm, or_false_l(M.Name.eq(M.Node.name(x), nm), M.named(rest, nm), h), named_splice_not(rest, par, right, n, nm, or_false_r(M.Name.eq(M.Node.name(x), nm), M.named(rest, nm), h), ne), ne)

def splice_absent(xs: List<&2, M.Node>, +par: M.Name, +right: Bool, +n: M.Node, +h: {M.named(xs, par) == False{} : Bool}) -> {splice(xs, par, right, n) == xs : List<&2, M.Node>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, M.Name.eq(M.Node.name(x), par), False{}, or_false_l(M.Name.eq(M.Node.name(x), par), M.named(rest, par), h)) : {splice.at(x, splice(rest, par, right, n), n, _, right) == x <> rest : List<&2, M.Node>}
      cons_cong(x, splice(rest, par, right, n), rest, splice_absent(rest, par, right, n, or_false_r(M.Name.eq(M.Node.name(x), par), M.named(rest, par), h)))

def nodup_splice.at(+x: M.Node, +par: M.Name, +n: M.Node, hit: Bool, +eh: {M.Name.eq(M.Node.name(x), par) == hit : Bool}, +right: Bool, +rest: List<&2, M.Node>, +nx: {M.named(rest, M.Node.name(x)) == False{} : Bool}, +ndr: {M.nodup(rest) == True{} : Bool}, +fx: {M.Name.eq(M.Node.name(x), M.Node.name(n)) == False{} : Bool}, +fr: {M.named(rest, M.Node.name(n)) == False{} : Bool}, ih: {M.nodup(splice(rest, par, right, n)) == True{} : Bool}) -> {M.nodup(splice.at(x, splice(rest, par, right, n), n, hit, right)) == True{} : Bool}:
  match hit:
    case False{}:
      and_intro(Bool.not(M.named(splice(rest, par, right, n), M.Node.name(x))), M.nodup(splice(rest, par, right, n)), not_true(M.named(splice(rest, par, right, n), M.Node.name(x)), named_splice_not(rest, par, right, n, M.Node.name(x), nx, name_ne_sym(M.Node.name(x), M.Node.name(n), fx))), ih)
    case True{}:
      match right:
        case True{}:
          %Equal.sym(List<&2, M.Node>, splice(rest, par, True{}, n), rest, splice_absent(rest, par, True{}, n, named_transport(rest, M.Node.name(x), par, name_eq_equal(M.Node.name(x), par, eh), nx))) : {M.nodup(splice.at(x, _, n, True{}, True{})) == True{} : Bool}
          and_intro(Bool.not(M.named(n <> rest, M.Node.name(x))), M.nodup(n <> rest), not_true(M.named(n <> rest, M.Node.name(x)), or_false(M.Name.eq(M.Node.name(n), M.Node.name(x)), M.named(rest, M.Node.name(x)), name_ne_sym(M.Node.name(x), M.Node.name(n), fx), nx)), and_intro(Bool.not(M.named(rest, M.Node.name(n))), M.nodup(rest), not_true(M.named(rest, M.Node.name(n)), fr), ndr))
        case False{}:
          %Equal.sym(List<&2, M.Node>, splice(rest, par, False{}, n), rest, splice_absent(rest, par, False{}, n, named_transport(rest, M.Node.name(x), par, name_eq_equal(M.Node.name(x), par, eh), nx))) : {M.nodup(splice.at(x, _, n, True{}, False{})) == True{} : Bool}
          and_intro(Bool.not(M.named(x <> rest, M.Node.name(n))), M.nodup(x <> rest), not_true(M.named(x <> rest, M.Node.name(n)), or_false(M.Name.eq(M.Node.name(x), M.Node.name(n)), M.named(rest, M.Node.name(n)), fx, fr)), and_intro(Bool.not(M.named(rest, M.Node.name(x))), M.nodup(rest), not_true(M.named(rest, M.Node.name(x)), nx), ndr))

def nodup_splice(xs: List<&2, M.Node>, +par: M.Name, +right: Bool, +n: M.Node, +nd: {M.nodup(xs) == True{} : Bool}, +fr: {M.named(xs, M.Node.name(n)) == False{} : Bool}) -> {M.nodup(splice(xs, par, right, n)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      nodup_splice.at(x, par, n, M.Name.eq(M.Node.name(x), par), {==}, right, rest,
        not_of_true(M.named(rest, M.Node.name(x)), Comp.and_left(Bool.not(M.named(rest, M.Node.name(x))), M.nodup(rest), nd)),
        Comp.and_right(Bool.not(M.named(rest, M.Node.name(x))), M.nodup(rest), nd),
        or_false_l(M.Name.eq(M.Node.name(x), M.Node.name(n)), M.named(rest, M.Node.name(n)), fr),
        or_false_r(M.Name.eq(M.Node.name(x), M.Node.name(n)), M.named(rest, M.Node.name(n)), fr),
        nodup_splice(rest, par, right, n, Comp.and_right(Bool.not(M.named(rest, M.Node.name(x))), M.nodup(rest), nd), or_false_r(M.Name.eq(M.Node.name(x), M.Node.name(n)), M.named(rest, M.Node.name(n)), fr)))

# Before the landing is after the element it follows.
def next_is_named.at(+x: M.Node, +par: M.Name, +l: M.Name, hit: Bool, eh: {M.Name.eq(M.Node.name(x), par) == hit : Bool}, rest: List<&2, M.Node>, fo: {follows(hit, rest, l) == True{} : Bool}, hp: {Bool.or(hit, M.named(rest, par)) == True{} : Bool}, ih: {M.named(rest, par) == True{} : Bool} -> {M.named(rest, l) == True{} : Bool}) -> {M.named(x <> rest, l) == True{} : Bool}:
  match hit:
    case False{}:
      or_right(M.Name.eq(M.Node.name(x), l), M.named(rest, l), ih(hp))
    case True{}:
      match rest:
        case Nil{}:
          Empty.absurd({M.named([x], l) == True{} : Bool}, S.false_true(fo))
        case +y <> +more:
          or_right(M.Name.eq(M.Node.name(x), l), M.named(y <> more, l), or_left(M.Name.eq(M.Node.name(y), l), M.named(more, l), fo))

def next_is_named(xs: List<&2, M.Node>, +par: M.Name, +l: M.Name, +ni: {next_is(xs, par, l) == True{} : Bool}, hp: {M.named(xs, par) == True{} : Bool}) -> {M.named(xs, l) == True{} : Bool}:
  match xs:
    case Nil{}:
      hp
    case +x <> +rest:
      next_is_named.at(x, par, l, M.Name.eq(M.Node.name(x), par), {==}, rest, Comp.and_left(follows(M.Name.eq(M.Node.name(x), par), rest, l), next_is(rest, par, l), ni), hp, h2 => next_is_named(rest, par, l, Comp.and_right(follows(M.Name.eq(M.Node.name(x), par), rest, l), next_is(rest, par, l), ni), h2))

# With `x` named `par`, `y` named `l`, and neither name in `more`, both
# splices are `x <> n <> y <> more`.
def splice_swap.hit2(+x: M.Node, +par: M.Name, +l: M.Name, +n: M.Node, eq: {M.Node.name(x) == par : M.Name}, +y: M.Node, +more: List<&2, M.Node>, +eqy: {M.Node.name(y) == l : M.Name}, +yx: {M.Name.eq(M.Node.name(y), M.Node.name(x)) == False{} : Bool}, +mx: {M.named(more, M.Node.name(x)) == False{} : Bool}, +my: {M.named(more, M.Node.name(y)) == False{} : Bool}) -> {splice(x <> y <> more, l, False{}, n) == splice(x <> y <> more, par, True{}, n) : List<&2, M.Node>}:
  %eq : {splice(x <> y <> more, l, False{}, n) == splice(x <> y <> more, _, True{}, n) : List<&2, M.Node>}
  %eqy : {splice(x <> y <> more, _, False{}, n) == splice(x <> y <> more, M.Node.name(x), True{}, n) : List<&2, M.Node>}
  %Equal.sym(Bool, M.Name.eq(M.Node.name(x), M.Node.name(y)), False{}, name_ne_sym(M.Node.name(y), M.Node.name(x), yx)) : {splice.at(x, splice.at(y, splice(more, M.Node.name(y), False{}, n), n, M.Name.eq(M.Node.name(y), M.Node.name(y)), False{}), n, _, False{}) == splice.at(x, splice.at(y, splice(more, M.Node.name(x), True{}, n), n, M.Name.eq(M.Node.name(y), M.Node.name(x)), True{}), n, M.Name.eq(M.Node.name(x), M.Node.name(x)), True{}) : List<&2, M.Node>}
  %Equal.sym(Bool, M.Name.eq(M.Node.name(y), M.Node.name(y)), True{}, name_eq_refl(M.Node.name(y))) : {splice.at(x, splice.at(y, splice(more, M.Node.name(y), False{}, n), n, _, False{}), n, False{}, False{}) == splice.at(x, splice.at(y, splice(more, M.Node.name(x), True{}, n), n, M.Name.eq(M.Node.name(y), M.Node.name(x)), True{}), n, M.Name.eq(M.Node.name(x), M.Node.name(x)), True{}) : List<&2, M.Node>}
  %Equal.sym(Bool, M.Name.eq(M.Node.name(y), M.Node.name(x)), False{}, yx) : {splice.at(x, splice.at(y, splice(more, M.Node.name(y), False{}, n), n, True{}, False{}), n, False{}, False{}) == splice.at(x, splice.at(y, splice(more, M.Node.name(x), True{}, n), n, _, True{}), n, M.Name.eq(M.Node.name(x), M.Node.name(x)), True{}) : List<&2, M.Node>}
  %Equal.sym(Bool, M.Name.eq(M.Node.name(x), M.Node.name(x)), True{}, name_eq_refl(M.Node.name(x))) : {splice.at(x, splice.at(y, splice(more, M.Node.name(y), False{}, n), n, True{}, False{}), n, False{}, False{}) == splice.at(x, splice.at(y, splice(more, M.Node.name(x), True{}, n), n, False{}, True{}), n, _, True{}) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, splice(more, M.Node.name(y), False{}, n), more, splice_absent(more, M.Node.name(y), False{}, n, my)) : {splice.at(x, splice.at(y, _, n, True{}, False{}), n, False{}, False{}) == splice.at(x, splice.at(y, splice(more, M.Node.name(x), True{}, n), n, False{}, True{}), n, True{}, True{}) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, splice(more, M.Node.name(x), True{}, n), more, splice_absent(more, M.Node.name(x), True{}, n, mx)) : {splice.at(x, splice.at(y, more, n, True{}, False{}), n, False{}, False{}) == splice.at(x, splice.at(y, _, n, False{}, True{}), n, True{}, True{}) : List<&2, M.Node>}
  {==}

def splice_swap.hit(+x: M.Node, +par: M.Name, +l: M.Name, +n: M.Node, +eq: {M.Node.name(x) == par : M.Name}, rest: List<&2, M.Node>, +ni: {Bool.and(starts(rest, l), next_is(rest, par, l)) == True{} : Bool}, +nd: {Bool.and(Bool.not(M.named(rest, M.Node.name(x))), M.nodup(rest)) == True{} : Bool}) -> {splice(x <> rest, l, False{}, n) == splice(x <> rest, par, True{}, n) : List<&2, M.Node>}:
  match rest:
    case Nil{}:
      Empty.absurd({splice([x], l, False{}, n) == splice([x], par, True{}, n) : List<&2, M.Node>}, S.false_true(Comp.and_left(starts(Nil{}, l), next_is(Nil{}, par, l), ni)))
    case +y <> +more:
      splice_swap.hit2(x, par, l, n, eq, y, more, name_eq_equal(M.Node.name(y), l, Comp.and_left(starts(y <> more, l), next_is(y <> more, par, l), ni)),
        or_false_l(M.Name.eq(M.Node.name(y), M.Node.name(x)), M.named(more, M.Node.name(x)), not_of_true(M.named(y <> more, M.Node.name(x)), Comp.and_left(Bool.not(M.named(y <> more, M.Node.name(x))), M.nodup(y <> more), nd))),
        or_false_r(M.Name.eq(M.Node.name(y), M.Node.name(x)), M.named(more, M.Node.name(x)), not_of_true(M.named(y <> more, M.Node.name(x)), Comp.and_left(Bool.not(M.named(y <> more, M.Node.name(x))), M.nodup(y <> more), nd))),
        not_of_true(M.named(more, M.Node.name(y)), Comp.and_left(Bool.not(M.named(more, M.Node.name(y))), M.nodup(more), Comp.and_right(Bool.not(M.named(y <> more, M.Node.name(x))), M.nodup(y <> more), nd))))

def splice_swap.at(+x: M.Node, +par: M.Name, +l: M.Name, +n: M.Node, hit: Bool, +eh: {M.Name.eq(M.Node.name(x), par) == hit : Bool}, +rest: List<&2, M.Node>, +ni: {Bool.and(follows(hit, rest, l), next_is(rest, par, l)) == True{} : Bool}, +nd: {Bool.and(Bool.not(M.named(rest, M.Node.name(x))), M.nodup(rest)) == True{} : Bool}, +hp: {Bool.or(hit, M.named(rest, par)) == True{} : Bool}, ih: {M.named(rest, par) == True{} : Bool} -> {splice(rest, l, False{}, n) == splice(rest, par, True{}, n) : List<&2, M.Node>}) -> {splice(x <> rest, l, False{}, n) == splice(x <> rest, par, True{}, n) : List<&2, M.Node>}:
  match hit:
    case True{}:
      splice_swap.hit(x, par, l, n, name_eq_equal(M.Node.name(x), par, eh), rest, ni, nd)
    case False{}:
      %Equal.sym(Bool, M.Name.eq(M.Node.name(x), par), False{}, eh) : {splice.at(x, splice(rest, l, False{}, n), n, M.Name.eq(M.Node.name(x), l), False{}) == splice.at(x, splice(rest, par, True{}, n), n, _, True{}) : List<&2, M.Node>}
      %Equal.sym(Bool, M.Name.eq(M.Node.name(x), l), False{}, name_ne_sym(l, M.Node.name(x), named_ne(rest, l, M.Node.name(x), next_is_named(rest, par, l, Comp.and_right(follows(False{}, rest, l), next_is(rest, par, l), ni), hp), not_of_true(M.named(rest, M.Node.name(x)), Comp.and_left(Bool.not(M.named(rest, M.Node.name(x))), M.nodup(rest), nd))))) : {splice.at(x, splice(rest, l, False{}, n), n, _, False{}) == x <> splice(rest, par, True{}, n) : List<&2, M.Node>}
      cons_cong(x, splice(rest, l, False{}, n), splice(rest, par, True{}, n), ih(hp))

def splice_swap(xs: List<&2, M.Node>, +par: M.Name, +l: M.Name, +n: M.Node, +ni: {next_is(xs, par, l) == True{} : Bool}, +nd: {M.nodup(xs) == True{} : Bool}, hp: {M.named(xs, par) == True{} : Bool}) -> {splice(xs, l, False{}, n) == splice(xs, par, True{}, n) : List<&2, M.Node>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      splice_swap.at(x, par, l, n, M.Name.eq(M.Node.name(x), par), {==}, rest, ni, nd, hp, h2 => splice_swap(rest, par, l, n, Comp.and_right(follows(M.Name.eq(M.Node.name(x), par), rest, l), next_is(rest, par, l), ni), Comp.and_right(Bool.not(M.named(rest, M.Node.name(x))), M.nodup(rest), nd), h2))

def splice_starts(xs: List<&2, M.Node>, +l: M.Name, +n: M.Node, +st: {starts(xs, l) == True{} : Bool}, nd: {M.nodup(xs) == True{} : Bool}) -> {splice(xs, l, False{}, n) == n <> xs : List<&2, M.Node>}:
  match xs:
    case Nil{}:
      Empty.absurd({Nil{} == [n] : List<&2, M.Node>}, S.false_true(st))
    case +x <> +rest:
      %Equal.sym(Bool, M.Name.eq(M.Node.name(x), l), True{}, st) : {splice.at(x, splice(rest, l, False{}, n), n, _, False{}) == n <> x <> rest : List<&2, M.Node>}
      %Equal.sym(List<&2, M.Node>, splice(rest, l, False{}, n), rest, splice_absent(rest, l, False{}, n, named_transport(rest, M.Node.name(x), l, name_eq_equal(M.Node.name(x), l, st), not_of_true(M.named(rest, M.Node.name(x)), Comp.and_left(Bool.not(M.named(rest, M.Node.name(x))), M.nodup(rest), nd))))) : {n <> x <> _ == n <> x <> rest : List<&2, M.Node>}
      {==}

# Tombstones
# ----------
#
# The visible reading is the reading with the tombstones left out; a
# splice after a visible element commutes with leaving them out.
def standing_cons(+n: M.Node, xs: List<&2, M.Node>, hs: {M.Node.standing(n) == True{} : Bool}) -> {M.standing(n <> xs) == n <> M.standing(xs) : List<&2, M.Node>}:
  %Equal.sym(Bool, M.Node.standing(n), True{}, hs) : {List.filter.put(M.Node, n, M.standing(xs), _) == n <> M.standing(xs) : List<&2, M.Node>}
  {==}

def nodup_standing.at(+x: M.Node, +rest: List<&2, M.Node>, up: Bool, nx: {Bool.not(M.named(rest, M.Node.name(x))) == True{} : Bool}, ih: {M.nodup(M.standing(rest)) == True{} : Bool}) -> {M.nodup(List.filter.put(M.Node, x, M.standing(rest), up)) == True{} : Bool}:
  match up:
    case True{}:
      and_intro(Bool.not(M.named(M.standing(rest), M.Node.name(x))), M.nodup(M.standing(rest)), not_true(M.named(M.standing(rest), M.Node.name(x)), standing_sub(rest, M.Node.name(x), not_of_true(M.named(rest, M.Node.name(x)), nx))), ih)
    case False{}:
      ih

def nodup_standing(xs: List<&2, M.Node>, +nd: {M.nodup(xs) == True{} : Bool}) -> {M.nodup(M.standing(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      nodup_standing.at(x, rest, M.Node.standing(x), Comp.and_left(Bool.not(M.named(rest, M.Node.name(x))), M.nodup(rest), nd), nodup_standing(rest, Comp.and_right(Bool.not(M.named(rest, M.Node.name(x))), M.nodup(rest), nd)))

def standing_splice.at(+x: M.Node, +par: M.Name, +n: M.Node, hit: Bool, +eh: {M.Name.eq(M.Node.name(x), par) == hit : Bool}, up: Bool, +eu: {M.Node.standing(x) == up : Bool}, +rest: List<&2, M.Node>, +nd: {Bool.and(Bool.not(M.named(rest, M.Node.name(x))), M.nodup(rest)) == True{} : Bool}, hL: {M.named(List.filter.put(M.Node, x, M.standing(rest), up), par) == True{} : Bool}, +hs: {M.Node.standing(n) == True{} : Bool}, ih: {M.named(M.standing(rest), par) == True{} : Bool} -> {M.standing(splice(rest, par, True{}, n)) == splice(M.standing(rest), par, True{}, n) : List<&2, M.Node>}) -> {M.standing(splice.at(x, splice(rest, par, True{}, n), n, hit, True{})) == splice(List.filter.put(M.Node, x, M.standing(rest), up), par, True{}, n) : List<&2, M.Node>}:
  match hit:
    case True{}:
      match up:
        case True{}:
          %Equal.sym(Bool, M.Node.standing(x), True{}, eu) : {List.filter.put(M.Node, x, M.standing(n <> splice(rest, par, True{}, n)), _) == splice(x <> M.standing(rest), par, True{}, n) : List<&2, M.Node>}
          %Equal.sym(Bool, M.Node.standing(n), True{}, hs) : {x <> List.filter.put(M.Node, n, M.standing(splice(rest, par, True{}, n)), _) == splice(x <> M.standing(rest), par, True{}, n) : List<&2, M.Node>}
          %Equal.sym(List<&2, M.Node>, splice(rest, par, True{}, n), rest, splice_absent(rest, par, True{}, n, named_transport(rest, M.Node.name(x), par, name_eq_equal(M.Node.name(x), par, eh), not_of_true(M.named(rest, M.Node.name(x)), Comp.and_left(Bool.not(M.named(rest, M.Node.name(x))), M.nodup(rest), nd))))) : {x <> n <> M.standing(_) == splice(x <> M.standing(rest), par, True{}, n) : List<&2, M.Node>}
          %Equal.sym(Bool, M.Name.eq(M.Node.name(x), par), True{}, eh) : {x <> n <> M.standing(rest) == splice.at(x, splice(M.standing(rest), par, True{}, n), n, _, True{}) : List<&2, M.Node>}
          %Equal.sym(List<&2, M.Node>, splice(M.standing(rest), par, True{}, n), M.standing(rest), splice_absent(M.standing(rest), par, True{}, n, standing_sub(rest, par, named_transport(rest, M.Node.name(x), par, name_eq_equal(M.Node.name(x), par, eh), not_of_true(M.named(rest, M.Node.name(x)), Comp.and_left(Bool.not(M.named(rest, M.Node.name(x))), M.nodup(rest), nd)))))) : {x <> n <> M.standing(rest) == x <> n <> _ : List<&2, M.Node>}
          {==}
        case False{}:
          Empty.absurd({M.standing(x <> n <> splice(rest, par, True{}, n)) == splice(M.standing(rest), par, True{}, n) : List<&2, M.Node>}, S.false_true(Equal.trans(Bool, False{}, M.named(rest, par), True{}, Equal.sym(Bool, M.named(rest, par), False{}, named_transport(rest, M.Node.name(x), par, name_eq_equal(M.Node.name(x), par, eh), not_of_true(M.named(rest, M.Node.name(x)), Comp.and_left(Bool.not(M.named(rest, M.Node.name(x))), M.nodup(rest), nd)))), standing_named(rest, par, hL))))
    case False{}:
      match up:
        case True{}:
          %Equal.sym(Bool, M.Node.standing(x), True{}, eu) : {List.filter.put(M.Node, x, M.standing(splice(rest, par, True{}, n)), _) == splice(x <> M.standing(rest), par, True{}, n) : List<&2, M.Node>}
          %Equal.sym(Bool, M.Name.eq(M.Node.name(x), par), False{}, eh) : {x <> M.standing(splice(rest, par, True{}, n)) == splice.at(x, splice(M.standing(rest), par, True{}, n), n, _, True{}) : List<&2, M.Node>}
          cons_cong(x, M.standing(splice(rest, par, True{}, n)), splice(M.standing(rest), par, True{}, n), ih(or_cases({M.named(M.standing(rest), par) == True{} : Bool}, M.Name.eq(M.Node.name(x), par), M.named(M.standing(rest), par), hL, e => Empty.absurd({M.named(M.standing(rest), par) == True{} : Bool}, S.false_true(Equal.trans(Bool, False{}, M.Name.eq(M.Node.name(x), par), True{}, Equal.sym(Bool, M.Name.eq(M.Node.name(x), par), False{}, eh), e))), e => e)))
        case False{}:
          %Equal.sym(Bool, M.Node.standing(x), False{}, eu) : {List.filter.put(M.Node, x, M.standing(splice(rest, par, True{}, n)), _) == splice(M.standing(rest), par, True{}, n) : List<&2, M.Node>}
          ih(hL)

def standing_splice(xs: List<&2, M.Node>, +par: M.Name, +n: M.Node, +nd: {M.nodup(xs) == True{} : Bool}, hL: {M.named(M.standing(xs), par) == True{} : Bool}, +hs: {M.Node.standing(n) == True{} : Bool}) -> {M.standing(splice(xs, par, True{}, n)) == splice(M.standing(xs), par, True{}, n) : List<&2, M.Node>}:
  match xs:
    case Nil{}:
      Empty.absurd({Nil{} == Nil{} : List<&2, M.Node>}, S.false_true(hL))
    case +x <> +rest:
      standing_splice.at(x, par, n, M.Name.eq(M.Node.name(x), par), {==}, M.Node.standing(x), {==}, rest, nd, hL, hs, h2 => standing_splice(rest, par, n, Comp.and_right(Bool.not(M.named(rest, M.Node.name(x))), M.nodup(rest), nd), h2, hs))

# The splice after the element at a visible position is the insertion
# at the gap after it.
def take_zero(xs: List<&2, M.Node>) -> {List.take(&2, M.Node, xs, 0n) == Nil{} : List<&2, M.Node>}:
  match xs:
    case Nil{}:
      {==}
    case h <> rest:
      {==}

def drop_zero(xs: List<&2, M.Node>) -> {List.drop(&2, M.Node, xs, 0n) == xs : List<&2, M.Node>}:
  match xs:
    case Nil{}:
      {==}
    case h <> rest:
      {==}

# The root insertion
# ------------------
#
# An insert at the front of an empty view: the element becomes the one
# root.
def splice_get(xs: List<&2, M.Node>, p: Nat, +x: M.Node, +n: M.Node, +e: {List.get(&2, M.Node, xs, p) == Some{x} : Maybe<&2, M.Node>}, +nd: {M.nodup(xs) == True{} : Bool}) -> {splice(xs, M.Node.name(x), True{}, n) == List.append(&2, M.Node, List.take(&2, M.Node, xs, 1n+p), n <> List.drop(&2, M.Node, xs, 1n+p)) : List<&2, M.Node>}:
  match xs:
    case Nil{}:
      Empty.absurd({Nil{} == [n] : List<&2, M.Node>}, ML.none_some(x, e))
    case +h <> +rest:
      match p:
        case 0n:
          %Equal.sym(List<&2, M.Node>, List.take(&2, M.Node, rest, 0n), Nil{}, take_zero(rest)) : {splice(h <> rest, M.Node.name(x), True{}, n) == h <> List.append(&2, M.Node, _, n <> List.drop(&2, M.Node, rest, 0n)) : List<&2, M.Node>}
          %Equal.sym(List<&2, M.Node>, List.drop(&2, M.Node, rest, 0n), rest, drop_zero(rest)) : {splice(h <> rest, M.Node.name(x), True{}, n) == h <> n <> _ : List<&2, M.Node>}
          %ML.some_node(h, x, e) : {splice(h <> rest, M.Node.name(_), True{}, n) == h <> n <> rest : List<&2, M.Node>}
          %Equal.sym(Bool, M.Name.eq(M.Node.name(h), M.Node.name(h)), True{}, name_eq_refl(M.Node.name(h))) : {splice.at(h, splice(rest, M.Node.name(h), True{}, n), n, _, True{}) == h <> n <> rest : List<&2, M.Node>}
          %Equal.sym(List<&2, M.Node>, splice(rest, M.Node.name(h), True{}, n), rest, splice_absent(rest, M.Node.name(h), True{}, n, not_of_true(M.named(rest, M.Node.name(h)), Comp.and_left(Bool.not(M.named(rest, M.Node.name(h))), M.nodup(rest), nd)))) : {h <> n <> _ == h <> n <> rest : List<&2, M.Node>}
          {==}
        case 1n++q:
          %Equal.sym(Bool, M.Name.eq(M.Node.name(h), M.Node.name(x)), False{}, name_ne_sym(M.Node.name(x), M.Node.name(h), named_ne(rest, M.Node.name(x), M.Node.name(h), get_named(rest, q, x, e), not_of_true(M.named(rest, M.Node.name(h)), Comp.and_left(Bool.not(M.named(rest, M.Node.name(h))), M.nodup(rest), nd))))) : {splice.at(h, splice(rest, M.Node.name(x), True{}, n), n, _, True{}) == h <> List.append(&2, M.Node, List.take(&2, M.Node, rest, 1n+q), n <> List.drop(&2, M.Node, rest, 1n+q)) : List<&2, M.Node>}
          cons_cong(h, splice(rest, M.Node.name(x), True{}, n), List.append(&2, M.Node, List.take(&2, M.Node, rest, 1n+q), n <> List.drop(&2, M.Node, rest, 1n+q)), splice_get(rest, q, x, n, e, Comp.and_right(Bool.not(M.named(rest, M.Node.name(h))), M.nodup(rest), nd)))

def hangs_none(n: M.Node, +ns: M.Name, +r: Bool, +right: Bool, hp: {M.Node.place(n) == M.Place{None{}, right} : M.Place}) -> {M.Node.hangs(n, Some{ns}, r) == False{} : Bool}:
  match n:
    case M.Node{x, it, pl, d}:
      %Equal.sym(M.Place, pl, M.Place{None{}, right}, hp) : {M.Node.hangs(M.Node{x, it, _, d}, Some{ns}, r) == False{} : Bool}
      {==}

def hangs_root_true(n: M.Node, hp: {M.Node.place(n) == M.Place{None{}, True{}} : M.Place}) -> {M.Node.hangs(n, None{}, True{}) == True{} : Bool}:
  match n:
    case M.Node{x, it, pl, d}:
      %Equal.sym(M.Place, pl, M.Place{None{}, True{}}, hp) : {M.Node.hangs(M.Node{x, it, _, d}, None{}, True{}) == True{} : Bool}
      {==}

def children_attach_fresh_root(+t: List<&2, M.Node>, +n: M.Node, +r: Bool, +hp: {M.Node.place(n) == M.Place{None{}, True{}} : M.Place}, fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}) -> {M.children(M.attach(t, n), Some{M.Node.name(n)}, r) == Nil{} : List<&2, M.Node>}:
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(n)}, r), M.children(t, Some{M.Node.name(n)}, r), children_attach_other(t, n, Some{M.Node.name(n)}, r, hangs_none(n, M.Node.name(n), r, True{}, hp))) : {_ == Nil{} : List<&2, M.Node>}
  children_none(t, M.Node.name(n), r, not_of_true(M.hangs_under(t, M.Node.name(n)), Comp.and_right(Bool.not(M.named(t, M.Node.name(n))), Bool.not(M.hangs_under(t, M.Node.name(n))), fr)))

def read_only_root(p: Nat, +t: List<&2, M.Node>, +n: M.Node, +hp: {M.Node.place(n) == M.Place{None{}, True{}} : M.Place}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}) -> {M.read_all(1n+p, M.attach(t, n), [n]) == [n] : List<&2, M.Node>}:
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(n)}, False{}), Nil{}, children_attach_fresh_root(t, n, False{}, hp, fr)) : {List.append(&2, M.Node, M.read_all(p, M.attach(t, n), _), n <> List.append(&2, M.Node, M.read_all(p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(n)}, True{})), M.read_all(p, M.attach(t, n), Nil{}))) == [n] : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(n)}, True{}), Nil{}, children_attach_fresh_root(t, n, True{}, hp, fr)) : {List.append(&2, M.Node, M.read_all(p, M.attach(t, n), Nil{}), n <> List.append(&2, M.Node, M.read_all(p, M.attach(t, n), _), M.read_all(p, M.attach(t, n), Nil{}))) == [n] : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.read_all(p, M.attach(t, n), Nil{}), Nil{}, read_nil(p, M.attach(t, n))) : {List.append(&2, M.Node, _, n <> List.append(&2, M.Node, _, _)) == [n] : List<&2, M.Node>}
  {==}

def fits_only_root(p: Nat, +t: List<&2, M.Node>, +n: M.Node, +hp: {M.Node.place(n) == M.Place{None{}, True{}} : M.Place}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}) -> {M.fits(1n+p, M.attach(t, n), [n]) == True{} : Bool}:
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(n)}, False{}), Nil{}, children_attach_fresh_root(t, n, False{}, hp, fr)) : {Bool.and(M.fits(p, M.attach(t, n), _), Bool.and(M.fits(p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(n)}, True{})), M.fits(p, M.attach(t, n), Nil{}))) == True{} : Bool}
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(n)}, True{}), Nil{}, children_attach_fresh_root(t, n, True{}, hp, fr)) : {Bool.and(M.fits(p, M.attach(t, n), Nil{}), Bool.and(M.fits(p, M.attach(t, n), _), M.fits(p, M.attach(t, n), Nil{}))) == True{} : Bool}
  %Equal.sym(Bool, M.fits(p, M.attach(t, n), Nil{}), True{}, fits_nil(p, M.attach(t, n))) : {Bool.and(_, Bool.and(_, _)) == True{} : Bool}
  {==}

# The reading of the tree with the element attached
# -------------------------------------------------
def order_attach(+t: List<&2, M.Node>, +n: M.Node, +par: M.Name, +right: Bool, +hp: {M.Node.place(n) == M.Place{Some{par}, right} : M.Place}, +e: {M.children(t, Some{par}, right) == Nil{} : List<&2, M.Node>}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +pn: {M.named(t, par) == True{} : Bool}, +fi: {M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})) == True{} : Bool}) -> {M.order(M.attach(t, n)) == splice(M.order(t), par, right, n) : List<&2, M.Node>}:
  %Equal.sym(Nat, List.length(&2, M.Node, M.attach(t, n)), 1n+List.length(&2, M.Node, t), attach_length(t, n)) : {M.read_all(1n+_, M.attach(t, n), M.children(M.attach(t, n), None{}, True{})) == splice(M.order(t), par, right, n) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), None{}, True{}), M.children(t, None{}, True{}), children_attach_other(t, n, None{}, True{}, hangs_root(n, par, right, True{}, hp))) : {M.read_all(1n+(1n+List.length(&2, M.Node, t)), M.attach(t, n), _) == splice(M.order(t), par, right, n) : List<&2, M.Node>}
  read_attach(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}), n, par, right, hp, e, fr, pn, fi)

# Where the anchor puts the element
# ---------------------------------
#
# Either the view is empty and the element is its one root, or the
# anchor names a parent with no child on that side yet — the element the
# insert follows, when it has no right child, or else the landing of the
# descent from its first right child — and the splice at that parent is
# the insertion after the element followed: `place_at`.
def place_at(xs: List<&2, M.Node>, left: Maybe<&2, M.Name>, n: M.Node) -> List<&2, M.Node>:
  match left:
    case None{}:
      n <> xs
    case Some{par}:
      splice(xs, par, True{}, n)

def head_named(+t: List<&2, M.Node>, +q: Maybe<&2, M.Name>, +r: Bool, +c: M.Node, more: List<&2, M.Node>, ecs: {M.children(t, q, r) == c <> more : List<&2, M.Node>}) -> {M.named(M.children(t, q, r), M.Node.name(c)) == True{} : Bool}:
  %Equal.sym(List<&2, M.Node>, M.children(t, q, r), c <> more, ecs) : {M.named(_, M.Node.name(c)) == True{} : Bool}
  or_left(M.Name.eq(M.Node.name(c), M.Node.name(c)), M.named(more, M.Node.name(c)), name_eq_refl(M.Node.name(c)))

def anchor_of_nil(+t: List<&2, M.Node>, +left: Maybe<&2, M.Name>, ecs: {M.children(t, left, True{}) == Nil{} : List<&2, M.Node>}) -> {M.anchor(t, left) == M.Place{left, True{}} : M.Place}:
  %Equal.sym(List<&2, M.Node>, M.children(t, left, True{}), Nil{}, ecs) : {M.anchor.of(t, left, _) == M.Place{left, True{}} : M.Place}
  {==}

def anchor_of_cons(+t: List<&2, M.Node>, +left: Maybe<&2, M.Name>, +c: M.Node, more: List<&2, M.Node>, ecs: {M.children(t, left, True{}) == c <> more : List<&2, M.Node>}) -> {M.anchor(t, left) == M.Place{Some{M.leftmost(List.length(&2, M.Node, t), t, M.Node.name(c))}, False{}} : M.Place}:
  %Equal.sym(List<&2, M.Node>, M.children(t, left, True{}), c <> more, ecs) : {M.anchor.of(t, left, _) == M.Place{Some{M.leftmost(List.length(&2, M.Node, t), t, M.Node.name(c))}, False{}} : M.Place}
  {==}

def order_starts(+t: List<&2, M.Node>, +c: M.Node, +more: List<&2, M.Node>, ecs: {M.children(t, None{}, True{}) == c <> more : List<&2, M.Node>}, +fi: {M.fits(1n+List.length(&2, M.Node, t), t, c <> more) == True{} : Bool}) -> {starts(M.order(t), M.leftmost(List.length(&2, M.Node, t), t, M.Node.name(c))) == True{} : Bool}:
  %leftmost_stable(List.length(&2, M.Node, t), 1n+List.length(&2, M.Node, t), t, M.Node.name(c), lchain_of_fits(List.length(&2, M.Node, t), t, M.children(t, Some{M.Node.name(c)}, False{}), Comp.and_left(M.fits(List.length(&2, M.Node, t), t, M.children(t, Some{M.Node.name(c)}, False{})), Bool.and(M.fits(List.length(&2, M.Node, t), t, M.children(t, Some{M.Node.name(c)}, True{})), M.fits(List.length(&2, M.Node, t), t, more)), fi)), Comp.le_succ(List.length(&2, M.Node, t), List.length(&2, M.Node, t), Comp.le_refl(List.length(&2, M.Node, t)))) : {starts(M.order(t), _) == True{} : Bool}
  %Equal.sym(List<&2, M.Node>, M.children(t, None{}, True{}), c <> more, ecs) : {starts(M.read_all(1n+List.length(&2, M.Node, t), t, _), M.leftmost(1n+List.length(&2, M.Node, t), t, M.Node.name(c))) == True{} : Bool}
  head_read(1n+List.length(&2, M.Node, t), t, c, more, fi)

def anchor_cases.none(-R: Type, +t: List<&2, M.Node>, +n: M.Node, cs: List<&2, M.Node>, +ecs: {M.children(t, None{}, True{}) == cs : List<&2, M.Node>}, +inv: {M.invariant(t) == True{} : Bool}, kroot: {None{} == None{} : Maybe<&2, M.Name>} -> {M.children(t, None{}, True{}) == Nil{} : List<&2, M.Node>} -> {M.anchor(t, None{}) == M.Place{None{}, True{}} : M.Place} -> R, kpar: @par: M.Name -> @right: Bool -> {M.anchor(t, None{}) == M.Place{Some{par}, right} : M.Place} -> {M.children(t, Some{par}, right) == Nil{} : List<&2, M.Node>} -> {M.named(t, par) == True{} : Bool} -> {splice(M.order(t), par, right, n) == place_at(M.order(t), None{}, n) : List<&2, M.Node>} -> R) -> R:
  match cs:
    case Nil{}:
      kroot({==}, ecs, anchor_of_nil(t, None{}, ecs))
    case +c <> +more:
      kpar(M.leftmost(List.length(&2, M.Node, t), t, M.Node.name(c)), False{}, anchor_of_cons(t, None{}, c, more, ecs),
        leftmost_lands(List.length(&2, M.Node, t), t, M.Node.name(c), lchain_of_fits(List.length(&2, M.Node, t), t, M.children(t, Some{M.Node.name(c)}, False{}), Comp.and_left(M.fits(List.length(&2, M.Node, t), t, M.children(t, Some{M.Node.name(c)}, False{})), Bool.and(M.fits(List.length(&2, M.Node, t), t, M.children(t, Some{M.Node.name(c)}, True{})), M.fits(List.length(&2, M.Node, t), t, more)), fits_transport(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}), c <> more, ecs, Comp.and_left(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.order(t)), inv))))),
        leftmost_named(List.length(&2, M.Node, t), t, M.Node.name(c), children_named(t, None{}, True{}, M.Node.name(c), head_named(t, None{}, True{}, c, more, ecs))),
        splice_starts(M.order(t), M.leftmost(List.length(&2, M.Node, t), t, M.Node.name(c)), n, order_starts(t, c, more, ecs, fits_transport(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}), c <> more, ecs, Comp.and_left(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.order(t)), inv))), Comp.and_right(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.order(t)), inv)))

def anchor_cases.some(-R: Type, +t: List<&2, M.Node>, +par: M.Name, +n: M.Node, cs: List<&2, M.Node>, +ecs: {M.children(t, Some{par}, True{}) == cs : List<&2, M.Node>}, +inv: {M.invariant(t) == True{} : Bool}, +lo: {M.named(M.visible(t), par) == True{} : Bool}, kpar: @par2: M.Name -> @right: Bool -> {M.anchor(t, Some{par}) == M.Place{Some{par2}, right} : M.Place} -> {M.children(t, Some{par2}, right) == Nil{} : List<&2, M.Node>} -> {M.named(t, par2) == True{} : Bool} -> {splice(M.order(t), par2, right, n) == place_at(M.order(t), Some{par}, n) : List<&2, M.Node>} -> R) -> R:
  match cs:
    case Nil{}:
      kpar(par, True{}, anchor_of_nil(t, Some{par}, ecs), ecs, order_named(t, par, standing_named(M.order(t), par, lo)), {==})
    case +c <> +more:
      kpar(M.leftmost(List.length(&2, M.Node, t), t, M.Node.name(c)), False{}, anchor_of_cons(t, Some{par}, c, more, ecs),
        leftmost_lands(List.length(&2, M.Node, t), t, M.Node.name(c), lchain_of_fits(List.length(&2, M.Node, t), t, M.children(t, Some{M.Node.name(c)}, False{}), Comp.and_left(M.fits(List.length(&2, M.Node, t), t, M.children(t, Some{M.Node.name(c)}, False{})), Bool.and(M.fits(List.length(&2, M.Node, t), t, M.children(t, Some{M.Node.name(c)}, True{})), M.fits(List.length(&2, M.Node, t), t, more)), fits_transport(1n+List.length(&2, M.Node, t), t, M.children(t, Some{par}, True{}), c <> more, ecs, Comp.and_right(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, Some{par}, False{})), M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, Some{par}, True{})), fits_in(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}), par, Comp.and_left(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.order(t)), inv), standing_named(M.order(t), par, lo))))))),
        leftmost_named(List.length(&2, M.Node, t), t, M.Node.name(c), children_named(t, Some{par}, True{}, M.Node.name(c), head_named(t, Some{par}, True{}, c, more, ecs))),
        splice_swap(M.order(t), par, M.leftmost(List.length(&2, M.Node, t), t, M.Node.name(c)), n, next_is_read(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}), par, c, more, List.length(&2, M.Node, t), Comp.and_left(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.order(t)), inv), ecs, Comp.le_refl(1n+List.length(&2, M.Node, t))), Comp.and_right(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.order(t)), inv), standing_named(M.order(t), par, lo)))

def anchor_cases(-R: Type, +t: List<&2, M.Node>, left: Maybe<&2, M.Name>, +n: M.Node, +inv: {M.invariant(t) == True{} : Bool}, lo: {M.in_view(t, left) == True{} : Bool}, kroot: {left == None{} : Maybe<&2, M.Name>} -> {M.children(t, None{}, True{}) == Nil{} : List<&2, M.Node>} -> {M.anchor(t, left) == M.Place{None{}, True{}} : M.Place} -> R, kpar: @par: M.Name -> @right: Bool -> {M.anchor(t, left) == M.Place{Some{par}, right} : M.Place} -> {M.children(t, Some{par}, right) == Nil{} : List<&2, M.Node>} -> {M.named(t, par) == True{} : Bool} -> {splice(M.order(t), par, right, n) == place_at(M.order(t), left, n) : List<&2, M.Node>} -> R) -> R:
  match left:
    case None{}:
      anchor_cases.none(R, t, n, M.children(t, None{}, True{}), {==}, inv, kroot, kpar)
    case Some{+par}:
      anchor_cases.some(R, t, par, n, M.children(t, Some{par}, True{}), {==}, inv, lo, kpar)

# The invariant is kept
# ---------------------
def invariant_par(+t: List<&2, M.Node>, +n: M.Node, +par: M.Name, +right: Bool, +hp: {M.Node.place(n) == M.Place{Some{par}, right} : M.Place}, +e: {M.children(t, Some{par}, right) == Nil{} : List<&2, M.Node>}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +pn: {M.named(t, par) == True{} : Bool}, +inv: {M.invariant(t) == True{} : Bool}) -> {M.invariant(M.attach(t, n)) == True{} : Bool}:
  %Equal.sym(List<&2, M.Node>, M.order(M.attach(t, n)), splice(M.order(t), par, right, n), order_attach(t, n, par, right, hp, e, fr, pn, Comp.and_left(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.order(t)), inv))) : {Bool.and(M.fits(1n+List.length(&2, M.Node, M.attach(t, n)), M.attach(t, n), M.children(M.attach(t, n), None{}, True{})), M.nodup(_)) == True{} : Bool}
  %Equal.sym(Nat, List.length(&2, M.Node, M.attach(t, n)), 1n+List.length(&2, M.Node, t), attach_length(t, n)) : {Bool.and(M.fits(1n+_, M.attach(t, n), M.children(M.attach(t, n), None{}, True{})), M.nodup(splice(M.order(t), par, right, n))) == True{} : Bool}
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), None{}, True{}), M.children(t, None{}, True{}), children_attach_other(t, n, None{}, True{}, hangs_root(n, par, right, True{}, hp))) : {Bool.and(M.fits(1n+(1n+List.length(&2, M.Node, t)), M.attach(t, n), _), M.nodup(splice(M.order(t), par, right, n))) == True{} : Bool}
  and_intro(M.fits(1n+(1n+List.length(&2, M.Node, t)), M.attach(t, n), M.children(t, None{}, True{})), M.nodup(splice(M.order(t), par, right, n)),
    fits_attach(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}), n, par, right, hp, e, fr, pn, Comp.and_left(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.order(t)), inv)),
    nodup_splice(M.order(t), par, right, n, Comp.and_right(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.order(t)), inv), order_sub(t, M.Node.name(n), not_of_true(M.named(t, M.Node.name(n)), Comp.and_left(Bool.not(M.named(t, M.Node.name(n))), Bool.not(M.hangs_under(t, M.Node.name(n))), fr)))))

def invariant_root(+t: List<&2, M.Node>, +n: M.Node, +hp: {M.Node.place(n) == M.Place{None{}, True{}} : M.Place}, +eR: {M.children(t, None{}, True{}) == Nil{} : List<&2, M.Node>}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}) -> {M.invariant(M.attach(t, n)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, M.Node, M.attach(t, n)), 1n+List.length(&2, M.Node, t), attach_length(t, n)) : {Bool.and(M.fits(1n+_, M.attach(t, n), M.children(M.attach(t, n), None{}, True{})), M.nodup(M.read_all(1n+_, M.attach(t, n), M.children(M.attach(t, n), None{}, True{})))) == True{} : Bool}
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), None{}, True{}), [n], children_attach_here(t, n, None{}, True{}, hangs_root_true(n, hp), eR)) : {Bool.and(M.fits(1n+(1n+List.length(&2, M.Node, t)), M.attach(t, n), _), M.nodup(M.read_all(1n+(1n+List.length(&2, M.Node, t)), M.attach(t, n), _))) == True{} : Bool}
  %Equal.sym(List<&2, M.Node>, M.read_all(1n+(1n+List.length(&2, M.Node, t)), M.attach(t, n), [n]), [n], read_only_root(1n+List.length(&2, M.Node, t), t, n, hp, fr)) : {Bool.and(M.fits(1n+(1n+List.length(&2, M.Node, t)), M.attach(t, n), [n]), M.nodup(_)) == True{} : Bool}
  %Equal.sym(Bool, M.fits(1n+(1n+List.length(&2, M.Node, t)), M.attach(t, n), [n]), True{}, fits_only_root(1n+List.length(&2, M.Node, t), t, n, hp, fr)) : {Bool.and(_, M.nodup([n])) == True{} : Bool}
  {==}

def invariant_attach(+t: List<&2, M.Node>, +n: M.Node, +left: Maybe<&2, M.Name>, +inv: {M.invariant(t) == True{} : Bool}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +hp: {M.Node.place(n) == M.anchor(t, left) : M.Place}, lo: {M.in_view(t, left) == True{} : Bool}) -> {M.invariant(M.attach(t, n)) == True{} : Bool}:
  anchor_cases({M.invariant(M.attach(t, n)) == True{} : Bool}, t, left, n, inv, lo,
    eN => eR => eA => invariant_root(t, n, Equal.trans(M.Place, M.Node.place(n), M.anchor(t, left), M.Place{None{}, True{}}, hp, eA), eR, fr),
    par => right => eA => e => pn => eq => invariant_par(t, n, par, right, Equal.trans(M.Place, M.Node.place(n), M.anchor(t, left), M.Place{Some{par}, right}, hp, eA), e, fr, pn, inv))

# The theorem
# -----------
def standing_place_at(+t: List<&2, M.Node>, left: Maybe<&2, M.Name>, +n: M.Node, +nd: {M.nodup(M.order(t)) == True{} : Bool}, lo: {M.in_view(t, left) == True{} : Bool}, +hs: {M.Node.standing(n) == True{} : Bool}) -> {M.standing(place_at(M.order(t), left, n)) == place_at(M.standing(M.order(t)), left, n) : List<&2, M.Node>}:
  match left:
    case None{}:
      standing_cons(n, M.order(t), hs)
    case Some{par}:
      standing_splice(M.order(t), par, n, nd, lo, hs)

def insert_root(+t: List<&2, M.Node>, +n: M.Node, +left: Maybe<&2, M.Name>, eN: {left == None{} : Maybe<&2, M.Name>}, +hp: {M.Node.place(n) == M.Place{None{}, True{}} : M.Place}, +eR: {M.children(t, None{}, True{}) == Nil{} : List<&2, M.Node>}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, hs: {M.Node.standing(n) == True{} : Bool}) -> {M.visible(M.attach(t, n)) == place_at(M.visible(t), left, n) : List<&2, M.Node>}:
  %Equal.sym(Maybe<&2, M.Name>, left, None{}, eN) : {M.visible(M.attach(t, n)) == place_at(M.visible(t), _, n) : List<&2, M.Node>}
  %Equal.sym(Nat, List.length(&2, M.Node, M.attach(t, n)), 1n+List.length(&2, M.Node, t), attach_length(t, n)) : {M.standing(M.read_all(1n+_, M.attach(t, n), M.children(M.attach(t, n), None{}, True{}))) == n <> M.visible(t) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), None{}, True{}), [n], children_attach_here(t, n, None{}, True{}, hangs_root_true(n, hp), eR)) : {M.standing(M.read_all(1n+(1n+List.length(&2, M.Node, t)), M.attach(t, n), _)) == n <> M.visible(t) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.read_all(1n+(1n+List.length(&2, M.Node, t)), M.attach(t, n), [n]), [n], read_only_root(1n+List.length(&2, M.Node, t), t, n, hp, fr)) : {M.standing(_) == n <> M.visible(t) : List<&2, M.Node>}
  %Equal.sym(Bool, M.Node.standing(n), True{}, hs) : {List.filter.put(M.Node, n, Nil{}, _) == n <> M.visible(t) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.children(t, None{}, True{}), Nil{}, eR) : {[n] == n <> M.standing(M.read_all(1n+List.length(&2, M.Node, t), t, _)) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.read_all(1n+List.length(&2, M.Node, t), t, Nil{}), Nil{}, read_nil(1n+List.length(&2, M.Node, t), t)) : {[n] == n <> M.standing(_) : List<&2, M.Node>}
  {==}

def insert_par(+t: List<&2, M.Node>, +n: M.Node, +left: Maybe<&2, M.Name>, +par: M.Name, +right: Bool, +hp: {M.Node.place(n) == M.Place{Some{par}, right} : M.Place}, +e: {M.children(t, Some{par}, right) == Nil{} : List<&2, M.Node>}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +pn: {M.named(t, par) == True{} : Bool}, +inv: {M.invariant(t) == True{} : Bool}, +hs: {M.Node.standing(n) == True{} : Bool}, lo: {M.in_view(t, left) == True{} : Bool}, eq: {splice(M.order(t), par, right, n) == place_at(M.order(t), left, n) : List<&2, M.Node>}) -> {M.visible(M.attach(t, n)) == place_at(M.visible(t), left, n) : List<&2, M.Node>}:
  %Equal.sym(List<&2, M.Node>, M.order(M.attach(t, n)), splice(M.order(t), par, right, n), order_attach(t, n, par, right, hp, e, fr, pn, Comp.and_left(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.order(t)), inv))) : {M.standing(_) == place_at(M.visible(t), left, n) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, splice(M.order(t), par, right, n), place_at(M.order(t), left, n), eq) : {M.standing(_) == place_at(M.visible(t), left, n) : List<&2, M.Node>}
  standing_place_at(t, left, n, Comp.and_right(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.order(t)), inv), lo, hs)

def insert_core(+t: List<&2, M.Node>, +n: M.Node, +left: Maybe<&2, M.Name>, +inv: {M.invariant(t) == True{} : Bool}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +hp: {M.Node.place(n) == M.anchor(t, left) : M.Place}, +hs: {M.Node.standing(n) == True{} : Bool}, +lo: {M.in_view(t, left) == True{} : Bool}) -> {M.visible(M.attach(t, n)) == place_at(M.visible(t), left, n) : List<&2, M.Node>}:
  anchor_cases({M.visible(M.attach(t, n)) == place_at(M.visible(t), left, n) : List<&2, M.Node>}, t, left, n, inv, lo,
    eN => eR => eA => insert_root(t, n, left, eN, Equal.trans(M.Place, M.Node.place(n), M.anchor(t, left), M.Place{None{}, True{}}, hp, eA), eR, fr, hs),
    par => right => eA => e => pn => eq => insert_par(t, n, left, par, right, Equal.trans(M.Place, M.Node.place(n), M.anchor(t, left), M.Place{Some{par}, right}, hp, eA), e, fr, pn, inv, hs, lo, eq))

# `left_of` at a position: none at zero, the element before it otherwise.
def mdisc(m: Maybe<&2, Maybe<&2, M.Name>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some_left(-x: Maybe<&2, M.Name>, e: {None{} == Some{x} : Maybe<&2, Maybe<&2, M.Name>>}) -> Empty:
  %e : {mdisc(_) : Type}
  Unit{}

def unwrap_left(m: Maybe<&2, Maybe<&2, M.Name>>) -> Maybe<&2, M.Name>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      x

def some_left(-a: Maybe<&2, M.Name>, -b: Maybe<&2, M.Name>, e: {Some{a} == Some{b} : Maybe<&2, Maybe<&2, M.Name>>}) -> {a == b : Maybe<&2, M.Name>}:
  Equal.cong(Maybe<&2, Maybe<&2, M.Name>>, Maybe<&2, M.Name>, unwrap_left, Some{a}, Some{b}, e)

def insert_at.some(+t: List<&2, M.Node>, +p: Nat, +nm: M.Name, +it: Ops.Item, +left: Maybe<&2, M.Name>, m: Maybe<&2, M.Node>, +em: {List.get(&2, M.Node, M.visible(t), p) == m : Maybe<&2, M.Node>}, +inv: {M.invariant(t) == True{} : Bool}, +fr: {M.fresh(t, nm) == True{} : Bool}, lo: {Maybe.map(&2, M.Node, Maybe<&2, M.Name>, x => Some{M.Node.name(x)}, m) == Some{left} : Maybe<&2, Maybe<&2, M.Name>>}) -> {M.visible(M.attach(t, M.Node{nm, it, M.anchor(t, left), Nil{}})) == List.append(&2, M.Node, List.take(&2, M.Node, M.visible(t), 1n+p), M.Node{nm, it, M.anchor(t, left), Nil{}} <> List.drop(&2, M.Node, M.visible(t), 1n+p)) : List<&2, M.Node>}:
  match m:
    case None{}:
      Empty.absurd({M.visible(M.attach(t, M.Node{nm, it, M.anchor(t, left), Nil{}})) == List.append(&2, M.Node, List.take(&2, M.Node, M.visible(t), 1n+p), M.Node{nm, it, M.anchor(t, left), Nil{}} <> List.drop(&2, M.Node, M.visible(t), 1n+p)) : List<&2, M.Node>}, none_some_left(left, lo))
    case Some{+x}:
      %some_left(Some{M.Node.name(x)}, left, lo) : {M.visible(M.attach(t, M.Node{nm, it, M.anchor(t, _), Nil{}})) == List.append(&2, M.Node, List.take(&2, M.Node, M.visible(t), 1n+p), M.Node{nm, it, M.anchor(t, _), Nil{}} <> List.drop(&2, M.Node, M.visible(t), 1n+p)) : List<&2, M.Node>}
      Equal.trans(List<&2, M.Node>, M.visible(M.attach(t, M.Node{nm, it, M.anchor(t, Some{M.Node.name(x)}), Nil{}})), splice(M.visible(t), M.Node.name(x), True{}, M.Node{nm, it, M.anchor(t, Some{M.Node.name(x)}), Nil{}}), List.append(&2, M.Node, List.take(&2, M.Node, M.visible(t), 1n+p), M.Node{nm, it, M.anchor(t, Some{M.Node.name(x)}), Nil{}} <> List.drop(&2, M.Node, M.visible(t), 1n+p)),
        insert_core(t, M.Node{nm, it, M.anchor(t, Some{M.Node.name(x)}), Nil{}}, Some{M.Node.name(x)}, inv, fr, {==}, {==}, get_named(M.visible(t), p, x, em)),
        splice_get(M.visible(t), p, x, M.Node{nm, it, M.anchor(t, Some{M.Node.name(x)}), Nil{}}, em, nodup_standing(M.order(t), Comp.and_right(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.order(t)), inv))))

def insert_at(+t: List<&2, M.Node>, at: Nat, +nm: M.Name, +it: Ops.Item, +left: Maybe<&2, M.Name>, +inv: {M.invariant(t) == True{} : Bool}, +fr: {M.fresh(t, nm) == True{} : Bool}, lo: {M.left_of(M.visible(t), at) == Some{left} : Maybe<&2, Maybe<&2, M.Name>>}) -> {M.visible(M.attach(t, M.Node{nm, it, M.anchor(t, left), Nil{}})) == List.append(&2, M.Node, List.take(&2, M.Node, M.visible(t), at), M.Node{nm, it, M.anchor(t, left), Nil{}} <> List.drop(&2, M.Node, M.visible(t), at)) : List<&2, M.Node>}:
  match at:
    case 0n:
      %some_left(None{}, left, lo) : {M.visible(M.attach(t, M.Node{nm, it, M.anchor(t, _), Nil{}})) == List.append(&2, M.Node, List.take(&2, M.Node, M.visible(t), 0n), M.Node{nm, it, M.anchor(t, _), Nil{}} <> List.drop(&2, M.Node, M.visible(t), 0n)) : List<&2, M.Node>}
      %Equal.sym(List<&2, M.Node>, List.take(&2, M.Node, M.visible(t), 0n), Nil{}, take_zero(M.visible(t))) : {M.visible(M.attach(t, M.Node{nm, it, M.anchor(t, None{}), Nil{}})) == List.append(&2, M.Node, _, M.Node{nm, it, M.anchor(t, None{}), Nil{}} <> List.drop(&2, M.Node, M.visible(t), 0n)) : List<&2, M.Node>}
      %Equal.sym(List<&2, M.Node>, List.drop(&2, M.Node, M.visible(t), 0n), M.visible(t), drop_zero(M.visible(t))) : {M.visible(M.attach(t, M.Node{nm, it, M.anchor(t, None{}), Nil{}})) == M.Node{nm, it, M.anchor(t, None{}), Nil{}} <> _ : List<&2, M.Node>}
      insert_core(t, M.Node{nm, it, M.anchor(t, None{}), Nil{}}, None{}, inv, fr, {==}, {==}, {==})
    case 1n++p:
      insert_at.some(t, p, nm, it, left, List.get(&2, M.Node, M.visible(t), p), {==}, inv, fr, lo)

# A mark keeps the invariant
# --------------------------
#
# A mark changes no name and no place, so the reading is the reading
# with each element marked, and the fuel and the names are as they were.
def hangs_mark(x: M.Node, +tg: M.Name, +by: Nat, +q: Maybe<&2, M.Name>, +r: Bool) -> {M.Node.hangs(x, q, r) == M.Node.hangs(M.Node.mark(x, tg, by), q, r) : Bool}:
  match x:
    case M.Node{nm, it, M.Place{pl, rr}, d}:
      {==}

def mark_filter(+x: M.Node, +xs: List<&2, M.Node>, +tg: M.Name, +by: Nat, b: Bool) -> {M.mark(List.filter.put(M.Node, x, xs, b), tg, by) == List.filter.put(M.Node, M.Node.mark(x, tg, by), M.mark(xs, tg, by), b) : List<&2, M.Node>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def children_mark(t: List<&2, M.Node>, +tg: M.Name, +by: Nat, +q: Maybe<&2, M.Name>, +r: Bool) -> {M.mark(M.children(t, q, r), tg, by) == M.children(M.mark(t, tg, by), q, r) : List<&2, M.Node>}:
  match t:
    case Nil{}:
      {==}
    case +x <> +xs:
      %hangs_mark(x, tg, by, q, r) : {M.mark(List.filter.put(M.Node, x, M.children(xs, q, r), M.Node.hangs(x, q, r)), tg, by) == List.filter.put(M.Node, M.Node.mark(x, tg, by), M.children(M.mark(xs, tg, by), q, r), _) : List<&2, M.Node>}
      %children_mark(xs, tg, by, q, r) : {M.mark(List.filter.put(M.Node, x, M.children(xs, q, r), M.Node.hangs(x, q, r)), tg, by) == List.filter.put(M.Node, M.Node.mark(x, tg, by), _, M.Node.hangs(x, q, r)) : List<&2, M.Node>}
      mark_filter(x, M.children(xs, q, r), tg, by, M.Node.hangs(x, q, r))

def mark_append(xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +tg: M.Name, +by: Nat) -> {List.append(&2, M.Node, M.mark(xs, tg, by), M.mark(ys, tg, by)) == M.mark(List.append(&2, M.Node, xs, ys), tg, by) : List<&2, M.Node>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      cons_cong(M.Node.mark(x, tg, by), List.append(&2, M.Node, M.mark(rest, tg, by), M.mark(ys, tg, by)), M.mark(List.append(&2, M.Node, rest, ys), tg, by), mark_append(rest, ys, tg, by))

def read_mark(fuel: Nat, +t: List<&2, M.Node>, siblings: List<&2, M.Node>, +tg: M.Name, +by: Nat) -> {M.mark(M.read_all(fuel, t, siblings), tg, by) == M.read_all(fuel, M.mark(t, tg, by), M.mark(siblings, tg, by)) : List<&2, M.Node>}:
  match fuel:
    case 0n:
      {==}
    case 1n++p:
      match siblings:
        case Nil{}:
          {==}
        case +s <> +rest:
          %Equal.sym(M.Name, M.Node.name(M.Node.mark(s, tg, by)), M.Node.name(s), ML.mark_name(s, tg, by)) : {M.mark(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), tg, by) == List.append(&2, M.Node, M.read_all(p, M.mark(t, tg, by), M.children(M.mark(t, tg, by), Some{_}, False{})), M.Node.mark(s, tg, by) <> List.append(&2, M.Node, M.read_all(p, M.mark(t, tg, by), M.children(M.mark(t, tg, by), Some{_}, True{})), M.read_all(p, M.mark(t, tg, by), M.mark(rest, tg, by)))) : List<&2, M.Node>}
          %children_mark(t, tg, by, Some{M.Node.name(s)}, False{}) : {M.mark(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), tg, by) == List.append(&2, M.Node, M.read_all(p, M.mark(t, tg, by), _), M.Node.mark(s, tg, by) <> List.append(&2, M.Node, M.read_all(p, M.mark(t, tg, by), M.children(M.mark(t, tg, by), Some{M.Node.name(s)}, True{})), M.read_all(p, M.mark(t, tg, by), M.mark(rest, tg, by)))) : List<&2, M.Node>}
          %children_mark(t, tg, by, Some{M.Node.name(s)}, True{}) : {M.mark(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), tg, by) == List.append(&2, M.Node, M.read_all(p, M.mark(t, tg, by), M.mark(M.children(t, Some{M.Node.name(s)}, False{}), tg, by)), M.Node.mark(s, tg, by) <> List.append(&2, M.Node, M.read_all(p, M.mark(t, tg, by), _), M.read_all(p, M.mark(t, tg, by), M.mark(rest, tg, by)))) : List<&2, M.Node>}
          %read_mark(p, t, M.children(t, Some{M.Node.name(s)}, False{}), tg, by) : {M.mark(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), tg, by) == List.append(&2, M.Node, _, M.Node.mark(s, tg, by) <> List.append(&2, M.Node, M.read_all(p, M.mark(t, tg, by), M.mark(M.children(t, Some{M.Node.name(s)}, True{}), tg, by)), M.read_all(p, M.mark(t, tg, by), M.mark(rest, tg, by)))) : List<&2, M.Node>}
          %read_mark(p, t, M.children(t, Some{M.Node.name(s)}, True{}), tg, by) : {M.mark(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), tg, by) == List.append(&2, M.Node, M.mark(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), tg, by), M.Node.mark(s, tg, by) <> List.append(&2, M.Node, _, M.read_all(p, M.mark(t, tg, by), M.mark(rest, tg, by)))) : List<&2, M.Node>}
          %read_mark(p, t, rest, tg, by) : {M.mark(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), tg, by) == List.append(&2, M.Node, M.mark(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), tg, by), M.Node.mark(s, tg, by) <> List.append(&2, M.Node, M.mark(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), tg, by), _)) : List<&2, M.Node>}
          %mark_append(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), tg, by) : {_ == List.append(&2, M.Node, M.mark(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), tg, by), M.Node.mark(s, tg, by) <> List.append(&2, M.Node, M.mark(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), tg, by), M.mark(M.read_all(p, t, rest), tg, by))) : List<&2, M.Node>}
          %mark_append(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), tg, by) : {List.append(&2, M.Node, M.mark(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), tg, by), M.Node.mark(s, tg, by) <> _) == List.append(&2, M.Node, M.mark(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), tg, by), M.Node.mark(s, tg, by) <> List.append(&2, M.Node, M.mark(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), tg, by), M.mark(M.read_all(p, t, rest), tg, by))) : List<&2, M.Node>}
          {==}

def named_mark(xs: List<&2, M.Node>, +tg: M.Name, +by: Nat, +nm: M.Name) -> {M.named(xs, nm) == M.named(M.mark(xs, tg, by), nm) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(M.Name, M.Node.name(M.Node.mark(x, tg, by)), M.Node.name(x), ML.mark_name(x, tg, by)) : {Bool.or(M.Name.eq(M.Node.name(x), nm), M.named(rest, nm)) == Bool.or(M.Name.eq(_, nm), M.named(M.mark(rest, tg, by), nm)) : Bool}
      %named_mark(rest, tg, by, nm) : {Bool.or(M.Name.eq(M.Node.name(x), nm), M.named(rest, nm)) == Bool.or(M.Name.eq(M.Node.name(x), nm), _) : Bool}
      {==}

def nodup_mark(xs: List<&2, M.Node>, +tg: M.Name, +by: Nat) -> {M.nodup(xs) == M.nodup(M.mark(xs, tg, by)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(M.Name, M.Node.name(M.Node.mark(x, tg, by)), M.Node.name(x), ML.mark_name(x, tg, by)) : {Bool.and(Bool.not(M.named(rest, M.Node.name(x))), M.nodup(rest)) == Bool.and(Bool.not(M.named(M.mark(rest, tg, by), _)), M.nodup(M.mark(rest, tg, by))) : Bool}
      %named_mark(rest, tg, by, M.Node.name(x)) : {Bool.and(Bool.not(M.named(rest, M.Node.name(x))), M.nodup(rest)) == Bool.and(Bool.not(_), M.nodup(M.mark(rest, tg, by))) : Bool}
      %nodup_mark(rest, tg, by) : {Bool.and(Bool.not(M.named(rest, M.Node.name(x))), M.nodup(rest)) == Bool.and(Bool.not(M.named(rest, M.Node.name(x))), _) : Bool}
      {==}

def is_nil_mark(xs: List<&2, M.Node>, tg: M.Name, by: Nat) -> {M.is_nil(xs) == M.is_nil(M.mark(xs, tg, by)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      {==}

def fits_mark(fuel: Nat, +t: List<&2, M.Node>, siblings: List<&2, M.Node>, +tg: M.Name, +by: Nat) -> {M.fits(fuel, t, siblings) == M.fits(fuel, M.mark(t, tg, by), M.mark(siblings, tg, by)) : Bool}:
  match fuel:
    case 0n:
      is_nil_mark(siblings, tg, by)
    case 1n++p:
      match siblings:
        case Nil{}:
          {==}
        case +s <> +rest:
          %Equal.sym(M.Name, M.Node.name(M.Node.mark(s, tg, by)), M.Node.name(s), ML.mark_name(s, tg, by)) : {Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest))) == Bool.and(M.fits(p, M.mark(t, tg, by), M.children(M.mark(t, tg, by), Some{_}, False{})), Bool.and(M.fits(p, M.mark(t, tg, by), M.children(M.mark(t, tg, by), Some{_}, True{})), M.fits(p, M.mark(t, tg, by), M.mark(rest, tg, by)))) : Bool}
          %children_mark(t, tg, by, Some{M.Node.name(s)}, False{}) : {Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest))) == Bool.and(M.fits(p, M.mark(t, tg, by), _), Bool.and(M.fits(p, M.mark(t, tg, by), M.children(M.mark(t, tg, by), Some{M.Node.name(s)}, True{})), M.fits(p, M.mark(t, tg, by), M.mark(rest, tg, by)))) : Bool}
          %children_mark(t, tg, by, Some{M.Node.name(s)}, True{}) : {Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest))) == Bool.and(M.fits(p, M.mark(t, tg, by), M.mark(M.children(t, Some{M.Node.name(s)}, False{}), tg, by)), Bool.and(M.fits(p, M.mark(t, tg, by), _), M.fits(p, M.mark(t, tg, by), M.mark(rest, tg, by)))) : Bool}
          %fits_mark(p, t, M.children(t, Some{M.Node.name(s)}, False{}), tg, by) : {Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest))) == Bool.and(_, Bool.and(M.fits(p, M.mark(t, tg, by), M.mark(M.children(t, Some{M.Node.name(s)}, True{}), tg, by)), M.fits(p, M.mark(t, tg, by), M.mark(rest, tg, by)))) : Bool}
          %fits_mark(p, t, M.children(t, Some{M.Node.name(s)}, True{}), tg, by) : {Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest))) == Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(_, M.fits(p, M.mark(t, tg, by), M.mark(rest, tg, by)))) : Bool}
          %fits_mark(p, t, rest, tg, by) : {Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest))) == Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), _)) : Bool}
          {==}

def length_mark(t: List<&2, M.Node>, +tg: M.Name, +by: Nat) -> {List.length(&2, M.Node, t) == List.length(&2, M.Node, M.mark(t, tg, by)) : Nat}:
  match t:
    case Nil{}:
      {==}
    case x <> +rest:
      %length_mark(rest, tg, by) : {1n+List.length(&2, M.Node, rest) == 1n+_ : Nat}
      {==}

def invariant_mark(+t: List<&2, M.Node>, +tg: M.Name, +by: Nat, inv: {M.invariant(t) == True{} : Bool}) -> {M.invariant(M.mark(t, tg, by)) == True{} : Bool}:
  %length_mark(t, tg, by) : {Bool.and(M.fits(1n+_, M.mark(t, tg, by), M.children(M.mark(t, tg, by), None{}, True{})), M.nodup(M.read_all(1n+_, M.mark(t, tg, by), M.children(M.mark(t, tg, by), None{}, True{})))) == True{} : Bool}
  %children_mark(t, tg, by, None{}, True{}) : {Bool.and(M.fits(1n+List.length(&2, M.Node, t), M.mark(t, tg, by), _), M.nodup(M.read_all(1n+List.length(&2, M.Node, t), M.mark(t, tg, by), _))) == True{} : Bool}
  %fits_mark(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}), tg, by) : {Bool.and(_, M.nodup(M.read_all(1n+List.length(&2, M.Node, t), M.mark(t, tg, by), M.mark(M.children(t, None{}, True{}), tg, by)))) == True{} : Bool}
  %read_mark(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}), tg, by) : {Bool.and(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(_)) == True{} : Bool}
  %nodup_mark(M.read_all(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), tg, by) : {Bool.and(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), _) == True{} : Bool}
  inv

def invariant_nil() -> {M.invariant(Nil{}) == True{} : Bool}:
  {==}

def main() -> Unit:
  Unit{}
