# On one line of history the merge walk is plain replay. Each event of a
# chain has seen every event before it, so its view is the whole tree, and
# its run is a cursor walk over that view: a delete marks the elements it
# quotes, and an insert's elements land, by `AL.insert_at`, right after the
# element its gap follows — which, with the parser's ordering, is where the
# cursor put everything written before it. The file the event leaves is its
# view with the marked elements left out, and that is `Cursor.walk`'s
# result, which `Ops.apply` is proven to compute.
import Base
import ./ops.bend as Ops
import ./merge.bend as M
import ./replay_spec.bend as Spec
import ./cursor_spec.bend as Cursor
import ./composition_lemmas.bend as Comp
import ./position_lemmas.bend as Pos
import ./replay_lemmas.bend as L
import ./merge_lemmas.bend as ML
import ./anchor_lemmas.bend as AL
import ./text.bend as T
import ./string_lemmas.bend as S
import ./diff_lemmas.bend as Diff
import ./semantic_replay.bend as Block
import ./parser_lemmas.bend as PL

# Bools
# -----

def or_and_mono(b1: Bool, b2: Bool, -b3: Bool, -b4: Bool, +h: {Bool.or(b1, Bool.and(b2, b3)) == True{} : Bool}, f: {b3 == True{} : Bool} -> {b4 == True{} : Bool}) -> {Bool.or(b1, Bool.and(b2, b4)) == True{} : Bool}:
  match b1:
    case True{}:
      {==}
    case False{}:
      match b2:
        case True{}:
          f(h)
        case False{}:
          Empty.absurd({False{} == True{} : Bool}, Comp.false_true(h))

def or_and_to(b1: Bool, b2: Bool, -b3: Bool, -c: Bool, +h: {Bool.or(b1, Bool.and(b2, b3)) == True{} : Bool}, f1: {b1 == True{} : Bool} -> {c == True{} : Bool}, f2: {b2 == True{} : Bool} -> {b3 == True{} : Bool} -> {c == True{} : Bool}) -> {c == True{} : Bool}:
  match b1:
    case True{}:
      f1({==})
    case False{}:
      match b2:
        case True{}:
          f2({==}, h)
        case False{}:
          Empty.absurd({c == True{} : Bool}, Comp.false_true(h))

# Bounds on names
# ---------------
#
# While event `k` runs, every name in its view was written by an event it
# had seen (`W`) other than `k`, or by `k` itself before its `m`th
# element; so the names it mints are fresh. Removals are by `k` or by an
# event of `W`. Between events, `inw` says every name, parent and removal
# is by an event of `W`.
def before(nm: M.Name, +W: List<&2, Nat>, +k: Nat, +m: Nat) -> Bool:
  match nm:
    case M.Name{+a, o}:
      Bool.or(Bool.and(Bool.not(Nat.is_eq(a, k)), M.has(W, a)), Bool.and(Nat.is_eq(a, k), Nat.is_lt(o, m)))

def before.m(p: Maybe<&2, M.Name>, +W: List<&2, Nat>, +k: Nat, +m: Nat) -> Bool:
  match p:
    case None{}:
      True{}
    case Some{x}:
      before(x, W, k, m)

def all_has(d: List<&2, Nat>, +W: List<&2, Nat>) -> Bool:
  match d:
    case Nil{}:
      True{}
    case y <> ys:
      Bool.and(M.has(W, y), all_has(ys, W))

def good(n: M.Node, +W: List<&2, Nat>, +k: Nat, +m: Nat) -> Bool:
  match n:
    case M.Node{nm, it, M.Place{p, r}, d}:
      Bool.and(before(nm, W, k, m), Bool.and(before.m(p, W, k, m), all_has(d, k <> W)))

def goods(t: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +m: Nat) -> Bool:
  match t:
    case Nil{}:
      True{}
    case x <> xs:
      Bool.and(good(x, W, k, m), goods(xs, W, k, m))

def name_ne_before.b(+a: Nat, +o: Nat, +W: List<&2, Nat>, +k: Nat, +m: Nat, b: Bool, eb: {Nat.is_eq(a, k) == b : Bool}, h: {Bool.or(Bool.and(Bool.not(b), M.has(W, a)), Bool.and(b, Nat.is_lt(o, m))) == True{} : Bool}) -> {M.Name.eq(M.Name{a, o}, M.Name{k, m}) == False{} : Bool}:
  match b:
    case False{}:
      ML.name_ne(a, o, k, m, eb)
    case True{}:
      %Equal.sym(Nat, a, k, ML.nat_eq(a, k, eb)) : {M.Name.eq(M.Name{_, o}, M.Name{k, m}) == False{} : Bool}
      %Equal.sym(Cmp, Nat.cmp(k, k), EQ{}, AL.cmp_refl(k)) : {Cmp.is_eq(M.Name.cmp.of(_, o, m)) == False{} : Bool}
      %Equal.sym(Cmp, Nat.cmp(o, m), LT{}, ML.cmp_of_is_lt(Nat.cmp(o, m), h)) : {Cmp.is_eq(_) == False{} : Bool}
      {==}

# A name before `(k, m)` is not the name `k` mints `m`th.
def name_ne_before(nm: M.Name, +W: List<&2, Nat>, +k: Nat, +m: Nat, +h: {before(nm, W, k, m) == True{} : Bool}) -> {M.Name.eq(nm, M.Name{k, m}) == False{} : Bool}:
  match nm:
    case M.Name{+a, +o}:
      name_ne_before.b(a, o, W, k, m, Nat.is_eq(a, k), {==}, h)

def under_ne(p: Maybe<&2, M.Name>, +W: List<&2, Nat>, +k: Nat, +m: Nat, +h: {before.m(p, W, k, m) == True{} : Bool}) -> {M.Name.same(p, Some{M.Name{k, m}}) == False{} : Bool}:
  match p:
    case None{}:
      {==}
    case Some{x}:
      name_ne_before(x, W, k, m, h)

def not_named(t: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +m: Nat, +h: {goods(t, W, k, m) == True{} : Bool}) -> {M.named(t, M.Name{k, m}) == False{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case M.Node{+nm, +it, M.Place{+p, +r}, +d} <> +xs:
      AL.or_false(M.Name.eq(nm, M.Name{k, m}), M.named(xs, M.Name{k, m}),
        name_ne_before(nm, W, k, m, Comp.and_left(before(nm, W, k, m), Bool.and(before.m(p, W, k, m), all_has(d, k <> W)), Comp.and_left(good(M.Node{nm, it, M.Place{p, r}, d}, W, k, m), goods(xs, W, k, m), h))),
        not_named(xs, W, k, m, Comp.and_right(good(M.Node{nm, it, M.Place{p, r}, d}, W, k, m), goods(xs, W, k, m), h)))

def not_hangs(t: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +m: Nat, +h: {goods(t, W, k, m) == True{} : Bool}) -> {M.hangs_under(t, M.Name{k, m}) == False{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case M.Node{+nm, +it, M.Place{+p, +r}, +d} <> +xs:
      AL.or_false(M.Name.same(p, Some{M.Name{k, m}}), M.hangs_under(xs, M.Name{k, m}),
        under_ne(p, W, k, m, Comp.and_left(before.m(p, W, k, m), all_has(d, k <> W), Comp.and_right(before(nm, W, k, m), Bool.and(before.m(p, W, k, m), all_has(d, k <> W)), Comp.and_left(good(M.Node{nm, it, M.Place{p, r}, d}, W, k, m), goods(xs, W, k, m), h)))),
        not_hangs(xs, W, k, m, Comp.and_right(good(M.Node{nm, it, M.Place{p, r}, d}, W, k, m), goods(xs, W, k, m), h)))

# What `k` mints `m`th is fresh in a view bounded by `(k, m)`.
def fresh_of(+t: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +m: Nat, +h: {goods(t, W, k, m) == True{} : Bool}) -> {M.fresh(t, M.Name{k, m}) == True{} : Bool}:
  AL.and_intro(Bool.not(M.named(t, M.Name{k, m})), Bool.not(M.hangs_under(t, M.Name{k, m})),
    AL.not_true(M.named(t, M.Name{k, m}), not_named(t, W, k, m, h)),
    AL.not_true(M.hangs_under(t, M.Name{k, m}), not_hangs(t, W, k, m, h)))

# A name the view holds is bounded as the view is.
def named_before(t: List<&2, M.Node>, +nm: M.Name, +W: List<&2, Nat>, +k: Nat, +m: Nat, +h: {goods(t, W, k, m) == True{} : Bool}, hn: {M.named(t, nm) == True{} : Bool}) -> {before(nm, W, k, m) == True{} : Bool}:
  match t:
    case Nil{}:
      Empty.absurd({before(nm, W, k, m) == True{} : Bool}, Comp.false_true(hn))
    case M.Node{+x, +it, M.Place{+p, +r}, +d} <> +xs:
      AL.or_cases({before(nm, W, k, m) == True{} : Bool}, M.Name.eq(x, nm), M.named(xs, nm), hn,
        ea => (%AL.name_eq_equal(x, nm, ea) : {before(_, W, k, m) == True{} : Bool}
          Comp.and_left(before(x, W, k, m), Bool.and(before.m(p, W, k, m), all_has(d, k <> W)), Comp.and_left(good(M.Node{x, it, M.Place{p, r}, d}, W, k, m), goods(xs, W, k, m), h))),
        eb => named_before(xs, nm, W, k, m, Comp.and_right(good(M.Node{x, it, M.Place{p, r}, d}, W, k, m), goods(xs, W, k, m), h), eb))

# The bounds are kept
# -------------------

def before_mono(nm: M.Name, +W: List<&2, Nat>, +k: Nat, +m: Nat, +h: {before(nm, W, k, m) == True{} : Bool}) -> {before(nm, W, k, 1n+m) == True{} : Bool}:
  match nm:
    case M.Name{+a, +o}:
      or_and_mono(Bool.and(Bool.not(Nat.is_eq(a, k)), M.has(W, a)), Nat.is_eq(a, k), Nat.is_lt(o, m), Nat.is_lt(o, 1n+m), h, e => Comp.lt_succ(o, m, e))

def before.m_mono(p: Maybe<&2, M.Name>, +W: List<&2, Nat>, +k: Nat, +m: Nat, +h: {before.m(p, W, k, m) == True{} : Bool}) -> {before.m(p, W, k, 1n+m) == True{} : Bool}:
  match p:
    case None{}:
      {==}
    case Some{x}:
      before_mono(x, W, k, m, h)

def good_mono(n: M.Node, +W: List<&2, Nat>, +k: Nat, +m: Nat, +h: {good(n, W, k, m) == True{} : Bool}) -> {good(n, W, k, 1n+m) == True{} : Bool}:
  match n:
    case M.Node{+nm, +it, M.Place{+p, +r}, +d}:
      AL.and_intro(before(nm, W, k, 1n+m), Bool.and(before.m(p, W, k, 1n+m), all_has(d, k <> W)),
        before_mono(nm, W, k, m, Comp.and_left(before(nm, W, k, m), Bool.and(before.m(p, W, k, m), all_has(d, k <> W)), h)),
        AL.and_intro(before.m(p, W, k, 1n+m), all_has(d, k <> W),
          before.m_mono(p, W, k, m, Comp.and_left(before.m(p, W, k, m), all_has(d, k <> W), Comp.and_right(before(nm, W, k, m), Bool.and(before.m(p, W, k, m), all_has(d, k <> W)), h))),
          Comp.and_right(before.m(p, W, k, m), all_has(d, k <> W), Comp.and_right(before(nm, W, k, m), Bool.and(before.m(p, W, k, m), all_has(d, k <> W)), h))))

def goods_mono(t: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +m: Nat, +h: {goods(t, W, k, m) == True{} : Bool}) -> {goods(t, W, k, 1n+m) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +x <> +xs:
      AL.and_intro(good(x, W, k, 1n+m), goods(xs, W, k, 1n+m),
        good_mono(x, W, k, m, Comp.and_left(good(x, W, k, m), goods(xs, W, k, m), h)),
        goods_mono(xs, W, k, m, Comp.and_right(good(x, W, k, m), goods(xs, W, k, m), h)))

# Everything an event has seen, and the event itself
# --------------------------------------------------
#
# Once the event is done, every name, parent and removal in the view is by
# the event or one it had seen.
def inw.n(nm: M.Name, +W: List<&2, Nat>) -> Bool:
  match nm:
    case M.Name{a, o}:
      M.has(W, a)

def inw.m(p: Maybe<&2, M.Name>, +W: List<&2, Nat>) -> Bool:
  match p:
    case None{}:
      True{}
    case Some{x}:
      inw.n(x, W)

def inw.node(n: M.Node, +W: List<&2, Nat>) -> Bool:
  match n:
    case M.Node{nm, it, M.Place{p, r}, d}:
      Bool.and(inw.n(nm, W), Bool.and(inw.m(p, W), all_has(d, W)))

def inw(t: List<&2, M.Node>, +W: List<&2, Nat>) -> Bool:
  match t:
    case Nil{}:
      True{}
    case x <> xs:
      Bool.and(inw.node(x, W), inw(xs, W))

def before_inw(nm: M.Name, +W: List<&2, Nat>, +k: Nat, +m: Nat, +h: {before(nm, W, k, m) == True{} : Bool}) -> {inw.n(nm, k <> W) == True{} : Bool}:
  match nm:
    case M.Name{+a, +o}:
      or_and_to(Bool.and(Bool.not(Nat.is_eq(a, k)), M.has(W, a)), Nat.is_eq(a, k), Nat.is_lt(o, m), M.has(k <> W, a), h,
        e => AL.or_right(Nat.is_eq(k, a), M.has(W, a), Comp.and_right(Bool.not(Nat.is_eq(a, k)), M.has(W, a), e)),
        e => l => AL.or_left(Nat.is_eq(k, a), M.has(W, a), Equal.trans(Bool, Nat.is_eq(k, a), Nat.is_eq(a, k), True{}, ML.is_eq_sym(a, k), e)))

def before.m_inw(p: Maybe<&2, M.Name>, +W: List<&2, Nat>, +k: Nat, +m: Nat, +h: {before.m(p, W, k, m) == True{} : Bool}) -> {inw.m(p, k <> W) == True{} : Bool}:
  match p:
    case None{}:
      {==}
    case Some{x}:
      before_inw(x, W, k, m, h)

def good_inw(n: M.Node, +W: List<&2, Nat>, +k: Nat, +m: Nat, +h: {good(n, W, k, m) == True{} : Bool}) -> {inw.node(n, k <> W) == True{} : Bool}:
  match n:
    case M.Node{+nm, +it, M.Place{+p, +r}, +d}:
      AL.and_intro(inw.n(nm, k <> W), Bool.and(inw.m(p, k <> W), all_has(d, k <> W)),
        before_inw(nm, W, k, m, Comp.and_left(before(nm, W, k, m), Bool.and(before.m(p, W, k, m), all_has(d, k <> W)), h)),
        AL.and_intro(inw.m(p, k <> W), all_has(d, k <> W),
          before.m_inw(p, W, k, m, Comp.and_left(before.m(p, W, k, m), all_has(d, k <> W), Comp.and_right(before(nm, W, k, m), Bool.and(before.m(p, W, k, m), all_has(d, k <> W)), h))),
          Comp.and_right(before.m(p, W, k, m), all_has(d, k <> W), Comp.and_right(before(nm, W, k, m), Bool.and(before.m(p, W, k, m), all_has(d, k <> W)), h))))

def goods_inw(t: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +m: Nat, +h: {goods(t, W, k, m) == True{} : Bool}) -> {inw(t, k <> W) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +x <> +xs:
      AL.and_intro(inw.node(x, k <> W), inw(xs, k <> W),
        good_inw(x, W, k, m, Comp.and_left(good(x, W, k, m), goods(xs, W, k, m), h)),
        goods_inw(xs, W, k, m, Comp.and_right(good(x, W, k, m), goods(xs, W, k, m), h)))

# Before an event runs: a view whose names are all by events it had seen,
# and not by itself, is bounded by it.
def all_has_weak(d: List<&2, Nat>, +W: List<&2, Nat>, +k: Nat, +h: {all_has(d, W) == True{} : Bool}) -> {all_has(d, k <> W) == True{} : Bool}:
  match d:
    case Nil{}:
      {==}
    case +y <> +ys:
      AL.and_intro(M.has(k <> W, y), all_has(ys, k <> W),
        AL.or_right(Nat.is_eq(k, y), M.has(W, y), Comp.and_left(M.has(W, y), all_has(ys, W), h)),
        all_has_weak(ys, W, k, Comp.and_right(M.has(W, y), all_has(ys, W), h)))

def inw_before(nm: M.Name, +W: List<&2, Nat>, +k: Nat, +hk: {M.has(W, k) == False{} : Bool}, +h: {inw.n(nm, W) == True{} : Bool}) -> {before(nm, W, k, 0n) == True{} : Bool}:
  match nm:
    case M.Name{+a, +o}:
      AL.or_left(Bool.and(Bool.not(Nat.is_eq(a, k)), M.has(W, a)), Bool.and(Nat.is_eq(a, k), Nat.is_lt(o, 0n)),
        AL.and_intro(Bool.not(Nat.is_eq(a, k)), M.has(W, a), AL.not_true(Nat.is_eq(a, k), ML.ne_sym(k, a, ML.ne_of_has(W, k, a, hk, h))), h))

def inw_before.m(p: Maybe<&2, M.Name>, +W: List<&2, Nat>, +k: Nat, +hk: {M.has(W, k) == False{} : Bool}, +h: {inw.m(p, W) == True{} : Bool}) -> {before.m(p, W, k, 0n) == True{} : Bool}:
  match p:
    case None{}:
      {==}
    case Some{x}:
      inw_before(x, W, k, hk, h)

def inw_good(n: M.Node, +W: List<&2, Nat>, +k: Nat, +hk: {M.has(W, k) == False{} : Bool}, +h: {inw.node(n, W) == True{} : Bool}) -> {good(n, W, k, 0n) == True{} : Bool}:
  match n:
    case M.Node{+nm, +it, M.Place{+p, +r}, +d}:
      AL.and_intro(before(nm, W, k, 0n), Bool.and(before.m(p, W, k, 0n), all_has(d, k <> W)),
        inw_before(nm, W, k, hk, Comp.and_left(inw.n(nm, W), Bool.and(inw.m(p, W), all_has(d, W)), h)),
        AL.and_intro(before.m(p, W, k, 0n), all_has(d, k <> W),
          inw_before.m(p, W, k, hk, Comp.and_left(inw.m(p, W), all_has(d, W), Comp.and_right(inw.n(nm, W), Bool.and(inw.m(p, W), all_has(d, W)), h))),
          all_has_weak(d, W, k, Comp.and_right(inw.m(p, W), all_has(d, W), Comp.and_right(inw.n(nm, W), Bool.and(inw.m(p, W), all_has(d, W)), h)))))

def inw_goods(t: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +hk: {M.has(W, k) == False{} : Bool}, +h: {inw(t, W) == True{} : Bool}) -> {goods(t, W, k, 0n) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +x <> +xs:
      AL.and_intro(good(x, W, k, 0n), goods(xs, W, k, 0n),
        inw_good(x, W, k, hk, Comp.and_left(inw.node(x, W), inw(xs, W), h)),
        inw_goods(xs, W, k, hk, Comp.and_right(inw.node(x, W), inw(xs, W), h)))

# A wider set of events bounds what a narrower one did.
def has_sub(a: List<&2, Nat>, +b: List<&2, Nat>, +y: Nat, +s: {M.subset(a, b) == True{} : Bool}, h: {M.has(a, y) == True{} : Bool}) -> {M.has(b, y) == True{} : Bool}:
  match a:
    case Nil{}:
      Empty.absurd({M.has(b, y) == True{} : Bool}, Comp.false_true(h))
    case +x <> +xs:
      AL.or_cases({M.has(b, y) == True{} : Bool}, Nat.is_eq(x, y), M.has(xs, y), h,
        e => (%ML.nat_eq(x, y, e) : {M.has(b, _) == True{} : Bool}
          Comp.and_left(M.has(b, x), M.subset(xs, b), s)),
        e => has_sub(xs, b, y, Comp.and_right(M.has(b, x), M.subset(xs, b), s), e))

def all_has_sub(d: List<&2, Nat>, +a: List<&2, Nat>, +b: List<&2, Nat>, +s: {M.subset(a, b) == True{} : Bool}, +h: {all_has(d, a) == True{} : Bool}) -> {all_has(d, b) == True{} : Bool}:
  match d:
    case Nil{}:
      {==}
    case +y <> +ys:
      AL.and_intro(M.has(b, y), all_has(ys, b),
        has_sub(a, b, y, s, Comp.and_left(M.has(a, y), all_has(ys, a), h)),
        all_has_sub(ys, a, b, s, Comp.and_right(M.has(a, y), all_has(ys, a), h)))

def inw.n_sub(nm: M.Name, +a: List<&2, Nat>, +b: List<&2, Nat>, +s: {M.subset(a, b) == True{} : Bool}, h: {inw.n(nm, a) == True{} : Bool}) -> {inw.n(nm, b) == True{} : Bool}:
  match nm:
    case M.Name{x, o}:
      has_sub(a, b, x, s, h)

def inw.m_sub(p: Maybe<&2, M.Name>, +a: List<&2, Nat>, +b: List<&2, Nat>, +s: {M.subset(a, b) == True{} : Bool}, h: {inw.m(p, a) == True{} : Bool}) -> {inw.m(p, b) == True{} : Bool}:
  match p:
    case None{}:
      {==}
    case Some{x}:
      inw.n_sub(x, a, b, s, h)

def inw_sub(t: List<&2, M.Node>, +a: List<&2, Nat>, +b: List<&2, Nat>, +s: {M.subset(a, b) == True{} : Bool}, +h: {inw(t, a) == True{} : Bool}) -> {inw(t, b) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case M.Node{+nm, +it, M.Place{+p, +r}, +d} <> +xs:
      AL.and_intro(inw.node(M.Node{nm, it, M.Place{p, r}, d}, b), inw(xs, b),
        AL.and_intro(inw.n(nm, b), Bool.and(inw.m(p, b), all_has(d, b)),
          inw.n_sub(nm, a, b, s, Comp.and_left(inw.n(nm, a), Bool.and(inw.m(p, a), all_has(d, a)), Comp.and_left(inw.node(M.Node{nm, it, M.Place{p, r}, d}, a), inw(xs, a), h))),
          AL.and_intro(inw.m(p, b), all_has(d, b),
            inw.m_sub(p, a, b, s, Comp.and_left(inw.m(p, a), all_has(d, a), Comp.and_right(inw.n(nm, a), Bool.and(inw.m(p, a), all_has(d, a)), Comp.and_left(inw.node(M.Node{nm, it, M.Place{p, r}, d}, a), inw(xs, a), h)))),
            all_has_sub(d, a, b, s, Comp.and_right(inw.m(p, a), all_has(d, a), Comp.and_right(inw.n(nm, a), Bool.and(inw.m(p, a), all_has(d, a)), Comp.and_left(inw.node(M.Node{nm, it, M.Place{p, r}, d}, a), inw(xs, a), h)))))),
        inw_sub(xs, a, b, s, Comp.and_right(inw.node(M.Node{nm, it, M.Place{p, r}, d}, a), inw(xs, a), h)))

def subset_weak(a: List<&2, Nat>, +b: List<&2, Nat>, +y: Nat, +s: {M.subset(a, b) == True{} : Bool}) -> {M.subset(a, y <> b) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case +x <> +xs:
      AL.and_intro(M.has(y <> b, x), M.subset(xs, y <> b),
        AL.or_right(Nat.is_eq(y, x), M.has(b, x), Comp.and_left(M.has(b, x), M.subset(xs, b), s)),
        subset_weak(xs, b, y, Comp.and_right(M.has(b, x), M.subset(xs, b), s)))

# An attach adds one bounded element.
def goods_attach.put(+n: M.Node, +x: M.Node, +xs: List<&2, M.Node>, r: List<&2, M.Node>, first: Bool, +W: List<&2, Nat>, +k: Nat, +m: Nat, hn: {good(n, W, k, m) == True{} : Bool}, hx: {good(x, W, k, m) == True{} : Bool}, hxs: {goods(xs, W, k, m) == True{} : Bool}, hr: {goods(r, W, k, m) == True{} : Bool}) -> {goods(M.attach.put(n, x, xs, r, first), W, k, m) == True{} : Bool}:
  match first:
    case True{}:
      AL.and_intro(good(n, W, k, m), goods(x <> xs, W, k, m), hn, AL.and_intro(good(x, W, k, m), goods(xs, W, k, m), hx, hxs))
    case False{}:
      AL.and_intro(good(x, W, k, m), goods(r, W, k, m), hx, hr)

def goods_attach(t: List<&2, M.Node>, +n: M.Node, +W: List<&2, Nat>, +k: Nat, +m: Nat, +hn: {good(n, W, k, m) == True{} : Bool}, +h: {goods(t, W, k, m) == True{} : Bool}) -> {goods(M.attach(t, n), W, k, m) == True{} : Bool}:
  match t:
    case Nil{}:
      AL.and_intro(good(n, W, k, m), True{}, hn, {==})
    case +x <> +xs:
      goods_attach.put(n, x, xs, M.attach(xs, n), Cmp.is_lt(M.Name.cmp(M.Node.name(n), M.Node.name(x))), W, k, m, hn,
        Comp.and_left(good(x, W, k, m), goods(xs, W, k, m), h),
        Comp.and_right(good(x, W, k, m), goods(xs, W, k, m), h),
        goods_attach(xs, n, W, k, m, hn, Comp.and_right(good(x, W, k, m), goods(xs, W, k, m), h)))

# A mark by the event, or one it had seen, keeps every removal bounded.
def all_has_ins.put(+by: Nat, +y: Nat, +ys: List<&2, Nat>, r: List<&2, Nat>, first: Bool, +W: List<&2, Nat>, hb: {M.has(W, by) == True{} : Bool}, hy: {M.has(W, y) == True{} : Bool}, hys: {all_has(ys, W) == True{} : Bool}, hr: {all_has(r, W) == True{} : Bool}) -> {all_has(M.ins.put(by, y, ys, r, first), W) == True{} : Bool}:
  match first:
    case True{}:
      AL.and_intro(M.has(W, by), all_has(y <> ys, W), hb, AL.and_intro(M.has(W, y), all_has(ys, W), hy, hys))
    case False{}:
      AL.and_intro(M.has(W, y), all_has(r, W), hy, hr)

def all_has_ins(d: List<&2, Nat>, +by: Nat, +W: List<&2, Nat>, +hb: {M.has(W, by) == True{} : Bool}, +h: {all_has(d, W) == True{} : Bool}) -> {all_has(M.ins(d, by), W) == True{} : Bool}:
  match d:
    case Nil{}:
      AL.and_intro(M.has(W, by), True{}, hb, {==})
    case +y <> +ys:
      all_has_ins.put(by, y, ys, M.ins(ys, by), Nat.is_lt(by, y), W, hb,
        Comp.and_left(M.has(W, y), all_has(ys, W), h),
        Comp.and_right(M.has(W, y), all_has(ys, W), h),
        all_has_ins(ys, by, W, hb, Comp.and_right(M.has(W, y), all_has(ys, W), h)))

def all_has_ins_if(d: List<&2, Nat>, +by: Nat, hit: Bool, +W: List<&2, Nat>, hb: {M.has(W, by) == True{} : Bool}, +h: {all_has(d, W) == True{} : Bool}) -> {all_has(M.ins.if(d, by, hit), W) == True{} : Bool}:
  match hit:
    case True{}:
      all_has_ins(d, by, W, hb, h)
    case False{}:
      h

def good_mark(n: M.Node, +tg: M.Name, +by: Nat, +W: List<&2, Nat>, +k: Nat, +m: Nat, hb: {M.has(k <> W, by) == True{} : Bool}, +h: {good(n, W, k, m) == True{} : Bool}) -> {good(M.Node.mark(n, tg, by), W, k, m) == True{} : Bool}:
  match n:
    case M.Node{+nm, +it, M.Place{+p, +r}, +d}:
      AL.and_intro(before(nm, W, k, m), Bool.and(before.m(p, W, k, m), all_has(M.ins.if(d, by, M.Name.eq(nm, tg)), k <> W)),
        Comp.and_left(before(nm, W, k, m), Bool.and(before.m(p, W, k, m), all_has(d, k <> W)), h),
        AL.and_intro(before.m(p, W, k, m), all_has(M.ins.if(d, by, M.Name.eq(nm, tg)), k <> W),
          Comp.and_left(before.m(p, W, k, m), all_has(d, k <> W), Comp.and_right(before(nm, W, k, m), Bool.and(before.m(p, W, k, m), all_has(d, k <> W)), h)),
          all_has_ins_if(d, by, M.Name.eq(nm, tg), k <> W, hb, Comp.and_right(before.m(p, W, k, m), all_has(d, k <> W), Comp.and_right(before(nm, W, k, m), Bool.and(before.m(p, W, k, m), all_has(d, k <> W)), h)))))

def goods_mark(t: List<&2, M.Node>, +tg: M.Name, +by: Nat, +W: List<&2, Nat>, +k: Nat, +m: Nat, +hb: {M.has(k <> W, by) == True{} : Bool}, +h: {goods(t, W, k, m) == True{} : Bool}) -> {goods(M.mark(t, tg, by), W, k, m) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +x <> +xs:
      AL.and_intro(good(M.Node.mark(x, tg, by), W, k, m), goods(M.mark(xs, tg, by), W, k, m),
        good_mark(x, tg, by, W, k, m, hb, Comp.and_left(good(x, W, k, m), goods(xs, W, k, m), h)),
        goods_mark(xs, tg, by, W, k, m, hb, Comp.and_right(good(x, W, k, m), goods(xs, W, k, m), h)))

# A view whose names and removals are all by events of `W` is the whole
# tree, restricted to `W`.
def put_true(-A: Data, x: A, r: List<&2, A>, b: Bool, e: {b == True{} : Bool}) -> {List.filter.put(A, x, r, b) == x <> r : List<&2, A>}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({r == x <> r : List<&2, A>}, Comp.false_true(e))

def keep_id(d: List<&2, Nat>, +W: List<&2, Nat>, +h: {all_has(d, W) == True{} : Bool}) -> {M.keep(d, W) == d : List<&2, Nat>}:
  match d:
    case Nil{}:
      {==}
    case +y <> +ys:
      Equal.trans(List<&2, Nat>, List.filter.put(Nat, y, M.keep(ys, W), M.has(W, y)), y <> M.keep(ys, W), y <> ys,
        put_true(Nat, y, M.keep(ys, W), M.has(W, y), Comp.and_left(M.has(W, y), all_has(ys, W), h)),
        Equal.cong(List<&2, Nat>, List<&2, Nat>, l => y <> l, M.keep(ys, W), ys, keep_id(ys, W, Comp.and_right(M.has(W, y), all_has(ys, W), h))))

def restrict_id(t: List<&2, M.Node>, +W: List<&2, Nat>, +h: {inw(t, W) == True{} : Bool}) -> {M.restrict(t, W) == t : List<&2, M.Node>}:
  match t:
    case Nil{}:
      {==}
    case M.Node{M.Name{+a, +o}, +it, M.Place{+p, +r}, +d} <> +xs:
      Equal.trans(List<&2, M.Node>, List.filter.put(M.Node, M.Node{M.Name{a, o}, it, M.Place{p, r}, M.keep(d, W)}, M.restrict(xs, W), M.has(W, a)), M.Node{M.Name{a, o}, it, M.Place{p, r}, M.keep(d, W)} <> M.restrict(xs, W), M.Node{M.Name{a, o}, it, M.Place{p, r}, d} <> xs,
        put_true(M.Node, M.Node{M.Name{a, o}, it, M.Place{p, r}, M.keep(d, W)}, M.restrict(xs, W), M.has(W, a),
          Comp.and_left(M.has(W, a), Bool.and(inw.m(p, W), all_has(d, W)), Comp.and_left(inw.node(M.Node{M.Name{a, o}, it, M.Place{p, r}, d}, W), inw(xs, W), h))),
        (%Equal.sym(List<&2, Nat>, M.keep(d, W), d, keep_id(d, W, Comp.and_right(inw.m(p, W), all_has(d, W), Comp.and_right(M.has(W, a), Bool.and(inw.m(p, W), all_has(d, W)), Comp.and_left(inw.node(M.Node{M.Name{a, o}, it, M.Place{p, r}, d}, W), inw(xs, W), h))))) : {M.Node{M.Name{a, o}, it, M.Place{p, r}, _} <> M.restrict(xs, W) == M.Node{M.Name{a, o}, it, M.Place{p, r}, d} <> xs : List<&2, M.Node>}
          Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => M.Node{M.Name{a, o}, it, M.Place{p, r}, d} <> l, M.restrict(xs, W), xs, restrict_id(xs, W, Comp.and_right(inw.node(M.Node{M.Name{a, o}, it, M.Place{p, r}, d}, W), inw(xs, W), h)))))

# The chain's views are whole
# ---------------------------
#
# Event `k` has seen `upto(k)`, every event before it, and not itself; and
# what it and they did is what event `1 + k` has seen.

def has_upto(n: Nat, +j: Nat, i: Nat, l: {Nat.is_lt(i, n) == True{} : Bool}) -> {M.has(M.upto.go(n, j), Nat.add(i, j)) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({M.has(Nil{}, Nat.add(i, j)) == True{} : Bool}, ML.lt_zero(i, l))
    case 1n++p:
      match i:
        case 0n:
          AL.or_left(Nat.is_eq(j, j), M.has(M.upto.go(p, 1n+j), j), Comp.eq_refl(j))
        case 1n++q:
          AL.or_right(Nat.is_eq(j, 1n+Nat.add(q, j)), M.has(M.upto.go(p, 1n+j), 1n+Nat.add(q, j)),
            (%Pos.add_succ(q, j) : {M.has(M.upto.go(p, 1n+j), _) == True{} : Bool}
              has_upto(p, 1n+j, q, l)))

def ne_above(j: Nat, +p: Nat) -> {Nat.is_eq(j, 1n+Nat.add(p, j)) == False{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n++jp:
      %Equal.sym(Nat, Nat.add(p, 1n+jp), 1n+Nat.add(p, jp), Pos.add_succ(p, jp)) : {Nat.is_eq(jp, _) == False{} : Bool}
      ne_above(jp, p)

def has_upto_top(n: Nat, +j: Nat) -> {M.has(M.upto.go(n, j), Nat.add(n, j)) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      AL.or_false(Nat.is_eq(j, 1n+Nat.add(p, j)), M.has(M.upto.go(p, 1n+j), 1n+Nat.add(p, j)),
        ne_above(j, p),
        (%Pos.add_succ(p, j) : {M.has(M.upto.go(p, 1n+j), _) == False{} : Bool}
          has_upto_top(p, 1n+j)))

# An event has not seen itself.
def not_seen_self(+k: Nat) -> {M.has(M.upto(k), k) == False{} : Bool}:
  %Comp.add_zero(k) : {M.has(M.upto(k), _) == False{} : Bool}
  has_upto_top(k, 0n)

def seen_below(+k: Nat, +a: Nat, l: {Nat.is_lt(a, k) == True{} : Bool}) -> {M.has(M.upto(k), a) == True{} : Bool}:
  %Comp.add_zero(a) : {M.has(M.upto(k), _) == True{} : Bool}
  has_upto(k, 0n, a, l)

def upto_sub(n: Nat, +s: Nat) -> {M.subset(M.upto.go(n, s), M.upto.go(1n+n, s)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      AL.and_intro(M.has(s <> M.upto.go(1n+p, 1n+s), s), M.subset(M.upto.go(p, 1n+s), s <> M.upto.go(1n+p, 1n+s)),
        AL.or_left(Nat.is_eq(s, s), M.has(M.upto.go(1n+p, 1n+s), s), Comp.eq_refl(s)),
        subset_weak(M.upto.go(p, 1n+s), M.upto.go(1n+p, 1n+s), s, upto_sub(p, 1n+s)))

# What event `k` and the events it had seen did, event `1 + k` has seen.
def upto_step(+k: Nat) -> {M.subset(k <> M.upto(k), M.upto(1n+k)) == True{} : Bool}:
  AL.and_intro(M.has(M.upto(1n+k), k), M.subset(M.upto(k), M.upto(1n+k)),
    seen_below(1n+k, k, Comp.lt_succ_self(k)),
    upto_sub(k, 0n))

# Removals
# --------
#
# An event's deletes are marks; a view read after them is the view read
# before, with every element a delete names left out (`cuts`). `hit` says
# whether an element's name is one a delete names, `clear` that none of a
# list's is, `gone` that all of them are.
def cut(xs: List<&2, M.Node>, +tg: M.Name) -> List<&2, M.Node>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      List.filter.put(M.Node, x, cut(rest, tg), Bool.not(M.Name.eq(M.Node.name(x), tg)))

def cuts(acts: List<&2, M.Action>, xs: List<&2, M.Node>) -> List<&2, M.Node>:
  match acts:
    case Nil{}:
      xs
    case M.Attach{m, it, pl} <> rest:
      cuts(rest, xs)
    case M.Delete{tg} <> rest:
      cuts(rest, cut(xs, tg))

def hit(acts: List<&2, M.Action>, +nm: M.Name) -> Bool:
  match acts:
    case Nil{}:
      False{}
    case M.Attach{m, it, pl} <> rest:
      hit(rest, nm)
    case M.Delete{tg} <> rest:
      Bool.or(M.Name.eq(nm, tg), hit(rest, nm))

def clear(xs: List<&2, M.Node>, +acts: List<&2, M.Action>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(Bool.not(hit(acts, M.Node.name(x))), clear(rest, acts))

def gone(xs: List<&2, M.Node>, +acts: List<&2, M.Action>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(hit(acts, M.Node.name(x)), gone(rest, acts))

# The deletes of a run of elements.
def dels(ds: List<&2, M.Node>) -> List<&2, M.Action>:
  match ds:
    case Nil{}:
      Nil{}
    case x <> rest:
      M.Delete{M.Node.name(x)} <> dels(rest)

# The tree an event's actions leave, with the attaches already made: its
# marks, by the event.
def mk(acts: List<&2, M.Action>, t: List<&2, M.Node>, +by: Nat) -> List<&2, M.Node>:
  match acts:
    case Nil{}:
      t
    case M.Attach{m, it, pl} <> rest:
      mk(rest, t, by)
    case M.Delete{tg} <> rest:
      mk(rest, M.mark(t, tg, by), by)

def cuts_cons.d(rest: List<&2, M.Action>, +x: M.Node, +ys: List<&2, M.Node>, b: Bool, ih: {cuts(rest, x <> ys) == List.filter.put(M.Node, x, cuts(rest, ys), Bool.not(hit(rest, M.Node.name(x)))) : List<&2, M.Node>}) -> {cuts(rest, List.filter.put(M.Node, x, ys, Bool.not(b))) == List.filter.put(M.Node, x, cuts(rest, ys), Bool.not(Bool.or(b, hit(rest, M.Node.name(x))))) : List<&2, M.Node>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# The one fact everything below is read from.
def cuts_cons(acts: List<&2, M.Action>, +x: M.Node, +xs: List<&2, M.Node>) -> {cuts(acts, x <> xs) == List.filter.put(M.Node, x, cuts(acts, xs), Bool.not(hit(acts, M.Node.name(x)))) : List<&2, M.Node>}:
  match acts:
    case Nil{}:
      {==}
    case M.Attach{m, it, pl} <> rest:
      cuts_cons(rest, x, xs)
    case M.Delete{+tg} <> +rest:
      cuts_cons.d(rest, x, cut(xs, tg), M.Name.eq(M.Node.name(x), tg), cuts_cons(rest, x, cut(xs, tg)))

def cuts_nil(acts: List<&2, M.Action>) -> {cuts(acts, Nil{}) == Nil{} : List<&2, M.Node>}:
  match acts:
    case Nil{}:
      {==}
    case M.Attach{m, it, pl} <> rest:
      cuts_nil(rest)
    case M.Delete{tg} <> rest:
      cuts_nil(rest)

def put_append(x: M.Node, a: List<&2, M.Node>, -b: List<&2, M.Node>, keep: Bool) -> {List.append(&2, M.Node, List.filter.put(M.Node, x, a, keep), b) == List.filter.put(M.Node, x, List.append(&2, M.Node, a, b), keep) : List<&2, M.Node>}:
  match keep:
    case True{}:
      {==}
    case False{}:
      {==}

def cuts_append(+acts: List<&2, M.Action>, xs: List<&2, M.Node>, +ys: List<&2, M.Node>) -> {cuts(acts, List.append(&2, M.Node, xs, ys)) == List.append(&2, M.Node, cuts(acts, xs), cuts(acts, ys)) : List<&2, M.Node>}:
  match xs:
    case Nil{}:
      %Equal.sym(List<&2, M.Node>, cuts(acts, Nil{}), Nil{}, cuts_nil(acts)) : {cuts(acts, ys) == List.append(&2, M.Node, _, cuts(acts, ys)) : List<&2, M.Node>}
      {==}
    case +x <> +rest:
      Equal.trans(List<&2, M.Node>, cuts(acts, x <> List.append(&2, M.Node, rest, ys)), List.filter.put(M.Node, x, cuts(acts, List.append(&2, M.Node, rest, ys)), Bool.not(hit(acts, M.Node.name(x)))), List.append(&2, M.Node, cuts(acts, x <> rest), cuts(acts, ys)),
        cuts_cons(acts, x, List.append(&2, M.Node, rest, ys)),
        Equal.trans(List<&2, M.Node>, List.filter.put(M.Node, x, cuts(acts, List.append(&2, M.Node, rest, ys)), Bool.not(hit(acts, M.Node.name(x)))), List.filter.put(M.Node, x, List.append(&2, M.Node, cuts(acts, rest), cuts(acts, ys)), Bool.not(hit(acts, M.Node.name(x)))), List.append(&2, M.Node, cuts(acts, x <> rest), cuts(acts, ys)),
          Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => List.filter.put(M.Node, x, l, Bool.not(hit(acts, M.Node.name(x)))), cuts(acts, List.append(&2, M.Node, rest, ys)), List.append(&2, M.Node, cuts(acts, rest), cuts(acts, ys)), cuts_append(acts, rest, ys)),
          Equal.trans(List<&2, M.Node>, List.filter.put(M.Node, x, List.append(&2, M.Node, cuts(acts, rest), cuts(acts, ys)), Bool.not(hit(acts, M.Node.name(x)))), List.append(&2, M.Node, List.filter.put(M.Node, x, cuts(acts, rest), Bool.not(hit(acts, M.Node.name(x)))), cuts(acts, ys)), List.append(&2, M.Node, cuts(acts, x <> rest), cuts(acts, ys)),
            Equal.sym(List<&2, M.Node>, List.append(&2, M.Node, List.filter.put(M.Node, x, cuts(acts, rest), Bool.not(hit(acts, M.Node.name(x)))), cuts(acts, ys)), List.filter.put(M.Node, x, List.append(&2, M.Node, cuts(acts, rest), cuts(acts, ys)), Bool.not(hit(acts, M.Node.name(x)))), put_append(x, cuts(acts, rest), cuts(acts, ys), Bool.not(hit(acts, M.Node.name(x))))),
            Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => List.append(&2, M.Node, l, cuts(acts, ys)), List.filter.put(M.Node, x, cuts(acts, rest), Bool.not(hit(acts, M.Node.name(x)))), cuts(acts, x <> rest), Equal.sym(List<&2, M.Node>, cuts(acts, x <> rest), List.filter.put(M.Node, x, cuts(acts, rest), Bool.not(hit(acts, M.Node.name(x)))), cuts_cons(acts, x, rest))))))

def put_hit(x: M.Node, r: List<&2, M.Node>, b: Bool, e: {b == False{} : Bool}) -> {List.filter.put(M.Node, x, r, Bool.not(b)) == x <> r : List<&2, M.Node>}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({r == x <> r : List<&2, M.Node>}, ML.true_false(e))

def put_miss(x: M.Node, r: List<&2, M.Node>, b: Bool, e: {b == True{} : Bool}) -> {List.filter.put(M.Node, x, r, Bool.not(b)) == r : List<&2, M.Node>}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({x <> r == r : List<&2, M.Node>}, Comp.false_true(e))

# What no delete names is read as it was.
def cuts_clear(+acts: List<&2, M.Action>, xs: List<&2, M.Node>, +h: {clear(xs, acts) == True{} : Bool}) -> {cuts(acts, xs) == xs : List<&2, M.Node>}:
  match xs:
    case Nil{}:
      cuts_nil(acts)
    case +x <> +rest:
      Equal.trans(List<&2, M.Node>, cuts(acts, x <> rest), List.filter.put(M.Node, x, cuts(acts, rest), Bool.not(hit(acts, M.Node.name(x)))), x <> rest,
        cuts_cons(acts, x, rest),
        Equal.trans(List<&2, M.Node>, List.filter.put(M.Node, x, cuts(acts, rest), Bool.not(hit(acts, M.Node.name(x)))), x <> cuts(acts, rest), x <> rest,
          put_hit(x, cuts(acts, rest), hit(acts, M.Node.name(x)), AL.not_of_true(hit(acts, M.Node.name(x)), Comp.and_left(Bool.not(hit(acts, M.Node.name(x))), clear(rest, acts), h))),
          Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => x <> l, cuts(acts, rest), rest, cuts_clear(acts, rest, Comp.and_right(Bool.not(hit(acts, M.Node.name(x))), clear(rest, acts), h)))))

# What every delete names is left out.
def cuts_gone(+acts: List<&2, M.Action>, xs: List<&2, M.Node>, +h: {gone(xs, acts) == True{} : Bool}) -> {cuts(acts, xs) == Nil{} : List<&2, M.Node>}:
  match xs:
    case Nil{}:
      cuts_nil(acts)
    case +x <> +rest:
      Equal.trans(List<&2, M.Node>, cuts(acts, x <> rest), List.filter.put(M.Node, x, cuts(acts, rest), Bool.not(hit(acts, M.Node.name(x)))), Nil{},
        cuts_cons(acts, x, rest),
        Equal.trans(List<&2, M.Node>, List.filter.put(M.Node, x, cuts(acts, rest), Bool.not(hit(acts, M.Node.name(x)))), cuts(acts, rest), Nil{},
          put_miss(x, cuts(acts, rest), hit(acts, M.Node.name(x)), Comp.and_left(hit(acts, M.Node.name(x)), gone(rest, acts), h)),
          cuts_gone(acts, rest, Comp.and_right(hit(acts, M.Node.name(x)), gone(rest, acts), h))))

def cuts_seq(a1: List<&2, M.Action>, +a2: List<&2, M.Action>, xs: List<&2, M.Node>) -> {cuts(List.append(&2, M.Action, a1, a2), xs) == cuts(a2, cuts(a1, xs)) : List<&2, M.Node>}:
  match a1:
    case Nil{}:
      {==}
    case M.Attach{m, it, pl} <> rest:
      cuts_seq(rest, a2, xs)
    case M.Delete{+tg} <> rest:
      cuts_seq(rest, a2, cut(xs, tg))

def clear_put(+x: M.Node, r: List<&2, M.Node>, b: Bool, +more: List<&2, M.Action>, hx: {Bool.not(hit(more, M.Node.name(x))) == True{} : Bool}, hr: {clear(r, more) == True{} : Bool}) -> {clear(List.filter.put(M.Node, x, r, b), more) == True{} : Bool}:
  match b:
    case True{}:
      AL.and_intro(Bool.not(hit(more, M.Node.name(x))), clear(r, more), hx, hr)
    case False{}:
      hr

# A list clear of some deletes stays clear once others are made.
def clear_cuts(+more: List<&2, M.Action>, +acts: List<&2, M.Action>, xs: List<&2, M.Node>, +h: {clear(xs, more) == True{} : Bool}) -> {clear(cuts(acts, xs), more) == True{} : Bool}:
  match xs:
    case Nil{}:
      %Equal.sym(List<&2, M.Node>, cuts(acts, Nil{}), Nil{}, cuts_nil(acts)) : {clear(_, more) == True{} : Bool}
      {==}
    case +x <> +rest:
      %Equal.sym(List<&2, M.Node>, cuts(acts, x <> rest), List.filter.put(M.Node, x, cuts(acts, rest), Bool.not(hit(acts, M.Node.name(x)))), cuts_cons(acts, x, rest)) : {clear(_, more) == True{} : Bool}
      clear_put(x, cuts(acts, rest), Bool.not(hit(acts, M.Node.name(x))), more,
        Comp.and_left(Bool.not(hit(more, M.Node.name(x))), clear(rest, more), h),
        clear_cuts(more, acts, rest, Comp.and_right(Bool.not(hit(more, M.Node.name(x))), clear(rest, more), h)))

# Deletes added after the ones made, naming nothing a list holds, leave it.
def cuts_after(+acts: List<&2, M.Action>, +more: List<&2, M.Action>, +xs: List<&2, M.Node>, h: {clear(xs, more) == True{} : Bool}) -> {cuts(List.append(&2, M.Action, acts, more), xs) == cuts(acts, xs) : List<&2, M.Node>}:
  Equal.trans(List<&2, M.Node>, cuts(List.append(&2, M.Action, acts, more), xs), cuts(more, cuts(acts, xs)), cuts(acts, xs),
    cuts_seq(acts, more, xs),
    cuts_clear(more, cuts(acts, xs), clear_cuts(more, acts, xs, h)))

def hit_append(a1: List<&2, M.Action>, +a2: List<&2, M.Action>, +nm: M.Name, +h1: {hit(a1, nm) == False{} : Bool}, h2: {hit(a2, nm) == False{} : Bool}) -> {hit(List.append(&2, M.Action, a1, a2), nm) == False{} : Bool}:
  match a1:
    case Nil{}:
      h2
    case M.Attach{m, it, pl} <> rest:
      hit_append(rest, a2, nm, h1, h2)
    case M.Delete{+tg} <> +rest:
      AL.or_false(M.Name.eq(nm, tg), hit(List.append(&2, M.Action, rest, a2), nm),
        AL.or_false_l(M.Name.eq(nm, tg), hit(rest, nm), h1),
        hit_append(rest, a2, nm, AL.or_false_r(M.Name.eq(nm, tg), hit(rest, nm), h1), h2))

def clear_append(xs: List<&2, M.Node>, +a1: List<&2, M.Action>, +a2: List<&2, M.Action>, +h1: {clear(xs, a1) == True{} : Bool}, +h2: {clear(xs, a2) == True{} : Bool}) -> {clear(xs, List.append(&2, M.Action, a1, a2)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Bool.not(hit(List.append(&2, M.Action, a1, a2), M.Node.name(x))), clear(rest, List.append(&2, M.Action, a1, a2)),
        AL.not_true(hit(List.append(&2, M.Action, a1, a2), M.Node.name(x)),
          hit_append(a1, a2, M.Node.name(x),
            AL.not_of_true(hit(a1, M.Node.name(x)), Comp.and_left(Bool.not(hit(a1, M.Node.name(x))), clear(rest, a1), h1)),
            AL.not_of_true(hit(a2, M.Node.name(x)), Comp.and_left(Bool.not(hit(a2, M.Node.name(x))), clear(rest, a2), h2)))),
        clear_append(rest, a1, a2, Comp.and_right(Bool.not(hit(a1, M.Node.name(x))), clear(rest, a1), h1), Comp.and_right(Bool.not(hit(a2, M.Node.name(x))), clear(rest, a2), h2)))

def clear_left(xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +acts: List<&2, M.Action>, +h: {clear(List.append(&2, M.Node, xs, ys), acts) == True{} : Bool}) -> {clear(xs, acts) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Bool.not(hit(acts, M.Node.name(x))), clear(rest, acts),
        Comp.and_left(Bool.not(hit(acts, M.Node.name(x))), clear(List.append(&2, M.Node, rest, ys), acts), h),
        clear_left(rest, ys, acts, Comp.and_right(Bool.not(hit(acts, M.Node.name(x))), clear(List.append(&2, M.Node, rest, ys), acts), h)))

def clear_right(xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +acts: List<&2, M.Action>, h: {clear(List.append(&2, M.Node, xs, ys), acts) == True{} : Bool}) -> {clear(ys, acts) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +x <> +rest:
      clear_right(rest, ys, acts, Comp.and_right(Bool.not(hit(acts, M.Node.name(x))), clear(List.append(&2, M.Node, rest, ys), acts), h))

# Apart
# -----
#
# `sep(xs, ys)`: no element of `xs` is named in `ys`, which a duplicate-free
# reading gives of any two of its pieces.
def sep(xs: List<&2, M.Node>, +ys: List<&2, M.Node>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(Bool.not(M.named(ys, M.Node.name(x))), sep(rest, ys))

def nodup_sep(xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +nd: {M.nodup(List.append(&2, M.Node, xs, ys)) == True{} : Bool}) -> {sep(xs, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Bool.not(M.named(ys, M.Node.name(x))), sep(rest, ys),
        AL.not_true(M.named(ys, M.Node.name(x)),
          AL.or_false_r(M.named(rest, M.Node.name(x)), M.named(ys, M.Node.name(x)),
            Equal.trans(Bool, Bool.or(M.named(rest, M.Node.name(x)), M.named(ys, M.Node.name(x))), M.named(List.append(&2, M.Node, rest, ys), M.Node.name(x)), False{},
              Equal.sym(Bool, M.named(List.append(&2, M.Node, rest, ys), M.Node.name(x)), Bool.or(M.named(rest, M.Node.name(x)), M.named(ys, M.Node.name(x))), AL.named_append(rest, ys, M.Node.name(x))),
              AL.not_of_true(M.named(List.append(&2, M.Node, rest, ys), M.Node.name(x)), Comp.and_left(Bool.not(M.named(List.append(&2, M.Node, rest, ys), M.Node.name(x))), M.nodup(List.append(&2, M.Node, rest, ys)), nd))))),
        nodup_sep(rest, ys, Comp.and_right(Bool.not(M.named(List.append(&2, M.Node, rest, ys), M.Node.name(x))), M.nodup(List.append(&2, M.Node, rest, ys)), nd)))

def named_left(+xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +nm: M.Name, h: {M.named(List.append(&2, M.Node, xs, ys), nm) == False{} : Bool}) -> {M.named(xs, nm) == False{} : Bool}:
  AL.or_false_l(M.named(xs, nm), M.named(ys, nm), Equal.trans(Bool, Bool.or(M.named(xs, nm), M.named(ys, nm)), M.named(List.append(&2, M.Node, xs, ys), nm), False{}, Equal.sym(Bool, M.named(List.append(&2, M.Node, xs, ys), nm), Bool.or(M.named(xs, nm), M.named(ys, nm)), AL.named_append(xs, ys, nm)), h))

def named_right(+xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +nm: M.Name, h: {M.named(List.append(&2, M.Node, xs, ys), nm) == False{} : Bool}) -> {M.named(ys, nm) == False{} : Bool}:
  AL.or_false_r(M.named(xs, nm), M.named(ys, nm), Equal.trans(Bool, Bool.or(M.named(xs, nm), M.named(ys, nm)), M.named(List.append(&2, M.Node, xs, ys), nm), False{}, Equal.sym(Bool, M.named(List.append(&2, M.Node, xs, ys), nm), Bool.or(M.named(xs, nm), M.named(ys, nm)), AL.named_append(xs, ys, nm)), h))

def sep_left(xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +zs: List<&2, M.Node>, +h: {sep(xs, List.append(&2, M.Node, ys, zs)) == True{} : Bool}) -> {sep(xs, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Bool.not(M.named(ys, M.Node.name(x))), sep(rest, ys),
        AL.not_true(M.named(ys, M.Node.name(x)), named_left(ys, zs, M.Node.name(x), AL.not_of_true(M.named(List.append(&2, M.Node, ys, zs), M.Node.name(x)), Comp.and_left(Bool.not(M.named(List.append(&2, M.Node, ys, zs), M.Node.name(x))), sep(rest, List.append(&2, M.Node, ys, zs)), h)))),
        sep_left(rest, ys, zs, Comp.and_right(Bool.not(M.named(List.append(&2, M.Node, ys, zs), M.Node.name(x))), sep(rest, List.append(&2, M.Node, ys, zs)), h)))

def sep_right(xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +zs: List<&2, M.Node>, +h: {sep(xs, List.append(&2, M.Node, ys, zs)) == True{} : Bool}) -> {sep(xs, zs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Bool.not(M.named(zs, M.Node.name(x))), sep(rest, zs),
        AL.not_true(M.named(zs, M.Node.name(x)), named_right(ys, zs, M.Node.name(x), AL.not_of_true(M.named(List.append(&2, M.Node, ys, zs), M.Node.name(x)), Comp.and_left(Bool.not(M.named(List.append(&2, M.Node, ys, zs), M.Node.name(x))), sep(rest, List.append(&2, M.Node, ys, zs)), h)))),
        sep_right(rest, ys, zs, Comp.and_right(Bool.not(M.named(List.append(&2, M.Node, ys, zs), M.Node.name(x))), sep(rest, List.append(&2, M.Node, ys, zs)), h)))

def sep_lleft(xs: List<&2, M.Node>, +ws: List<&2, M.Node>, +ys: List<&2, M.Node>, +h: {sep(List.append(&2, M.Node, xs, ws), ys) == True{} : Bool}) -> {sep(xs, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Bool.not(M.named(ys, M.Node.name(x))), sep(rest, ys),
        Comp.and_left(Bool.not(M.named(ys, M.Node.name(x))), sep(List.append(&2, M.Node, rest, ws), ys), h),
        sep_lleft(rest, ws, ys, Comp.and_right(Bool.not(M.named(ys, M.Node.name(x))), sep(List.append(&2, M.Node, rest, ws), ys), h)))

def sep_lright(xs: List<&2, M.Node>, +ws: List<&2, M.Node>, +ys: List<&2, M.Node>, h: {sep(List.append(&2, M.Node, xs, ws), ys) == True{} : Bool}) -> {sep(ws, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +x <> +rest:
      sep_lright(rest, ws, ys, Comp.and_right(Bool.not(M.named(ys, M.Node.name(x))), sep(List.append(&2, M.Node, rest, ws), ys), h))

# The deletes of a run name exactly its elements.
def hit_dels(xs: List<&2, M.Node>, +nm: M.Name) -> {hit(dels(xs), nm) == M.named(xs, nm) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      Equal.trans(Bool, Bool.or(M.Name.eq(nm, M.Node.name(x)), hit(dels(rest), nm)), Bool.or(M.Name.eq(nm, M.Node.name(x)), M.named(rest, nm)), Bool.or(M.Name.eq(M.Node.name(x), nm), M.named(rest, nm)),
        Equal.cong(Bool, Bool, l => Bool.or(M.Name.eq(nm, M.Node.name(x)), l), hit(dels(rest), nm), M.named(rest, nm), hit_dels(rest, nm)),
        Equal.cong(Bool, Bool, l => Bool.or(l, M.named(rest, nm)), M.Name.eq(nm, M.Node.name(x)), M.Name.eq(M.Node.name(x), nm), AL.name_eq_sym(M.Node.name(x), nm)))

def gone_weaken(xs: List<&2, M.Node>, +y: M.Node, +ys: List<&2, M.Node>, +h: {gone(xs, dels(ys)) == True{} : Bool}) -> {gone(xs, dels(y <> ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Bool.or(M.Name.eq(M.Node.name(x), M.Node.name(y)), hit(dels(ys), M.Node.name(x))), gone(rest, dels(y <> ys)),
        AL.or_right(M.Name.eq(M.Node.name(x), M.Node.name(y)), hit(dels(ys), M.Node.name(x)), Comp.and_left(hit(dels(ys), M.Node.name(x)), gone(rest, dels(ys)), h)),
        gone_weaken(rest, y, ys, Comp.and_right(hit(dels(ys), M.Node.name(x)), gone(rest, dels(ys)), h)))

def gone_dels(xs: List<&2, M.Node>) -> {gone(xs, dels(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Bool.or(M.Name.eq(M.Node.name(x), M.Node.name(x)), hit(dels(rest), M.Node.name(x))), gone(rest, dels(x <> rest)),
        AL.or_left(M.Name.eq(M.Node.name(x), M.Node.name(x)), hit(dels(rest), M.Node.name(x)), AL.name_eq_refl(M.Node.name(x))),
        gone_weaken(rest, x, rest, gone_dels(rest)))

# Pieces apart: what one is, the deletes of the other do not name.
def sep_clear_rev(xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +h: {sep(xs, ys) == True{} : Bool}) -> {clear(xs, dels(ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Bool.not(hit(dels(ys), M.Node.name(x))), clear(rest, dels(ys)),
        (%Equal.sym(Bool, hit(dels(ys), M.Node.name(x)), M.named(ys, M.Node.name(x)), hit_dels(ys, M.Node.name(x))) : {Bool.not(_) == True{} : Bool}
          Comp.and_left(Bool.not(M.named(ys, M.Node.name(x))), sep(rest, ys), h)),
        sep_clear_rev(rest, ys, Comp.and_right(Bool.not(M.named(ys, M.Node.name(x))), sep(rest, ys), h)))

def sep_head(xs: List<&2, M.Node>, +y: M.Node, +ys: List<&2, M.Node>, +h: {sep(xs, y <> ys) == True{} : Bool}) -> {hit(dels(xs), M.Node.name(y)) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.or_false(M.Name.eq(M.Node.name(y), M.Node.name(x)), hit(dels(rest), M.Node.name(y)),
        AL.or_false_l(M.Name.eq(M.Node.name(y), M.Node.name(x)), M.named(ys, M.Node.name(x)), AL.not_of_true(M.named(y <> ys, M.Node.name(x)), Comp.and_left(Bool.not(M.named(y <> ys, M.Node.name(x))), sep(rest, y <> ys), h))),
        sep_head(rest, y, ys, Comp.and_right(Bool.not(M.named(y <> ys, M.Node.name(x))), sep(rest, y <> ys), h)))

def sep_tail(xs: List<&2, M.Node>, +y: M.Node, +ys: List<&2, M.Node>, +h: {sep(xs, y <> ys) == True{} : Bool}) -> {sep(xs, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Bool.not(M.named(ys, M.Node.name(x))), sep(rest, ys),
        AL.not_true(M.named(ys, M.Node.name(x)), AL.or_false_r(M.Name.eq(M.Node.name(y), M.Node.name(x)), M.named(ys, M.Node.name(x)), AL.not_of_true(M.named(y <> ys, M.Node.name(x)), Comp.and_left(Bool.not(M.named(y <> ys, M.Node.name(x))), sep(rest, y <> ys), h)))),
        sep_tail(rest, y, ys, Comp.and_right(Bool.not(M.named(y <> ys, M.Node.name(x))), sep(rest, y <> ys), h)))

def sep_clear(+xs: List<&2, M.Node>, ys: List<&2, M.Node>, +h: {sep(xs, ys) == True{} : Bool}) -> {clear(ys, dels(xs)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +rest:
      AL.and_intro(Bool.not(hit(dels(xs), M.Node.name(y))), clear(rest, dels(xs)),
        AL.not_true(hit(dels(xs), M.Node.name(y)), sep_head(xs, y, rest, h)),
        sep_clear(xs, rest, sep_tail(xs, y, rest, h)))

# The view after a mark
# ---------------------
def ins_put_standing(+nm: M.Name, +it: Ops.Item, +pl: M.Place, +by: Nat, +y: Nat, +ys: List<&2, Nat>, r: List<&2, Nat>, b: Bool) -> {M.Node.standing(M.Node{nm, it, pl, M.ins.put(by, y, ys, r, b)}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ins_standing(+nm: M.Name, +it: Ops.Item, +pl: M.Place, d: List<&2, Nat>, +by: Nat) -> {M.Node.standing(M.Node{nm, it, pl, M.ins(d, by)}) == False{} : Bool}:
  match d:
    case Nil{}:
      {==}
    case +y <> +ys:
      ins_put_standing(nm, it, pl, by, y, ys, M.ins(ys, by), Nat.is_lt(by, y))

def node_mark_hit(+nm: M.Name, +it: Ops.Item, +pl: M.Place, +d: List<&2, Nat>, +tg: M.Name, +by: Nat, e: {M.Name.eq(nm, tg) == True{} : Bool}) -> {M.Node.mark(M.Node{nm, it, pl, d}, tg, by) == M.Node{nm, it, pl, M.ins(d, by)} : M.Node}:
  %Equal.sym(Bool, M.Name.eq(nm, tg), True{}, e) : {M.Node{nm, it, pl, M.ins.if(d, by, _)} == M.Node{nm, it, pl, M.ins(d, by)} : M.Node}
  {==}

def node_mark_miss(+nm: M.Name, +it: Ops.Item, +pl: M.Place, +d: List<&2, Nat>, +tg: M.Name, +by: Nat, e: {M.Name.eq(nm, tg) == False{} : Bool}) -> {M.Node.mark(M.Node{nm, it, pl, d}, tg, by) == M.Node{nm, it, pl, d} : M.Node}:
  %Equal.sym(Bool, M.Name.eq(nm, tg), False{}, e) : {M.Node{nm, it, pl, M.ins.if(d, by, _)} == M.Node{nm, it, pl, d} : M.Node}
  {==}

def cut_put_hit(+x: M.Node, r: List<&2, M.Node>, s: Bool, +tg: M.Name, e: {M.Name.eq(M.Node.name(x), tg) == True{} : Bool}) -> {cut(List.filter.put(M.Node, x, r, s), tg) == cut(r, tg) : List<&2, M.Node>}:
  match s:
    case True{}:
      %Equal.sym(Bool, M.Name.eq(M.Node.name(x), tg), True{}, e) : {List.filter.put(M.Node, x, cut(r, tg), Bool.not(_)) == cut(r, tg) : List<&2, M.Node>}
      {==}
    case False{}:
      {==}

def cut_put_miss(+x: M.Node, r: List<&2, M.Node>, s: Bool, +tg: M.Name, e: {M.Name.eq(M.Node.name(x), tg) == False{} : Bool}) -> {cut(List.filter.put(M.Node, x, r, s), tg) == List.filter.put(M.Node, x, cut(r, tg), s) : List<&2, M.Node>}:
  match s:
    case True{}:
      %Equal.sym(Bool, M.Name.eq(M.Node.name(x), tg), False{}, e) : {List.filter.put(M.Node, x, cut(r, tg), Bool.not(_)) == x <> cut(r, tg) : List<&2, M.Node>}
      {==}
    case False{}:
      {==}

def std_mark.at(+nm: M.Name, +it: Ops.Item, +pl: M.Place, +d: List<&2, Nat>, +rest: List<&2, M.Node>, +tg: M.Name, +by: Nat, e: Bool, +ee: {M.Name.eq(nm, tg) == e : Bool}, ih: {M.standing(M.mark(rest, tg, by)) == cut(M.standing(rest), tg) : List<&2, M.Node>}) -> {M.standing(M.Node.mark(M.Node{nm, it, pl, d}, tg, by) <> M.mark(rest, tg, by)) == cut(M.standing(M.Node{nm, it, pl, d} <> rest), tg) : List<&2, M.Node>}:
  match e:
    case True{}:
      %Equal.sym(M.Node, M.Node.mark(M.Node{nm, it, pl, d}, tg, by), M.Node{nm, it, pl, M.ins(d, by)}, node_mark_hit(nm, it, pl, d, tg, by, ee)) : {M.standing(_ <> M.mark(rest, tg, by)) == cut(M.standing(M.Node{nm, it, pl, d} <> rest), tg) : List<&2, M.Node>}
      %Equal.sym(Bool, M.Node.standing(M.Node{nm, it, pl, M.ins(d, by)}), False{}, ins_standing(nm, it, pl, d, by)) : {List.filter.put(M.Node, M.Node{nm, it, pl, M.ins(d, by)}, M.standing(M.mark(rest, tg, by)), _) == cut(M.standing(M.Node{nm, it, pl, d} <> rest), tg) : List<&2, M.Node>}
      %Equal.sym(List<&2, M.Node>, cut(M.standing(M.Node{nm, it, pl, d} <> rest), tg), cut(M.standing(rest), tg), cut_put_hit(M.Node{nm, it, pl, d}, M.standing(rest), M.Node.standing(M.Node{nm, it, pl, d}), tg, ee)) : {M.standing(M.mark(rest, tg, by)) == _ : List<&2, M.Node>}
      ih
    case False{}:
      %Equal.sym(M.Node, M.Node.mark(M.Node{nm, it, pl, d}, tg, by), M.Node{nm, it, pl, d}, node_mark_miss(nm, it, pl, d, tg, by, ee)) : {M.standing(_ <> M.mark(rest, tg, by)) == cut(M.standing(M.Node{nm, it, pl, d} <> rest), tg) : List<&2, M.Node>}
      %Equal.sym(List<&2, M.Node>, cut(M.standing(M.Node{nm, it, pl, d} <> rest), tg), List.filter.put(M.Node, M.Node{nm, it, pl, d}, cut(M.standing(rest), tg), M.Node.standing(M.Node{nm, it, pl, d})), cut_put_miss(M.Node{nm, it, pl, d}, M.standing(rest), M.Node.standing(M.Node{nm, it, pl, d}), tg, ee)) : {M.standing(M.Node{nm, it, pl, d} <> M.mark(rest, tg, by)) == _ : List<&2, M.Node>}
      Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => List.filter.put(M.Node, M.Node{nm, it, pl, d}, l, M.Node.standing(M.Node{nm, it, pl, d})), M.standing(M.mark(rest, tg, by)), cut(M.standing(rest), tg), ih)

def standing_mark(xs: List<&2, M.Node>, +tg: M.Name, +by: Nat) -> {M.standing(M.mark(xs, tg, by)) == cut(M.standing(xs), tg) : List<&2, M.Node>}:
  match xs:
    case Nil{}:
      {==}
    case M.Node{+nm, +it, +pl, +d} <> +rest:
      std_mark.at(nm, it, pl, d, rest, tg, by, M.Name.eq(nm, tg), {==}, standing_mark(rest, tg, by))

def order_mark(+t: List<&2, M.Node>, +tg: M.Name, +by: Nat) -> {M.order(M.mark(t, tg, by)) == M.mark(M.order(t), tg, by) : List<&2, M.Node>}:
  %AL.length_mark(t, tg, by) : {M.read_all(1n+_, M.mark(t, tg, by), M.children(M.mark(t, tg, by), None{}, True{})) == M.mark(M.order(t), tg, by) : List<&2, M.Node>}
  %AL.children_mark(t, tg, by, None{}, True{}) : {M.read_all(1n+List.length(&2, M.Node, t), M.mark(t, tg, by), _) == M.mark(M.order(t), tg, by) : List<&2, M.Node>}
  %AL.read_mark(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}), tg, by) : {_ == M.mark(M.order(t), tg, by) : List<&2, M.Node>}
  {==}

def visible_mark(+t: List<&2, M.Node>, +tg: M.Name, +by: Nat) -> {M.visible(M.mark(t, tg, by)) == cut(M.visible(t), tg) : List<&2, M.Node>}:
  Equal.trans(List<&2, M.Node>, M.standing(M.order(M.mark(t, tg, by))), M.standing(M.mark(M.order(t), tg, by)), cut(M.visible(t), tg),
    Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => M.standing(l), M.order(M.mark(t, tg, by)), M.mark(M.order(t), tg, by), order_mark(t, tg, by)),
    standing_mark(M.order(t), tg, by))

# The marks of an event read as its removals.
def visible_mk(acts: List<&2, M.Action>, +t: List<&2, M.Node>, +by: Nat) -> {M.visible(mk(acts, t, by)) == cuts(acts, M.visible(t)) : List<&2, M.Node>}:
  match acts:
    case Nil{}:
      {==}
    case M.Attach{m, it, pl} <> rest:
      visible_mk(rest, t, by)
    case M.Delete{+tg} <> +rest:
      Equal.trans(List<&2, M.Node>, M.visible(mk(rest, M.mark(t, tg, by), by)), cuts(rest, M.visible(M.mark(t, tg, by))), cuts(rest, cut(M.visible(t), tg)),
        visible_mk(rest, M.mark(t, tg, by), by),
        Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => cuts(rest, l), M.visible(M.mark(t, tg, by)), cut(M.visible(t), tg), visible_mark(t, tg, by)))

# Lists
# -----

def nappend_assoc(xs: List<&2, M.Node>, -ys: List<&2, M.Node>, -zs: List<&2, M.Node>) -> {List.append(&2, M.Node, List.append(&2, M.Node, xs, ys), zs) == List.append(&2, M.Node, xs, List.append(&2, M.Node, ys, zs)) : List<&2, M.Node>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => h <> l, List.append(&2, M.Node, List.append(&2, M.Node, t, ys), zs), List.append(&2, M.Node, t, List.append(&2, M.Node, ys, zs)), nappend_assoc(t, ys, zs))

def take_drop(xs: List<&2, M.Node>, n: Nat) -> {List.append(&2, M.Node, List.take(&2, M.Node, xs, n), List.drop(&2, M.Node, xs, n)) == xs : List<&2, M.Node>}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case h <> t 0n:
      {==}
    case +h <> t 1n+p:
      Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => h <> l, List.append(&2, M.Node, List.take(&2, M.Node, t, p), List.drop(&2, M.Node, t, p)), t, take_drop(t, p))

def ndrop_drop(n: Nat, xs: List<&2, M.Node>, m: Nat) -> {List.drop(&2, M.Node, List.drop(&2, M.Node, xs, n), m) == List.drop(&2, M.Node, xs, Nat.add(n, m)) : List<&2, M.Node>}:
  match n xs:
    case 0n Nil{}:
      {==}
    case 0n h <> t:
      {==}
    case 1n+p Nil{}:
      match m:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p h <> t:
      ndrop_drop(p, t, m)

# The parent from `c`: what lies before `a`, then the parent from `a`.
def drop_split(+xs: List<&2, M.Node>, +c: Nat, +a: Nat, le: {Nat.is_le(c, a) == True{} : Bool}) -> {List.drop(&2, M.Node, xs, c) == List.append(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, xs, c), Nat.sub(a, c)), List.drop(&2, M.Node, xs, a)) : List<&2, M.Node>}:
  %Comp.add_sub(c, a, le) : {List.drop(&2, M.Node, xs, c) == List.append(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, xs, c), Nat.sub(a, c)), List.drop(&2, M.Node, xs, _)) : List<&2, M.Node>}
  %ndrop_drop(c, xs, Nat.sub(a, c)) : {List.drop(&2, M.Node, xs, c) == List.append(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, xs, c), Nat.sub(a, c)), _) : List<&2, M.Node>}
  Equal.sym(List<&2, M.Node>, List.append(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, xs, c), Nat.sub(a, c)), List.drop(&2, M.Node, List.drop(&2, M.Node, xs, c), Nat.sub(a, c))), List.drop(&2, M.Node, xs, c), take_drop(List.drop(&2, M.Node, xs, c), Nat.sub(a, c)))

def len_append(xs: List<&2, M.Node>, -ys: List<&2, M.Node>) -> {List.length(&2, M.Node, List.append(&2, M.Node, xs, ys)) == Nat.add(List.length(&2, M.Node, xs), List.length(&2, M.Node, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      Equal.cong(Nat, Nat, l => 1n+l, List.length(&2, M.Node, List.append(&2, M.Node, t, ys)), Nat.add(List.length(&2, M.Node, t), List.length(&2, M.Node, ys)), len_append(t, ys))

def len_take(xs: List<&2, M.Node>, g: Nat, e: {Nat.is_le(g, List.length(&2, M.Node, xs)) == True{} : Bool}) -> {List.length(&2, M.Node, List.take(&2, M.Node, xs, g)) == g : Nat}:
  match xs g:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      Empty.absurd({0n == 1n+p : Nat}, Comp.false_true(e))
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      Equal.cong(Nat, Nat, l => 1n+l, List.length(&2, M.Node, List.take(&2, M.Node, t, p)), p, len_take(t, p, e))

def gap_fits(gap: Nat, pos: Nat, xs: List<&2, M.Node>, e: {Nat.is_le(Nat.add(pos, gap), List.length(&2, M.Node, xs)) == True{} : Bool}) -> {Nat.is_le(gap, List.length(&2, M.Node, List.drop(&2, M.Node, xs, pos))) == True{} : Bool}:
  match pos xs:
    case 0n Nil{}:
      e
    case 0n h <> t:
      e
    case 1n+p Nil{}:
      Empty.absurd({Nat.is_le(gap, 0n) == True{} : Bool}, Comp.false_true(e))
    case 1n+p h <> t:
      gap_fits(gap, p, t, e)

def get_append_right(xs: List<&2, M.Node>, -ys: List<&2, M.Node>, -i: Nat) -> {List.get(&2, M.Node, List.append(&2, M.Node, xs, ys), Nat.add(List.length(&2, M.Node, xs), i)) == List.get(&2, M.Node, ys, i) : Maybe<&2, M.Node>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      get_append_right(t, ys, i)

def get_take(xs: List<&2, M.Node>, n: Nat, i: Nat, l: {Nat.is_lt(i, n) == True{} : Bool}) -> {List.get(&2, M.Node, List.take(&2, M.Node, xs, n), i) == List.get(&2, M.Node, xs, i) : Maybe<&2, M.Node>}:
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      Empty.absurd({List.get(&2, M.Node, Nil{}, i) == List.get(&2, M.Node, h <> t, i) : Maybe<&2, M.Node>}, ML.lt_zero(i, l))
    case h <> t 1n+p:
      match i:
        case 0n:
          {==}
        case 1n+q:
          get_take(t, p, q, l)

def get_drop(xs: List<&2, M.Node>, a: Nat, -i: Nat) -> {List.get(&2, M.Node, List.drop(&2, M.Node, xs, a), i) == List.get(&2, M.Node, xs, Nat.add(a, i)) : Maybe<&2, M.Node>}:
  match xs a:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      get_drop(t, p, i)

# The element before the end of a run cut from the parent is the parent's
# element before where the run ends.
def last_of(+ys: List<&2, M.Node>, +xs: List<&2, M.Node>, +a: Nat, +g: Nat, r: {Nat.is_le(Nat.add(a, 1n+g), List.length(&2, M.Node, xs)) == True{} : Bool}) -> {M.left_of(List.append(&2, M.Node, ys, List.take(&2, M.Node, List.drop(&2, M.Node, xs, a), 1n+g)), List.length(&2, M.Node, List.append(&2, M.Node, ys, List.take(&2, M.Node, List.drop(&2, M.Node, xs, a), 1n+g)))) == M.left_of(xs, Nat.add(a, 1n+g)) : Maybe<&2, Maybe<&2, M.Name>>}:
  %Equal.sym(Nat, List.length(&2, M.Node, List.append(&2, M.Node, ys, List.take(&2, M.Node, List.drop(&2, M.Node, xs, a), 1n+g))), Nat.add(List.length(&2, M.Node, ys), List.length(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, xs, a), 1n+g))), len_append(ys, List.take(&2, M.Node, List.drop(&2, M.Node, xs, a), 1n+g))) : {M.left_of(List.append(&2, M.Node, ys, List.take(&2, M.Node, List.drop(&2, M.Node, xs, a), 1n+g)), _) == M.left_of(xs, Nat.add(a, 1n+g)) : Maybe<&2, Maybe<&2, M.Name>>}
  %Equal.sym(Nat, List.length(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, xs, a), 1n+g)), 1n+g, len_take(List.drop(&2, M.Node, xs, a), 1n+g, gap_fits(1n+g, a, xs, r))) : {M.left_of(List.append(&2, M.Node, ys, List.take(&2, M.Node, List.drop(&2, M.Node, xs, a), 1n+g)), Nat.add(List.length(&2, M.Node, ys), _)) == M.left_of(xs, Nat.add(a, 1n+g)) : Maybe<&2, Maybe<&2, M.Name>>}
  %Equal.sym(Nat, Nat.add(List.length(&2, M.Node, ys), 1n+g), 1n+Nat.add(List.length(&2, M.Node, ys), g), Pos.add_succ(List.length(&2, M.Node, ys), g)) : {M.left_of(List.append(&2, M.Node, ys, List.take(&2, M.Node, List.drop(&2, M.Node, xs, a), 1n+g)), _) == M.left_of(xs, Nat.add(a, 1n+g)) : Maybe<&2, Maybe<&2, M.Name>>}
  %Equal.sym(Nat, Nat.add(a, 1n+g), 1n+Nat.add(a, g), Pos.add_succ(a, g)) : {M.left_of(List.append(&2, M.Node, ys, List.take(&2, M.Node, List.drop(&2, M.Node, xs, a), 1n+g)), 1n+Nat.add(List.length(&2, M.Node, ys), g)) == M.left_of(xs, _) : Maybe<&2, Maybe<&2, M.Name>>}
  Equal.cong(Maybe<&2, M.Node>, Maybe<&2, Maybe<&2, M.Name>>, mx => Maybe.map(&2, M.Node, Maybe<&2, M.Name>, x => Some{M.Node.name(x)}, mx),
    List.get(&2, M.Node, List.append(&2, M.Node, ys, List.take(&2, M.Node, List.drop(&2, M.Node, xs, a), 1n+g)), Nat.add(List.length(&2, M.Node, ys), g)), List.get(&2, M.Node, xs, Nat.add(a, g)),
    Equal.trans(Maybe<&2, M.Node>, List.get(&2, M.Node, List.append(&2, M.Node, ys, List.take(&2, M.Node, List.drop(&2, M.Node, xs, a), 1n+g)), Nat.add(List.length(&2, M.Node, ys), g)), List.get(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, xs, a), 1n+g), g), List.get(&2, M.Node, xs, Nat.add(a, g)),
      get_append_right(ys, List.take(&2, M.Node, List.drop(&2, M.Node, xs, a), 1n+g), g),
      Equal.trans(Maybe<&2, M.Node>, List.get(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, xs, a), 1n+g), g), List.get(&2, M.Node, List.drop(&2, M.Node, xs, a), g), List.get(&2, M.Node, xs, Nat.add(a, g)),
        get_take(List.drop(&2, M.Node, xs, a), 1n+g, g, Comp.lt_succ_self(g)),
        get_drop(xs, a, g))))

# Items
# -----

def file_append(xs: List<&2, M.Node>, -ys: List<&2, M.Node>) -> {M.file.of(List.append(&2, M.Node, xs, ys)) == List.append(&2, Ops.Item, M.file.of(xs), M.file.of(ys)) : List<&2, Ops.Item>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => M.Node.item(h) <> l, M.file.of(List.append(&2, M.Node, t, ys)), List.append(&2, Ops.Item, M.file.of(t), M.file.of(ys)), file_append(t, ys))

def file_drop(xs: List<&2, M.Node>, n: Nat) -> {M.file.of(List.drop(&2, M.Node, xs, n)) == List.drop(&2, Ops.Item, M.file.of(xs), n) : List<&2, Ops.Item>}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      file_drop(t, p)

def file_take(xs: List<&2, M.Node>, n: Nat) -> {M.file.of(List.take(&2, M.Node, xs, n)) == List.take(&2, Ops.Item, M.file.of(xs), n) : List<&2, Ops.Item>}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case h <> t 0n:
      {==}
    case +h <> t 1n+p:
      Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => M.Node.item(h) <> l, M.file.of(List.take(&2, M.Node, t, p)), List.take(&2, Ops.Item, M.file.of(t), p), file_take(t, p))

def len_file(xs: List<&2, M.Node>) -> {List.length(&2, Ops.Item, M.file.of(xs)) == List.length(&2, M.Node, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      Equal.cong(Nat, Nat, l => 1n+l, List.length(&2, Ops.Item, M.file.of(t)), List.length(&2, M.Node, t), len_file(t))

def max_le(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.max(a, b) == b : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, Comp.false_true(e))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, l => 1n+l, Nat.max(p, q), q, max_le(p, q, e))

def sub_past(a: Nat, n: Nat) -> {Nat.sub(a, Nat.add(a, n)) == 0n : Nat}:
  match a:
    case 0n:
      match n:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      sub_past(p, n)

# A delete's run
# --------------
#
# A quote the parent holds from `a` on is a delete of the elements there.
def mt(f: Bool, g: Bool, -a: String, -b: String, h: {Spec.matches_text(a, f, b, g) == True{} : Bool}) -> {Bool.or(Bool.or(f, g), T.same(a, b)) == True{} : Bool}:
  match f g:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      h

def ma(n: Bool, m: Bool, -a: String, f: Bool, -b: String, g: Bool, h: {Spec.matches_shape(n, m, a, f, b, g) == True{} : Bool}) -> {Bool.and(Bool.not(Bool.xor(n, m)), Bool.or(Bool.or(f, g), T.same(a, b))) == True{} : Bool}:
  match n m:
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(h))
    case True{} False{}:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(h))
    case False{} False{}:
      mt(f, g, a, b, h)
    case True{} True{}:
      mt(f, g, a, b, h)

def matches_agrees(r: Ops.Item, x: Ops.Item, h: {Spec.matches(r, x) == True{} : Bool}) -> {Ops.agrees(r, x) == True{} : Bool}:
  match r x:
    case Ops.Item{a, n, f} Ops.Item{b, m, g}:
      ma(n, m, a, f, b, g, h)

def one_add(+a: Nat) -> {1n+a == Nat.add(a, 1n) : Nat}:
  Equal.sym(Nat, Nat.add(a, 1n), 1n+a, Equal.trans(Nat, Nat.add(a, 1n), 1n+Nat.add(a, 0n), 1n+a, Pos.add_succ(a, 0n), Equal.cong(Nat, Nat, l => 1n+l, Nat.add(a, 0n), a, Comp.add_zero(a))))

def get_at(+xs: List<&2, M.Node>, +a: Nat, +z: M.Node, +zs: List<&2, M.Node>, e: {List.drop(&2, M.Node, xs, a) == z <> zs : List<&2, M.Node>}) -> {List.get(&2, M.Node, xs, a) == Some{z} : Maybe<&2, M.Node>}:
  Equal.trans(Maybe<&2, M.Node>, List.get(&2, M.Node, xs, a), List.get(&2, M.Node, xs, Nat.add(a, 0n)), Some{z},
    Equal.cong(Nat, Maybe<&2, M.Node>, i => List.get(&2, M.Node, xs, i), a, Nat.add(a, 0n), Equal.sym(Nat, Nat.add(a, 0n), a, Comp.add_zero(a))),
    Equal.trans(Maybe<&2, M.Node>, List.get(&2, M.Node, xs, Nat.add(a, 0n)), List.get(&2, M.Node, List.drop(&2, M.Node, xs, a), 0n), Some{z},
      Equal.sym(Maybe<&2, M.Node>, List.get(&2, M.Node, List.drop(&2, M.Node, xs, a), 0n), List.get(&2, M.Node, xs, Nat.add(a, 0n)), get_drop(xs, a, 0n)),
      Equal.cong(List<&2, M.Node>, Maybe<&2, M.Node>, l => List.get(&2, M.Node, l, 0n), List.drop(&2, M.Node, xs, a), z <> zs, e)))

def drop_next(+xs: List<&2, M.Node>, +a: Nat, +z: M.Node, +zs: List<&2, M.Node>, e: {List.drop(&2, M.Node, xs, a) == z <> zs : List<&2, M.Node>}) -> {List.drop(&2, M.Node, xs, 1n+a) == zs : List<&2, M.Node>}:
  Equal.trans(List<&2, M.Node>, List.drop(&2, M.Node, xs, 1n+a), List.drop(&2, M.Node, xs, Nat.add(a, 1n)), zs,
    Equal.cong(Nat, List<&2, M.Node>, i => List.drop(&2, M.Node, xs, i), 1n+a, Nat.add(a, 1n), one_add(a)),
    Equal.trans(List<&2, M.Node>, List.drop(&2, M.Node, xs, Nat.add(a, 1n)), List.drop(&2, M.Node, List.drop(&2, M.Node, xs, a), 1n), zs,
      Equal.sym(List<&2, M.Node>, List.drop(&2, M.Node, List.drop(&2, M.Node, xs, a), 1n), List.drop(&2, M.Node, xs, Nat.add(a, 1n)), ndrop_drop(a, xs, 1n)),
      Equal.trans(List<&2, M.Node>, List.drop(&2, M.Node, List.drop(&2, M.Node, xs, a), 1n), List.drop(&2, M.Node, zs, 0n), zs,
        Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => List.drop(&2, M.Node, l, 1n), List.drop(&2, M.Node, xs, a), z <> zs, e),
        AL.drop_zero(zs))))

def deletes_of(items: List<&2, Ops.Item>, +xs: List<&2, M.Node>, +a: Nat, zs: List<&2, M.Node>, +e: {List.drop(&2, M.Node, xs, a) == zs : List<&2, M.Node>}, +pm: {Spec.prefix_matches(items, M.file.of(zs)) == True{} : Bool}) -> {M.deletes(items, xs, a) == Some{dels(List.take(&2, M.Node, zs, List.length(&2, Ops.Item, items)))} : Maybe<&2, List<&2, M.Action>>}:
  match items:
    case Nil{}:
      %Equal.sym(List<&2, M.Node>, List.take(&2, M.Node, zs, 0n), Nil{}, AL.take_zero(zs)) : {Some{Nil{}} == Some{dels(_)} : Maybe<&2, List<&2, M.Action>>}
      {==}
    case +it <> +more:
      match zs:
        case Nil{}:
          Empty.absurd({M.deletes(it <> more, xs, a) == Some{dels(Nil{})} : Maybe<&2, List<&2, M.Action>>}, Comp.false_true(pm))
        case M.Node{+nm, +itm, +pl, +d} <> +rest:
          %Equal.sym(Maybe<&2, M.Node>, List.get(&2, M.Node, xs, a), Some{M.Node{nm, itm, pl, d}}, get_at(xs, a, M.Node{nm, itm, pl, d}, rest, e)) : {M.deletes.at(it, M.deletes(more, xs, 1n+a), _) == Some{M.Delete{nm} <> dels(List.take(&2, M.Node, rest, List.length(&2, Ops.Item, more)))} : Maybe<&2, List<&2, M.Action>>}
          %Equal.sym(Maybe<&2, List<&2, M.Action>>, M.deletes(more, xs, 1n+a), Some{dels(List.take(&2, M.Node, rest, List.length(&2, Ops.Item, more)))}, deletes_of(more, xs, 1n+a, rest, drop_next(xs, a, M.Node{nm, itm, pl, d}, rest, e), Comp.and_right(Spec.matches(it, itm), Spec.prefix_matches(more, M.file.of(rest)), pm))) : {M.deletes.at(it, _, Some{M.Node{nm, itm, pl, d}}) == Some{M.Delete{nm} <> dels(List.take(&2, M.Node, rest, List.length(&2, Ops.Item, more)))} : Maybe<&2, List<&2, M.Action>>}
          %Equal.sym(Bool, Ops.agrees(it, itm), True{}, matches_agrees(it, itm, Comp.and_left(Spec.matches(it, itm), Spec.prefix_matches(more, M.file.of(rest)), pm))) : {M.deletes.agreed(nm, Some{dels(List.take(&2, M.Node, rest, List.length(&2, Ops.Item, more)))}, _) == Some{M.Delete{nm} <> dels(List.take(&2, M.Node, rest, List.length(&2, Ops.Item, more)))} : Maybe<&2, List<&2, M.Action>>}
          {==}

# An insert's run
# ---------------
def iv(r: M.Inserted) -> List<&2, M.Node>:
  match r:
    case M.Inserted{v, acts, m}:
      v

def im(r: M.Inserted) -> Nat:
  match r:
    case M.Inserted{v, acts, m}:
      m

def iv_of(-minted: Nat, -it: Ops.Item, -place: M.Place, r: M.Inserted) -> {iv(M.inserts.of(minted, it, place, r)) == iv(r) : List<&2, M.Node>}:
  match r:
    case M.Inserted{v, acts, m}:
      {==}

def im_of(-minted: Nat, -it: Ops.Item, -place: M.Place, r: M.Inserted) -> {im(M.inserts.of(minted, it, place, r)) == im(r) : Nat}:
  match r:
    case M.Inserted{v, acts, m}:
      {==}

def ia_of(-minted: Nat, -it: Ops.Item, -place: M.Place, r: M.Inserted) -> {ML.Inserted.acts(M.inserts.of(minted, it, place, r)) == M.Attach{minted, it, place} <> ML.Inserted.acts(r) : List<&2, M.Action>}:
  match r:
    case M.Inserted{v, acts, m}:
      {==}

def run_inserted(-acts: List<&2, M.Action>, r: M.Inserted) -> {M.run.inserted(acts, r) == Some{M.Running{iv(r), im(r), List.append(&2, M.Action, acts, ML.Inserted.acts(r))}} : Maybe<&2, M.Running>}:
  match r:
    case M.Inserted{v, a, m}:
      {==}

# The elements a run mints, as `inserts` places them.
def fresh_nodes(items: List<&2, Ops.Item>, +v: List<&2, M.Node>, +k: Nat, +left: Maybe<&2, M.Name>, +m: Nat) -> List<&2, M.Node>:
  match items:
    case Nil{}:
      Nil{}
    case +it <> more:
      +place = M.anchor(v, left)
      M.Node{M.Name{k, m}, it, place, Nil{}} <> fresh_nodes(more, M.attach(v, M.Node{M.Name{k, m}, it, place, Nil{}}), k, Some{M.Name{k, m}}, 1n+m)

def file_fresh(items: List<&2, Ops.Item>, +v: List<&2, M.Node>, +k: Nat, +left: Maybe<&2, M.Name>, +m: Nat) -> {M.file.of(fresh_nodes(items, v, k, left, m)) == items : List<&2, Ops.Item>}:
  match items:
    case Nil{}:
      {==}
    case +it <> +more:
      Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => it <> l, M.file.of(fresh_nodes(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m)), more, file_fresh(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m))

def im_ins(items: List<&2, Ops.Item>, +v: List<&2, M.Node>, +k: Nat, +left: Maybe<&2, M.Name>, +m: Nat) -> {im(M.inserts(items, v, k, left, m)) == Nat.add(List.length(&2, Ops.Item, items), m) : Nat}:
  match items:
    case Nil{}:
      {==}
    case +it <> +more:
      Equal.trans(Nat, im(M.inserts.of(m, it, M.anchor(v, left), M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m))), im(M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m)), 1n+Nat.add(List.length(&2, Ops.Item, more), m),
        im_of(m, it, M.anchor(v, left), M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m)),
        Equal.trans(Nat, im(M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m)), Nat.add(List.length(&2, Ops.Item, more), 1n+m), 1n+Nat.add(List.length(&2, Ops.Item, more), m),
          im_ins(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m),
          Pos.add_succ(List.length(&2, Ops.Item, more), m)))

def attaches(acts: List<&2, M.Action>) -> Bool:
  match acts:
    case Nil{}:
      True{}
    case M.Attach{m, it, pl} <> rest:
      attaches(rest)
    case M.Delete{tg} <> rest:
      False{}

def attaches_ins(items: List<&2, Ops.Item>, +v: List<&2, M.Node>, +k: Nat, +left: Maybe<&2, M.Name>, +m: Nat) -> {attaches(ML.Inserted.acts(M.inserts(items, v, k, left, m))) == True{} : Bool}:
  match items:
    case Nil{}:
      {==}
    case +it <> +more:
      %Equal.sym(List<&2, M.Action>, ML.Inserted.acts(M.inserts.of(m, it, M.anchor(v, left), M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m))), M.Attach{m, it, M.anchor(v, left)} <> ML.Inserted.acts(M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m)), ia_of(m, it, M.anchor(v, left), M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m))) : {attaches(_) == True{} : Bool}
      attaches_ins(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m)

# The view a run leaves is its attaches, applied.
def ins_apply(items: List<&2, Ops.Item>, +v: List<&2, M.Node>, +k: Nat, +left: Maybe<&2, M.Name>, +m: Nat) -> {iv(M.inserts(items, v, k, left, m)) == M.apply(ML.Inserted.acts(M.inserts(items, v, k, left, m)), v, k) : List<&2, M.Node>}:
  match items:
    case Nil{}:
      {==}
    case +it <> +more:
      %Equal.sym(List<&2, M.Action>, ML.Inserted.acts(M.inserts.of(m, it, M.anchor(v, left), M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m))), M.Attach{m, it, M.anchor(v, left)} <> ML.Inserted.acts(M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m)), ia_of(m, it, M.anchor(v, left), M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m))) : {iv(M.inserts.of(m, it, M.anchor(v, left), M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m))) == M.apply(_, v, k) : List<&2, M.Node>}
      %Equal.sym(List<&2, M.Node>, iv(M.inserts.of(m, it, M.anchor(v, left), M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m))), iv(M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m)), iv_of(m, it, M.anchor(v, left), M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m))) : {_ == M.apply(M.Attach{m, it, M.anchor(v, left)} <> ML.Inserted.acts(M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m)), v, k) : List<&2, M.Node>}
      ins_apply(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m)

# Actions
# -------

def apply_append(xs: List<&2, M.Action>, -ys: List<&2, M.Action>, t: List<&2, M.Node>, +by: Nat) -> {M.apply(List.append(&2, M.Action, xs, ys), t, by) == M.apply(ys, M.apply(xs, t, by), by) : List<&2, M.Node>}:
  match xs:
    case Nil{}:
      {==}
    case a <> rest:
      apply_append(rest, ys, M.one(t, by, a), by)

def mk_append(xs: List<&2, M.Action>, -ys: List<&2, M.Action>, t: List<&2, M.Node>, +by: Nat) -> {mk(List.append(&2, M.Action, xs, ys), t, by) == mk(ys, mk(xs, t, by), by) : List<&2, M.Node>}:
  match xs:
    case Nil{}:
      {==}
    case M.Attach{m, it, pl} <> rest:
      mk_append(rest, ys, t, by)
    case M.Delete{+tg} <> rest:
      mk_append(rest, ys, M.mark(t, tg, by), by)

def apply_dels(ds: List<&2, M.Node>, u: List<&2, M.Node>, +by: Nat) -> {M.apply(dels(ds), u, by) == mk(dels(ds), u, by) : List<&2, M.Node>}:
  match ds:
    case Nil{}:
      {==}
    case +x <> rest:
      apply_dels(rest, M.mark(u, M.Node.name(x), by), by)

def mk_attaches(acts: List<&2, M.Action>, u: List<&2, M.Node>, +by: Nat, h: {attaches(acts) == True{} : Bool}) -> {mk(acts, u, by) == u : List<&2, M.Node>}:
  match acts:
    case Nil{}:
      {==}
    case M.Attach{m, it, pl} <> rest:
      mk_attaches(rest, u, by, h)
    case M.Delete{tg} <> rest:
      Empty.absurd({mk(rest, M.mark(u, tg, by), by) == u : List<&2, M.Node>}, Comp.false_true(h))

def hit_attaches(acts: List<&2, M.Action>, +nm: M.Name, h: {attaches(acts) == True{} : Bool}) -> {hit(acts, nm) == False{} : Bool}:
  match acts:
    case Nil{}:
      {==}
    case M.Attach{m, it, pl} <> rest:
      hit_attaches(rest, nm, h)
    case M.Delete{tg} <> rest:
      Empty.absurd({Bool.or(M.Name.eq(nm, tg), hit(rest, nm)) == False{} : Bool}, Comp.false_true(h))

def clear_attaches(xs: List<&2, M.Node>, +acts: List<&2, M.Action>, +h: {attaches(acts) == True{} : Bool}) -> {clear(xs, acts) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      AL.and_intro(Bool.not(hit(acts, M.Node.name(x))), clear(rest, acts), AL.not_true(hit(acts, M.Node.name(x)), hit_attaches(acts, M.Node.name(x), h)), clear_attaches(rest, acts, h))

# An element an event writes is marked by none of its deletes.
def attach_mk(acts: List<&2, M.Action>, +u: List<&2, M.Node>, +k: Nat, +mm: Nat, +it: Ops.Item, +pl: M.Place, +h: {ML.avoid(acts, k) == True{} : Bool}) -> {M.attach(mk(acts, u, k), M.Node{M.Name{k, mm}, it, pl, Nil{}}) == mk(acts, M.attach(u, M.Node{M.Name{k, mm}, it, pl, Nil{}}), k) : List<&2, M.Node>}:
  match acts:
    case Nil{}:
      {==}
    case M.Attach{m, i, p} <> rest:
      attach_mk(rest, u, k, mm, it, pl, h)
    case M.Delete{M.Name{+a, +m2}} <> rest:
      Equal.trans(List<&2, M.Node>, M.attach(mk(rest, M.mark(u, M.Name{a, m2}, k), k), M.Node{M.Name{k, mm}, it, pl, Nil{}}), mk(rest, M.attach(M.mark(u, M.Name{a, m2}, k), M.Node{M.Name{k, mm}, it, pl, Nil{}}), k), mk(rest, M.mark(M.attach(u, M.Node{M.Name{k, mm}, it, pl, Nil{}}), M.Name{a, m2}, k), k),
        attach_mk(rest, M.mark(u, M.Name{a, m2}, k), k, mm, it, pl, Comp.and_right(Bool.not(Nat.is_eq(k, a)), ML.avoid(rest, k), h)),
        Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => mk(rest, l, k), M.attach(M.mark(u, M.Name{a, m2}, k), M.Node{M.Name{k, mm}, it, pl, Nil{}}), M.mark(M.attach(u, M.Node{M.Name{k, mm}, it, pl, Nil{}}), M.Name{a, m2}, k),
          Equal.sym(List<&2, M.Node>, M.mark(M.attach(u, M.Node{M.Name{k, mm}, it, pl, Nil{}}), M.Name{a, m2}, k), M.attach(M.mark(u, M.Name{a, m2}, k), M.Node{M.Name{k, mm}, it, pl, Nil{}}),
            ML.attach_mark(u, M.Node{M.Name{k, mm}, it, pl, Nil{}}, M.Name{a, m2}, k, ML.unmarked(k, mm, it, pl, Nil{}, a, m2, k, AL.not_of_true(Nat.is_eq(k, a), Comp.and_left(Bool.not(Nat.is_eq(k, a)), ML.avoid(rest, k), h)))))))

def apply_attaches_mk(ia: List<&2, M.Action>, +acts: List<&2, M.Action>, +v: List<&2, M.Node>, +k: Nat, +ha: {ML.avoid(acts, k) == True{} : Bool}, h: {attaches(ia) == True{} : Bool}) -> {M.apply(ia, mk(acts, v, k), k) == mk(acts, M.apply(ia, v, k), k) : List<&2, M.Node>}:
  match ia:
    case Nil{}:
      {==}
    case M.Attach{+m, +it, +pl} <> rest:
      Equal.trans(List<&2, M.Node>, M.apply(rest, M.attach(mk(acts, v, k), M.Node{M.Name{k, m}, it, pl, Nil{}}), k), M.apply(rest, mk(acts, M.attach(v, M.Node{M.Name{k, m}, it, pl, Nil{}}), k), k), mk(acts, M.apply(rest, M.attach(v, M.Node{M.Name{k, m}, it, pl, Nil{}}), k), k),
        Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => M.apply(rest, l, k), M.attach(mk(acts, v, k), M.Node{M.Name{k, m}, it, pl, Nil{}}), mk(acts, M.attach(v, M.Node{M.Name{k, m}, it, pl, Nil{}}), k), attach_mk(acts, v, k, m, it, pl, ha)),
        apply_attaches_mk(rest, acts, M.attach(v, M.Node{M.Name{k, m}, it, pl, Nil{}}), k, ha, h))
    case M.Delete{tg} <> rest:
      Empty.absurd({M.apply(rest, M.mark(mk(acts, v, k), tg, k), k) == mk(acts, M.apply(rest, M.mark(v, tg, k), k), k) : List<&2, M.Node>}, Comp.false_true(h))

# Where a run lands
# -----------------

def take_app(xs: List<&2, M.Node>, +ys: List<&2, M.Node>) -> {List.take(&2, M.Node, List.append(&2, M.Node, xs, ys), List.length(&2, M.Node, xs)) == xs : List<&2, M.Node>}:
  match xs:
    case Nil{}:
      AL.take_zero(ys)
    case +h <> t:
      Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => h <> l, List.take(&2, M.Node, List.append(&2, M.Node, t, ys), List.length(&2, M.Node, t)), t, take_app(t, ys))

def drop_app(xs: List<&2, M.Node>, +ys: List<&2, M.Node>) -> {List.drop(&2, M.Node, List.append(&2, M.Node, xs, ys), List.length(&2, M.Node, xs)) == ys : List<&2, M.Node>}:
  match xs:
    case Nil{}:
      AL.drop_zero(ys)
    case h <> t:
      drop_app(t, ys)

def get_append_left(xs: List<&2, M.Node>, -ys: List<&2, M.Node>, i: Nat, l: {Nat.is_lt(i, List.length(&2, M.Node, xs)) == True{} : Bool}) -> {List.get(&2, M.Node, List.append(&2, M.Node, xs, ys), i) == List.get(&2, M.Node, xs, i) : Maybe<&2, M.Node>}:
  match xs i:
    case Nil{} _:
      Empty.absurd({List.get(&2, M.Node, ys, i) == None{} : Maybe<&2, M.Node>}, ML.lt_zero(i, l))
    case h <> t 0n:
      {==}
    case h <> t 1n+q:
      get_append_left(t, ys, q, l)

def left_append(xs: List<&2, M.Node>, +ys: List<&2, M.Node>) -> {M.left_of(List.append(&2, M.Node, xs, ys), List.length(&2, M.Node, xs)) == M.left_of(xs, List.length(&2, M.Node, xs)) : Maybe<&2, Maybe<&2, M.Name>>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      Equal.cong(Maybe<&2, M.Node>, Maybe<&2, Maybe<&2, M.Name>>, mx => Maybe.map(&2, M.Node, Maybe<&2, M.Name>, x => Some{M.Node.name(x)}, mx), List.get(&2, M.Node, h <> List.append(&2, M.Node, t, ys), List.length(&2, M.Node, t)), List.get(&2, M.Node, h <> t, List.length(&2, M.Node, t)),
        get_append_left(h <> t, ys, List.length(&2, M.Node, t), Comp.lt_succ_self(List.length(&2, M.Node, t))))

def left_snoc(+xs: List<&2, M.Node>, +n: M.Node) -> {M.left_of(List.append(&2, M.Node, xs, [n]), List.length(&2, M.Node, List.append(&2, M.Node, xs, [n]))) == Some{Some{M.Node.name(n)}} : Maybe<&2, Maybe<&2, M.Name>>}:
  %Equal.sym(Nat, List.length(&2, M.Node, List.append(&2, M.Node, xs, [n])), Nat.add(List.length(&2, M.Node, xs), 1n), len_append(xs, [n])) : {M.left_of(List.append(&2, M.Node, xs, [n]), _) == Some{Some{M.Node.name(n)}} : Maybe<&2, Maybe<&2, M.Name>>}
  %Equal.sym(Nat, Nat.add(List.length(&2, M.Node, xs), 1n), 1n+Nat.add(List.length(&2, M.Node, xs), 0n), Pos.add_succ(List.length(&2, M.Node, xs), 0n)) : {M.left_of(List.append(&2, M.Node, xs, [n]), _) == Some{Some{M.Node.name(n)}} : Maybe<&2, Maybe<&2, M.Name>>}
  Equal.cong(Maybe<&2, M.Node>, Maybe<&2, Maybe<&2, M.Name>>, mx => Maybe.map(&2, M.Node, Maybe<&2, M.Name>, x => Some{M.Node.name(x)}, mx), List.get(&2, M.Node, List.append(&2, M.Node, xs, [n]), Nat.add(List.length(&2, M.Node, xs), 0n)), Some{n}, get_append_right(xs, [n], 0n))

def nmdisc(m: Maybe<&2, M.Name>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def name_or(m: Maybe<&2, M.Name>, d: M.Name) -> M.Name:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def some_name(+a: M.Name, -b: M.Name, e: {Some{a} == Some{b} : Maybe<&2, M.Name>}) -> {a == b : M.Name}:
  Equal.cong(Maybe<&2, M.Name>, M.Name, mx => name_or(mx, a), Some{a}, Some{b}, e)

def left_named.at(+xs: List<&2, M.Node>, +q: Nat, +nm: M.Name, mx: Maybe<&2, M.Node>, emx: {List.get(&2, M.Node, xs, q) == mx : Maybe<&2, M.Node>}, e: {Maybe.map(&2, M.Node, Maybe<&2, M.Name>, x => Some{M.Node.name(x)}, mx) == Some{Some{nm}} : Maybe<&2, Maybe<&2, M.Name>>}) -> {M.named(xs, nm) == True{} : Bool}:
  match mx:
    case None{}:
      Empty.absurd({M.named(xs, nm) == True{} : Bool}, AL.none_some_left(Some{nm}, e))
    case Some{+x}:
      %some_name(M.Node.name(x), nm, AL.some_left(Some{M.Node.name(x)}, Some{nm}, e)) : {M.named(xs, _) == True{} : Bool}
      AL.get_named(xs, q, x, emx)

# A left neighbour the view reads is an element it holds.
def left_named(+xs: List<&2, M.Node>, p: Nat, +nm: M.Name, e: {M.left_of(xs, p) == Some{Some{nm}} : Maybe<&2, Maybe<&2, M.Name>>}) -> {M.named(xs, nm) == True{} : Bool}:
  match p:
    case 0n:
      Empty.absurd({M.named(xs, nm) == True{} : Bool}, (%AL.some_left(None{}, Some{nm}, e) : {nmdisc(_) : Type}
        Unit{}))
    case 1n++q:
      left_named.at(xs, q, nm, List.get(&2, M.Node, xs, q), {==}, e)

def in_view_of(+v: List<&2, M.Node>, +xs: List<&2, M.Node>, +ys: List<&2, M.Node>, left: Maybe<&2, M.Name>, hq: {M.visible(v) == List.append(&2, M.Node, xs, ys) : List<&2, M.Node>}, hl: {M.left_of(xs, List.length(&2, M.Node, xs)) == Some{left} : Maybe<&2, Maybe<&2, M.Name>>}) -> {M.in_view(v, left) == True{} : Bool}:
  match left:
    case None{}:
      {==}
    case Some{+nm}:
      %Equal.sym(List<&2, M.Node>, M.visible(v), List.append(&2, M.Node, xs, ys), hq) : {M.named(_, nm) == True{} : Bool}
      %Equal.sym(Bool, M.named(List.append(&2, M.Node, xs, ys), nm), Bool.or(M.named(xs, nm), M.named(ys, nm)), AL.named_append(xs, ys, nm)) : {_ == True{} : Bool}
      AL.or_left(M.named(xs, nm), M.named(ys, nm), left_named(xs, List.length(&2, M.Node, xs), nm, hl))

def before_self(+W: List<&2, Nat>, +k: Nat, +m: Nat) -> {before(M.Name{k, m}, W, k, 1n+m) == True{} : Bool}:
  AL.or_right(Bool.and(Bool.not(Nat.is_eq(k, k)), M.has(W, k)), Bool.and(Nat.is_eq(k, k), Nat.is_lt(m, 1n+m)), AL.and_intro(Nat.is_eq(k, k), Nat.is_lt(m, 1n+m), Comp.eq_refl(k), Comp.lt_succ_self(m)))

# The element a run mints is bounded once it is counted.
def good_new(+v: List<&2, M.Node>, +left: Maybe<&2, M.Name>, +it: Ops.Item, +W: List<&2, Nat>, +k: Nat, +m: Nat, +hi: {M.invariant(v) == True{} : Bool}, +lo: {M.in_view(v, left) == True{} : Bool}, +hg: {goods(v, W, k, m) == True{} : Bool}) -> {good(M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}, W, k, 1n+m) == True{} : Bool}:
  AL.anchor_cases({good(M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}, W, k, 1n+m) == True{} : Bool}, v, left, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}, hi, lo,
    eN => eR => eA => (%Equal.sym(M.Place, M.anchor(v, left), M.Place{None{}, True{}}, eA) : {good(M.Node{M.Name{k, m}, it, _, Nil{}}, W, k, 1n+m) == True{} : Bool}
      AL.and_intro(before(M.Name{k, m}, W, k, 1n+m), True{}, before_self(W, k, m), {==})),
    +par => right => eA => e => pn => eq => (%Equal.sym(M.Place, M.anchor(v, left), M.Place{Some{par}, right}, eA) : {good(M.Node{M.Name{k, m}, it, _, Nil{}}, W, k, 1n+m) == True{} : Bool}
      AL.and_intro(before(M.Name{k, m}, W, k, 1n+m), Bool.and(before(par, W, k, 1n+m), True{}), before_self(W, k, m),
        AL.and_intro(before(par, W, k, 1n+m), True{}, before_mono(par, W, k, m, named_before(v, par, W, k, m, hg, pn)), {==}))))

def lo_of(+v: List<&2, M.Node>, +xs: List<&2, M.Node>, +ys: List<&2, M.Node>, -left: Maybe<&2, M.Name>, hq: {M.visible(v) == List.append(&2, M.Node, xs, ys) : List<&2, M.Node>}, hl: {M.left_of(xs, List.length(&2, M.Node, xs)) == Some{left} : Maybe<&2, Maybe<&2, M.Name>>}) -> {M.left_of(M.visible(v), List.length(&2, M.Node, xs)) == Some{left} : Maybe<&2, Maybe<&2, M.Name>>}:
  Equal.trans(Maybe<&2, Maybe<&2, M.Name>>, M.left_of(M.visible(v), List.length(&2, M.Node, xs)), M.left_of(List.append(&2, M.Node, xs, ys), List.length(&2, M.Node, xs)), Some{left},
    Equal.cong(List<&2, M.Node>, Maybe<&2, Maybe<&2, M.Name>>, l => M.left_of(l, List.length(&2, M.Node, xs)), M.visible(v), List.append(&2, M.Node, xs, ys), hq),
    Equal.trans(Maybe<&2, Maybe<&2, M.Name>>, M.left_of(List.append(&2, M.Node, xs, ys), List.length(&2, M.Node, xs)), M.left_of(xs, List.length(&2, M.Node, xs)), Some{left}, left_append(xs, ys), hl))

# One element of a run: the view keeps its invariant and bound, and reads
# the element right after the gap.
def ins_inv(+v: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +m: Nat, +it: Ops.Item, +left: Maybe<&2, M.Name>, +xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +hi: {M.invariant(v) == True{} : Bool}, +hg: {goods(v, W, k, m) == True{} : Bool}, +hq: {M.visible(v) == List.append(&2, M.Node, xs, ys) : List<&2, M.Node>}, +hl: {M.left_of(xs, List.length(&2, M.Node, xs)) == Some{left} : Maybe<&2, Maybe<&2, M.Name>>}) -> {M.invariant(M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}})) == True{} : Bool}:
  AL.invariant_attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}, left, hi, fresh_of(v, W, k, m, hg), {==}, in_view_of(v, xs, ys, left, hq, hl))

def ins_goods(+v: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +m: Nat, +it: Ops.Item, +left: Maybe<&2, M.Name>, +xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +hi: {M.invariant(v) == True{} : Bool}, +hg: {goods(v, W, k, m) == True{} : Bool}, +hq: {M.visible(v) == List.append(&2, M.Node, xs, ys) : List<&2, M.Node>}, +hl: {M.left_of(xs, List.length(&2, M.Node, xs)) == Some{left} : Maybe<&2, Maybe<&2, M.Name>>}) -> {goods(M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), W, k, 1n+m) == True{} : Bool}:
  goods_attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}, W, k, 1n+m, good_new(v, left, it, W, k, m, hi, in_view_of(v, xs, ys, left, hq, hl), hg), goods_mono(v, W, k, m, hg))

def ins_vis(+v: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +m: Nat, +it: Ops.Item, +left: Maybe<&2, M.Name>, +xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +hi: {M.invariant(v) == True{} : Bool}, +hg: {goods(v, W, k, m) == True{} : Bool}, +hq: {M.visible(v) == List.append(&2, M.Node, xs, ys) : List<&2, M.Node>}, +hl: {M.left_of(xs, List.length(&2, M.Node, xs)) == Some{left} : Maybe<&2, Maybe<&2, M.Name>>}) -> {M.visible(M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}})) == List.append(&2, M.Node, List.append(&2, M.Node, xs, [M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}]), ys) : List<&2, M.Node>}:
  Equal.trans(List<&2, M.Node>, M.visible(M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}})), List.append(&2, M.Node, List.take(&2, M.Node, M.visible(v), List.length(&2, M.Node, xs)), M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}} <> List.drop(&2, M.Node, M.visible(v), List.length(&2, M.Node, xs))), List.append(&2, M.Node, List.append(&2, M.Node, xs, [M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}]), ys),
    AL.insert_at(v, List.length(&2, M.Node, xs), M.Name{k, m}, it, left, hi, fresh_of(v, W, k, m, hg), lo_of(v, xs, ys, left, hq, hl)),
    Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, List.take(&2, M.Node, M.visible(v), List.length(&2, M.Node, xs)), M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}} <> List.drop(&2, M.Node, M.visible(v), List.length(&2, M.Node, xs))), List.append(&2, M.Node, List.take(&2, M.Node, List.append(&2, M.Node, xs, ys), List.length(&2, M.Node, xs)), M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}} <> List.drop(&2, M.Node, List.append(&2, M.Node, xs, ys), List.length(&2, M.Node, xs))), List.append(&2, M.Node, List.append(&2, M.Node, xs, [M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}]), ys),
      Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => List.append(&2, M.Node, List.take(&2, M.Node, l, List.length(&2, M.Node, xs)), M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}} <> List.drop(&2, M.Node, l, List.length(&2, M.Node, xs))), M.visible(v), List.append(&2, M.Node, xs, ys), hq),
      (%Equal.sym(List<&2, M.Node>, List.take(&2, M.Node, List.append(&2, M.Node, xs, ys), List.length(&2, M.Node, xs)), xs, take_app(xs, ys)) : {List.append(&2, M.Node, _, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}} <> List.drop(&2, M.Node, List.append(&2, M.Node, xs, ys), List.length(&2, M.Node, xs))) == List.append(&2, M.Node, List.append(&2, M.Node, xs, [M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}]), ys) : List<&2, M.Node>}
        %Equal.sym(List<&2, M.Node>, List.drop(&2, M.Node, List.append(&2, M.Node, xs, ys), List.length(&2, M.Node, xs)), ys, drop_app(xs, ys)) : {List.append(&2, M.Node, xs, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}} <> _) == List.append(&2, M.Node, List.append(&2, M.Node, xs, [M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}]), ys) : List<&2, M.Node>}
        Equal.sym(List<&2, M.Node>, List.append(&2, M.Node, List.append(&2, M.Node, xs, [M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}]), ys), List.append(&2, M.Node, xs, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}} <> ys), nappend_assoc(xs, [M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}], ys)))))

# A whole run keeps the invariant and the bound, counted past its elements.
def ins_all(items: List<&2, Ops.Item>, +v: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +left: Maybe<&2, M.Name>, +m: Nat, +xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +hi: {M.invariant(v) == True{} : Bool}, +hg: {goods(v, W, k, m) == True{} : Bool}, +hq: {M.visible(v) == List.append(&2, M.Node, xs, ys) : List<&2, M.Node>}, +hl: {M.left_of(xs, List.length(&2, M.Node, xs)) == Some{left} : Maybe<&2, Maybe<&2, M.Name>>}) -> {Bool.and(M.invariant(iv(M.inserts(items, v, k, left, m))), goods(iv(M.inserts(items, v, k, left, m)), W, k, Nat.add(List.length(&2, Ops.Item, items), m))) == True{} : Bool}:
  match items:
    case Nil{}:
      AL.and_intro(M.invariant(v), goods(v, W, k, m), hi, hg)
    case +it <> +more:
      %Equal.sym(List<&2, M.Node>, iv(M.inserts.of(m, it, M.anchor(v, left), M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m))), iv(M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m)), iv_of(m, it, M.anchor(v, left), M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m))) : {Bool.and(M.invariant(_), goods(_, W, k, 1n+Nat.add(List.length(&2, Ops.Item, more), m))) == True{} : Bool}
      %Pos.add_succ(List.length(&2, Ops.Item, more), m) : {Bool.and(M.invariant(iv(M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m))), goods(iv(M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m)), W, k, _)) == True{} : Bool}
      ins_all(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), W, k, Some{M.Name{k, m}}, 1n+m, List.append(&2, M.Node, xs, [M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}]), ys,
        ins_inv(v, W, k, m, it, left, xs, ys, hi, hg, hq, hl),
        ins_goods(v, W, k, m, it, left, xs, ys, hi, hg, hq, hl),
        ins_vis(v, W, k, m, it, left, xs, ys, hi, hg, hq, hl),
        left_snoc(xs, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}))

# And reads its items right after the gap.
def ins_view(items: List<&2, Ops.Item>, +v: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +left: Maybe<&2, M.Name>, +m: Nat, +xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +hi: {M.invariant(v) == True{} : Bool}, +hg: {goods(v, W, k, m) == True{} : Bool}, +hq: {M.visible(v) == List.append(&2, M.Node, xs, ys) : List<&2, M.Node>}, +hl: {M.left_of(xs, List.length(&2, M.Node, xs)) == Some{left} : Maybe<&2, Maybe<&2, M.Name>>}) -> {M.visible(iv(M.inserts(items, v, k, left, m))) == List.append(&2, M.Node, xs, List.append(&2, M.Node, fresh_nodes(items, v, k, left, m), ys)) : List<&2, M.Node>}:
  match items:
    case Nil{}:
      hq
    case +it <> +more:
      Equal.trans(List<&2, M.Node>, M.visible(iv(M.inserts.of(m, it, M.anchor(v, left), M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m)))), M.visible(iv(M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m))), List.append(&2, M.Node, xs, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}} <> List.append(&2, M.Node, fresh_nodes(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m), ys)),
        Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => M.visible(l), iv(M.inserts.of(m, it, M.anchor(v, left), M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m))), iv(M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m)), iv_of(m, it, M.anchor(v, left), M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m))),
        Equal.trans(List<&2, M.Node>, M.visible(iv(M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m))), List.append(&2, M.Node, List.append(&2, M.Node, xs, [M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}]), List.append(&2, M.Node, fresh_nodes(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m), ys)), List.append(&2, M.Node, xs, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}} <> List.append(&2, M.Node, fresh_nodes(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m), ys)),
          ins_view(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), W, k, Some{M.Name{k, m}}, 1n+m, List.append(&2, M.Node, xs, [M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}]), ys,
            ins_inv(v, W, k, m, it, left, xs, ys, hi, hg, hq, hl),
            ins_goods(v, W, k, m, it, left, xs, ys, hi, hg, hq, hl),
            ins_vis(v, W, k, m, it, left, xs, ys, hi, hg, hq, hl),
            left_snoc(xs, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}})),
          nappend_assoc(xs, [M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}], List.append(&2, M.Node, fresh_nodes(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m), ys))))

# Numbers
# -------

def lt_le(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({True{} == True{} : Bool}, Comp.false_true(e))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(e))
    case 1n+p 1n+q:
      lt_le(p, q, e)

def le_lt_trans(a: Nat, b: Nat, c: Nat, e1: {Nat.is_le(a, b) == True{} : Bool}, e2: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n 0n:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(e2))
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(e2))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      Empty.absurd({Nat.is_lt(1n+p, c) == True{} : Bool}, Comp.false_true(e1))
    case 1n+p 1n+q 0n:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(e2))
    case 1n+p 1n+q 1n+r:
      le_lt_trans(p, q, r, e1, e2)

def lt_irrefl(a: Nat) -> {Nat.is_lt(a, a) == False{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      lt_irrefl(p)

def sub_zero(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def sub_self(a: Nat) -> {Nat.sub(a, a) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      sub_self(p)

def sub_pos(c: Nat, a: Nat, l: {Nat.is_lt(c, a) == True{} : Bool}) -> {Nat.sub(a, c) == 1n+Nat.sub(a, 1n+c) : Nat}:
  match c a:
    case 0n 0n:
      Empty.absurd({0n == 1n+0n : Nat}, Comp.false_true(l))
    case 0n 1n++ap:
      Equal.cong(Nat, Nat, x => 1n+x, ap, Nat.sub(ap, 0n), Equal.sym(Nat, Nat.sub(ap, 0n), ap, sub_zero(ap)))
    case 1n+cp 0n:
      Empty.absurd({0n == 1n+0n : Nat}, Comp.false_true(l))
    case 1n+cp 1n+ap:
      sub_pos(cp, ap, l)

def eq_of_le_nlt(c: Nat, a: Nat, le: {Nat.is_le(c, a) == True{} : Bool}, nl: {Nat.is_lt(c, a) == False{} : Bool}) -> {c == a : Nat}:
  match c a:
    case 0n 0n:
      {==}
    case 0n 1n+ap:
      Empty.absurd({0n == 1n+ap : Nat}, ML.true_false(nl))
    case 1n+cp 0n:
      Empty.absurd({1n+cp == 0n : Nat}, Comp.false_true(le))
    case 1n+cp 1n+ap:
      Equal.cong(Nat, Nat, x => 1n+x, cp, ap, eq_of_le_nlt(cp, ap, le, nl))

def max_ge(s: Nat, a: Nat, e: {Nat.is_le(a, s) == True{} : Bool}) -> {Nat.max(s, a) == s : Nat}:
  match s a:
    case 0n 0n:
      {==}
    case 0n 1n+ap:
      Empty.absurd({1n+ap == 0n : Nat}, Comp.false_true(e))
    case 1n+sp 0n:
      {==}
    case 1n+sp 1n+ap:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.max(sp, ap), sp, max_ge(sp, ap, e))

# The order the run needs
# -----------------------
#
# Each operation sits at or past where the one before left the cursor; an
# insert sits past it, unless nothing of the event's own has been written
# there (`open`); and a delete followed by an insert at its own position
# is one replacement. The parser's order admits no more than this.
def gap_ok(+c: Nat, +a: Nat, open: Bool) -> Bool:
  match open:
    case True{}:
      Nat.is_le(c, a)
    case False{}:
      Nat.is_lt(c, a)

def strict(ops: List<&2, Ops.Op>, +c: Nat, +open: Bool) -> Bool:
  match ops:
    case Nil{}:
      True{}
    case Ops.Op{Ops.Insert{}, +a, items} <> rest:
      Bool.and(gap_ok(c, a, open), strict(rest, a, False{}))
    case Ops.Op{Ops.Delete{}, +a, +items} <> rest:
      match rest:
        case Nil{}:
          Nat.is_le(c, a)
        case Ops.Op{Ops.Insert{}, +a2, +items2} <> +more:
          Bool.pick(Bool, Nat.is_eq(a2, a),
            Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))),
            Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))))
        case Ops.Op{Ops.Delete{}, +a2, +items2} <> +more:
          Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Delete{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)))

def gap_le(+c: Nat, +a: Nat, open: Bool, h: {gap_ok(c, a, open) == True{} : Bool}) -> {Nat.is_le(c, a) == True{} : Bool}:
  match open:
    case True{}:
      h
    case False{}:
      lt_le(c, a, h)

def gap_or(+c: Nat, +a: Nat, open: Bool, h: {gap_ok(c, a, open) == True{} : Bool}) -> {Bool.or(Nat.is_lt(c, a), open) == True{} : Bool}:
  match open:
    case True{}:
      AL.or_right(Nat.is_lt(c, a), True{}, {==})
    case False{}:
      AL.or_left(Nat.is_lt(c, a), False{}, h)

# What a finished event must leave
# --------------------------------

def xor_eq(n: Bool, m: Bool, e: {Bool.not(Bool.xor(n, m)) == True{} : Bool}) -> {n == m : Bool}:
  match n m:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, Comp.false_true(e))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(e))

def item_eq(a: Ops.Item, b: Ops.Item) -> Bool:
  match a b:
    case Ops.Item{x, n, f} Ops.Item{y, m, g}:
      Bool.and(String.eq(x, y), Bool.and(Bool.not(Bool.xor(n, m)), Bool.not(Bool.xor(f, g))))

def items_eq(a: List<&2, Ops.Item>, b: List<&2, Ops.Item>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case x <> xs y <> ys:
      Bool.and(item_eq(x, y), items_eq(xs, ys))
    case _ _:
      False{}

def item_eq_refl(x: Ops.Item) -> {item_eq(x, x) == True{} : Bool}:
  match x:
    case Ops.Item{+s, +n, +f}:
      AL.and_intro(String.eq(s, s), Bool.and(Bool.not(Bool.xor(n, n)), Bool.not(Bool.xor(f, f))), S.eq_refl(s), AL.and_intro(Bool.not(Bool.xor(n, n)), Bool.not(Bool.xor(f, f)), AL.xor_self(n), AL.xor_self(f)))

def items_eq_refl(xs: List<&2, Ops.Item>) -> {items_eq(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(item_eq(x, x), items_eq(rest, rest), item_eq_refl(x), items_eq_refl(rest))

def item_eq_equal(x: Ops.Item, y: Ops.Item, +h: {item_eq(x, y) == True{} : Bool}) -> {x == y : Ops.Item}:
  match x y:
    case Ops.Item{+s, +n, +f} Ops.Item{+t, +m, +g}:
      %S.eq_true(s, t, Comp.and_left(String.eq(s, t), Bool.and(Bool.not(Bool.xor(n, m)), Bool.not(Bool.xor(f, g))), h)) : {Ops.Item{s, n, f} == Ops.Item{_, m, g} : Ops.Item}
      %xor_eq(n, m, Comp.and_left(Bool.not(Bool.xor(n, m)), Bool.not(Bool.xor(f, g)), Comp.and_right(String.eq(s, t), Bool.and(Bool.not(Bool.xor(n, m)), Bool.not(Bool.xor(f, g))), h))) : {Ops.Item{s, n, f} == Ops.Item{s, _, g} : Ops.Item}
      %xor_eq(f, g, Comp.and_right(Bool.not(Bool.xor(n, m)), Bool.not(Bool.xor(f, g)), Comp.and_right(String.eq(s, t), Bool.and(Bool.not(Bool.xor(n, m)), Bool.not(Bool.xor(f, g))), h))) : {Ops.Item{s, n, f} == Ops.Item{s, n, _} : Ops.Item}
      {==}

def items_eq_equal(a: List<&2, Ops.Item>, b: List<&2, Ops.Item>, +h: {items_eq(a, b) == True{} : Bool}) -> {a == b : List<&2, Ops.Item>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case +x <> +xs +y <> +ys:
      Equal.trans(List<&2, Ops.Item>, x <> xs, y <> xs, y <> ys,
        Equal.cong(Ops.Item, List<&2, Ops.Item>, i => i <> xs, x, y, item_eq_equal(x, y, Comp.and_left(item_eq(x, y), items_eq(xs, ys), h))),
        Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => y <> l, xs, ys, items_eq_equal(xs, ys, Comp.and_right(item_eq(x, y), items_eq(xs, ys), h))))
    case Nil{} y <> ys:
      Empty.absurd({Nil{} == y <> ys : List<&2, Ops.Item>}, Comp.false_true(h))
    case x <> xs Nil{}:
      Empty.absurd({x <> xs == Nil{} : List<&2, Ops.Item>}, Comp.false_true(h))

def fine.of(+u: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +cf: List<&2, Ops.Item>) -> Bool:
  Bool.and(M.invariant(u), Bool.and(inw(u, k <> W), items_eq(M.file(u), cf)))

# What the event leaves — its actions, applied to the whole tree — keeps
# the invariant, is bounded by the event and those it had seen, and reads
# as `cf`.
def fine(st: Maybe<&2, M.Running>, +t: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +cf: List<&2, Ops.Item>) -> Bool:
  match st:
    case None{}:
      False{}
    case Some{M.Running{v, m, acts}}:
      fine.of(M.apply(acts, t, k), W, k, cf)

def inv_mk(acts: List<&2, M.Action>, +u: List<&2, M.Node>, +by: Nat, h: {M.invariant(u) == True{} : Bool}) -> {M.invariant(mk(acts, u, by)) == True{} : Bool}:
  match acts:
    case Nil{}:
      h
    case M.Attach{m, it, pl} <> rest:
      inv_mk(rest, u, by, h)
    case M.Delete{+tg} <> rest:
      inv_mk(rest, M.mark(u, tg, by), by, AL.invariant_mark(u, tg, by, h))

def goods_mk(acts: List<&2, M.Action>, +u: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +m: Nat, h: {goods(u, W, k, m) == True{} : Bool}) -> {goods(mk(acts, u, k), W, k, m) == True{} : Bool}:
  match acts:
    case Nil{}:
      h
    case M.Attach{a, it, pl} <> rest:
      goods_mk(rest, u, W, k, m, h)
    case M.Delete{+tg} <> rest:
      goods_mk(rest, M.mark(u, tg, k), W, k, m, goods_mark(u, tg, k, W, k, m, AL.or_left(Nat.is_eq(k, k), M.has(W, k), Comp.eq_refl(k)), h))

def fine_of(+v: List<&2, M.Node>, +m: Nat, +acts: List<&2, M.Action>, +t: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +cf: List<&2, Ops.Item>, h5: {M.apply(acts, t, k) == mk(acts, v, k) : List<&2, M.Node>}, hi: {M.invariant(v) == True{} : Bool}, hg: {goods(v, W, k, m) == True{} : Bool}, hf: {M.file.of(cuts(acts, M.visible(v))) == cf : List<&2, Ops.Item>}) -> {fine(Some{M.Running{v, m, acts}}, t, W, k, cf) == True{} : Bool}:
  %Equal.sym(List<&2, M.Node>, M.apply(acts, t, k), mk(acts, v, k), h5) : {fine.of(_, W, k, cf) == True{} : Bool}
  %Equal.trans(List<&2, Ops.Item>, M.file(mk(acts, v, k)), M.file.of(cuts(acts, M.visible(v))), cf, Equal.cong(List<&2, M.Node>, List<&2, Ops.Item>, l => M.file.of(l), M.visible(mk(acts, v, k)), cuts(acts, M.visible(v)), visible_mk(acts, v, k)), hf) : {Bool.and(M.invariant(mk(acts, v, k)), Bool.and(inw(mk(acts, v, k), k <> W), items_eq(M.file(mk(acts, v, k)), _))) == True{} : Bool}
  AL.and_intro(M.invariant(mk(acts, v, k)), Bool.and(inw(mk(acts, v, k), k <> W), items_eq(M.file(mk(acts, v, k)), M.file(mk(acts, v, k)))),
    inv_mk(acts, v, k, hi),
    AL.and_intro(inw(mk(acts, v, k), k <> W), items_eq(M.file(mk(acts, v, k)), M.file(mk(acts, v, k))),
      goods_inw(mk(acts, v, k), W, k, m, goods_mk(acts, v, W, k, m, hg)),
      items_eq_refl(M.file(mk(acts, v, k)))))

# The element before the cursor
# -----------------------------
#
# Where the cursor stands, the element read just before it is the parent's
# element before that position — unless the event has just written there,
# which the order forbids an insert to meet (`open`).
def ends_gap.b(+F: List<&2, M.Node>, +P: List<&2, M.Node>, +c: Nat, +a: Nat, +open: Bool, b: Bool, +eb: {Nat.is_lt(c, a) == b : Bool}, +ho: {M.left_of(F, List.length(&2, M.Node, F)) == Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, open, M.left_of(P, c), M.left_of(F, List.length(&2, M.Node, F))) : Maybe<&2, Maybe<&2, M.Name>>}, +le: {Nat.is_le(c, a) == True{} : Bool}, +ra: {Nat.is_le(a, List.length(&2, M.Node, P)) == True{} : Bool}) -> {M.left_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.length(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))))) == Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, Bool.or(Nat.is_lt(c, a), open), M.left_of(P, a), M.left_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.length(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))))) : Maybe<&2, Maybe<&2, M.Name>>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(c, a), True{}, eb) : {M.left_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.length(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))))) == Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, Bool.or(_, open), M.left_of(P, a), M.left_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.length(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))))) : Maybe<&2, Maybe<&2, M.Name>>}
      %Equal.sym(Nat, Nat.sub(a, c), 1n+Nat.sub(a, 1n+c), sub_pos(c, a, eb)) : {M.left_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), _)), List.length(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), _)))) == M.left_of(P, a) : Maybe<&2, Maybe<&2, M.Name>>}
      %Equal.trans(Nat, Nat.add(c, 1n+Nat.sub(a, 1n+c)), Nat.add(c, Nat.sub(a, c)), a, Equal.cong(Nat, Nat, x => Nat.add(c, x), 1n+Nat.sub(a, 1n+c), Nat.sub(a, c), Equal.sym(Nat, Nat.sub(a, c), 1n+Nat.sub(a, 1n+c), sub_pos(c, a, eb))), Comp.add_sub(c, a, le)) : {M.left_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), 1n+Nat.sub(a, 1n+c))), List.length(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), 1n+Nat.sub(a, 1n+c))))) == M.left_of(P, _) : Maybe<&2, Maybe<&2, M.Name>>}
      last_of(F, P, c, Nat.sub(a, 1n+c),
        (%Equal.sym(Nat, Nat.add(c, 1n+Nat.sub(a, 1n+c)), a, Equal.trans(Nat, Nat.add(c, 1n+Nat.sub(a, 1n+c)), Nat.add(c, Nat.sub(a, c)), a, Equal.cong(Nat, Nat, x => Nat.add(c, x), 1n+Nat.sub(a, 1n+c), Nat.sub(a, c), Equal.sym(Nat, Nat.sub(a, c), 1n+Nat.sub(a, 1n+c), sub_pos(c, a, eb))), Comp.add_sub(c, a, le))) : {Nat.is_le(_, List.length(&2, M.Node, P)) == True{} : Bool}
          ra))
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(c, a), False{}, eb) : {M.left_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.length(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))))) == Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, Bool.or(_, open), M.left_of(P, a), M.left_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.length(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))))) : Maybe<&2, Maybe<&2, M.Name>>}
      %Equal.sym(List<&2, M.Node>, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), F, Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.append(&2, M.Node, F, Nil{}), F, Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => List.append(&2, M.Node, F, l), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)), Nil{}, Equal.trans(List<&2, M.Node>, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), 0n), Nil{}, Equal.cong(Nat, List<&2, M.Node>, x => List.take(&2, M.Node, List.drop(&2, M.Node, P, c), x), Nat.sub(a, c), 0n, Equal.trans(Nat, Nat.sub(a, c), Nat.sub(c, c), 0n, Equal.cong(Nat, Nat, x => Nat.sub(x, c), a, c, Equal.sym(Nat, c, a, eq_of_le_nlt(c, a, le, eb))), sub_self(c))), AL.take_zero(List.drop(&2, M.Node, P, c)))), AL.append_nil(F))) : {M.left_of(_, List.length(&2, M.Node, _)) == Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, open, M.left_of(P, a), M.left_of(_, List.length(&2, M.Node, _))) : Maybe<&2, Maybe<&2, M.Name>>}
      %eq_of_le_nlt(c, a, le, eb) : {M.left_of(F, List.length(&2, M.Node, F)) == Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, open, M.left_of(P, _), M.left_of(F, List.length(&2, M.Node, F))) : Maybe<&2, Maybe<&2, M.Name>>}
      ho

def ends_gap(+F: List<&2, M.Node>, +P: List<&2, M.Node>, +c: Nat, +a: Nat, +open: Bool, +ho: {M.left_of(F, List.length(&2, M.Node, F)) == Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, open, M.left_of(P, c), M.left_of(F, List.length(&2, M.Node, F))) : Maybe<&2, Maybe<&2, M.Name>>}, +le: {Nat.is_le(c, a) == True{} : Bool}, +ra: {Nat.is_le(a, List.length(&2, M.Node, P)) == True{} : Bool}) -> {M.left_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.length(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))))) == Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, Bool.or(Nat.is_lt(c, a), open), M.left_of(P, a), M.left_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.length(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))))) : Maybe<&2, Maybe<&2, M.Name>>}:
  ends_gap.b(F, P, c, a, open, Nat.is_lt(c, a), {==}, ho, le, ra)

def ends_ins(+F: List<&2, M.Node>, +P: List<&2, M.Node>, +c: Nat, +a: Nat, +open: Bool, +ho: {M.left_of(F, List.length(&2, M.Node, F)) == Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, open, M.left_of(P, c), M.left_of(F, List.length(&2, M.Node, F))) : Maybe<&2, Maybe<&2, M.Name>>}, +gap: {gap_ok(c, a, open) == True{} : Bool}, +ra: {Nat.is_le(a, List.length(&2, M.Node, P)) == True{} : Bool}) -> {M.left_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.length(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))))) == M.left_of(P, a) : Maybe<&2, Maybe<&2, M.Name>>}:
  Equal.trans(Maybe<&2, Maybe<&2, M.Name>>, M.left_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.length(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))))), Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, Bool.or(Nat.is_lt(c, a), open), M.left_of(P, a), M.left_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.length(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))))), M.left_of(P, a),
    ends_gap(F, P, c, a, open, ho, gap_le(c, a, open, gap), ra),
    Equal.cong(Bool, Maybe<&2, Maybe<&2, M.Name>>, b => Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, b, M.left_of(P, a), M.left_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.length(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))))), Bool.or(Nat.is_lt(c, a), open), True{}, gap_or(c, a, open, gap)))

def lt_of_succ_le(q: Nat, n: Nat, e: {Nat.is_le(1n+q, n) == True{} : Bool}) -> {Nat.is_lt(q, n) == True{} : Bool}:
  match q n:
    case 0n 0n:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(e))
    case 0n 1n+r:
      {==}
    case 1n+p 0n:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(e))
    case 1n+p 1n+r:
      lt_of_succ_le(p, r, e)

def is_node(m: Maybe<&2, M.Node>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

def get_lt(xs: List<&2, M.Node>, q: Nat, l: {Nat.is_lt(q, List.length(&2, M.Node, xs)) == True{} : Bool}) -> {is_node(List.get(&2, M.Node, xs, q)) == True{} : Bool}:
  match xs q:
    case Nil{} _:
      Empty.absurd({False{} == True{} : Bool}, ML.lt_zero(q, l))
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      get_lt(t, p, l)

def left_some.at(+xs: List<&2, M.Node>, +q: Nat, mx: Maybe<&2, M.Node>, +emx: {List.get(&2, M.Node, xs, q) == mx : Maybe<&2, M.Node>}, l: {is_node(List.get(&2, M.Node, xs, q)) == True{} : Bool}) -> {M.left_of(xs, 1n+q) == Some{AL.unwrap_left(M.left_of(xs, 1n+q))} : Maybe<&2, Maybe<&2, M.Name>>}:
  match mx:
    case None{}:
      Empty.absurd({M.left_of(xs, 1n+q) == Some{AL.unwrap_left(M.left_of(xs, 1n+q))} : Maybe<&2, Maybe<&2, M.Name>>}, Comp.false_true(Equal.trans(Bool, False{}, is_node(List.get(&2, M.Node, xs, q)), True{}, Equal.sym(Bool, is_node(List.get(&2, M.Node, xs, q)), False{}, Equal.cong(Maybe<&2, M.Node>, Bool, y => is_node(y), List.get(&2, M.Node, xs, q), None{}, emx)), l)))
    case Some{x}:
      %Equal.sym(Maybe<&2, M.Node>, List.get(&2, M.Node, xs, q), Some{x}, emx) : {Maybe.map(&2, M.Node, Maybe<&2, M.Name>, y => Some{M.Node.name(y)}, _) == Some{AL.unwrap_left(Maybe.map(&2, M.Node, Maybe<&2, M.Name>, y => Some{M.Node.name(y)}, _))} : Maybe<&2, Maybe<&2, M.Name>>}
      {==}

# A gap inside the parent follows an element, or none.
def left_some(+xs: List<&2, M.Node>, a: Nat, ra: {Nat.is_le(a, List.length(&2, M.Node, xs)) == True{} : Bool}) -> {M.left_of(xs, a) == Some{AL.unwrap_left(M.left_of(xs, a))} : Maybe<&2, Maybe<&2, M.Name>>}:
  match a:
    case 0n:
      {==}
    case 1n++q:
      left_some.at(xs, q, List.get(&2, M.Node, xs, q), {==}, get_lt(xs, q, lt_of_succ_le(q, List.length(&2, M.Node, xs), ra)))

# The cursor
# ----------
#
# Where `Cursor.walk` succeeds, what it has written so far and what it
# will write from the cursor on.
def rdisc(r: Result<&2, &2, String, List<&2, Ops.Item>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{x}:
      Empty

def dis_ok(+at: Nat, ok: Bool, front: List<&2, Ops.Item>, r: Result<&2, &2, String, List<&2, Ops.Item>>, -cf: List<&2, Ops.Item>, e: {Cursor.combine(Cursor.disagreement(at, ok), front, r) == Done{cf} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {ok == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, (%e : {rdisc(_) : Type}
        Unit{}))

def done_or(r: Result<&2, &2, String, List<&2, Ops.Item>>, d: List<&2, Ops.Item>) -> List<&2, Ops.Item>:
  match r:
    case Fail{e}:
      d
    case Done{x}:
      x

def done_inj(+x: List<&2, Ops.Item>, -y: List<&2, Ops.Item>, e: {Done{x} == Done{y} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {x == y : List<&2, Ops.Item>}:
  Equal.cong(Result<&2, &2, String, List<&2, Ops.Item>>, List<&2, Ops.Item>, r => done_or(r, x), Done{x}, Done{y}, e)

def itake_zero(xs: List<&2, Ops.Item>) -> {List.take(&2, Ops.Item, xs, 0n) == Nil{} : List<&2, Ops.Item>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

def idrop_zero(xs: List<&2, Ops.Item>) -> {List.drop(&2, Ops.Item, xs, 0n) == xs : List<&2, Ops.Item>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

# Past an insert at `a`: the parent up to `a`, then the items.
def cur_ins(+O: List<&2, Ops.Item>, +P: List<&2, M.Node>, +c: Nat, +a: Nat, +items: List<&2, Ops.Item>, +rest: List<&2, Ops.Op>, -cf: List<&2, Ops.Item>, +le: {Nat.is_le(c, a) == True{} : Bool}, hw: {Cursor.combine(None{}, O, Cursor.walk(Ops.Op{Ops.Insert{}, a, items} <> rest, c, List.drop(&2, Ops.Item, M.file.of(P), c))) == Done{cf} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Cursor.combine(None{}, List.append(&2, Ops.Item, List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), items), Cursor.walk(rest, a, List.drop(&2, Ops.Item, M.file.of(P), a))) == Done{cf} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  %Equal.sym(List<&2, Ops.Item>, List.append(&2, Ops.Item, List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), items), List.append(&2, Ops.Item, O, List.append(&2, Ops.Item, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), items)), L.append_assoc(O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), items)) : {Cursor.combine(None{}, _, Cursor.walk(rest, a, List.drop(&2, Ops.Item, M.file.of(P), a))) == Done{cf} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %Equal.sym(List<&2, Ops.Item>, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), Equal.trans(List<&2, Ops.Item>, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, Ops.Item, M.file.of(List.drop(&2, M.Node, P, c)), Nat.sub(a, c)), List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), file_take(List.drop(&2, M.Node, P, c), Nat.sub(a, c)), Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => List.take(&2, Ops.Item, l, Nat.sub(a, c)), M.file.of(List.drop(&2, M.Node, P, c)), List.drop(&2, Ops.Item, M.file.of(P), c), file_drop(P, c)))) : {Cursor.combine(None{}, List.append(&2, Ops.Item, O, List.append(&2, Ops.Item, _, items)), Cursor.walk(rest, a, List.drop(&2, Ops.Item, M.file.of(P), a))) == Done{cf} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %max_le(c, a, le) : {Cursor.combine(None{}, List.append(&2, Ops.Item, O, List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), items)), Cursor.walk(rest, _, List.drop(&2, Ops.Item, M.file.of(P), a))) == Done{cf} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %Equal.trans(List<&2, Ops.Item>, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), List.drop(&2, Ops.Item, M.file.of(P), Nat.add(c, Nat.sub(a, c))), List.drop(&2, Ops.Item, M.file.of(P), a), Comp.drop_drop(c, M.file.of(P), Nat.sub(a, c)), Equal.cong(Nat, List<&2, Ops.Item>, x => List.drop(&2, Ops.Item, M.file.of(P), x), Nat.add(c, Nat.sub(a, c)), a, Comp.add_sub(c, a, le))) : {Cursor.combine(None{}, List.append(&2, Ops.Item, O, List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), items)), Cursor.walk(rest, Nat.max(c, a), _)) == Done{cf} : Result<&2, &2, String, List<&2, Ops.Item>>}
  Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.combine(None{}, List.append(&2, Ops.Item, O, List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), items)), Cursor.walk(rest, Nat.max(c, a), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)))), Cursor.combine(None{}, O, Cursor.combine(None{}, List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), items), Cursor.walk(rest, Nat.max(c, a), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c))))), Done{cf},
    L.combine_split(None{}, None{}, O, List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), items), Cursor.walk(rest, Nat.max(c, a), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)))), hw)

# At a delete at `a`: the quote agrees with the parent there.
def cur_del_pm(+O: List<&2, Ops.Item>, +P: List<&2, M.Node>, +c: Nat, +a: Nat, +items: List<&2, Ops.Item>, +rest: List<&2, Ops.Op>, -cf: List<&2, Ops.Item>, +le: {Nat.is_le(c, a) == True{} : Bool}, hw: {Cursor.combine(None{}, O, Cursor.walk(Ops.Op{Ops.Delete{}, a, items} <> rest, c, List.drop(&2, Ops.Item, M.file.of(P), c))) == Done{cf} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Spec.prefix_matches(items, M.file.of(List.drop(&2, M.Node, P, a))) == True{} : Bool}:
  %Equal.sym(List<&2, Ops.Item>, M.file.of(List.drop(&2, M.Node, P, a)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), Equal.trans(List<&2, Ops.Item>, M.file.of(List.drop(&2, M.Node, P, a)), List.drop(&2, Ops.Item, M.file.of(P), a), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), file_drop(P, a), Equal.sym(List<&2, Ops.Item>, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), List.drop(&2, Ops.Item, M.file.of(P), a), Equal.trans(List<&2, Ops.Item>, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), List.drop(&2, Ops.Item, M.file.of(P), Nat.add(c, Nat.sub(a, c))), List.drop(&2, Ops.Item, M.file.of(P), a), Comp.drop_drop(c, M.file.of(P), Nat.sub(a, c)), Equal.cong(Nat, List<&2, Ops.Item>, x => List.drop(&2, Ops.Item, M.file.of(P), x), Nat.add(c, Nat.sub(a, c)), a, Comp.add_sub(c, a, le)))))) : {Spec.prefix_matches(items, _) == True{} : Bool}
  dis_ok(a, Spec.prefix_matches(items, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c))), List.append(&2, Ops.Item, O, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c))), Cursor.walk(rest, Nat.add(a, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), List.length(&2, Ops.Item, items))), cf,
    Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.combine(Cursor.disagreement(a, Spec.prefix_matches(items, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)))), List.append(&2, Ops.Item, O, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c))), Cursor.walk(rest, Nat.add(a, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), List.length(&2, Ops.Item, items)))), Cursor.combine(None{}, O, Cursor.combine(Cursor.disagreement(a, Spec.prefix_matches(items, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)))), List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), Cursor.walk(rest, Nat.add(a, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), List.length(&2, Ops.Item, items))))), Done{cf},
      L.combine_split(None{}, Cursor.disagreement(a, Spec.prefix_matches(items, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)))), O, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), Cursor.walk(rest, Nat.add(a, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), List.length(&2, Ops.Item, items)))), hw))

# Past a delete at `a`: the parent up to `a`, and the cursor past the quote.
def cur_del_w(+O: List<&2, Ops.Item>, +P: List<&2, M.Node>, +c: Nat, +a: Nat, +items: List<&2, Ops.Item>, +rest: List<&2, Ops.Op>, -cf: List<&2, Ops.Item>, +le: {Nat.is_le(c, a) == True{} : Bool}, +hw: {Cursor.combine(None{}, O, Cursor.walk(Ops.Op{Ops.Delete{}, a, items} <> rest, c, List.drop(&2, Ops.Item, M.file.of(P), c))) == Done{cf} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Cursor.combine(None{}, List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), Cursor.walk(rest, Nat.add(a, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, M.file.of(P), Nat.add(a, List.length(&2, Ops.Item, items))))) == Done{cf} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  %Equal.sym(List<&2, Ops.Item>, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), Equal.trans(List<&2, Ops.Item>, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, Ops.Item, M.file.of(List.drop(&2, M.Node, P, c)), Nat.sub(a, c)), List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), file_take(List.drop(&2, M.Node, P, c), Nat.sub(a, c)), Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => List.take(&2, Ops.Item, l, Nat.sub(a, c)), M.file.of(List.drop(&2, M.Node, P, c)), List.drop(&2, Ops.Item, M.file.of(P), c), file_drop(P, c)))) : {Cursor.combine(None{}, List.append(&2, Ops.Item, O, _), Cursor.walk(rest, Nat.add(a, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, M.file.of(P), Nat.add(a, List.length(&2, Ops.Item, items))))) == Done{cf} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %Equal.trans(List<&2, Ops.Item>, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), a), List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, M.file.of(P), Nat.add(a, List.length(&2, Ops.Item, items))), Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => List.drop(&2, Ops.Item, l, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), List.drop(&2, Ops.Item, M.file.of(P), a), Equal.trans(List<&2, Ops.Item>, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), List.drop(&2, Ops.Item, M.file.of(P), Nat.add(c, Nat.sub(a, c))), List.drop(&2, Ops.Item, M.file.of(P), a), Comp.drop_drop(c, M.file.of(P), Nat.sub(a, c)), Equal.cong(Nat, List<&2, Ops.Item>, x => List.drop(&2, Ops.Item, M.file.of(P), x), Nat.add(c, Nat.sub(a, c)), a, Comp.add_sub(c, a, le)))), Comp.drop_drop(a, M.file.of(P), List.length(&2, Ops.Item, items))) : {Cursor.combine(None{}, List.append(&2, Ops.Item, O, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c))), Cursor.walk(rest, Nat.add(a, List.length(&2, Ops.Item, items)), _)) == Done{cf} : Result<&2, &2, String, List<&2, Ops.Item>>}
  Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.combine(None{}, List.append(&2, Ops.Item, O, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c))), Cursor.walk(rest, Nat.add(a, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), List.length(&2, Ops.Item, items)))), Cursor.combine(Cursor.disagreement(a, True{}), List.append(&2, Ops.Item, O, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c))), Cursor.walk(rest, Nat.add(a, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), List.length(&2, Ops.Item, items)))), Done{cf},
    {==},
    Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.combine(Cursor.disagreement(a, True{}), List.append(&2, Ops.Item, O, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c))), Cursor.walk(rest, Nat.add(a, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), List.length(&2, Ops.Item, items)))), Cursor.combine(Cursor.disagreement(a, Spec.prefix_matches(items, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)))), List.append(&2, Ops.Item, O, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c))), Cursor.walk(rest, Nat.add(a, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), List.length(&2, Ops.Item, items)))), Done{cf},
      Equal.cong(Bool, Result<&2, &2, String, List<&2, Ops.Item>>, x => Cursor.combine(Cursor.disagreement(a, x), List.append(&2, Ops.Item, O, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c))), Cursor.walk(rest, Nat.add(a, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), List.length(&2, Ops.Item, items)))), True{}, Spec.prefix_matches(items, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c))),
        Equal.sym(Bool, Spec.prefix_matches(items, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c))), True{}, dis_ok(a, Spec.prefix_matches(items, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c))), List.append(&2, Ops.Item, O, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c))), Cursor.walk(rest, Nat.add(a, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), List.length(&2, Ops.Item, items))), cf, Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.combine(Cursor.disagreement(a, Spec.prefix_matches(items, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)))), List.append(&2, Ops.Item, O, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c))), Cursor.walk(rest, Nat.add(a, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), List.length(&2, Ops.Item, items)))), Cursor.combine(None{}, O, Cursor.combine(Cursor.disagreement(a, Spec.prefix_matches(items, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)))), List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), Cursor.walk(rest, Nat.add(a, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), List.length(&2, Ops.Item, items))))), Done{cf}, L.combine_split(None{}, Cursor.disagreement(a, Spec.prefix_matches(items, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)))), O, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), Cursor.walk(rest, Nat.add(a, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), List.length(&2, Ops.Item, items)))), hw)))),
      Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.combine(Cursor.disagreement(a, Spec.prefix_matches(items, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)))), List.append(&2, Ops.Item, O, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c))), Cursor.walk(rest, Nat.add(a, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), List.length(&2, Ops.Item, items)))), Cursor.combine(None{}, O, Cursor.combine(Cursor.disagreement(a, Spec.prefix_matches(items, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)))), List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), Cursor.walk(rest, Nat.add(a, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), List.length(&2, Ops.Item, items))))), Done{cf}, L.combine_split(None{}, Cursor.disagreement(a, Spec.prefix_matches(items, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)))), O, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), Cursor.walk(rest, Nat.add(a, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), c), Nat.sub(a, c)), List.length(&2, Ops.Item, items)))), hw)))

# An insert at a delete's own position, once the cursor is past the quote:
# its items, and the cursor stays.
def cur_rep(+O: List<&2, Ops.Item>, +P: List<&2, M.Node>, +a: Nat, +items2: List<&2, Ops.Item>, +more: List<&2, Ops.Op>, +stop: Nat, -cf: List<&2, Ops.Item>, +le: {Nat.is_le(a, stop) == True{} : Bool}, +z: {Nat.sub(a, stop) == 0n : Nat}, hw: {Cursor.combine(None{}, O, Cursor.walk(Ops.Op{Ops.Insert{}, a, items2} <> more, stop, List.drop(&2, Ops.Item, M.file.of(P), stop))) == Done{cf} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Cursor.combine(None{}, List.append(&2, Ops.Item, O, items2), Cursor.walk(more, stop, List.drop(&2, Ops.Item, M.file.of(P), stop))) == Done{cf} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  %Equal.trans(List<&2, Ops.Item>, List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), stop), Nat.sub(a, stop)), items2), List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), stop), 0n), items2), items2, Equal.cong(Nat, List<&2, Ops.Item>, x => List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), stop), x), items2), Nat.sub(a, stop), 0n, z), Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => List.append(&2, Ops.Item, l, items2), List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), stop), 0n), Nil{}, itake_zero(List.drop(&2, Ops.Item, M.file.of(P), stop)))) : {Cursor.combine(None{}, List.append(&2, Ops.Item, O, _), Cursor.walk(more, stop, List.drop(&2, Ops.Item, M.file.of(P), stop))) == Done{cf} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %max_ge(stop, a, le) : {Cursor.combine(None{}, List.append(&2, Ops.Item, O, List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), stop), Nat.sub(a, stop)), items2)), Cursor.walk(more, _, List.drop(&2, Ops.Item, M.file.of(P), stop))) == Done{cf} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %Equal.trans(List<&2, Ops.Item>, List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), stop), Nat.sub(a, stop)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), stop), 0n), List.drop(&2, Ops.Item, M.file.of(P), stop), Equal.cong(Nat, List<&2, Ops.Item>, x => List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), stop), x), Nat.sub(a, stop), 0n, z), idrop_zero(List.drop(&2, Ops.Item, M.file.of(P), stop))) : {Cursor.combine(None{}, List.append(&2, Ops.Item, O, List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), stop), Nat.sub(a, stop)), items2)), Cursor.walk(more, Nat.max(stop, a), _)) == Done{cf} : Result<&2, &2, String, List<&2, Ops.Item>>}
  Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.combine(None{}, List.append(&2, Ops.Item, O, List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), stop), Nat.sub(a, stop)), items2)), Cursor.walk(more, Nat.max(stop, a), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), stop), Nat.sub(a, stop)))), Cursor.combine(None{}, O, Cursor.combine(None{}, List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), stop), Nat.sub(a, stop)), items2), Cursor.walk(more, Nat.max(stop, a), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), stop), Nat.sub(a, stop))))), Done{cf},
    L.combine_split(None{}, None{}, O, List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), stop), Nat.sub(a, stop)), items2), Cursor.walk(more, Nat.max(stop, a), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, M.file.of(P), stop), Nat.sub(a, stop)))), hw)

# One step of the run
# -------------------

# Nothing left to do: the view, with the event's removals left out, is
# what the cursor wrote and the parent from the cursor on.
def sim_nil(+v: List<&2, M.Node>, +acts: List<&2, M.Action>, +F: List<&2, M.Node>, +O: List<&2, Ops.Item>, +P: List<&2, M.Node>, +c: Nat, -cf: List<&2, Ops.Item>, hq: {M.visible(v) == List.append(&2, M.Node, F, List.drop(&2, M.Node, P, c)) : List<&2, M.Node>}, h6: {M.file.of(cuts(acts, F)) == O : List<&2, Ops.Item>}, h7: {clear(List.drop(&2, M.Node, P, c), acts) == True{} : Bool}, hw: {Cursor.combine(None{}, O, Cursor.walk(Nil{}, c, List.drop(&2, Ops.Item, M.file.of(P), c))) == Done{cf} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {M.file.of(cuts(acts, M.visible(v))) == cf : List<&2, Ops.Item>}:
  Equal.trans(List<&2, Ops.Item>, M.file.of(cuts(acts, M.visible(v))), M.file.of(cuts(acts, List.append(&2, M.Node, F, List.drop(&2, M.Node, P, c)))), cf, Equal.cong(List<&2, M.Node>, List<&2, Ops.Item>, l => M.file.of(cuts(acts, l)), M.visible(v), List.append(&2, M.Node, F, List.drop(&2, M.Node, P, c)), hq), Equal.trans(List<&2, Ops.Item>, M.file.of(cuts(acts, List.append(&2, M.Node, F, List.drop(&2, M.Node, P, c)))), M.file.of(List.append(&2, M.Node, cuts(acts, F), List.drop(&2, M.Node, P, c))), cf, Equal.cong(List<&2, M.Node>, List<&2, Ops.Item>, l => M.file.of(l), cuts(acts, List.append(&2, M.Node, F, List.drop(&2, M.Node, P, c))), List.append(&2, M.Node, cuts(acts, F), List.drop(&2, M.Node, P, c)), Equal.trans(List<&2, M.Node>, cuts(acts, List.append(&2, M.Node, F, List.drop(&2, M.Node, P, c))), List.append(&2, M.Node, cuts(acts, F), cuts(acts, List.drop(&2, M.Node, P, c))), List.append(&2, M.Node, cuts(acts, F), List.drop(&2, M.Node, P, c)), cuts_append(acts, F, List.drop(&2, M.Node, P, c)), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => List.append(&2, M.Node, cuts(acts, F), l), cuts(acts, List.drop(&2, M.Node, P, c)), List.drop(&2, M.Node, P, c), cuts_clear(acts, List.drop(&2, M.Node, P, c), h7)))), Equal.trans(List<&2, Ops.Item>, M.file.of(List.append(&2, M.Node, cuts(acts, F), List.drop(&2, M.Node, P, c))), List.append(&2, Ops.Item, O, List.drop(&2, Ops.Item, M.file.of(P), c)), cf, (%h6 : {M.file.of(List.append(&2, M.Node, cuts(acts, F), List.drop(&2, M.Node, P, c))) == List.append(&2, Ops.Item, _, List.drop(&2, Ops.Item, M.file.of(P), c)) : List<&2, Ops.Item>}
          %file_drop(P, c) : {M.file.of(List.append(&2, M.Node, cuts(acts, F), List.drop(&2, M.Node, P, c))) == List.append(&2, Ops.Item, M.file.of(cuts(acts, F)), _) : List<&2, Ops.Item>}
          file_append(cuts(acts, F), List.drop(&2, M.Node, P, c))), done_inj(List.append(&2, Ops.Item, O, List.drop(&2, Ops.Item, M.file.of(P), c)), cf, hw))))

# The view split at the gap an operation at `a` names.
def hq_gap(+v: List<&2, M.Node>, +F: List<&2, M.Node>, +P: List<&2, M.Node>, +c: Nat, +a: Nat, +le: {Nat.is_le(c, a) == True{} : Bool}, hq: {M.visible(v) == List.append(&2, M.Node, F, List.drop(&2, M.Node, P, c)) : List<&2, M.Node>}) -> {M.visible(v) == List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.drop(&2, M.Node, P, a)) : List<&2, M.Node>}:
  Equal.trans(List<&2, M.Node>, M.visible(v), List.append(&2, M.Node, F, List.drop(&2, M.Node, P, c)), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.drop(&2, M.Node, P, a)), hq, Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, F, List.drop(&2, M.Node, P, c)), List.append(&2, M.Node, F, List.append(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)), List.drop(&2, M.Node, P, a))), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.drop(&2, M.Node, P, a)), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => List.append(&2, M.Node, F, l), List.drop(&2, M.Node, P, c), List.append(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)), List.drop(&2, M.Node, P, a)), drop_split(P, c, a, le)), Equal.sym(List<&2, M.Node>, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.drop(&2, M.Node, P, a)), List.append(&2, M.Node, F, List.append(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)), List.drop(&2, M.Node, P, a))), nappend_assoc(F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)), List.drop(&2, M.Node, P, a)))))

def h7_gap(+acts: List<&2, M.Action>, +P: List<&2, M.Node>, +c: Nat, +a: Nat, +le: {Nat.is_le(c, a) == True{} : Bool}, h7: {clear(List.drop(&2, M.Node, P, c), acts) == True{} : Bool}) -> {clear(List.append(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)), List.drop(&2, M.Node, P, a)), acts) == True{} : Bool}:
  %drop_split(P, c, a, le) : {clear(_, acts) == True{} : Bool}
  h7

def cuts_gap(+acts: List<&2, M.Action>, +F: List<&2, M.Node>, +P: List<&2, M.Node>, +c: Nat, +a: Nat, +le: {Nat.is_le(c, a) == True{} : Bool}, +h7: {clear(List.drop(&2, M.Node, P, c), acts) == True{} : Bool}) -> {cuts(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))) == List.append(&2, M.Node, cuts(acts, F), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))) : List<&2, M.Node>}:
  Equal.trans(List<&2, M.Node>, cuts(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), List.append(&2, M.Node, cuts(acts, F), cuts(acts, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), List.append(&2, M.Node, cuts(acts, F), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), cuts_append(acts, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => List.append(&2, M.Node, cuts(acts, F), l), cuts(acts, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)), cuts_clear(acts, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)), clear_left(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)), List.drop(&2, M.Node, P, a), acts, h7_gap(acts, P, c, a, le, h7)))))

# Inserts
# -------

def ins_step_eq(+v: List<&2, M.Node>, +m: Nat, +acts: List<&2, M.Action>, +items: List<&2, Ops.Item>, +a: Nat, +P: List<&2, M.Node>, +k: Nat, +l: Maybe<&2, M.Name>, hl0: {M.left_of(P, a) == Some{l} : Maybe<&2, Maybe<&2, M.Name>>}) -> {M.run.step(Some{M.Running{v, m, acts}}, Ops.Op{Ops.Insert{}, a, items}, k, P) == Some{M.Running{iv(M.inserts(items, v, k, l, m)), im(M.inserts(items, v, k, l, m)), List.append(&2, M.Action, acts, ML.Inserted.acts(M.inserts(items, v, k, l, m)))}} : Maybe<&2, M.Running>}:
  %Equal.sym(Maybe<&2, Maybe<&2, M.Name>>, M.left_of(P, a), Some{l}, hl0) : {M.run.insert(items, v, k, m, acts, _) == Some{M.Running{iv(M.inserts(items, v, k, l, m)), im(M.inserts(items, v, k, l, m)), List.append(&2, M.Action, acts, ML.Inserted.acts(M.inserts(items, v, k, l, m)))}} : Maybe<&2, M.Running>}
  run_inserted(acts, M.inserts(items, v, k, l, m))

def ins_h5(+t: List<&2, M.Node>, +v: List<&2, M.Node>, +acts: List<&2, M.Action>, +items: List<&2, Ops.Item>, +k: Nat, +l: Maybe<&2, M.Name>, +m: Nat, +ha: {ML.avoid(acts, k) == True{} : Bool}, +h5: {M.apply(acts, t, k) == mk(acts, v, k) : List<&2, M.Node>}) -> {M.apply(List.append(&2, M.Action, acts, ML.Inserted.acts(M.inserts(items, v, k, l, m))), t, k) == mk(List.append(&2, M.Action, acts, ML.Inserted.acts(M.inserts(items, v, k, l, m))), iv(M.inserts(items, v, k, l, m)), k) : List<&2, M.Node>}:
  Equal.trans(List<&2, M.Node>, M.apply(List.append(&2, M.Action, acts, ML.Inserted.acts(M.inserts(items, v, k, l, m))), t, k), M.apply(ML.Inserted.acts(M.inserts(items, v, k, l, m)), M.apply(acts, t, k), k), mk(List.append(&2, M.Action, acts, ML.Inserted.acts(M.inserts(items, v, k, l, m))), iv(M.inserts(items, v, k, l, m)), k), apply_append(acts, ML.Inserted.acts(M.inserts(items, v, k, l, m)), t, k), Equal.trans(List<&2, M.Node>, M.apply(ML.Inserted.acts(M.inserts(items, v, k, l, m)), M.apply(acts, t, k), k), M.apply(ML.Inserted.acts(M.inserts(items, v, k, l, m)), mk(acts, v, k), k), mk(List.append(&2, M.Action, acts, ML.Inserted.acts(M.inserts(items, v, k, l, m))), iv(M.inserts(items, v, k, l, m)), k), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, u => M.apply(ML.Inserted.acts(M.inserts(items, v, k, l, m)), u, k), M.apply(acts, t, k), mk(acts, v, k), h5), Equal.trans(List<&2, M.Node>, M.apply(ML.Inserted.acts(M.inserts(items, v, k, l, m)), mk(acts, v, k), k), mk(acts, M.apply(ML.Inserted.acts(M.inserts(items, v, k, l, m)), v, k), k), mk(List.append(&2, M.Action, acts, ML.Inserted.acts(M.inserts(items, v, k, l, m))), iv(M.inserts(items, v, k, l, m)), k), apply_attaches_mk(ML.Inserted.acts(M.inserts(items, v, k, l, m)), acts, v, k, ha, attaches_ins(items, v, k, l, m)), Equal.trans(List<&2, M.Node>, mk(acts, M.apply(ML.Inserted.acts(M.inserts(items, v, k, l, m)), v, k), k), mk(acts, iv(M.inserts(items, v, k, l, m)), k), mk(List.append(&2, M.Action, acts, ML.Inserted.acts(M.inserts(items, v, k, l, m))), iv(M.inserts(items, v, k, l, m)), k), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, u => mk(acts, u, k), M.apply(ML.Inserted.acts(M.inserts(items, v, k, l, m)), v, k), iv(M.inserts(items, v, k, l, m)), Equal.sym(List<&2, M.Node>, iv(M.inserts(items, v, k, l, m)), M.apply(ML.Inserted.acts(M.inserts(items, v, k, l, m)), v, k), ins_apply(items, v, k, l, m))), Equal.trans(List<&2, M.Node>, mk(acts, iv(M.inserts(items, v, k, l, m)), k), mk(ML.Inserted.acts(M.inserts(items, v, k, l, m)), mk(acts, iv(M.inserts(items, v, k, l, m)), k), k), mk(List.append(&2, M.Action, acts, ML.Inserted.acts(M.inserts(items, v, k, l, m))), iv(M.inserts(items, v, k, l, m)), k), Equal.sym(List<&2, M.Node>, mk(ML.Inserted.acts(M.inserts(items, v, k, l, m)), mk(acts, iv(M.inserts(items, v, k, l, m)), k), k), mk(acts, iv(M.inserts(items, v, k, l, m)), k), mk_attaches(ML.Inserted.acts(M.inserts(items, v, k, l, m)), mk(acts, iv(M.inserts(items, v, k, l, m)), k), k, attaches_ins(items, v, k, l, m))), Equal.sym(List<&2, M.Node>, mk(List.append(&2, M.Action, acts, ML.Inserted.acts(M.inserts(items, v, k, l, m))), iv(M.inserts(items, v, k, l, m)), k), mk(ML.Inserted.acts(M.inserts(items, v, k, l, m)), mk(acts, iv(M.inserts(items, v, k, l, m)), k), k), mk_append(acts, ML.Inserted.acts(M.inserts(items, v, k, l, m)), iv(M.inserts(items, v, k, l, m)), k)))))))

def ins_hi(+items: List<&2, Ops.Item>, +v: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +l: Maybe<&2, M.Name>, +m: Nat, +xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +hi: {M.invariant(v) == True{} : Bool}, +hg: {goods(v, W, k, m) == True{} : Bool}, +hq: {M.visible(v) == List.append(&2, M.Node, xs, ys) : List<&2, M.Node>}, +hl: {M.left_of(xs, List.length(&2, M.Node, xs)) == Some{l} : Maybe<&2, Maybe<&2, M.Name>>}) -> {M.invariant(iv(M.inserts(items, v, k, l, m))) == True{} : Bool}:
  Comp.and_left(M.invariant(iv(M.inserts(items, v, k, l, m))), goods(iv(M.inserts(items, v, k, l, m)), W, k, Nat.add(List.length(&2, Ops.Item, items), m)), ins_all(items, v, W, k, l, m, xs, ys, hi, hg, hq, hl))

def ins_hg(+items: List<&2, Ops.Item>, +v: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +l: Maybe<&2, M.Name>, +m: Nat, +xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +hi: {M.invariant(v) == True{} : Bool}, +hg: {goods(v, W, k, m) == True{} : Bool}, +hq: {M.visible(v) == List.append(&2, M.Node, xs, ys) : List<&2, M.Node>}, +hl: {M.left_of(xs, List.length(&2, M.Node, xs)) == Some{l} : Maybe<&2, Maybe<&2, M.Name>>}) -> {goods(iv(M.inserts(items, v, k, l, m)), W, k, im(M.inserts(items, v, k, l, m))) == True{} : Bool}:
  %Equal.sym(Nat, im(M.inserts(items, v, k, l, m)), Nat.add(List.length(&2, Ops.Item, items), m), im_ins(items, v, k, l, m)) : {goods(iv(M.inserts(items, v, k, l, m)), W, k, _) == True{} : Bool}
  Comp.and_right(M.invariant(iv(M.inserts(items, v, k, l, m))), goods(iv(M.inserts(items, v, k, l, m)), W, k, Nat.add(List.length(&2, Ops.Item, items), m)), ins_all(items, v, W, k, l, m, xs, ys, hi, hg, hq, hl))

def hit_avoid(acts: List<&2, M.Action>, +k: Nat, +mm: Nat, +h: {ML.avoid(acts, k) == True{} : Bool}) -> {hit(acts, M.Name{k, mm}) == False{} : Bool}:
  match acts:
    case Nil{}:
      {==}
    case M.Attach{x, it, pl} <> rest:
      hit_avoid(rest, k, mm, Comp.and_right(True{}, ML.avoid(rest, k), h))
    case M.Delete{M.Name{+a, +m2}} <> rest:
      AL.or_false(M.Name.eq(M.Name{k, mm}, M.Name{a, m2}), hit(rest, M.Name{k, mm}),
        ML.name_ne(k, mm, a, m2, AL.not_of_true(Nat.is_eq(k, a), Comp.and_left(Bool.not(Nat.is_eq(k, a)), ML.avoid(rest, k), h))),
        hit_avoid(rest, k, mm, Comp.and_right(Bool.not(Nat.is_eq(k, a)), ML.avoid(rest, k), h)))

# What a run mints, no earlier delete names.
def clear_fresh(items: List<&2, Ops.Item>, +v: List<&2, M.Node>, +k: Nat, +l: Maybe<&2, M.Name>, +m: Nat, +acts: List<&2, M.Action>, +ha: {ML.avoid(acts, k) == True{} : Bool}) -> {clear(fresh_nodes(items, v, k, l, m), acts) == True{} : Bool}:
  match items:
    case Nil{}:
      {==}
    case +it <> +more:
      AL.and_intro(Bool.not(hit(acts, M.Name{k, m})), clear(fresh_nodes(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, l), Nil{}}), k, Some{M.Name{k, m}}, 1n+m), acts),
        AL.not_true(hit(acts, M.Name{k, m}), hit_avoid(acts, k, m, ha)),
        clear_fresh(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, l), Nil{}}), k, Some{M.Name{k, m}}, 1n+m, acts, ha))

def cuts_ia(+acts: List<&2, M.Action>, +w: List<&2, M.Node>, +items: List<&2, Ops.Item>, +v: List<&2, M.Node>, +k: Nat, +l: Maybe<&2, M.Name>, +m: Nat) -> {cuts(List.append(&2, M.Action, acts, ML.Inserted.acts(M.inserts(items, v, k, l, m))), w) == cuts(acts, w) : List<&2, M.Node>}:
  cuts_after(acts, ML.Inserted.acts(M.inserts(items, v, k, l, m)), w, clear_attaches(w, ML.Inserted.acts(M.inserts(items, v, k, l, m)), attaches_ins(items, v, k, l, m)))

def cuts_fresh(+acts: List<&2, M.Action>, +xs: List<&2, M.Node>, +items: List<&2, Ops.Item>, +v: List<&2, M.Node>, +k: Nat, +l: Maybe<&2, M.Name>, +m: Nat, +ha: {ML.avoid(acts, k) == True{} : Bool}) -> {cuts(acts, List.append(&2, M.Node, xs, fresh_nodes(items, v, k, l, m))) == List.append(&2, M.Node, cuts(acts, xs), fresh_nodes(items, v, k, l, m)) : List<&2, M.Node>}:
  Equal.trans(List<&2, M.Node>, cuts(acts, List.append(&2, M.Node, xs, fresh_nodes(items, v, k, l, m))), List.append(&2, M.Node, cuts(acts, xs), cuts(acts, fresh_nodes(items, v, k, l, m))), List.append(&2, M.Node, cuts(acts, xs), fresh_nodes(items, v, k, l, m)), cuts_append(acts, xs, fresh_nodes(items, v, k, l, m)), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, q => List.append(&2, M.Node, cuts(acts, xs), q), cuts(acts, fresh_nodes(items, v, k, l, m)), fresh_nodes(items, v, k, l, m), cuts_clear(acts, fresh_nodes(items, v, k, l, m), clear_fresh(items, v, k, l, m, acts, ha))))

def clear_ia(+zs: List<&2, M.Node>, +acts: List<&2, M.Action>, +items: List<&2, Ops.Item>, +v: List<&2, M.Node>, +k: Nat, +l: Maybe<&2, M.Name>, +m: Nat, +hz: {clear(zs, acts) == True{} : Bool}) -> {clear(zs, List.append(&2, M.Action, acts, ML.Inserted.acts(M.inserts(items, v, k, l, m)))) == True{} : Bool}:
  clear_append(zs, acts, ML.Inserted.acts(M.inserts(items, v, k, l, m)), hz, clear_attaches(zs, ML.Inserted.acts(M.inserts(items, v, k, l, m)), attaches_ins(items, v, k, l, m)))

# Deletes
# -------

def dsplit(+P: List<&2, M.Node>, +a: Nat, +items: List<&2, Ops.Item>) -> {List.drop(&2, M.Node, P, a) == List.append(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items)))) : List<&2, M.Node>}:
  %Comp.sub_add(a, List.length(&2, Ops.Item, items)) : {List.drop(&2, M.Node, P, a) == List.append(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), _), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items)))) : List<&2, M.Node>}
  drop_split(P, a, Nat.add(a, List.length(&2, Ops.Item, items)), Comp.le_add(a, a, List.length(&2, Ops.Item, items), Comp.le_refl(a)))

def hq_del(+v: List<&2, M.Node>, +F: List<&2, M.Node>, +P: List<&2, M.Node>, +c: Nat, +a: Nat, +items: List<&2, Ops.Item>, +le: {Nat.is_le(c, a) == True{} : Bool}, +hq: {M.visible(v) == List.append(&2, M.Node, F, List.drop(&2, M.Node, P, c)) : List<&2, M.Node>}) -> {M.visible(v) == List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items)))) : List<&2, M.Node>}:
  Equal.trans(List<&2, M.Node>, M.visible(v), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.drop(&2, M.Node, P, a)), List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items)))), hq_gap(v, F, P, c, a, le, hq), Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.drop(&2, M.Node, P, a)), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.append(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))))), List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items)))), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, q => List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), q), List.drop(&2, M.Node, P, a), List.append(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items)))), dsplit(P, a, items)), Equal.sym(List<&2, M.Node>, List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items)))), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.append(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))))), nappend_assoc(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items)))))))

def del_step_eq(+v: List<&2, M.Node>, +m: Nat, +acts: List<&2, M.Action>, +items: List<&2, Ops.Item>, +a: Nat, +P: List<&2, M.Node>, +k: Nat, +pm: {Spec.prefix_matches(items, M.file.of(List.drop(&2, M.Node, P, a))) == True{} : Bool}) -> {M.run.step(Some{M.Running{v, m, acts}}, Ops.Op{Ops.Delete{}, a, items}, k, P) == Some{M.Running{v, m, List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))))}} : Maybe<&2, M.Running>}:
  %Equal.sym(Maybe<&2, List<&2, M.Action>>, M.deletes(items, P, a), Some{dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))}, deletes_of(items, P, a, List.drop(&2, M.Node, P, a), {==}, pm)) : {M.run.deleted(v, m, acts, _) == Some{M.Running{v, m, List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))))}} : Maybe<&2, M.Running>}
  {==}

def avoid_dels(+items: List<&2, Ops.Item>, +P: List<&2, M.Node>, +a: Nat, +W: List<&2, Nat>, +k: Nat, +hk: {M.has(W, k) == False{} : Bool}, +hpa: {ML.authors_in(P, W) == True{} : Bool}, +pm: {Spec.prefix_matches(items, M.file.of(List.drop(&2, M.Node, P, a))) == True{} : Bool}) -> {ML.avoid(dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), k) == True{} : Bool}:
  %deletes_of(items, P, a, List.drop(&2, M.Node, P, a), {==}, pm) : {ML.avoid.m(_, k) == True{} : Bool}
  ML.deletes_avoid(items, P, a, W, k, hpa, hk)

def del_h5(+t: List<&2, M.Node>, +v: List<&2, M.Node>, +acts: List<&2, M.Action>, +ds: List<&2, M.Node>, +k: Nat, +h5: {M.apply(acts, t, k) == mk(acts, v, k) : List<&2, M.Node>}) -> {M.apply(List.append(&2, M.Action, acts, dels(ds)), t, k) == mk(List.append(&2, M.Action, acts, dels(ds)), v, k) : List<&2, M.Node>}:
  Equal.trans(List<&2, M.Node>, M.apply(List.append(&2, M.Action, acts, dels(ds)), t, k), M.apply(dels(ds), M.apply(acts, t, k), k), mk(List.append(&2, M.Action, acts, dels(ds)), v, k), apply_append(acts, dels(ds), t, k), Equal.trans(List<&2, M.Node>, M.apply(dels(ds), M.apply(acts, t, k), k), M.apply(dels(ds), mk(acts, v, k), k), mk(List.append(&2, M.Action, acts, dels(ds)), v, k), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, u => M.apply(dels(ds), u, k), M.apply(acts, t, k), mk(acts, v, k), h5), Equal.trans(List<&2, M.Node>, M.apply(dels(ds), mk(acts, v, k), k), mk(dels(ds), mk(acts, v, k), k), mk(List.append(&2, M.Action, acts, dels(ds)), v, k), apply_dels(ds, mk(acts, v, k), k), Equal.sym(List<&2, M.Node>, mk(List.append(&2, M.Action, acts, dels(ds)), v, k), mk(dels(ds), mk(acts, v, k), k), mk_append(acts, dels(ds), v, k)))))

def nd_v(+v: List<&2, M.Node>, +hi: {M.invariant(v) == True{} : Bool}) -> {M.nodup(M.visible(v)) == True{} : Bool}:
  AL.nodup_standing(M.order(v), Comp.and_right(M.fits(1n+List.length(&2, M.Node, v), v, M.children(v, None{}, True{})), M.nodup(M.order(v)), hi))

def nodup_right(xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +h: {M.nodup(List.append(&2, M.Node, xs, ys)) == True{} : Bool}) -> {M.nodup(ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +x <> +rest:
      nodup_right(rest, ys, Comp.and_right(Bool.not(M.named(List.append(&2, M.Node, rest, ys), M.Node.name(x))), M.nodup(List.append(&2, M.Node, rest, ys)), h))

def nd_split(+v: List<&2, M.Node>, +w: List<&2, M.Node>, +ds: List<&2, M.Node>, +zs: List<&2, M.Node>, +hi: {M.invariant(v) == True{} : Bool}, +hq: {M.visible(v) == List.append(&2, M.Node, List.append(&2, M.Node, w, ds), zs) : List<&2, M.Node>}) -> {M.nodup(List.append(&2, M.Node, w, List.append(&2, M.Node, ds, zs))) == True{} : Bool}:
  %nappend_assoc(w, ds, zs) : {M.nodup(_) == True{} : Bool}
  %hq : {M.nodup(_) == True{} : Bool}
  nd_v(v, hi)

# A delete's targets are not the elements before them, nor after.
def sep_before(+v: List<&2, M.Node>, +w: List<&2, M.Node>, +ds: List<&2, M.Node>, +zs: List<&2, M.Node>, +hi: {M.invariant(v) == True{} : Bool}, +hq: {M.visible(v) == List.append(&2, M.Node, List.append(&2, M.Node, w, ds), zs) : List<&2, M.Node>}) -> {clear(w, dels(ds)) == True{} : Bool}:
  sep_clear_rev(w, ds, sep_left(w, ds, zs, nodup_sep(w, List.append(&2, M.Node, ds, zs), nd_split(v, w, ds, zs, hi, hq))))

def sep_after(+v: List<&2, M.Node>, +w: List<&2, M.Node>, +ds: List<&2, M.Node>, +zs: List<&2, M.Node>, +hi: {M.invariant(v) == True{} : Bool}, +hq: {M.visible(v) == List.append(&2, M.Node, List.append(&2, M.Node, w, ds), zs) : List<&2, M.Node>}) -> {clear(zs, dels(ds)) == True{} : Bool}:
  sep_clear(ds, zs, nodup_sep(ds, zs, nodup_right(w, List.append(&2, M.Node, ds, zs), nd_split(v, w, ds, zs, hi, hq))))

# What a delete targets, the view it cuts no longer reads.
def cuts_del(+acts: List<&2, M.Action>, +w: List<&2, M.Node>, +ds: List<&2, M.Node>, +hw: {clear(w, dels(ds)) == True{} : Bool}, +hd: {clear(ds, acts) == True{} : Bool}) -> {cuts(List.append(&2, M.Action, acts, dels(ds)), List.append(&2, M.Node, w, ds)) == cuts(acts, w) : List<&2, M.Node>}:
  Equal.trans(List<&2, M.Node>, cuts(List.append(&2, M.Action, acts, dels(ds)), List.append(&2, M.Node, w, ds)), List.append(&2, M.Node, cuts(List.append(&2, M.Action, acts, dels(ds)), w), cuts(List.append(&2, M.Action, acts, dels(ds)), ds)), cuts(acts, w), cuts_append(List.append(&2, M.Action, acts, dels(ds)), w, ds), Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, cuts(List.append(&2, M.Action, acts, dels(ds)), w), cuts(List.append(&2, M.Action, acts, dels(ds)), ds)), List.append(&2, M.Node, cuts(acts, w), Nil{}), cuts(acts, w), Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, cuts(List.append(&2, M.Action, acts, dels(ds)), w), cuts(List.append(&2, M.Action, acts, dels(ds)), ds)), List.append(&2, M.Node, cuts(acts, w), cuts(List.append(&2, M.Action, acts, dels(ds)), ds)), List.append(&2, M.Node, cuts(acts, w), Nil{}), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, q => List.append(&2, M.Node, q, cuts(List.append(&2, M.Action, acts, dels(ds)), ds)), cuts(List.append(&2, M.Action, acts, dels(ds)), w), cuts(acts, w), cuts_after(acts, dels(ds), w, hw)), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, q => List.append(&2, M.Node, cuts(acts, w), q), cuts(List.append(&2, M.Action, acts, dels(ds)), ds), Nil{}, Equal.trans(List<&2, M.Node>, cuts(List.append(&2, M.Action, acts, dels(ds)), ds), cuts(dels(ds), cuts(acts, ds)), Nil{}, cuts_seq(acts, dels(ds), ds), Equal.trans(List<&2, M.Node>, cuts(dels(ds), cuts(acts, ds)), cuts(dels(ds), ds), Nil{}, Equal.cong(List<&2, M.Node>, List<&2, M.Node>, q => cuts(dels(ds), q), cuts(acts, ds), ds, cuts_clear(acts, ds, hd)), cuts_gone(dels(ds), ds, gone_dels(ds)))))), AL.append_nil(cuts(acts, w))))

def clear_dz(+acts: List<&2, M.Action>, +P: List<&2, M.Node>, +c: Nat, +a: Nat, +items: List<&2, Ops.Item>, +le: {Nat.is_le(c, a) == True{} : Bool}, +h7: {clear(List.drop(&2, M.Node, P, c), acts) == True{} : Bool}) -> {clear(List.append(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items)))), acts) == True{} : Bool}:
  %dsplit(P, a, items) : {clear(_, acts) == True{} : Bool}
  clear_right(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)), List.drop(&2, M.Node, P, a), acts, h7_gap(acts, P, c, a, le, h7))

# Past a delete the cursor stands after its last target, which is the
# parent's element before the new position; a delete of nothing moves it
# only as far as the gap.
def del_ho(+F: List<&2, M.Node>, +P: List<&2, M.Node>, +c: Nat, +a: Nat, items: List<&2, Ops.Item>, +open: Bool, +ho: {M.left_of(F, List.length(&2, M.Node, F)) == Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, open, M.left_of(P, c), M.left_of(F, List.length(&2, M.Node, F))) : Maybe<&2, Maybe<&2, M.Name>>}, +le: {Nat.is_le(c, a) == True{} : Bool}, +ra: {Nat.is_le(Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P)) == True{} : Bool}) -> {M.left_of(List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), List.length(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))))) == Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open), M.left_of(P, Nat.add(a, List.length(&2, Ops.Item, items))), M.left_of(List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), List.length(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))))) : Maybe<&2, Maybe<&2, M.Name>>}:
  match items:
    case Nil{}:
      %Equal.sym(List<&2, M.Node>, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 0n)), List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 0n)), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), Nil{}), List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, q => List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), q), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 0n), Nil{}, AL.take_zero(List.drop(&2, M.Node, P, a))), AL.append_nil(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))))) : {M.left_of(_, List.length(&2, M.Node, _)) == Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, Bool.or(Nat.is_lt(c, Nat.add(a, 0n)), open), M.left_of(P, Nat.add(a, 0n)), M.left_of(_, List.length(&2, M.Node, _))) : Maybe<&2, Maybe<&2, M.Name>>}
      %Equal.sym(Nat, Nat.add(a, 0n), a, Comp.add_zero(a)) : {M.left_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.length(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))))) == Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, Bool.or(Nat.is_lt(c, _), open), M.left_of(P, _), M.left_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.length(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))))) : Maybe<&2, Maybe<&2, M.Name>>}
      ends_gap(F, P, c, a, open, ho, le, (%Comp.add_zero(a) : {Nat.is_le(_, List.length(&2, M.Node, P)) == True{} : Bool}
        ra))
    case +it <> +more:
      Equal.trans(Maybe<&2, Maybe<&2, M.Name>>, M.left_of(List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 1n+List.length(&2, Ops.Item, more))), List.length(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 1n+List.length(&2, Ops.Item, more))))), M.left_of(P, Nat.add(a, 1n+List.length(&2, Ops.Item, more))), Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, Bool.or(Nat.is_lt(c, Nat.add(a, 1n+List.length(&2, Ops.Item, more))), open), M.left_of(P, Nat.add(a, 1n+List.length(&2, Ops.Item, more))), M.left_of(List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 1n+List.length(&2, Ops.Item, more))), List.length(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 1n+List.length(&2, Ops.Item, more)))))), last_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), P, a, List.length(&2, Ops.Item, more), ra), Equal.sym(Maybe<&2, Maybe<&2, M.Name>>, Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, Bool.or(Nat.is_lt(c, Nat.add(a, 1n+List.length(&2, Ops.Item, more))), open), M.left_of(P, Nat.add(a, 1n+List.length(&2, Ops.Item, more))), M.left_of(List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 1n+List.length(&2, Ops.Item, more))), List.length(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 1n+List.length(&2, Ops.Item, more)))))), M.left_of(P, Nat.add(a, 1n+List.length(&2, Ops.Item, more))), Equal.cong(Bool, Maybe<&2, Maybe<&2, M.Name>>, b => Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, Bool.or(b, open), M.left_of(P, Nat.add(a, 1n+List.length(&2, Ops.Item, more))), M.left_of(List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 1n+List.length(&2, Ops.Item, more))), List.length(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 1n+List.length(&2, Ops.Item, more)))))), Nat.is_lt(c, Nat.add(a, 1n+List.length(&2, Ops.Item, more))), True{}, le_lt_trans(c, a, Nat.add(a, 1n+List.length(&2, Ops.Item, more)), le, Comp.lt_add_succ(a, List.length(&2, Ops.Item, more))))))

# After a replacement the cursor stands after the last target, unless the
# delete was of nothing, and then the event's own elements end the view.
def rep_ho(+w: List<&2, M.Node>, +P: List<&2, M.Node>, +a: Nat, items: List<&2, Ops.Item>, +ra: {Nat.is_le(Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P)) == True{} : Bool}) -> {M.left_of(List.append(&2, M.Node, w, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), List.length(&2, M.Node, List.append(&2, M.Node, w, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))))) == Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))), M.left_of(P, Nat.add(a, List.length(&2, Ops.Item, items))), M.left_of(List.append(&2, M.Node, w, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), List.length(&2, M.Node, List.append(&2, M.Node, w, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))))) : Maybe<&2, Maybe<&2, M.Name>>}:
  match items:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_lt(a, Nat.add(a, 0n)), False{}, (%Equal.sym(Nat, Nat.add(a, 0n), a, Comp.add_zero(a)) : {Nat.is_lt(a, _) == False{} : Bool}
        lt_irrefl(a))) : {M.left_of(List.append(&2, M.Node, w, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 0n)), List.length(&2, M.Node, List.append(&2, M.Node, w, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 0n)))) == Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, _, M.left_of(P, Nat.add(a, 0n)), M.left_of(List.append(&2, M.Node, w, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 0n)), List.length(&2, M.Node, List.append(&2, M.Node, w, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 0n))))) : Maybe<&2, Maybe<&2, M.Name>>}
      {==}
    case +it <> +more:
      Equal.trans(Maybe<&2, Maybe<&2, M.Name>>, M.left_of(List.append(&2, M.Node, w, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 1n+List.length(&2, Ops.Item, more))), List.length(&2, M.Node, List.append(&2, M.Node, w, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 1n+List.length(&2, Ops.Item, more))))), M.left_of(P, Nat.add(a, 1n+List.length(&2, Ops.Item, more))), Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, Nat.is_lt(a, Nat.add(a, 1n+List.length(&2, Ops.Item, more))), M.left_of(P, Nat.add(a, 1n+List.length(&2, Ops.Item, more))), M.left_of(List.append(&2, M.Node, w, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 1n+List.length(&2, Ops.Item, more))), List.length(&2, M.Node, List.append(&2, M.Node, w, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 1n+List.length(&2, Ops.Item, more)))))), last_of(w, P, a, List.length(&2, Ops.Item, more), ra), Equal.sym(Maybe<&2, Maybe<&2, M.Name>>, Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, Nat.is_lt(a, Nat.add(a, 1n+List.length(&2, Ops.Item, more))), M.left_of(P, Nat.add(a, 1n+List.length(&2, Ops.Item, more))), M.left_of(List.append(&2, M.Node, w, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 1n+List.length(&2, Ops.Item, more))), List.length(&2, M.Node, List.append(&2, M.Node, w, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 1n+List.length(&2, Ops.Item, more)))))), M.left_of(P, Nat.add(a, 1n+List.length(&2, Ops.Item, more))), Equal.cong(Bool, Maybe<&2, Maybe<&2, M.Name>>, b => Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, b, M.left_of(P, Nat.add(a, 1n+List.length(&2, Ops.Item, more))), M.left_of(List.append(&2, M.Node, w, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 1n+List.length(&2, Ops.Item, more))), List.length(&2, M.Node, List.append(&2, M.Node, w, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), 1n+List.length(&2, Ops.Item, more)))))), Nat.is_lt(a, Nat.add(a, 1n+List.length(&2, Ops.Item, more))), True{}, Comp.lt_add_succ(a, List.length(&2, Ops.Item, more)))))

def pick_true(b: Bool, -x: Bool, -y: Bool, e: {b == True{} : Bool}, h: {Bool.pick(Bool, b, x, y) == True{} : Bool}) -> {x == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      Empty.absurd({x == True{} : Bool}, Comp.false_true(e))

def pick_false(b: Bool, -x: Bool, -y: Bool, e: {b == False{} : Bool}, h: {Bool.pick(Bool, b, x, y) == True{} : Bool}) -> {y == True{} : Bool}:
  match b:
    case False{}:
      h
    case True{}:
      Empty.absurd({y == True{} : Bool}, ML.true_false(e))

def le_trans(a: Nat, b: Nat, c: Nat, e1: {Nat.is_le(a, b) == True{} : Bool}, e2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      Empty.absurd({True{} == True{} : Bool}, Comp.false_true(e2))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, Comp.false_true(e1))
    case 1n+p 1n+q 0n:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(e2))
    case 1n+p 1n+q 1n+r:
      le_trans(p, q, r, e1, e2)

def file_front(+acts: List<&2, M.Action>, +F: List<&2, M.Node>, +w: List<&2, M.Node>, +O: List<&2, Ops.Item>, h6: {M.file.of(cuts(acts, F)) == O : List<&2, Ops.Item>}) -> {M.file.of(List.append(&2, M.Node, cuts(acts, F), w)) == List.append(&2, Ops.Item, O, M.file.of(w)) : List<&2, Ops.Item>}:
  Equal.trans(List<&2, Ops.Item>, M.file.of(List.append(&2, M.Node, cuts(acts, F), w)), List.append(&2, Ops.Item, M.file.of(cuts(acts, F)), M.file.of(w)), List.append(&2, Ops.Item, O, M.file.of(w)), file_append(cuts(acts, F), w), Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, q => List.append(&2, Ops.Item, q, M.file.of(w)), M.file.of(cuts(acts, F)), O, h6))

def clear_app_list(xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +acts: List<&2, M.Action>, +hx: {clear(xs, acts) == True{} : Bool}, +hy: {clear(ys, acts) == True{} : Bool}) -> {clear(List.append(&2, M.Node, xs, ys), acts) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +x <> +rest:
      AL.and_intro(Bool.not(hit(acts, M.Node.name(x))), clear(List.append(&2, M.Node, rest, ys), acts), Comp.and_left(Bool.not(hit(acts, M.Node.name(x))), clear(rest, acts), hx), clear_app_list(rest, ys, acts, Comp.and_right(Bool.not(hit(acts, M.Node.name(x))), clear(rest, acts), hx), hy))

# The run
# -------
#
# The run of an event's document over its whole view, step by step beside
# `Cursor.walk`: the view is `F` then the parent from the cursor on; the
# event's removals leave out of `F` what the cursor has written, `O`; and
# the tree the actions make is the view with those removals marked. When
# the walk succeeds, so does the run, and it leaves `cf`.
def run_sim(ops: List<&2, Ops.Op>, +c: Nat, +open: Bool, +v: List<&2, M.Node>, +m: Nat, +acts: List<&2, M.Action>, +F: List<&2, M.Node>, +O: List<&2, Ops.Item>, +P: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +t: List<&2, M.Node>, +cf: List<&2, Ops.Item>, +hs: {strict(ops, c, open) == True{} : Bool}, +hr: {Ops.in_range(ops, List.length(&2, M.Node, P)) == True{} : Bool}, +hw: {Cursor.combine(None{}, O, Cursor.walk(ops, c, List.drop(&2, Ops.Item, M.file.of(P), c))) == Done{cf} : Result<&2, &2, String, List<&2, Ops.Item>>}, +hq: {M.visible(v) == List.append(&2, M.Node, F, List.drop(&2, M.Node, P, c)) : List<&2, M.Node>}, +ho: {M.left_of(F, List.length(&2, M.Node, F)) == Bool.pick(Maybe<&2, Maybe<&2, M.Name>>, open, M.left_of(P, c), M.left_of(F, List.length(&2, M.Node, F))) : Maybe<&2, Maybe<&2, M.Name>>}, +hk: {M.has(W, k) == False{} : Bool}, +hpa: {ML.authors_in(P, W) == True{} : Bool}, +hi: {M.invariant(v) == True{} : Bool}, +hg: {goods(v, W, k, m) == True{} : Bool}, +ha: {ML.avoid(acts, k) == True{} : Bool}, +h5: {M.apply(acts, t, k) == mk(acts, v, k) : List<&2, M.Node>}, +h6: {M.file.of(cuts(acts, F)) == O : List<&2, Ops.Item>}, +h7: {clear(List.drop(&2, M.Node, P, c), acts) == True{} : Bool}) -> {fine(M.run(ops, Some{M.Running{v, m, acts}}, k, P), t, W, k, cf) == True{} : Bool}:
  match ops:
    case Nil{}:
      fine_of(v, m, acts, t, W, k, cf, h5, hi, hg, sim_nil(v, acts, F, O, P, c, cf, hq, h6, h7, hw))
    case Ops.Op{Ops.Insert{}, +a, +items} <> +rest:
      %Equal.sym(Maybe<&2, M.Running>, M.run.step(Some{M.Running{v, m, acts}}, Ops.Op{Ops.Insert{}, a, items}, k, P), Some{M.Running{iv(M.inserts(items, v, k, AL.unwrap_left(M.left_of(P, a)), m)), im(M.inserts(items, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.append(&2, M.Action, acts, ML.Inserted.acts(M.inserts(items, v, k, AL.unwrap_left(M.left_of(P, a)), m)))}}, ins_step_eq(v, m, acts, items, a, P, k, AL.unwrap_left(M.left_of(P, a)), left_some(P, a, Comp.and_left(Nat.is_le(a, List.length(&2, M.Node, P)), Ops.in_range(rest, List.length(&2, M.Node, P)), hr)))) : {fine(M.run(rest, _, k, P), t, W, k, cf) == True{} : Bool}
      run_sim(rest, a, False{}, iv(M.inserts(items, v, k, AL.unwrap_left(M.left_of(P, a)), m)), im(M.inserts(items, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.append(&2, M.Action, acts, ML.Inserted.acts(M.inserts(items, v, k, AL.unwrap_left(M.left_of(P, a)), m))), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.append(&2, Ops.Item, List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), items), P, W, k, t, cf,
        Comp.and_right(gap_ok(c, a, open), strict(rest, a, False{}), hs),
        Comp.and_right(Nat.is_le(a, List.length(&2, M.Node, P)), Ops.in_range(rest, List.length(&2, M.Node, P)), hr),
        cur_ins(O, P, c, a, items, rest, cf, gap_le(c, a, open, Comp.and_left(gap_ok(c, a, open), strict(rest, a, False{}), hs)), hw),
        Equal.trans(List<&2, M.Node>, M.visible(iv(M.inserts(items, v, k, AL.unwrap_left(M.left_of(P, a)), m))), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.append(&2, M.Node, fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m), List.drop(&2, M.Node, P, a))), List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.drop(&2, M.Node, P, a)), ins_view(items, v, W, k, AL.unwrap_left(M.left_of(P, a)), m, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.drop(&2, M.Node, P, a), hi, hg, hq_gap(v, F, P, c, a, gap_le(c, a, open, Comp.and_left(gap_ok(c, a, open), strict(rest, a, False{}), hs)), hq), Equal.trans(Maybe<&2, Maybe<&2, M.Name>>, M.left_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.length(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))))), M.left_of(P, a), Some{AL.unwrap_left(M.left_of(P, a))}, ends_ins(F, P, c, a, open, ho, Comp.and_left(gap_ok(c, a, open), strict(rest, a, False{}), hs), Comp.and_left(Nat.is_le(a, List.length(&2, M.Node, P)), Ops.in_range(rest, List.length(&2, M.Node, P)), hr)), left_some(P, a, Comp.and_left(Nat.is_le(a, List.length(&2, M.Node, P)), Ops.in_range(rest, List.length(&2, M.Node, P)), hr)))), Equal.sym(List<&2, M.Node>, List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.drop(&2, M.Node, P, a)), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.append(&2, M.Node, fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m), List.drop(&2, M.Node, P, a))), nappend_assoc(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m), List.drop(&2, M.Node, P, a)))),
        {==},
        hk, hpa,
        ins_hi(items, v, W, k, AL.unwrap_left(M.left_of(P, a)), m, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.drop(&2, M.Node, P, a), hi, hg, hq_gap(v, F, P, c, a, gap_le(c, a, open, Comp.and_left(gap_ok(c, a, open), strict(rest, a, False{}), hs)), hq), Equal.trans(Maybe<&2, Maybe<&2, M.Name>>, M.left_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.length(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))))), M.left_of(P, a), Some{AL.unwrap_left(M.left_of(P, a))}, ends_ins(F, P, c, a, open, ho, Comp.and_left(gap_ok(c, a, open), strict(rest, a, False{}), hs), Comp.and_left(Nat.is_le(a, List.length(&2, M.Node, P)), Ops.in_range(rest, List.length(&2, M.Node, P)), hr)), left_some(P, a, Comp.and_left(Nat.is_le(a, List.length(&2, M.Node, P)), Ops.in_range(rest, List.length(&2, M.Node, P)), hr)))),
        ins_hg(items, v, W, k, AL.unwrap_left(M.left_of(P, a)), m, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.drop(&2, M.Node, P, a), hi, hg, hq_gap(v, F, P, c, a, gap_le(c, a, open, Comp.and_left(gap_ok(c, a, open), strict(rest, a, False{}), hs)), hq), Equal.trans(Maybe<&2, Maybe<&2, M.Name>>, M.left_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.length(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))))), M.left_of(P, a), Some{AL.unwrap_left(M.left_of(P, a))}, ends_ins(F, P, c, a, open, ho, Comp.and_left(gap_ok(c, a, open), strict(rest, a, False{}), hs), Comp.and_left(Nat.is_le(a, List.length(&2, M.Node, P)), Ops.in_range(rest, List.length(&2, M.Node, P)), hr)), left_some(P, a, Comp.and_left(Nat.is_le(a, List.length(&2, M.Node, P)), Ops.in_range(rest, List.length(&2, M.Node, P)), hr)))),
        ML.append_avoid(acts, ML.Inserted.acts(M.inserts(items, v, k, AL.unwrap_left(M.left_of(P, a)), m)), k, ha, ML.inserts_avoid(items, v, k, AL.unwrap_left(M.left_of(P, a)), m, k)),
        ins_h5(t, v, acts, items, k, AL.unwrap_left(M.left_of(P, a)), m, ha, h5),
        Equal.trans(List<&2, Ops.Item>, M.file.of(cuts(List.append(&2, M.Action, acts, ML.Inserted.acts(M.inserts(items, v, k, AL.unwrap_left(M.left_of(P, a)), m))), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m)))), M.file.of(cuts(acts, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m)))), List.append(&2, Ops.Item, List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), items), Equal.cong(List<&2, M.Node>, List<&2, Ops.Item>, q => M.file.of(q), cuts(List.append(&2, M.Action, acts, ML.Inserted.acts(M.inserts(items, v, k, AL.unwrap_left(M.left_of(P, a)), m))), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m))), cuts(acts, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m))), cuts_ia(acts, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m)), items, v, k, AL.unwrap_left(M.left_of(P, a)), m)), Equal.trans(List<&2, Ops.Item>, M.file.of(cuts(acts, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m)))), M.file.of(List.append(&2, M.Node, cuts(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m))), List.append(&2, Ops.Item, List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), items), Equal.cong(List<&2, M.Node>, List<&2, Ops.Item>, q => M.file.of(q), cuts(acts, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m))), List.append(&2, M.Node, cuts(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m)), cuts_fresh(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), items, v, k, AL.unwrap_left(M.left_of(P, a)), m, ha)), Equal.trans(List<&2, Ops.Item>, M.file.of(List.append(&2, M.Node, cuts(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m))), M.file.of(List.append(&2, M.Node, List.append(&2, M.Node, cuts(acts, F), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m))), List.append(&2, Ops.Item, List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), items), Equal.cong(List<&2, M.Node>, List<&2, Ops.Item>, q => M.file.of(List.append(&2, M.Node, q, fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m))), cuts(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), List.append(&2, M.Node, cuts(acts, F), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), cuts_gap(acts, F, P, c, a, gap_le(c, a, open, Comp.and_left(gap_ok(c, a, open), strict(rest, a, False{}), hs)), h7)), Equal.trans(List<&2, Ops.Item>, M.file.of(List.append(&2, M.Node, List.append(&2, M.Node, cuts(acts, F), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m))), List.append(&2, Ops.Item, M.file.of(List.append(&2, M.Node, cuts(acts, F), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), M.file.of(fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m))), List.append(&2, Ops.Item, List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), items), file_append(List.append(&2, M.Node, cuts(acts, F), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m)), Equal.trans(List<&2, Ops.Item>, List.append(&2, Ops.Item, M.file.of(List.append(&2, M.Node, cuts(acts, F), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), M.file.of(fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m))), List.append(&2, Ops.Item, List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), M.file.of(fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m))), List.append(&2, Ops.Item, List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), items), Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, q => List.append(&2, Ops.Item, q, M.file.of(fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m))), M.file.of(List.append(&2, M.Node, cuts(acts, F), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), file_front(acts, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)), O, h6)), Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, q => List.append(&2, Ops.Item, List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), q), M.file.of(fresh_nodes(items, v, k, AL.unwrap_left(M.left_of(P, a)), m)), items, file_fresh(items, v, k, AL.unwrap_left(M.left_of(P, a)), m))))))),
        clear_ia(List.drop(&2, M.Node, P, a), acts, items, v, k, AL.unwrap_left(M.left_of(P, a)), m, clear_right(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)), List.drop(&2, M.Node, P, a), acts, h7_gap(acts, P, c, a, gap_le(c, a, open, Comp.and_left(gap_ok(c, a, open), strict(rest, a, False{}), hs)), h7))))
    case Ops.Op{Ops.Delete{}, +a, +items} <> +rest:
      match rest:
        case Nil{}:
          %Equal.sym(Maybe<&2, M.Running>, M.run.step(Some{M.Running{v, m, acts}}, Ops.Op{Ops.Delete{}, a, items}, k, P), Some{M.Running{v, m, List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))))}}, del_step_eq(v, m, acts, items, a, P, k, cur_del_pm(O, P, c, a, items, Nil{}, cf, hs, hw))) : {fine(M.run(Nil{}, _, k, P), t, W, k, cf) == True{} : Bool}
          run_sim(Nil{}, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open), v, m, List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), P, W, k, t, cf,
            {==},
            Comp.and_right(Nat.is_le(Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P)), Ops.in_range(Nil{}, List.length(&2, M.Node, P)), hr),
            cur_del_w(O, P, c, a, items, Nil{}, cf, hs, hw),
            hq_del(v, F, P, c, a, items, hs, hq),
            del_ho(F, P, c, a, items, open, ho, hs, Comp.and_left(Nat.is_le(Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P)), Ops.in_range(Nil{}, List.length(&2, M.Node, P)), hr)),
            hk, hpa,
            hi,
            hg,
            ML.append_avoid(acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), k, ha, avoid_dels(items, P, a, W, k, hk, hpa, cur_del_pm(O, P, c, a, items, Nil{}, cf, hs, hw))),
            del_h5(t, v, acts, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), k, h5),
            Equal.trans(List<&2, Ops.Item>, M.file.of(cuts(List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))))), M.file.of(cuts(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))))), List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), Equal.cong(List<&2, M.Node>, List<&2, Ops.Item>, q => M.file.of(q), cuts(List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), cuts(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), cuts_del(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), sep_before(v, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))), hi, hq_del(v, F, P, c, a, items, hs, hq)), clear_left(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))), acts, clear_dz(acts, P, c, a, items, hs, h7)))), Equal.trans(List<&2, Ops.Item>, M.file.of(cuts(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))))), M.file.of(List.append(&2, M.Node, cuts(acts, F), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), Equal.cong(List<&2, M.Node>, List<&2, Ops.Item>, q => M.file.of(q), cuts(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), List.append(&2, M.Node, cuts(acts, F), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), cuts_gap(acts, F, P, c, a, hs, h7)), file_front(acts, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)), O, h6))),
            clear_append(List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))), acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), clear_right(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))), acts, clear_dz(acts, P, c, a, items, hs, h7)), sep_after(v, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))), hi, hq_del(v, F, P, c, a, items, hs, hq))))
        case Ops.Op{Ops.Insert{}, +a2, +items2} <> +more:
          AL.bool_cases({fine(M.run(Ops.Op{Ops.Delete{}, a, items} <> Ops.Op{Ops.Insert{}, a2, items2} <> more, Some{M.Running{v, m, acts}}, k, P), t, W, k, cf) == True{} : Bool}, Nat.is_eq(a2, a),
            +e =>
              (%Equal.sym(Nat, a2, a, ML.nat_eq(a2, a, e)) : {fine(M.run(Ops.Op{Ops.Delete{}, a, items} <> Ops.Op{Ops.Insert{}, _, items2} <> more, Some{M.Running{v, m, acts}}, k, P), t, W, k, cf) == True{} : Bool}
              %Equal.sym(Maybe<&2, M.Running>, M.run.step(Some{M.Running{v, m, acts}}, Ops.Op{Ops.Delete{}, a, items}, k, P), Some{M.Running{v, m, List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))))}}, del_step_eq(v, m, acts, items, a, P, k, cur_del_pm(O, P, c, a, items, Ops.Op{Ops.Insert{}, a2, items2} <> more, cf, gap_le(c, a, open, Comp.and_left(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items)))), pick_true(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs))), hw))) : {fine(M.run(more, M.run.step(_, Ops.Op{Ops.Insert{}, a, items2}, k, P), k, P), t, W, k, cf) == True{} : Bool}
              %Equal.sym(Maybe<&2, M.Running>, M.run.step(Some{M.Running{v, m, List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))))}}, Ops.Op{Ops.Insert{}, a, items2}, k, P), Some{M.Running{iv(M.inserts(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), im(M.inserts(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.append(&2, M.Action, List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), ML.Inserted.acts(M.inserts(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)))}}, ins_step_eq(v, m, List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), items2, a, P, k, AL.unwrap_left(M.left_of(P, a)), left_some(P, a, le_trans(a, Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P), Comp.le_add(a, a, List.length(&2, Ops.Item, items), Comp.le_refl(a)), Comp.and_left(Nat.is_le(Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P)), Bool.and(Nat.is_le(a2, List.length(&2, M.Node, P)), Ops.in_range(more, List.length(&2, M.Node, P))), hr))))) : {fine(M.run(more, _, k, P), t, W, k, cf) == True{} : Bool}
              run_sim(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))), iv(M.inserts(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), im(M.inserts(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.append(&2, M.Action, List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), ML.Inserted.acts(M.inserts(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m))), List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), List.append(&2, Ops.Item, List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), items2), P, W, k, t, cf,
                Comp.and_right(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items)))), pick_true(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs)),
                Comp.and_right(Nat.is_le(a2, List.length(&2, M.Node, P)), Ops.in_range(more, List.length(&2, M.Node, P)), Comp.and_right(Nat.is_le(Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P)), Bool.and(Nat.is_le(a2, List.length(&2, M.Node, P)), Ops.in_range(more, List.length(&2, M.Node, P))), hr)),
                cur_rep(List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), P, a2, items2, more, Nat.add(a, List.length(&2, Ops.Item, items)), cf, (%Equal.sym(Nat, a2, a, ML.nat_eq(a2, a, e)) : {Nat.is_le(_, Nat.add(a, List.length(&2, Ops.Item, items))) == True{} : Bool}
                    Comp.le_add(a, a, List.length(&2, Ops.Item, items), Comp.le_refl(a))), (%Equal.sym(Nat, a2, a, ML.nat_eq(a2, a, e)) : {Nat.sub(_, Nat.add(a, List.length(&2, Ops.Item, items))) == 0n : Nat}
                    sub_past(a, List.length(&2, Ops.Item, items))), cur_del_w(O, P, c, a, items, Ops.Op{Ops.Insert{}, a2, items2} <> more, cf, gap_le(c, a, open, Comp.and_left(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items)))), pick_true(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs))), hw)),
                Equal.trans(List<&2, M.Node>, M.visible(iv(M.inserts(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m))), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.append(&2, M.Node, fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m), List.drop(&2, M.Node, P, a))), List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items)))), ins_view(items2, v, W, k, AL.unwrap_left(M.left_of(P, a)), m, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.drop(&2, M.Node, P, a), hi, hg, hq_gap(v, F, P, c, a, gap_le(c, a, open, Comp.and_left(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items)))), pick_true(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs))), hq), Equal.trans(Maybe<&2, Maybe<&2, M.Name>>, M.left_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.length(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))))), M.left_of(P, a), Some{AL.unwrap_left(M.left_of(P, a))}, ends_ins(F, P, c, a, open, ho, Comp.and_left(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items)))), pick_true(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs)), le_trans(a, Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P), Comp.le_add(a, a, List.length(&2, Ops.Item, items), Comp.le_refl(a)), Comp.and_left(Nat.is_le(Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P)), Bool.and(Nat.is_le(a2, List.length(&2, M.Node, P)), Ops.in_range(more, List.length(&2, M.Node, P))), hr))), left_some(P, a, le_trans(a, Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P), Comp.le_add(a, a, List.length(&2, Ops.Item, items), Comp.le_refl(a)), Comp.and_left(Nat.is_le(Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P)), Bool.and(Nat.is_le(a2, List.length(&2, M.Node, P)), Ops.in_range(more, List.length(&2, M.Node, P))), hr))))), Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.append(&2, M.Node, fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m), List.drop(&2, M.Node, P, a))), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.append(&2, M.Node, fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m), List.append(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items)))))), List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items)))), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, q => List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.append(&2, M.Node, fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m), q)), List.drop(&2, M.Node, P, a), List.append(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items)))), dsplit(P, a, items)), Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.append(&2, M.Node, fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m), List.append(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items)))))), List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.append(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))))), List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items)))), Equal.sym(List<&2, M.Node>, List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.append(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))))), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.append(&2, M.Node, fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m), List.append(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items)))))), nappend_assoc(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m), List.append(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items)))))), Equal.sym(List<&2, M.Node>, List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items)))), List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.append(&2, M.Node, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))))), nappend_assoc(List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items)))))))),
                rep_ho(List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), P, a, items, Comp.and_left(Nat.is_le(Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P)), Bool.and(Nat.is_le(a2, List.length(&2, M.Node, P)), Ops.in_range(more, List.length(&2, M.Node, P))), hr)),
                hk, hpa,
                ins_hi(items2, v, W, k, AL.unwrap_left(M.left_of(P, a)), m, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.drop(&2, M.Node, P, a), hi, hg, hq_gap(v, F, P, c, a, gap_le(c, a, open, Comp.and_left(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items)))), pick_true(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs))), hq), Equal.trans(Maybe<&2, Maybe<&2, M.Name>>, M.left_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.length(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))))), M.left_of(P, a), Some{AL.unwrap_left(M.left_of(P, a))}, ends_ins(F, P, c, a, open, ho, Comp.and_left(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items)))), pick_true(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs)), le_trans(a, Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P), Comp.le_add(a, a, List.length(&2, Ops.Item, items), Comp.le_refl(a)), Comp.and_left(Nat.is_le(Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P)), Bool.and(Nat.is_le(a2, List.length(&2, M.Node, P)), Ops.in_range(more, List.length(&2, M.Node, P))), hr))), left_some(P, a, le_trans(a, Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P), Comp.le_add(a, a, List.length(&2, Ops.Item, items), Comp.le_refl(a)), Comp.and_left(Nat.is_le(Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P)), Bool.and(Nat.is_le(a2, List.length(&2, M.Node, P)), Ops.in_range(more, List.length(&2, M.Node, P))), hr))))),
                ins_hg(items2, v, W, k, AL.unwrap_left(M.left_of(P, a)), m, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.drop(&2, M.Node, P, a), hi, hg, hq_gap(v, F, P, c, a, gap_le(c, a, open, Comp.and_left(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items)))), pick_true(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs))), hq), Equal.trans(Maybe<&2, Maybe<&2, M.Name>>, M.left_of(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.length(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))))), M.left_of(P, a), Some{AL.unwrap_left(M.left_of(P, a))}, ends_ins(F, P, c, a, open, ho, Comp.and_left(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items)))), pick_true(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs)), le_trans(a, Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P), Comp.le_add(a, a, List.length(&2, Ops.Item, items), Comp.le_refl(a)), Comp.and_left(Nat.is_le(Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P)), Bool.and(Nat.is_le(a2, List.length(&2, M.Node, P)), Ops.in_range(more, List.length(&2, M.Node, P))), hr))), left_some(P, a, le_trans(a, Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P), Comp.le_add(a, a, List.length(&2, Ops.Item, items), Comp.le_refl(a)), Comp.and_left(Nat.is_le(Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P)), Bool.and(Nat.is_le(a2, List.length(&2, M.Node, P)), Ops.in_range(more, List.length(&2, M.Node, P))), hr))))),
                ML.append_avoid(List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), ML.Inserted.acts(M.inserts(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), k, ML.append_avoid(acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), k, ha, avoid_dels(items, P, a, W, k, hk, hpa, cur_del_pm(O, P, c, a, items, Ops.Op{Ops.Insert{}, a2, items2} <> more, cf, gap_le(c, a, open, Comp.and_left(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items)))), pick_true(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs))), hw))), ML.inserts_avoid(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m, k)),
                ins_h5(t, v, List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), items2, k, AL.unwrap_left(M.left_of(P, a)), m, ML.append_avoid(acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), k, ha, avoid_dels(items, P, a, W, k, hk, hpa, cur_del_pm(O, P, c, a, items, Ops.Op{Ops.Insert{}, a2, items2} <> more, cf, gap_le(c, a, open, Comp.and_left(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items)))), pick_true(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs))), hw))), del_h5(t, v, acts, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), k, h5)),
                Equal.trans(List<&2, Ops.Item>, M.file.of(cuts(List.append(&2, M.Action, List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), ML.Inserted.acts(M.inserts(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m))), List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))))), M.file.of(cuts(List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))))), List.append(&2, Ops.Item, List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), items2), Equal.cong(List<&2, M.Node>, List<&2, Ops.Item>, q => M.file.of(q), cuts(List.append(&2, M.Action, List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), ML.Inserted.acts(M.inserts(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m))), List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), cuts(List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), cuts_ia(List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), Equal.trans(List<&2, Ops.Item>, M.file.of(cuts(List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))))), M.file.of(cuts(acts, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)))), List.append(&2, Ops.Item, List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), items2), Equal.cong(List<&2, M.Node>, List<&2, Ops.Item>, q => M.file.of(q), cuts(List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), List.append(&2, M.Node, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), cuts(acts, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m))), cuts_del(acts, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), clear_app_list(List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m), dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), sep_before(v, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))), hi, hq_del(v, F, P, c, a, items, gap_le(c, a, open, Comp.and_left(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items)))), pick_true(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs))), hq)), clear_fresh(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), avoid_dels(items, P, a, W, k, hk, hpa, cur_del_pm(O, P, c, a, items, Ops.Op{Ops.Insert{}, a2, items2} <> more, cf, gap_le(c, a, open, Comp.and_left(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items)))), pick_true(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs))), hw)))), clear_left(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))), acts, clear_dz(acts, P, c, a, items, gap_le(c, a, open, Comp.and_left(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items)))), pick_true(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs))), h7)))), Equal.trans(List<&2, Ops.Item>, M.file.of(cuts(acts, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)))), M.file.of(List.append(&2, M.Node, cuts(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m))), List.append(&2, Ops.Item, List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), items2), Equal.cong(List<&2, M.Node>, List<&2, Ops.Item>, q => M.file.of(q), cuts(acts, List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m))), List.append(&2, M.Node, cuts(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), cuts_fresh(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), items2, v, k, AL.unwrap_left(M.left_of(P, a)), m, ha)), Equal.trans(List<&2, Ops.Item>, M.file.of(List.append(&2, M.Node, cuts(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m))), M.file.of(List.append(&2, M.Node, List.append(&2, M.Node, cuts(acts, F), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m))), List.append(&2, Ops.Item, List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), items2), Equal.cong(List<&2, M.Node>, List<&2, Ops.Item>, q => M.file.of(List.append(&2, M.Node, q, fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m))), cuts(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), List.append(&2, M.Node, cuts(acts, F), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), cuts_gap(acts, F, P, c, a, gap_le(c, a, open, Comp.and_left(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items)))), pick_true(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs))), h7)), Equal.trans(List<&2, Ops.Item>, M.file.of(List.append(&2, M.Node, List.append(&2, M.Node, cuts(acts, F), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m))), List.append(&2, Ops.Item, M.file.of(List.append(&2, M.Node, cuts(acts, F), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), M.file.of(fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m))), List.append(&2, Ops.Item, List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), items2), file_append(List.append(&2, M.Node, cuts(acts, F), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), Equal.trans(List<&2, Ops.Item>, List.append(&2, Ops.Item, M.file.of(List.append(&2, M.Node, cuts(acts, F), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), M.file.of(fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m))), List.append(&2, Ops.Item, List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), M.file.of(fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m))), List.append(&2, Ops.Item, List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), items2), Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, q => List.append(&2, Ops.Item, q, M.file.of(fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m))), M.file.of(List.append(&2, M.Node, cuts(acts, F), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), file_front(acts, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)), O, h6)), Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, q => List.append(&2, Ops.Item, List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), q), M.file.of(fresh_nodes(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)), items2, file_fresh(items2, v, k, AL.unwrap_left(M.left_of(P, a)), m)))))))),
                clear_ia(List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))), List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), items2, v, k, AL.unwrap_left(M.left_of(P, a)), m, clear_append(List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))), acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), clear_right(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))), acts, clear_dz(acts, P, c, a, items, gap_le(c, a, open, Comp.and_left(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items)))), pick_true(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs))), h7)), sep_after(v, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))), hi, hq_del(v, F, P, c, a, items, gap_le(c, a, open, Comp.and_left(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items)))), pick_true(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs))), hq)))))),
            +e => (
              %Equal.sym(Maybe<&2, M.Running>, M.run.step(Some{M.Running{v, m, acts}}, Ops.Op{Ops.Delete{}, a, items}, k, P), Some{M.Running{v, m, List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))))}}, del_step_eq(v, m, acts, items, a, P, k, cur_del_pm(O, P, c, a, items, Ops.Op{Ops.Insert{}, a2, items2} <> more, cf, Comp.and_left(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), pick_false(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs)), hw))) : {fine(M.run(Ops.Op{Ops.Insert{}, a2, items2} <> more, _, k, P), t, W, k, cf) == True{} : Bool}
              run_sim(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open), v, m, List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), P, W, k, t, cf,
                Comp.and_right(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), pick_false(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs)),
                Comp.and_right(Nat.is_le(Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P)), Ops.in_range(Ops.Op{Ops.Insert{}, a2, items2} <> more, List.length(&2, M.Node, P)), hr),
                cur_del_w(O, P, c, a, items, Ops.Op{Ops.Insert{}, a2, items2} <> more, cf, Comp.and_left(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), pick_false(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs)), hw),
                hq_del(v, F, P, c, a, items, Comp.and_left(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), pick_false(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs)), hq),
                del_ho(F, P, c, a, items, open, ho, Comp.and_left(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), pick_false(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs)), Comp.and_left(Nat.is_le(Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P)), Ops.in_range(Ops.Op{Ops.Insert{}, a2, items2} <> more, List.length(&2, M.Node, P)), hr)),
                hk, hpa,
                hi,
                hg,
                ML.append_avoid(acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), k, ha, avoid_dels(items, P, a, W, k, hk, hpa, cur_del_pm(O, P, c, a, items, Ops.Op{Ops.Insert{}, a2, items2} <> more, cf, Comp.and_left(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), pick_false(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs)), hw))),
                del_h5(t, v, acts, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), k, h5),
                Equal.trans(List<&2, Ops.Item>, M.file.of(cuts(List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))))), M.file.of(cuts(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))))), List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), Equal.cong(List<&2, M.Node>, List<&2, Ops.Item>, q => M.file.of(q), cuts(List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), cuts(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), cuts_del(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), sep_before(v, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))), hi, hq_del(v, F, P, c, a, items, Comp.and_left(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), pick_false(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs)), hq)), clear_left(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))), acts, clear_dz(acts, P, c, a, items, Comp.and_left(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), pick_false(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs)), h7)))), Equal.trans(List<&2, Ops.Item>, M.file.of(cuts(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))))), M.file.of(List.append(&2, M.Node, cuts(acts, F), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), Equal.cong(List<&2, M.Node>, List<&2, Ops.Item>, q => M.file.of(q), cuts(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), List.append(&2, M.Node, cuts(acts, F), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), cuts_gap(acts, F, P, c, a, Comp.and_left(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), pick_false(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs)), h7)), file_front(acts, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)), O, h6))),
                clear_append(List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))), acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), clear_right(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))), acts, clear_dz(acts, P, c, a, items, Comp.and_left(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), pick_false(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs)), h7)), sep_after(v, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))), hi, hq_del(v, F, P, c, a, items, Comp.and_left(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), pick_false(Nat.is_eq(a2, a), Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))), e, hs)), hq))))))
        case Ops.Op{Ops.Delete{}, +a2, +items2} <> +more:
          %Equal.sym(Maybe<&2, M.Running>, M.run.step(Some{M.Running{v, m, acts}}, Ops.Op{Ops.Delete{}, a, items}, k, P), Some{M.Running{v, m, List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))))}}, del_step_eq(v, m, acts, items, a, P, k, cur_del_pm(O, P, c, a, items, Ops.Op{Ops.Delete{}, a2, items2} <> more, cf, Comp.and_left(Nat.is_le(c, a), strict(Ops.Op{Ops.Delete{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), hs), hw))) : {fine(M.run(Ops.Op{Ops.Delete{}, a2, items2} <> more, _, k, P), t, W, k, cf) == True{} : Bool}
          run_sim(Ops.Op{Ops.Delete{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open), v, m, List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), P, W, k, t, cf,
            Comp.and_right(Nat.is_le(c, a), strict(Ops.Op{Ops.Delete{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), hs),
            Comp.and_right(Nat.is_le(Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P)), Ops.in_range(Ops.Op{Ops.Delete{}, a2, items2} <> more, List.length(&2, M.Node, P)), hr),
            cur_del_w(O, P, c, a, items, Ops.Op{Ops.Delete{}, a2, items2} <> more, cf, Comp.and_left(Nat.is_le(c, a), strict(Ops.Op{Ops.Delete{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), hs), hw),
            hq_del(v, F, P, c, a, items, Comp.and_left(Nat.is_le(c, a), strict(Ops.Op{Ops.Delete{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), hs), hq),
            del_ho(F, P, c, a, items, open, ho, Comp.and_left(Nat.is_le(c, a), strict(Ops.Op{Ops.Delete{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), hs), Comp.and_left(Nat.is_le(Nat.add(a, List.length(&2, Ops.Item, items)), List.length(&2, M.Node, P)), Ops.in_range(Ops.Op{Ops.Delete{}, a2, items2} <> more, List.length(&2, M.Node, P)), hr)),
            hk, hpa,
            hi,
            hg,
            ML.append_avoid(acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), k, ha, avoid_dels(items, P, a, W, k, hk, hpa, cur_del_pm(O, P, c, a, items, Ops.Op{Ops.Delete{}, a2, items2} <> more, cf, Comp.and_left(Nat.is_le(c, a), strict(Ops.Op{Ops.Delete{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), hs), hw))),
            del_h5(t, v, acts, List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), k, h5),
            Equal.trans(List<&2, Ops.Item>, M.file.of(cuts(List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))))), M.file.of(cuts(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))))), List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), Equal.cong(List<&2, M.Node>, List<&2, Ops.Item>, q => M.file.of(q), cuts(List.append(&2, M.Action, acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), List.append(&2, M.Node, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)))), cuts(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), cuts_del(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), sep_before(v, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))), hi, hq_del(v, F, P, c, a, items, Comp.and_left(Nat.is_le(c, a), strict(Ops.Op{Ops.Delete{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), hs), hq)), clear_left(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))), acts, clear_dz(acts, P, c, a, items, Comp.and_left(Nat.is_le(c, a), strict(Ops.Op{Ops.Delete{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), hs), h7)))), Equal.trans(List<&2, Ops.Item>, M.file.of(cuts(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))))), M.file.of(List.append(&2, M.Node, cuts(acts, F), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), List.append(&2, Ops.Item, O, M.file.of(List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), Equal.cong(List<&2, M.Node>, List<&2, Ops.Item>, q => M.file.of(q), cuts(acts, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)))), List.append(&2, M.Node, cuts(acts, F), List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), cuts_gap(acts, F, P, c, a, Comp.and_left(Nat.is_le(c, a), strict(Ops.Op{Ops.Delete{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), hs), h7)), file_front(acts, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c)), O, h6))),
            clear_append(List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))), acts, dels(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items))), clear_right(List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))), acts, clear_dz(acts, P, c, a, items, Comp.and_left(Nat.is_le(c, a), strict(Ops.Op{Ops.Delete{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), hs), h7)), sep_after(v, List.append(&2, M.Node, F, List.take(&2, M.Node, List.drop(&2, M.Node, P, c), Nat.sub(a, c))), List.take(&2, M.Node, List.drop(&2, M.Node, P, a), List.length(&2, Ops.Item, items)), List.drop(&2, M.Node, P, Nat.add(a, List.length(&2, Ops.Item, items))), hi, hq_del(v, F, P, c, a, items, Comp.and_left(Nat.is_le(c, a), strict(Ops.Op{Ops.Delete{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), hs), hq))))

# One event
# ---------

def clear_nil(xs: List<&2, M.Node>) -> {clear(xs, Nil{}) == True{} : Bool}:
  clear_attaches(xs, Nil{}, {==})

# An event of the chain, over a tree bounded by it: when the cursor walk
# of its document succeeds, its run leaves what the walk wrote.
def step_fine(+t: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +d: List<&2, Ops.Op>, +cf: List<&2, Ops.Item>, +hi: {M.invariant(t) == True{} : Bool}, +hn: {inw(t, W) == True{} : Bool}, +hk: {M.has(W, k) == False{} : Bool}, +hs: {strict(d, 0n, True{}) == True{} : Bool}, +hr: {Ops.in_range(d, List.length(&2, M.Node, M.visible(t))) == True{} : Bool}, +hw: {Cursor.walk(d, 0n, M.file(t)) == Done{cf} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {fine(M.run(d, Some{M.Running{M.restrict(t, W), 0n, Nil{}}}, k, M.visible(M.restrict(t, W))), t, W, k, cf) == True{} : Bool}:
  %Equal.sym(List<&2, M.Node>, M.restrict(t, W), t, restrict_id(t, W, hn)) : {fine(M.run(d, Some{M.Running{_, 0n, Nil{}}}, k, M.visible(_)), t, W, k, cf) == True{} : Bool}
  run_sim(d, 0n, True{}, t, 0n, Nil{}, Nil{}, Nil{}, M.visible(t), W, k, t, cf,
    hs, hr,
    (%Equal.sym(List<&2, Ops.Item>, List.drop(&2, Ops.Item, M.file.of(M.visible(t)), 0n), M.file.of(M.visible(t)), idrop_zero(M.file.of(M.visible(t)))) : {Cursor.combine(None{}, Nil{}, Cursor.walk(d, 0n, _)) == Done{cf} : Result<&2, &2, String, List<&2, Ops.Item>>}
      Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.combine(None{}, Nil{}, Cursor.walk(d, 0n, M.file(t))), Cursor.walk(d, 0n, M.file(t)), Done{cf}, L.combine_nil(Cursor.walk(d, 0n, M.file(t))), hw)),
    Equal.sym(List<&2, M.Node>, List.drop(&2, M.Node, M.visible(t), 0n), M.visible(t), AL.drop_zero(M.visible(t))),
    {==}, hk,
    (%restrict_id(t, W, hn) : {ML.authors_in(M.visible(_), W) == True{} : Bool}
      ML.visible_authors(t, W)),
    hi, inw_goods(t, W, k, hk, hn), {==}, {==}, {==}, clear_nil(List.drop(&2, M.Node, M.visible(t), 0n)))

# What a finished event leaves, with the facts `fine` records of it.
def after_fine(st: Maybe<&2, M.Running>, +t: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +cf: List<&2, Ops.Item>, -rest: List<&2, Nat>, -g: List<&2, M.Rev>, -f: List<&2, Ops.Item>, +h: {fine(st, t, W, k, cf) == True{} : Bool}, ih: @u: List<&2, M.Node> -> {M.invariant(u) == True{} : Bool} -> {inw(u, k <> W) == True{} : Bool} -> {M.file(u) == cf : List<&2, Ops.Item>} -> {M.merged.of(M.walk(rest, g, Some{u})) == Some{f} : Maybe<&2, List<&2, Ops.Item>>}) -> {M.merged.of(M.walk(rest, g, M.step.of(t, k, M.run.acts(st)))) == Some{f} : Maybe<&2, List<&2, Ops.Item>>}:
  match st:
    case None{}:
      Empty.absurd({M.merged.of(M.walk(rest, g, None{})) == Some{f} : Maybe<&2, List<&2, Ops.Item>>}, Comp.false_true(h))
    case Some{M.Running{v, m, +acts}}:
      ih(M.apply(acts, t, k),
        Comp.and_left(M.invariant(M.apply(acts, t, k)), Bool.and(inw(M.apply(acts, t, k), k <> W), items_eq(M.file(M.apply(acts, t, k)), cf)), h),
        Comp.and_left(inw(M.apply(acts, t, k), k <> W), items_eq(M.file(M.apply(acts, t, k)), cf), Comp.and_right(M.invariant(M.apply(acts, t, k)), Bool.and(inw(M.apply(acts, t, k), k <> W), items_eq(M.file(M.apply(acts, t, k)), cf)), h)),
        items_eq_equal(M.file(M.apply(acts, t, k)), cf, Comp.and_right(inw(M.apply(acts, t, k), k <> W), items_eq(M.file(M.apply(acts, t, k)), cf), Comp.and_right(M.invariant(M.apply(acts, t, k)), Bool.and(inw(M.apply(acts, t, k), k <> W), items_eq(M.file(M.apply(acts, t, k)), cf)), h))))

# The chain
# ---------
#
# Plain replay by the cursor specification: `Merge.replay` with
# `Cursor.apply` for `Ops.apply`, which `LAWS.cursor_apply_equivalent`
# says is the same thing.
def creplay(docs: List<&2, List<&2, Ops.Op>>, r: Result<&2, &2, String, List<&2, Ops.Item>>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match docs r:
    case _ Fail{e}:
      Fail{e}
    case Nil{} Done{f}:
      Done{f}
    case d <> ds Done{f}:
      creplay(ds, Cursor.apply(f, Ops.Doc{None{}, None{}, d}))

def all_strict(docs: List<&2, List<&2, Ops.Op>>) -> Bool:
  match docs:
    case Nil{}:
      True{}
    case d <> ds:
      Bool.and(strict(d, 0n, True{}), all_strict(ds))

def is_done(r: Result<&2, &2, String, List<&2, Ops.Item>>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{x}:
      True{}

def creplay_done(ds: List<&2, List<&2, Ops.Op>>, r: Result<&2, &2, String, List<&2, Ops.Item>>, -f: List<&2, Ops.Item>, e: {creplay(ds, r) == Done{f} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {is_done(r) == True{} : Bool}:
  match ds r:
    case Nil{} Fail{m}:
      Empty.absurd({False{} == True{} : Bool}, (%e : {rdisc(_) : Type}
        Unit{}))
    case Nil{} Done{x}:
      {==}
    case d <> rest Fail{m}:
      Empty.absurd({False{} == True{} : Bool}, (%e : {rdisc(_) : Type}
        Unit{}))
    case d <> rest Done{x}:
      {==}

def done_eq(r: Result<&2, &2, String, List<&2, Ops.Item>>, h: {is_done(r) == True{} : Bool}) -> {r == Done{done_or(r, Nil{})} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match r:
    case Fail{m}:
      Empty.absurd({Fail{m} == Done{Nil{}} : Result<&2, &2, String, List<&2, Ops.Item>>}, Comp.false_true(h))
    case Done{x}:
      {==}

def checked_range(b: Bool, -w: Result<&2, &2, String, List<&2, Ops.Item>>, -x: List<&2, Ops.Item>, e: {Cursor.checked(b, None{}, w) == Done{x} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, (%e : {rdisc(_) : Type}
        Unit{}))

def after_done(+y: List<&2, Ops.Item>, tb: Bool, -x: List<&2, Ops.Item>, e: {Diff.after_checks(y, tb, Done{Unit{}}) == Done{x} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Done{y} == Done{x} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match tb:
    case True{}:
      e
    case False{}:
      Empty.absurd({Done{y} == Done{x} : Result<&2, &2, String, List<&2, Ops.Item>>}, (%e : {rdisc(_) : Type}
        Unit{}))

def checked_walk(w: Result<&2, &2, String, List<&2, Ops.Item>>, -x: List<&2, Ops.Item>, e: {Cursor.checked(True{}, None{}, w) == Done{x} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {w == Done{x} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match w:
    case Fail{m}:
      Empty.absurd({Fail{m} == Done{x} : Result<&2, &2, String, List<&2, Ops.Item>>}, (%e : {rdisc(_) : Type}
        Unit{}))
    case Done{+y}:
      after_done(y, Ops.terminated_but_last(y), x, e)

def gget_drop(-A: Data, xs: List<&2, A>, a: Nat, -i: Nat) -> {List.get(&2, A, List.drop(&2, A, xs, a), i) == List.get(&2, A, xs, Nat.add(a, i)) : Maybe<&2, A>}:
  match xs a:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      gget_drop(A, t, p, i)

def gdrop_drop(-A: Data, n: Nat, xs: List<&2, A>, m: Nat) -> {List.drop(&2, A, List.drop(&2, A, xs, n), m) == List.drop(&2, A, xs, Nat.add(n, m)) : List<&2, A>}:
  match n xs:
    case 0n Nil{}:
      {==}
    case 0n h <> t:
      {==}
    case 1n+p Nil{}:
      match m:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p h <> t:
      gdrop_drop(A, p, t, m)

def gdrop_zero(-A: Data, xs: List<&2, A>) -> {List.drop(&2, A, xs, 0n) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

def rget_at(+g: List<&2, M.Rev>, +j: Nat, +x: M.Rev, +xs: List<&2, M.Rev>, e: {List.drop(&2, M.Rev, g, j) == x <> xs : List<&2, M.Rev>}) -> {List.get(&2, M.Rev, g, j) == Some{x} : Maybe<&2, M.Rev>}:
  Equal.trans(Maybe<&2, M.Rev>, List.get(&2, M.Rev, g, j), List.get(&2, M.Rev, g, Nat.add(j, 0n)), Some{x},
    Equal.cong(Nat, Maybe<&2, M.Rev>, i => List.get(&2, M.Rev, g, i), j, Nat.add(j, 0n), Equal.sym(Nat, Nat.add(j, 0n), j, Comp.add_zero(j))),
    Equal.trans(Maybe<&2, M.Rev>, List.get(&2, M.Rev, g, Nat.add(j, 0n)), List.get(&2, M.Rev, List.drop(&2, M.Rev, g, j), 0n), Some{x},
      Equal.sym(Maybe<&2, M.Rev>, List.get(&2, M.Rev, List.drop(&2, M.Rev, g, j), 0n), List.get(&2, M.Rev, g, Nat.add(j, 0n)), gget_drop(M.Rev, g, j, 0n)),
      Equal.cong(List<&2, M.Rev>, Maybe<&2, M.Rev>, l => List.get(&2, M.Rev, l, 0n), List.drop(&2, M.Rev, g, j), x <> xs, e)))

def rdrop_next(+g: List<&2, M.Rev>, +j: Nat, +x: M.Rev, +xs: List<&2, M.Rev>, e: {List.drop(&2, M.Rev, g, j) == x <> xs : List<&2, M.Rev>}) -> {List.drop(&2, M.Rev, g, 1n+j) == xs : List<&2, M.Rev>}:
  Equal.trans(List<&2, M.Rev>, List.drop(&2, M.Rev, g, 1n+j), List.drop(&2, M.Rev, g, Nat.add(j, 1n)), xs,
    Equal.cong(Nat, List<&2, M.Rev>, i => List.drop(&2, M.Rev, g, i), 1n+j, Nat.add(j, 1n), one_add(j)),
    Equal.trans(List<&2, M.Rev>, List.drop(&2, M.Rev, g, Nat.add(j, 1n)), List.drop(&2, M.Rev, List.drop(&2, M.Rev, g, j), 1n), xs,
      Equal.sym(List<&2, M.Rev>, List.drop(&2, M.Rev, List.drop(&2, M.Rev, g, j), 1n), List.drop(&2, M.Rev, g, Nat.add(j, 1n)), gdrop_drop(M.Rev, j, g, 1n)),
      Equal.trans(List<&2, M.Rev>, List.drop(&2, M.Rev, List.drop(&2, M.Rev, g, j), 1n), List.drop(&2, M.Rev, xs, 0n), xs,
        Equal.cong(List<&2, M.Rev>, List<&2, M.Rev>, l => List.drop(&2, M.Rev, l, 1n), List.drop(&2, M.Rev, g, j), x <> xs, e),
        gdrop_zero(M.Rev, xs))))

# The walk from event `j` on, over a tree the first `j` events left.
def chain_go(ds: List<&2, List<&2, Ops.Op>>, +g: List<&2, M.Rev>, +j: Nat, +t: List<&2, M.Node>, -f: List<&2, Ops.Item>, +hd: {List.drop(&2, M.Rev, g, j) == M.chain.go(ds, j) : List<&2, M.Rev>}, +hi: {M.invariant(t) == True{} : Bool}, +hn: {inw(t, M.upto(j)) == True{} : Bool}, +ho: {all_strict(ds) == True{} : Bool}, +e: {creplay(ds, Done{M.file(t)}) == Done{f} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {M.merged.of(M.walk(M.upto.go(List.length(&2, List<&2, Ops.Op>, ds), j), g, Some{t})) == Some{f} : Maybe<&2, List<&2, Ops.Item>>}:
  match ds:
    case Nil{}:
      Equal.cong(List<&2, Ops.Item>, Maybe<&2, List<&2, Ops.Item>>, x => Some{x}, M.file(t), f, done_inj(M.file(t), f, e))
    case +d <> +rest:
      %Equal.sym(Maybe<&2, M.Rev>, List.get(&2, M.Rev, g, j), Some{M.Rev{M.upto(j), Some{M.Edits{d}}}}, rget_at(g, j, M.Rev{M.upto(j), Some{M.Edits{d}}}, M.chain.go(rest, 1n+j), hd)) : {M.merged.of(M.walk(M.upto.go(List.length(&2, List<&2, Ops.Op>, rest), 1n+j), g, M.step.m(Some{t}, _, j))) == Some{f} : Maybe<&2, List<&2, Ops.Item>>}
      after_fine(M.run(d, Some{M.Running{M.restrict(t, M.upto(j)), 0n, Nil{}}}, j, M.visible(M.restrict(t, M.upto(j)))), t, M.upto(j), j, done_or(Cursor.apply(M.file(t), Ops.Doc{None{}, None{}, d}), Nil{}), M.upto.go(List.length(&2, List<&2, Ops.Op>, rest), 1n+j), g, f,
        step_fine(t, M.upto(j), j, d, done_or(Cursor.apply(M.file(t), Ops.Doc{None{}, None{}, d}), Nil{}), hi, hn, not_seen_self(j),
          Comp.and_left(strict(d, 0n, True{}), all_strict(rest), ho),
          (%len_file(M.visible(t)) : {Ops.in_range(d, _) == True{} : Bool}
            checked_range(Ops.in_range(d, List.length(&2, Ops.Item, M.file(t))), Cursor.walk(d, 0n, M.file(t)), done_or(Cursor.apply(M.file(t), Ops.Doc{None{}, None{}, d}), Nil{}), done_eq(Cursor.apply(M.file(t), Ops.Doc{None{}, None{}, d}), creplay_done(rest, Cursor.apply(M.file(t), Ops.Doc{None{}, None{}, d}), f, e)))),
          checked_walk(Cursor.walk(d, 0n, M.file(t)), done_or(Cursor.apply(M.file(t), Ops.Doc{None{}, None{}, d}), Nil{}), (%checked_range(Ops.in_range(d, List.length(&2, Ops.Item, M.file(t))), Cursor.walk(d, 0n, M.file(t)), done_or(Cursor.apply(M.file(t), Ops.Doc{None{}, None{}, d}), Nil{}), done_eq(Cursor.apply(M.file(t), Ops.Doc{None{}, None{}, d}), creplay_done(rest, Cursor.apply(M.file(t), Ops.Doc{None{}, None{}, d}), f, e))) : {Cursor.checked(_, None{}, Cursor.walk(d, 0n, M.file(t))) == Done{done_or(Cursor.apply(M.file(t), Ops.Doc{None{}, None{}, d}), Nil{})} : Result<&2, &2, String, List<&2, Ops.Item>>}
            done_eq(Cursor.apply(M.file(t), Ops.Doc{None{}, None{}, d}), creplay_done(rest, Cursor.apply(M.file(t), Ops.Doc{None{}, None{}, d}), f, e))))),
        +u => h1 => h2 => h3 => chain_go(rest, g, 1n+j, u, f, rdrop_next(g, j, M.Rev{M.upto(j), Some{M.Edits{d}}}, M.chain.go(rest, 1n+j), hd), h1, inw_sub(u, j <> M.upto(j), M.upto(1n+j), upto_step(j), h2), Comp.and_right(strict(d, 0n, True{}), all_strict(rest), ho),
          (%Equal.sym(List<&2, Ops.Item>, M.file(u), done_or(Cursor.apply(M.file(t), Ops.Doc{None{}, None{}, d}), Nil{}), h3) : {creplay(rest, Done{_}) == Done{f} : Result<&2, &2, String, List<&2, Ops.Item>>}
            Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, creplay(rest, Done{done_or(Cursor.apply(M.file(t), Ops.Doc{None{}, None{}, d}), Nil{})}), creplay(rest, Cursor.apply(M.file(t), Ops.Doc{None{}, None{}, d})), Done{f}, Equal.cong(Result<&2, &2, String, List<&2, Ops.Item>>, Result<&2, &2, String, List<&2, Ops.Item>>, x => creplay(rest, x), Done{done_or(Cursor.apply(M.file(t), Ops.Doc{None{}, None{}, d}), Nil{})}, Cursor.apply(M.file(t), Ops.Doc{None{}, None{}, d}), Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.apply(M.file(t), Ops.Doc{None{}, None{}, d}), Done{done_or(Cursor.apply(M.file(t), Ops.Doc{None{}, None{}, d}), Nil{})}, done_eq(Cursor.apply(M.file(t), Ops.Doc{None{}, None{}, d}), creplay_done(rest, Cursor.apply(M.file(t), Ops.Doc{None{}, None{}, d}), f, e)))), e))))

# On one line of history, with each document ordered as the run needs,
# the merge walk reads what the cursor replay wrote.
def merge_linear_c(+docs: List<&2, List<&2, Ops.Op>>, -f: List<&2, Ops.Item>, +ho: {all_strict(docs) == True{} : Bool}, +e: {creplay(docs, Done{Nil{}}) == Done{f} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {M.merged(M.chain(docs), M.upto(List.length(&2, List<&2, Ops.Op>, docs))) == Some{f} : Maybe<&2, List<&2, Ops.Item>>}:
  chain_go(docs, M.chain(docs), 0n, Nil{}, f, gdrop_zero(M.Rev, M.chain(docs)), AL.invariant_nil(), {==}, ho, e)

# The parser's order is the run's
# --------------------------------
#
# What `Ops.next_op.bounded` demands of each operation (`Block.ordered_all`)
# is at least what the run needs (`strict`): an insert never lands where the
# event has just written, because the parser refuses two inserts at one
# position and a delete after an insert at one position.
def del_at(prev: Maybe<&2, Ops.Op>, +x: Nat) -> Bool:
  match prev:
    case None{}:
      False{}
    case Some{Ops.Op{Ops.Delete{}, at, items}}:
      Nat.is_eq(x, at)
    case Some{Ops.Op{Ops.Insert{}, at, items}}:
      False{}

# Whether the operations start with an insert at the delete just made.
def rep_head(prev: Maybe<&2, Ops.Op>, ops: List<&2, Ops.Op>) -> Bool:
  match ops:
    case Nil{}:
      False{}
    case Ops.Op{Ops.Insert{}, +x, its} <> rest:
      del_at(prev, x)
    case Ops.Op{Ops.Delete{}, x, its} <> rest:
      False{}

def rep_after_ins(-a: Nat, -items: List<&2, Ops.Item>, ops: List<&2, Ops.Op>) -> {rep_head(Some{Ops.Op{Ops.Insert{}, a, items}}, ops) == False{} : Bool}:
  match ops:
    case Nil{}:
      {==}
    case Ops.Op{Ops.Insert{}, x, its} <> rest:
      {==}
    case Ops.Op{Ops.Delete{}, x, its} <> rest:
      {==}

def rep_none(ops: List<&2, Ops.Op>) -> {rep_head(None{}, ops) == False{} : Bool}:
  match ops:
    case Nil{}:
      {==}
    case Ops.Op{Ops.Insert{}, x, its} <> rest:
      {==}
    case Ops.Op{Ops.Delete{}, x, its} <> rest:
      {==}

def lt_le_trans(a: Nat, b: Nat, c: Nat, e1: {Nat.is_lt(a, b) == True{} : Bool}, e2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n _:
      Empty.absurd({Nat.is_lt(0n, c) == True{} : Bool}, Comp.false_true(e1))
    case 0n 1n+q 0n:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(e2))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      Empty.absurd({Nat.is_lt(1n+p, c) == True{} : Bool}, Comp.false_true(e1))
    case 1n+p 1n+q 0n:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(e2))
    case 1n+p 1n+q 1n+r:
      lt_le_trans(p, q, r, e1, e2)

# Past a delete the insert-at-the-cursor case is open: the cursor either
# moved, or stood where nothing had been written.
def or_open(+c: Nat, +a: Nat, +items: List<&2, Ops.Item>, open: Bool, gap: {gap_ok(c, a, open) == True{} : Bool}) -> {Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open) == True{} : Bool}:
  match open:
    case True{}:
      AL.or_right(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), True{}, {==})
    case False{}:
      AL.or_left(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), False{}, lt_le_trans(c, a, Nat.add(a, List.length(&2, Ops.Item, items)), gap, Comp.le_add(a, a, List.length(&2, Ops.Item, items), Comp.le_refl(a))))

def k_after_del(+c: Nat, +a: Nat, +items: List<&2, Ops.Item>, +open: Bool, +gap: {gap_ok(c, a, open) == True{} : Bool}, +v: Ops.Verb, +x: Nat, +its: List<&2, Ops.Item>, +h1: {Maybe.is_none(&2, String, Ops.ordered(Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.Op{v, x, its})) == True{} : Bool}, +h3: {Bool.and(Ops.verb_is(v, Ops.Insert{}), del_at(Some{Ops.Op{Ops.Delete{}, a, items}}, x)) == False{} : Bool}) -> {gap_ok(Nat.add(a, List.length(&2, Ops.Item, items)), x, Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)) == True{} : Bool}:
  %Equal.sym(Bool, Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open), True{}, or_open(c, a, items, open, gap)) : {gap_ok(Nat.add(a, List.length(&2, Ops.Item, items)), x, _) == True{} : Bool}
  AL.bool_cases({Nat.is_le(Nat.add(a, List.length(&2, Ops.Item, items)), x) == True{} : Bool}, Nat.is_eq(x, a),
    +eb => Empty.absurd({Nat.is_le(Nat.add(a, List.length(&2, Ops.Item, items)), x) == True{} : Bool}, ML.true_false(Equal.trans(Bool, True{}, Bool.and(Ops.verb_is(v, Ops.Insert{}), Nat.is_eq(x, a)), False{},
      Equal.sym(Bool, Bool.and(Ops.verb_is(v, Ops.Insert{}), Nat.is_eq(x, a)), True{}, AL.and_intro(Ops.verb_is(v, Ops.Insert{}), Nat.is_eq(x, a), pick_true(Nat.is_eq(x, a), Ops.verb_is(v, Ops.Insert{}), Nat.is_le(Nat.add(a, List.length(&2, Ops.Item, items)), x), eb, PL.after_delete(a, items, v, x, its, PL.none_of_is_none(Ops.ordered(Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.Op{v, x, its}), h1))), eb)),
      h3))),
    eb => pick_false(Nat.is_eq(x, a), Ops.verb_is(v, Ops.Insert{}), Nat.is_le(Nat.add(a, List.length(&2, Ops.Item, items)), x), eb, PL.after_delete(a, items, v, x, its, PL.none_of_is_none(Ops.ordered(Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.Op{v, x, its}), h1))))

def k_after_rep(+a: Nat, +items: List<&2, Ops.Item>, +a2: Nat, +items2: List<&2, Ops.Item>, +eqa: {a2 == a : Nat}, +v: Ops.Verb, +x: Nat, +its: List<&2, Ops.Item>, +h1: {Maybe.is_none(&2, String, Ops.ordered(Some{Ops.Op{Ops.Insert{}, a2, items2}}, Ops.Op{v, x, its})) == True{} : Bool}, +h2: {Maybe.is_none(&2, String, Ops.ordered(Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.Op{v, x, its})) == True{} : Bool}) -> {gap_ok(Nat.add(a, List.length(&2, Ops.Item, items)), x, Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items)))) == True{} : Bool}:
  AL.bool_cases({gap_ok(Nat.add(a, List.length(&2, Ops.Item, items)), x, Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items)))) == True{} : Bool}, Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))),
    +t => (%Equal.sym(Bool, Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))), True{}, t) : {gap_ok(Nat.add(a, List.length(&2, Ops.Item, items)), x, _) == True{} : Bool}
      pick_false(Nat.is_eq(x, a), Ops.verb_is(v, Ops.Insert{}), Nat.is_le(Nat.add(a, List.length(&2, Ops.Item, items)), x), PL.lt_not_eq_rev(a, x, (%eqa : {Nat.is_lt(_, x) == True{} : Bool}
        PL.after_insert(a2, items2, v, x, its, PL.none_of_is_none(Ops.ordered(Some{Ops.Op{Ops.Insert{}, a2, items2}}, Ops.Op{v, x, its}), h1)))), PL.after_delete(a, items, v, x, its, PL.none_of_is_none(Ops.ordered(Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.Op{v, x, its}), h2)))),
    +f => (%Equal.sym(Bool, Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))), False{}, f) : {gap_ok(Nat.add(a, List.length(&2, Ops.Item, items)), x, _) == True{} : Bool}
      %eq_of_le_nlt(a, Nat.add(a, List.length(&2, Ops.Item, items)), Comp.le_add(a, a, List.length(&2, Ops.Item, items), Comp.le_refl(a)), f) : {Nat.is_lt(_, x) == True{} : Bool}
      %eqa : {Nat.is_lt(_, x) == True{} : Bool}
      PL.after_insert(a2, items2, v, x, its, PL.none_of_is_none(Ops.ordered(Some{Ops.Op{Ops.Insert{}, a2, items2}}, Ops.Op{v, x, its}), h1))))

def del_next(+c: Nat, +a: Nat, +items: List<&2, Ops.Item>, +open: Bool, -rest: List<&2, Ops.Op>, +gap: {gap_ok(c, a, open) == True{} : Bool}, ih: {gap_ok(c, a, open) == True{} : Bool} -> {strict(rest, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)) == True{} : Bool}) -> {Bool.and(Nat.is_le(c, a), strict(rest, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open))) == True{} : Bool}:
  AL.and_intro(Nat.is_le(c, a), strict(rest, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), gap_le(c, a, open, gap), ih(gap))

def rep_or_not(+c: Nat, +a: Nat, +items: List<&2, Ops.Item>, +open: Bool, +a2: Nat, +items2: List<&2, Ops.Item>, +more: List<&2, Ops.Op>, +gap: {gap_ok(c, a, open) == True{} : Bool}, ihr: {Nat.is_eq(a2, a) == True{} : Bool} -> {strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items)))) == True{} : Bool}, ihn: {Nat.is_eq(a2, a) == False{} : Bool} -> {gap_ok(c, a, open) == True{} : Bool} -> {strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)) == True{} : Bool}) -> {strict(Ops.Op{Ops.Delete{}, a, items} <> Ops.Op{Ops.Insert{}, a2, items2} <> more, c, open) == True{} : Bool}:
  AL.bool_cases({strict(Ops.Op{Ops.Delete{}, a, items} <> Ops.Op{Ops.Insert{}, a2, items2} <> more, c, open) == True{} : Bool}, Nat.is_eq(a2, a),
    +eq => (%Equal.sym(Bool, Nat.is_eq(a2, a), True{}, eq) : {Bool.pick(Bool, _, Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)))) == True{} : Bool}
      AL.and_intro(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items)))), gap, ihr(eq))),
    +neq => (%Equal.sym(Bool, Nat.is_eq(a2, a), False{}, neq) : {Bool.pick(Bool, _, Bool.and(gap_ok(c, a, open), strict(more, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))))), Bool.and(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)))) == True{} : Bool}
      AL.and_intro(Nat.is_le(c, a), strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open)), gap_le(c, a, open, gap), ihn(neq, gap))))

def parser_strict(ops: List<&2, Ops.Op>, +prev: Maybe<&2, Ops.Op>, +pd: Maybe<&2, Ops.Op>, +c: Nat, +open: Bool, +e: {Block.ordered_all(ops, prev, pd) == True{} : Bool}, +nr: {rep_head(prev, ops) == False{} : Bool}, kk: @v: Ops.Verb -> @x: Nat -> @its: List<&2, Ops.Item> -> {Maybe.is_none(&2, String, Ops.ordered(prev, Ops.Op{v, x, its})) == True{} : Bool} -> {Maybe.is_none(&2, String, Ops.ordered(pd, Ops.Op{v, x, its})) == True{} : Bool} -> {Bool.and(Ops.verb_is(v, Ops.Insert{}), del_at(prev, x)) == False{} : Bool} -> {gap_ok(c, x, open) == True{} : Bool}) -> {strict(ops, c, open) == True{} : Bool}:
  match ops:
    case Nil{}:
      {==}
    case Ops.Op{Ops.Insert{}, +a, +items} <> +rest:
      AL.and_intro(gap_ok(c, a, open), strict(rest, a, False{}),
        kk(Ops.Insert{}, a, items, Comp.and_left(Maybe.is_none(&2, String, Ops.ordered(prev, Ops.Op{Ops.Insert{}, a, items})), Bool.and(Maybe.is_none(&2, String, Ops.ordered(pd, Ops.Op{Ops.Insert{}, a, items})), Block.ordered_all(rest, Some{Ops.Op{Ops.Insert{}, a, items}}, Ops.remember_delete(Ops.Op{Ops.Insert{}, a, items}, pd))), e), Comp.and_left(Maybe.is_none(&2, String, Ops.ordered(pd, Ops.Op{Ops.Insert{}, a, items})), Block.ordered_all(rest, Some{Ops.Op{Ops.Insert{}, a, items}}, Ops.remember_delete(Ops.Op{Ops.Insert{}, a, items}, pd)), Comp.and_right(Maybe.is_none(&2, String, Ops.ordered(prev, Ops.Op{Ops.Insert{}, a, items})), Bool.and(Maybe.is_none(&2, String, Ops.ordered(pd, Ops.Op{Ops.Insert{}, a, items})), Block.ordered_all(rest, Some{Ops.Op{Ops.Insert{}, a, items}}, Ops.remember_delete(Ops.Op{Ops.Insert{}, a, items}, pd))), e)), nr),
        parser_strict(rest, Some{Ops.Op{Ops.Insert{}, a, items}}, pd, a, False{}, Comp.and_right(Maybe.is_none(&2, String, Ops.ordered(pd, Ops.Op{Ops.Insert{}, a, items})), Block.ordered_all(rest, Some{Ops.Op{Ops.Insert{}, a, items}}, Ops.remember_delete(Ops.Op{Ops.Insert{}, a, items}, pd)), Comp.and_right(Maybe.is_none(&2, String, Ops.ordered(prev, Ops.Op{Ops.Insert{}, a, items})), Bool.and(Maybe.is_none(&2, String, Ops.ordered(pd, Ops.Op{Ops.Insert{}, a, items})), Block.ordered_all(rest, Some{Ops.Op{Ops.Insert{}, a, items}}, Ops.remember_delete(Ops.Op{Ops.Insert{}, a, items}, pd))), e)), rep_after_ins(a, items, rest),
          +v => +x => its => h1 => h2 => h3 => PL.after_insert(a, items, v, x, its, PL.none_of_is_none(Ops.ordered(Some{Ops.Op{Ops.Insert{}, a, items}}, Ops.Op{v, x, its}), h1))))
    case Ops.Op{Ops.Delete{}, +a, +items} <> +rest:
      match rest:
        case Nil{}:
          gap_le(c, a, open, kk(Ops.Delete{}, a, items, Comp.and_left(Maybe.is_none(&2, String, Ops.ordered(prev, Ops.Op{Ops.Delete{}, a, items})), Bool.and(Maybe.is_none(&2, String, Ops.ordered(pd, Ops.Op{Ops.Delete{}, a, items})), Block.ordered_all(Nil{}, Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.remember_delete(Ops.Op{Ops.Delete{}, a, items}, pd))), e), Comp.and_left(Maybe.is_none(&2, String, Ops.ordered(pd, Ops.Op{Ops.Delete{}, a, items})), Block.ordered_all(Nil{}, Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.remember_delete(Ops.Op{Ops.Delete{}, a, items}, pd)), Comp.and_right(Maybe.is_none(&2, String, Ops.ordered(prev, Ops.Op{Ops.Delete{}, a, items})), Bool.and(Maybe.is_none(&2, String, Ops.ordered(pd, Ops.Op{Ops.Delete{}, a, items})), Block.ordered_all(Nil{}, Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.remember_delete(Ops.Op{Ops.Delete{}, a, items}, pd))), e)), {==}))
        case Ops.Op{Ops.Insert{}, +a2, +items2} <> +more:
          rep_or_not(c, a, items, open, a2, items2, more, kk(Ops.Delete{}, a, items, Comp.and_left(Maybe.is_none(&2, String, Ops.ordered(prev, Ops.Op{Ops.Delete{}, a, items})), Bool.and(Maybe.is_none(&2, String, Ops.ordered(pd, Ops.Op{Ops.Delete{}, a, items})), Block.ordered_all(Ops.Op{Ops.Insert{}, a2, items2} <> more, Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.remember_delete(Ops.Op{Ops.Delete{}, a, items}, pd))), e), Comp.and_left(Maybe.is_none(&2, String, Ops.ordered(pd, Ops.Op{Ops.Delete{}, a, items})), Block.ordered_all(Ops.Op{Ops.Insert{}, a2, items2} <> more, Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.remember_delete(Ops.Op{Ops.Delete{}, a, items}, pd)), Comp.and_right(Maybe.is_none(&2, String, Ops.ordered(prev, Ops.Op{Ops.Delete{}, a, items})), Bool.and(Maybe.is_none(&2, String, Ops.ordered(pd, Ops.Op{Ops.Delete{}, a, items})), Block.ordered_all(Ops.Op{Ops.Insert{}, a2, items2} <> more, Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.remember_delete(Ops.Op{Ops.Delete{}, a, items}, pd))), e)), {==}),
            +eq => parser_strict(more, Some{Ops.Op{Ops.Insert{}, a2, items2}}, Some{Ops.Op{Ops.Delete{}, a, items}}, Nat.add(a, List.length(&2, Ops.Item, items)), Nat.is_lt(a, Nat.add(a, List.length(&2, Ops.Item, items))), Comp.and_right(Maybe.is_none(&2, String, Ops.ordered(Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.Op{Ops.Insert{}, a2, items2})), Block.ordered_all(more, Some{Ops.Op{Ops.Insert{}, a2, items2}}, Ops.remember_delete(Ops.Op{Ops.Insert{}, a2, items2}, Some{Ops.Op{Ops.Delete{}, a, items}})), Comp.and_right(Maybe.is_none(&2, String, Ops.ordered(Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.Op{Ops.Insert{}, a2, items2})), Bool.and(Maybe.is_none(&2, String, Ops.ordered(Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.Op{Ops.Insert{}, a2, items2})), Block.ordered_all(more, Some{Ops.Op{Ops.Insert{}, a2, items2}}, Ops.remember_delete(Ops.Op{Ops.Insert{}, a2, items2}, Some{Ops.Op{Ops.Delete{}, a, items}}))), Comp.and_right(Maybe.is_none(&2, String, Ops.ordered(pd, Ops.Op{Ops.Delete{}, a, items})), Block.ordered_all(Ops.Op{Ops.Insert{}, a2, items2} <> more, Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.remember_delete(Ops.Op{Ops.Delete{}, a, items}, pd)), Comp.and_right(Maybe.is_none(&2, String, Ops.ordered(prev, Ops.Op{Ops.Delete{}, a, items})), Bool.and(Maybe.is_none(&2, String, Ops.ordered(pd, Ops.Op{Ops.Delete{}, a, items})), Block.ordered_all(Ops.Op{Ops.Insert{}, a2, items2} <> more, Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.remember_delete(Ops.Op{Ops.Delete{}, a, items}, pd))), e)))), rep_after_ins(a2, items2, more),
              v => x => its => h1 => h2 => h3 => k_after_rep(a, items, a2, items2, ML.nat_eq(a2, a, eq), v, x, its, h1, h2)),
            neq => g => parser_strict(Ops.Op{Ops.Insert{}, a2, items2} <> more, Some{Ops.Op{Ops.Delete{}, a, items}}, Some{Ops.Op{Ops.Delete{}, a, items}}, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open), Comp.and_right(Maybe.is_none(&2, String, Ops.ordered(pd, Ops.Op{Ops.Delete{}, a, items})), Block.ordered_all(Ops.Op{Ops.Insert{}, a2, items2} <> more, Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.remember_delete(Ops.Op{Ops.Delete{}, a, items}, pd)), Comp.and_right(Maybe.is_none(&2, String, Ops.ordered(prev, Ops.Op{Ops.Delete{}, a, items})), Bool.and(Maybe.is_none(&2, String, Ops.ordered(pd, Ops.Op{Ops.Delete{}, a, items})), Block.ordered_all(Ops.Op{Ops.Insert{}, a2, items2} <> more, Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.remember_delete(Ops.Op{Ops.Delete{}, a, items}, pd))), e)), neq,
              v => x => its => h1 => h2 => h3 => k_after_del(c, a, items, open, g, v, x, its, h1, h3)))
        case Ops.Op{Ops.Delete{}, +a2, +items2} <> +more:
          del_next(c, a, items, open, Ops.Op{Ops.Delete{}, a2, items2} <> more, kk(Ops.Delete{}, a, items, Comp.and_left(Maybe.is_none(&2, String, Ops.ordered(prev, Ops.Op{Ops.Delete{}, a, items})), Bool.and(Maybe.is_none(&2, String, Ops.ordered(pd, Ops.Op{Ops.Delete{}, a, items})), Block.ordered_all(Ops.Op{Ops.Delete{}, a2, items2} <> more, Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.remember_delete(Ops.Op{Ops.Delete{}, a, items}, pd))), e), Comp.and_left(Maybe.is_none(&2, String, Ops.ordered(pd, Ops.Op{Ops.Delete{}, a, items})), Block.ordered_all(Ops.Op{Ops.Delete{}, a2, items2} <> more, Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.remember_delete(Ops.Op{Ops.Delete{}, a, items}, pd)), Comp.and_right(Maybe.is_none(&2, String, Ops.ordered(prev, Ops.Op{Ops.Delete{}, a, items})), Bool.and(Maybe.is_none(&2, String, Ops.ordered(pd, Ops.Op{Ops.Delete{}, a, items})), Block.ordered_all(Ops.Op{Ops.Delete{}, a2, items2} <> more, Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.remember_delete(Ops.Op{Ops.Delete{}, a, items}, pd))), e)), {==}),
            g => parser_strict(Ops.Op{Ops.Delete{}, a2, items2} <> more, Some{Ops.Op{Ops.Delete{}, a, items}}, Some{Ops.Op{Ops.Delete{}, a, items}}, Nat.add(a, List.length(&2, Ops.Item, items)), Bool.or(Nat.is_lt(c, Nat.add(a, List.length(&2, Ops.Item, items))), open), Comp.and_right(Maybe.is_none(&2, String, Ops.ordered(pd, Ops.Op{Ops.Delete{}, a, items})), Block.ordered_all(Ops.Op{Ops.Delete{}, a2, items2} <> more, Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.remember_delete(Ops.Op{Ops.Delete{}, a, items}, pd)), Comp.and_right(Maybe.is_none(&2, String, Ops.ordered(prev, Ops.Op{Ops.Delete{}, a, items})), Bool.and(Maybe.is_none(&2, String, Ops.ordered(pd, Ops.Op{Ops.Delete{}, a, items})), Block.ordered_all(Ops.Op{Ops.Delete{}, a2, items2} <> more, Some{Ops.Op{Ops.Delete{}, a, items}}, Ops.remember_delete(Ops.Op{Ops.Delete{}, a, items}, pd))), e)), {==},
              v => x => its => h1 => h2 => h3 => k_after_del(c, a, items, open, g, v, x, its, h1, h3)))

# Every document the parser's order admits is one the run can replay.
def all_strict_of(docs: List<&2, List<&2, Ops.Op>>, +h: {Block.each_ordered(docs) == True{} : Bool}) -> {all_strict(docs) == True{} : Bool}:
  match docs:
    case Nil{}:
      {==}
    case +d <> +ds:
      AL.and_intro(strict(d, 0n, True{}), all_strict(ds),
        parser_strict(d, None{}, None{}, 0n, True{}, Comp.and_left(Block.ordered_all(d, None{}, None{}), Block.each_ordered(ds), h), rep_none(d),
          v => x => its => h1 => h2 => h3 => PL.le_zero(x)),
        all_strict_of(ds, Comp.and_right(Block.ordered_all(d, None{}, None{}), Block.each_ordered(ds), h)))

def main() -> Unit:
  Unit{}
