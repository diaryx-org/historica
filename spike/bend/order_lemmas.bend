# The order the tool walks a merge in is causal. `main.bend` sorts each
# event by how many events it had seen; every event had seen more than
# any event it had seen (`Main.deepens`), so nothing comes before what it
# had seen, and the sort moves no event in or out, so it is an order of
# every event — which `merge_converges` then says reads what any other
# causal order of them reads.
import Base
import ./ops.bend as Ops
import ./merge.bend as M
import ./commands.bend as Main
import ./store.bend as Store
import ./tree.bend as Tree
import ./composition_lemmas.bend as Comp
import ./merge_lemmas.bend as ML
import ./anchor_lemmas.bend as AL
import ./linear_lemmas.bend as Lin
import ./parser_lemmas.bend as PL
import ./walk_lemmas.bend as Walk

# Bools
# -----

def or_swap(a: Bool, b: Bool, -c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(b, Bool.or(a, c)) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def and_swap(a: Bool, b: Bool, -c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(b, Bool.and(a, c)) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# `x` before `y` or `y` before `x`: each is distinct from the rest the same.
def distinct_swap(a: Bool, b: Bool, c: Bool, -d: Bool) -> {Bool.and(Bool.not(Bool.or(a, b)), Bool.and(Bool.not(c), d)) == Bool.and(Bool.not(Bool.or(a, c)), Bool.and(Bool.not(b), d)) : Bool}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# Nats
# ----

def le_flip(a: Nat, b: Nat, e: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, ML.true_false(e))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      le_flip(p, q, e)

# The sort keeps what it sorts
# ----------------------------

def put_has.at(+dx: Nat, +ax: Nat, +dy: Nat, +ay: Nat, +rest: List<&2, Main.Rank>, +y: Nat, le: Bool, ih: {M.has(Main.rank_at(Main.rank.put(Main.Rank{dx, ax}, rest)), y) == M.has(ax <> Main.rank_at(rest), y) : Bool}) -> {M.has(Main.rank_at(Main.rank.put.pick(Main.Rank{dx, ax}, Main.Rank{dy, ay}, rest, Main.rank.put(Main.Rank{dx, ax}, rest), le)), y) == M.has(ax <> ay <> Main.rank_at(rest), y) : Bool}:
  match le:
    case True{}:
      {==}
    case False{}:
      Equal.trans(Bool, Bool.or(Nat.is_eq(ay, y), M.has(Main.rank_at(Main.rank.put(Main.Rank{dx, ax}, rest)), y)), Bool.or(Nat.is_eq(ay, y), Bool.or(Nat.is_eq(ax, y), M.has(Main.rank_at(rest), y))), Bool.or(Nat.is_eq(ax, y), Bool.or(Nat.is_eq(ay, y), M.has(Main.rank_at(rest), y))),
        Equal.cong(Bool, Bool, h => Bool.or(Nat.is_eq(ay, y), h), M.has(Main.rank_at(Main.rank.put(Main.Rank{dx, ax}, rest)), y), Bool.or(Nat.is_eq(ax, y), M.has(Main.rank_at(rest), y)), ih),
        or_swap(Nat.is_eq(ay, y), Nat.is_eq(ax, y), M.has(Main.rank_at(rest), y)))

# Inserting a rank holds what prepending it holds.
def put_has(+dx: Nat, +ax: Nat, ys: List<&2, Main.Rank>, +y: Nat) -> {M.has(Main.rank_at(Main.rank.put(Main.Rank{dx, ax}, ys)), y) == M.has(ax <> Main.rank_at(ys), y) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Main.Rank{+dy, +ay} <> +rest:
      put_has.at(dx, ax, dy, ay, rest, y, Nat.is_le(dx, dy), put_has(dx, ax, rest, y))

def sort_has(rs: List<&2, Main.Rank>, +y: Nat) -> {M.has(Main.rank_at(Main.rank.sort(rs)), y) == M.has(Main.rank_at(rs), y) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Main.Rank{+d, +a} <> +rest:
      Equal.trans(Bool, M.has(Main.rank_at(Main.rank.put(Main.Rank{d, a}, Main.rank.sort(rest))), y), Bool.or(Nat.is_eq(a, y), M.has(Main.rank_at(Main.rank.sort(rest)), y)), Bool.or(Nat.is_eq(a, y), M.has(Main.rank_at(rest), y)),
        put_has(d, a, Main.rank.sort(rest), y),
        Equal.cong(Bool, Bool, h => Bool.or(Nat.is_eq(a, y), h), M.has(Main.rank_at(Main.rank.sort(rest)), y), M.has(Main.rank_at(rest), y), sort_has(rest, y)))

# What a list is a subset of is the same for the sorted list.
def sub_sort(xs: List<&2, Nat>, +rs: List<&2, Main.Rank>) -> {M.subset(xs, Main.rank_at(Main.rank.sort(rs))) == M.subset(xs, Main.rank_at(rs)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      Equal.trans(Bool, Bool.and(M.has(Main.rank_at(Main.rank.sort(rs)), x), M.subset(rest, Main.rank_at(Main.rank.sort(rs)))), Bool.and(M.has(Main.rank_at(rs), x), M.subset(rest, Main.rank_at(Main.rank.sort(rs)))), Bool.and(M.has(Main.rank_at(rs), x), M.subset(rest, Main.rank_at(rs))),
        Equal.cong(Bool, Bool, h => Bool.and(h, M.subset(rest, Main.rank_at(Main.rank.sort(rs)))), M.has(Main.rank_at(Main.rank.sort(rs)), x), M.has(Main.rank_at(rs), x), sort_has(rs, x)),
        Equal.cong(Bool, Bool, h => Bool.and(M.has(Main.rank_at(rs), x), h), M.subset(rest, Main.rank_at(Main.rank.sort(rs))), M.subset(rest, Main.rank_at(rs)), sub_sort(rest, rs)))

def put_sub.at(+dx: Nat, +ax: Nat, +dy: Nat, +ay: Nat, +rest: List<&2, Main.Rank>, +X: List<&2, Nat>, le: Bool, ih: {M.subset(Main.rank_at(Main.rank.put(Main.Rank{dx, ax}, rest)), X) == M.subset(ax <> Main.rank_at(rest), X) : Bool}) -> {M.subset(Main.rank_at(Main.rank.put.pick(Main.Rank{dx, ax}, Main.Rank{dy, ay}, rest, Main.rank.put(Main.Rank{dx, ax}, rest), le)), X) == M.subset(ax <> ay <> Main.rank_at(rest), X) : Bool}:
  match le:
    case True{}:
      {==}
    case False{}:
      Equal.trans(Bool, Bool.and(M.has(X, ay), M.subset(Main.rank_at(Main.rank.put(Main.Rank{dx, ax}, rest)), X)), Bool.and(M.has(X, ay), Bool.and(M.has(X, ax), M.subset(Main.rank_at(rest), X))), Bool.and(M.has(X, ax), Bool.and(M.has(X, ay), M.subset(Main.rank_at(rest), X))),
        Equal.cong(Bool, Bool, h => Bool.and(M.has(X, ay), h), M.subset(Main.rank_at(Main.rank.put(Main.Rank{dx, ax}, rest)), X), Bool.and(M.has(X, ax), M.subset(Main.rank_at(rest), X)), ih),
        and_swap(M.has(X, ay), M.has(X, ax), M.subset(Main.rank_at(rest), X)))

def put_sub(+dx: Nat, +ax: Nat, ys: List<&2, Main.Rank>, +X: List<&2, Nat>) -> {M.subset(Main.rank_at(Main.rank.put(Main.Rank{dx, ax}, ys)), X) == M.subset(ax <> Main.rank_at(ys), X) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Main.Rank{+dy, +ay} <> +rest:
      put_sub.at(dx, ax, dy, ay, rest, X, Nat.is_le(dx, dy), put_sub(dx, ax, rest, X))

# The sorted list is a subset of what the list is a subset of.
def sort_sub(rs: List<&2, Main.Rank>, +X: List<&2, Nat>) -> {M.subset(Main.rank_at(Main.rank.sort(rs)), X) == M.subset(Main.rank_at(rs), X) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Main.Rank{+d, +a} <> +rest:
      Equal.trans(Bool, M.subset(Main.rank_at(Main.rank.put(Main.Rank{d, a}, Main.rank.sort(rest))), X), Bool.and(M.has(X, a), M.subset(Main.rank_at(Main.rank.sort(rest)), X)), Bool.and(M.has(X, a), M.subset(Main.rank_at(rest), X)),
        put_sub(d, a, Main.rank.sort(rest), X),
        Equal.cong(Bool, Bool, h => Bool.and(M.has(X, a), h), M.subset(Main.rank_at(Main.rank.sort(rest)), X), M.subset(Main.rank_at(rest), X), sort_sub(rest, X)))

def put_distinct.at(+dx: Nat, +ax: Nat, +dy: Nat, +ay: Nat, +rest: List<&2, Main.Rank>, le: Bool, ih: {M.distinct(Main.rank_at(Main.rank.put(Main.Rank{dx, ax}, rest))) == M.distinct(ax <> Main.rank_at(rest)) : Bool}) -> {M.distinct(Main.rank_at(Main.rank.put.pick(Main.Rank{dx, ax}, Main.Rank{dy, ay}, rest, Main.rank.put(Main.Rank{dx, ax}, rest), le))) == M.distinct(ax <> ay <> Main.rank_at(rest)) : Bool}:
  match le:
    case True{}:
      {==}
    case False{}:
      Equal.trans(Bool, Bool.and(Bool.not(M.has(Main.rank_at(Main.rank.put(Main.Rank{dx, ax}, rest)), ay)), M.distinct(Main.rank_at(Main.rank.put(Main.Rank{dx, ax}, rest)))), Bool.and(Bool.not(M.has(ax <> Main.rank_at(rest), ay)), M.distinct(ax <> Main.rank_at(rest))), Bool.and(Bool.not(Bool.or(Nat.is_eq(ay, ax), M.has(Main.rank_at(rest), ax))), Bool.and(Bool.not(M.has(Main.rank_at(rest), ay)), M.distinct(Main.rank_at(rest)))),
        Equal.trans(Bool, Bool.and(Bool.not(M.has(Main.rank_at(Main.rank.put(Main.Rank{dx, ax}, rest)), ay)), M.distinct(Main.rank_at(Main.rank.put(Main.Rank{dx, ax}, rest)))), Bool.and(Bool.not(M.has(ax <> Main.rank_at(rest), ay)), M.distinct(Main.rank_at(Main.rank.put(Main.Rank{dx, ax}, rest)))), Bool.and(Bool.not(M.has(ax <> Main.rank_at(rest), ay)), M.distinct(ax <> Main.rank_at(rest))),
          Equal.cong(Bool, Bool, h => Bool.and(Bool.not(h), M.distinct(Main.rank_at(Main.rank.put(Main.Rank{dx, ax}, rest)))), M.has(Main.rank_at(Main.rank.put(Main.Rank{dx, ax}, rest)), ay), M.has(ax <> Main.rank_at(rest), ay), put_has(dx, ax, rest, ay)),
          Equal.cong(Bool, Bool, h => Bool.and(Bool.not(M.has(ax <> Main.rank_at(rest), ay)), h), M.distinct(Main.rank_at(Main.rank.put(Main.Rank{dx, ax}, rest))), M.distinct(ax <> Main.rank_at(rest)), ih)),
        Equal.trans(Bool, Bool.and(Bool.not(Bool.or(Nat.is_eq(ax, ay), M.has(Main.rank_at(rest), ay))), Bool.and(Bool.not(M.has(Main.rank_at(rest), ax)), M.distinct(Main.rank_at(rest)))), Bool.and(Bool.not(Bool.or(Nat.is_eq(ax, ay), M.has(Main.rank_at(rest), ax))), Bool.and(Bool.not(M.has(Main.rank_at(rest), ay)), M.distinct(Main.rank_at(rest)))), Bool.and(Bool.not(Bool.or(Nat.is_eq(ay, ax), M.has(Main.rank_at(rest), ax))), Bool.and(Bool.not(M.has(Main.rank_at(rest), ay)), M.distinct(Main.rank_at(rest)))),
          distinct_swap(Nat.is_eq(ax, ay), M.has(Main.rank_at(rest), ay), M.has(Main.rank_at(rest), ax), M.distinct(Main.rank_at(rest))),
          Equal.cong(Bool, Bool, h => Bool.and(Bool.not(Bool.or(h, M.has(Main.rank_at(rest), ax))), Bool.and(Bool.not(M.has(Main.rank_at(rest), ay)), M.distinct(Main.rank_at(rest)))), Nat.is_eq(ax, ay), Nat.is_eq(ay, ax), ML.is_eq_sym(ay, ax))))

def put_distinct(+dx: Nat, +ax: Nat, ys: List<&2, Main.Rank>) -> {M.distinct(Main.rank_at(Main.rank.put(Main.Rank{dx, ax}, ys))) == M.distinct(ax <> Main.rank_at(ys)) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Main.Rank{+dy, +ay} <> +rest:
      put_distinct.at(dx, ax, dy, ay, rest, Nat.is_le(dx, dy), put_distinct(dx, ax, rest))

def sort_distinct(rs: List<&2, Main.Rank>) -> {M.distinct(Main.rank_at(Main.rank.sort(rs))) == M.distinct(Main.rank_at(rs)) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Main.Rank{+d, +a} <> +rest:
      Equal.trans(Bool, M.distinct(Main.rank_at(Main.rank.put(Main.Rank{d, a}, Main.rank.sort(rest)))), Bool.and(Bool.not(M.has(Main.rank_at(Main.rank.sort(rest)), a)), M.distinct(Main.rank_at(Main.rank.sort(rest)))), Bool.and(Bool.not(M.has(Main.rank_at(rest), a)), M.distinct(Main.rank_at(rest))),
        put_distinct(d, a, Main.rank.sort(rest)),
        Equal.trans(Bool, Bool.and(Bool.not(M.has(Main.rank_at(Main.rank.sort(rest)), a)), M.distinct(Main.rank_at(Main.rank.sort(rest)))), Bool.and(Bool.not(M.has(Main.rank_at(rest), a)), M.distinct(Main.rank_at(Main.rank.sort(rest)))), Bool.and(Bool.not(M.has(Main.rank_at(rest), a)), M.distinct(Main.rank_at(rest))),
          Equal.cong(Bool, Bool, h => Bool.and(Bool.not(h), M.distinct(Main.rank_at(Main.rank.sort(rest)))), M.has(Main.rank_at(Main.rank.sort(rest)), a), M.has(Main.rank_at(rest), a), sort_has(rest, a)),
          Equal.cong(Bool, Bool, h => Bool.and(Bool.not(M.has(Main.rank_at(rest), a)), h), M.distinct(Main.rank_at(Main.rank.sort(rest))), M.distinct(Main.rank_at(rest)), sort_distinct(rest))))

# The sort sorts
# --------------

# Every rank at least `d` deep.
def all_ge(+d: Nat, rs: List<&2, Main.Rank>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> rest:
      Bool.and(Nat.is_le(d, Main.depth_of(r)), all_ge(d, rest))

def sorted(rs: List<&2, Main.Rank>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case +r <> +rest:
      Bool.and(all_ge(Main.depth_of(r), rest), sorted(rest))

def all_ge_trans(+a: Nat, +b: Nat, rs: List<&2, Main.Rank>, +ab: {Nat.is_le(a, b) == True{} : Bool}, +h: {all_ge(b, rs) == True{} : Bool}) -> {all_ge(a, rs) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Main.Rank{+d, +x} <> +rest:
      AL.and_intro(Nat.is_le(a, d), all_ge(a, rest),
        Lin.le_trans(a, b, d, ab, Comp.and_left(Nat.is_le(b, d), all_ge(b, rest), h)),
        all_ge_trans(a, b, rest, ab, Comp.and_right(Nat.is_le(b, d), all_ge(b, rest), h)))

def put_ge.at(+d: Nat, +dx: Nat, +ax: Nat, +dy: Nat, +ay: Nat, +rest: List<&2, Main.Rank>, le: Bool, +hx: {Nat.is_le(d, dx) == True{} : Bool}, +hy: {Bool.and(Nat.is_le(d, dy), all_ge(d, rest)) == True{} : Bool}, ih: {all_ge(d, Main.rank.put(Main.Rank{dx, ax}, rest)) == True{} : Bool}) -> {all_ge(d, Main.rank.put.pick(Main.Rank{dx, ax}, Main.Rank{dy, ay}, rest, Main.rank.put(Main.Rank{dx, ax}, rest), le)) == True{} : Bool}:
  match le:
    case True{}:
      AL.and_intro(Nat.is_le(d, dx), Bool.and(Nat.is_le(d, dy), all_ge(d, rest)), hx, hy)
    case False{}:
      AL.and_intro(Nat.is_le(d, dy), all_ge(d, Main.rank.put(Main.Rank{dx, ax}, rest)), Comp.and_left(Nat.is_le(d, dy), all_ge(d, rest), hy), ih)

def put_ge(+d: Nat, +dx: Nat, +ax: Nat, ys: List<&2, Main.Rank>, +hx: {Nat.is_le(d, dx) == True{} : Bool}, +h: {all_ge(d, ys) == True{} : Bool}) -> {all_ge(d, Main.rank.put(Main.Rank{dx, ax}, ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      AL.and_intro(Nat.is_le(d, dx), True{}, hx, {==})
    case Main.Rank{+dy, +ay} <> +rest:
      put_ge.at(d, dx, ax, dy, ay, rest, Nat.is_le(dx, dy), hx, h, put_ge(d, dx, ax, rest, hx, Comp.and_right(Nat.is_le(d, dy), all_ge(d, rest), h)))

def put_sorted.at(+dx: Nat, +ax: Nat, +dy: Nat, +ay: Nat, +rest: List<&2, Main.Rank>, le: Bool, +el: {Nat.is_le(dx, dy) == le : Bool}, +h: {Bool.and(all_ge(dy, rest), sorted(rest)) == True{} : Bool}, ih: {sorted(Main.rank.put(Main.Rank{dx, ax}, rest)) == True{} : Bool}) -> {sorted(Main.rank.put.pick(Main.Rank{dx, ax}, Main.Rank{dy, ay}, rest, Main.rank.put(Main.Rank{dx, ax}, rest), le)) == True{} : Bool}:
  match le:
    case True{}:
      AL.and_intro(all_ge(dx, Main.Rank{dy, ay} <> rest), sorted(Main.Rank{dy, ay} <> rest),
        AL.and_intro(Nat.is_le(dx, dy), all_ge(dx, rest), el, all_ge_trans(dx, dy, rest, el, Comp.and_left(all_ge(dy, rest), sorted(rest), h))),
        h)
    case False{}:
      AL.and_intro(all_ge(dy, Main.rank.put(Main.Rank{dx, ax}, rest)), sorted(Main.rank.put(Main.Rank{dx, ax}, rest)),
        put_ge(dy, dx, ax, rest, le_flip(dx, dy, el), Comp.and_left(all_ge(dy, rest), sorted(rest), h)),
        ih)

def put_sorted(+dx: Nat, +ax: Nat, ys: List<&2, Main.Rank>, +h: {sorted(ys) == True{} : Bool}) -> {sorted(Main.rank.put(Main.Rank{dx, ax}, ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Main.Rank{+dy, +ay} <> +rest:
      put_sorted.at(dx, ax, dy, ay, rest, Nat.is_le(dx, dy), {==}, h, put_sorted(dx, ax, rest, Comp.and_right(all_ge(dy, rest), sorted(rest), h)))

def sort_sorted(rs: List<&2, Main.Rank>) -> {sorted(Main.rank.sort(rs)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Main.Rank{+d, +a} <> +rest:
      put_sorted(d, a, Main.rank.sort(rest), sort_sorted(rest))

# Each rank is honest: its depth is how many its event had seen, and each
# of those had seen fewer.
def good(+g: List<&2, M.Rev>, r: Main.Rank) -> Bool:
  match r:
    case Main.Rank{+d, +a}:
      Bool.and(Main.shallower(g, M.past(g, a), d), Nat.is_le(d, List.length(&2, Nat, M.past(g, a))))

def all_good(+g: List<&2, M.Rev>, rs: List<&2, Main.Rank>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> rest:
      Bool.and(good(g, r), all_good(g, rest))

def put_good.at(+g: List<&2, M.Rev>, +dx: Nat, +ax: Nat, +dy: Nat, +ay: Nat, +rest: List<&2, Main.Rank>, le: Bool, +hx: {good(g, Main.Rank{dx, ax}) == True{} : Bool}, +hy: {Bool.and(good(g, Main.Rank{dy, ay}), all_good(g, rest)) == True{} : Bool}, ih: {all_good(g, Main.rank.put(Main.Rank{dx, ax}, rest)) == True{} : Bool}) -> {all_good(g, Main.rank.put.pick(Main.Rank{dx, ax}, Main.Rank{dy, ay}, rest, Main.rank.put(Main.Rank{dx, ax}, rest), le)) == True{} : Bool}:
  match le:
    case True{}:
      AL.and_intro(good(g, Main.Rank{dx, ax}), all_good(g, Main.Rank{dy, ay} <> rest), hx, hy)
    case False{}:
      AL.and_intro(good(g, Main.Rank{dy, ay}), all_good(g, Main.rank.put(Main.Rank{dx, ax}, rest)), Comp.and_left(good(g, Main.Rank{dy, ay}), all_good(g, rest), hy), ih)

def put_good(+g: List<&2, M.Rev>, +dx: Nat, +ax: Nat, ys: List<&2, Main.Rank>, +hx: {good(g, Main.Rank{dx, ax}) == True{} : Bool}, +h: {all_good(g, ys) == True{} : Bool}) -> {all_good(g, Main.rank.put(Main.Rank{dx, ax}, ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      AL.and_intro(good(g, Main.Rank{dx, ax}), True{}, hx, {==})
    case Main.Rank{+dy, +ay} <> +rest:
      put_good.at(g, dx, ax, dy, ay, rest, Nat.is_le(dx, dy), hx, h, put_good(g, dx, ax, rest, hx, Comp.and_right(good(g, Main.Rank{dy, ay}), all_good(g, rest), h)))

def sort_good(+g: List<&2, M.Rev>, rs: List<&2, Main.Rank>, +h: {all_good(g, rs) == True{} : Bool}) -> {all_good(g, Main.rank.sort(rs)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Main.Rank{+d, +a} <> +rest:
      put_good(g, d, a, Main.rank.sort(rest), Comp.and_left(good(g, Main.Rank{d, a}), all_good(g, rest), h), sort_good(g, rest, Comp.and_right(good(g, Main.Rank{d, a}), all_good(g, rest), h)))

# Sorted and honest is causal
# ---------------------------

def shallower_has(+g: List<&2, M.Rev>, js: List<&2, Nat>, +d: Nat, +y: Nat, +h: {Main.shallower(g, js, d) == True{} : Bool}, m: {M.has(js, y) == True{} : Bool}) -> {Nat.is_lt(List.length(&2, Nat, M.past(g, y)), d) == True{} : Bool}:
  match js:
    case Nil{}:
      Empty.absurd({Nat.is_lt(List.length(&2, Nat, M.past(g, y)), d) == True{} : Bool}, Comp.false_true(m))
    case +j <> +rest:
      AL.or_cases({Nat.is_lt(List.length(&2, Nat, M.past(g, y)), d) == True{} : Bool}, Nat.is_eq(j, y), M.has(rest, y), m,
        e => (%ML.nat_eq(j, y, e) : {Nat.is_lt(List.length(&2, Nat, M.past(g, _)), d) == True{} : Bool}
          Comp.and_left(Nat.is_lt(List.length(&2, Nat, M.past(g, j)), d), Main.shallower(g, rest, d), h)),
        e => shallower_has(g, rest, d, y, Comp.and_right(Nat.is_lt(List.length(&2, Nat, M.past(g, j)), d), Main.shallower(g, rest, d), h), e))

# An event `y` at least as deep as `x`, and honestly so, is not one `x` had seen.
def unseen.at(+g: List<&2, M.Rev>, +d: Nat, +a: Nat, +d2: Nat, +a2: Nat, b: Bool, eb: {M.has(M.past(g, a), a2) == b : Bool}, +hs: {Main.shallower(g, M.past(g, a), d) == True{} : Bool}, +le: {Nat.is_le(d, d2) == True{} : Bool}, +g2: {good(g, Main.Rank{d2, a2}) == True{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool},
        ML.true_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_le(d2, List.length(&2, Nat, M.past(g, a2))), Nat.is_lt(List.length(&2, Nat, M.past(g, a2)), d2)), False{},
          Equal.sym(Bool, Bool.and(Nat.is_le(d2, List.length(&2, Nat, M.past(g, a2))), Nat.is_lt(List.length(&2, Nat, M.past(g, a2)), d2)), True{},
            AL.and_intro(Nat.is_le(d2, List.length(&2, Nat, M.past(g, a2))), Nat.is_lt(List.length(&2, Nat, M.past(g, a2)), d2),
              Comp.and_right(Main.shallower(g, M.past(g, a2), d2), Nat.is_le(d2, List.length(&2, Nat, M.past(g, a2))), g2),
              Lin.lt_le_trans(List.length(&2, Nat, M.past(g, a2)), d, d2, shallower_has(g, M.past(g, a), d, a2, hs, eb), le))),
          Comp.le_lt_contra(d2, List.length(&2, Nat, M.past(g, a2))))))

def unseen(+g: List<&2, M.Rev>, +d: Nat, +a: Nat, rest: List<&2, Main.Rank>, +hs: {Main.shallower(g, M.past(g, a), d) == True{} : Bool}, +ge: {all_ge(d, rest) == True{} : Bool}, +hg: {all_good(g, rest) == True{} : Bool}) -> {M.none_known(M.past(g, a), Main.rank_at(rest)) == True{} : Bool}:
  match rest:
    case Nil{}:
      {==}
    case Main.Rank{+d2, +a2} <> +more:
      AL.and_intro(Bool.not(M.has(M.past(g, a), a2)), M.none_known(M.past(g, a), Main.rank_at(more)),
        unseen.at(g, d, a, d2, a2, M.has(M.past(g, a), a2), {==}, hs, Comp.and_left(Nat.is_le(d, d2), all_ge(d, more), ge), Comp.and_left(good(g, Main.Rank{d2, a2}), all_good(g, more), hg)),
        unseen(g, d, a, more, hs, Comp.and_right(Nat.is_le(d, d2), all_ge(d, more), ge), Comp.and_right(good(g, Main.Rank{d2, a2}), all_good(g, more), hg)))

def sorted_causal(+g: List<&2, M.Rev>, rs: List<&2, Main.Rank>, +hs: {sorted(rs) == True{} : Bool}, +hg: {all_good(g, rs) == True{} : Bool}) -> {M.causal(Main.rank_at(rs), g) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Main.Rank{+d, +a} <> +rest:
      AL.and_intro(M.none_known(M.past(g, a), Main.rank_at(rest)), M.causal(Main.rank_at(rest), g),
        unseen(g, d, a, rest,
          Comp.and_left(Main.shallower(g, M.past(g, a), d), Nat.is_le(d, List.length(&2, Nat, M.past(g, a))), Comp.and_left(good(g, Main.Rank{d, a}), all_good(g, rest), hg)),
          Comp.and_left(all_ge(d, rest), sorted(rest), hs),
          Comp.and_right(good(g, Main.Rank{d, a}), all_good(g, rest), hg)),
        sorted_causal(g, rest, Comp.and_right(all_ge(d, rest), sorted(rest), hs), Comp.and_right(good(g, Main.Rank{d, a}), all_good(g, rest), hg)))

# The ranks the tool starts from
# ------------------------------

def ranks_at(+g: List<&2, M.Rev>, ixs: List<&2, Nat>) -> {Main.rank_at(Main.ranks(g, ixs)) == ixs : List<&2, Nat>}:
  match ixs:
    case Nil{}:
      {==}
    case +i <> +rest:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, l => i <> l, Main.rank_at(Main.ranks(g, rest)), rest, ranks_at(g, rest))

def ranks_good(+g: List<&2, M.Rev>, ixs: List<&2, Nat>, +h: {Main.deepens.all(g, ixs) == True{} : Bool}) -> {all_good(g, Main.ranks(g, ixs)) == True{} : Bool}:
  match ixs:
    case Nil{}:
      {==}
    case +i <> +rest:
      AL.and_intro(good(g, Main.Rank{List.length(&2, Nat, M.past(g, i)), i}), all_good(g, Main.ranks(g, rest)),
        AL.and_intro(Main.shallower(g, M.past(g, i), List.length(&2, Nat, M.past(g, i))), Nat.is_le(List.length(&2, Nat, M.past(g, i)), List.length(&2, Nat, M.past(g, i))),
          Comp.and_left(Main.shallower(g, M.past(g, i), List.length(&2, Nat, M.past(g, i))), Main.deepens.all(g, rest), h),
          Comp.le_refl(List.length(&2, Nat, M.past(g, i)))),
        ranks_good(g, rest, Comp.and_right(Main.shallower(g, M.past(g, i), List.length(&2, Nat, M.past(g, i))), Main.deepens.all(g, rest), h)))

# The indices are each once
# -------------------------

def has_upto_lt(p: Nat, +j: Nat, +k: Nat, +lt: {Nat.is_lt(k, j) == True{} : Bool}) -> {M.has(M.upto.go(p, j), k) == False{} : Bool}:
  match p:
    case 0n:
      {==}
    case 1n++q:
      AL.or_false(Nat.is_eq(j, k), M.has(M.upto.go(q, 1n+j), k), PL.lt_not_eq_rev(k, j, lt), has_upto_lt(q, 1n+j, k, Comp.lt_succ(k, j, lt)))

def distinct_upto(n: Nat, +k: Nat) -> {M.distinct(M.upto.go(n, k)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      AL.and_intro(Bool.not(M.has(M.upto.go(p, 1n+k), k)), M.distinct(M.upto.go(p, 1n+k)),
        AL.not_true(M.has(M.upto.go(p, 1n+k), k), has_upto_lt(p, 1n+k, k, Comp.lt_succ_self(k))),
        distinct_upto(p, 1n+k))

def subset_trans(a: List<&2, Nat>, +b: List<&2, Nat>, +c: List<&2, Nat>, +ab: {M.subset(a, b) == True{} : Bool}, +bc: {M.subset(b, c) == True{} : Bool}) -> {M.subset(a, c) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case +x <> +xs:
      AL.and_intro(M.has(c, x), M.subset(xs, c),
        Lin.has_sub(b, c, x, bc, Comp.and_left(M.has(b, x), M.subset(xs, b), ab)),
        subset_trans(xs, b, c, Comp.and_right(M.has(b, x), M.subset(xs, b), ab), bc))

# The order
# ---------

def order_causal(+g: List<&2, M.Rev>, +h: {Main.deepens(g) == True{} : Bool}) -> {M.causal(Main.walked.order(g), g) == True{} : Bool}:
  sorted_causal(g, Main.rank.sort(Main.ranks(g, M.upto(List.length(&2, M.Rev, g)))),
    sort_sorted(Main.ranks(g, M.upto(List.length(&2, M.Rev, g)))),
    sort_good(g, Main.ranks(g, M.upto(List.length(&2, M.Rev, g))), ranks_good(g, M.upto(List.length(&2, M.Rev, g)), h)))

def order_distinct(+g: List<&2, M.Rev>) -> {M.distinct(Main.walked.order(g)) == True{} : Bool}:
  Equal.trans(Bool, M.distinct(Main.walked.order(g)), M.distinct(Main.rank_at(Main.ranks(g, M.upto(List.length(&2, M.Rev, g))))), True{},
    sort_distinct(Main.ranks(g, M.upto(List.length(&2, M.Rev, g)))),
    (%Equal.sym(List<&2, Nat>, Main.rank_at(Main.ranks(g, M.upto(List.length(&2, M.Rev, g)))), M.upto(List.length(&2, M.Rev, g)), ranks_at(g, M.upto(List.length(&2, M.Rev, g)))) : {M.distinct(_) == True{} : Bool}
      distinct_upto(List.length(&2, M.Rev, g), 0n)))

# Every event, and nothing else.
def order_within(+g: List<&2, M.Rev>) -> {M.subset(Main.walked.order(g), M.upto(List.length(&2, M.Rev, g))) == True{} : Bool}:
  Equal.trans(Bool, M.subset(Main.walked.order(g), M.upto(List.length(&2, M.Rev, g))), M.subset(Main.rank_at(Main.ranks(g, M.upto(List.length(&2, M.Rev, g)))), M.upto(List.length(&2, M.Rev, g))), True{},
    sort_sub(Main.ranks(g, M.upto(List.length(&2, M.Rev, g))), M.upto(List.length(&2, M.Rev, g))),
    (%Equal.sym(List<&2, Nat>, Main.rank_at(Main.ranks(g, M.upto(List.length(&2, M.Rev, g)))), M.upto(List.length(&2, M.Rev, g)), ranks_at(g, M.upto(List.length(&2, M.Rev, g)))) : {M.subset(_, M.upto(List.length(&2, M.Rev, g))) == True{} : Bool}
      Walk.subset_refl_n(M.upto(List.length(&2, M.Rev, g)))))

def order_every(+g: List<&2, M.Rev>) -> {M.subset(M.upto(List.length(&2, M.Rev, g)), Main.walked.order(g)) == True{} : Bool}:
  Equal.trans(Bool, M.subset(M.upto(List.length(&2, M.Rev, g)), Main.walked.order(g)), M.subset(M.upto(List.length(&2, M.Rev, g)), Main.rank_at(Main.ranks(g, M.upto(List.length(&2, M.Rev, g))))), True{},
    sub_sort(M.upto(List.length(&2, M.Rev, g)), Main.ranks(g, M.upto(List.length(&2, M.Rev, g)))),
    (%Equal.sym(List<&2, Nat>, Main.rank_at(Main.ranks(g, M.upto(List.length(&2, M.Rev, g)))), M.upto(List.length(&2, M.Rev, g)), ranks_at(g, M.upto(List.length(&2, M.Rev, g)))) : {M.subset(M.upto(List.length(&2, M.Rev, g)), _) == True{} : Bool}
      Walk.subset_refl_n(M.upto(List.length(&2, M.Rev, g)))))

# The tool's walk reads what every causal order of every event reads.
def order_converges(+g: List<&2, M.Rev>, +b: List<&2, Nat>, +h: {Main.deepens(g) == True{} : Bool}, +hb: {M.distinct(b) == True{} : Bool}, +hc: {M.causal(b, g) == True{} : Bool}, +hs: {M.subset(b, M.upto(List.length(&2, M.Rev, g))) == True{} : Bool}, +ht: {M.subset(M.upto(List.length(&2, M.Rev, g)), b) == True{} : Bool}) -> {M.merged(g, Main.walked.order(g)) == M.merged(g, b) : Maybe<&2, List<&2, Ops.Item>>}:
  ML.merge_converges(g, Main.walked.order(g), b,
    AL.and_intro(M.distinct(Main.walked.order(g)), Bool.and(M.distinct(b), Bool.and(M.subset(Main.walked.order(g), b), Bool.and(M.subset(b, Main.walked.order(g)), Bool.and(M.causal(Main.walked.order(g), g), M.causal(b, g))))),
      order_distinct(g),
      AL.and_intro(M.distinct(b), Bool.and(M.subset(Main.walked.order(g), b), Bool.and(M.subset(b, Main.walked.order(g)), Bool.and(M.causal(Main.walked.order(g), g), M.causal(b, g)))),
        hb,
        AL.and_intro(M.subset(Main.walked.order(g), b), Bool.and(M.subset(b, Main.walked.order(g)), Bool.and(M.causal(Main.walked.order(g), g), M.causal(b, g))),
          subset_trans(Main.walked.order(g), M.upto(List.length(&2, M.Rev, g)), b, order_within(g), ht),
          AL.and_intro(M.subset(b, Main.walked.order(g)), Bool.and(M.causal(Main.walked.order(g), g), M.causal(b, g)),
            subset_trans(b, M.upto(List.length(&2, M.Rev, g)), Main.walked.order(g), hs, order_every(g)),
            AL.and_intro(M.causal(Main.walked.order(g), g), M.causal(b, g), order_causal(g, h), hc))))))

# What the tool reads
# -------------------

def rdisc(r: Result<&2, &2, String, Main.Walked>) -> Type:
  match r:
    case Done{w}:
      Empty
    case Fail{e}:
      Unit

def fail_done(-e: String, -w: Main.Walked, h: {Fail{e} == Done{w} : Result<&2, &2, String, Main.Walked>}) -> Empty:
  %h : {rdisc(_) : Type}
  Unit{}

def done_walked(-a: Main.Walked, -b: Main.Walked, h: {Done{a} == Done{b} : Result<&2, &2, String, Main.Walked>}) -> {a == b : Main.Walked}:
  Equal.cong(Result<&2, &2, String, Main.Walked>, Main.Walked, r => Result.default(&2, &2, String, Main.Walked, r, a), Done{a}, Done{b}, h)

def walked_file.at(+head: String, +file: String, +names: List<&2, String>, m: Maybe<&2, List<&2, M.Node>>, +w: Main.Walked, e: {Main.walked.tree(head, file, names, m) == Done{w} : Result<&2, &2, String, Main.Walked>}) -> {Some{Main.walked.file(w)} == M.merged.of(m) : Maybe<&2, List<&2, Ops.Item>>}:
  match m:
    case None{}:
      Empty.absurd({Some{Main.walked.file(w)} == M.merged.of(None{}) : Maybe<&2, List<&2, Ops.Item>>}, fail_done(head ++ ", file " ++ file ++ ": a revision behind it names a position or an item its author's view of the file does not hold; the document was recorded against a different history", w, e))
    case Some{t}:
      (%done_walked(Main.Walked{names, t}, w, e) : {Some{Main.walked.file(_)} == M.merged.of(Some{t}) : Maybe<&2, List<&2, Ops.Item>>}
        {==})

def reads.at(+head: String, +file: String, +names: List<&2, String>, +g: List<&2, M.Rev>, +b: List<&2, Nat>, +w: Main.Walked, ok: Bool, eo: {Main.deepens(g) == ok : Bool}, +hb: {M.distinct(b) == True{} : Bool}, +hc: {M.causal(b, g) == True{} : Bool}, +hs: {M.subset(b, M.upto(List.length(&2, M.Rev, g))) == True{} : Bool}, +ht: {M.subset(M.upto(List.length(&2, M.Rev, g)), b) == True{} : Bool}, e: {Main.walked.causal(head, file, names, g, ok) == Done{w} : Result<&2, &2, String, Main.Walked>}) -> {Some{Main.walked.file(w)} == M.merged(g, b) : Maybe<&2, List<&2, Ops.Item>>}:
  match ok:
    case True{}:
      Equal.trans(Maybe<&2, List<&2, Ops.Item>>, Some{Main.walked.file(w)}, M.merged(g, Main.walked.order(g)), M.merged(g, b),
        walked_file.at(head, file, names, M.walk(Main.walked.order(g), g, Some{Nil{}}), w, e),
        order_converges(g, b, eo, hb, hc, hs, ht))
    case False{}:
      Empty.absurd({Some{Main.walked.file(w)} == M.merged(g, b) : Maybe<&2, List<&2, Ops.Item>>}, fail_done(head ++ ", file " ++ file ++ ": a revision behind it had seen no more revisions than one it had seen, so the ancestry is not a history", w, e))

def reads_every_order(+head: String, +file: String, +names: List<&2, String>, +g: List<&2, M.Rev>, +b: List<&2, Nat>, +w: Main.Walked, +hb: {M.distinct(b) == True{} : Bool}, +hc: {M.causal(b, g) == True{} : Bool}, +hs: {M.subset(b, M.upto(List.length(&2, M.Rev, g))) == True{} : Bool}, +ht: {M.subset(M.upto(List.length(&2, M.Rev, g)), b) == True{} : Bool}, e: {Main.walked.causal(head, file, names, g, Main.deepens(g)) == Done{w} : Result<&2, &2, String, Main.Walked>}) -> {Some{Main.walked.file(w)} == M.merged(g, b) : Maybe<&2, List<&2, Ops.Item>>}:
  reads.at(head, file, names, g, b, w, Main.deepens(g), {==}, hb, hc, hs, ht, e)

# The reading, unfolded: once the ancestry's table and graph are known, the
# tool's reading is the walk of that graph.
def of_causal(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +head: String, +file: String, +ss: List<&2, Tree.Seen>, +g: List<&2, M.Rev>, +hs: {Tree.seen(List.length(&2, Main.Full, Main.walked.ancestry(fs, head)), Main.events_of(Main.walked.ancestry(fs, head)), Nil{}) == Done{ss} : Result<&2, &2, Tree.Fault, List<&2, Tree.Seen>>}, +hg: {Main.walked.revs(Main.walked.ancestry(fs, head), Main.ids(Main.walked.ancestry(fs, head)), Main.minted_digests(Main.walked.ancestry(fs, head), file), ss, ds, file) == Done{g} : Result<&2, &2, String, List<&2, M.Rev>>}) -> {Main.walked.causal(head, file, Main.ids(Main.walked.ancestry(fs, head)), g, Main.deepens(g)) == Main.walked.of(fs, ds, head, file) : Result<&2, &2, String, Main.Walked>}:
  (%Equal.sym(Result<&2, &2, Tree.Fault, List<&2, Tree.Seen>>, Tree.seen(List.length(&2, Main.Full, Main.walked.ancestry(fs, head)), Main.events_of(Main.walked.ancestry(fs, head)), Nil{}), Done{ss}, hs) : {Main.walked.causal(head, file, Main.ids(Main.walked.ancestry(fs, head)), g, Main.deepens(g)) == Main.walked.seen(Main.walked.ancestry(fs, head), ds, head, file, _) : Result<&2, &2, String, Main.Walked>}
    (%Equal.sym(Result<&2, &2, String, List<&2, M.Rev>>, Main.walked.revs(Main.walked.ancestry(fs, head), Main.ids(Main.walked.ancestry(fs, head)), Main.minted_digests(Main.walked.ancestry(fs, head), file), ss, ds, file), Done{g}, hg) : {Main.walked.causal(head, file, Main.ids(Main.walked.ancestry(fs, head)), g, Main.deepens(g)) == Result.bind(&2, &2, String, List<&2, M.Rev>, Main.Walked, _, g => Main.walked.causal(head, file, Main.ids(Main.walked.ancestry(fs, head)), g, Main.deepens(g))) : Result<&2, &2, String, Main.Walked>}
      {==}))

def file_every_order(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +head: String, +file: String, +ss: List<&2, Tree.Seen>, +g: List<&2, M.Rev>, +b: List<&2, Nat>, +w: Main.Walked, +hs: {Tree.seen(List.length(&2, Main.Full, Main.walked.ancestry(fs, head)), Main.events_of(Main.walked.ancestry(fs, head)), Nil{}) == Done{ss} : Result<&2, &2, Tree.Fault, List<&2, Tree.Seen>>}, +hg: {Main.walked.revs(Main.walked.ancestry(fs, head), Main.ids(Main.walked.ancestry(fs, head)), Main.minted_digests(Main.walked.ancestry(fs, head), file), ss, ds, file) == Done{g} : Result<&2, &2, String, List<&2, M.Rev>>}, +hb: {M.distinct(b) == True{} : Bool}, +hc: {M.causal(b, g) == True{} : Bool}, +hu: {M.subset(b, M.upto(List.length(&2, M.Rev, g))) == True{} : Bool}, +ht: {M.subset(M.upto(List.length(&2, M.Rev, g)), b) == True{} : Bool}, e: {Main.walked.of(fs, ds, head, file) == Done{w} : Result<&2, &2, String, Main.Walked>}) -> {Some{Main.walked.file(w)} == M.merged(g, b) : Maybe<&2, List<&2, Ops.Item>>}:
  reads_every_order(head, file, Main.ids(Main.walked.ancestry(fs, head)), g, b, w, hb, hc, hu, ht,
    Equal.trans(Result<&2, &2, String, Main.Walked>, Main.walked.causal(head, file, Main.ids(Main.walked.ancestry(fs, head)), g, Main.deepens(g)), Main.walked.of(fs, ds, head, file), Done{w}, of_causal(fs, ds, head, file, ss, g, hs, hg), e))
