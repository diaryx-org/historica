# The graph: the merge is a function of what each revision's parents are,
# not the order it lists them.
import Base
import ./tree.bend as T
import ./revision.bend as Rev
import ./string_lemmas.bend as S
import ./tree_lemmas.bend as TL

# Bool
# ----

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

def and_intro(a: Bool, b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, S.false_true(ea))

# Two Bools that imply each other are one Bool.
def bool_iff(a: Bool, b: Bool, ab: {a == True{} : Bool} -> {b == True{} : Bool}, ba: {b == True{} : Bool} -> {a == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, S.false_true(ab({==})))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(ba({==})))

# Membership
# ----------

def member_head(+x: String, rest: List<&2, String>) -> {Rev.member(x <> rest, x) == True{} : Bool}:
  or_left(String.eq(x, x), Rev.member(rest, x), S.eq_refl(x))

def member_tail(y: String, rest: List<&2, String>, +x: String, m: {Rev.member(rest, x) == True{} : Bool}) -> {Rev.member(y <> rest, x) == True{} : Bool}:
  or_right(String.eq(y, x), Rev.member(rest, x), m)

def member_cons(-R: Type, +y: String, +rest: List<&2, String>, +x: String, m: {Rev.member(y <> rest, x) == True{} : Bool}, h: {y == x : String} -> R, t: {Rev.member(rest, x) == True{} : Bool} -> R) -> R:
  or_cases(R, String.eq(y, x), Rev.member(rest, x), m, e => h(S.eq_true(y, x, e)), t)

def member_at(+b: List<&2, String>, +y: String, +x: String, h: {y == x : String}, m: {Rev.member(b, y) == True{} : Bool}) -> {Rev.member(b, x) == True{} : Bool}:
  %h : {Rev.member(b, _) == True{} : Bool}
  m

def in_subset(a: List<&2, String>, +b: List<&2, String>, +x: String, +s: {T.subset_ids(a, b) == True{} : Bool}, m: {Rev.member(a, x) == True{} : Bool}) -> {Rev.member(b, x) == True{} : Bool}:
  match a:
    case Nil{}:
      Empty.absurd({Rev.member(b, x) == True{} : Bool}, S.false_true(m))
    case +y <> +rest:
      member_cons({Rev.member(b, x) == True{} : Bool}, y, rest, x, m, h => member_at(b, y, x, h, TL.and_left(Rev.member(b, y), T.subset_ids(rest, b), s)), t => in_subset(rest, b, x, TL.and_right(Rev.member(b, y), T.subset_ids(rest, b), s), t))

def subset_weak(a: List<&2, String>, +m: List<&2, String>, +y: String, +s: {T.subset_ids(a, m) == True{} : Bool}) -> {T.subset_ids(a, y <> m) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case +z <> +rest:
      and_intro(Rev.member(y <> m, z), T.subset_ids(rest, y <> m), member_tail(y, m, z, TL.and_left(Rev.member(m, z), T.subset_ids(rest, m), s)), subset_weak(rest, m, y, TL.and_right(Rev.member(m, z), T.subset_ids(rest, m), s)))

def subset_refl(+a: List<&2, String>) -> {T.subset_ids(a, a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case +y <> +rest:
      and_intro(Rev.member(y <> rest, y), T.subset_ids(rest, y <> rest), member_head(y, rest), subset_weak(rest, rest, y, subset_refl(rest)))

def same_sym(+a: List<&2, String>, +b: List<&2, String>, +s: {T.same_ids(a, b) == True{} : Bool}) -> {T.same_ids(b, a) == True{} : Bool}:
  and_intro(T.subset_ids(b, a), T.subset_ids(a, b), TL.and_right(T.subset_ids(a, b), T.subset_ids(b, a), s), TL.and_left(T.subset_ids(a, b), T.subset_ids(b, a), s))

def same_mem(+a: List<&2, String>, +b: List<&2, String>, +x: String, +s: {T.same_ids(a, b) == True{} : Bool}) -> {Rev.member(a, x) == Rev.member(b, x) : Bool}:
  bool_iff(Rev.member(a, x), Rev.member(b, x), m => in_subset(a, b, x, TL.and_left(T.subset_ids(a, b), T.subset_ids(b, a), s), m), m => in_subset(b, a, x, TL.and_right(T.subset_ids(a, b), T.subset_ids(b, a), s), m))

# Membership through append, without, and union
# ---------------------------------------------

def append_mem(xs: List<&2, String>, +ys: List<&2, String>, +x: String, m: {Rev.member(List.append(&2, String, xs, ys), x) == True{} : Bool}) -> {Bool.or(Rev.member(xs, x), Rev.member(ys, x)) == True{} : Bool}:
  match xs:
    case Nil{}:
      m
    case +y <> +rest:
      or_cases({Bool.or(Bool.or(String.eq(y, x), Rev.member(rest, x)), Rev.member(ys, x)) == True{} : Bool}, String.eq(y, x), Rev.member(List.append(&2, String, rest, ys), x), m, h => or_left(Bool.or(String.eq(y, x), Rev.member(rest, x)), Rev.member(ys, x), or_left(String.eq(y, x), Rev.member(rest, x), h)), t => or_cases({Bool.or(Bool.or(String.eq(y, x), Rev.member(rest, x)), Rev.member(ys, x)) == True{} : Bool}, Rev.member(rest, x), Rev.member(ys, x), append_mem(rest, ys, x, t), l => or_left(Bool.or(String.eq(y, x), Rev.member(rest, x)), Rev.member(ys, x), or_right(String.eq(y, x), Rev.member(rest, x), l)), r => or_right(Bool.or(String.eq(y, x), Rev.member(rest, x)), Rev.member(ys, x), r)))

def append_left(xs: List<&2, String>, +ys: List<&2, String>, +x: String, m: {Rev.member(xs, x) == True{} : Bool}) -> {Rev.member(List.append(&2, String, xs, ys), x) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Rev.member(ys, x) == True{} : Bool}, S.false_true(m))
    case +y <> +rest:
      or_cases({Bool.or(String.eq(y, x), Rev.member(List.append(&2, String, rest, ys), x)) == True{} : Bool}, String.eq(y, x), Rev.member(rest, x), m, h => or_left(String.eq(y, x), Rev.member(List.append(&2, String, rest, ys), x), h), t => or_right(String.eq(y, x), Rev.member(List.append(&2, String, rest, ys), x), append_left(rest, ys, x, t)))

def append_right(xs: List<&2, String>, +ys: List<&2, String>, +x: String, m: {Rev.member(ys, x) == True{} : Bool}) -> {Rev.member(List.append(&2, String, xs, ys), x) == True{} : Bool}:
  match xs:
    case Nil{}:
      m
    case +y <> +rest:
      or_right(String.eq(y, x), Rev.member(List.append(&2, String, rest, ys), x), append_right(rest, ys, x, m))

def keep_mem(b: Bool, +y: String, +w: List<&2, String>, +x: String, m: {Rev.member(w, x) == True{} : Bool}) -> {Rev.member(Rev.keep(b, y, w), x) == True{} : Bool}:
  match b:
    case True{}:
      member_tail(y, w, x, m)
    case False{}:
      m

def without_sub.of(b: Bool, +y: String, +rest: List<&2, String>, +ys: List<&2, String>, +x: String, m: {Rev.member(Rev.keep(Bool.not(b), y, Rev.without(rest, ys)), x) == True{} : Bool}, ih: {Rev.member(Rev.without(rest, ys), x) == True{} : Bool} -> {Rev.member(rest, x) == True{} : Bool}) -> {Rev.member(y <> rest, x) == True{} : Bool}:
  match b:
    case True{}:
      member_tail(y, rest, x, ih(m))
    case False{}:
      member_cons({Rev.member(y <> rest, x) == True{} : Bool}, y, Rev.without(rest, ys), x, m, h => member_at(y <> rest, y, x, h, member_head(y, rest)), t => member_tail(y, rest, x, ih(t)))

def without_sub(xs: List<&2, String>, +ys: List<&2, String>, +x: String, m: {Rev.member(Rev.without(xs, ys), x) == True{} : Bool}) -> {Rev.member(xs, x) == True{} : Bool}:
  match xs:
    case Nil{}:
      m
    case +y <> +rest:
      without_sub.of(Rev.member(ys, y), y, rest, ys, x, m, w => without_sub(rest, ys, x, w))

def without_head(+y: String, +rest: List<&2, String>, +ys: List<&2, String>, +x: String, h: {y == x : String}, n: {Rev.member(ys, x) == False{} : Bool}) -> {Rev.member(Rev.keep(Bool.not(Rev.member(ys, y)), y, Rev.without(rest, ys)), x) == True{} : Bool}:
  %Equal.sym(String, y, x, h) : {Rev.member(Rev.keep(Bool.not(Rev.member(ys, _)), _, Rev.without(rest, ys)), x) == True{} : Bool}
  %Equal.sym(Bool, Rev.member(ys, x), False{}, n) : {Rev.member(Rev.keep(Bool.not(_), x, Rev.without(rest, ys)), x) == True{} : Bool}
  member_head(x, Rev.without(rest, ys))

def without_in(xs: List<&2, String>, +ys: List<&2, String>, +x: String, m: {Rev.member(xs, x) == True{} : Bool}, +n: {Rev.member(ys, x) == False{} : Bool}) -> {Rev.member(Rev.without(xs, ys), x) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Rev.member(Nil{}, x) == True{} : Bool}, S.false_true(m))
    case +y <> +rest:
      member_cons({Rev.member(Rev.keep(Bool.not(Rev.member(ys, y)), y, Rev.without(rest, ys)), x) == True{} : Bool}, y, rest, x, m, h => without_head(y, rest, ys, x, h, n), t => keep_mem(Bool.not(Rev.member(ys, y)), y, Rev.without(rest, ys), x, without_in(rest, ys, x, t, n)))

def union_left(+xs: List<&2, String>, +ys: List<&2, String>, +x: String, m: {Rev.member(xs, x) == True{} : Bool}) -> {Rev.member(T.union_ids(xs, ys), x) == True{} : Bool}:
  bool_cases({Rev.member(T.union_ids(xs, ys), x) == True{} : Bool}, Rev.member(ys, x), t => append_right(Rev.without(xs, ys), ys, x, t), f => append_left(Rev.without(xs, ys), ys, x, without_in(xs, ys, x, m, f)))

def union_right(+xs: List<&2, String>, +ys: List<&2, String>, +x: String, m: {Rev.member(ys, x) == True{} : Bool}) -> {Rev.member(T.union_ids(xs, ys), x) == True{} : Bool}:
  append_right(Rev.without(xs, ys), ys, x, m)

def union_cases(-R: Type, +xs: List<&2, String>, +ys: List<&2, String>, +x: String, m: {Rev.member(T.union_ids(xs, ys), x) == True{} : Bool}, l: {Rev.member(xs, x) == True{} : Bool} -> R, r: {Rev.member(ys, x) == True{} : Bool} -> R) -> R:
  or_cases(R, Rev.member(Rev.without(xs, ys), x), Rev.member(ys, x), append_mem(Rev.without(xs, ys), ys, x, m), w => l(without_sub(xs, ys, x, w)), r)

# Who had seen whom, up to the order of the ancestors
# --------------------------------------------------

# Two ancestor tables naming the same revisions with the same ancestors,
# as sets.
def seen_alike(ss: List<&2, T.Seen>, ss2: List<&2, T.Seen>) -> Bool:
  match ss ss2:
    case Nil{} Nil{}:
      True{}
    case s <> rest Nil{}:
      False{}
    case Nil{} s2 <> rest2:
      False{}
    case T.Seen{i, as} <> rest T.Seen{i2, as2} <> rest2:
      Bool.and(String.eq(i, i2), Bool.and(T.same_ids(as, as2), seen_alike(rest, rest2)))

def seen_alike_sym(ss: List<&2, T.Seen>, ss2: List<&2, T.Seen>, +al: {seen_alike(ss, ss2) == True{} : Bool}) -> {seen_alike(ss2, ss) == True{} : Bool}:
  match ss ss2:
    case Nil{} Nil{}:
      {==}
    case T.Seen{i, as} <> rest Nil{}:
      Empty.absurd({seen_alike(Nil{}, T.Seen{i, as} <> rest) == True{} : Bool}, S.false_true(al))
    case Nil{} T.Seen{i2, as2} <> rest2:
      Empty.absurd({seen_alike(T.Seen{i2, as2} <> rest2, Nil{}) == True{} : Bool}, S.false_true(al))
    case T.Seen{+i, +as} <> +rest T.Seen{+i2, +as2} <> +rest2:
      %S.eq_true(i, i2, TL.and_left(String.eq(i, i2), Bool.and(T.same_ids(as, as2), seen_alike(rest, rest2)), al)) : {Bool.and(String.eq(_, i), Bool.and(T.same_ids(as2, as), seen_alike(rest2, rest))) == True{} : Bool}
      and_intro(String.eq(i, i), Bool.and(T.same_ids(as2, as), seen_alike(rest2, rest)), S.eq_refl(i), and_intro(T.same_ids(as2, as), seen_alike(rest2, rest), same_sym(as, as2, TL.and_left(T.same_ids(as, as2), seen_alike(rest, rest2), TL.and_right(String.eq(i, i2), Bool.and(T.same_ids(as, as2), seen_alike(rest, rest2)), al))), seen_alike_sym(rest, rest2, TL.and_right(T.same_ids(as, as2), seen_alike(rest, rest2), TL.and_right(String.eq(i, i2), Bool.and(T.same_ids(as, as2), seen_alike(rest, rest2)), al)))))

def is_seen_alike(ss: List<&2, T.Seen>, ss2: List<&2, T.Seen>, +id: String, +al: {seen_alike(ss, ss2) == True{} : Bool}) -> {T.is_seen(ss, id) == T.is_seen(ss2, id) : Bool}:
  match ss ss2:
    case Nil{} Nil{}:
      {==}
    case T.Seen{i, as} <> rest Nil{}:
      Empty.absurd({T.is_seen(T.Seen{i, as} <> rest, id) == T.is_seen(Nil{}, id) : Bool}, S.false_true(al))
    case Nil{} T.Seen{i2, as2} <> rest2:
      Empty.absurd({T.is_seen(Nil{}, id) == T.is_seen(T.Seen{i2, as2} <> rest2, id) : Bool}, S.false_true(al))
    case T.Seen{+i, +as} <> +rest T.Seen{+i2, +as2} <> +rest2:
      %S.eq_true(i, i2, TL.and_left(String.eq(i, i2), Bool.and(T.same_ids(as, as2), seen_alike(rest, rest2)), al)) : {Bool.or(String.eq(i, id), T.is_seen(rest, id)) == Bool.or(String.eq(_, id), T.is_seen(rest2, id)) : Bool}
      %is_seen_alike(rest, rest2, id, TL.and_right(T.same_ids(as, as2), seen_alike(rest, rest2), TL.and_right(String.eq(i, i2), Bool.and(T.same_ids(as, as2), seen_alike(rest, rest2)), al))) : {Bool.or(String.eq(i, id), T.is_seen(rest, id)) == Bool.or(String.eq(i, id), _) : Bool}
      {==}

def anc_alike.of(b: Bool, +as: List<&2, String>, +as2: List<&2, String>, +r: List<&2, String>, +r2: List<&2, String>, +x: String, s: {Rev.member(as, x) == Rev.member(as2, x) : Bool}, ih: {Rev.member(r, x) == Rev.member(r2, x) : Bool}) -> {Rev.member(Bool.pick(List<&2, String>, b, as, r), x) == Rev.member(Bool.pick(List<&2, String>, b, as2, r2), x) : Bool}:
  match b:
    case True{}:
      s
    case False{}:
      ih

def anc_alike(ss: List<&2, T.Seen>, ss2: List<&2, T.Seen>, +id: String, +x: String, +al: {seen_alike(ss, ss2) == True{} : Bool}) -> {Rev.member(T.ancestors_of(ss, id), x) == Rev.member(T.ancestors_of(ss2, id), x) : Bool}:
  match ss ss2:
    case Nil{} Nil{}:
      {==}
    case T.Seen{i, as} <> rest Nil{}:
      Empty.absurd({Rev.member(T.ancestors_of(T.Seen{i, as} <> rest, id), x) == Rev.member(T.ancestors_of(Nil{}, id), x) : Bool}, S.false_true(al))
    case Nil{} T.Seen{i2, as2} <> rest2:
      Empty.absurd({Rev.member(T.ancestors_of(Nil{}, id), x) == Rev.member(T.ancestors_of(T.Seen{i2, as2} <> rest2, id), x) : Bool}, S.false_true(al))
    case T.Seen{+i, +as} <> +rest T.Seen{+i2, +as2} <> +rest2:
      %S.eq_true(i, i2, TL.and_left(String.eq(i, i2), Bool.and(T.same_ids(as, as2), seen_alike(rest, rest2)), al)) : {Rev.member(Bool.pick(List<&2, String>, String.eq(i, id), as, T.ancestors_of(rest, id)), x) == Rev.member(Bool.pick(List<&2, String>, String.eq(_, id), as2, T.ancestors_of(rest2, id)), x) : Bool}
      anc_alike.of(String.eq(i, id), as, as2, T.ancestors_of(rest, id), T.ancestors_of(rest2, id), x, same_mem(as, as2, x, TL.and_left(T.same_ids(as, as2), seen_alike(rest, rest2), TL.and_right(String.eq(i, i2), Bool.and(T.same_ids(as, as2), seen_alike(rest, rest2)), al))), anc_alike(rest, rest2, id, x, TL.and_right(T.same_ids(as, as2), seen_alike(rest, rest2), TL.and_right(String.eq(i, i2), Bool.and(T.same_ids(as, as2), seen_alike(rest, rest2)), al))))

def is_ancestor_alike(+ss: List<&2, T.Seen>, +ss2: List<&2, T.Seen>, +earlier: String, +later: String, +al: {seen_alike(ss, ss2) == True{} : Bool}) -> {T.is_ancestor(ss, earlier, later) == T.is_ancestor(ss2, earlier, later) : Bool}:
  anc_alike(ss, ss2, later, earlier, al)

# The closure of a parent list names the same revisions whatever the
# order of the list, or of the ancestor lists it draws on.
def head_has(+q: String, +p: String, +ss: List<&2, T.Seen>, +x: String, h: {q == p : String}, hx: {Bool.or(String.eq(p, x), Rev.member(T.ancestors_of(ss, p), x)) == True{} : Bool}) -> {Rev.member(q <> T.ancestors_of(ss, q), x) == True{} : Bool}:
  %Equal.sym(String, q, p, h) : {Rev.member(_ <> T.ancestors_of(ss, _), x) == True{} : Bool}
  hx

def closure_has(ps: List<&2, String>, +ss: List<&2, T.Seen>, +p: String, +x: String, mp: {Rev.member(ps, p) == True{} : Bool}, +hx: {Bool.or(String.eq(p, x), Rev.member(T.ancestors_of(ss, p), x)) == True{} : Bool}) -> {Rev.member(T.closure(ps, ss), x) == True{} : Bool}:
  match ps:
    case Nil{}:
      Empty.absurd({Rev.member(T.closure(Nil{}, ss), x) == True{} : Bool}, S.false_true(mp))
    case +q <> +rest:
      member_cons({Rev.member(T.closure(q <> rest, ss), x) == True{} : Bool}, q, rest, p, mp, h => union_left(q <> T.ancestors_of(ss, q), T.closure(rest, ss), x, head_has(q, p, ss, x, h, hx)), t => union_right(q <> T.ancestors_of(ss, q), T.closure(rest, ss), x, closure_has(rest, ss, p, x, t, hx)))

def head_alike(+ss: List<&2, T.Seen>, +ss2: List<&2, T.Seen>, +p: String, +x: String, +al: {seen_alike(ss, ss2) == True{} : Bool}, l: {Rev.member(p <> T.ancestors_of(ss, p), x) == True{} : Bool}) -> {Bool.or(String.eq(p, x), Rev.member(T.ancestors_of(ss2, p), x)) == True{} : Bool}:
  %anc_alike(ss, ss2, p, x, al) : {Bool.or(String.eq(p, x), _) == True{} : Bool}
  l

def closure_mem(ps: List<&2, String>, +ps2: List<&2, String>, +ss: List<&2, T.Seen>, +ss2: List<&2, T.Seen>, +x: String, +s: {T.subset_ids(ps, ps2) == True{} : Bool}, +al: {seen_alike(ss, ss2) == True{} : Bool}, m: {Rev.member(T.closure(ps, ss), x) == True{} : Bool}) -> {Rev.member(T.closure(ps2, ss2), x) == True{} : Bool}:
  match ps:
    case Nil{}:
      Empty.absurd({Rev.member(T.closure(ps2, ss2), x) == True{} : Bool}, S.false_true(m))
    case +p <> +rest:
      union_cases({Rev.member(T.closure(ps2, ss2), x) == True{} : Bool}, p <> T.ancestors_of(ss, p), T.closure(rest, ss), x, m, l => closure_has(ps2, ss2, p, x, TL.and_left(Rev.member(ps2, p), T.subset_ids(rest, ps2), s), head_alike(ss, ss2, p, x, al, l)), r => closure_mem(rest, ps2, ss, ss2, x, TL.and_right(Rev.member(ps2, p), T.subset_ids(rest, ps2), s), al, r))

def subset_closure(l: List<&2, String>, +ps: List<&2, String>, +ps2: List<&2, String>, +ss: List<&2, T.Seen>, +ss2: List<&2, T.Seen>, +s: {T.subset_ids(ps, ps2) == True{} : Bool}, +al: {seen_alike(ss, ss2) == True{} : Bool}, +sl: {T.subset_ids(l, T.closure(ps, ss)) == True{} : Bool}) -> {T.subset_ids(l, T.closure(ps2, ss2)) == True{} : Bool}:
  match l:
    case Nil{}:
      {==}
    case +y <> +rest:
      and_intro(Rev.member(T.closure(ps2, ss2), y), T.subset_ids(rest, T.closure(ps2, ss2)), closure_mem(ps, ps2, ss, ss2, y, s, al, TL.and_left(Rev.member(T.closure(ps, ss), y), T.subset_ids(rest, T.closure(ps, ss)), sl)), subset_closure(rest, ps, ps2, ss, ss2, s, al, TL.and_right(Rev.member(T.closure(ps, ss), y), T.subset_ids(rest, T.closure(ps, ss)), sl)))

def closure_same(+ps: List<&2, String>, +ps2: List<&2, String>, +ss: List<&2, T.Seen>, +ss2: List<&2, T.Seen>, +s: {T.same_ids(ps, ps2) == True{} : Bool}, +al: {seen_alike(ss, ss2) == True{} : Bool}) -> {T.same_ids(T.closure(ps, ss), T.closure(ps2, ss2)) == True{} : Bool}:
  and_intro(T.subset_ids(T.closure(ps, ss), T.closure(ps2, ss2)), T.subset_ids(T.closure(ps2, ss2), T.closure(ps, ss)), subset_closure(T.closure(ps, ss), ps, ps2, ss, ss2, TL.and_left(T.subset_ids(ps, ps2), T.subset_ids(ps2, ps), s), al, subset_refl(T.closure(ps, ss))), subset_closure(T.closure(ps2, ss2), ps2, ps, ss2, ss, TL.and_right(T.subset_ids(ps, ps2), T.subset_ids(ps2, ps), s), seen_alike_sym(ss, ss2, al), subset_refl(T.closure(ps2, ss2))))

# Whether every parent is known is the same question of the same set.
def seen_at(+ss: List<&2, T.Seen>, +q: String, +p: String, h: {q == p : String}, e: {T.is_seen(ss, q) == True{} : Bool}) -> {T.is_seen(ss, p) == True{} : Bool}:
  %h : {T.is_seen(ss, _) == True{} : Bool}
  e

def known_mem(+ss: List<&2, T.Seen>, ps: List<&2, String>, +p: String, mp: {Rev.member(ps, p) == True{} : Bool}, +k: {T.known(ss, ps) == True{} : Bool}) -> {T.is_seen(ss, p) == True{} : Bool}:
  match ps:
    case Nil{}:
      Empty.absurd({T.is_seen(ss, p) == True{} : Bool}, S.false_true(mp))
    case +q <> +rest:
      member_cons({T.is_seen(ss, p) == True{} : Bool}, q, rest, p, mp, h => seen_at(ss, q, p, h, TL.and_left(T.is_seen(ss, q), T.known(ss, rest), k)), t => known_mem(ss, rest, p, t, TL.and_right(T.is_seen(ss, q), T.known(ss, rest), k)))

def known_sub(+ss: List<&2, T.Seen>, +ss2: List<&2, T.Seen>, ps: List<&2, String>, +ps2: List<&2, String>, +al: {seen_alike(ss, ss2) == True{} : Bool}, +s: {T.subset_ids(ps, ps2) == True{} : Bool}, +k: {T.known(ss2, ps2) == True{} : Bool}) -> {T.known(ss, ps) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +rest:
      and_intro(T.is_seen(ss, p), T.known(ss, rest), Equal.trans(Bool, T.is_seen(ss, p), T.is_seen(ss2, p), True{}, is_seen_alike(ss, ss2, p, al), known_mem(ss2, ps2, p, TL.and_left(Rev.member(ps2, p), T.subset_ids(rest, ps2), s), k)), known_sub(ss, ss2, rest, ps2, al, TL.and_right(Rev.member(ps2, p), T.subset_ids(rest, ps2), s), k))

def known_alike(+ss: List<&2, T.Seen>, +ss2: List<&2, T.Seen>, +ps: List<&2, String>, +ps2: List<&2, String>, +al: {seen_alike(ss, ss2) == True{} : Bool}, +s: {T.same_ids(ps, ps2) == True{} : Bool}) -> {T.known(ss, ps) == T.known(ss2, ps2) : Bool}:
  bool_iff(T.known(ss, ps), T.known(ss2, ps2), k => known_sub(ss2, ss, ps2, ps, seen_alike_sym(ss, ss2, al), TL.and_right(T.subset_ids(ps, ps2), T.subset_ids(ps2, ps), s), k), k => known_sub(ss, ss2, ps, ps2, al, TL.and_left(T.subset_ids(ps, ps2), T.subset_ids(ps2, ps), s), k))

# Events alike
# ------------
#
# What `T.alike` grants: the same digests, the same facts, parents that
# are one set.

def alike_id(+id: String, +id2: String, +doc: Rev.Rev, +doc2: Rev.Rev, +rest: List<&2, T.Ev>, +rest2: List<&2, T.Ev>, al: {T.alike(T.Ev{id, doc} <> rest, T.Ev{id2, doc2} <> rest2) == True{} : Bool}) -> {id == id2 : String}:
  S.eq_true(id, id2, TL.and_left(String.eq(id, id2), Bool.and(T.rev_alike(doc, doc2), T.alike(rest, rest2)), al))

def alike_doc(+id: String, +id2: String, +doc: Rev.Rev, +doc2: Rev.Rev, +rest: List<&2, T.Ev>, +rest2: List<&2, T.Ev>, al: {T.alike(T.Ev{id, doc} <> rest, T.Ev{id2, doc2} <> rest2) == True{} : Bool}) -> {T.rev_alike(doc, doc2) == True{} : Bool}:
  TL.and_left(T.rev_alike(doc, doc2), T.alike(rest, rest2), TL.and_right(String.eq(id, id2), Bool.and(T.rev_alike(doc, doc2), T.alike(rest, rest2)), al))

def alike_rest(+id: String, +id2: String, +doc: Rev.Rev, +doc2: Rev.Rev, +rest: List<&2, T.Ev>, +rest2: List<&2, T.Ev>, al: {T.alike(T.Ev{id, doc} <> rest, T.Ev{id2, doc2} <> rest2) == True{} : Bool}) -> {T.alike(rest, rest2) == True{} : Bool}:
  TL.and_right(T.rev_alike(doc, doc2), T.alike(rest, rest2), TL.and_right(String.eq(id, id2), Bool.and(T.rev_alike(doc, doc2), T.alike(rest, rest2)), al))

def headers_true(fs: List<&2, Rev.Header>, fs2: List<&2, Rev.Header>, +e: {T.headers_eq(fs, fs2) == True{} : Bool}) -> {fs == fs2 : List<&2, Rev.Header>}:
  match fs fs2:
    case Nil{} Nil{}:
      {==}
    case Rev.Header{k, v} <> rest Nil{}:
      Empty.absurd({Rev.Header{k, v} <> rest == Nil{} : List<&2, Rev.Header>}, S.false_true(e))
    case Nil{} Rev.Header{k2, v2} <> rest2:
      Empty.absurd({Nil{} == Rev.Header{k2, v2} <> rest2 : List<&2, Rev.Header>}, S.false_true(e))
    case Rev.Header{+k, +v} <> +rest Rev.Header{+k2, +v2} <> +rest2:
      %S.eq_true(k, k2, TL.and_left(String.eq(k, k2), String.eq(v, v2), TL.and_left(T.header_eq(Rev.Header{k, v}, Rev.Header{k2, v2}), T.headers_eq(rest, rest2), e))) : {Rev.Header{k, v} <> rest == Rev.Header{_, v2} <> rest2 : List<&2, Rev.Header>}
      %S.eq_true(v, v2, TL.and_right(String.eq(k, k2), String.eq(v, v2), TL.and_left(T.header_eq(Rev.Header{k, v}, Rev.Header{k2, v2}), T.headers_eq(rest, rest2), e))) : {Rev.Header{k, v} <> rest == Rev.Header{k, _} <> rest2 : List<&2, Rev.Header>}
      %headers_true(rest, rest2, TL.and_right(T.header_eq(Rev.Header{k, v}, Rev.Header{k2, v2}), T.headers_eq(rest, rest2), e)) : {Rev.Header{k, v} <> rest == Rev.Header{k, v} <> _ : List<&2, Rev.Header>}
      {==}

def facts_alike(+doc: Rev.Rev, +doc2: Rev.Rev, al: {T.rev_alike(doc, doc2) == True{} : Bool}) -> {T.facts_about(doc) == T.facts_about(doc2) : List<&2, Rev.Header>}:
  headers_true(T.facts_about(doc), T.facts_about(doc2), TL.and_right(T.same_ids(T.parents_of(doc), T.parents_of(doc2)), T.headers_eq(T.facts_about(doc), T.facts_about(doc2)), al))

def parents_alike(+doc: Rev.Rev, +doc2: Rev.Rev, al: {T.rev_alike(doc, doc2) == True{} : Bool}) -> {T.same_ids(T.parents_of(doc), T.parents_of(doc2)) == True{} : Bool}:
  TL.and_left(T.same_ids(T.parents_of(doc), T.parents_of(doc2)), T.headers_eq(T.facts_about(doc), T.facts_about(doc2)), al)

def ev_ids_alike(es: List<&2, T.Ev>, es2: List<&2, T.Ev>, +al: {T.alike(es, es2) == True{} : Bool}) -> {T.ev_ids(es) == T.ev_ids(es2) : List<&2, String>}:
  match es es2:
    case Nil{} Nil{}:
      {==}
    case T.Ev{id, doc} <> rest Nil{}:
      Empty.absurd({T.ev_ids(T.Ev{id, doc} <> rest) == T.ev_ids(Nil{}) : List<&2, String>}, S.false_true(al))
    case Nil{} T.Ev{id2, doc2} <> rest2:
      Empty.absurd({T.ev_ids(Nil{}) == T.ev_ids(T.Ev{id2, doc2} <> rest2) : List<&2, String>}, S.false_true(al))
    case T.Ev{+id, +doc} <> +rest T.Ev{+id2, +doc2} <> +rest2:
      %alike_id(id, id2, doc, doc2, rest, rest2, al) : {id <> T.ev_ids(rest) == _ <> T.ev_ids(rest2) : List<&2, String>}
      %ev_ids_alike(rest, rest2, alike_rest(id, id2, doc, doc2, rest, rest2, al)) : {id <> T.ev_ids(rest) == id <> _ : List<&2, String>}
      {==}

def len_alike(es: List<&2, T.Ev>, es2: List<&2, T.Ev>, +al: {T.alike(es, es2) == True{} : Bool}) -> {List.length(&2, T.Ev, es) == List.length(&2, T.Ev, es2) : Nat}:
  match es es2:
    case Nil{} Nil{}:
      {==}
    case T.Ev{id, doc} <> rest Nil{}:
      Empty.absurd({List.length(&2, T.Ev, T.Ev{id, doc} <> rest) == List.length(&2, T.Ev, Nil{}) : Nat}, S.false_true(al))
    case Nil{} T.Ev{id2, doc2} <> rest2:
      Empty.absurd({List.length(&2, T.Ev, Nil{}) == List.length(&2, T.Ev, T.Ev{id2, doc2} <> rest2) : Nat}, S.false_true(al))
    case T.Ev{+id, +doc} <> +rest T.Ev{+id2, +doc2} <> +rest2:
      %len_alike(rest, rest2, alike_rest(id, id2, doc, doc2, rest, rest2, al)) : {1n+List.length(&2, T.Ev, rest) == 1n+_ : Nat}
      {==}

def is_empty_alike(es: List<&2, T.Ev>, es2: List<&2, T.Ev>, +al: {T.alike(es, es2) == True{} : Bool}) -> {List.is_empty(&2, T.Ev, es) == List.is_empty(&2, T.Ev, es2) : Bool}:
  match es es2:
    case Nil{} Nil{}:
      {==}
    case T.Ev{id, doc} <> rest Nil{}:
      Empty.absurd({List.is_empty(&2, T.Ev, T.Ev{id, doc} <> rest) == List.is_empty(&2, T.Ev, Nil{}) : Bool}, S.false_true(al))
    case Nil{} T.Ev{id2, doc2} <> rest2:
      Empty.absurd({List.is_empty(&2, T.Ev, Nil{}) == List.is_empty(&2, T.Ev, T.Ev{id2, doc2} <> rest2) : Bool}, S.false_true(al))
    case T.Ev{id, doc} <> rest T.Ev{id2, doc2} <> rest2:
      {==}

def gather_alike(es: List<&2, T.Ev>, es2: List<&2, T.Ev>, xs: List<&2, T.Facts>, +al: {T.alike(es, es2) == True{} : Bool}) -> {T.gather(es, xs) == T.gather(es2, xs) : List<&2, T.Facts>}:
  match es es2:
    case Nil{} Nil{}:
      {==}
    case T.Ev{id, doc} <> rest Nil{}:
      Empty.absurd({T.gather(T.Ev{id, doc} <> rest, xs) == T.gather(Nil{}, xs) : List<&2, T.Facts>}, S.false_true(al))
    case Nil{} T.Ev{id2, doc2} <> rest2:
      Empty.absurd({T.gather(Nil{}, xs) == T.gather(T.Ev{id2, doc2} <> rest2, xs) : List<&2, T.Facts>}, S.false_true(al))
    case T.Ev{+id, +doc} <> +rest T.Ev{+id2, +doc2} <> +rest2:
      %alike_id(id, id2, doc, doc2, rest, rest2, al) : {T.gather(rest, T.gather.one(T.facts_about(doc), id, xs)) == T.gather(rest2, T.gather.one(T.facts_about(doc2), _, xs)) : List<&2, T.Facts>}
      %facts_alike(doc, doc2, alike_doc(id, id2, doc, doc2, rest, rest2, al)) : {T.gather(rest, T.gather.one(T.facts_about(doc), id, xs)) == T.gather(rest2, T.gather.one(_, id, xs)) : List<&2, T.Facts>}
      gather_alike(rest, rest2, T.gather.one(T.facts_about(doc), id, xs), alike_rest(id, id2, doc, doc2, rest, rest2, al))

# The ancestor tables built from alike events are alike
# -----------------------------------------------------

def keep_alike(b: Bool, +id: String, +id2: String, +doc: Rev.Rev, +doc2: Rev.Rev, +r: List<&2, T.Ev>, +r2: List<&2, T.Ev>, ei: {String.eq(id, id2) == True{} : Bool}, ed: {T.rev_alike(doc, doc2) == True{} : Bool}, ih: {T.alike(r, r2) == True{} : Bool}) -> {T.alike(T.keep(~T.Ev, b, T.Ev{id, doc}, r), T.keep(~T.Ev, b, T.Ev{id2, doc2}, r2)) == True{} : Bool}:
  match b:
    case True{}:
      and_intro(String.eq(id, id2), Bool.and(T.rev_alike(doc, doc2), T.alike(r, r2)), ei, and_intro(T.rev_alike(doc, doc2), T.alike(r, r2), ed, ih))
    case False{}:
      ih

def ready_alike(es: List<&2, T.Ev>, es2: List<&2, T.Ev>, +ss: List<&2, T.Seen>, +ss2: List<&2, T.Seen>, +al: {T.alike(es, es2) == True{} : Bool}, +sal: {seen_alike(ss, ss2) == True{} : Bool}) -> {T.alike(T.ready(es, ss), T.ready(es2, ss2)) == True{} : Bool}:
  match es es2:
    case Nil{} Nil{}:
      {==}
    case T.Ev{id, doc} <> rest Nil{}:
      Empty.absurd({T.alike(T.ready(T.Ev{id, doc} <> rest, ss), T.ready(Nil{}, ss2)) == True{} : Bool}, S.false_true(al))
    case Nil{} T.Ev{id2, doc2} <> rest2:
      Empty.absurd({T.alike(T.ready(Nil{}, ss), T.ready(T.Ev{id2, doc2} <> rest2, ss2)) == True{} : Bool}, S.false_true(al))
    case T.Ev{+id, +doc} <> +rest T.Ev{+id2, +doc2} <> +rest2:
      %known_alike(ss, ss2, T.parents_of(doc), T.parents_of(doc2), sal, parents_alike(doc, doc2, alike_doc(id, id2, doc, doc2, rest, rest2, al))) : {T.alike(T.keep(~T.Ev, T.known(ss, T.parents_of(doc)), T.Ev{id, doc}, T.ready(rest, ss)), T.keep(~T.Ev, _, T.Ev{id2, doc2}, T.ready(rest2, ss2))) == True{} : Bool}
      keep_alike(T.known(ss, T.parents_of(doc)), id, id2, doc, doc2, T.ready(rest, ss), T.ready(rest2, ss2), TL.and_left(String.eq(id, id2), Bool.and(T.rev_alike(doc, doc2), T.alike(rest, rest2)), al), alike_doc(id, id2, doc, doc2, rest, rest2, al), ready_alike(rest, rest2, ss, ss2, alike_rest(id, id2, doc, doc2, rest, rest2, al), sal))

def stuck_alike(es: List<&2, T.Ev>, es2: List<&2, T.Ev>, +ss: List<&2, T.Seen>, +ss2: List<&2, T.Seen>, +al: {T.alike(es, es2) == True{} : Bool}, +sal: {seen_alike(ss, ss2) == True{} : Bool}) -> {T.alike(T.stuck(es, ss), T.stuck(es2, ss2)) == True{} : Bool}:
  match es es2:
    case Nil{} Nil{}:
      {==}
    case T.Ev{id, doc} <> rest Nil{}:
      Empty.absurd({T.alike(T.stuck(T.Ev{id, doc} <> rest, ss), T.stuck(Nil{}, ss2)) == True{} : Bool}, S.false_true(al))
    case Nil{} T.Ev{id2, doc2} <> rest2:
      Empty.absurd({T.alike(T.stuck(Nil{}, ss), T.stuck(T.Ev{id2, doc2} <> rest2, ss2)) == True{} : Bool}, S.false_true(al))
    case T.Ev{+id, +doc} <> +rest T.Ev{+id2, +doc2} <> +rest2:
      %known_alike(ss, ss2, T.parents_of(doc), T.parents_of(doc2), sal, parents_alike(doc, doc2, alike_doc(id, id2, doc, doc2, rest, rest2, al))) : {T.alike(T.keep(~T.Ev, Bool.not(T.known(ss, T.parents_of(doc))), T.Ev{id, doc}, T.stuck(rest, ss)), T.keep(~T.Ev, Bool.not(_), T.Ev{id2, doc2}, T.stuck(rest2, ss2))) == True{} : Bool}
      keep_alike(Bool.not(T.known(ss, T.parents_of(doc))), id, id2, doc, doc2, T.stuck(rest, ss), T.stuck(rest2, ss2), TL.and_left(String.eq(id, id2), Bool.and(T.rev_alike(doc, doc2), T.alike(rest, rest2)), al), alike_doc(id, id2, doc, doc2, rest, rest2, al), stuck_alike(rest, rest2, ss, ss2, alike_rest(id, id2, doc, doc2, rest, rest2, al), sal))

def seen_add_alike(rd: List<&2, T.Ev>, rd2: List<&2, T.Ev>, +ss: List<&2, T.Seen>, +ss2: List<&2, T.Seen>, +al: {T.alike(rd, rd2) == True{} : Bool}, +sal: {seen_alike(ss, ss2) == True{} : Bool}) -> {seen_alike(T.seen.add(rd, ss), T.seen.add(rd2, ss2)) == True{} : Bool}:
  match rd rd2:
    case Nil{} Nil{}:
      sal
    case T.Ev{id, doc} <> rest Nil{}:
      Empty.absurd({seen_alike(T.seen.add(T.Ev{id, doc} <> rest, ss), T.seen.add(Nil{}, ss2)) == True{} : Bool}, S.false_true(al))
    case Nil{} T.Ev{id2, doc2} <> rest2:
      Empty.absurd({seen_alike(T.seen.add(Nil{}, ss), T.seen.add(T.Ev{id2, doc2} <> rest2, ss2)) == True{} : Bool}, S.false_true(al))
    case T.Ev{+id, +doc} <> +rest T.Ev{+id2, +doc2} <> +rest2:
      and_intro(String.eq(id, id2), Bool.and(T.same_ids(T.closure(T.parents_of(doc), ss), T.closure(T.parents_of(doc2), ss2)), seen_alike(T.seen.add(rest, ss), T.seen.add(rest2, ss2))), TL.and_left(String.eq(id, id2), Bool.and(T.rev_alike(doc, doc2), T.alike(rest, rest2)), al), and_intro(T.same_ids(T.closure(T.parents_of(doc), ss), T.closure(T.parents_of(doc2), ss2)), seen_alike(T.seen.add(rest, ss), T.seen.add(rest2, ss2)), closure_same(T.parents_of(doc), T.parents_of(doc2), ss, ss2, parents_alike(doc, doc2, alike_doc(id, id2, doc, doc2, rest, rest2, al)), sal), seen_add_alike(rest, rest2, ss, ss2, alike_rest(id, id2, doc, doc2, rest, rest2, al), sal)))

# The outcome of building the tables: refused in both, or alike.
def seen_r_alike(r: Result<&2, &2, T.Fault, List<&2, T.Seen>>, r2: Result<&2, &2, T.Fault, List<&2, T.Seen>>) -> Bool:
  match r r2:
    case Fail{e} Fail{e2}:
      True{}
    case Fail{e} Done{ss2}:
      False{}
    case Done{ss} Fail{e2}:
      False{}
    case Done{ss} Done{ss2}:
      seen_alike(ss, ss2)

def seen_done_alike(b: Bool, ss: List<&2, T.Seen>, ss2: List<&2, T.Seen>, sal: {seen_alike(ss, ss2) == True{} : Bool}) -> {seen_r_alike(T.seen.done(b, ss), T.seen.done(b, ss2)) == True{} : Bool}:
  match b:
    case True{}:
      sal
    case False{}:
      {==}

def seen_pick(b: Bool, f: Nat, +es: List<&2, T.Ev>, +es2: List<&2, T.Ev>, +ss: List<&2, T.Seen>, +ss2: List<&2, T.Seen>, +al: {T.alike(es, es2) == True{} : Bool}, +sal: {seen_alike(ss, ss2) == True{} : Bool}, ih: {seen_r_alike(T.seen(f, T.stuck(es, ss), T.seen.add(T.ready(es, ss), ss)), T.seen(f, T.stuck(es2, ss2), T.seen.add(T.ready(es2, ss2), ss2))) == True{} : Bool}) -> {seen_r_alike(Bool.pick(Result<&2, &2, T.Fault, List<&2, T.Seen>>, b, T.seen.done(List.is_empty(&2, T.Ev, T.stuck(es, ss)), ss), T.seen(f, T.stuck(es, ss), T.seen.add(T.ready(es, ss), ss))), Bool.pick(Result<&2, &2, T.Fault, List<&2, T.Seen>>, b, T.seen.done(List.is_empty(&2, T.Ev, T.stuck(es2, ss2)), ss2), T.seen(f, T.stuck(es2, ss2), T.seen.add(T.ready(es2, ss2), ss2)))) == True{} : Bool}:
  match b:
    case True{}:
      %is_empty_alike(T.stuck(es, ss), T.stuck(es2, ss2), stuck_alike(es, es2, ss, ss2, al, sal)) : {seen_r_alike(T.seen.done(List.is_empty(&2, T.Ev, T.stuck(es, ss)), ss), T.seen.done(_, ss2)) == True{} : Bool}
      seen_done_alike(List.is_empty(&2, T.Ev, T.stuck(es, ss)), ss, ss2, sal)
    case False{}:
      ih

def seen_alike_fuel(fuel: Nat, +es: List<&2, T.Ev>, +es2: List<&2, T.Ev>, +ss: List<&2, T.Seen>, +ss2: List<&2, T.Seen>, +al: {T.alike(es, es2) == True{} : Bool}, +sal: {seen_alike(ss, ss2) == True{} : Bool}) -> {seen_r_alike(T.seen(fuel, es, ss), T.seen(fuel, es2, ss2)) == True{} : Bool}:
  match fuel:
    case 0n:
      %is_empty_alike(es, es2, al) : {seen_r_alike(T.seen.done(List.is_empty(&2, T.Ev, es), ss), T.seen.done(_, ss2)) == True{} : Bool}
      seen_done_alike(List.is_empty(&2, T.Ev, es), ss, ss2, sal)
    case 1n++f:
      %is_empty_alike(T.ready(es, ss), T.ready(es2, ss2), ready_alike(es, es2, ss, ss2, al, sal)) : {seen_r_alike(Bool.pick(Result<&2, &2, T.Fault, List<&2, T.Seen>>, List.is_empty(&2, T.Ev, T.ready(es, ss)), T.seen.done(List.is_empty(&2, T.Ev, T.stuck(es, ss)), ss), T.seen(f, T.stuck(es, ss), T.seen.add(T.ready(es, ss), ss))), Bool.pick(Result<&2, &2, T.Fault, List<&2, T.Seen>>, _, T.seen.done(List.is_empty(&2, T.Ev, T.stuck(es2, ss2)), ss2), T.seen(f, T.stuck(es2, ss2), T.seen.add(T.ready(es2, ss2), ss2)))) == True{} : Bool}
      seen_pick(List.is_empty(&2, T.Ev, T.ready(es, ss)), f, es, es2, ss, ss2, al, sal, seen_alike_fuel(f, T.stuck(es, ss), T.stuck(es2, ss2), T.seen.add(T.ready(es, ss), ss), T.seen.add(T.ready(es2, ss2), ss2), stuck_alike(es, es2, ss, ss2, al, sal), seen_add_alike(T.ready(es, ss), T.ready(es2, ss2), ss, ss2, ready_alike(es, es2, ss, ss2, al, sal), sal)))

# Deciding the files reads the tables only as ancestry
# ---------------------------------------------------

def replaced_alike(cs: List<&2, T.Claim>, +by: String, +ss: List<&2, T.Seen>, +ss2: List<&2, T.Seen>, +al: {seen_alike(ss, ss2) == True{} : Bool}) -> {T.replaced(cs, by, ss) == T.replaced(cs, by, ss2) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case T.Claim{+other, what} <> rest:
      %is_ancestor_alike(ss, ss2, by, other, al) : {Bool.or(Bool.and(Bool.not(String.eq(other, by)), T.is_ancestor(ss, by, other)), T.replaced(rest, by, ss)) == Bool.or(Bool.and(Bool.not(String.eq(other, by)), _), T.replaced(rest, by, ss2)) : Bool}
      %replaced_alike(rest, by, ss, ss2, al) : {Bool.or(Bool.and(Bool.not(String.eq(other, by)), T.is_ancestor(ss, by, other)), T.replaced(rest, by, ss)) == Bool.or(Bool.and(Bool.not(String.eq(other, by)), T.is_ancestor(ss, by, other)), _) : Bool}
      {==}

def latest_alike(cs: List<&2, T.Claim>, +all: List<&2, T.Claim>, +ss: List<&2, T.Seen>, +ss2: List<&2, T.Seen>, +al: {seen_alike(ss, ss2) == True{} : Bool}) -> {T.latest(cs, all, ss) == T.latest(cs, all, ss2) : List<&2, T.Claim>}:
  match cs:
    case Nil{}:
      {==}
    case T.Claim{+by, what} <> rest:
      %replaced_alike(all, by, ss, ss2, al) : {T.keep(~T.Claim, Bool.not(T.replaced(all, by, ss)), T.Claim{by, what}, T.latest(rest, all, ss)) == T.keep(~T.Claim, Bool.not(_), T.Claim{by, what}, T.latest(rest, all, ss2)) : List<&2, T.Claim>}
      %latest_alike(rest, all, ss, ss2, al) : {T.keep(~T.Claim, Bool.not(T.replaced(all, by, ss)), T.Claim{by, what}, T.latest(rest, all, ss)) == T.keep(~T.Claim, Bool.not(T.replaced(all, by, ss)), T.Claim{by, what}, _) : List<&2, T.Claim>}
      {==}

def current_alike(+cs: List<&2, T.Claim>, +ss: List<&2, T.Seen>, +ss2: List<&2, T.Seen>, +al: {seen_alike(ss, ss2) == True{} : Bool}) -> {T.current(cs, ss) == T.current(cs, ss2) : List<&2, T.Claim>}:
  %latest_alike(cs, cs, ss, ss2, al) : {T.sorted_claims(T.latest(cs, cs, ss)) == T.sorted_claims(_) : List<&2, T.Claim>}
  {==}

def concurrent_alike(ts: List<&2, String>, +drop: String, +ss: List<&2, T.Seen>, +ss2: List<&2, T.Seen>, +al: {seen_alike(ss, ss2) == True{} : Bool}) -> {T.concurrent(ts, drop, ss) == T.concurrent(ts, drop, ss2) : Bool}:
  match ts:
    case Nil{}:
      {==}
    case +t <> rest:
      %is_ancestor_alike(ss, ss2, t, drop, al) : {Bool.or(Bool.and(Bool.not(String.eq(t, drop)), Bool.not(T.is_ancestor(ss, t, drop))), T.concurrent(rest, drop, ss)) == Bool.or(Bool.and(Bool.not(String.eq(t, drop)), Bool.not(_)), T.concurrent(rest, drop, ss2)) : Bool}
      %concurrent_alike(rest, drop, ss, ss2, al) : {Bool.or(Bool.and(Bool.not(String.eq(t, drop)), Bool.not(T.is_ancestor(ss, t, drop))), T.concurrent(rest, drop, ss)) == Bool.or(Bool.and(Bool.not(String.eq(t, drop)), Bool.not(T.is_ancestor(ss, t, drop))), _) : Bool}
      {==}

def sort_drops_alike(ds: List<&2, String>, +ts: List<&2, String>, +ss: List<&2, T.Seen>, +ss2: List<&2, T.Seen>, +al: {seen_alike(ss, ss2) == True{} : Bool}) -> {T.sort_drops(ds, ts, ss) == T.sort_drops(ds, ts, ss2) : T.Drops}:
  match ds:
    case Nil{}:
      {==}
    case +d <> rest:
      %concurrent_alike(ts, d, ss, ss2, al) : {T.sort_drops.of(T.concurrent(ts, d, ss), d, T.sort_drops(rest, ts, ss)) == T.sort_drops.of(_, d, T.sort_drops(rest, ts, ss2)) : T.Drops}
      %sort_drops_alike(rest, ts, ss, ss2, al) : {T.sort_drops.of(T.concurrent(ts, d, ss), d, T.sort_drops(rest, ts, ss)) == T.sort_drops.of(T.concurrent(ts, d, ss), d, _) : T.Drops}
      {==}

def decide_added_alike(as: List<&2, String>, +file: String, +ps: List<&2, T.Claim>, +ts: List<&2, String>, +ds: List<&2, String>, +ws: List<&2, T.Claim>, +ms: List<&2, T.Claim>, +gs: List<&2, T.Claim>, l: Bool, w: Bool, +ss: List<&2, T.Seen>, +ss2: List<&2, T.Seen>, +al: {seen_alike(ss, ss2) == True{} : Bool}) -> {T.decide.added(as, file, ps, ts, ds, ws, ms, gs, l, w, ss) == T.decide.added(as, file, ps, ts, ds, ws, ms, gs, l, w, ss2) : Result<&2, &2, T.Fault, T.Decided>}:
  match as:
    case Nil{}:
      {==}
    case a <> more:
      %sort_drops_alike(ds, ts, ss, ss2, al) : {Done{T.decide.of(file, T.sort_drops(ds, ts, ss), T.current(ps, ss), T.current(ws, ss), T.current(ms, ss), T.current(gs, ss), T.kind_flags(l, w))} == Done{T.decide.of(file, _, T.current(ps, ss2), T.current(ws, ss2), T.current(ms, ss2), T.current(gs, ss2), T.kind_flags(l, w))} : Result<&2, &2, T.Fault, T.Decided>}
      %current_alike(ps, ss, ss2, al) : {Done{T.decide.of(file, T.sort_drops(ds, ts, ss), T.current(ps, ss), T.current(ws, ss), T.current(ms, ss), T.current(gs, ss), T.kind_flags(l, w))} == Done{T.decide.of(file, T.sort_drops(ds, ts, ss), _, T.current(ws, ss2), T.current(ms, ss2), T.current(gs, ss2), T.kind_flags(l, w))} : Result<&2, &2, T.Fault, T.Decided>}
      %current_alike(ws, ss, ss2, al) : {Done{T.decide.of(file, T.sort_drops(ds, ts, ss), T.current(ps, ss), T.current(ws, ss), T.current(ms, ss), T.current(gs, ss), T.kind_flags(l, w))} == Done{T.decide.of(file, T.sort_drops(ds, ts, ss), T.current(ps, ss), _, T.current(ms, ss2), T.current(gs, ss2), T.kind_flags(l, w))} : Result<&2, &2, T.Fault, T.Decided>}
      %current_alike(ms, ss, ss2, al) : {Done{T.decide.of(file, T.sort_drops(ds, ts, ss), T.current(ps, ss), T.current(ws, ss), T.current(ms, ss), T.current(gs, ss), T.kind_flags(l, w))} == Done{T.decide.of(file, T.sort_drops(ds, ts, ss), T.current(ps, ss), T.current(ws, ss), _, T.current(gs, ss2), T.kind_flags(l, w))} : Result<&2, &2, T.Fault, T.Decided>}
      %current_alike(gs, ss, ss2, al) : {Done{T.decide.of(file, T.sort_drops(ds, ts, ss), T.current(ps, ss), T.current(ws, ss), T.current(ms, ss), T.current(gs, ss), T.kind_flags(l, w))} == Done{T.decide.of(file, T.sort_drops(ds, ts, ss), T.current(ps, ss), T.current(ws, ss), T.current(ms, ss), _, T.kind_flags(l, w))} : Result<&2, &2, T.Fault, T.Decided>}
      {==}

def decide_alike(x: T.Facts, +ss: List<&2, T.Seen>, +ss2: List<&2, T.Seen>, +al: {seen_alike(ss, ss2) == True{} : Bool}) -> {T.decide(x, ss) == T.decide(x, ss2) : Result<&2, &2, T.Fault, T.Decided>}:
  match x:
    case T.Facts{file, ps, ts, ds, as, ws, ms, gs, w, l}:
      decide_added_alike(as, file, ps, ts, ds, ws, ms, gs, l, w, ss, ss2, al)

def decide_all_bind(r: Result<&2, &2, T.Fault, T.Decided>, +rest: List<&2, T.Facts>, +ss: List<&2, T.Seen>, +ss2: List<&2, T.Seen>, +acc: T.Placed, ih: @d: T.Decided -> {T.decide_all(rest, ss, T.place(d, acc)) == T.decide_all(rest, ss2, T.place(d, acc)) : Result<&2, &2, T.Fault, T.Placed>}) -> {Result.bind(&2, &2, T.Fault, T.Decided, T.Placed, r, d => T.decide_all(rest, ss, T.place(d, acc))) == Result.bind(&2, &2, T.Fault, T.Decided, T.Placed, r, d => T.decide_all(rest, ss2, T.place(d, acc))) : Result<&2, &2, T.Fault, T.Placed>}:
  match r:
    case Fail{e}:
      {==}
    case Done{d}:
      ih(d)

def decide_all_alike(xs: List<&2, T.Facts>, +ss: List<&2, T.Seen>, +ss2: List<&2, T.Seen>, +acc: T.Placed, +al: {seen_alike(ss, ss2) == True{} : Bool}) -> {T.decide_all(xs, ss, acc) == T.decide_all(xs, ss2, acc) : Result<&2, &2, T.Fault, T.Placed>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %decide_alike(x, ss, ss2, al) : {Result.bind(&2, &2, T.Fault, T.Decided, T.Placed, T.decide(x, ss), d => T.decide_all(rest, ss, T.place(d, acc))) == Result.bind(&2, &2, T.Fault, T.Decided, T.Placed, _, d => T.decide_all(rest, ss2, T.place(d, acc))) : Result<&2, &2, T.Fault, T.Placed>}
      decide_all_bind(T.decide(x, ss), rest, ss, ss2, acc, d => decide_all_alike(rest, ss, ss2, T.place(d, acc), al))

# Whether every parent was delivered is the same question of the same set
# -----------------------------------------------------------------------

def consdisc(xs: List<&2, String>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case x <> rest:
      Unit

def cons_nil(x: String, rest: List<&2, String>, d: {x <> rest == Nil{} : List<&2, String>}) -> Empty:
  %d : {consdisc(_) : Type}
  Unit{}

def without_nil.of(b: Bool, +q: String, +rest: List<&2, String>, +ids: List<&2, String>, +p: String, eb: {Rev.member(ids, q) == b : Bool}, e: {Rev.keep(Bool.not(b), q, Rev.without(rest, ids)) == Nil{} : List<&2, String>}, mp: {Rev.member(q <> rest, p) == True{} : Bool}, ih: {Rev.without(rest, ids) == Nil{} : List<&2, String>} -> {Rev.member(rest, p) == True{} : Bool} -> {Rev.member(ids, p) == True{} : Bool}) -> {Rev.member(ids, p) == True{} : Bool}:
  match b:
    case False{}:
      Empty.absurd({Rev.member(ids, p) == True{} : Bool}, cons_nil(q, Rev.without(rest, ids), e))
    case True{}:
      member_cons({Rev.member(ids, p) == True{} : Bool}, q, rest, p, mp, h => member_at(ids, q, p, h, eb), t => ih(e, t))

def without_nil_all(ps: List<&2, String>, +ids: List<&2, String>, +p: String, e: {Rev.without(ps, ids) == Nil{} : List<&2, String>}, mp: {Rev.member(ps, p) == True{} : Bool}) -> {Rev.member(ids, p) == True{} : Bool}:
  match ps:
    case Nil{}:
      Empty.absurd({Rev.member(ids, p) == True{} : Bool}, S.false_true(mp))
    case +q <> +rest:
      without_nil.of(Rev.member(ids, q), q, rest, ids, p, {==}, e, mp, w => t => without_nil_all(rest, ids, p, w, t))

def without_nil_sub(ps: List<&2, String>, +ps0: List<&2, String>, +ids: List<&2, String>, +s: {T.subset_ids(ps, ps0) == True{} : Bool}, +e: {Rev.without(ps0, ids) == Nil{} : List<&2, String>}) -> {Rev.without(ps, ids) == Nil{} : List<&2, String>}:
  match ps:
    case Nil{}:
      {==}
    case +q <> +rest:
      %Equal.sym(Bool, Rev.member(ids, q), True{}, without_nil_all(ps0, ids, q, e, TL.and_left(Rev.member(ps0, q), T.subset_ids(rest, ps0), s))) : {Rev.keep(Bool.not(_), q, Rev.without(rest, ids)) == Nil{} : List<&2, String>}
      without_nil_sub(rest, ps0, ids, TL.and_right(Rev.member(ps0, q), T.subset_ids(rest, ps0), s), e)

def delivered_nil(w: List<&2, String>, +id: String, +rest: List<&2, T.Ev>, +ids: List<&2, String>, e: {Result.bind(&2, &2, T.Fault, Unit, Unit, T.delivered_one(w, id), u => T.delivered(rest, ids)) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}) -> {w == Nil{} : List<&2, String>}:
  match w:
    case Nil{}:
      {==}
    case p <> more:
      Empty.absurd({p <> more == Nil{} : List<&2, String>}, TL.fail_done(T.Undelivered{p, id}, e))

def delivered_rest(w: List<&2, String>, +id: String, +rest: List<&2, T.Ev>, +ids: List<&2, String>, e: {Result.bind(&2, &2, T.Fault, Unit, Unit, T.delivered_one(w, id), u => T.delivered(rest, ids)) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}) -> {T.delivered(rest, ids) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}:
  match w:
    case Nil{}:
      e
    case p <> more:
      Empty.absurd({T.delivered(rest, ids) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}, TL.fail_done(T.Undelivered{p, id}, e))

def delivered_alike(es: List<&2, T.Ev>, es2: List<&2, T.Ev>, +ids: List<&2, String>, +al: {T.alike(es, es2) == True{} : Bool}, +e: {T.delivered(es, ids) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}) -> {T.delivered(es2, ids) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}:
  match es es2:
    case Nil{} Nil{}:
      {==}
    case T.Ev{id, doc} <> rest Nil{}:
      Empty.absurd({T.delivered(Nil{}, ids) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}, S.false_true(al))
    case Nil{} T.Ev{id2, doc2} <> rest2:
      Empty.absurd({T.delivered(T.Ev{id2, doc2} <> rest2, ids) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}, S.false_true(al))
    case T.Ev{+id, +doc} <> +rest T.Ev{+id2, +doc2} <> +rest2:
      %Equal.sym(List<&2, String>, Rev.without(T.parents_of(doc2), ids), Nil{}, without_nil_sub(T.parents_of(doc2), T.parents_of(doc), ids, TL.and_right(T.subset_ids(T.parents_of(doc), T.parents_of(doc2)), T.subset_ids(T.parents_of(doc2), T.parents_of(doc)), parents_alike(doc, doc2, alike_doc(id, id2, doc, doc2, rest, rest2, al))), delivered_nil(Rev.without(T.parents_of(doc), ids), id, rest, ids, e))) : {Result.bind(&2, &2, T.Fault, Unit, Unit, T.delivered_one(_, id2), u => T.delivered(rest2, ids)) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}
      delivered_alike(rest, rest2, ids, alike_rest(id, id2, doc, doc2, rest, rest2, al), delivered_rest(Rev.without(T.parents_of(doc), ids), id, rest, ids, e))

# The merge
# ---------

def mergeddisc(r: Result<&2, &2, T.Fault, T.Merged>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{m}:
      Empty

def fail_merged(x: T.Fault, m: T.Merged, d: {Fail{x} == Done{m} : Result<&2, &2, T.Fault, T.Merged>}) -> Empty:
  %d : {mergeddisc(_) : Type}
  Unit{}

def merge_seen(r: Result<&2, &2, T.Fault, List<&2, T.Seen>>, r2: Result<&2, &2, T.Fault, List<&2, T.Seen>>, +es: List<&2, T.Ev>, +es2: List<&2, T.Ev>, m: T.Merged, +al: {T.alike(es, es2) == True{} : Bool}, sal: {seen_r_alike(r, r2) == True{} : Bool}, e: {T.merge.seen(r, es) == Done{m} : Result<&2, &2, T.Fault, T.Merged>}) -> {T.merge.seen(r2, es2) == Done{m} : Result<&2, &2, T.Fault, T.Merged>}:
  match r r2:
    case Fail{x} Fail{x2}:
      Empty.absurd({Fail{x2} == Done{m} : Result<&2, &2, T.Fault, T.Merged>}, fail_merged(x, m, e))
    case Fail{x} Done{ss2}:
      Empty.absurd({T.merge.seen(Done{ss2}, es2) == Done{m} : Result<&2, &2, T.Fault, T.Merged>}, fail_merged(x, m, e))
    case Done{ss} Fail{x2}:
      Empty.absurd({Fail{x2} == Done{m} : Result<&2, &2, T.Fault, T.Merged>}, S.false_true(sal))
    case Done{+ss} Done{+ss2}:
      %gather_alike(es, es2, Nil{}, al) : {T.merge.decided(T.decide_all(_, ss2, T.Placed{T.empty(), Nil{}, Nil{}}), List.length(&2, T.Ev, es2)) == Done{m} : Result<&2, &2, T.Fault, T.Merged>}
      %len_alike(es, es2, al) : {T.merge.decided(T.decide_all(T.gather(es, Nil{}), ss2, T.Placed{T.empty(), Nil{}, Nil{}}), _) == Done{m} : Result<&2, &2, T.Fault, T.Merged>}
      %decide_all_alike(T.gather(es, Nil{}), ss, ss2, T.Placed{T.empty(), Nil{}, Nil{}}, sal) : {T.merge.decided(_, List.length(&2, T.Ev, es)) == Done{m} : Result<&2, &2, T.Fault, T.Merged>}
      e

def merge_delivered(r: Result<&2, &2, T.Fault, Unit>, +es: List<&2, T.Ev>, +es2: List<&2, T.Ev>, m: T.Merged, +al: {T.alike(es, es2) == True{} : Bool}, er: {T.delivered(es, T.ev_ids(es)) == r : Result<&2, &2, T.Fault, Unit>}, e: {T.merge.delivered(r, es) == Done{m} : Result<&2, &2, T.Fault, T.Merged>}) -> {T.merge.delivered(T.delivered(es2, T.ev_ids(es)), es2) == Done{m} : Result<&2, &2, T.Fault, T.Merged>}:
  match r:
    case Fail{x}:
      Empty.absurd({T.merge.delivered(T.delivered(es2, T.ev_ids(es)), es2) == Done{m} : Result<&2, &2, T.Fault, T.Merged>}, fail_merged(x, m, e))
    case Done{u}:
      match u:
        case Unit{}:
          %Equal.sym(Result<&2, &2, T.Fault, Unit>, T.delivered(es2, T.ev_ids(es)), Done{Unit{}}, delivered_alike(es, es2, T.ev_ids(es), al, er)) : {T.merge.delivered(_, es2) == Done{m} : Result<&2, &2, T.Fault, T.Merged>}
          %len_alike(es, es2, al) : {T.merge.seen(T.seen(_, es2, Nil{}), es2) == Done{m} : Result<&2, &2, T.Fault, T.Merged>}
          merge_seen(T.seen(List.length(&2, T.Ev, es), es, Nil{}), T.seen(List.length(&2, T.Ev, es), es2, Nil{}), es, es2, m, al, seen_alike_fuel(List.length(&2, T.Ev, es), es, es2, Nil{}, Nil{}, al, {==}), e)

# The merge of alike graphs is one merge: what each revision's parents
# are decides it, not the order they are listed in.
def merge_alike(+es: List<&2, T.Ev>, +es2: List<&2, T.Ev>, m: T.Merged, +al: {T.alike(es, es2) == True{} : Bool}, e: {T.merge(es) == Done{m} : Result<&2, &2, T.Fault, T.Merged>}) -> {T.merge(es2) == Done{m} : Result<&2, &2, T.Fault, T.Merged>}:
  %ev_ids_alike(es, es2, al) : {T.merge.delivered(T.delivered(es2, _), es2) == Done{m} : Result<&2, &2, T.Fault, T.Merged>}
  merge_delivered(T.delivered(es, T.ev_ids(es)), es, es2, m, al, {==}, e)

def main() -> IO(Unit):
  IO.print("ok")
