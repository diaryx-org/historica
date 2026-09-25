# The revision writer spells what the parser read: `Rev.write(r) == s`
# whenever `Rev.parse(s) == Done{r}`.
import Base
import ./revision.bend as Rev
import ./text.bend as T
import ./composition_lemmas.bend as Comp
import ./equality_lemmas.bend as Eq
import ./string_lemmas.bend as Str
import ./spelling_lemmas.bend as Spell

# Which key a header is
# ---------------------

# The name of each key that has one fixed name, by rank.
def name_at(n: Nat) -> String:
  match n:
    case 0n:
      "change"
    case 1n:
      "parent"
    case 2n:
      "supersedes"
    case 3n:
      "author"
    case 4n:
      "when"
    case 5n:
      "revised-by"
    case 6n:
      "revised"
    case _:
      SNil{}

def named_low(-k: String, b: Bool, e: {Nat.is_lt(Rev.rank(Rev.classify.named(k, b)), 7n) == True{} : Bool}) -> Empty:
  match b:
    case True{}:
      Comp.false_true(e)
    case False{}:
      Comp.false_true(e)

# Every entry of the table below rank seven carries its key's own name.
def entry_ok.of(name: String, key: Rev.Key, low: Bool) -> Bool:
  match low:
    case True{}:
      T.same(name, name_at(Rev.rank(key)))
    case False{}:
      True{}

def table_ok(table: List<&2, Rev.Named>) -> Bool:
  match table:
    case Nil{}:
      True{}
    case Rev.Named{name, +key} <> rest:
      Bool.and(entry_ok.of(name, key, Nat.is_lt(Rev.rank(key), 7n)), table_ok(rest))

def entry_named(+k: String, +name: String, +key: Rev.Key, low: Bool, el: {Nat.is_lt(Rev.rank(key), 7n) == low : Bool}, ok: {entry_ok.of(name, key, low) == True{} : Bool}, same: {T.same(k, name) == True{} : Bool}, e: {Nat.is_lt(Rev.rank(key), 7n) == True{} : Bool}) -> {k == name_at(Rev.rank(key)) : String}:
  match low:
    case True{}:
      Equal.trans(String, k, name, name_at(Rev.rank(key)), Eq.same_eq(k, name, same), Eq.same_eq(name, name_at(Rev.rank(key)), ok))
    case False{}:
      Empty.absurd({k == name_at(Rev.rank(key)) : String}, Comp.false_true(Equal.trans(Bool, False{}, Nat.is_lt(Rev.rank(key), 7n), True{}, Equal.sym(Bool, Nat.is_lt(Rev.rank(key), 7n), False{}, el), e)))

def go_pick(+k: String, +name: String, +key: Rev.Key, -rest: Rev.Key, c: Bool, ec: {T.same(k, name) == c : Bool}, ok: {entry_ok.of(name, key, Nat.is_lt(Rev.rank(key), 7n)) == True{} : Bool}, e: {Nat.is_lt(Rev.rank(Bool.pick(Rev.Key, c, key, rest)), 7n) == True{} : Bool}, ih: {Nat.is_lt(Rev.rank(rest), 7n) == True{} : Bool} -> {k == name_at(Rev.rank(rest)) : String}) -> {k == name_at(Rev.rank(Bool.pick(Rev.Key, c, key, rest))) : String}:
  match c:
    case True{}:
      entry_named(k, name, key, Nat.is_lt(Rev.rank(key), 7n), {==}, ok, ec, e)
    case False{}:
      ih(e)

def go_named(table: List<&2, Rev.Named>, +k: String, +ok: {table_ok(table) == True{} : Bool}, e: {Nat.is_lt(Rev.rank(Rev.classify.go(table, k)), 7n) == True{} : Bool}) -> {k == name_at(Rev.rank(Rev.classify.go(table, k))) : String}:
  match table:
    case Nil{}:
      Empty.absurd({k == name_at(Rev.rank(Rev.classify.go(Nil{}, k))) : String}, named_low(k, T.has_char(k, '.'), e))
    case Rev.Named{+name, +key} <> rest:
      go_pick(k, name, key, Rev.classify.go(rest, k), T.same(k, name), {==},
        Comp.and_left(entry_ok.of(name, key, Nat.is_lt(Rev.rank(key), 7n)), table_ok(rest), ok), e,
        x => go_named(rest, k, Comp.and_right(entry_ok.of(name, key, Nat.is_lt(Rev.rank(key), 7n)), table_ok(rest), ok), x))

# A header whose key ranks below seven is spelled with that rank's name.
def classify_named(+k: String, e: {Nat.is_lt(Rev.rank(Rev.classify(k)), 7n) == True{} : Bool}) -> {k == name_at(Rev.rank(Rev.classify(k))) : String}:
  go_named(Rev.keys(), k, {==}, e)

# Comparing naturals
# ------------------

def cmp_refl(n: Nat) -> {Nat.cmp(n, n) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      cmp_refl(p)

def cmpdisc(c: Cmp) -> Type:
  match c:
    case LT{}:
      Unit
    case EQ{}:
      Empty
    case GT{}:
      Empty

def lt_not_eq(e: {LT{} == EQ{} : Cmp}) -> Empty:
  %e : {cmpdisc(_) : Type}
  Unit{}

def lt_not_gt(e: {LT{} == GT{} : Cmp}) -> Empty:
  %e : {cmpdisc(_) : Type}
  Unit{}

def cmp_eq(a: Nat, b: Nat, e: {Nat.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, lt_not_eq(e))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, Comp.false_true(Equal.cong(Cmp, Bool, Cmp.is_eq, GT{}, EQ{}, e)))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, cmp_eq(p, q, e))

# `a < b` read the other way round.
def lt_flip(a: Nat, b: Nat, e: {Nat.cmp(a, b) == LT{} : Cmp}) -> {Nat.cmp(b, a) == GT{} : Cmp}:
  match a b:
    case 0n 0n:
      Empty.absurd({EQ{} == GT{} : Cmp}, Comp.false_true(Equal.cong(Cmp, Bool, Cmp.is_lt, EQ{}, LT{}, e)))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({LT{} == GT{} : Cmp}, Comp.false_true(Equal.cong(Cmp, Bool, Cmp.is_lt, GT{}, LT{}, e)))
    case 1n+p 1n+q:
      lt_flip(p, q, e)

def lt_not_zero(a: Nat, e: {Nat.cmp(a, 0n) == LT{} : Cmp}) -> Empty:
  match a:
    case 0n:
      Comp.false_true(Equal.cong(Cmp, Bool, Cmp.is_lt, EQ{}, LT{}, e))
    case 1n+p:
      Comp.false_true(Equal.cong(Cmp, Bool, Cmp.is_lt, GT{}, LT{}, e))

# `a < b` and `b <= c` make `a < c`.
def lt_ge_trans(a: Nat, b: Nat, c: Nat, e1: {Nat.cmp(a, b) == LT{} : Cmp}, e2: {Nat.is_ge(c, b) == True{} : Bool}) -> {Nat.cmp(a, c) == LT{} : Cmp}:
  match a b c:
    case _ 0n _:
      Empty.absurd({Nat.cmp(a, c) == LT{} : Cmp}, lt_not_zero(a, e1))
    case 0n 1n+q 0n:
      Empty.absurd({EQ{} == LT{} : Cmp}, Comp.false_true(e2))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 0n:
      Empty.absurd({GT{} == LT{} : Cmp}, Comp.false_true(e2))
    case 1n+p 1n+q 1n+r:
      lt_ge_trans(p, q, r, e1, e2)

def lt_succ(x: Nat, r: Nat, e: {Nat.cmp(x, r) == LT{} : Cmp}) -> {Nat.cmp(x, 1n+r) == LT{} : Cmp}:
  match x r:
    case _ 0n:
      Empty.absurd({Nat.cmp(x, 1n) == LT{} : Cmp}, lt_not_zero(x, e))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      lt_succ(p, q, e)

def lt_self_succ(r: Nat) -> {Nat.cmp(r, 1n+r) == LT{} : Cmp}:
  match r:
    case 0n:
      {==}
    case 1n+q:
      lt_self_succ(q)

def eq_succ(+x: Nat, r: Nat, e: {Nat.cmp(x, r) == EQ{} : Cmp}) -> {Nat.cmp(x, 1n+r) == LT{} : Cmp}:
  %cmp_eq(x, r, e) : {Nat.cmp(x, 1n+_) == LT{} : Cmp}
  lt_self_succ(x)

def ge_zero(x: Nat) -> {Nat.is_ge(x, 0n) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def gt_succ(x: Nat, r: Nat, e: {Nat.cmp(x, r) == GT{} : Cmp}) -> {Nat.is_ge(x, 1n+r) == True{} : Bool}:
  match x r:
    case 0n 0n:
      Empty.absurd({Nat.is_ge(0n, 1n) == True{} : Bool}, Comp.false_true(Equal.cong(Cmp, Bool, Cmp.is_eq, GT{}, EQ{}, Equal.sym(Cmp, EQ{}, GT{}, e))))
    case 0n 1n+q:
      Empty.absurd({Nat.is_ge(0n, 2n+q) == True{} : Bool}, lt_not_gt(e))
    case 1n+p 0n:
      ge_zero(p)
    case 1n+p 1n+q:
      gt_succ(p, q, e)

def ge_trans(a: Nat, b: Nat, c: Nat, e1: {Nat.is_ge(a, b) == True{} : Bool}, e2: {Nat.is_ge(b, c) == True{} : Bool}) -> {Nat.is_ge(a, c) == True{} : Bool}:
  match a b c:
    case _ _ 0n:
      ge_zero(a)
    case _ 0n 1n+r:
      Empty.absurd({Nat.is_ge(a, 1n+r) == True{} : Bool}, Comp.false_true(e2))
    case 0n 1n+q 1n+r:
      Empty.absurd({Nat.is_ge(0n, 1n+r) == True{} : Bool}, Comp.false_true(e1))
    case 1n+p 1n+q 1n+r:
      ge_trans(p, q, r, e1, e2)

def both(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, Comp.false_true(ea))

# Validation sorts the headers
# ----------------------------

# Whether a header of rank comparing `c` to the last one's may follow it:
# anything may come first, and after that the rank may rise, or stay if the
# key repeats.
def later(c: Cmp, rep: Bool) -> Bool:
  match c:
    case LT{}:
      False{}
    case EQ{}:
      rep
    case GT{}:
      True{}

def step(fresh: Bool, c: Cmp, rep: Bool) -> Bool:
  Bool.or(fresh, later(c, rep))

def sorted(hs: List<&2, Rev.Header>, lr: Nat, fresh: Bool) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Rev.Header{+k, v} <> rest:
      Bool.and(step(fresh, Nat.cmp(Rev.rank(Rev.classify(k)), lr), Rev.repeatable(Rev.classify(k))), sorted(rest, Rev.rank(Rev.classify(k)), False{}))

def fresh_of(last: Maybe<&2, Rev.Header>) -> Bool:
  match last:
    case None{}:
      True{}
    case Some{h}:
      False{}

def somedisc(m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def some_none(-x: String, e: {Some{x} == None{} : Maybe<&2, String>}) -> Empty:
  %Equal.sym(Maybe<&2, String>, Some{x}, None{}, e) : {somedisc(_) : Type}
  Unit{}

def or_left(a: Maybe<&2, String>, -b: Maybe<&2, String>, e: {Maybe.or(&2, String, a, b) == None{} : Maybe<&2, String>}) -> {a == None{} : Maybe<&2, String>}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, String>}, some_none(x, e))

def or_right(a: Maybe<&2, String>, -b: Maybe<&2, String>, e: {Maybe.or(&2, String, a, b) == None{} : Maybe<&2, String>}) -> {b == None{} : Maybe<&2, String>}:
  match a:
    case None{}:
      e
    case Some{x}:
      Empty.absurd({b == None{} : Maybe<&2, String>}, some_none(x, e))

def line_none(-at: Nat, c: Maybe<&2, String>, e: {Rev.line_error(at, c) == None{} : Maybe<&2, String>}) -> {c == None{} : Maybe<&2, String>}:
  match c:
    case None{}:
      {==}
    case Some{msg}:
      Empty.absurd({Some{msg} == None{} : Maybe<&2, String>}, some_none("line " ++ Nat.show(at) ++ ": " ++ msg, e))

def same_rank_rep(k: Rev.Key, rep: Bool, er: {Rev.repeatable(k) == rep : Bool}, -key: String, -value: String, -lk: String, -lv: String, -ext: Bool, e: {Rev.order.same_rank.of(key, value, lk, lv, rep, ext) == None{} : Maybe<&2, String>}) -> {Rev.repeatable(k) == True{} : Bool}:
  match rep:
    case False{}:
      Empty.absurd({Rev.repeatable(k) == True{} : Bool}, some_none("the header `" ++ key ++ "` is repeated", e))
    case True{}:
      er

# What `order` lets through is what `step` allows.
def order_step(+k: Rev.Key, -key: String, -value: String, last: Maybe<&2, Rev.Header>, -lr: Nat, c: Cmp, e: {Rev.order.of(k, key, value, last, lr, c) == None{} : Maybe<&2, String>}) -> {step(fresh_of(last), c, Rev.repeatable(k)) == True{} : Bool}:
  match last:
    case None{}:
      {==}
    case Some{Rev.Header{lk, lv}}:
      match c:
        case LT{}:
          Empty.absurd({step(False{}, LT{}, Rev.repeatable(k)) == True{} : Bool}, some_none("the header `" ++ key ++ "` comes after `" ++ lk ++ "`", e))
        case EQ{}:
          same_rank_rep(k, Rev.repeatable(k), {==}, key, value, lk, lv, Nat.is_eq(Rev.rank(k), 15n), e)
        case GT{}:
          {==}

def known(+k: Rev.Key, +key: String, +value: String, +last: Maybe<&2, Rev.Header>, +lr: Nat, e: {Maybe.or(&2, String, Rev.order(k, key, value, last, lr), Bool.pick(Maybe<&2, String>, Rev.value_ok(k, value), None{}, Some{"a malformed `" ++ key ++ "` value: " ++ value})) == None{} : Maybe<&2, String>}) -> {step(fresh_of(last), Nat.cmp(Rev.rank(k), lr), Rev.repeatable(k)) == True{} : Bool}:
  order_step(k, key, value, last, lr, Nat.cmp(Rev.rank(k), lr), or_left(Rev.order(k, key, value, last, lr), Bool.pick(Maybe<&2, String>, Rev.value_ok(k, value), None{}, Some{"a malformed `" ++ key ++ "` value: " ++ value}), e))

def check_step(k: Rev.Key, +key: String, +value: String, +last: Maybe<&2, Rev.Header>, +lr: Nat, e: {Rev.check(k, key, value, last, lr) == None{} : Maybe<&2, String>}) -> {step(fresh_of(last), Nat.cmp(Rev.rank(k), lr), Rev.repeatable(k)) == True{} : Bool}:
  match k:
    case Rev.Key.Change{}:
      known(Rev.Key.Change{}, key, value, last, lr, e)
    case Rev.Key.Parent{}:
      known(Rev.Key.Parent{}, key, value, last, lr, e)
    case Rev.Key.Supersedes{}:
      known(Rev.Key.Supersedes{}, key, value, last, lr, e)
    case Rev.Key.Author{}:
      known(Rev.Key.Author{}, key, value, last, lr, e)
    case Rev.Key.When{}:
      known(Rev.Key.When{}, key, value, last, lr, e)
    case Rev.Key.RevisedBy{}:
      known(Rev.Key.RevisedBy{}, key, value, last, lr, e)
    case Rev.Key.Revised{}:
      known(Rev.Key.Revised{}, key, value, last, lr, e)
    case Rev.Key.Add{}:
      known(Rev.Key.Add{}, key, value, last, lr, e)
    case Rev.Key.Move{}:
      known(Rev.Key.Move{}, key, value, last, lr, e)
    case Rev.Key.Mode{}:
      known(Rev.Key.Mode{}, key, value, last, lr, e)
    case Rev.Key.Drop{}:
      known(Rev.Key.Drop{}, key, value, last, lr, e)
    case Rev.Key.Edit{}:
      known(Rev.Key.Edit{}, key, value, last, lr, e)
    case Rev.Key.Text{}:
      known(Rev.Key.Text{}, key, value, last, lr, e)
    case Rev.Key.Bytes{}:
      known(Rev.Key.Bytes{}, key, value, last, lr, e)
    case Rev.Key.Link{}:
      known(Rev.Key.Link{}, key, value, last, lr, e)
    case Rev.Key.Extension{}:
      known(Rev.Key.Extension{}, key, value, last, lr, e)
    case Rev.Key.Unknown{}:
      Empty.absurd({step(fresh_of(last), Nat.cmp(99n, lr), False{}) == True{} : Bool}, some_none("an unknown header `" ++ key ++ "`", e))

# Whatever `validate` passes is sorted by rank.
def validate_sorted(hs: List<&2, Rev.Header>, +last: Maybe<&2, Rev.Header>, +lr: Nat, +at: Nat, +e: {Rev.validate(hs, Rev.classify_head(hs), last, lr, at) == None{} : Maybe<&2, String>}) -> {sorted(hs, lr, fresh_of(last)) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Rev.Header{+key, +value} <> +rest:
      +e1 = or_left(Rev.line_error(at, Rev.check(Rev.classify(key), key, value, last, lr)), Rev.validate(rest, Rev.classify_head(rest), Some{Rev.Header{key, value}}, Rev.rank(Rev.classify(key)), 1n+at), e)
      +e2 = or_right(Rev.line_error(at, Rev.check(Rev.classify(key), key, value, last, lr)), Rev.validate(rest, Rev.classify_head(rest), Some{Rev.Header{key, value}}, Rev.rank(Rev.classify(key)), 1n+at), e)
      both(step(fresh_of(last), Nat.cmp(Rev.rank(Rev.classify(key)), lr), Rev.repeatable(Rev.classify(key))), sorted(rest, Rev.rank(Rev.classify(key)), False{}),
        check_step(Rev.classify(key), key, value, last, lr, line_none(at, Rev.check(Rev.classify(key), key, value, last, lr), e1)),
        validate_sorted(rest, Some{Rev.Header{key, value}}, Rev.rank(Rev.classify(key)), 1n+at, e2))

# Headers by rank
# ---------------

# The headers of rank `r` or more, and of rank `r` exactly, in order.
def upper(hs: List<&2, Rev.Header>, +r: Nat) -> List<&2, Rev.Header>:
  match hs:
    case Nil{}:
      Nil{}
    case Rev.Header{+k, v} <> rest:
      Rev.keep_header(Nat.is_ge(Rev.rank(Rev.classify(k)), r), Rev.Header{k, v}, upper(rest, r))

def slice(hs: List<&2, Rev.Header>, +r: Nat) -> List<&2, Rev.Header>:
  match hs:
    case Nil{}:
      Nil{}
    case Rev.Header{+k, v} <> rest:
      Rev.keep_header(Nat.is_eq(Rev.rank(Rev.classify(k)), r), Rev.Header{k, v}, slice(rest, r))

def later_ge(c: Cmp, -rep: Bool, e: {later(c, rep) == True{} : Bool}) -> {Cmp.is_ge(c) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(e))
    case EQ{}:
      {==}
    case GT{}:
      {==}

# Nothing of a rank below the last one's follows it.
def none_below(hs: List<&2, Rev.Header>, +lr: Nat, +r: Nat, s: {sorted(hs, lr, False{}) == True{} : Bool}, lt: {Nat.cmp(r, lr) == LT{} : Cmp}) -> {slice(hs, r) == Nil{} : List<&2, Rev.Header>}:
  match hs:
    case Nil{}:
      {==}
    case Rev.Header{+k, v} <> rest:
      +s2 = s
      +lt2 = lt_ge_trans(r, lr, Rev.rank(Rev.classify(k)), lt, later_ge(Nat.cmp(Rev.rank(Rev.classify(k)), lr), Rev.repeatable(Rev.classify(k)), Comp.and_left(later(Nat.cmp(Rev.rank(Rev.classify(k)), lr), Rev.repeatable(Rev.classify(k))), sorted(rest, Rev.rank(Rev.classify(k)), False{}), s2)))
      %Equal.sym(Cmp, Nat.cmp(Rev.rank(Rev.classify(k)), r), GT{}, lt_flip(r, Rev.rank(Rev.classify(k)), lt2)) : {Rev.keep_header(Cmp.is_eq(_), Rev.Header{k, v}, slice(rest, r)) == Nil{} : List<&2, Rev.Header>}
      none_below(rest, Rev.rank(Rev.classify(k)), r, Comp.and_right(later(Nat.cmp(Rev.rank(Rev.classify(k)), lr), Rev.repeatable(Rev.classify(k))), sorted(rest, Rev.rank(Rev.classify(k)), False{}), s2), lt2)

def cons_app(+k: String, +v: String, a: List<&2, Rev.Header>, -b: String) -> {Rev.write_facts(Rev.Header{k, v} <> a) ++ b == k ++ (" " ++ (v ++ ("\n" ++ (Rev.write_facts(a) ++ b)))) : String}:
  %Equal.sym(String, (k ++ (" " ++ (v ++ ("\n" ++ Rev.write_facts(a))))) ++ b, k ++ ((" " ++ (v ++ ("\n" ++ Rev.write_facts(a)))) ++ b), Spell.app_assoc(k, " " ++ (v ++ ("\n" ++ Rev.write_facts(a))), b)) : {_ == k ++ (" " ++ (v ++ ("\n" ++ (Rev.write_facts(a) ++ b)))) : String}
  %Equal.sym(String, (v ++ ("\n" ++ Rev.write_facts(a))) ++ b, v ++ (("\n" ++ Rev.write_facts(a)) ++ b), Spell.app_assoc(v, "\n" ++ Rev.write_facts(a), b)) : {k ++ (" " ++ _) == k ++ (" " ++ (v ++ ("\n" ++ (Rev.write_facts(a) ++ b)))) : String}
  {==}

def gt_flip(a: Nat, b: Nat, e: {Nat.cmp(a, b) == GT{} : Cmp}) -> {Nat.cmp(b, a) == LT{} : Cmp}:
  match a b:
    case 0n 0n:
      Empty.absurd({EQ{} == LT{} : Cmp}, Comp.false_true(Equal.cong(Cmp, Bool, Cmp.is_eq, GT{}, EQ{}, Equal.sym(Cmp, EQ{}, GT{}, e))))
    case 0n 1n+q:
      Empty.absurd({GT{} == LT{} : Cmp}, lt_not_gt(e))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      gt_flip(p, q, e)

# The headers of rank `r` or more are those of rank `r`, then the rest.
def split.at(+k: String, +v: String, +rest: List<&2, Rev.Header>, +r: Nat, c: Cmp, +ec: {Nat.cmp(Rev.rank(Rev.classify(k)), r) == c : Cmp}, s: {sorted(rest, Rev.rank(Rev.classify(k)), False{}) == True{} : Bool}, ih: {Rev.write_facts(upper(rest, r)) == Rev.write_facts(slice(rest, r)) ++ Rev.write_facts(upper(rest, 1n+r)) : String}) -> {Rev.write_facts(Rev.keep_header(Cmp.is_ge(c), Rev.Header{k, v}, upper(rest, r))) == Rev.write_facts(Rev.keep_header(Cmp.is_eq(c), Rev.Header{k, v}, slice(rest, r))) ++ Rev.write_facts(Rev.keep_header(Nat.is_ge(Rev.rank(Rev.classify(k)), 1n+r), Rev.Header{k, v}, upper(rest, 1n+r))) : String}:
  match c:
    case LT{}:
      %Equal.sym(Cmp, Nat.cmp(Rev.rank(Rev.classify(k)), 1n+r), LT{}, lt_succ(Rev.rank(Rev.classify(k)), r, ec)) : {Rev.write_facts(upper(rest, r)) == Rev.write_facts(slice(rest, r)) ++ Rev.write_facts(Rev.keep_header(Cmp.is_ge(_), Rev.Header{k, v}, upper(rest, 1n+r))) : String}
      ih
    case EQ{}:
      %Equal.sym(Cmp, Nat.cmp(Rev.rank(Rev.classify(k)), 1n+r), LT{}, eq_succ(Rev.rank(Rev.classify(k)), r, ec)) : {Rev.write_facts(Rev.Header{k, v} <> upper(rest, r)) == Rev.write_facts(Rev.Header{k, v} <> slice(rest, r)) ++ Rev.write_facts(Rev.keep_header(Cmp.is_ge(_), Rev.Header{k, v}, upper(rest, 1n+r))) : String}
      %Equal.sym(String, Rev.write_facts(Rev.Header{k, v} <> slice(rest, r)) ++ Rev.write_facts(upper(rest, 1n+r)), k ++ (" " ++ (v ++ ("\n" ++ (Rev.write_facts(slice(rest, r)) ++ Rev.write_facts(upper(rest, 1n+r)))))), cons_app(k, v, slice(rest, r), Rev.write_facts(upper(rest, 1n+r)))) : {Rev.write_facts(Rev.Header{k, v} <> upper(rest, r)) == _ : String}
      %Equal.sym(String, Rev.write_facts(upper(rest, r)), Rev.write_facts(slice(rest, r)) ++ Rev.write_facts(upper(rest, 1n+r)), ih) : {k ++ (" " ++ (v ++ ("\n" ++ _))) == k ++ (" " ++ (v ++ ("\n" ++ (Rev.write_facts(slice(rest, r)) ++ Rev.write_facts(upper(rest, 1n+r)))))) : String}
      {==}
    case GT{}:
      +none = none_below(rest, Rev.rank(Rev.classify(k)), r, s, gt_flip(Rev.rank(Rev.classify(k)), r, ec))
      %Equal.sym(Bool, Nat.is_ge(Rev.rank(Rev.classify(k)), 1n+r), True{}, gt_succ(Rev.rank(Rev.classify(k)), r, ec)) : {Rev.write_facts(Rev.Header{k, v} <> upper(rest, r)) == Rev.write_facts(slice(rest, r)) ++ Rev.write_facts(Rev.keep_header(_, Rev.Header{k, v}, upper(rest, 1n+r))) : String}
      %Equal.sym(List<&2, Rev.Header>, slice(rest, r), Nil{}, none) : {Rev.write_facts(Rev.Header{k, v} <> upper(rest, r)) == Rev.write_facts(_) ++ Rev.write_facts(Rev.Header{k, v} <> upper(rest, 1n+r)) : String}
      %Equal.sym(String, Rev.write_facts(upper(rest, r)), Rev.write_facts(slice(rest, r)) ++ Rev.write_facts(upper(rest, 1n+r)), ih) : {k ++ (" " ++ (v ++ ("\n" ++ _))) == k ++ (" " ++ (v ++ ("\n" ++ Rev.write_facts(upper(rest, 1n+r))))) : String}
      %Equal.sym(List<&2, Rev.Header>, slice(rest, r), Nil{}, none) : {k ++ (" " ++ (v ++ ("\n" ++ (Rev.write_facts(_) ++ Rev.write_facts(upper(rest, 1n+r)))))) == k ++ (" " ++ (v ++ ("\n" ++ Rev.write_facts(upper(rest, 1n+r))))) : String}
      {==}

def split(hs: List<&2, Rev.Header>, +lr: Nat, +fresh: Bool, +r: Nat, s: {sorted(hs, lr, fresh) == True{} : Bool}) -> {Rev.write_facts(upper(hs, r)) == Rev.write_facts(slice(hs, r)) ++ Rev.write_facts(upper(hs, 1n+r)) : String}:
  match hs:
    case Nil{}:
      {==}
    case Rev.Header{+k, +v} <> +rest:
      +s2 = Comp.and_right(step(fresh, Nat.cmp(Rev.rank(Rev.classify(k)), lr), Rev.repeatable(Rev.classify(k))), sorted(rest, Rev.rank(Rev.classify(k)), False{}), s)
      split.at(k, v, rest, r, Nat.cmp(Rev.rank(Rev.classify(k)), r), {==}, s2, split(rest, Rev.rank(Rev.classify(k)), False{}, r, s2))

def upper_zero(hs: List<&2, Rev.Header>) -> {upper(hs, 0n) == hs : List<&2, Rev.Header>}:
  match hs:
    case Nil{}:
      {==}
    case Rev.Header{+k, +v} <> +rest:
      %Equal.sym(Bool, Nat.is_ge(Rev.rank(Rev.classify(k)), 0n), True{}, ge_zero(Rev.rank(Rev.classify(k)))) : {Rev.keep_header(_, Rev.Header{k, v}, upper(rest, 0n)) == Rev.Header{k, v} <> rest : List<&2, Rev.Header>}
      Equal.cong(List<&2, Rev.Header>, List<&2, Rev.Header>, t => Rev.Header{k, v} <> t, upper(rest, 0n), rest, upper_zero(rest))

def upper_facts(hs: List<&2, Rev.Header>) -> {upper(hs, 7n) == Rev.facts_of(hs) : List<&2, Rev.Header>}:
  match hs:
    case Nil{}:
      {==}
    case Rev.Header{+k, +v} <> +rest:
      %Equal.sym(List<&2, Rev.Header>, upper(rest, 7n), Rev.facts_of(rest), upper_facts(rest)) : {Rev.keep_header(Nat.is_ge(Rev.rank(Rev.classify(k)), 7n), Rev.Header{k, v}, _) == Rev.facts_of(Rev.Header{k, v} <> rest) : List<&2, Rev.Header>}
      {==}

# Each named key is classified at its own rank.
def rank_name(r: Nat, lt: {Nat.is_lt(r, 7n) == True{} : Bool}) -> {Rev.rank(Rev.classify(name_at(r))) == r : Nat}:
  match r:
    case 0n:
      {==}
    case 1n+r1:
      match r1:
        case 0n:
          {==}
        case 1n+r2:
          match r2:
            case 0n:
              {==}
            case 1n+r3:
              match r3:
                case 0n:
                  {==}
                case 1n+r4:
                  match r4:
                    case 0n:
                      {==}
                    case 1n+r5:
                      match r5:
                        case 0n:
                          {==}
                        case 1n+r6:
                          match r6:
                            case 0n:
                              {==}
                            case 1n+r7:
                              match r7:
                                case 0n:
                                  Empty.absurd({Rev.rank(Rev.classify(name_at(r))) == r : Nat}, Comp.false_true(lt))
                                case 1n+r8:
                                  Empty.absurd({Rev.rank(Rev.classify(name_at(r))) == r : Nat}, Comp.false_true(lt))

# A header of rank `r` below seven is spelled with that rank's name.
def rank_spelled(+k: String, +r: Nat, lt: {Nat.is_lt(r, 7n) == True{} : Bool}, e: {Nat.is_eq(Rev.rank(Rev.classify(k)), r) == True{} : Bool}) -> {k == name_at(r) : String}:
  +er = cmp_eq(Rev.rank(Rev.classify(k)), r, Str.is_eq_true(Nat.cmp(Rev.rank(Rev.classify(k)), r), e))
  %er : {k == name_at(_) : String}
  classify_named(k, Equal.trans(Bool, Nat.is_lt(Rev.rank(Rev.classify(k)), 7n), Nat.is_lt(r, 7n), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(n, 7n), Rev.rank(Rev.classify(k)), r, er), lt))

# `String.eq` against a rank's name picks out that rank.
def eq_rank(+k: String, +r: Nat, lt: {Nat.is_lt(r, 7n) == True{} : Bool}, e: {String.eq(k, name_at(r)) == True{} : Bool}) -> {Rev.rank(Rev.classify(k)) == r : Nat}:
  Equal.trans(Nat, Rev.rank(Rev.classify(k)), Rev.rank(Rev.classify(name_at(r))), r, Equal.cong(String, Nat, t => Rev.rank(Rev.classify(t)), k, name_at(r), Str.eq_true(k, name_at(r), e)), rank_name(r, lt))

def is_eq_refl(+x: Nat, +r: Nat, e: {x == r : Nat}) -> {Nat.is_eq(x, r) == True{} : Bool}:
  %e : {Nat.is_eq(x, _) == True{} : Bool}
  Equal.cong(Cmp, Bool, Cmp.is_eq, Nat.cmp(x, x), EQ{}, cmp_refl(x))

def is_ge_refl(+x: Nat, +r: Nat, e: {x == r : Nat}) -> {Nat.is_ge(x, r) == True{} : Bool}:
  %e : {Nat.is_ge(x, _) == True{} : Bool}
  Equal.cong(Cmp, Bool, Cmp.is_ge, Nat.cmp(x, x), EQ{}, cmp_refl(x))

def slice_values.at(+k: String, +v: String, -rest: List<&2, Rev.Header>, +r: Nat, +lt: {Nat.is_lt(r, 7n) == True{} : Bool}, b1: Bool, e1: {Nat.is_eq(Rev.rank(Rev.classify(k)), r) == b1 : Bool}, b2: Bool, e2: {String.eq(k, name_at(r)) == b2 : Bool}, ih: {Rev.write_facts(slice(rest, r)) == Rev.each(name_at(r), Rev.values_of(rest, name_at(r))) : String}) -> {Rev.write_facts(Rev.keep_header(b1, Rev.Header{k, v}, slice(rest, r))) == Rev.each(name_at(r), Rev.keep(b2, v, Rev.values_of(rest, name_at(r)))) : String}:
  match b1 b2:
    case True{} True{}:
      %ih : {k ++ (" " ++ (v ++ ("\n" ++ Rev.write_facts(slice(rest, r))))) == name_at(r) ++ (" " ++ (v ++ ("\n" ++ _))) : String}
      %rank_spelled(k, r, lt, e1) : {k ++ (" " ++ (v ++ ("\n" ++ Rev.write_facts(slice(rest, r))))) == _ ++ (" " ++ (v ++ ("\n" ++ Rev.write_facts(slice(rest, r))))) : String}
      {==}
    case True{} False{}:
      +ek = rank_spelled(k, r, lt, e1)
      Empty.absurd({Rev.write_facts(Rev.Header{k, v} <> slice(rest, r)) == Rev.each(name_at(r), Rev.values_of(rest, name_at(r))) : String},
        Comp.false_true(Equal.trans(Bool, False{}, String.eq(k, name_at(r)), True{}, Equal.sym(Bool, String.eq(k, name_at(r)), False{}, e2),
          Equal.trans(Bool, String.eq(k, name_at(r)), String.eq(name_at(r), name_at(r)), True{}, Equal.cong(String, Bool, t => String.eq(t, name_at(r)), k, name_at(r), ek), Str.eq_refl(name_at(r))))))
    case False{} True{}:
      Empty.absurd({Rev.write_facts(slice(rest, r)) == Rev.each(name_at(r), v <> Rev.values_of(rest, name_at(r))) : String},
        Comp.false_true(Equal.trans(Bool, False{}, Nat.is_eq(Rev.rank(Rev.classify(k)), r), True{}, Equal.sym(Bool, Nat.is_eq(Rev.rank(Rev.classify(k)), r), False{}, e1), is_eq_refl(Rev.rank(Rev.classify(k)), r, eq_rank(k, r, lt, e2)))))
    case False{} False{}:
      ih

# The headers of a rank below seven are the values under its name.
def slice_values(hs: List<&2, Rev.Header>, +r: Nat, +lt: {Nat.is_lt(r, 7n) == True{} : Bool}) -> {Rev.write_facts(slice(hs, r)) == Rev.each(name_at(r), Rev.values_of(hs, name_at(r))) : String}:
  match hs:
    case Nil{}:
      {==}
    case Rev.Header{+k, +v} <> +rest:
      slice_values.at(k, v, rest, r, lt, Nat.is_eq(Rev.rank(Rev.classify(k)), r), {==}, String.eq(k, name_at(r)), {==}, slice_values(rest, r, lt))

# A key that may not repeat
# -------------------------

def later_stuck.of(c: Cmp, +r: Nat, +lr: Nat, ec: {Nat.cmp(r, lr) == c : Cmp}, ge: {Nat.is_ge(lr, r) == True{} : Bool}, e: {later(c, False{}) == True{} : Bool}) -> Empty:
  match c:
    case LT{}:
      Comp.false_true(e)
    case EQ{}:
      Comp.false_true(e)
    case GT{}:
      Comp.false_true(Equal.trans(Bool, False{}, Nat.is_ge(lr, r), True{}, Equal.cong(Cmp, Bool, Cmp.is_ge, LT{}, Nat.cmp(lr, r), Equal.sym(Cmp, Nat.cmp(lr, r), LT{}, gt_flip(r, lr, ec))), ge))

# A header of rank `r`, whose key may not repeat, cannot follow one of rank
# `r` or more.
def later_stuck(+x: Nat, +rep: Bool, +r: Nat, +lr: Nat, ex: {x == r : Nat}, erep: {rep == False{} : Bool}, ge: {Nat.is_ge(lr, r) == True{} : Bool}, e: {later(Nat.cmp(x, lr), rep) == True{} : Bool}) -> Empty:
  +e1 = Equal.trans(Bool, later(Nat.cmp(r, lr), rep), later(Nat.cmp(x, lr), rep), True{}, Equal.cong(Nat, Bool, y => later(Nat.cmp(y, lr), rep), r, x, Equal.sym(Nat, x, r, ex)), e)
  +e2 = Equal.trans(Bool, later(Nat.cmp(r, lr), False{}), later(Nat.cmp(r, lr), rep), True{}, Equal.cong(Bool, Bool, b => later(Nat.cmp(r, lr), b), False{}, rep, Equal.sym(Bool, rep, False{}, erep)), e1)
  later_stuck.of(Nat.cmp(r, lr), r, lr, {==}, ge, e2)

def none_eq.at(+k: String, -v: String, -rest: List<&2, Rev.Header>, +lr: Nat, +r: Nat, b: Bool, +eb: {String.eq(k, name_at(r)) == b : Bool}, +s: {later(Nat.cmp(Rev.rank(Rev.classify(k)), lr), Rev.repeatable(Rev.classify(k))) == True{} : Bool}, +ge: {Nat.is_ge(lr, r) == True{} : Bool}, +nr: {Rev.repeatable(Rev.classify(name_at(r))) == False{} : Bool}, +lt: {Nat.is_lt(r, 7n) == True{} : Bool}, ih: {Nat.is_ge(Rev.rank(Rev.classify(k)), r) == True{} : Bool} -> {Rev.values_of(rest, name_at(r)) == Nil{} : List<&2, String>}) -> {Rev.keep(b, v, Rev.values_of(rest, name_at(r))) == Nil{} : List<&2, String>}:
  match b:
    case True{}:
      +ek = Str.eq_true(k, name_at(r), eb)
      Empty.absurd({v <> Rev.values_of(rest, name_at(r)) == Nil{} : List<&2, String>},
        later_stuck(Rev.rank(Rev.classify(k)), Rev.repeatable(Rev.classify(k)), r, lr, eq_rank(k, r, lt, eb),
          Equal.trans(Bool, Rev.repeatable(Rev.classify(k)), Rev.repeatable(Rev.classify(name_at(r))), False{}, Equal.cong(String, Bool, t => Rev.repeatable(Rev.classify(t)), k, name_at(r), ek), nr),
          ge, s))
    case False{}:
      ih(ge_trans(Rev.rank(Rev.classify(k)), lr, r, later_ge(Nat.cmp(Rev.rank(Rev.classify(k)), lr), Rev.repeatable(Rev.classify(k)), s), ge))

# After a header of rank `r` or more, no header names a key of rank `r` that
# may not repeat.
def none_eq(hs: List<&2, Rev.Header>, +lr: Nat, +r: Nat, s: {sorted(hs, lr, False{}) == True{} : Bool}, +ge: {Nat.is_ge(lr, r) == True{} : Bool}, +nr: {Rev.repeatable(Rev.classify(name_at(r))) == False{} : Bool}, +lt: {Nat.is_lt(r, 7n) == True{} : Bool}) -> {Rev.values_of(hs, name_at(r)) == Nil{} : List<&2, String>}:
  match hs:
    case Nil{}:
      {==}
    case Rev.Header{+k, +v} <> +rest:
      +s2 = s
      none_eq.at(k, v, rest, lr, r, String.eq(k, name_at(r)), {==},
        Comp.and_left(later(Nat.cmp(Rev.rank(Rev.classify(k)), lr), Rev.repeatable(Rev.classify(k))), sorted(rest, Rev.rank(Rev.classify(k)), False{}), s2),
        ge, nr, lt,
        g => none_eq(rest, Rev.rank(Rev.classify(k)), r, Comp.and_right(later(Nat.cmp(Rev.rank(Rev.classify(k)), lr), Rev.repeatable(Rev.classify(k))), sorted(rest, Rev.rank(Rev.classify(k)), False{}), s2), g, nr, lt))

def opt_list(m: Maybe<&2, String>) -> List<&2, String>:
  match m:
    case None{}:
      Nil{}
    case Some{x}:
      [x]

def single.at(+k: String, +v: String, +rest: List<&2, Rev.Header>, +r: Nat, b: Bool, +eb: {String.eq(k, name_at(r)) == b : Bool}, s: {sorted(rest, Rev.rank(Rev.classify(k)), False{}) == True{} : Bool}, +nr: {Rev.repeatable(Rev.classify(name_at(r))) == False{} : Bool}, +lt: {Nat.is_lt(r, 7n) == True{} : Bool}, ih: {Rev.values_of(rest, name_at(r)) == opt_list(Rev.value_of(rest, name_at(r))) : List<&2, String>}) -> {Rev.keep(b, v, Rev.values_of(rest, name_at(r))) == opt_list(Bool.pick(Maybe<&2, String>, b, Some{v}, Rev.value_of(rest, name_at(r)))) : List<&2, String>}:
  match b:
    case True{}:
      %Equal.sym(List<&2, String>, Rev.values_of(rest, name_at(r)), Nil{}, none_eq(rest, Rev.rank(Rev.classify(k)), r, s, is_ge_refl(Rev.rank(Rev.classify(k)), r, eq_rank(k, r, lt, eb)), nr, lt)) : {v <> _ == [v] : List<&2, String>}
      {==}
    case False{}:
      ih

# A key that may not repeat is stated at most once.
def single(hs: List<&2, Rev.Header>, +lr: Nat, +fresh: Bool, +r: Nat, s: {sorted(hs, lr, fresh) == True{} : Bool}, +nr: {Rev.repeatable(Rev.classify(name_at(r))) == False{} : Bool}, +lt: {Nat.is_lt(r, 7n) == True{} : Bool}) -> {Rev.values_of(hs, name_at(r)) == opt_list(Rev.value_of(hs, name_at(r))) : List<&2, String>}:
  match hs:
    case Nil{}:
      {==}
    case Rev.Header{+k, +v} <> +rest:
      +s2 = Comp.and_right(step(fresh, Nat.cmp(Rev.rank(Rev.classify(k)), lr), Rev.repeatable(Rev.classify(k))), sorted(rest, Rev.rank(Rev.classify(k)), False{}), s)
      single.at(k, v, rest, r, String.eq(k, name_at(r)), {==}, s2, nr, lt, single(rest, Rev.rank(Rev.classify(k)), False{}, r, s2, nr, lt))

def each_opt(+key: String, m: Maybe<&2, String>) -> {Rev.each(key, opt_list(m)) == Rev.optional(key, m) : String}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# The headers, laid out
# ---------------------

def stage_tail(+hs: List<&2, Rev.Header>, +lr: Nat, +fresh: Bool, +r: Nat, +s: {sorted(hs, lr, fresh) == True{} : Bool}, +lt: {Nat.is_lt(r, 7n) == True{} : Bool}, +X: String) -> {Rev.write_facts(upper(hs, r)) ++ X == Rev.each(name_at(r), Rev.values_of(hs, name_at(r))) ++ (Rev.write_facts(upper(hs, 1n+r)) ++ X) : String}:
  Equal.trans(String, Rev.write_facts(upper(hs, r)) ++ X, (Rev.write_facts(slice(hs, r)) ++ Rev.write_facts(upper(hs, 1n+r))) ++ X, Rev.each(name_at(r), Rev.values_of(hs, name_at(r))) ++ (Rev.write_facts(upper(hs, 1n+r)) ++ X),
    Equal.cong(String, String, y => y ++ X, Rev.write_facts(upper(hs, r)), Rev.write_facts(slice(hs, r)) ++ Rev.write_facts(upper(hs, 1n+r)), split(hs, lr, fresh, r, s)),
    Equal.trans(String, (Rev.write_facts(slice(hs, r)) ++ Rev.write_facts(upper(hs, 1n+r))) ++ X, Rev.write_facts(slice(hs, r)) ++ (Rev.write_facts(upper(hs, 1n+r)) ++ X), Rev.each(name_at(r), Rev.values_of(hs, name_at(r))) ++ (Rev.write_facts(upper(hs, 1n+r)) ++ X),
      Spell.app_assoc(Rev.write_facts(slice(hs, r)), Rev.write_facts(upper(hs, 1n+r)), X),
      Equal.cong(String, String, y => y ++ (Rev.write_facts(upper(hs, 1n+r)) ++ X), Rev.write_facts(slice(hs, r)), Rev.each(name_at(r), Rev.values_of(hs, name_at(r))), slice_values(hs, r, lt))))

# Sorted headers are the headers of each named key in rank order, then the
# facts.
def layout(+hs: List<&2, Rev.Header>, +lr: Nat, +fresh: Bool, +s: {sorted(hs, lr, fresh) == True{} : Bool}, +X: String) -> {Rev.write_facts(hs) ++ X == Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X))))))) : String}:
  Equal.trans(String, Rev.write_facts(hs) ++ X, Rev.write_facts(upper(hs, 0n)) ++ X, Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X))))))), Equal.cong(List<&2, Rev.Header>, String, y => Rev.write_facts(y) ++ X, hs, upper(hs, 0n), Equal.sym(List<&2, Rev.Header>, upper(hs, 0n), hs, upper_zero(hs))), Equal.trans(String, Rev.write_facts(upper(hs, 0n)) ++ X, Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.write_facts(upper(hs, 1n)) ++ X), Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X))))))), stage_tail(hs, lr, fresh, 0n, s, {==}, X), Equal.trans(String, Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.write_facts(upper(hs, 1n)) ++ X), Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.write_facts(upper(hs, 2n)) ++ X)), Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X))))))), Equal.cong(String, String, y => Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (y), Rev.write_facts(upper(hs, 1n)) ++ X, Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.write_facts(upper(hs, 2n)) ++ X), stage_tail(hs, lr, fresh, 1n, s, {==}, X)), Equal.trans(String, Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.write_facts(upper(hs, 2n)) ++ X)), Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.write_facts(upper(hs, 3n)) ++ X))), Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X))))))), Equal.cong(String, String, y => Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (y)), Rev.write_facts(upper(hs, 2n)) ++ X, Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.write_facts(upper(hs, 3n)) ++ X), stage_tail(hs, lr, fresh, 2n, s, {==}, X)), Equal.trans(String, Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.write_facts(upper(hs, 3n)) ++ X))), Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.write_facts(upper(hs, 4n)) ++ X)))), Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X))))))), Equal.cong(String, String, y => Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (y))), Rev.write_facts(upper(hs, 3n)) ++ X, Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.write_facts(upper(hs, 4n)) ++ X), stage_tail(hs, lr, fresh, 3n, s, {==}, X)), Equal.trans(String, Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.write_facts(upper(hs, 4n)) ++ X)))), Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.write_facts(upper(hs, 5n)) ++ X))))), Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X))))))), Equal.cong(String, String, y => Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (y)))), Rev.write_facts(upper(hs, 4n)) ++ X, Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.write_facts(upper(hs, 5n)) ++ X), stage_tail(hs, lr, fresh, 4n, s, {==}, X)), Equal.trans(String, Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.write_facts(upper(hs, 5n)) ++ X))))), Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.write_facts(upper(hs, 6n)) ++ X)))))), Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X))))))), Equal.cong(String, String, y => Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (y))))), Rev.write_facts(upper(hs, 5n)) ++ X, Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.write_facts(upper(hs, 6n)) ++ X), stage_tail(hs, lr, fresh, 5n, s, {==}, X)), Equal.trans(String, Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.write_facts(upper(hs, 6n)) ++ X)))))), Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(upper(hs, 7n)) ++ X))))))), Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X))))))), Equal.cong(String, String, y => Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (y)))))), Rev.write_facts(upper(hs, 6n)) ++ X, Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(upper(hs, 7n)) ++ X), stage_tail(hs, lr, fresh, 6n, s, {==}, X)), Equal.cong(List<&2, Rev.Header>, String, y => Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(y) ++ X))))))), upper(hs, 7n), Rev.facts_of(hs), upper_facts(hs))))))))))

def one_line(+key: String, +c: String, -Y: String) -> {Rev.each(key, [c]) ++ Y == key ++ (" " ++ (c ++ ("\n" ++ Y))) : String}:
  cons_app(key, c, Nil{}, Y)

# A key that may not repeat, and is present, is one line.
def single_piece(+hs: List<&2, Rev.Header>, +lr: Nat, +fresh: Bool, +s: {sorted(hs, lr, fresh) == True{} : Bool}, +r: Nat, nr: {Rev.repeatable(Rev.classify(name_at(r))) == False{} : Bool}, lt: {Nat.is_lt(r, 7n) == True{} : Bool}, +c: String, e: {Rev.value_of(hs, name_at(r)) == Some{c} : Maybe<&2, String>}, -Y: String) -> {Rev.each(name_at(r), Rev.values_of(hs, name_at(r))) ++ Y == name_at(r) ++ (" " ++ (c ++ ("\n" ++ Y))) : String}:
  %Equal.sym(List<&2, String>, Rev.values_of(hs, name_at(r)), opt_list(Rev.value_of(hs, name_at(r))), single(hs, lr, fresh, r, s, nr, lt)) : {Rev.each(name_at(r), _) ++ Y == name_at(r) ++ (" " ++ (c ++ ("\n" ++ Y))) : String}
  %Equal.sym(Maybe<&2, String>, Rev.value_of(hs, name_at(r)), Some{c}, e) : {Rev.each(name_at(r), opt_list(_)) ++ Y == name_at(r) ++ (" " ++ (c ++ ("\n" ++ Y))) : String}
  one_line(name_at(r), c, Y)

# A key that may not repeat, present or not, is what `optional` writes.
def opt_piece(+hs: List<&2, Rev.Header>, +lr: Nat, +fresh: Bool, +s: {sorted(hs, lr, fresh) == True{} : Bool}, +r: Nat, nr: {Rev.repeatable(Rev.classify(name_at(r))) == False{} : Bool}, lt: {Nat.is_lt(r, 7n) == True{} : Bool}, -Y: String) -> {Rev.each(name_at(r), Rev.values_of(hs, name_at(r))) ++ Y == Rev.optional(name_at(r), Rev.value_of(hs, name_at(r))) ++ Y : String}:
  %Equal.sym(List<&2, String>, Rev.values_of(hs, name_at(r)), opt_list(Rev.value_of(hs, name_at(r))), single(hs, lr, fresh, r, s, nr, lt)) : {Rev.each(name_at(r), _) ++ Y == Rev.optional(name_at(r), Rev.value_of(hs, name_at(r))) ++ Y : String}
  Equal.cong(String, String, y => y ++ Y, Rev.each(name_at(r), opt_list(Rev.value_of(hs, name_at(r)))), Rev.optional(name_at(r), Rev.value_of(hs, name_at(r))), each_opt(name_at(r), Rev.value_of(hs, name_at(r))))

# Sorted headers with the three required keys present are what `write`
# spells from them.
def canon(+hs: List<&2, Rev.Header>, +lr: Nat, +fresh: Bool, +s: {sorted(hs, lr, fresh) == True{} : Bool}, +c: String, +a: String, +w: String, ec: {Rev.value_of(hs, "change") == Some{c} : Maybe<&2, String>}, ea: {Rev.value_of(hs, "author") == Some{a} : Maybe<&2, String>}, ew: {Rev.value_of(hs, "when") == Some{w} : Maybe<&2, String>}, +X: String) -> {Rev.write_facts(hs) ++ X == name_at(0n) ++ (" " ++ (c ++ ("\n" ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (name_at(3n) ++ (" " ++ (a ++ ("\n" ++ (name_at(4n) ++ (" " ++ (w ++ ("\n" ++ (Rev.optional(name_at(5n), Rev.value_of(hs, name_at(5n))) ++ (Rev.optional(name_at(6n), Rev.value_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X)))))))))))))))) : String}:
  Equal.trans(String, Rev.write_facts(hs) ++ X, Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X))))))), name_at(0n) ++ (" " ++ (c ++ ("\n" ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (name_at(3n) ++ (" " ++ (a ++ ("\n" ++ (name_at(4n) ++ (" " ++ (w ++ ("\n" ++ (Rev.optional(name_at(5n), Rev.value_of(hs, name_at(5n))) ++ (Rev.optional(name_at(6n), Rev.value_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X)))))))))))))))), layout(hs, lr, fresh, s, X),
    Equal.trans(String, Rev.each(name_at(0n), Rev.values_of(hs, name_at(0n))) ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X))))))), name_at(0n) ++ (" " ++ (c ++ ("\n" ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X)))))))))), name_at(0n) ++ (" " ++ (c ++ ("\n" ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (name_at(3n) ++ (" " ++ (a ++ ("\n" ++ (name_at(4n) ++ (" " ++ (w ++ ("\n" ++ (Rev.optional(name_at(5n), Rev.value_of(hs, name_at(5n))) ++ (Rev.optional(name_at(6n), Rev.value_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X)))))))))))))))), single_piece(hs, lr, fresh, s, 0n, {==}, {==}, c, ec, Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X))))))), Equal.cong(String, String, y => name_at(0n) ++ (" " ++ (c ++ ("\n" ++ y))), Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X)))))), Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (name_at(3n) ++ (" " ++ (a ++ ("\n" ++ (name_at(4n) ++ (" " ++ (w ++ ("\n" ++ (Rev.optional(name_at(5n), Rev.value_of(hs, name_at(5n))) ++ (Rev.optional(name_at(6n), Rev.value_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X)))))))))))), Equal.cong(String, String, y => Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ y, Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X))))), Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (name_at(3n) ++ (" " ++ (a ++ ("\n" ++ (name_at(4n) ++ (" " ++ (w ++ ("\n" ++ (Rev.optional(name_at(5n), Rev.value_of(hs, name_at(5n))) ++ (Rev.optional(name_at(6n), Rev.value_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X))))))))))), Equal.cong(String, String, y => Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ y, Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X)))), name_at(3n) ++ (" " ++ (a ++ ("\n" ++ (name_at(4n) ++ (" " ++ (w ++ ("\n" ++ (Rev.optional(name_at(5n), Rev.value_of(hs, name_at(5n))) ++ (Rev.optional(name_at(6n), Rev.value_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X)))))))))), Equal.trans(String, Rev.each(name_at(3n), Rev.values_of(hs, name_at(3n))) ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X)))), name_at(3n) ++ (" " ++ (a ++ ("\n" ++ (Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X))))))), name_at(3n) ++ (" " ++ (a ++ ("\n" ++ (name_at(4n) ++ (" " ++ (w ++ ("\n" ++ (Rev.optional(name_at(5n), Rev.value_of(hs, name_at(5n))) ++ (Rev.optional(name_at(6n), Rev.value_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X)))))))))), single_piece(hs, lr, fresh, s, 3n, {==}, {==}, a, ea, Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X)))), Equal.cong(String, String, y => name_at(3n) ++ (" " ++ (a ++ ("\n" ++ y))), Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X))), name_at(4n) ++ (" " ++ (w ++ ("\n" ++ (Rev.optional(name_at(5n), Rev.value_of(hs, name_at(5n))) ++ (Rev.optional(name_at(6n), Rev.value_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X)))))), Equal.trans(String, Rev.each(name_at(4n), Rev.values_of(hs, name_at(4n))) ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X))), name_at(4n) ++ (" " ++ (w ++ ("\n" ++ (Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X)))))), name_at(4n) ++ (" " ++ (w ++ ("\n" ++ (Rev.optional(name_at(5n), Rev.value_of(hs, name_at(5n))) ++ (Rev.optional(name_at(6n), Rev.value_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X)))))), single_piece(hs, lr, fresh, s, 4n, {==}, {==}, w, ew, Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X))), Equal.cong(String, String, y => name_at(4n) ++ (" " ++ (w ++ ("\n" ++ y))), Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X)), Rev.optional(name_at(5n), Rev.value_of(hs, name_at(5n))) ++ (Rev.optional(name_at(6n), Rev.value_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X)), Equal.trans(String, Rev.each(name_at(5n), Rev.values_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X)), Rev.optional(name_at(5n), Rev.value_of(hs, name_at(5n))) ++ (Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X)), Rev.optional(name_at(5n), Rev.value_of(hs, name_at(5n))) ++ (Rev.optional(name_at(6n), Rev.value_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X)), opt_piece(hs, lr, fresh, s, 5n, {==}, {==}, Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X)), Equal.cong(String, String, y => Rev.optional(name_at(5n), Rev.value_of(hs, name_at(5n))) ++ y, Rev.each(name_at(6n), Rev.values_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X), Rev.optional(name_at(6n), Rev.value_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ X), opt_piece(hs, lr, fresh, s, 6n, {==}, {==}, Rev.write_facts(Rev.facts_of(hs)) ++ X))))))))))))

# Assembly
# --------

def tail(+m: String) -> String:
  Bool.pick(String, String.is_empty(m), SNil{}, "\n" ++ m)

def rdisc(r: Result<&2, &2, String, Rev.Rev>) -> Type:
  match r:
    case Fail{msg}:
      Unit
    case Done{d}:
      Empty

def fail_done(-msg: String, -x: Rev.Rev, e: {Fail{msg} == Done{x} : Result<&2, &2, String, Rev.Rev>}) -> Empty:
  %e : {rdisc(_) : Type}
  Unit{}

def done_or(r: Result<&2, &2, String, Rev.Rev>, d: Rev.Rev) -> Rev.Rev:
  match r:
    case Fail{msg}:
      d
    case Done{y}:
      y

def checked_done(ok: Result<&2, &2, String, Unit>, +r: Rev.Rev, +x: Rev.Rev, e: {Rev.assemble.checked(ok, r) == Done{x} : Result<&2, &2, String, Rev.Rev>}) -> {r == x : Rev.Rev}:
  match ok:
    case Fail{msg}:
      Empty.absurd({r == x : Rev.Rev}, fail_done(msg, x, e))
    case Done{u}:
      Equal.cong(Result<&2, &2, String, Rev.Rev>, Rev.Rev, y => done_or(y, r), Done{r}, Done{x}, e)

def written(+hs: List<&2, Rev.Header>, +m: String, +s: {sorted(hs, 0n, True{}) == True{} : Bool}, +c: String, +a: String, +w: String, ec: {Rev.value_of(hs, "change") == Some{c} : Maybe<&2, String>}, ea: {Rev.value_of(hs, "author") == Some{a} : Maybe<&2, String>}, ew: {Rev.value_of(hs, "when") == Some{w} : Maybe<&2, String>}) -> {Rev.write(Rev.Rev{c, Rev.values_of(hs, "parent"), Rev.values_of(hs, "supersedes"), a, w, Rev.value_of(hs, "revised-by"), Rev.value_of(hs, "revised"), Rev.facts_of(hs), m}) == "historica" ++ ("\n" ++ (Rev.write_facts(hs) ++ tail(m))) : String}:
  Equal.sym(String, "historica" ++ ("\n" ++ (Rev.write_facts(hs) ++ tail(m))), Rev.write(Rev.Rev{c, Rev.values_of(hs, "parent"), Rev.values_of(hs, "supersedes"), a, w, Rev.value_of(hs, "revised-by"), Rev.value_of(hs, "revised"), Rev.facts_of(hs), m}),
    Equal.cong(String, String, y => "historica" ++ ("\n" ++ y), Rev.write_facts(hs) ++ tail(m), name_at(0n) ++ (" " ++ (c ++ ("\n" ++ (Rev.each(name_at(1n), Rev.values_of(hs, name_at(1n))) ++ (Rev.each(name_at(2n), Rev.values_of(hs, name_at(2n))) ++ (name_at(3n) ++ (" " ++ (a ++ ("\n" ++ (name_at(4n) ++ (" " ++ (w ++ ("\n" ++ (Rev.optional(name_at(5n), Rev.value_of(hs, name_at(5n))) ++ (Rev.optional(name_at(6n), Rev.value_of(hs, name_at(6n))) ++ (Rev.write_facts(Rev.facts_of(hs)) ++ tail(m))))))))))))))))), canon(hs, 0n, True{}, s, c, a, w, ec, ea, ew, tail(m))))

def assembled.w(+hs: List<&2, Rev.Header>, +m: String, +s: {sorted(hs, 0n, True{}) == True{} : Bool}, +c: String, +a: String, ec: {Rev.value_of(hs, "change") == Some{c} : Maybe<&2, String>}, ea: {Rev.value_of(hs, "author") == Some{a} : Maybe<&2, String>}, mw: Maybe<&2, String>, ew: {Rev.value_of(hs, "when") == mw : Maybe<&2, String>}, +x: Rev.Rev, e: {Rev.assemble.when(hs, m, c, a, Rev.required(mw, "when")) == Done{x} : Result<&2, &2, String, Rev.Rev>}) -> {Rev.write(x) == "historica" ++ ("\n" ++ (Rev.write_facts(hs) ++ tail(m))) : String}:
  match mw:
    case None{}:
      Empty.absurd({Rev.write(x) == "historica" ++ ("\n" ++ (Rev.write_facts(hs) ++ tail(m))) : String}, fail_done("the header `when` is missing", x, e))
    case Some{+w}:
      %checked_done(Rev.assemble.checks(hs, a), Rev.Rev{c, Rev.values_of(hs, "parent"), Rev.values_of(hs, "supersedes"), a, w, Rev.value_of(hs, "revised-by"), Rev.value_of(hs, "revised"), Rev.facts_of(hs), m}, x, e) : {Rev.write(_) == "historica" ++ ("\n" ++ (Rev.write_facts(hs) ++ tail(m))) : String}
      written(hs, m, s, c, a, w, ec, ea, ew)

def assembled.a(+hs: List<&2, Rev.Header>, +m: String, +s: {sorted(hs, 0n, True{}) == True{} : Bool}, +c: String, ec: {Rev.value_of(hs, "change") == Some{c} : Maybe<&2, String>}, ma: Maybe<&2, String>, ea: {Rev.value_of(hs, "author") == ma : Maybe<&2, String>}, +x: Rev.Rev, e: {Rev.assemble.author(hs, m, c, Rev.required(ma, "author")) == Done{x} : Result<&2, &2, String, Rev.Rev>}) -> {Rev.write(x) == "historica" ++ ("\n" ++ (Rev.write_facts(hs) ++ tail(m))) : String}:
  match ma:
    case None{}:
      Empty.absurd({Rev.write(x) == "historica" ++ ("\n" ++ (Rev.write_facts(hs) ++ tail(m))) : String}, fail_done("the header `author` is missing", x, e))
    case Some{+a}:
      assembled.w(hs, m, s, c, a, ec, ea, Rev.value_of(hs, "when"), {==}, x, e)

def assembled.c(+hs: List<&2, Rev.Header>, +m: String, +s: {sorted(hs, 0n, True{}) == True{} : Bool}, mc: Maybe<&2, String>, ec: {Rev.value_of(hs, "change") == mc : Maybe<&2, String>}, +x: Rev.Rev, e: {Rev.assemble.change(hs, m, Rev.required(mc, "change")) == Done{x} : Result<&2, &2, String, Rev.Rev>}) -> {Rev.write(x) == "historica" ++ ("\n" ++ (Rev.write_facts(hs) ++ tail(m))) : String}:
  match mc:
    case None{}:
      Empty.absurd({Rev.write(x) == "historica" ++ ("\n" ++ (Rev.write_facts(hs) ++ tail(m))) : String}, fail_done("the header `change` is missing", x, e))
    case Some{+c}:
      assembled.a(hs, m, s, c, ec, Rev.value_of(hs, "author"), {==}, x, e)

# What `assemble` builds from sorted headers, `write` spells as them.
def assembled(+hs: List<&2, Rev.Header>, +m: String, +s: {sorted(hs, 0n, True{}) == True{} : Bool}, +x: Rev.Rev, e: {Rev.assemble(hs, m) == Done{x} : Result<&2, &2, String, Rev.Rev>}) -> {Rev.write(x) == "historica" ++ ("\n" ++ (Rev.write_facts(hs) ++ tail(m))) : String}:
  assembled.c(hs, m, s, Rev.value_of(hs, "change"), {==}, x, e)

# One header line
# ---------------

def hdisc(r: Result<&2, &2, String, Rev.Header>) -> Type:
  match r:
    case Fail{msg}:
      Unit
    case Done{d}:
      Empty

def hfail(-msg: String, -x: Rev.Header, e: {Fail{msg} == Done{x} : Result<&2, &2, String, Rev.Header>}) -> Empty:
  %e : {hdisc(_) : Type}
  Unit{}

def hdone(r: Result<&2, &2, String, Rev.Header>, d: Rev.Header) -> Rev.Header:
  match r:
    case Fail{msg}:
      d
    case Done{y}:
      y

# A passed `ensure` leaves the rest of the block.
def ens(ok: Bool, -msg: String, -rest: Result<&2, &2, String, Rev.Header>, -hd: Rev.Header, e: {Result.bind(&2, &2, String, Unit, Rev.Header, Rev.ensure(ok, msg), u => rest) == Done{hd} : Result<&2, &2, String, Rev.Header>}) -> {rest == Done{hd} : Result<&2, &2, String, Rev.Header>}:
  match ok:
    case True{}:
      e
    case False{}:
      Empty.absurd({rest == Done{hd} : Result<&2, &2, String, Rev.Header>}, hfail(msg, hd, e))

def scanned(+k: String, +v: String, sc: Rev.Scan, +hd: Rev.Header, e: {Rev.header_of.scanned(k, v, sc) == Done{hd} : Result<&2, &2, String, Rev.Header>}) -> {Rev.Header{k, v} == hd : Rev.Header}:
  match sc:
    case Rev.Scan{padded, control}:
      +e1 = ens(Bool.not(padded), "the header `" ++ k ++ "` has a padded value", Result.bind(&2, &2, String, Unit, Rev.Header, Rev.ensure(Bool.not(control), "the header `" ++ k ++ "` holds a control character"), u => Done{Rev.Header{k, v}}), hd, e)
      +e2 = ens(Bool.not(control), "the header `" ++ k ++ "` holds a control character", Done{Rev.Header{k, v}}, hd, e1)
      Equal.cong(Result<&2, &2, String, Rev.Header>, Rev.Header, y => hdone(y, Rev.Header{k, v}), Done{Rev.Header{k, v}}, Done{hd}, e2)

def header_cut(+t: String, cut: Maybe<&2, T.Split>, ecut: {T.split_once(t) == cut : Maybe<&2, T.Split>}, +hd: Rev.Header, e: {Rev.header_of(t, cut) == Done{hd} : Result<&2, &2, String, Rev.Header>}, -U: String) -> {t ++ ("\n" ++ U) == Rev.write_facts([hd]) ++ U : String}:
  match cut:
    case None{}:
      Empty.absurd({t ++ ("\n" ++ U) == Rev.write_facts([hd]) ++ U : String}, hfail("the header `" ++ t ++ "` has no value", hd, e))
    case Some{T.Split{+k, +v}}:
      +e1 = ens(Rev.shaped_key(k), "a malformed key `" ++ k ++ "`", Result.bind(&2, &2, String, Unit, Rev.Header, Rev.ensure(Bool.not(String.is_empty(v)), "the header `" ++ k ++ "` has no value"), u => Rev.header_of.scanned(k, v, Rev.scan(v))), hd, e)
      +e2 = ens(Bool.not(String.is_empty(v)), "the header `" ++ k ++ "` has no value", Rev.header_of.scanned(k, v, Rev.scan(v)), hd, e1)
      %scanned(k, v, Rev.scan(v), hd, e2) : {t ++ ("\n" ++ U) == Rev.write_facts([_]) ++ U : String}
      %Equal.sym(String, String.reverse.go(SNil{}, t), k ++ (" " ++ v), Spell.split_top(t, k, v, ecut)) : {_ ++ ("\n" ++ U) == Rev.write_facts([Rev.Header{k, v}]) ++ U : String}
      %Equal.sym(String, (k ++ (" " ++ v)) ++ ("\n" ++ U), k ++ ((" " ++ v) ++ ("\n" ++ U)), Spell.app_assoc(k, " " ++ v, "\n" ++ U)) : {_ == Rev.write_facts([Rev.Header{k, v}]) ++ U : String}
      %Equal.sym(String, v ++ ("\n" ++ U), (v ++ "\n") ++ U, Equal.sym(String, (v ++ "\n") ++ U, v ++ ("\n" ++ U), Spell.app_assoc(v, "\n", U))) : {k ++ (" " ++ (v ++ ("\n" ++ U))) == Rev.write_facts([Rev.Header{k, v}]) ++ U : String}
      Equal.sym(String, Rev.write_facts([Rev.Header{k, v}]) ++ U, k ++ (" " ++ (v ++ ("\n" ++ U))), cons_app(k, v, Nil{}, U))

# A header line the loop accepted is that header, written.
def header_line(+t: String, +hd: Rev.Header, e: {Rev.header_of(t, T.split_once(t)) == Done{hd} : Result<&2, &2, String, Rev.Header>}, -U: String) -> {t ++ ("\n" ++ U) == Rev.write_facts([hd]) ++ U : String}:
  header_cut(t, T.split_once(t), {==}, hd, e, U)

# Lines
# -----

# What `T.lines` makes: every line but the last ends in a newline, and a
# last line without one is not empty.
def wf(ls: List<&2, T.Line>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case T.Line{t, True{}} <> rest:
      wf(rest)
    case T.Line{t, False{}} <> Nil{}:
      Bool.not(String.is_empty(t))
    case T.Line{t, False{}} <> more:
      False{}

def wf_last(+last: String, b: Bool, eb: {String.is_empty(last) == b : Bool}) -> {wf(Bool.pick(List<&2, T.Line>, b, Nil{}, [T.Line{last, False{}}])) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, String.is_empty(last), False{}, eb) : {Bool.not(_) == True{} : Bool}
      {==}

def lines_wf.go(parts: List<&2, String>) -> {wf(T.lines.go(parts)) == True{} : Bool}:
  match parts:
    case Nil{}:
      {==}
    case +last <> Nil{}:
      wf_last(last, String.is_empty(last), {==})
    case h <> t <> more:
      lines_wf.go(t <> more)

def lines_wf(s: String) -> {wf(T.lines(s)) == True{} : Bool}:
  lines_wf.go(String.split(s, '\n'))

def unlines_same(ls: List<&2, T.Line>) -> {Rev.unlines(ls) == Spell.unlines(ls) : String}:
  match ls:
    case Nil{}:
      {==}
    case T.Line{+t, +n} <> rest:
      Equal.cong(String, String, y => t ++ (Bool.pick(String, n, "\n", SNil{}) ++ y), Rev.unlines(rest), Spell.unlines(rest), unlines_same(rest))

def app_nonempty(t: String, -u: String, e: {String.is_empty(u) == False{} : Bool}) -> {String.is_empty(t ++ u) == False{} : Bool}:
  match t:
    case SNil{}:
      e
    case SCon{h, r}:
      {==}

def nonempty_first(t: String, e: {Bool.not(String.is_empty(t)) == True{} : Bool}, -u: String) -> {String.is_empty(t ++ u) == False{} : Bool}:
  match t:
    case SNil{}:
      Empty.absurd({String.is_empty(u) == False{} : Bool}, Comp.false_true(e))
    case SCon{h, r}:
      {==}

# Lines of a file, one or more, are not the empty string.
def unlines_nonempty.of(+t: String, term: Bool, rest: List<&2, T.Line>, w: {wf(T.Line{t, term} <> rest) == True{} : Bool}) -> {String.is_empty(Rev.unlines(T.Line{t, term} <> rest)) == False{} : Bool}:
  match term rest:
    case True{} _:
      app_nonempty(t, "\n" ++ Rev.unlines(rest), {==})
    case False{} Nil{}:
      nonempty_first(t, w, SNil{} ++ SNil{})
    case False{} r <> more:
      Empty.absurd({String.is_empty(Rev.unlines(T.Line{t, False{}} <> r <> more)) == False{} : Bool}, Comp.false_true(w))

def unlines_nonempty(l: T.Line, rest: List<&2, T.Line>, w: {wf(l <> rest) == True{} : Bool}) -> {String.is_empty(Rev.unlines(l <> rest)) == False{} : Bool}:
  match l:
    case T.Line{+t, term}:
      unlines_nonempty.of(t, term, rest, w)

# The header loop
# ---------------

def rev_extend(xs: List<&2, Rev.Header>, acc: List<&2, Rev.Header>, -tl: List<&2, Rev.Header>) -> {List.reverse.go(&2, Rev.Header, xs, List.append(&2, Rev.Header, acc, tl)) == List.append(&2, Rev.Header, List.reverse.go(&2, Rev.Header, xs, acc), tl) : List<&2, Rev.Header>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      rev_extend(t, h <> acc, tl)

def rev_cons(-hd: Rev.Header, acc: List<&2, Rev.Header>) -> {List.reverse(&2, Rev.Header, hd <> acc) == List.append(&2, Rev.Header, List.reverse(&2, Rev.Header, acc), [hd]) : List<&2, Rev.Header>}:
  rev_extend(acc, Nil{}, [hd])

def facts_append(a: List<&2, Rev.Header>, +b: List<&2, Rev.Header>) -> {Rev.write_facts(List.append(&2, Rev.Header, a, b)) == Rev.write_facts(a) ++ Rev.write_facts(b) : String}:
  match a:
    case Nil{}:
      {==}
    case Rev.Header{+k, +v} <> +t:
      Equal.trans(String, Rev.write_facts(Rev.Header{k, v} <> List.append(&2, Rev.Header, t, b)), k ++ (" " ++ (v ++ ("\n" ++ (Rev.write_facts(t) ++ Rev.write_facts(b))))), Rev.write_facts(Rev.Header{k, v} <> t) ++ Rev.write_facts(b),
        Equal.cong(String, String, y => k ++ (" " ++ (v ++ ("\n" ++ y))), Rev.write_facts(List.append(&2, Rev.Header, t, b)), Rev.write_facts(t) ++ Rev.write_facts(b), facts_append(t, b)),
        Equal.sym(String, Rev.write_facts(Rev.Header{k, v} <> t) ++ Rev.write_facts(b), k ++ (" " ++ (v ++ ("\n" ++ (Rev.write_facts(t) ++ Rev.write_facts(b))))), cons_app(k, v, t, Rev.write_facts(b))))

def sdisc(r: Result<&2, &2, String, Rev.Split>) -> Type:
  match r:
    case Fail{msg}:
      Unit
    case Done{d}:
      Empty

def sfail(-msg: String, -x: Rev.Split, e: {Fail{msg} == Done{x} : Result<&2, &2, String, Rev.Split>}) -> Empty:
  %e : {sdisc(_) : Type}
  Unit{}

def sdone(r: Result<&2, &2, String, Rev.Split>, d: Rev.Split) -> Rev.Split:
  match r:
    case Fail{msg}:
      d
    case Done{y}:
      y

def split_text(x: Rev.Split) -> String:
  match x:
    case Rev.Headers{hs, m}:
      Rev.write_facts(hs) ++ tail(m)

# One header further along: the line read is the header it was read as.
def headers_step(+acc: List<&2, Rev.Header>, +hd: Rev.Header, +t: String, +U: String, -x: Rev.Split, eh: {Rev.header_of(t, T.split_once(t)) == Done{hd} : Result<&2, &2, String, Rev.Header>}, ih: {Rev.write_facts(List.reverse(&2, Rev.Header, hd <> acc)) ++ U == split_text(x) : String}) -> {Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ (t ++ ("\n" ++ U)) == split_text(x) : String}:
  %Equal.sym(String, t ++ ("\n" ++ U), Rev.write_facts([hd]) ++ U, header_line(t, hd, eh, U)) : {Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ _ == split_text(x) : String}
  Equal.trans(String, Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ (Rev.write_facts([hd]) ++ U), Rev.write_facts(List.reverse(&2, Rev.Header, hd <> acc)) ++ U, split_text(x),
    Equal.sym(String, Rev.write_facts(List.reverse(&2, Rev.Header, hd <> acc)) ++ U, Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ (Rev.write_facts([hd]) ++ U),
      Equal.trans(String, Rev.write_facts(List.reverse(&2, Rev.Header, hd <> acc)) ++ U, Rev.write_facts(List.append(&2, Rev.Header, List.reverse(&2, Rev.Header, acc), [hd])) ++ U, Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ (Rev.write_facts([hd]) ++ U),
        Equal.cong(List<&2, Rev.Header>, String, l => Rev.write_facts(l) ++ U, List.reverse(&2, Rev.Header, hd <> acc), List.append(&2, Rev.Header, List.reverse(&2, Rev.Header, acc), [hd]), rev_cons(hd, acc)),
        Equal.trans(String, Rev.write_facts(List.append(&2, Rev.Header, List.reverse(&2, Rev.Header, acc), [hd])) ++ U, (Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ Rev.write_facts([hd])) ++ U, Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ (Rev.write_facts([hd]) ++ U),
          Equal.cong(String, String, y => y ++ U, Rev.write_facts(List.append(&2, Rev.Header, List.reverse(&2, Rev.Header, acc), [hd])), Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ Rev.write_facts([hd]), facts_append(List.reverse(&2, Rev.Header, acc), [hd])),
          Spell.app_assoc(Rev.write_facts(List.reverse(&2, Rev.Header, acc)), Rev.write_facts([hd]), U)))),
    ih)

def blank_line(term: Bool, rest: List<&2, T.Line>, h: Result<&2, &2, String, Rev.Header>, +acc: List<&2, Rev.Header>, +at: Nat, +x: Rev.Split, w: {wf(T.Line{SNil{}, term} <> rest) == True{} : Bool}, e: {Rev.headers.go(T.Line{SNil{}, term} <> rest, h, at, acc) == Done{x} : Result<&2, &2, String, Rev.Split>}) -> {Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ Rev.unlines(T.Line{SNil{}, term} <> rest) == split_text(x) : String}:
  match term rest h:
    case False{} Nil{} _:
      Empty.absurd({Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ Rev.unlines([T.Line{SNil{}, False{}}]) == split_text(x) : String}, sfail("line " ++ Nat.show(at) ++ ": a blank line with no message after it", x, e))
    case True{} Nil{} Fail{m}:
      Empty.absurd({Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ Rev.unlines([T.Line{SNil{}, True{}}]) == split_text(x) : String}, sfail("line " ++ Nat.show(at) ++ ": a blank line with no message after it", x, e))
    case True{} Nil{} Done{d}:
      Empty.absurd({Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ Rev.unlines([T.Line{SNil{}, True{}}]) == split_text(x) : String}, sfail("line " ++ Nat.show(at) ++ ": a blank line with no message after it", x, e))
    case False{} l <> more _:
      Empty.absurd({Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ Rev.unlines(T.Line{SNil{}, False{}} <> l <> more) == split_text(x) : String}, Comp.false_true(w))
    case True{} +l <> +more Fail{m}:
      %Equal.cong(Result<&2, &2, String, Rev.Split>, Rev.Split, y => sdone(y, x), Done{Rev.Headers{List.reverse(&2, Rev.Header, acc), Rev.unlines(l <> more)}}, Done{x}, e) : {Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ Rev.unlines(T.Line{SNil{}, True{}} <> l <> more) == split_text(_) : String}
      %Equal.sym(Bool, String.is_empty(Rev.unlines(l <> more)), False{}, unlines_nonempty(l, more, w)) : {Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ ("\n" ++ Rev.unlines(l <> more)) == Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ Bool.pick(String, _, SNil{}, "\n" ++ Rev.unlines(l <> more)) : String}
      {==}
    case True{} +l <> +more Done{d}:
      %Equal.cong(Result<&2, &2, String, Rev.Split>, Rev.Split, y => sdone(y, x), Done{Rev.Headers{List.reverse(&2, Rev.Header, acc), Rev.unlines(l <> more)}}, Done{x}, e) : {Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ Rev.unlines(T.Line{SNil{}, True{}} <> l <> more) == split_text(_) : String}
      %Equal.sym(Bool, String.is_empty(Rev.unlines(l <> more)), False{}, unlines_nonempty(l, more, w)) : {Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ ("\n" ++ Rev.unlines(l <> more)) == Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ Bool.pick(String, _, SNil{}, "\n" ++ Rev.unlines(l <> more)) : String}
      {==}

def header_sp(+c: Char, +tt: String, term: Bool, h: Result<&2, &2, String, Rev.Header>, +rest: List<&2, T.Line>, +acc: List<&2, Rev.Header>, +at: Nat, +x: Rev.Split, eh: {Rev.head_header(T.Line{SCon{c, tt}, term} <> rest) == h : Result<&2, &2, String, Rev.Header>}, w: {wf(T.Line{SCon{c, tt}, term} <> rest) == True{} : Bool}, e: {Rev.headers.go(T.Line{SCon{c, tt}, term} <> rest, h, at, acc) == Done{x} : Result<&2, &2, String, Rev.Split>}, ih: @hd: Rev.Header -> {wf(rest) == True{} : Bool} -> {Rev.headers.go(rest, Rev.head_header(rest), 1n+at, hd <> acc) == Done{x} : Result<&2, &2, String, Rev.Split>} -> {Rev.write_facts(List.reverse(&2, Rev.Header, hd <> acc)) ++ Rev.unlines(rest) == split_text(x) : String}) -> {Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ Rev.unlines(T.Line{SCon{c, tt}, term} <> rest) == split_text(x) : String}:
  match term h:
    case False{} _:
      Empty.absurd({Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ Rev.unlines(T.Line{SCon{c, tt}, False{}} <> rest) == split_text(x) : String}, sfail("line " ++ Nat.show(at) ++ ": unterminated line", x, e))
    case True{} Fail{msg}:
      Empty.absurd({Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ Rev.unlines(T.Line{SCon{c, tt}, True{}} <> rest) == split_text(x) : String}, sfail("line " ++ Nat.show(at) ++ ": " ++ msg, x, e))
    case True{} Done{+hd}:
      headers_step(acc, hd, SCon{c, tt}, Rev.unlines(rest), x, eh, ih(hd, w, e))

def line_sp(t: String, term: Bool, h: Result<&2, &2, String, Rev.Header>, +rest: List<&2, T.Line>, +acc: List<&2, Rev.Header>, +at: Nat, +x: Rev.Split, eh: {Rev.head_header(T.Line{t, term} <> rest) == h : Result<&2, &2, String, Rev.Header>}, w: {wf(T.Line{t, term} <> rest) == True{} : Bool}, e: {Rev.headers.go(T.Line{t, term} <> rest, h, at, acc) == Done{x} : Result<&2, &2, String, Rev.Split>}, ih: @hd: Rev.Header -> {wf(rest) == True{} : Bool} -> {Rev.headers.go(rest, Rev.head_header(rest), 1n+at, hd <> acc) == Done{x} : Result<&2, &2, String, Rev.Split>} -> {Rev.write_facts(List.reverse(&2, Rev.Header, hd <> acc)) ++ Rev.unlines(rest) == split_text(x) : String}) -> {Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ Rev.unlines(T.Line{t, term} <> rest) == split_text(x) : String}:
  match t:
    case SNil{}:
      blank_line(term, rest, h, acc, at, x, w, e)
    case SCon{+c, +tt}:
      header_sp(c, tt, term, h, rest, acc, at, x, eh, w, e, ih)

# The headers the loop read, and the message after them, are the lines.
def headers_sp(ls: List<&2, T.Line>, h: Result<&2, &2, String, Rev.Header>, eh: {Rev.head_header(ls) == h : Result<&2, &2, String, Rev.Header>}, +at: Nat, +acc: List<&2, Rev.Header>, w: {wf(ls) == True{} : Bool}, +x: Rev.Split, e: {Rev.headers.go(ls, h, at, acc) == Done{x} : Result<&2, &2, String, Rev.Split>}) -> {Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ Rev.unlines(ls) == split_text(x) : String}:
  match ls:
    case Nil{}:
      %Equal.cong(Result<&2, &2, String, Rev.Split>, Rev.Split, y => sdone(y, x), Done{Rev.Headers{List.reverse(&2, Rev.Header, acc), SNil{}}}, Done{x}, e) : {Rev.write_facts(List.reverse(&2, Rev.Header, acc)) ++ Rev.unlines(Nil{}) == split_text(_) : String}
      {==}
    case T.Line{t, term} <> +rest:
      line_sp(t, term, h, rest, acc, at, x, eh, w, e, hd => w2 => e2 => headers_sp(rest, Rev.head_header(rest), {==}, 1n+at, hd <> acc, w2, x, e2))

# The document
# ------------

def pick_fail(c: Bool, -a: String, -b: String, -x: Rev.Rev, e: {Bool.pick(Result<&2, &2, String, Rev.Rev>, c, Fail{a}, Fail{b}) == Done{x} : Result<&2, &2, String, Rev.Rev>}) -> Empty:
  match c:
    case True{}:
      fail_done(a, x, e)
    case False{}:
      fail_done(b, x, e)

def validated_sp(+hs: List<&2, Rev.Header>, +m: String, -rest: List<&2, T.Line>, comp: Maybe<&2, String>, ec: {Rev.validate(hs, Rev.classify_head(hs), None{}, 0n, 2n) == comp : Maybe<&2, String>}, hs_eq: {Rev.unlines(rest) == Rev.write_facts(hs) ++ tail(m) : String}, +x: Rev.Rev, e: {Rev.parse.validated(hs, m, comp) == Done{x} : Result<&2, &2, String, Rev.Rev>}) -> {Rev.write(x) == "historica" ++ ("\n" ++ Rev.unlines(rest)) : String}:
  match comp:
    case Some{msg}:
      Empty.absurd({Rev.write(x) == "historica" ++ ("\n" ++ Rev.unlines(rest)) : String}, fail_done(msg, x, e))
    case None{}:
      Equal.trans(String, Rev.write(x), "historica" ++ ("\n" ++ (Rev.write_facts(hs) ++ tail(m))), "historica" ++ ("\n" ++ Rev.unlines(rest)),
        assembled(hs, m, validate_sorted(hs, None{}, 0n, 2n, ec), x, e),
        Equal.cong(String, String, y => "historica" ++ ("\n" ++ y), Rev.write_facts(hs) ++ tail(m), Rev.unlines(rest), Equal.sym(String, Rev.unlines(rest), Rev.write_facts(hs) ++ tail(m), hs_eq)))

def body_sp(+rest: List<&2, T.Line>, w: {wf(rest) == True{} : Bool}, +x: Rev.Rev, sr: Result<&2, &2, String, Rev.Split>, esr: {Rev.headers.go(rest, Rev.head_header(rest), 2n, Nil{}) == sr : Result<&2, &2, String, Rev.Split>}, e: {Rev.parse.split(sr) == Done{x} : Result<&2, &2, String, Rev.Rev>}) -> {Rev.write(x) == "historica" ++ ("\n" ++ Rev.unlines(rest)) : String}:
  match sr:
    case Fail{msg}:
      Empty.absurd({Rev.write(x) == "historica" ++ ("\n" ++ Rev.unlines(rest)) : String}, fail_done(msg, x, e))
    case Done{Rev.Headers{+hs, +m}}:
      validated_sp(hs, m, rest, Rev.validate(hs, Rev.classify_head(hs), None{}, 0n, 2n), {==}, headers_sp(rest, Rev.head_header(rest), {==}, 2n, Nil{}, w, Rev.Headers{hs, m}, esr), x, e)

def head_sp(+t: String, term: Bool, b: Bool, +rest: List<&2, T.Line>, eb: {Bool.and(term, T.same(t, "historica")) == b : Bool}, w: {wf(T.Line{t, term} <> rest) == True{} : Bool}, +x: Rev.Rev, e: {Rev.parse.head(t, b, rest) == Done{x} : Result<&2, &2, String, Rev.Rev>}) -> {Rev.write(x) == Rev.unlines(T.Line{t, term} <> rest) : String}:
  match term b:
    case False{} False{}:
      Empty.absurd({Rev.write(x) == Rev.unlines(T.Line{t, False{}} <> rest) : String}, pick_fail(String.starts_with(t, "historica-"), "line 1: an unknown version `" ++ t ++ "`, likely a newer historica", "line 1: not a historica document", x, e))
    case True{} False{}:
      Empty.absurd({Rev.write(x) == Rev.unlines(T.Line{t, True{}} <> rest) : String}, pick_fail(String.starts_with(t, "historica-"), "line 1: an unknown version `" ++ t ++ "`, likely a newer historica", "line 1: not a historica document", x, e))
    case False{} True{}:
      Empty.absurd({Rev.write(x) == Rev.unlines(T.Line{t, False{}} <> rest) : String}, Comp.false_true(eb))
    case True{} True{}:
      %Equal.sym(String, t, "historica", Eq.same_eq(t, "historica", eb)) : {Rev.write(x) == Rev.unlines(T.Line{_, True{}} <> rest) : String}
      body_sp(rest, w, x, Rev.headers.go(rest, Rev.head_header(rest), 2n, Nil{}), {==}, e)

def preamble_sp(ls: List<&2, T.Line>, w: {wf(ls) == True{} : Bool}, +x: Rev.Rev, e: {Rev.parse.preamble(ls) == Done{x} : Result<&2, &2, String, Rev.Rev>}) -> {Rev.write(x) == Rev.unlines(ls) : String}:
  match ls:
    case Nil{}:
      Empty.absurd({Rev.write(x) == Rev.unlines(Nil{}) : String}, fail_done("an empty document", x, e))
    case T.Line{+t, +term} <> +rest:
      head_sp(t, term, Bool.and(term, T.same(t, "historica")), rest, {==}, w, x, e)

def no_cr(+s: String, c: Bool, +x: Rev.Rev, e: {Bool.pick(Result<&2, &2, String, Rev.Rev>, c, Fail{"a carriage return"}, Rev.parse.preamble(T.lines(s))) == Done{x} : Result<&2, &2, String, Rev.Rev>}) -> {Rev.parse.preamble(T.lines(s)) == Done{x} : Result<&2, &2, String, Rev.Rev>}:
  match c:
    case True{}:
      Empty.absurd({Rev.parse.preamble(T.lines(s)) == Done{x} : Result<&2, &2, String, Rev.Rev>}, fail_done("a carriage return", x, e))
    case False{}:
      e

# `Rev.parse` only rewords a refusal: what it accepts, the parser under it
# accepted.
def worded_done(+s: String, r: Result<&2, &2, String, Rev.Rev>, -x: Rev.Rev, e: {Rev.worded(s, r) == Done{x} : Result<&2, &2, String, Rev.Rev>}) -> {r == Done{x} : Result<&2, &2, String, Rev.Rev>}:
  match r:
    case Done{y}:
      e
    case Fail{m}:
      Empty.absurd({Fail{m} == Done{x} : Result<&2, &2, String, Rev.Rev>}, fail_done(Maybe.default(&2, String, Rev.refusal(s), m), x, e))

# The theorem: what the parser accepts, the writer spells back byte for byte.
def write_parse(+s: String, +x: Rev.Rev, e: {Rev.parse(s) == Done{x} : Result<&2, &2, String, Rev.Rev>}) -> {Rev.write(x) == s : String}:
  Equal.trans(String, Rev.write(x), Rev.unlines(T.lines(s)), s,
    preamble_sp(T.lines(s), lines_wf(s), x, no_cr(s, T.has_char(s, '\r'), x, worded_done(s, Bool.pick(Result<&2, &2, String, Rev.Rev>, T.has_char(s, '\r'), Fail{"a carriage return"}, Rev.parse.preamble(T.lines(s))), x, e))),
    Equal.trans(String, Rev.unlines(T.lines(s)), Spell.unlines(T.lines(s)), s, unlines_same(T.lines(s)), Spell.unlines_lines(s)))

def main() -> Unit:
  Unit{}
