# `skip`, held to what it says: the rule it writes for a path or a name is
# one the reader of `skipped/` reads back, private or not, and skips that
# path and nothing that does not start with it; what it writes is new to the
# store and named once, and nothing asked is lost; and its listing names
# every stated rule once. Rule equality is proved to be equality first, so
# `held` means membership.
import Base
import ./skip.bend as Skip
import ./composition_lemmas.bend as Comp
import ./anchor_lemmas.bend as AL
import ./folder.bend as Folder
import ./commands.bend as Main
import ./string_lemmas.bend as S
import ./equality_lemmas.bend as EqL

# Rule equality
# -------------

def scope_eq_sound(a: Folder.Scope, b: Folder.Scope, e: {Skip.scope.eq(a, b) == True{} : Bool}) -> {a == b : Folder.Scope}:
  match a b:
    case Folder.Scope.Path{+x} Folder.Scope.Path{+y}:
      Equal.cong(String, Folder.Scope, v => Folder.Scope.Path{v}, x, y, S.eq_true(x, y, e))
    case Folder.Scope.Path{x} Folder.Scope.Under{y}:
      Empty.absurd({Folder.Scope.Path{x} == Folder.Scope.Under{y} : Folder.Scope}, S.false_true(e))
    case Folder.Scope.Path{x} Folder.Scope.Name{y}:
      Empty.absurd({Folder.Scope.Path{x} == Folder.Scope.Name{y} : Folder.Scope}, S.false_true(e))
    case Folder.Scope.Path{x} Folder.Scope.NameUnder{y}:
      Empty.absurd({Folder.Scope.Path{x} == Folder.Scope.NameUnder{y} : Folder.Scope}, S.false_true(e))
    case Folder.Scope.Under{x} Folder.Scope.Path{y}:
      Empty.absurd({Folder.Scope.Under{x} == Folder.Scope.Path{y} : Folder.Scope}, S.false_true(e))
    case Folder.Scope.Under{+x} Folder.Scope.Under{+y}:
      Equal.cong(String, Folder.Scope, v => Folder.Scope.Under{v}, x, y, S.eq_true(x, y, e))
    case Folder.Scope.Under{x} Folder.Scope.Name{y}:
      Empty.absurd({Folder.Scope.Under{x} == Folder.Scope.Name{y} : Folder.Scope}, S.false_true(e))
    case Folder.Scope.Under{x} Folder.Scope.NameUnder{y}:
      Empty.absurd({Folder.Scope.Under{x} == Folder.Scope.NameUnder{y} : Folder.Scope}, S.false_true(e))
    case Folder.Scope.Name{x} Folder.Scope.Path{y}:
      Empty.absurd({Folder.Scope.Name{x} == Folder.Scope.Path{y} : Folder.Scope}, S.false_true(e))
    case Folder.Scope.Name{x} Folder.Scope.Under{y}:
      Empty.absurd({Folder.Scope.Name{x} == Folder.Scope.Under{y} : Folder.Scope}, S.false_true(e))
    case Folder.Scope.Name{+x} Folder.Scope.Name{+y}:
      Equal.cong(String, Folder.Scope, v => Folder.Scope.Name{v}, x, y, S.eq_true(x, y, e))
    case Folder.Scope.Name{x} Folder.Scope.NameUnder{y}:
      Empty.absurd({Folder.Scope.Name{x} == Folder.Scope.NameUnder{y} : Folder.Scope}, S.false_true(e))
    case Folder.Scope.NameUnder{x} Folder.Scope.Path{y}:
      Empty.absurd({Folder.Scope.NameUnder{x} == Folder.Scope.Path{y} : Folder.Scope}, S.false_true(e))
    case Folder.Scope.NameUnder{x} Folder.Scope.Under{y}:
      Empty.absurd({Folder.Scope.NameUnder{x} == Folder.Scope.Under{y} : Folder.Scope}, S.false_true(e))
    case Folder.Scope.NameUnder{x} Folder.Scope.Name{y}:
      Empty.absurd({Folder.Scope.NameUnder{x} == Folder.Scope.Name{y} : Folder.Scope}, S.false_true(e))
    case Folder.Scope.NameUnder{+x} Folder.Scope.NameUnder{+y}:
      Equal.cong(String, Folder.Scope, v => Folder.Scope.NameUnder{v}, x, y, S.eq_true(x, y, e))

def scope_eq_refl(a: Folder.Scope) -> {Skip.scope.eq(a, a) == True{} : Bool}:
  match a:
    case Folder.Scope.Path{+x}:
      S.eq_refl(x)
    case Folder.Scope.Under{+x}:
      S.eq_refl(x)
    case Folder.Scope.Name{+x}:
      S.eq_refl(x)
    case Folder.Scope.NameUnder{+x}:
      S.eq_refl(x)

def xor_not(p: Bool, q: Bool, h: {Bool.not(Bool.xor(p, q)) == True{} : Bool}) -> {p == q : Bool}:
  match p q:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, S.false_true(h))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(h))

def xor_refl(p: Bool) -> {Bool.not(Bool.xor(p, p)) == True{} : Bool}:
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

# Two rules `rule.eq` calls one are one rule, and every rule is one with
# itself.
def rule_eq_sound(a: Skip.Rule, b: Skip.Rule, +e: {Skip.rule.eq(a, b) == True{} : Bool}) -> {a == b : Skip.Rule}:
  match a b:
    case Skip.Rule{+x, +p} Skip.Rule{+y, +q}:
      +xe : {x == y : Folder.Scope} = scope_eq_sound(x, y, Comp.and_left(Skip.scope.eq(x, y), Bool.not(Bool.xor(p, q)), e))
      +pe : {p == q : Bool} = xor_not(p, q, Comp.and_right(Skip.scope.eq(x, y), Bool.not(Bool.xor(p, q)), e))
      %xe : {Skip.Rule{x, p} == Skip.Rule{_, q} : Skip.Rule}
      %pe : {Skip.Rule{x, p} == Skip.Rule{x, _} : Skip.Rule}
      {==}

def rule_eq_refl(a: Skip.Rule) -> {Skip.rule.eq(a, a) == True{} : Bool}:
  match a:
    case Skip.Rule{+x, +p}:
      %Equal.sym(Bool, Skip.scope.eq(x, x), True{}, scope_eq_refl(x)) : {Bool.and(_, Bool.not(Bool.xor(p, p))) == True{} : Bool}
      xor_refl(p)

# Two rules one of which is not the other are not, either way round.
def rule_ne_sym.at(+a: Skip.Rule, +b: Skip.Rule, c: Bool, ec: {Skip.rule.eq(b, a) == c : Bool}, h: {Skip.rule.eq(a, b) == False{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      +be : {b == a : Skip.Rule} = rule_eq_sound(b, a, ec)
      +h2 : {Skip.rule.eq(a, a) == False{} : Bool} = (%be : {Skip.rule.eq(a, _) == False{} : Bool} h)
      (%rule_eq_refl(a) : {_ == False{} : Bool} h2)

def rule_ne_sym(+a: Skip.Rule, +b: Skip.Rule, h: {Skip.rule.eq(a, b) == False{} : Bool}) -> {Skip.rule.eq(b, a) == False{} : Bool}:
  rule_ne_sym.at(a, b, Skip.rule.eq(b, a), {==}, h)

def or_swap(a: Bool, b: Bool, -c: Bool) -> {Bool.or(b, Bool.or(a, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

# Listing
# -------

def or_true_r(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def not_true_false(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, S.false_true(e))

# A rule some earlier file stated is one `x` is not, when `x` was seen and
# the rule was not.
def unseen_ne.at(+r: Skip.Rule, +x: Skip.Rule, +seen: List<&2, Skip.Rule>, c: Bool, ec: {Skip.rule.eq(r, x) == c : Bool}, e: {Skip.held(seen, r) == False{} : Bool}, hx: {Skip.held(seen, x) == True{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      +re : {r == x : Skip.Rule} = rule_eq_sound(r, x, ec)
      +e2 : {Skip.held(seen, x) == False{} : Bool} = (%re : {Skip.held(seen, _) == False{} : Bool} e)
      (%hx : {_ == False{} : Bool} e2)

# Nothing the listing keeps is a rule already seen.
def disj.at(+r: Skip.Rule, +f: String, +rest: List<&2, Skip.Stating>, +seen: List<&2, Skip.Rule>, +x: Skip.Rule, +hx: {Skip.held(seen, x) == True{} : Bool}, d: Bool, e: {Skip.once.dup(Skip.Stating{r, f} <> rest, seen) == d : Bool}, ih: @s2: List<&2, Skip.Rule> -> {Skip.held(s2, x) == True{} : Bool} -> {Skip.held(Skip.stated.rules(Skip.once(rest, s2, Skip.once.dup(rest, s2))), x) == False{} : Bool}) -> {Skip.held(Skip.stated.rules(Skip.once(Skip.Stating{r, f} <> rest, seen, d)), x) == False{} : Bool}:
  match d:
    case True{}:
      ih(seen, hx)
    case False{}:
      +h2 : {Skip.held(r <> seen, x) == True{} : Bool} = (%Equal.sym(Bool, Skip.held(seen, x), True{}, hx) : {Bool.or(Skip.rule.eq(r, x), _) == True{} : Bool} or_true_r(Skip.rule.eq(r, x)))
      +n : {Skip.rule.eq(r, x) == False{} : Bool} = unseen_ne.at(r, x, seen, Skip.rule.eq(r, x), {==}, e, hx)
      %Equal.sym(Bool, Skip.rule.eq(r, x), False{}, n) : {Bool.or(_, Skip.held(Skip.stated.rules(Skip.once(rest, r <> seen, Skip.once.dup(rest, r <> seen))), x)) == False{} : Bool}
      ih(r <> seen, h2)

def disj(ss: List<&2, Skip.Stating>, +seen: List<&2, Skip.Rule>, +x: Skip.Rule, +hx: {Skip.held(seen, x) == True{} : Bool}) -> {Skip.held(Skip.stated.rules(Skip.once(ss, seen, Skip.once.dup(ss, seen))), x) == False{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case Skip.Stating{+r, +f} <> +rest:
      disj.at(r, f, rest, seen, x, hx, Skip.once.dup(Skip.Stating{r, f} <> rest, seen), {==}, s2 => h => disj(rest, s2, x, h))

def seen_self(+r: Skip.Rule, +seen: List<&2, Skip.Rule>) -> {Skip.held(r <> seen, r) == True{} : Bool}:
  (%Equal.sym(Bool, Skip.rule.eq(r, r), True{}, rule_eq_refl(r)) : {Bool.or(_, Skip.held(seen, r)) == True{} : Bool} {==})

def nd.at(+r: Skip.Rule, +f: String, +rest: List<&2, Skip.Stating>, +seen: List<&2, Skip.Rule>, d: Bool, e: {Skip.once.dup(Skip.Stating{r, f} <> rest, seen) == d : Bool}, ih: @s2: List<&2, Skip.Rule> -> {Skip.nodup(Skip.stated.rules(Skip.once(rest, s2, Skip.once.dup(rest, s2)))) == True{} : Bool}) -> {Skip.nodup(Skip.stated.rules(Skip.once(Skip.Stating{r, f} <> rest, seen, d))) == True{} : Bool}:
  match d:
    case True{}:
      ih(seen)
    case False{}:
      +o = Skip.stated.rules(Skip.once(rest, r <> seen, Skip.once.dup(rest, r <> seen)))
      %Equal.sym(Bool, Skip.held(o, r), False{}, disj(rest, r <> seen, r, seen_self(r, seen))) : {Bool.and(Bool.not(_), Skip.nodup(o)) == True{} : Bool}
      ih(r <> seen)

# The listing names no rule twice.
def nd(ss: List<&2, Skip.Stating>, +seen: List<&2, Skip.Rule>) -> {Skip.nodup(Skip.stated.rules(Skip.once(ss, seen, Skip.once.dup(ss, seen)))) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case Skip.Stating{+r, +f} <> +rest:
      nd.at(r, f, rest, seen, Skip.once.dup(Skip.Stating{r, f} <> rest, seen), {==}, s2 => nd(rest, s2))

# Every stated rule is one seen before or one the listing keeps.
def cov(ss: List<&2, Skip.Stating>, +seen: List<&2, Skip.Rule>, +out: List<&2, Skip.Rule>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Skip.Stating{+r, f} <> rest:
      Bool.and(Bool.or(Skip.held(seen, r), Skip.held(out, r)), cov(rest, seen, out))

def cov_shift(ss: List<&2, Skip.Stating>, +r: Skip.Rule, +seen: List<&2, Skip.Rule>, +out: List<&2, Skip.Rule>) -> {cov(ss, r <> seen, out) == cov(ss, seen, r <> out) : Bool}:
  match ss:
    case Nil{}:
      {==}
    case Skip.Stating{+y, g} <> +rest:
      %Equal.sym(Bool, cov(rest, r <> seen, out), cov(rest, seen, r <> out), cov_shift(rest, r, seen, out)) : {Bool.and(Bool.or(Bool.or(Skip.rule.eq(r, y), Skip.held(seen, y)), Skip.held(out, y)), _) == Bool.and(Bool.or(Skip.held(seen, y), Bool.or(Skip.rule.eq(r, y), Skip.held(out, y))), cov(rest, seen, r <> out)) : Bool}
      %or_swap(Skip.rule.eq(r, y), Skip.held(seen, y), Skip.held(out, y)) : {Bool.and(_, cov(rest, seen, r <> out)) == Bool.and(Bool.or(Skip.held(seen, y), Bool.or(Skip.rule.eq(r, y), Skip.held(out, y))), cov(rest, seen, r <> out)) : Bool}
      {==}

def cov.at(+r: Skip.Rule, +f: String, +rest: List<&2, Skip.Stating>, +seen: List<&2, Skip.Rule>, d: Bool, e: {Skip.once.dup(Skip.Stating{r, f} <> rest, seen) == d : Bool}, ih: @s2: List<&2, Skip.Rule> -> {cov(rest, s2, Skip.stated.rules(Skip.once(rest, s2, Skip.once.dup(rest, s2)))) == True{} : Bool}) -> {cov(Skip.Stating{r, f} <> rest, seen, Skip.stated.rules(Skip.once(Skip.Stating{r, f} <> rest, seen, d))) == True{} : Bool}:
  match d:
    case True{}:
      +o = Skip.stated.rules(Skip.once(rest, seen, Skip.once.dup(rest, seen)))
      %Equal.sym(Bool, Skip.held(seen, r), True{}, e) : {Bool.and(Bool.or(_, Skip.held(o, r)), cov(rest, seen, o)) == True{} : Bool}
      ih(seen)
    case False{}:
      +o = Skip.stated.rules(Skip.once(rest, r <> seen, Skip.once.dup(rest, r <> seen)))
      %Equal.sym(Bool, Skip.held(seen, r), False{}, e) : {Bool.and(Bool.or(_, Skip.held(r <> o, r)), cov(rest, seen, r <> o)) == True{} : Bool}
      %Equal.sym(Bool, Skip.held(r <> o, r), True{}, seen_self(r, o)) : {Bool.and(Bool.or(False{}, _), cov(rest, seen, r <> o)) == True{} : Bool}
      %cov_shift(rest, r, seen, o) : {_ == True{} : Bool}
      ih(r <> seen)

def cov_once(ss: List<&2, Skip.Stating>, +seen: List<&2, Skip.Rule>) -> {cov(ss, seen, Skip.stated.rules(Skip.once(ss, seen, Skip.once.dup(ss, seen)))) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case Skip.Stating{+r, +f} <> +rest:
      cov.at(r, f, rest, seen, Skip.once.dup(Skip.Stating{r, f} <> rest, seen), {==}, s2 => cov_once(rest, s2))

def cov_nil(ss: List<&2, Skip.Stating>, +out: List<&2, Skip.Rule>) -> {cov(ss, Nil{}, out) == Skip.all.held(Skip.stated.rules(ss), out) : Bool}:
  match ss:
    case Nil{}:
      {==}
    case Skip.Stating{+r, f} <> rest:
      Equal.cong(Bool, Bool, t => Bool.and(Skip.held(out, r), t), cov(rest, Nil{}, out), Skip.all.held(Skip.stated.rules(rest), out), cov_nil(rest, out))

# `skip` with no arguments lists every rule the store states, and none
# twice.
def lists_once(+ss: List<&2, Skip.Stating>) -> {Bool.and(Skip.nodup(Skip.stated.rules(Skip.once(ss, Nil{}, Skip.once.dup(ss, Nil{})))), Skip.all.held(Skip.stated.rules(ss), Skip.stated.rules(Skip.once(ss, Nil{}, Skip.once.dup(ss, Nil{}))))) == True{} : Bool}:
  +o = Skip.stated.rules(Skip.once(ss, Nil{}, Skip.once.dup(ss, Nil{})))
  %Equal.sym(Bool, Skip.nodup(o), True{}, nd(ss, Nil{})) : {Bool.and(_, Skip.all.held(Skip.stated.rules(ss), o)) == True{} : Bool}
  %cov_nil(ss, o) : {_ == True{} : Bool}
  cov_once(ss, Nil{})

# Writing
# -------

def or_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def held_app(xs: List<&2, Skip.Rule>, +ys: List<&2, Skip.Rule>, +r: Skip.Rule) -> {Skip.held(List.append(&2, Skip.Rule, xs, ys), r) == Bool.or(Skip.held(xs, r), Skip.held(ys, r)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      %Equal.sym(Bool, Skip.held(List.append(&2, Skip.Rule, rest, ys), r), Bool.or(Skip.held(rest, r), Skip.held(ys, r)), held_app(rest, ys, r)) : {Bool.or(Skip.rule.eq(x, r), _) == Bool.or(Bool.or(Skip.rule.eq(x, r), Skip.held(rest, r)), Skip.held(ys, r)) : Bool}
      or_assoc(Skip.rule.eq(x, r), Skip.held(rest, r), Skip.held(ys, r))


# A rule added last keeps a list clear of the store's rules, and free of
# repeats, where it is neither.
def none_snoc(xs: List<&2, Skip.Rule>, +had: List<&2, Skip.Rule>, +r: Skip.Rule, +h1: {Skip.none.held(xs, had) == True{} : Bool}, +h2: {Skip.held(had, r) == False{} : Bool}) -> {Skip.none.held(List.append(&2, Skip.Rule, xs, [r]), had) == True{} : Bool}:
  match xs:
    case Nil{}:
      %Equal.sym(Bool, Skip.held(had, r), False{}, h2) : {Bool.and(Bool.not(_), True{}) == True{} : Bool}
      {==}
    case +x <> +rest:
      AL.and_intro(Bool.not(Skip.held(had, x)), Skip.none.held(List.append(&2, Skip.Rule, rest, [r]), had), Comp.and_left(Bool.not(Skip.held(had, x)), Skip.none.held(rest, had), h1), none_snoc(rest, had, r, Comp.and_right(Bool.not(Skip.held(had, x)), Skip.none.held(rest, had), h1), h2))

def nodup_snoc(xs: List<&2, Skip.Rule>, +r: Skip.Rule, +h1: {Skip.nodup(xs) == True{} : Bool}, +h2: {Skip.held(xs, r) == False{} : Bool}) -> {Skip.nodup(List.append(&2, Skip.Rule, xs, [r])) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      +hx : {Skip.held(rest, x) == False{} : Bool} = not_true_false(Skip.held(rest, x), Comp.and_left(Bool.not(Skip.held(rest, x)), Skip.nodup(rest), h1))
      +nr : {Skip.nodup(rest) == True{} : Bool} = Comp.and_right(Bool.not(Skip.held(rest, x)), Skip.nodup(rest), h1)
      +c : {Skip.rule.eq(r, x) == False{} : Bool} = rule_ne_sym(x, r, AL.or_false_l(Skip.rule.eq(x, r), Skip.held(rest, r), h2))
      +d : {Skip.held(rest, r) == False{} : Bool} = AL.or_false_r(Skip.rule.eq(x, r), Skip.held(rest, r), h2)
      %Equal.sym(Bool, Skip.held(List.append(&2, Skip.Rule, rest, [r]), x), Bool.or(Skip.held(rest, x), Skip.held([r], x)), held_app(rest, [r], x)) : {Bool.and(Bool.not(_), Skip.nodup(List.append(&2, Skip.Rule, rest, [r]))) == True{} : Bool}
      %Equal.sym(Bool, Skip.held(rest, x), False{}, hx) : {Bool.and(Bool.not(Bool.or(_, Bool.or(Skip.rule.eq(r, x), False{}))), Skip.nodup(List.append(&2, Skip.Rule, rest, [r]))) == True{} : Bool}
      %Equal.sym(Bool, Skip.rule.eq(r, x), False{}, c) : {Bool.and(Bool.not(Bool.or(False{}, Bool.or(_, False{}))), Skip.nodup(List.append(&2, Skip.Rule, rest, [r]))) == True{} : Bool}
      nodup_snoc(rest, r, nr, d)

# What is written holds what it held before.
def mono.at(+r: Skip.Rule, +rest: List<&2, Skip.Rule>, +had: List<&2, Skip.Rule>, +f0: List<&2, Skip.Rule>, +a: List<&2, Skip.Rule>, +x: Skip.Rule, +hx: {Skip.held(f0, x) == True{} : Bool}, d: Bool, ih: @f1: List<&2, Skip.Rule> -> @a1: List<&2, Skip.Rule> -> {Skip.held(f1, x) == True{} : Bool} -> {Skip.held(Skip.sorted.fresh(Skip.sorted.go(rest, had, f1, a1, Skip.sorted.dup(rest, had, f1))), x) == True{} : Bool}) -> {Skip.held(Skip.sorted.fresh(Skip.sorted.go(r <> rest, had, f0, a, d)), x) == True{} : Bool}:
  match d:
    case True{}:
      ih(f0, List.append(&2, Skip.Rule, a, [r]), hx)
    case False{}:
      +h0 : {Bool.or(Skip.held(f0, x), Skip.held([r], x)) == True{} : Bool} = (%Equal.sym(Bool, Skip.held(f0, x), True{}, hx) : {Bool.or(_, Skip.held([r], x)) == True{} : Bool} {==})
      +h : {Skip.held(List.append(&2, Skip.Rule, f0, [r]), x) == True{} : Bool} = (%Equal.sym(Bool, Skip.held(List.append(&2, Skip.Rule, f0, [r]), x), Bool.or(Skip.held(f0, x), Skip.held([r], x)), held_app(f0, [r], x)) : {_ == True{} : Bool} h0)
      ih(List.append(&2, Skip.Rule, f0, [r]), a, h)

def mono(rs: List<&2, Skip.Rule>, +had: List<&2, Skip.Rule>, +f0: List<&2, Skip.Rule>, +a: List<&2, Skip.Rule>, +x: Skip.Rule, +hx: {Skip.held(f0, x) == True{} : Bool}) -> {Skip.held(Skip.sorted.fresh(Skip.sorted.go(rs, had, f0, a, Skip.sorted.dup(rs, had, f0))), x) == True{} : Bool}:
  match rs:
    case Nil{}:
      hx
    case +r <> +rest:
      mono.at(r, rest, had, f0, a, x, hx, Skip.sorted.dup(r <> rest, had, f0), f1 => a1 => h => mono(rest, had, f1, a1, x, h))

# What is written is new to the store and names no rule twice.
def fresh_new.at(+r: Skip.Rule, +rest: List<&2, Skip.Rule>, +had: List<&2, Skip.Rule>, +f0: List<&2, Skip.Rule>, +a: List<&2, Skip.Rule>, +h1: {Skip.none.held(f0, had) == True{} : Bool}, +h2: {Skip.nodup(f0) == True{} : Bool}, d: Bool, +e: {Bool.or(Skip.held(had, r), Skip.held(f0, r)) == d : Bool}, ih: @f1: List<&2, Skip.Rule> -> @a1: List<&2, Skip.Rule> -> {Skip.none.held(f1, had) == True{} : Bool} -> {Skip.nodup(f1) == True{} : Bool} -> {Bool.and(Skip.none.held(Skip.sorted.fresh(Skip.sorted.go(rest, had, f1, a1, Skip.sorted.dup(rest, had, f1))), had), Skip.nodup(Skip.sorted.fresh(Skip.sorted.go(rest, had, f1, a1, Skip.sorted.dup(rest, had, f1))))) == True{} : Bool}) -> {Bool.and(Skip.none.held(Skip.sorted.fresh(Skip.sorted.go(r <> rest, had, f0, a, d)), had), Skip.nodup(Skip.sorted.fresh(Skip.sorted.go(r <> rest, had, f0, a, d)))) == True{} : Bool}:
  match d:
    case True{}:
      ih(f0, List.append(&2, Skip.Rule, a, [r]), h1, h2)
    case False{}:
      +eh : {Skip.held(had, r) == False{} : Bool} = AL.or_false_l(Skip.held(had, r), Skip.held(f0, r), e)
      +ef : {Skip.held(f0, r) == False{} : Bool} = AL.or_false_r(Skip.held(had, r), Skip.held(f0, r), e)
      ih(List.append(&2, Skip.Rule, f0, [r]), a, none_snoc(f0, had, r, h1, eh), nodup_snoc(f0, r, h2, ef))

def fresh_new(rs: List<&2, Skip.Rule>, +had: List<&2, Skip.Rule>, +f0: List<&2, Skip.Rule>, +a: List<&2, Skip.Rule>, +h1: {Skip.none.held(f0, had) == True{} : Bool}, +h2: {Skip.nodup(f0) == True{} : Bool}) -> {Bool.and(Skip.none.held(Skip.sorted.fresh(Skip.sorted.go(rs, had, f0, a, Skip.sorted.dup(rs, had, f0))), had), Skip.nodup(Skip.sorted.fresh(Skip.sorted.go(rs, had, f0, a, Skip.sorted.dup(rs, had, f0))))) == True{} : Bool}:
  match rs:
    case Nil{}:
      AL.and_intro(Skip.none.held(f0, had), Skip.nodup(f0), h1, h2)
    case +r <> +rest:
      fresh_new.at(r, rest, had, f0, a, h1, h2, Skip.sorted.dup(r <> rest, had, f0), {==}, f1 => a1 => g1 => g2 => fresh_new(rest, had, f1, a1, g1, g2))

# Every rule asked is written or already stated.
def asked_had.at(+r: Skip.Rule, +rest: List<&2, Skip.Rule>, +had: List<&2, Skip.Rule>, +f0: List<&2, Skip.Rule>, +a: List<&2, Skip.Rule>, hh: Bool, ehh: {Skip.held(had, r) == hh : Bool}, e: {Bool.or(hh, Skip.held(f0, r)) == True{} : Bool}) -> {Bool.or(Skip.held(Skip.sorted.fresh(Skip.sorted.go(rest, had, f0, List.append(&2, Skip.Rule, a, [r]), Skip.sorted.dup(rest, had, f0))), r), hh) == True{} : Bool}:
  match hh:
    case True{}:
      or_true_r(Skip.held(Skip.sorted.fresh(Skip.sorted.go(rest, had, f0, List.append(&2, Skip.Rule, a, [r]), Skip.sorted.dup(rest, had, f0))), r))
    case False{}:
      %Equal.sym(Bool, Skip.held(Skip.sorted.fresh(Skip.sorted.go(rest, had, f0, List.append(&2, Skip.Rule, a, [r]), Skip.sorted.dup(rest, had, f0))), r), True{}, mono(rest, had, f0, List.append(&2, Skip.Rule, a, [r]), r, e)) : {Bool.or(_, False{}) == True{} : Bool}
      {==}

def asked.at(+r: Skip.Rule, +rest: List<&2, Skip.Rule>, +had: List<&2, Skip.Rule>, +f0: List<&2, Skip.Rule>, +a: List<&2, Skip.Rule>, d: Bool, e: {Bool.or(Skip.held(had, r), Skip.held(f0, r)) == d : Bool}, ih: @f1: List<&2, Skip.Rule> -> @a1: List<&2, Skip.Rule> -> {Skip.all.held(rest, List.append(&2, Skip.Rule, Skip.sorted.fresh(Skip.sorted.go(rest, had, f1, a1, Skip.sorted.dup(rest, had, f1))), had)) == True{} : Bool}) -> {Skip.all.held(r <> rest, List.append(&2, Skip.Rule, Skip.sorted.fresh(Skip.sorted.go(r <> rest, had, f0, a, d)), had)) == True{} : Bool}:
  match d:
    case True{}:
      +o = Skip.sorted.fresh(Skip.sorted.go(rest, had, f0, List.append(&2, Skip.Rule, a, [r]), Skip.sorted.dup(rest, had, f0)))
      %Equal.sym(Bool, Skip.held(List.append(&2, Skip.Rule, o, had), r), Bool.or(Skip.held(o, r), Skip.held(had, r)), held_app(o, had, r)) : {Bool.and(_, Skip.all.held(rest, List.append(&2, Skip.Rule, o, had))) == True{} : Bool}
      AL.and_intro(Bool.or(Skip.held(o, r), Skip.held(had, r)), Skip.all.held(rest, List.append(&2, Skip.Rule, o, had)), asked_had.at(r, rest, had, f0, a, Skip.held(had, r), {==}, e), ih(f0, List.append(&2, Skip.Rule, a, [r])))
    case False{}:
      +f1 = List.append(&2, Skip.Rule, f0, [r])
      +o = Skip.sorted.fresh(Skip.sorted.go(rest, had, f1, a, Skip.sorted.dup(rest, had, f1)))
      +s0 : {Bool.or(Skip.held(f0, r), Skip.held([r], r)) == True{} : Bool} = (%Equal.sym(Bool, Skip.held([r], r), True{}, seen_self(r, Nil{})) : {Bool.or(Skip.held(f0, r), _) == True{} : Bool} or_true_r(Skip.held(f0, r)))
      +self : {Skip.held(f1, r) == True{} : Bool} = (%Equal.sym(Bool, Skip.held(f1, r), Bool.or(Skip.held(f0, r), Skip.held([r], r)), held_app(f0, [r], r)) : {_ == True{} : Bool} s0)
      %Equal.sym(Bool, Skip.held(List.append(&2, Skip.Rule, o, had), r), Bool.or(Skip.held(o, r), Skip.held(had, r)), held_app(o, had, r)) : {Bool.and(_, Skip.all.held(rest, List.append(&2, Skip.Rule, o, had))) == True{} : Bool}
      %Equal.sym(Bool, Skip.held(o, r), True{}, mono(rest, had, f1, a, r, self)) : {Bool.and(Bool.or(_, Skip.held(had, r)), Skip.all.held(rest, List.append(&2, Skip.Rule, o, had))) == True{} : Bool}
      ih(f1, a)

def asked(rs: List<&2, Skip.Rule>, +had: List<&2, Skip.Rule>, +f0: List<&2, Skip.Rule>, +a: List<&2, Skip.Rule>) -> {Skip.all.held(rs, List.append(&2, Skip.Rule, Skip.sorted.fresh(Skip.sorted.go(rs, had, f0, a, Skip.sorted.dup(rs, had, f0))), had)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +rest:
      asked.at(r, rest, had, f0, a, Skip.sorted.dup(r <> rest, had, f0), {==}, f1 => a1 => asked(rest, had, f1, a1))

# What `skip <path>...` writes is no rule the store already states and no
# rule twice, and every rule asked for is written or was already there.
def writes_new(+rs: List<&2, Skip.Rule>, +had: List<&2, Skip.Rule>) -> {Bool.and(Bool.and(Skip.none.held(Skip.sorted.fresh(Skip.sorted.go(rs, had, Nil{}, Nil{}, Skip.sorted.dup(rs, had, Nil{}))), had), Skip.nodup(Skip.sorted.fresh(Skip.sorted.go(rs, had, Nil{}, Nil{}, Skip.sorted.dup(rs, had, Nil{}))))), Skip.all.held(rs, List.append(&2, Skip.Rule, Skip.sorted.fresh(Skip.sorted.go(rs, had, Nil{}, Nil{}, Skip.sorted.dup(rs, had, Nil{}))), had))) == True{} : Bool}:
  AL.and_intro(Bool.and(Skip.none.held(Skip.sorted.fresh(Skip.sorted.go(rs, had, Nil{}, Nil{}, Skip.sorted.dup(rs, had, Nil{}))), had), Skip.nodup(Skip.sorted.fresh(Skip.sorted.go(rs, had, Nil{}, Nil{}, Skip.sorted.dup(rs, had, Nil{}))))), Skip.all.held(rs, List.append(&2, Skip.Rule, Skip.sorted.fresh(Skip.sorted.go(rs, had, Nil{}, Nil{}, Skip.sorted.dup(rs, had, Nil{}))), had)), fresh_new(rs, had, Nil{}, Nil{}, {==}, {==}), asked(rs, had, Nil{}, Nil{}))









# What `skip` writes, read back
# -----------------------------
#
# `skip <path>` files one line, `show` of the rule and a newline, and every
# later command reads it back through `Folder.rule_in`, `Skipped::rule_in`'s
# port. Written for a path `skip` accepts — spelled, as `skip` spells it,
# with no `/` at its end — the file states exactly the rule meant.

def app_nil(a: String) -> {String.append(a, SNil{}) == a : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      Equal.cong(String, String, x => SCon{h, x}, String.append(t, SNil{}), t, app_nil(t))

def app_assoc(a: String, +b: String, +c: String) -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      Equal.cong(String, String, x => SCon{h, x}, String.append(String.append(t, b), c), String.append(t, String.append(b, c)), app_assoc(t, b, c))

def rev_go_app(a: String, +b: String, acc: String) -> {String.reverse.go(String.append(a, b), acc) == String.reverse.go(b, String.reverse.go(a, acc)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      rev_go_app(t, b, SCon{h, acc})

def rev_acc(s: String, +acc: String) -> {String.reverse.go(s, acc) == String.append(String.reverse.go(s, SNil{}), acc) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.trans(String, String.reverse.go(t, SCon{h, acc}), String.append(String.reverse.go(t, SNil{}), SCon{h, acc}), String.append(String.reverse.go(t, SCon{h, SNil{}}), acc),
        rev_acc(t, SCon{h, acc}),
        Equal.trans(String, String.append(String.reverse.go(t, SNil{}), SCon{h, acc}), String.append(String.append(String.reverse.go(t, SNil{}), SCon{h, SNil{}}), acc), String.append(String.reverse.go(t, SCon{h, SNil{}}), acc),
          Equal.sym(String, String.append(String.append(String.reverse.go(t, SNil{}), SCon{h, SNil{}}), acc), String.append(String.reverse.go(t, SNil{}), SCon{h, acc}), app_assoc(String.reverse.go(t, SNil{}), SCon{h, SNil{}}, acc)),
          Equal.cong(String, String, x => String.append(x, acc), String.append(String.reverse.go(t, SNil{}), SCon{h, SNil{}}), String.reverse.go(t, SCon{h, SNil{}}), Equal.sym(String, String.reverse.go(t, SCon{h, SNil{}}), String.append(String.reverse.go(t, SNil{}), SCon{h, SNil{}}), rev_acc(t, SCon{h, SNil{}})))))

def rev_app(+a: String, +b: String) -> {String.reverse(String.append(a, b)) == String.append(String.reverse(b), String.reverse(a)) : String}:
  Equal.trans(String, String.reverse.go(String.append(a, b), SNil{}), String.reverse.go(b, String.reverse.go(a, SNil{})), String.append(String.reverse.go(b, SNil{}), String.reverse.go(a, SNil{})),
    rev_go_app(a, b, SNil{}), rev_acc(b, String.reverse.go(a, SNil{})))

def sw_nil(z: String) -> {String.starts_with(z, SNil{}) == True{} : Bool}:
  match z:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

# Turning a string round twice gives it back.
def rev_rev(v: String) -> {String.reverse(String.reverse(v)) == v : String}:
  match v:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym(String, String.reverse.go(t, SCon{h, SNil{}}), String.append(String.reverse(t), SCon{h, SNil{}}), rev_acc(t, SCon{h, SNil{}})) : {String.reverse(_) == SCon{h, t} : String}
      %Equal.sym(String, String.reverse(String.append(String.reverse(t), SCon{h, SNil{}})), String.append(String.reverse(SCon{h, SNil{}}), String.reverse(String.reverse(t))), rev_app(String.reverse(t), SCon{h, SNil{}})) : {_ == SCon{h, t} : String}
      %Equal.sym(String, String.reverse(String.reverse(t)), t, rev_rev(t)) : {SCon{h, _} == SCon{h, t} : String}
      {==}

# A value with no line break in it is one line of the file.
def split_line(l: String, +h: {Skip.has_break(l) == False{} : Bool}) -> {String.split(l ++ "\n", '\n') == [l, SNil{}] : List<&2, String>}:
  match l:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(List<&2, String>, String.split(t ++ "\n", '\n'), [t, SNil{}], split_line(t, AL.or_false_r(Char.is_eq(c, '\n'), Skip.has_break(t), h))) : {String.split.fin(c, _, Char.is_eq(c, '\n')) == [SCon{c, t}, SNil{}] : List<&2, String>}
      %Equal.sym(Bool, Char.is_eq(c, '\n'), False{}, AL.or_false_l(Char.is_eq(c, '\n'), Skip.has_break(t), h)) : {String.split.fin(c, [t, SNil{}], _) == [SCon{c, t}, SNil{}] : List<&2, String>}
      {==}

# A character that is not whitespace is not a carriage return.
def no_cr.at(c: Char, b: Bool, e: {Char.is_eq(c, '\r') == b : Bool}, h: {Folder.is_ws(c) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      +ce : {c == '\r' : Char} = EqL.char_eq(c, '\r', e)
      Empty.absurd({True{} == False{} : Bool}, S.true_false((%ce : {Folder.is_ws(_) == False{} : Bool} h)))

def no_cr(+c: Char, h: {Folder.is_ws(c) == False{} : Bool}) -> {Char.is_eq(c, '\r') == False{} : Bool}:
  no_cr.at(c, Char.is_eq(c, '\r'), {==}, h)

# A string that is not empty does not turn round into one that is.
def rev_nonempty(+v: String, e: {String.reverse(v) == SNil{} : String}, ne: {String.is_empty(v) == False{} : Bool}) -> Empty:
  +vn : {String.reverse(SNil{}) == v : String} = (%e : {String.reverse(_) == v : String} rev_rev(v))
  S.true_false((%Equal.sym(String, SNil{}, v, vn) : {String.is_empty(_) == False{} : Bool} ne))

def trim_back.c(c: Char, t: String, +v: String, b: Bool, e: {String.reverse(v) == SCon{c, t} : String}, h: {String.starts_with.if(t, SNil{}, b) == False{} : Bool}) -> {Folder.trim.go(SCon{c, t}, b) == v : String}:
  match b:
    case True{}:
      Empty.absurd({Folder.trim.go(SCon{c, t}, True{}) == v : String}, S.false_true((%h : {_ == True{} : Bool} sw_nil(t))))
    case False{}:
      (%e : {String.reverse(_) == v : String} rev_rev(v))

def trim_back.at(+v: String, rv: String, e: {String.reverse(v) == rv : String}, ne: {String.is_empty(v) == False{} : Bool}, h: {String.starts_with(rv, "/") == False{} : Bool}) -> {Folder.trim_slashes(rv) == v : String}:
  match rv:
    case SNil{}:
      Empty.absurd({Folder.trim_slashes(SNil{}) == v : String}, rev_nonempty(v, e, ne))
    case SCon{+c, +t}:
      trim_back.c(c, t, v, Char.is_eq(c, '/'), e, h)

# A value with no `/` at its end is what `trim_end_matches('/')` leaves.
def trim_back(+v: String, ne: {String.is_empty(v) == False{} : Bool}, h: {String.ends_with(v, "/") == False{} : Bool}) -> {Folder.trim_slashes(String.reverse(v)) == v : String}:
  trim_back.at(v, String.reverse(v), {==}, ne, h)

# `skip <value>` reads back as a path, `skip <value>/` as a directory.
def path_value(+v: String, +ne: {String.is_empty(v) == False{} : Bool}, +h: {String.ends_with(v, "/") == False{} : Bool}) -> {Folder.scope.value(v, False{}) == Done{Folder.Scope.Path{v}} : Result<&2, &2, String, Folder.Scope>}:
  %Equal.sym(String, Folder.trim_slashes(String.reverse(v)), v, trim_back(v, ne, h)) : {Bool.pick(Result<&2, &2, String, Folder.Scope>, String.is_empty(_), Fail{Folder.value_error()}, Folder.scope.of(_, False{}, String.ends_with(v, "/"))) == Done{Folder.Scope.Path{v}} : Result<&2, &2, String, Folder.Scope>}
  %Equal.sym(Bool, String.is_empty(v), False{}, ne) : {Bool.pick(Result<&2, &2, String, Folder.Scope>, _, Fail{Folder.value_error()}, Folder.scope.of(v, False{}, String.ends_with(v, "/"))) == Done{Folder.Scope.Path{v}} : Result<&2, &2, String, Folder.Scope>}
  %Equal.sym(Bool, String.ends_with(v, "/"), False{}, h) : {Folder.scope.of(v, False{}, _) == Done{Folder.Scope.Path{v}} : Result<&2, &2, String, Folder.Scope>}
  {==}

def under_value(+v: String, +ne: {String.is_empty(v) == False{} : Bool}, +h: {String.ends_with(v, "/") == False{} : Bool}) -> {Folder.scope.value(v ++ "/", False{}) == Done{Folder.Scope.Under{v}} : Result<&2, &2, String, Folder.Scope>}:
  %Equal.sym(String, String.reverse.go(v ++ "/", SNil{}), String.reverse.go("/", String.reverse.go(v, SNil{})), rev_go_app(v, "/", SNil{})) : {Bool.pick(Result<&2, &2, String, Folder.Scope>, String.is_empty(Folder.trim_slashes(_)), Fail{Folder.value_error()}, Folder.scope.of(Folder.trim_slashes(_), False{}, String.starts_with(_, "/"))) == Done{Folder.Scope.Under{v}} : Result<&2, &2, String, Folder.Scope>}
  %Equal.sym(String, Folder.trim_slashes(String.reverse(v)), v, trim_back(v, ne, h)) : {Bool.pick(Result<&2, &2, String, Folder.Scope>, String.is_empty(_), Fail{Folder.value_error()}, Folder.scope.of(_, False{}, String.starts_with(String.reverse(v), SNil{}))) == Done{Folder.Scope.Under{v}} : Result<&2, &2, String, Folder.Scope>}
  %Equal.sym(Bool, String.is_empty(v), False{}, ne) : {Bool.pick(Result<&2, &2, String, Folder.Scope>, _, Fail{Folder.value_error()}, Folder.scope.of(v, False{}, String.starts_with(String.reverse(v), SNil{}))) == Done{Folder.Scope.Under{v}} : Result<&2, &2, String, Folder.Scope>}
  %Equal.sym(Bool, String.starts_with(String.reverse(v), SNil{}), True{}, sw_nil(String.reverse(v))) : {Folder.scope.of(v, False{}, _) == Done{Folder.Scope.Under{v}} : Result<&2, &2, String, Folder.Scope>}
  {==}

# A value trimmed of space stays so with a `/` after it.
def untrimmed_slash(v: String, u: {Folder.untrimmed(v) == False{} : Bool}) -> {Folder.untrimmed(v ++ "/") == False{} : Bool}:
  match v:
    case SNil{}:
      Empty.absurd({Folder.untrimmed("/") == False{} : Bool}, S.true_false(u))
    case SCon{+h, +t}:
      +u2 : {Bool.or(Folder.ws_at(Some{h}), Folder.ws_at(Folder.first_char(String.reverse(SCon{h, t})))) == False{} : Bool} = AL.or_false_r(False{}, Bool.or(Folder.ws_at(Some{h}), Folder.ws_at(Folder.first_char(String.reverse(SCon{h, t})))), u)
      +u3 : {Folder.ws_at(Some{h}) == False{} : Bool} = AL.or_false_l(Folder.ws_at(Some{h}), Folder.ws_at(Folder.first_char(String.reverse(SCon{h, t}))), u2)
      %Equal.sym(String, String.reverse.go(t ++ "/", SCon{h, SNil{}}), String.reverse.go("/", String.reverse.go(t, SCon{h, SNil{}})), rev_go_app(t, "/", SCon{h, SNil{}})) : {Bool.or(False{}, Bool.or(Folder.ws_at(Some{h}), Folder.ws_at(Folder.first_char(_)))) == False{} : Bool}
      %Equal.sym(Bool, Folder.ws_at(Some{h}), False{}, u3) : {Bool.or(False{}, Bool.or(_, Folder.ws_at(Some{'/'}))) == False{} : Bool}
      {==}

# Nor does it gain a line break.
def hb_slash(v: String, +h: {Skip.has_break(v) == False{} : Bool}) -> {Skip.has_break(v ++ "/") == False{} : Bool}:
  match v:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Skip.has_break(t ++ "/"), False{}, hb_slash(t, AL.or_false_r(Char.is_eq(c, '\n'), Skip.has_break(t), h))) : {Bool.or(Char.is_eq(c, '\n'), _) == False{} : Bool}
      %Equal.sym(Bool, Char.is_eq(c, '\n'), False{}, AL.or_false_l(Char.is_eq(c, '\n'), Skip.has_break(t), h)) : {Bool.or(_, False{}) == False{} : Bool}
      {==}

# Nor does it end in a carriage return, which `str::lines` would drop.
def last_not_cr.at(+v: String, rv: String, e: {String.reverse(v) == rv : String}, ne: {String.is_empty(v) == False{} : Bool}, w: {Folder.ws_at(Folder.first_char(rv)) == False{} : Bool}, +acc: String) -> {String.starts_with(String.append(rv, acc), "\r") == False{} : Bool}:
  match rv:
    case SNil{}:
      Empty.absurd({String.starts_with(acc, "\r") == False{} : Bool}, rev_nonempty(v, e, ne))
    case SCon{+c, t}:
      %Equal.sym(Bool, Char.is_eq(c, '\r'), False{}, no_cr(c, w)) : {String.starts_with.if(String.append(t, acc), SNil{}, _) == False{} : Bool}
      {==}

def last_not_cr(+v: String, ne: {String.is_empty(v) == False{} : Bool}, u: {Folder.untrimmed(v) == False{} : Bool}, +acc: String) -> {String.starts_with(String.reverse.go(v, acc), "\r") == False{} : Bool}:
  +u2 : {Bool.or(Folder.ws_at(Folder.first_char(v)), Folder.ws_at(Folder.first_char(String.reverse(v)))) == False{} : Bool} = AL.or_false_r(String.is_empty(v), Bool.or(Folder.ws_at(Folder.first_char(v)), Folder.ws_at(Folder.first_char(String.reverse(v)))), u)
  +w : {Folder.ws_at(Folder.first_char(String.reverse(v))) == False{} : Bool} = AL.or_false_r(Folder.ws_at(Folder.first_char(v)), Folder.ws_at(Folder.first_char(String.reverse(v))), u2)
  %Equal.sym(String, String.reverse.go(v, acc), String.append(String.reverse.go(v, SNil{}), acc), rev_acc(v, acc)) : {String.starts_with(_, "\r") == False{} : Bool}
  last_not_cr.at(v, String.reverse(v), {==}, ne, w, acc)

# A file of one line and a newline states what that line says.
def line_read(+l: String, hb: {Skip.has_break(l) == False{} : Bool}, hr: {String.ends_with(l, "\r") == False{} : Bool}) -> {Folder.rule_in(l ++ "\n") == Folder.stated.line(Folder.Stated.None{}, 1n, Folder.said(l)) : Folder.Stated}:
  %Equal.sym(List<&2, String>, String.split(l ++ "\n", '\n'), [l, SNil{}], split_line(l, hb)) : {Folder.stated.go(Folder.lines.trimmed(_), 1n, Folder.Stated.None{}) == Folder.stated.line(Folder.Stated.None{}, 1n, Folder.said(l)) : Folder.Stated}
  %Equal.sym(Bool, String.ends_with(l, "\r"), False{}, hr) : {Folder.stated.line(Folder.Stated.None{}, 1n, Folder.said(Bool.pick(String, _, String.take(l, Nat.sub(String.length(l), 1n)), l))) == Folder.stated.line(Folder.Stated.None{}, 1n, Folder.said(l)) : Folder.Stated}
  {==}

def nil_back(+v: String) -> {v == String.append(v, SNil{}) : String}:
  Equal.sym(String, String.append(v, SNil{}), v, app_nil(v))


def slash_not_cr(+v: String, +acc: String) -> {String.starts_with(String.reverse.go(v ++ "/", acc), "\r") == False{} : Bool}:
  %Equal.sym(String, String.reverse.go(v ++ "/", acc), String.reverse.go("/", String.reverse.go(v, acc)), rev_go_app(v, "/", acc)) : {String.starts_with(_, "\r") == False{} : Bool}
  {==}


def rdisc(r: Result<&2, &2, Main.Refused, Folder.Scope>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{s}:
      Empty

def fail_done(-x: Main.Refused, -sc: Folder.Scope, h: {Fail{x} == Done{sc} : Result<&2, &2, Main.Refused, Folder.Scope>}) -> Empty:
  %h : {rdisc(_) : Type}
  Unit{}

def scope_of(r: Result<&2, &2, Main.Refused, Folder.Scope>, d: Folder.Scope) -> Folder.Scope:
  match r:
    case Fail{e}:
      d
    case Done{s}:
      s




# Names
# -----

# Turning a string round keeps whether it holds a `/`.
def hs_rev_go(s: String, +acc: String) -> {Folder.has_slash(String.reverse.go(s, acc)) == Bool.or(Folder.has_slash(s), Folder.has_slash(acc)) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym(Bool, Folder.has_slash(String.reverse.go(t, SCon{h, acc})), Bool.or(Folder.has_slash(t), Folder.has_slash(SCon{h, acc})), hs_rev_go(t, SCon{h, acc})) : {_ == Bool.or(Bool.or(Char.is_eq(h, '/'), Folder.has_slash(t)), Folder.has_slash(acc)) : Bool}
      or_swap(Char.is_eq(h, '/'), Folder.has_slash(t), Folder.has_slash(acc))

def sw_slash.at(c: Char, t: String, b: Bool, eb: {Char.is_eq(c, '/') == b : Bool}, h: {String.starts_with.if(t, SNil{}, b) == True{} : Bool}) -> {Bool.or(b, Folder.has_slash(t)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Bool.or(False{}, Folder.has_slash(t)) == True{} : Bool}, S.false_true(h))

def sw_slash(s: String, h: {String.starts_with(s, "/") == True{} : Bool}) -> {Folder.has_slash(s) == True{} : Bool}:
  match s:
    case SNil{}:
      Empty.absurd({Folder.has_slash(SNil{}) == True{} : Bool}, S.false_true(h))
    case SCon{+c, t}:
      sw_slash.at(c, t, Char.is_eq(c, '/'), {==}, h)

def ends_no_slash.at(+v: String, b: Bool, eb: {String.starts_with(String.reverse(v), "/") == b : Bool}, hs: {Folder.has_slash(v) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      +r : {Folder.has_slash(String.reverse(v)) == True{} : Bool} = sw_slash(String.reverse(v), eb)
      +r2 : {Bool.or(Folder.has_slash(v), False{}) == True{} : Bool} = (%hs_rev_go(v, SNil{}) : {_ == True{} : Bool} r)
      Empty.absurd({True{} == False{} : Bool}, S.false_true((%hs : {Bool.or(_, False{}) == True{} : Bool} r2)))

# A value with no `/` in it has none at its end.
def ends_no_slash(+v: String, hs: {Folder.has_slash(v) == False{} : Bool}) -> {String.ends_with(v, "/") == False{} : Bool}:
  ends_no_slash.at(v, String.starts_with(String.reverse(v), "/"), {==}, hs)

# A name `skip --name` accepts is a pattern `Folder.pattern` takes.
def pattern_ok(+v: String, +ne: {String.is_empty(v) == False{} : Bool}, +hs: {Folder.has_slash(v) == False{} : Bool}, +st: {Folder.all_stars(v) == False{} : Bool}) -> {Folder.pattern(v) == Done{v} : Result<&2, &2, String, String>}:
  %Equal.sym(Bool, String.is_empty(v), False{}, ne) : {Bool.pick(Result<&2, &2, String, String>, _, Fail{"a pattern is not empty"}, Bool.pick(Result<&2, &2, String, String>, Folder.has_slash(v), Fail{"a pattern is one path component and holds no `/`: a path is spelled with `skip`"}, Bool.pick(Result<&2, &2, String, String>, Folder.all_stars(v), Fail{"a pattern of nothing but `*` is the whole folder, which rules exist to name the exceptions to"}, Done{v}))) == Done{v} : Result<&2, &2, String, String>}
  %Equal.sym(Bool, Folder.has_slash(v), False{}, hs) : {Bool.pick(Result<&2, &2, String, String>, _, Fail{"a pattern is one path component and holds no `/`: a path is spelled with `skip`"}, Bool.pick(Result<&2, &2, String, String>, Folder.all_stars(v), Fail{"a pattern of nothing but `*` is the whole folder, which rules exist to name the exceptions to"}, Done{v})) == Done{v} : Result<&2, &2, String, String>}
  %Equal.sym(Bool, Folder.all_stars(v), False{}, st) : {Bool.pick(Result<&2, &2, String, String>, _, Fail{"a pattern of nothing but `*` is the whole folder, which rules exist to name the exceptions to"}, Done{v}) == Done{v} : Result<&2, &2, String, String>}
  {==}

def name_value(+v: String, +ne: {String.is_empty(v) == False{} : Bool}, +hs: {Folder.has_slash(v) == False{} : Bool}, +st: {Folder.all_stars(v) == False{} : Bool}) -> {Folder.scope.value(v, True{}) == Done{Folder.Scope.Name{v}} : Result<&2, &2, String, Folder.Scope>}:
  +h : {String.ends_with(v, "/") == False{} : Bool} = ends_no_slash(v, hs)
  %Equal.sym(String, Folder.trim_slashes(String.reverse(v)), v, trim_back(v, ne, h)) : {Bool.pick(Result<&2, &2, String, Folder.Scope>, String.is_empty(_), Fail{Folder.value_error()}, Folder.scope.of(_, True{}, String.ends_with(v, "/"))) == Done{Folder.Scope.Name{v}} : Result<&2, &2, String, Folder.Scope>}
  %Equal.sym(Bool, String.is_empty(v), False{}, ne) : {Bool.pick(Result<&2, &2, String, Folder.Scope>, _, Fail{Folder.value_error()}, Folder.scope.of(v, True{}, String.ends_with(v, "/"))) == Done{Folder.Scope.Name{v}} : Result<&2, &2, String, Folder.Scope>}
  %Equal.sym(Bool, String.ends_with(v, "/"), False{}, h) : {Folder.scope.of(v, True{}, _) == Done{Folder.Scope.Name{v}} : Result<&2, &2, String, Folder.Scope>}
  %Equal.sym(Result<&2, &2, String, String>, Folder.pattern(v), Done{v}, pattern_ok(v, ne, hs, st)) : {Result.map(&2, &2, String, String, Folder.Scope, p => Folder.Scope.Name{p}, _) == Done{Folder.Scope.Name{v}} : Result<&2, &2, String, Folder.Scope>}
  {==}

def name_under_value(+v: String, +ne: {String.is_empty(v) == False{} : Bool}, +hs: {Folder.has_slash(v) == False{} : Bool}, +st: {Folder.all_stars(v) == False{} : Bool}) -> {Folder.scope.value(v ++ "/", True{}) == Done{Folder.Scope.NameUnder{v}} : Result<&2, &2, String, Folder.Scope>}:
  +h : {String.ends_with(v, "/") == False{} : Bool} = ends_no_slash(v, hs)
  %Equal.sym(String, String.reverse.go(v ++ "/", SNil{}), String.reverse.go("/", String.reverse.go(v, SNil{})), rev_go_app(v, "/", SNil{})) : {Bool.pick(Result<&2, &2, String, Folder.Scope>, String.is_empty(Folder.trim_slashes(_)), Fail{Folder.value_error()}, Folder.scope.of(Folder.trim_slashes(_), True{}, String.starts_with(_, "/"))) == Done{Folder.Scope.NameUnder{v}} : Result<&2, &2, String, Folder.Scope>}
  %Equal.sym(String, Folder.trim_slashes(String.reverse(v)), v, trim_back(v, ne, h)) : {Bool.pick(Result<&2, &2, String, Folder.Scope>, String.is_empty(_), Fail{Folder.value_error()}, Folder.scope.of(_, True{}, String.starts_with(String.reverse(v), SNil{}))) == Done{Folder.Scope.NameUnder{v}} : Result<&2, &2, String, Folder.Scope>}
  %Equal.sym(Bool, String.is_empty(v), False{}, ne) : {Bool.pick(Result<&2, &2, String, Folder.Scope>, _, Fail{Folder.value_error()}, Folder.scope.of(v, True{}, String.starts_with(String.reverse(v), SNil{}))) == Done{Folder.Scope.NameUnder{v}} : Result<&2, &2, String, Folder.Scope>}
  %Equal.sym(Bool, String.starts_with(String.reverse(v), SNil{}), True{}, sw_nil(String.reverse(v))) : {Folder.scope.of(v, True{}, _) == Done{Folder.Scope.NameUnder{v}} : Result<&2, &2, String, Folder.Scope>}
  %Equal.sym(Result<&2, &2, String, String>, Folder.pattern(v), Done{v}, pattern_ok(v, ne, hs, st)) : {Result.map(&2, &2, String, String, Folder.Scope, p => Folder.Scope.NameUnder{p}, _) == Done{Folder.Scope.NameUnder{v}} : Result<&2, &2, String, Folder.Scope>}
  {==}

# One line, read back whole: the rule `Folder.rule_in` finds in it, and
# whether it is private, as `Skip.stated.of` reads a file for the listing.
def back(+f: String, +l: String, +sc: Folder.Scope, +p: Bool, +hb: {Skip.has_break(l) == False{} : Bool}, +hr: {String.ends_with(l, "\r") == False{} : Bool}, es: {Folder.said(l) == Folder.Said.Rule{sc} : Folder.Said}, ep: {Skip.private.line([l]) == p : Bool}) -> {Skip.stated.of(f, l ++ "\n", Folder.rule_in(l ++ "\n")) == [Skip.Stating{Skip.Rule{sc, p}, f}] : List<&2, Skip.Stating>}:
  %Equal.sym(Folder.Stated, Folder.rule_in(l ++ "\n"), Folder.stated.line(Folder.Stated.None{}, 1n, Folder.said(l)), line_read(l, hb, hr)) : {Skip.stated.of(f, l ++ "\n", _) == [Skip.Stating{Skip.Rule{sc, p}, f}] : List<&2, Skip.Stating>}
  %Equal.sym(Folder.Said, Folder.said(l), Folder.Said.Rule{sc}, es) : {Skip.stated.of(f, l ++ "\n", Folder.stated.line(Folder.Stated.None{}, 1n, _)) == [Skip.Stating{Skip.Rule{sc, p}, f}] : List<&2, Skip.Stating>}
  %Equal.sym(List<&2, String>, String.split(l ++ "\n", '\n'), [l, SNil{}], split_line(l, hb)) : {[Skip.Stating{Skip.Rule{sc, Skip.private.line(Folder.lines.trimmed(_))}, f}] == [Skip.Stating{Skip.Rule{sc, p}, f}] : List<&2, Skip.Stating>}
  %Equal.sym(Bool, String.ends_with(l, "\r"), False{}, hr) : {[Skip.Stating{Skip.Rule{sc, Skip.private.line([Bool.pick(String, _, String.take(l, Nat.sub(String.length(l), 1n)), l)])}, f}] == [Skip.Stating{Skip.Rule{sc, p}, f}] : List<&2, Skip.Stating>}
  %Equal.sym(Bool, Skip.private.line([l]), p, ep) : {[Skip.Stating{Skip.Rule{sc, _}, f}] == [Skip.Stating{Skip.Rule{sc, p}, f}] : List<&2, Skip.Stating>}
  {==}

def said_value(+val: String, +k: Bool, +sc: Folder.Scope, u: {Folder.untrimmed(val) == False{} : Bool}, pv: {Folder.scope.value(val, k) == Done{sc} : Result<&2, &2, String, Folder.Scope>}) -> {Folder.said.of(Bool.pick(Result<&2, &2, String, Folder.Scope>, Folder.untrimmed(val), Fail{Folder.value_error()}, Folder.scope.value(val, k))) == Folder.Said.Rule{sc} : Folder.Said}:
  %Equal.sym(Bool, Folder.untrimmed(val), False{}, u) : {Folder.said.of(Bool.pick(Result<&2, &2, String, Folder.Scope>, _, Fail{Folder.value_error()}, Folder.scope.value(val, k))) == Folder.Said.Rule{sc} : Folder.Said}
  %Equal.sym(Result<&2, &2, String, Folder.Scope>, Folder.scope.value(val, k), Done{sc}, pv) : {Folder.said.of(_) == Folder.Said.Rule{sc} : Folder.Said}
  {==}

def read_path(+f: String, +v: String, p: Bool, +ne: {String.is_empty(v) == False{} : Bool}, +u: {Folder.untrimmed(v) == False{} : Bool}, +hb: {Skip.has_break(v) == False{} : Bool}, +h: {String.ends_with(v, "/") == False{} : Bool}) -> {Skip.stated.of(f, Skip.file.text(Skip.Rule{Folder.Scope.Path{v}, p}), Folder.rule_in(Skip.file.text(Skip.Rule{Folder.Scope.Path{v}, p}))) == [Skip.Stating{Skip.Rule{Folder.Scope.Path{v}, p}, f}] : List<&2, Skip.Stating>}:
  match p:
    case False{}:
      +l = Skip.show(Skip.Rule{Folder.Scope.Path{v}, False{}})
      +hbl : {Skip.has_break(String.append(v, SNil{})) == False{} : Bool} = (%nil_back(v) : {Skip.has_break(_) == False{} : Bool} hb)
      +hrl : {String.starts_with(String.reverse.go(String.append(v, SNil{}), " piks"), "\r") == False{} : Bool} = (%nil_back(v) : {String.starts_with(String.reverse.go(_, " piks"), "\r") == False{} : Bool} last_not_cr(v, ne, u, " piks"))
      +es : {Folder.said(l) == Folder.Said.Rule{Folder.Scope.Path{v}} : Folder.Said} = (%nil_back(v) : {Folder.said.of(Bool.pick(Result<&2, &2, String, Folder.Scope>, Folder.untrimmed(_), Fail{Folder.value_error()}, Folder.scope.value(_, False{}))) == Folder.Said.Rule{Folder.Scope.Path{v}} : Folder.Said} said_value(v, False{}, Folder.Scope.Path{v}, u, path_value(v, ne, h)))
      +ep : {Skip.private.line([l]) == False{} : Bool} = {==}
      back(f, l, Folder.Scope.Path{v}, False{}, hbl, hrl, es, ep)
    case True{}:
      +l = Skip.show(Skip.Rule{Folder.Scope.Path{v}, True{}})
      +hbl : {Skip.has_break(String.append(v, SNil{})) == False{} : Bool} = (%nil_back(v) : {Skip.has_break(_) == False{} : Bool} hb)
      +hrl : {String.starts_with(String.reverse.go(String.append(v, SNil{}), " etavirp"), "\r") == False{} : Bool} = (%nil_back(v) : {String.starts_with(String.reverse.go(_, " etavirp"), "\r") == False{} : Bool} last_not_cr(v, ne, u, " etavirp"))
      +es : {Folder.said(l) == Folder.Said.Rule{Folder.Scope.Path{v}} : Folder.Said} = (%nil_back(v) : {Folder.said.of(Bool.pick(Result<&2, &2, String, Folder.Scope>, Folder.untrimmed(_), Fail{Folder.value_error()}, Folder.scope.value(_, False{}))) == Folder.Said.Rule{Folder.Scope.Path{v}} : Folder.Said} said_value(v, False{}, Folder.Scope.Path{v}, u, path_value(v, ne, h)))
      +ep : {Skip.private.line([l]) == True{} : Bool} = (%Equal.sym(Bool, String.starts_with(String.append(v, SNil{}), SNil{}), True{}, sw_nil(String.append(v, SNil{}))) : {Bool.or(_, String.starts_with(l, "private-name ")) == True{} : Bool} {==})
      back(f, l, Folder.Scope.Path{v}, True{}, hbl, hrl, es, ep)

def read_under(+f: String, +v: String, p: Bool, +ne: {String.is_empty(v) == False{} : Bool}, +u: {Folder.untrimmed(v) == False{} : Bool}, +hb: {Skip.has_break(v) == False{} : Bool}, +h: {String.ends_with(v, "/") == False{} : Bool}) -> {Skip.stated.of(f, Skip.file.text(Skip.Rule{Folder.Scope.Under{v}, p}), Folder.rule_in(Skip.file.text(Skip.Rule{Folder.Scope.Under{v}, p}))) == [Skip.Stating{Skip.Rule{Folder.Scope.Under{v}, p}, f}] : List<&2, Skip.Stating>}:
  match p:
    case False{}:
      +l = Skip.show(Skip.Rule{Folder.Scope.Under{v}, False{}})
      +hbl : {Skip.has_break(v ++ "/") == False{} : Bool} = hb_slash(v, hb)
      +hrl : {String.starts_with(String.reverse.go(v ++ "/", " piks"), "\r") == False{} : Bool} = slash_not_cr(v, " piks")
      +es : {Folder.said(l) == Folder.Said.Rule{Folder.Scope.Under{v}} : Folder.Said} = said_value(v ++ "/", False{}, Folder.Scope.Under{v}, untrimmed_slash(v, u), under_value(v, ne, h))
      +ep : {Skip.private.line([l]) == False{} : Bool} = {==}
      back(f, l, Folder.Scope.Under{v}, False{}, hbl, hrl, es, ep)
    case True{}:
      +l = Skip.show(Skip.Rule{Folder.Scope.Under{v}, True{}})
      +hbl : {Skip.has_break(v ++ "/") == False{} : Bool} = hb_slash(v, hb)
      +hrl : {String.starts_with(String.reverse.go(v ++ "/", " etavirp"), "\r") == False{} : Bool} = slash_not_cr(v, " etavirp")
      +es : {Folder.said(l) == Folder.Said.Rule{Folder.Scope.Under{v}} : Folder.Said} = said_value(v ++ "/", False{}, Folder.Scope.Under{v}, untrimmed_slash(v, u), under_value(v, ne, h))
      +ep : {Skip.private.line([l]) == True{} : Bool} = (%Equal.sym(Bool, String.starts_with((v ++ "/"), SNil{}), True{}, sw_nil((v ++ "/"))) : {Bool.or(_, String.starts_with(l, "private-name ")) == True{} : Bool} {==})
      back(f, l, Folder.Scope.Under{v}, True{}, hbl, hrl, es, ep)

def read_name(+f: String, +v: String, p: Bool, +ne: {String.is_empty(v) == False{} : Bool}, +u: {Folder.untrimmed(v) == False{} : Bool}, +hb: {Skip.has_break(v) == False{} : Bool}, +hs: {Folder.has_slash(v) == False{} : Bool}, +st: {Folder.all_stars(v) == False{} : Bool}) -> {Skip.stated.of(f, Skip.file.text(Skip.Rule{Folder.Scope.Name{v}, p}), Folder.rule_in(Skip.file.text(Skip.Rule{Folder.Scope.Name{v}, p}))) == [Skip.Stating{Skip.Rule{Folder.Scope.Name{v}, p}, f}] : List<&2, Skip.Stating>}:
  match p:
    case False{}:
      +l = Skip.show(Skip.Rule{Folder.Scope.Name{v}, False{}})
      +hbl : {Skip.has_break(String.append(v, SNil{})) == False{} : Bool} = (%nil_back(v) : {Skip.has_break(_) == False{} : Bool} hb)
      +hrl : {String.starts_with(String.reverse.go(String.append(v, SNil{}), " eman-piks"), "\r") == False{} : Bool} = (%nil_back(v) : {String.starts_with(String.reverse.go(_, " eman-piks"), "\r") == False{} : Bool} last_not_cr(v, ne, u, " eman-piks"))
      +es : {Folder.said(l) == Folder.Said.Rule{Folder.Scope.Name{v}} : Folder.Said} = (%nil_back(v) : {Folder.said.of(Bool.pick(Result<&2, &2, String, Folder.Scope>, Folder.untrimmed(_), Fail{Folder.value_error()}, Folder.scope.value(_, True{}))) == Folder.Said.Rule{Folder.Scope.Name{v}} : Folder.Said} said_value(v, True{}, Folder.Scope.Name{v}, u, name_value(v, ne, hs, st)))
      +ep : {Skip.private.line([l]) == False{} : Bool} = {==}
      back(f, l, Folder.Scope.Name{v}, False{}, hbl, hrl, es, ep)
    case True{}:
      +l = Skip.show(Skip.Rule{Folder.Scope.Name{v}, True{}})
      +hbl : {Skip.has_break(String.append(v, SNil{})) == False{} : Bool} = (%nil_back(v) : {Skip.has_break(_) == False{} : Bool} hb)
      +hrl : {String.starts_with(String.reverse.go(String.append(v, SNil{}), " eman-etavirp"), "\r") == False{} : Bool} = (%nil_back(v) : {String.starts_with(String.reverse.go(_, " eman-etavirp"), "\r") == False{} : Bool} last_not_cr(v, ne, u, " eman-etavirp"))
      +es : {Folder.said(l) == Folder.Said.Rule{Folder.Scope.Name{v}} : Folder.Said} = (%nil_back(v) : {Folder.said.of(Bool.pick(Result<&2, &2, String, Folder.Scope>, Folder.untrimmed(_), Fail{Folder.value_error()}, Folder.scope.value(_, True{}))) == Folder.Said.Rule{Folder.Scope.Name{v}} : Folder.Said} said_value(v, True{}, Folder.Scope.Name{v}, u, name_value(v, ne, hs, st)))
      +ep : {Skip.private.line([l]) == True{} : Bool} = (%Equal.sym(Bool, String.starts_with(String.append(v, SNil{}), SNil{}), True{}, sw_nil(String.append(v, SNil{}))) : {Bool.or(False{}, _) == True{} : Bool} {==})
      back(f, l, Folder.Scope.Name{v}, True{}, hbl, hrl, es, ep)

def read_name_under(+f: String, +v: String, p: Bool, +ne: {String.is_empty(v) == False{} : Bool}, +u: {Folder.untrimmed(v) == False{} : Bool}, +hb: {Skip.has_break(v) == False{} : Bool}, +hs: {Folder.has_slash(v) == False{} : Bool}, +st: {Folder.all_stars(v) == False{} : Bool}) -> {Skip.stated.of(f, Skip.file.text(Skip.Rule{Folder.Scope.NameUnder{v}, p}), Folder.rule_in(Skip.file.text(Skip.Rule{Folder.Scope.NameUnder{v}, p}))) == [Skip.Stating{Skip.Rule{Folder.Scope.NameUnder{v}, p}, f}] : List<&2, Skip.Stating>}:
  match p:
    case False{}:
      +l = Skip.show(Skip.Rule{Folder.Scope.NameUnder{v}, False{}})
      +hbl : {Skip.has_break(v ++ "/") == False{} : Bool} = hb_slash(v, hb)
      +hrl : {String.starts_with(String.reverse.go(v ++ "/", " eman-piks"), "\r") == False{} : Bool} = slash_not_cr(v, " eman-piks")
      +es : {Folder.said(l) == Folder.Said.Rule{Folder.Scope.NameUnder{v}} : Folder.Said} = said_value(v ++ "/", True{}, Folder.Scope.NameUnder{v}, untrimmed_slash(v, u), name_under_value(v, ne, hs, st))
      +ep : {Skip.private.line([l]) == False{} : Bool} = {==}
      back(f, l, Folder.Scope.NameUnder{v}, False{}, hbl, hrl, es, ep)
    case True{}:
      +l = Skip.show(Skip.Rule{Folder.Scope.NameUnder{v}, True{}})
      +hbl : {Skip.has_break(v ++ "/") == False{} : Bool} = hb_slash(v, hb)
      +hrl : {String.starts_with(String.reverse.go(v ++ "/", " eman-etavirp"), "\r") == False{} : Bool} = slash_not_cr(v, " eman-etavirp")
      +es : {Folder.said(l) == Folder.Said.Rule{Folder.Scope.NameUnder{v}} : Folder.Said} = said_value(v ++ "/", True{}, Folder.Scope.NameUnder{v}, untrimmed_slash(v, u), name_under_value(v, ne, hs, st))
      +ep : {Skip.private.line([l]) == True{} : Bool} = (%Equal.sym(Bool, String.starts_with((v ++ "/"), SNil{}), True{}, sw_nil((v ++ "/"))) : {Bool.or(False{}, _) == True{} : Bool} {==})
      back(f, l, Folder.Scope.NameUnder{v}, True{}, hbl, hrl, es, ep)

def read_scoped(+f: String, +v: String, d: Bool, +p: Bool, +ne: {String.is_empty(v) == False{} : Bool}, +u: {Folder.untrimmed(v) == False{} : Bool}, +hb: {Skip.has_break(v) == False{} : Bool}, +h: {String.ends_with(v, "/") == False{} : Bool}) -> {Skip.stated.of(f, Skip.file.text(Skip.Rule{Bool.pick(Folder.Scope, d, Folder.Scope.Under{v}, Folder.Scope.Path{v}), p}), Folder.rule_in(Skip.file.text(Skip.Rule{Bool.pick(Folder.Scope, d, Folder.Scope.Under{v}, Folder.Scope.Path{v}), p}))) == [Skip.Stating{Skip.Rule{Bool.pick(Folder.Scope, d, Folder.Scope.Under{v}, Folder.Scope.Path{v}), p}, f}] : List<&2, Skip.Stating>}:
  match d:
    case True{}:
      read_under(f, v, p, ne, u, hb, h)
    case False{}:
      read_path(f, v, p, ne, u, hb, h)

def scoped_reads.at(+f: String, +v: String, ut: Bool, +eu: {Folder.untrimmed(v) == ut : Bool}, hb: Bool, +eb: {Skip.has_break(v) == hb : Bool}, +d: Bool, +p: Bool, +sc: Folder.Scope, e: {Skip.path.scoped.of(Bool.pick(Result<&2, &2, Main.Refused, String>, ut, Fail{Main.Refused{2, "`" ++ v ++ "` cannot be a rule: a value is not empty and carries no leading or trailing space"}}, Bool.pick(Result<&2, &2, Main.Refused, String>, hb, Fail{Main.Refused{2, "a rule is one line, and this value holds a line break"}}, Done{v})), d) == Done{sc} : Result<&2, &2, Main.Refused, Folder.Scope>}, +h: {String.ends_with(v, "/") == False{} : Bool}) -> {Skip.stated.of(f, Skip.file.text(Skip.Rule{sc, p}), Folder.rule_in(Skip.file.text(Skip.Rule{sc, p}))) == [Skip.Stating{Skip.Rule{sc, p}, f}] : List<&2, Skip.Stating>}:
  match ut hb:
    case True{} _:
      Empty.absurd({Skip.stated.of(f, Skip.file.text(Skip.Rule{sc, p}), Folder.rule_in(Skip.file.text(Skip.Rule{sc, p}))) == [Skip.Stating{Skip.Rule{sc, p}, f}] : List<&2, Skip.Stating>}, fail_done(Main.Refused{2, "`" ++ v ++ "` cannot be a rule: a value is not empty and carries no leading or trailing space"}, sc, e))
    case False{} True{}:
      Empty.absurd({Skip.stated.of(f, Skip.file.text(Skip.Rule{sc, p}), Folder.rule_in(Skip.file.text(Skip.Rule{sc, p}))) == [Skip.Stating{Skip.Rule{sc, p}, f}] : List<&2, Skip.Stating>}, fail_done(Main.Refused{2, "a rule is one line, and this value holds a line break"}, sc, e))
    case False{} False{}:
      +ea : {Bool.pick(Folder.Scope, d, Folder.Scope.Under{v}, Folder.Scope.Path{v}) == sc : Folder.Scope} = Equal.cong(Result<&2, &2, Main.Refused, Folder.Scope>, Folder.Scope, r => scope_of(r, sc), Done{Bool.pick(Folder.Scope, d, Folder.Scope.Under{v}, Folder.Scope.Path{v})}, Done{sc}, e)
      +ne : {String.is_empty(v) == False{} : Bool} = AL.or_false_l(String.is_empty(v), Bool.or(Folder.ws_at(Folder.first_char(v)), Folder.ws_at(Folder.first_char(String.reverse(v)))), eu)
      %ea : {Skip.stated.of(f, Skip.file.text(Skip.Rule{_, p}), Folder.rule_in(Skip.file.text(Skip.Rule{_, p}))) == [Skip.Stating{Skip.Rule{_, p}, f}] : List<&2, Skip.Stating>}
      read_scoped(f, v, d, p, ne, eu, eb, h)

# What `skip <path>` files for a path it accepts — spelled with no `/` at
# its end, as `skip` spells one — reads back as exactly the rule it meant.
def scoped_reads(+f: String, +v: String, +d: Bool, +p: Bool, +sc: Folder.Scope, e: {Skip.path.scoped(v, d) == Done{sc} : Result<&2, &2, Main.Refused, Folder.Scope>}, +h: {String.ends_with(v, "/") == False{} : Bool}) -> {Skip.stated.of(f, Skip.file.text(Skip.Rule{sc, p}), Folder.rule_in(Skip.file.text(Skip.Rule{sc, p}))) == [Skip.Stating{Skip.Rule{sc, p}, f}] : List<&2, Skip.Stating>}:
  scoped_reads.at(f, v, Folder.untrimmed(v), {==}, Skip.has_break(v), {==}, d, p, sc, e, h)

def read_named(+f: String, +v: String, d: Bool, +p: Bool, +ne: {String.is_empty(v) == False{} : Bool}, +u: {Folder.untrimmed(v) == False{} : Bool}, +hb: {Skip.has_break(v) == False{} : Bool}, +hs: {Folder.has_slash(v) == False{} : Bool}, +st: {Folder.all_stars(v) == False{} : Bool}) -> {Skip.stated.of(f, Skip.file.text(Skip.Rule{Bool.pick(Folder.Scope, d, Folder.Scope.NameUnder{v}, Folder.Scope.Name{v}), p}), Folder.rule_in(Skip.file.text(Skip.Rule{Bool.pick(Folder.Scope, d, Folder.Scope.NameUnder{v}, Folder.Scope.Name{v}), p}))) == [Skip.Stating{Skip.Rule{Bool.pick(Folder.Scope, d, Folder.Scope.NameUnder{v}, Folder.Scope.Name{v}), p}, f}] : List<&2, Skip.Stating>}:
  match d:
    case True{}:
      read_name_under(f, v, p, ne, u, hb, hs, st)
    case False{}:
      read_name(f, v, p, ne, u, hb, hs, st)

def named_reads.pattern(+f: String, +n: String, +v: String, es: Bool, +ees: {String.is_empty(v) == es : Bool}, hs: Bool, +ehs: {Folder.has_slash(v) == hs : Bool}, st: Bool, +est: {Folder.all_stars(v) == st : Bool}, +d: Bool, +p: Bool, +sc: Folder.Scope, e: {Skip.name.pattern.r(n, d, Bool.pick(Result<&2, &2, String, String>, es, Fail{"a pattern is not empty"}, Bool.pick(Result<&2, &2, String, String>, hs, Fail{"a pattern is one path component and holds no `/`: a path is spelled with `skip`"}, Bool.pick(Result<&2, &2, String, String>, st, Fail{"a pattern of nothing but `*` is the whole folder, which rules exist to name the exceptions to"}, Done{v})))) == Done{sc} : Result<&2, &2, Main.Refused, Folder.Scope>}, +u: {Folder.untrimmed(v) == False{} : Bool}, +hb: {Skip.has_break(v) == False{} : Bool}) -> {Skip.stated.of(f, Skip.file.text(Skip.Rule{sc, p}), Folder.rule_in(Skip.file.text(Skip.Rule{sc, p}))) == [Skip.Stating{Skip.Rule{sc, p}, f}] : List<&2, Skip.Stating>}:
  match es hs st:
    case True{} _ _:
      Empty.absurd({Skip.stated.of(f, Skip.file.text(Skip.Rule{sc, p}), Folder.rule_in(Skip.file.text(Skip.Rule{sc, p}))) == [Skip.Stating{Skip.Rule{sc, p}, f}] : List<&2, Skip.Stating>}, fail_done(Main.Refused{2, "`" ++ n ++ "` cannot be a name to match: " ++ "a pattern is not empty"}, sc, e))
    case False{} True{} _:
      Empty.absurd({Skip.stated.of(f, Skip.file.text(Skip.Rule{sc, p}), Folder.rule_in(Skip.file.text(Skip.Rule{sc, p}))) == [Skip.Stating{Skip.Rule{sc, p}, f}] : List<&2, Skip.Stating>}, fail_done(Main.Refused{2, "`" ++ n ++ "` cannot be a name to match: " ++ "a pattern is one path component and holds no `/`: a path is spelled with `skip`"}, sc, e))
    case False{} False{} True{}:
      Empty.absurd({Skip.stated.of(f, Skip.file.text(Skip.Rule{sc, p}), Folder.rule_in(Skip.file.text(Skip.Rule{sc, p}))) == [Skip.Stating{Skip.Rule{sc, p}, f}] : List<&2, Skip.Stating>}, fail_done(Main.Refused{2, "`" ++ n ++ "` cannot be a name to match: " ++ "a pattern of nothing but `*` is the whole folder, which rules exist to name the exceptions to"}, sc, e))
    case False{} False{} False{}:
      +ea : {Bool.pick(Folder.Scope, d, Folder.Scope.NameUnder{v}, Folder.Scope.Name{v}) == sc : Folder.Scope} = Equal.cong(Result<&2, &2, Main.Refused, Folder.Scope>, Folder.Scope, r => scope_of(r, sc), Done{Bool.pick(Folder.Scope, d, Folder.Scope.NameUnder{v}, Folder.Scope.Name{v})}, Done{sc}, e)
      %ea : {Skip.stated.of(f, Skip.file.text(Skip.Rule{_, p}), Folder.rule_in(Skip.file.text(Skip.Rule{_, p}))) == [Skip.Stating{Skip.Rule{_, p}, f}] : List<&2, Skip.Stating>}
      read_named(f, v, d, p, ees, u, hb, ehs, est)

def named_reads.at(+f: String, +n: String, +v: String, ut: Bool, +eu: {Folder.untrimmed(v) == ut : Bool}, hb: Bool, +eb: {Skip.has_break(v) == hb : Bool}, +d: Bool, +p: Bool, +sc: Folder.Scope, e: {Skip.name.scope.of(n, d, Bool.pick(Result<&2, &2, Main.Refused, String>, ut, Fail{Main.Refused{2, "`" ++ v ++ "` cannot be a rule: a value is not empty and carries no leading or trailing space"}}, Bool.pick(Result<&2, &2, Main.Refused, String>, hb, Fail{Main.Refused{2, "a rule is one line, and this value holds a line break"}}, Done{v}))) == Done{sc} : Result<&2, &2, Main.Refused, Folder.Scope>}) -> {Skip.stated.of(f, Skip.file.text(Skip.Rule{sc, p}), Folder.rule_in(Skip.file.text(Skip.Rule{sc, p}))) == [Skip.Stating{Skip.Rule{sc, p}, f}] : List<&2, Skip.Stating>}:
  match ut hb:
    case True{} _:
      Empty.absurd({Skip.stated.of(f, Skip.file.text(Skip.Rule{sc, p}), Folder.rule_in(Skip.file.text(Skip.Rule{sc, p}))) == [Skip.Stating{Skip.Rule{sc, p}, f}] : List<&2, Skip.Stating>}, fail_done(Main.Refused{2, "`" ++ v ++ "` cannot be a rule: a value is not empty and carries no leading or trailing space"}, sc, e))
    case False{} True{}:
      Empty.absurd({Skip.stated.of(f, Skip.file.text(Skip.Rule{sc, p}), Folder.rule_in(Skip.file.text(Skip.Rule{sc, p}))) == [Skip.Stating{Skip.Rule{sc, p}, f}] : List<&2, Skip.Stating>}, fail_done(Main.Refused{2, "a rule is one line, and this value holds a line break"}, sc, e))
    case False{} False{}:
      named_reads.pattern(f, n, v, String.is_empty(v), {==}, Folder.has_slash(v), {==}, Folder.all_stars(v), {==}, d, p, sc, e, eu, eb)

# What `skip --name <name>` files for a name it accepts reads back as
# exactly the rule it meant.
def named_reads(+f: String, +n: String, +p: Bool, +sc: Folder.Scope, e: {Skip.name.scope.r(n) == Done{sc} : Result<&2, &2, Main.Refused, Folder.Scope>}) -> {Skip.stated.of(f, Skip.file.text(Skip.Rule{sc, p}), Folder.rule_in(Skip.file.text(Skip.Rule{sc, p}))) == [Skip.Stating{Skip.Rule{sc, p}, f}] : List<&2, Skip.Stating>}:
  named_reads.at(f, n, Skip.unslash_one(n), Folder.untrimmed(Skip.unslash_one(n)), {==}, Skip.has_break(Skip.unslash_one(n)), {==}, String.ends_with(n, "/"), p, sc, e)

# What it skips
# -------------

def char_refl(c: Char) -> {Char.is_eq(c, c) == True{} : Bool}:
  match c:
    case Chr{x}:
      match x:
        case U32{+w}:
          %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, S.word_refl(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
          {==}

def sw_refl(a: String) -> {String.starts_with(a, a) == True{} : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      %Equal.sym(Bool, Char.is_eq(x, x), True{}, char_refl(x)) : {String.starts_with.if(t, t, _) == True{} : Bool}
      sw_refl(t)

def sw_if(c: Bool, -z: String, xt: String, yt: String, h: {String.starts_with.if(xt, yt, c) == True{} : Bool}, ih: {String.starts_with(xt, yt) == True{} : Bool} -> {String.starts_with(String.append(xt, z), yt) == True{} : Bool}) -> {String.starts_with.if(String.append(xt, z), yt, c) == True{} : Bool}:
  match c:
    case True{}:
      ih(h)
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(h))

# What starts with `b` still does with anything after it.
def sw_ext(a: String, b: String, +z: String, h: {String.starts_with(a, b) == True{} : Bool}) -> {String.starts_with(String.append(a, z), b) == True{} : Bool}:
  match a b:
    case SNil{} SNil{}:
      sw_nil(z)
    case SNil{} SCon{y, +yt}:
      Empty.absurd({String.starts_with(z, SCon{y, yt}) == True{} : Bool}, S.false_true(h))
    case SCon{x, +xt} SNil{}:
      {==}
    case SCon{x, xt} SCon{y, +yt}:
      sw_if(Char.is_eq(x, y), z, xt, yt, h, hh => sw_ext(xt, yt, z, hh))

def or_false_id(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# What it skips is the path named, or under it, and nothing else; a file
# it skips is checked first, so a break in the rule meets its refusal here.

def drop_none(s: String) -> {s == String.drop(s, 0n) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{x, t}:
      {==}

def split_at.c(b: Bool, +x: Char, +xt: String, +y: Char, +yt: String, eb: {Char.is_eq(x, y) == b : Bool}, h: {String.starts_with.if(xt, yt, b) == True{} : Bool}, ih: {String.starts_with(xt, yt) == True{} : Bool} -> {xt == String.append(yt, String.drop(xt, String.length(yt))) : String}) -> {SCon{x, xt} == SCon{y, String.append(yt, String.drop(xt, String.length(yt)))} : String}:
  match b:
    case False{}:
      Empty.absurd({SCon{x, xt} == SCon{y, String.append(yt, String.drop(xt, String.length(yt)))} : String}, S.false_true(h))
    case True{}:
      %EqL.char_eq(x, y, eb) : {SCon{x, xt} == SCon{_, String.append(yt, String.drop(xt, String.length(yt)))} : String}
      Equal.cong(String, String, z => SCon{x, z}, xt, String.append(yt, String.drop(xt, String.length(yt))), ih(h))

# A string that starts with `p` is `p` and what follows it.
def split_at(p: String, +s: String, h: {String.starts_with(s, p) == True{} : Bool}) -> {s == String.append(p, String.drop(s, String.length(p))) : String}:
  match p s:
    case SNil{} _:
      drop_none(s)
    case SCon{y, yt} SNil{}:
      Empty.absurd({SNil{} == String.append(SCon{y, yt}, String.drop(SNil{}, String.length(SCon{y, yt}))) : String}, S.false_true(h))
    case SCon{+y, +yt} SCon{+x, +xt}:
      split_at.c(Char.is_eq(x, y), x, xt, y, yt, {==}, h, hh => split_at(yt, xt, hh))

def or_false_true(b: Bool, h: {Bool.or(b, False{}) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(h))

def only_scoped(+v: String, d: Bool, +q: String, s: {Folder.skips([Bool.pick(Folder.Scope, d, Folder.Scope.Under{v}, Folder.Scope.Path{v})], q) == True{} : Bool}) -> {q == Bool.pick(String, d, String.append(v ++ "/", String.drop(q, String.length(v ++ "/"))), v) : String}:
  match d:
    case False{}:
      S.eq_true(q, v, or_false_true(String.eq(q, v), s))
    case True{}:
      split_at(v ++ "/", q, or_false_true(String.starts_with(q, v ++ "/"), s))

def only_directory(+v: String, d: Bool, +p: String, s: {Folder.skips_directory([Bool.pick(Folder.Scope, d, Folder.Scope.Under{v}, Folder.Scope.Path{v})], p) == True{} : Bool}) -> {p == v : String}:
  match d:
    case False{}:
      S.eq_true(p, v, or_false_true(String.eq(p, v), s))
    case True{}:
      S.eq_true(p, v, or_false_true(String.eq(p, v), s))

def skips_scoped(+v: String, d: Bool, +x: String) -> {Bool.pick(Bool, d, Bool.and(Folder.skips_directory([Bool.pick(Folder.Scope, d, Folder.Scope.Under{v}, Folder.Scope.Path{v})], v), Folder.skips([Bool.pick(Folder.Scope, d, Folder.Scope.Under{v}, Folder.Scope.Path{v})], String.append(v ++ "/", x))), Folder.skips([Bool.pick(Folder.Scope, d, Folder.Scope.Under{v}, Folder.Scope.Path{v})], v)) == True{} : Bool}:
  match d:
    case False{}:
      %Equal.sym(Bool, String.eq(v, v), True{}, S.eq_refl(v)) : {Bool.or(_, False{}) == True{} : Bool}
      {==}
    case True{}:
      %Equal.sym(Bool, String.eq(v, v), True{}, S.eq_refl(v)) : {Bool.and(Bool.or(_, False{}), Bool.or(String.starts_with(String.append(v ++ "/", x), v ++ "/"), False{})) == True{} : Bool}
      %Equal.sym(Bool, String.starts_with(String.append(v ++ "/", x), v ++ "/"), True{}, sw_ext(v ++ "/", v ++ "/", x, sw_refl(v ++ "/"))) : {Bool.or(_, False{}) == True{} : Bool}
      {==}

def scoped_scope.at(+v: String, ut: Bool, hb: Bool, +d: Bool, +sc: Folder.Scope, e: {Skip.path.scoped.of(Bool.pick(Result<&2, &2, Main.Refused, String>, ut, Fail{Main.Refused{2, "`" ++ v ++ "` cannot be a rule: a value is not empty and carries no leading or trailing space"}}, Bool.pick(Result<&2, &2, Main.Refused, String>, hb, Fail{Main.Refused{2, "a rule is one line, and this value holds a line break"}}, Done{v})), d) == Done{sc} : Result<&2, &2, Main.Refused, Folder.Scope>}) -> {Bool.pick(Folder.Scope, d, Folder.Scope.Under{v}, Folder.Scope.Path{v}) == sc : Folder.Scope}:
  match ut hb:
    case True{} _:
      Empty.absurd({Bool.pick(Folder.Scope, d, Folder.Scope.Under{v}, Folder.Scope.Path{v}) == sc : Folder.Scope}, fail_done(Main.Refused{2, "`" ++ v ++ "` cannot be a rule: a value is not empty and carries no leading or trailing space"}, sc, e))
    case False{} True{}:
      Empty.absurd({Bool.pick(Folder.Scope, d, Folder.Scope.Under{v}, Folder.Scope.Path{v}) == sc : Folder.Scope}, fail_done(Main.Refused{2, "a rule is one line, and this value holds a line break"}, sc, e))
    case False{} False{}:
      Equal.cong(Result<&2, &2, Main.Refused, Folder.Scope>, Folder.Scope, r => scope_of(r, sc), Done{Bool.pick(Folder.Scope, d, Folder.Scope.Under{v}, Folder.Scope.Path{v})}, Done{sc}, e)

# The rule `skip <path>` makes skips the file, or the directory and a file
# in it.
def scoped_skips(+v: String, +d: Bool, +sc: Folder.Scope, e: {Skip.path.scoped(v, d) == Done{sc} : Result<&2, &2, Main.Refused, Folder.Scope>}, +x: String) -> {Bool.pick(Bool, d, Bool.and(Folder.skips_directory([sc], v), Folder.skips([sc], String.append(v ++ "/", x))), Folder.skips([sc], v)) == True{} : Bool}:
  +ea : {Bool.pick(Folder.Scope, d, Folder.Scope.Under{v}, Folder.Scope.Path{v}) == sc : Folder.Scope} = scoped_scope.at(v, Folder.untrimmed(v), Skip.has_break(v), d, sc, e)
  %ea : {Bool.pick(Bool, d, Bool.and(Folder.skips_directory([_], v), Folder.skips([_], String.append(v ++ "/", x))), Folder.skips([_], v)) == True{} : Bool}
  skips_scoped(v, d, x)

# A file the rule `skip <path>` makes skips is the one named, or, for a
# directory, the one named, a `/`, and the rest of its path.
def scoped_only(+v: String, +d: Bool, +sc: Folder.Scope, e: {Skip.path.scoped(v, d) == Done{sc} : Result<&2, &2, Main.Refused, Folder.Scope>}, +q: String, s: {Folder.skips([sc], q) == True{} : Bool}) -> {q == Bool.pick(String, d, String.append(v ++ "/", String.drop(q, String.length(v ++ "/"))), v) : String}:
  +ea : {Bool.pick(Folder.Scope, d, Folder.Scope.Under{v}, Folder.Scope.Path{v}) == sc : Folder.Scope} = scoped_scope.at(v, Folder.untrimmed(v), Skip.has_break(v), d, sc, e)
  only_scoped(v, d, q, (%Equal.sym(Folder.Scope, Bool.pick(Folder.Scope, d, Folder.Scope.Under{v}, Folder.Scope.Path{v}), sc, ea) : {Folder.skips([_], q) == True{} : Bool} s))

# And a directory it skips whole is the one named.
def scoped_only_directory(+v: String, +d: Bool, +sc: Folder.Scope, e: {Skip.path.scoped(v, d) == Done{sc} : Result<&2, &2, Main.Refused, Folder.Scope>}, +p: String, s: {Folder.skips_directory([sc], p) == True{} : Bool}) -> {p == v : String}:
  +ea : {Bool.pick(Folder.Scope, d, Folder.Scope.Under{v}, Folder.Scope.Path{v}) == sc : Folder.Scope} = scoped_scope.at(v, Folder.untrimmed(v), Skip.has_break(v), d, sc, e)
  only_directory(v, d, p, (%Equal.sym(Folder.Scope, Bool.pick(Folder.Scope, d, Folder.Scope.Under{v}, Folder.Scope.Path{v}), sc, ea) : {Folder.skips_directory([_], p) == True{} : Bool} s))
