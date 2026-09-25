# `skip` names each rule once: its listing keeps the first file stating a
# rule and passes over every later one, and what it writes is only what
# neither the store nor an earlier word already states.
import Base
import ./skip.bend as Skip
import ./composition_lemmas.bend as Comp
import ./anchor_lemmas.bend as AL

def once_fresh.at(+r: Skip.Rule, +f: String, +rest: List<&2, Skip.Stating>, +seen: List<&2, Skip.Rule>, dup: Bool, e: {Skip.once.dup(Skip.Stating{r, f} <> rest, seen) == dup : Bool}, ih: @s2: List<&2, Skip.Rule> -> {Skip.fresh.stated(Skip.once(rest, s2, Skip.once.dup(rest, s2)), s2) == True{} : Bool}) -> {Skip.fresh.stated(Skip.once(Skip.Stating{r, f} <> rest, seen, dup), seen) == True{} : Bool}:
  match dup:
    case True{}:
      ih(seen)
    case False{}:
      %Equal.sym(Bool, Skip.held(seen, r), False{}, e) : {Bool.and(Bool.not(_), Skip.fresh.stated(Skip.once(rest, r <> seen, Skip.once.dup(rest, r <> seen)), r <> seen)) == True{} : Bool}
      ih(r <> seen)

# What the listing keeps is new against everything before it.
def once_fresh(ss: List<&2, Skip.Stating>, +seen: List<&2, Skip.Rule>) -> {Skip.fresh.stated(Skip.once(ss, seen, Skip.once.dup(ss, seen)), seen) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case Skip.Stating{+r, +f} <> +rest:
      once_fresh.at(r, f, rest, seen, Skip.once.dup(Skip.Stating{r, f} <> rest, seen), {==}, s2 => once_fresh(rest, s2))

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

def rapp_assoc(xs: List<&2, Skip.Rule>, +ys: List<&2, Skip.Rule>, +zs: List<&2, Skip.Rule>) -> {List.append(&2, Skip.Rule, List.append(&2, Skip.Rule, xs, ys), zs) == List.append(&2, Skip.Rule, xs, List.append(&2, Skip.Rule, ys, zs)) : List<&2, Skip.Rule>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      Equal.cong(List<&2, Skip.Rule>, List<&2, Skip.Rule>, l => x <> l, List.append(&2, Skip.Rule, List.append(&2, Skip.Rule, rest, ys), zs), List.append(&2, Skip.Rule, rest, List.append(&2, Skip.Rule, ys, zs)), rapp_assoc(rest, ys, zs))

def rapp_nil(xs: List<&2, Skip.Rule>) -> {List.append(&2, Skip.Rule, xs, Nil{}) == xs : List<&2, Skip.Rule>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      Equal.cong(List<&2, Skip.Rule>, List<&2, Skip.Rule>, l => x <> l, List.append(&2, Skip.Rule, rest, Nil{}), rest, rapp_nil(rest))

def and_true(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def and_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# A rule added last is new exactly when it is new against everything
# before it.
def fresh_snoc(xs: List<&2, Skip.Rule>, +had: List<&2, Skip.Rule>, +b: List<&2, Skip.Rule>, +r: Skip.Rule) -> {Skip.fresh.rules(List.append(&2, Skip.Rule, xs, [r]), had, b) == Bool.and(Skip.fresh.rules(xs, had, b), Bool.not(Bool.or(Skip.held(had, r), Skip.held(List.append(&2, Skip.Rule, b, xs), r)))) : Bool}:
  match xs:
    case Nil{}:
      %Equal.sym(List<&2, Skip.Rule>, List.append(&2, Skip.Rule, b, Nil{}), b, rapp_nil(b)) : {Bool.and(Bool.not(Bool.or(Skip.held(had, r), Skip.held(b, r))), True{}) == Bool.not(Bool.or(Skip.held(had, r), Skip.held(_, r))) : Bool}
      and_true(Bool.not(Bool.or(Skip.held(had, r), Skip.held(b, r))))
    case +x <> +rest:
      +bx = List.append(&2, Skip.Rule, b, [x])
      +nx = Bool.not(Bool.or(Skip.held(had, x), Skip.held(b, x)))
      +f = Skip.fresh.rules(rest, had, bx)
      %Equal.sym(Bool, Skip.fresh.rules(List.append(&2, Skip.Rule, rest, [r]), had, bx), Bool.and(f, Bool.not(Bool.or(Skip.held(had, r), Skip.held(List.append(&2, Skip.Rule, bx, rest), r)))), fresh_snoc(rest, had, bx, r)) : {Bool.and(nx, _) == Bool.and(Bool.and(nx, f), Bool.not(Bool.or(Skip.held(had, r), Skip.held(List.append(&2, Skip.Rule, b, x <> rest), r)))) : Bool}
      %Equal.sym(List<&2, Skip.Rule>, List.append(&2, Skip.Rule, bx, rest), List.append(&2, Skip.Rule, b, x <> rest), rapp_assoc(b, [x], rest)) : {Bool.and(nx, Bool.and(f, Bool.not(Bool.or(Skip.held(had, r), Skip.held(_, r))))) == Bool.and(Bool.and(nx, f), Bool.not(Bool.or(Skip.held(had, r), Skip.held(List.append(&2, Skip.Rule, b, x <> rest), r)))) : Bool}
      and_assoc(nx, f, Bool.not(Bool.or(Skip.held(had, r), Skip.held(List.append(&2, Skip.Rule, b, x <> rest), r))))

def sorted_fresh.at(+r: Skip.Rule, +rest: List<&2, Skip.Rule>, +had: List<&2, Skip.Rule>, +f0: List<&2, Skip.Rule>, +a: List<&2, Skip.Rule>, d: Bool, e: {Bool.or(Skip.held(had, r), Skip.held(f0, r)) == d : Bool}, ih: @f1: List<&2, Skip.Rule> -> @a1: List<&2, Skip.Rule> -> {Skip.fresh.rules(Skip.sorted.fresh(Skip.sorted.go(rest, had, f1, a1, Skip.sorted.dup(rest, had, f1))), had, Nil{}) == Skip.fresh.rules(f1, had, Nil{}) : Bool}) -> {Skip.fresh.rules(Skip.sorted.fresh(Skip.sorted.go(r <> rest, had, f0, a, d)), had, Nil{}) == Skip.fresh.rules(f0, had, Nil{}) : Bool}:
  match d:
    case True{}:
      ih(f0, List.append(&2, Skip.Rule, a, [r]))
    case False{}:
      +more = List.append(&2, Skip.Rule, f0, [r])
      +f = Skip.fresh.rules(f0, had, Nil{})
      %Equal.sym(Bool, Skip.fresh.rules(Skip.sorted.fresh(Skip.sorted.go(rest, had, more, a, Skip.sorted.dup(rest, had, more))), had, Nil{}), Skip.fresh.rules(more, had, Nil{}), ih(more, a)) : {_ == f : Bool}
      %Equal.sym(Bool, Skip.fresh.rules(more, had, Nil{}), Bool.and(f, Bool.not(Bool.or(Skip.held(had, r), Skip.held(f0, r)))), fresh_snoc(f0, had, Nil{}, r)) : {_ == f : Bool}
      %Equal.sym(Bool, Bool.or(Skip.held(had, r), Skip.held(f0, r)), False{}, e) : {Bool.and(f, Bool.not(_)) == f : Bool}
      and_true(f)

def sorted_fresh(rs: List<&2, Skip.Rule>, +had: List<&2, Skip.Rule>, +f0: List<&2, Skip.Rule>, +a: List<&2, Skip.Rule>) -> {Skip.fresh.rules(Skip.sorted.fresh(Skip.sorted.go(rs, had, f0, a, Skip.sorted.dup(rs, had, f0))), had, Nil{}) == Skip.fresh.rules(f0, had, Nil{}) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +rest:
      sorted_fresh.at(r, rest, had, f0, a, Skip.sorted.dup(r <> rest, had, f0), {==}, f1 => a1 => sorted_fresh(rest, had, f1, a1))

# What `skip` writes is new: no rule the store states, none twice.
def writes_new(rs: List<&2, Skip.Rule>, +had: List<&2, Skip.Rule>) -> {Skip.fresh.rules(Skip.sorted.fresh(Skip.sorted.go(rs, had, Nil{}, Nil{}, Skip.sorted.dup(rs, had, Nil{}))), had, Nil{}) == True{} : Bool}:
  sorted_fresh(rs, had, Nil{}, Nil{})
