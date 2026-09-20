# The parser only accepts ordered documents. `ordered_all` is what
# `Ops.next_op.bounded` demands of every operation; the first half shows it
# implies `Block.ordered`, the second that `Ops.parse` establishes it.
import Base
import ./ops.bend as Ops
import ./text.bend as T
import ./semantic_replay.bend as Block
import ./composition_lemmas.bend as Comp

# Refuting hypotheses that computed to the wrong constructor.
def mdisc(m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{x}:
      Unit

def some_none(x: String, e: {Some{x} == None{} : Maybe<&2, String>}) -> Empty:
  %e : {mdisc(_) : Type}
  Unit{}

def cdisc(c: Cmp) -> Type:
  match c:
    case LT{}:
      Unit
    case EQ{}:
      Unit
    case GT{}:
      Empty

def lt_gt(e: {LT{} == GT{} : Cmp}) -> Empty:
  %e : {cdisc(_) : Type}
  Unit{}

def eq_gt(e: {EQ{} == GT{} : Cmp}) -> Empty:
  %e : {cdisc(_) : Type}
  Unit{}

def and_intro(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, Comp.false_true(ea))

def none_of_is_none(m: Maybe<&2, String>, e: {Maybe.is_none(&2, String, m) == True{} : Bool}) -> {m == None{} : Maybe<&2, String>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, String>}, Comp.false_true(e))

# Arithmetic read off a comparison.
def le_of_gt(a: Nat, b: Nat, e: {Nat.cmp(a, b) == GT{} : Cmp}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_le(0n, 0n) == True{} : Bool}, eq_gt(e))
    case 0n 1n+bp:
      Empty.absurd({Nat.is_le(1n+bp, 0n) == True{} : Bool}, lt_gt(e))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      le_of_gt(ap, bp, e)

def lt_of_gt(a: Nat, b: Nat, e: {Nat.cmp(a, b) == GT{} : Cmp}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, eq_gt(e))
    case 0n 1n+bp:
      Empty.absurd({Nat.is_lt(1n+bp, 0n) == True{} : Bool}, lt_gt(e))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      lt_of_gt(ap, bp, e)

def le_of_lt(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, Comp.false_true(e))
    case 1n+ap 1n+bp:
      le_of_lt(ap, bp, e)

def le_of_not_lt(a: Nat, b: Nat, e: {Nat.is_lt(b, a) == False{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, Comp.false_true(Equal.sym(Bool, Nat.is_lt(0n, 1n+ap), False{}, e)))
    case 1n+ap 1n+bp:
      le_of_not_lt(ap, bp, e)

def lt_not_eq_rev(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, Comp.false_true(e))
    case 1n+ap 0n:
      Empty.absurd({Nat.is_eq(0n, 1n+ap) == False{} : Bool}, Comp.false_true(e))
    case 0n 1n+bp:
      {==}
    case 1n+ap 1n+bp:
      lt_not_eq_rev(ap, bp, e)

# What `Ops.ordered` accepting an operation says about its position.
def after_insert.c(+pat: Nat, -pitems: List<&2, Ops.Item>, +nat: Nat, c: Cmp, eq: {Nat.cmp(nat, pat) == c : Cmp}, nv: Ops.Verb, e: {Ops.ordered.of(Ops.Op{Ops.Insert{}, pat, pitems}, nv, nat, c) == None{} : Maybe<&2, String>}) -> {Nat.is_lt(pat, nat) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Nat.is_lt(pat, nat) == True{} : Bool}, some_none("operations out of order", e))
    case EQ{}:
      match nv:
        case Ops.Delete{}:
          Empty.absurd({Nat.is_lt(pat, nat) == True{} : Bool}, some_none("a delete after an insert at one position", e))
        case Ops.Insert{}:
          Empty.absurd({Nat.is_lt(pat, nat) == True{} : Bool}, some_none("two inserts at one position", e))
    case GT{}:
      lt_of_gt(nat, pat, eq)

def after_insert(+pat: Nat, -pitems: List<&2, Ops.Item>, nv: Ops.Verb, +nat: Nat, -nitems: List<&2, Ops.Item>, e: {Ops.ordered(Some{Ops.Op{Ops.Insert{}, pat, pitems}}, Ops.Op{nv, nat, nitems}) == None{} : Maybe<&2, String>}) -> {Nat.is_lt(pat, nat) == True{} : Bool}:
  after_insert.c(pat, pitems, nat, Nat.cmp(nat, pat), {==}, nv, e)

def after_delete.lt(+pat: Nat, +pitems: List<&2, Ops.Item>, -nv: Ops.Verb, +nat: Nat, lt: Bool, eq: {Nat.is_lt(nat, Nat.add(pat, List.length(&2, Ops.Item, pitems))) == lt : Bool}, e: {Bool.pick(Maybe<&2, String>, lt, Some{"two operations overlap"}, Bool.pick(Maybe<&2, String>, Bool.and(Nat.is_eq(nat, Nat.add(pat, List.length(&2, Ops.Item, pitems))), Ops.verb_is(nv, Ops.Delete{})), Some{"two deletes that meet are one delete"}, None{})) == None{} : Maybe<&2, String>}) -> {Nat.is_le(Nat.add(pat, List.length(&2, Ops.Item, pitems)), nat) == True{} : Bool}:
  match lt:
    case True{}:
      Empty.absurd({Nat.is_le(Nat.add(pat, List.length(&2, Ops.Item, pitems)), nat) == True{} : Bool}, some_none("two operations overlap", e))
    case False{}:
      le_of_not_lt(Nat.add(pat, List.length(&2, Ops.Item, pitems)), nat, eq)

def after_delete.c(+pat: Nat, +pitems: List<&2, Ops.Item>, +nat: Nat, c: Cmp, +eq: {Nat.cmp(nat, pat) == c : Cmp}, nv: Ops.Verb, e: {Ops.ordered.of(Ops.Op{Ops.Delete{}, pat, pitems}, nv, nat, c) == None{} : Maybe<&2, String>}) -> {Bool.pick(Bool, Cmp.is_eq(c), Ops.verb_is(nv, Ops.Insert{}), Nat.is_le(Nat.add(pat, List.length(&2, Ops.Item, pitems)), nat)) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Nat.is_le(Nat.add(pat, List.length(&2, Ops.Item, pitems)), nat) == True{} : Bool}, some_none("operations out of order", e))
    case EQ{}:
      match nv:
        case Ops.Delete{}:
          Empty.absurd({False{} == True{} : Bool}, some_none("two operations overlap", e))
        case Ops.Insert{}:
          {==}
    case GT{}:
      after_delete.lt(pat, pitems, nv, nat, Nat.is_lt(nat, Nat.add(pat, List.length(&2, Ops.Item, pitems))), {==}, e)

# Past a delete, the next operation is its replacement or sits at its end or later.
def after_delete(+pat: Nat, +pitems: List<&2, Ops.Item>, nv: Ops.Verb, +nat: Nat, -nitems: List<&2, Ops.Item>, e: {Ops.ordered(Some{Ops.Op{Ops.Delete{}, pat, pitems}}, Ops.Op{nv, nat, nitems}) == None{} : Maybe<&2, String>}) -> {Bool.pick(Bool, Nat.is_eq(nat, pat), Ops.verb_is(nv, Ops.Insert{}), Nat.is_le(Nat.add(pat, List.length(&2, Ops.Item, pitems)), nat)) == True{} : Bool}:
  after_delete.c(pat, pitems, nat, Nat.cmp(nat, pat), {==}, nv, e)

# What the parser demands: every operation may follow the previous one and
# the last delete, as `Ops.next_op.bounded` checks.
def ordered_all(ops: List<&2, Ops.Op>, prev: Maybe<&2, Ops.Op>, +pd: Maybe<&2, Ops.Op>) -> Bool:
  match ops:
    case Nil{}:
      True{}
    case +op <> rest:
      Bool.and(Maybe.is_none(&2, String, Ops.ordered(prev, op)), Bool.and(Maybe.is_none(&2, String, Ops.ordered(pd, op)), ordered_all(rest, Some{op}, Ops.remember_delete(op, pd))))

# Where a list starts, with a default for the empty one.
def first_at(ops: List<&2, Ops.Op>, d: Nat) -> Nat:
  match ops:
    case Nil{}:
      d
    case Ops.Op{v, at, items} <> rest:
      at

def accepted_prev(+prev: Maybe<&2, Ops.Op>, +pd: Maybe<&2, Ops.Op>, +op: Ops.Op, +rest: List<&2, Ops.Op>, e: {ordered_all(op <> rest, prev, pd) == True{} : Bool}) -> {Ops.ordered(prev, op) == None{} : Maybe<&2, String>}:
  none_of_is_none(Ops.ordered(prev, op), Comp.and_left(Maybe.is_none(&2, String, Ops.ordered(prev, op)), Bool.and(Maybe.is_none(&2, String, Ops.ordered(pd, op)), ordered_all(rest, Some{op}, Ops.remember_delete(op, pd))), e))

def accepted_pd(+prev: Maybe<&2, Ops.Op>, +pd: Maybe<&2, Ops.Op>, +op: Ops.Op, +rest: List<&2, Ops.Op>, e: {ordered_all(op <> rest, prev, pd) == True{} : Bool}) -> {Ops.ordered(pd, op) == None{} : Maybe<&2, String>}:
  none_of_is_none(Ops.ordered(pd, op), Comp.and_left(Maybe.is_none(&2, String, Ops.ordered(pd, op)), ordered_all(rest, Some{op}, Ops.remember_delete(op, pd)), Comp.and_right(Maybe.is_none(&2, String, Ops.ordered(prev, op)), Bool.and(Maybe.is_none(&2, String, Ops.ordered(pd, op)), ordered_all(rest, Some{op}, Ops.remember_delete(op, pd))), e)))

def accepted_rest(+prev: Maybe<&2, Ops.Op>, +pd: Maybe<&2, Ops.Op>, +op: Ops.Op, +rest: List<&2, Ops.Op>, e: {ordered_all(op <> rest, prev, pd) == True{} : Bool}) -> {ordered_all(rest, Some{op}, Ops.remember_delete(op, pd)) == True{} : Bool}:
  Comp.and_right(Maybe.is_none(&2, String, Ops.ordered(pd, op)), ordered_all(rest, Some{op}, Ops.remember_delete(op, pd)), Comp.and_right(Maybe.is_none(&2, String, Ops.ordered(prev, op)), Bool.and(Maybe.is_none(&2, String, Ops.ordered(pd, op)), ordered_all(rest, Some{op}, Ops.remember_delete(op, pd))), e))

# After an insert, whatever follows starts past it.
def first_after_insert(rest: List<&2, Ops.Op>, +at: Nat, +items: List<&2, Ops.Item>, +pd: Maybe<&2, Ops.Op>, e: {ordered_all(rest, Some{Ops.Op{Ops.Insert{}, at, items}}, pd) == True{} : Bool}) -> {Nat.is_le(at, first_at(rest, at)) == True{} : Bool}:
  match rest:
    case Nil{}:
      Comp.le_refl(at)
    case Ops.Op{+nv, +nat, +nitems} <> +more:
      le_of_lt(at, nat, after_insert(at, items, nv, nat, nitems, accepted_prev(Some{Ops.Op{Ops.Insert{}, at, items}}, pd, Ops.Op{nv, nat, nitems}, more, e)))

# After a replacement, whatever follows starts at the delete's end or later:
# the insert forbids the delete's own position, the delete forbids its run.
def first_after_replacement(rest: List<&2, Ops.Op>, +at: Nat, +items: List<&2, Ops.Item>, +at2: Nat, +items2: List<&2, Ops.Item>, eq: {at == at2 : Nat}, +e: {ordered_all(rest, Some{Ops.Op{Ops.Insert{}, at2, items2}}, Some{Ops.Op{Ops.Delete{}, at, items}}) == True{} : Bool}) -> {Nat.is_le(Nat.add(at, List.length(&2, Ops.Item, items)), first_at(rest, Nat.add(at, List.length(&2, Ops.Item, items)))) == True{} : Bool}:
  match rest:
    case Nil{}:
      Comp.le_refl(Nat.add(at, List.length(&2, Ops.Item, items)))
    case Ops.Op{+nv, +nat, +nitems} <> +more:
      +apart = lt_not_eq_rev(at2, nat, after_insert(at2, items2, nv, nat, nitems, accepted_prev(Some{Ops.Op{Ops.Insert{}, at2, items2}}, Some{Ops.Op{Ops.Delete{}, at, items}}, Ops.Op{nv, nat, nitems}, more, e)))
      +past = after_delete(at, items, nv, nat, nitems, accepted_pd(Some{Ops.Op{Ops.Insert{}, at2, items2}}, Some{Ops.Op{Ops.Delete{}, at, items}}, Ops.Op{nv, nat, nitems}, more, e))
      %apart : {Bool.pick(Bool, _, Ops.verb_is(nv, Ops.Insert{}), Nat.is_le(Nat.add(at, List.length(&2, Ops.Item, items)), nat)) == True{} : Bool}
      %eq : {Bool.pick(Bool, Nat.is_eq(nat, _), Ops.verb_is(nv, Ops.Insert{}), Nat.is_le(Nat.add(at, List.length(&2, Ops.Item, items)), nat)) == True{} : Bool}
      past

def pick_false(c: Bool, -x: Bool, -y: Bool, eq: {c == False{} : Bool}, h: {Bool.pick(Bool, c, x, y) == True{} : Bool}) -> {y == True{} : Bool}:
  match c:
    case False{}:
      h
    case True{}:
      Empty.absurd({y == True{} : Bool}, Comp.false_true(Equal.sym(Bool, True{}, False{}, eq)))

def delete_apart.same(+at: Nat, +items: List<&2, Ops.Item>, +at2: Nat, same: Bool, h: {Bool.pick(Bool, same, False{}, Nat.is_le(Nat.add(at, List.length(&2, Ops.Item, items)), at2)) == True{} : Bool}) -> {Nat.is_le(Nat.add(at, List.length(&2, Ops.Item, items)), at2) == True{} : Bool}:
  match same:
    case True{}:
      Empty.absurd({Nat.is_le(Nat.add(at, List.length(&2, Ops.Item, items)), at2) == True{} : Bool}, Comp.false_true(h))
    case False{}:
      h

# Two deletes: the second starts at the first's end or later.
def delete_apart(+at: Nat, +items: List<&2, Ops.Item>, +at2: Nat, -items2: List<&2, Ops.Item>, e: {Ops.ordered(Some{Ops.Op{Ops.Delete{}, at, items}}, Ops.Op{Ops.Delete{}, at2, items2}) == None{} : Maybe<&2, String>}) -> {Nat.is_le(Nat.add(at, List.length(&2, Ops.Item, items)), at2) == True{} : Bool}:
  delete_apart.same(at, items, at2, Nat.is_eq(at2, at), after_delete(at, items, Ops.Delete{}, at2, items2, e))

# A delete and the insert after it, as `Block.ordered` reads them: the
# insert is a replacement when it shares the delete's position.
def parser_ordered.replacement(+pos: Nat, +at: Nat, +items: List<&2, Ops.Item>, +at2: Nat, +items2: List<&2, Ops.Item>, +more: List<&2, Ops.Op>, +prev: Maybe<&2, Ops.Op>, +pd: Maybe<&2, Ops.Op>, same: Bool, +eq: {Nat.is_eq(at2, at) == same : Bool}, +e: {ordered_all(Ops.Op{Ops.Delete{}, at, items} <> Ops.Op{Ops.Insert{}, at2, items2} <> more, prev, pd) == True{} : Bool}, lo: {Nat.is_le(pos, at) == True{} : Bool}, ih_stop: {ordered_all(more, Some{Ops.Op{Ops.Insert{}, at2, items2}}, Some{Ops.Op{Ops.Delete{}, at, items}}) == True{} : Bool} -> {Nat.is_le(Nat.add(at, List.length(&2, Ops.Item, items)), first_at(more, Nat.add(at, List.length(&2, Ops.Item, items)))) == True{} : Bool} -> {Block.ordered(more, Nat.add(at, List.length(&2, Ops.Item, items))) == True{} : Bool}, ih_at2: {ordered_all(more, Some{Ops.Op{Ops.Insert{}, at2, items2}}, Some{Ops.Op{Ops.Delete{}, at, items}}) == True{} : Bool} -> {Nat.is_le(at2, first_at(more, at2)) == True{} : Bool} -> {Block.ordered(more, at2) == True{} : Bool}) -> {Bool.and(Nat.is_le(pos, at), Bool.pick(Bool, same, Block.ordered(more, Nat.add(at, List.length(&2, Ops.Item, items))), Bool.and(Nat.is_le(Nat.add(at, List.length(&2, Ops.Item, items)), at2), Block.ordered(more, at2)))) == True{} : Bool}:
  match same:
    case True{}:
      +tail = {Ops.Op{Ops.Insert{}, at2, items2} <> more : List<&2, Ops.Op>}
      +e2 = accepted_rest(prev, pd, Ops.Op{Ops.Delete{}, at, items}, tail, e)
      +e3 = accepted_rest(Some{Ops.Op{Ops.Delete{}, at, items}}, Some{Ops.Op{Ops.Delete{}, at, items}}, Ops.Op{Ops.Insert{}, at2, items2}, more, e2)
      +stop = Nat.add(at, List.length(&2, Ops.Item, items))
      and_intro(Nat.is_le(pos, at), Block.ordered(more, stop), lo, ih_stop(e3, first_after_replacement(more, at, items, at2, items2, Equal.sym(Nat, at2, at, Comp.eq_of_is_eq(at2, at, eq)), e3)))
    case False{}:
      +tail = {Ops.Op{Ops.Insert{}, at2, items2} <> more : List<&2, Ops.Op>}
      +e2 = accepted_rest(prev, pd, Ops.Op{Ops.Delete{}, at, items}, tail, e)
      +e3 = accepted_rest(Some{Ops.Op{Ops.Delete{}, at, items}}, Some{Ops.Op{Ops.Delete{}, at, items}}, Ops.Op{Ops.Insert{}, at2, items2}, more, e2)
      +stop = Nat.add(at, List.length(&2, Ops.Item, items))
      +apart = pick_false(Nat.is_eq(at2, at), True{}, Nat.is_le(stop, at2), eq, after_delete(at, items, Ops.Insert{}, at2, items2, accepted_prev(Some{Ops.Op{Ops.Delete{}, at, items}}, Some{Ops.Op{Ops.Delete{}, at, items}}, Ops.Op{Ops.Insert{}, at2, items2}, more, e2)))
      and_intro(Nat.is_le(pos, at), Bool.and(Nat.is_le(stop, at2), Block.ordered(more, at2)), lo, and_intro(Nat.is_le(stop, at2), Block.ordered(more, at2), apart, ih_at2(e3, first_after_insert(more, at2, items2, Some{Ops.Op{Ops.Delete{}, at, items}}, e3))))

# Every list the parser's ordering admits is one `Block.ordered` admits.
def parser_ordered(ops: List<&2, Ops.Op>, +pos: Nat, +prev: Maybe<&2, Ops.Op>, +pd: Maybe<&2, Ops.Op>, +e: {ordered_all(ops, prev, pd) == True{} : Bool}, lo: {Nat.is_le(pos, first_at(ops, pos)) == True{} : Bool}) -> {Block.ordered(ops, pos) == True{} : Bool}:
  match ops:
    case Nil{}:
      {==}
    case Ops.Op{Ops.Insert{}, +at, +items} <> +rest:
      +e2 = accepted_rest(prev, pd, Ops.Op{Ops.Insert{}, at, items}, rest, e)
      and_intro(Nat.is_le(pos, at), Block.ordered(rest, at), lo, parser_ordered(rest, at, Some{Ops.Op{Ops.Insert{}, at, items}}, pd, e2, first_after_insert(rest, at, items, pd, e2)))
    case Ops.Op{Ops.Delete{}, +at, +items} <> rest:
      match rest:
        case Nil{}:
          lo
        case Ops.Op{Ops.Insert{}, +at2, +items2} <> +more:
          +stop = Nat.add(at, List.length(&2, Ops.Item, items))
          parser_ordered.replacement(pos, at, items, at2, items2, more, prev, pd, Nat.is_eq(at2, at), {==}, e, lo, x => y => parser_ordered(more, stop, Some{Ops.Op{Ops.Insert{}, at2, items2}}, Some{Ops.Op{Ops.Delete{}, at, items}}, x, y), x => y => parser_ordered(more, at2, Some{Ops.Op{Ops.Insert{}, at2, items2}}, Some{Ops.Op{Ops.Delete{}, at, items}}, x, y))
        case Ops.Op{Ops.Delete{}, +at2, +items2} <> +more:
          +stop = Nat.add(at, List.length(&2, Ops.Item, items))
          +tail = {Ops.Op{Ops.Delete{}, at2, items2} <> more : List<&2, Ops.Op>}
          +e2 = accepted_rest(prev, pd, Ops.Op{Ops.Delete{}, at, items}, tail, e)
          and_intro(Nat.is_le(pos, at), Block.ordered(tail, stop), lo, parser_ordered(tail, stop, Some{Ops.Op{Ops.Delete{}, at, items}}, Some{Ops.Op{Ops.Delete{}, at, items}}, e2, delete_apart(at, items, at2, items2, accepted_prev(Some{Ops.Op{Ops.Delete{}, at, items}}, Some{Ops.Op{Ops.Delete{}, at, items}}, Ops.Op{Ops.Delete{}, at2, items2}, more, e2))))

# The parse loop
# --------------

def ndisc(n: Ops.Next) -> Type:
  match n:
    case Ops.More{op, rest, at}:
      Empty
    case Ops.End{}:
      Unit
    case Ops.Bad{at, msg}:
      Unit

def end_more(-op: Ops.Op, -rest: List<&2, T.Line>, -at: Nat, e: {Ops.End{} == Ops.More{op, rest, at} : Ops.Next}) -> Empty:
  %e : {ndisc(_) : Type}
  Unit{}

def bad_more(-bat: Nat, -msg: String, -op: Ops.Op, -rest: List<&2, T.Line>, -at: Nat, e: {Ops.Bad{bat, msg} == Ops.More{op, rest, at} : Ops.Next}) -> Empty:
  %e : {ndisc(_) : Type}
  Unit{}

def rdisc(r: Result<&2, &2, String, List<&2, Ops.Op>>) -> Type:
  match r:
    case Fail{msg}:
      Unit
    case Done{xs}:
      Empty

def fail_done(-msg: String, -xs: List<&2, Ops.Op>, e: {Fail{msg} == Done{xs} : Result<&2, &2, String, List<&2, Ops.Op>>}) -> Empty:
  %e : {rdisc(_) : Type}
  Unit{}

def ops_of_result(r: Result<&2, &2, String, List<&2, Ops.Op>>) -> List<&2, Ops.Op>:
  match r:
    case Fail{msg}:
      Nil{}
    case Done{xs}:
      xs

def done_inj(-xs: List<&2, Ops.Op>, -ys: List<&2, Ops.Op>, e: {Done{xs} == Done{ys} : Result<&2, &2, String, List<&2, Ops.Op>>}) -> {xs == ys : List<&2, Ops.Op>}:
  Equal.cong(Result<&2, &2, String, List<&2, Ops.Op>>, List<&2, Ops.Op>, ops_of_result, Done{xs}, Done{ys}, e)

# What `Ops.next_op.bounded` has established about the operation it hands on.
def ordered_more(prev: Maybe<&2, Ops.Op>, pd: Maybe<&2, Ops.Op>, n: Ops.Next) -> Bool:
  match n:
    case Ops.More{+op, rest, at}:
      Bool.and(Maybe.is_none(&2, String, Ops.ordered(prev, op)), Maybe.is_none(&2, String, Ops.ordered(pd, op)))
    case Ops.End{}:
      True{}
    case Ops.Bad{at, msg}:
      True{}

def fin_ok(+prev: Maybe<&2, Ops.Op>, +pd: Maybe<&2, Ops.Op>, +op: Ops.Op, rest: List<&2, T.Line>, at: Nat, a: Maybe<&2, String>, b: Maybe<&2, String>, ea: {Ops.ordered(prev, op) == a : Maybe<&2, String>}, eb: {Ops.ordered(pd, op) == b : Maybe<&2, String>}) -> {ordered_more(prev, pd, Ops.next_op.fin(op, rest, at, Maybe.or(&2, String, a, b))) == True{} : Bool}:
  match a b:
    case Some{x} _:
      {==}
    case None{} Some{x}:
      {==}
    case None{} None{}:
      %Equal.sym(Maybe<&2, String>, Ops.ordered(prev, op), None{}, ea) : {Bool.and(Maybe.is_none(&2, String, _), Maybe.is_none(&2, String, Ops.ordered(pd, op))) == True{} : Bool}
      %Equal.sym(Maybe<&2, String>, Ops.ordered(pd, op), None{}, eb) : {Bool.and(Maybe.is_none(&2, String, None{}), Maybe.is_none(&2, String, _)) == True{} : Bool}
      {==}

def bounded_ok(+prev: Maybe<&2, Ops.Op>, +pd: Maybe<&2, Ops.Op>, m: Ops.Next) -> {ordered_more(prev, pd, Ops.next_op.bounded(prev, pd, m)) == True{} : Bool}:
  match m:
    case Ops.End{}:
      {==}
    case Ops.Bad{at, msg}:
      {==}
    case Ops.More{+op, rest, at}:
      fin_ok(prev, pd, op, rest, at, Ops.ordered(prev, op), Ops.ordered(pd, op), {==}, {==})

# The loop, building forward rather than onto a reversed accumulator.
def prepend_one(op: Ops.Op, r: Result<&2, &2, String, List<&2, Ops.Op>>) -> Result<&2, &2, String, List<&2, Ops.Op>>:
  match r:
    case Fail{msg}:
      Fail{msg}
    case Done{xs}:
      Done{op <> xs}

def prepend_rev(acc: List<&2, Ops.Op>, r: Result<&2, &2, String, List<&2, Ops.Op>>) -> Result<&2, &2, String, List<&2, Ops.Op>>:
  match r:
    case Fail{msg}:
      Fail{msg}
    case Done{xs}:
      Done{List.reverse.go(&2, Ops.Op, acc, xs)}

def collect(fuel: Nat, n: Ops.Next, +pd: Maybe<&2, Ops.Op>) -> Result<&2, &2, String, List<&2, Ops.Op>>:
  match fuel n:
    case _ Ops.End{}:
      Done{Nil{}}
    case _ Ops.Bad{at, msg}:
      Ops.fail(List<&2, Ops.Op>, at, msg)
    case 0n _:
      Fail{"the walk ran out of lines"}
    case 1n+p Ops.More{+op, rest, at}:
      +deletion = Ops.remember_delete(op, pd)
      prepend_one(op, collect(p, Ops.next_op.bounded(Some{op}, deletion, Ops.next_op(rest, at)), deletion))

def prepend_step(op: Ops.Op, acc: List<&2, Ops.Op>, r: Result<&2, &2, String, List<&2, Ops.Op>>) -> {prepend_rev(acc, prepend_one(op, r)) == prepend_rev(op <> acc, r) : Result<&2, &2, String, List<&2, Ops.Op>>}:
  match r:
    case Fail{msg}:
      {==}
    case Done{xs}:
      {==}

def ops_collect(fuel: Nat, n: Ops.Next, +acc: List<&2, Ops.Op>, +pd: Maybe<&2, Ops.Op>) -> {Ops.parse.ops(fuel, n, acc, pd) == prepend_rev(acc, collect(fuel, n, pd)) : Result<&2, &2, String, List<&2, Ops.Op>>}:
  match fuel n:
    case 0n Ops.End{}:
      {==}
    case 0n Ops.Bad{at, msg}:
      {==}
    case 0n Ops.More{op, rest, at}:
      {==}
    case 1n+p Ops.End{}:
      {==}
    case 1n+p Ops.Bad{at, msg}:
      {==}
    case 1n++p Ops.More{+op, rest, at}:
      +deletion = Ops.remember_delete(op, pd)
      +next = Ops.next_op.bounded(Some{op}, deletion, Ops.next_op(rest, at))
      %Equal.sym(Result<&2, &2, String, List<&2, Ops.Op>>, prepend_rev(acc, prepend_one(op, collect(p, next, deletion))), prepend_rev(op <> acc, collect(p, next, deletion)), prepend_step(op, acc, collect(p, next, deletion))) : {Ops.parse.ops(p, next, op <> acc, deletion) == _ : Result<&2, &2, String, List<&2, Ops.Op>>}
      ops_collect(p, next, op <> acc, deletion)

def collect_of_ops.rev(r: Result<&2, &2, String, List<&2, Ops.Op>>, -ops: List<&2, Ops.Op>, e: {prepend_rev(Nil{}, r) == Done{ops} : Result<&2, &2, String, List<&2, Ops.Op>>}) -> {r == Done{ops} : Result<&2, &2, String, List<&2, Ops.Op>>}:
  match r:
    case Fail{msg}:
      e
    case Done{xs}:
      e

def collect_of_ops(+fuel: Nat, +n: Ops.Next, +pd: Maybe<&2, Ops.Op>, -ops: List<&2, Ops.Op>, e: {Ops.parse.ops(fuel, n, Nil{}, pd) == Done{ops} : Result<&2, &2, String, List<&2, Ops.Op>>}) -> {collect(fuel, n, pd) == Done{ops} : Result<&2, &2, String, List<&2, Ops.Op>>}:
  collect_of_ops.rev(collect(fuel, n, pd), ops, Equal.trans(Result<&2, &2, String, List<&2, Ops.Op>>, prepend_rev(Nil{}, collect(fuel, n, pd)), Ops.parse.ops(fuel, n, Nil{}, pd), Done{ops}, Equal.sym(Result<&2, &2, String, List<&2, Ops.Op>>, Ops.parse.ops(fuel, n, Nil{}, pd), prepend_rev(Nil{}, collect(fuel, n, pd)), ops_collect(fuel, n, Nil{}, pd)), e))

def collect_ordered.step(+op: Ops.Op, r: Result<&2, &2, String, List<&2, Ops.Op>>, +prev: Maybe<&2, Ops.Op>, +pd: Maybe<&2, Ops.Op>, -ops: List<&2, Ops.Op>, +ok: {Bool.and(Maybe.is_none(&2, String, Ops.ordered(prev, op)), Maybe.is_none(&2, String, Ops.ordered(pd, op))) == True{} : Bool}, e: {prepend_one(op, r) == Done{ops} : Result<&2, &2, String, List<&2, Ops.Op>>}, ih: @-xs: List<&2, Ops.Op> -> {r == Done{xs} : Result<&2, &2, String, List<&2, Ops.Op>>} -> {ordered_all(xs, Some{op}, Ops.remember_delete(op, pd)) == True{} : Bool}) -> {ordered_all(ops, prev, pd) == True{} : Bool}:
  match r:
    case Fail{msg}:
      Empty.absurd({ordered_all(ops, prev, pd) == True{} : Bool}, fail_done(msg, ops, e))
    case Done{+xs}:
      %done_inj(op <> xs, ops, e) : {ordered_all(_, prev, pd) == True{} : Bool}
      and_intro(Maybe.is_none(&2, String, Ops.ordered(prev, op)), Bool.and(Maybe.is_none(&2, String, Ops.ordered(pd, op)), ordered_all(xs, Some{op}, Ops.remember_delete(op, pd))), Comp.and_left(Maybe.is_none(&2, String, Ops.ordered(prev, op)), Maybe.is_none(&2, String, Ops.ordered(pd, op)), ok), and_intro(Maybe.is_none(&2, String, Ops.ordered(pd, op)), ordered_all(xs, Some{op}, Ops.remember_delete(op, pd)), Comp.and_right(Maybe.is_none(&2, String, Ops.ordered(prev, op)), Maybe.is_none(&2, String, Ops.ordered(pd, op)), ok), ih(xs, {==})))

# Every list the loop collects is ordered from the state it started in.
def collect_ordered(fuel: Nat, n: Ops.Next, +prev: Maybe<&2, Ops.Op>, +pd: Maybe<&2, Ops.Op>, -ops: List<&2, Ops.Op>, ok: {ordered_more(prev, pd, n) == True{} : Bool}, e: {collect(fuel, n, pd) == Done{ops} : Result<&2, &2, String, List<&2, Ops.Op>>}) -> {ordered_all(ops, prev, pd) == True{} : Bool}:
  match fuel n:
    case 0n Ops.End{}:
      %done_inj(Nil{}, ops, e) : {ordered_all(_, prev, pd) == True{} : Bool}
      {==}
    case 1n+p Ops.End{}:
      %done_inj(Nil{}, ops, e) : {ordered_all(_, prev, pd) == True{} : Bool}
      {==}
    case 0n Ops.Bad{at, msg}:
      Empty.absurd({ordered_all(ops, prev, pd) == True{} : Bool}, fail_done("line " ++ Nat.show(at) ++ ": " ++ msg, ops, e))
    case 1n+p Ops.Bad{at, msg}:
      Empty.absurd({ordered_all(ops, prev, pd) == True{} : Bool}, fail_done("line " ++ Nat.show(at) ++ ": " ++ msg, ops, e))
    case 0n Ops.More{op, rest, at}:
      Empty.absurd({ordered_all(ops, prev, pd) == True{} : Bool}, fail_done("the walk ran out of lines", ops, e))
    case 1n++p Ops.More{+op, +rest, +at}:
      +deletion = Ops.remember_delete(op, pd)
      +next = Ops.next_op.bounded(Some{op}, deletion, Ops.next_op(rest, at))
      collect_ordered.step(op, collect(p, next, deletion), prev, pd, ops, ok, e, xs => h => collect_ordered(p, next, Some{op}, deletion, xs, bounded_ok(Some{op}, deletion, Ops.next_op(rest, at)), h))

# The headers
# -----------

def failing(r: Result<&2, &2, String, Ops.Doc>) -> Bool:
  match r:
    case Fail{msg}:
      True{}
    case Done{d}:
      False{}

def ddisc(r: Result<&2, &2, String, Ops.Doc>) -> Type:
  match r:
    case Fail{msg}:
      Unit
    case Done{d}:
      Empty

# A refusal is not an acceptance.
def refuse(r: Result<&2, &2, String, Ops.Doc>, -d: Ops.Doc, bad: {failing(r) == True{} : Bool}, e: {r == Done{d} : Result<&2, &2, String, Ops.Doc>}) -> Empty:
  match r:
    case Fail{msg}:
      %e : {ddisc(_) : Type}
      Unit{}
    case Done{d2}:
      Comp.false_true(bad)

# A validator that passed the document on must have been satisfied.
def pick_done(c: Bool, a: Result<&2, &2, String, Ops.Doc>, b: Result<&2, &2, String, Ops.Doc>, -d: Ops.Doc, bad: {failing(b) == True{} : Bool}, e: {Bool.pick(Result<&2, &2, String, Ops.Doc>, c, a, b) == Done{d} : Result<&2, &2, String, Ops.Doc>}) -> {a == Done{d} : Result<&2, &2, String, Ops.Doc>}:
  match c:
    case True{}:
      e
    case False{}:
      Empty.absurd({a == Done{d} : Result<&2, &2, String, Ops.Doc>}, refuse(b, d, bad, e))

def ops_of_doc(r: Result<&2, &2, String, Ops.Doc>) -> List<&2, Ops.Op>:
  match r:
    case Fail{msg}:
      Nil{}
    case Done{Ops.Doc{f, d, ops}}:
      ops

def body_ops(+f: Maybe<&2, String>, +r: Maybe<&2, String>, res: Result<&2, &2, String, List<&2, Ops.Op>>, -f2: Maybe<&2, String>, -r2: Maybe<&2, String>, -ops: List<&2, Ops.Op>, e: {Ops.parse.body(f, r, res) == Done{Ops.Doc{f2, r2, ops}} : Result<&2, &2, String, Ops.Doc>}) -> {res == Done{ops} : Result<&2, &2, String, List<&2, Ops.Op>>}:
  match res:
    case Fail{msg}:
      Empty.absurd({Fail{msg} == Done{ops} : Result<&2, &2, String, List<&2, Ops.Op>>}, refuse(Fail{msg}, Ops.Doc{f2, r2, ops}, {==}, e))
    case Done{xs}:
      match xs:
        case Nil{}:
          Empty.absurd({Done{Nil{}} == Done{ops} : Result<&2, &2, String, List<&2, Ops.Op>>}, refuse(Fail{"no operations"}, Ops.Doc{f2, r2, ops}, {==}, e))
        case +o <> +os:
          +accepted = pick_done(Ops.markers_ok(o <> os), Done{Ops.Doc{f, r, o <> os}}, Fail{"`\\ no newline` on an item that is not last"}, Ops.Doc{f2, r2, ops}, {==}, e)
          %Equal.cong(Result<&2, &2, String, Ops.Doc>, List<&2, Ops.Op>, ops_of_doc, Done{Ops.Doc{f, r, o <> os}}, Done{Ops.Doc{f2, r2, ops}}, accepted) : {Done{o <> os} == Done{_} : Result<&2, &2, String, List<&2, Ops.Op>>}
          {==}

def separator_ordered(ls: List<&2, T.Line>, +at: Nat, +f: Maybe<&2, String>, +r: Maybe<&2, String>, -f2: Maybe<&2, String>, -r2: Maybe<&2, String>, +ops: List<&2, Ops.Op>, e: {Ops.parse.separator(f, r, ls, at) == Done{Ops.Doc{f2, r2, ops}} : Result<&2, &2, String, Ops.Doc>}) -> {ordered_all(ops, None{}, None{}) == True{} : Bool}:
  match ls:
    case Nil{}:
      Empty.absurd({ordered_all(ops, None{}, None{}) == True{} : Bool}, refuse(Ops.fail(Ops.Doc, at, "missing the blank line after the headers"), Ops.Doc{f2, r2, ops}, {==}, e))
    case T.Line{t, term} <> +rest:
      match t term:
        case SNil{} True{}:
          +fuel = {1n+List.length(&2, T.Line, rest) : Nat}
          +start = Ops.next_op(rest, 1n+at)
          +n = Ops.next_op.bounded(None{}, None{}, start)
          collect_ordered(fuel, n, None{}, None{}, ops, bounded_ok(None{}, None{}, start), collect_of_ops(fuel, n, None{}, ops, body_ops(f, r, Ops.parse.ops(fuel, n, Nil{}, None{}), f2, r2, ops, e)))
        case SNil{} False{}:
          Empty.absurd({ordered_all(ops, None{}, None{}) == True{} : Bool}, refuse(Ops.fail(Ops.Doc, at, "missing the blank line after the headers"), Ops.Doc{f2, r2, ops}, {==}, e))
        case SCon{c, cs} True{}:
          Empty.absurd({ordered_all(ops, None{}, None{}) == True{} : Bool}, refuse(Ops.fail(Ops.Doc, at, "missing the blank line after the headers"), Ops.Doc{f2, r2, ops}, {==}, e))
        case SCon{c, cs} False{}:
          Empty.absurd({ordered_all(ops, None{}, None{}) == True{} : Bool}, refuse(Ops.fail(Ops.Doc, at, "missing the blank line after the headers"), Ops.Doc{f2, r2, ops}, {==}, e))

def result_ordered(f: Maybe<&2, String>, h: Ops.Headed, -f2: Maybe<&2, String>, -r2: Maybe<&2, String>, +ops: List<&2, Ops.Op>, e: {Ops.parse.result(f, h) == Done{Ops.Doc{f2, r2, ops}} : Result<&2, &2, String, Ops.Doc>}) -> {ordered_all(ops, None{}, None{}) == True{} : Bool}:
  match f h:
    case Some{x} Ops.Headed{Some{y}, rest, at}:
      Empty.absurd({ordered_all(ops, None{}, None{}) == True{} : Bool}, refuse(Ops.fail(Ops.Doc, at, "a result beside forgets"), Ops.Doc{f2, r2, ops}, {==}, e))
    case Some{+x} Ops.Headed{None{}, +rest, +at}:
      separator_ordered(rest, at, Some{x}, None{}, f2, r2, ops, pick_done(Ops.valid_digest(None{}), Ops.parse.separator(Some{x}, None{}, rest, at), Ops.fail(Ops.Doc, at, "a malformed result"), Ops.Doc{f2, r2, ops}, {==}, e))
    case None{} Ops.Headed{+result, +rest, +at}:
      separator_ordered(rest, at, None{}, result, f2, r2, ops, pick_done(Ops.valid_digest(result), Ops.parse.separator(None{}, result, rest, at), Ops.fail(Ops.Doc, at, "a malformed result"), Ops.Doc{f2, r2, ops}, {==}, e))

def forgets_ordered(h: Ops.Headed, -f2: Maybe<&2, String>, -r2: Maybe<&2, String>, +ops: List<&2, Ops.Op>, e: {Ops.parse.forgets(h) == Done{Ops.Doc{f2, r2, ops}} : Result<&2, &2, String, Ops.Doc>}) -> {ordered_all(ops, None{}, None{}) == True{} : Bool}:
  match h:
    case Ops.Headed{+forgets, +rest, +at}:
      result_ordered(forgets, Ops.header(rest, at, "result "), f2, r2, ops, pick_done(Ops.valid_digest(forgets), Ops.parse.result(forgets, Ops.header(rest, at, "result ")), Ops.fail(Ops.Doc, at, "a malformed forgets"), Ops.Doc{f2, r2, ops}, {==}, e))

def preamble_ordered(ls: List<&2, T.Line>, -f2: Maybe<&2, String>, -r2: Maybe<&2, String>, +ops: List<&2, Ops.Op>, e: {Ops.parse.preamble(ls) == Done{Ops.Doc{f2, r2, ops}} : Result<&2, &2, String, Ops.Doc>}) -> {ordered_all(ops, None{}, None{}) == True{} : Bool}:
  match ls:
    case Nil{}:
      Empty.absurd({ordered_all(ops, None{}, None{}) == True{} : Bool}, refuse(Ops.fail(Ops.Doc, 1n, "not a historica document"), Ops.Doc{f2, r2, ops}, {==}, e))
    case T.Line{+t, term} <> +rest:
      match term:
        case False{}:
          Empty.absurd({ordered_all(ops, None{}, None{}) == True{} : Bool}, refuse(Ops.fail(Ops.Doc, 1n, "not a historica document"), Ops.Doc{f2, r2, ops}, {==}, e))
        case True{}:
          forgets_ordered(Ops.header(rest, 2n, "forgets "), f2, r2, ops, pick_done(String.eq(t, "historica"), Ops.parse.forgets(Ops.header(rest, 2n, "forgets ")), Ops.fail(Ops.Doc, 1n, "not a historica document: " ++ t), Ops.Doc{f2, r2, ops}, {==}, e))

def le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# Every document the parser accepts is ordered from the start.
def parse_ordered(s: String, -f: Maybe<&2, String>, -r: Maybe<&2, String>, +ops: List<&2, Ops.Op>, e: {Ops.parse(s) == Done{Ops.Doc{f, r, ops}} : Result<&2, &2, String, Ops.Doc>}) -> {Block.ordered(ops, 0n) == True{} : Bool}:
  parser_ordered(ops, 0n, None{}, None{}, preamble_ordered(T.lines(s), f, r, ops, e), le_zero(first_at(ops, 0n)))

def main() -> Unit:
  Unit{}
