# Equality of characters and strings, decided down to the bits of a word,
# so that a comparison the parser made can be turned into an equation.
import Base
import ./text.bend as T
import ./composition_lemmas.bend as Comp

# Deciding equality
# -----------------

def eqdisc(c: Cmp) -> Type:
  match c:
    case LT{}:
      Unit
    case EQ{}:
      Empty
    case GT{}:
      Unit

def lt_eq(e: {LT{} == EQ{} : Cmp}) -> Empty:
  %e : {eqdisc(_) : Type}
  Unit{}

def gt_eq(e: {GT{} == EQ{} : Cmp}) -> Empty:
  %e : {eqdisc(_) : Type}
  Unit{}

def cmp_of_is_eq(c: Cmp, e: {Cmp.is_eq(c) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, Comp.false_true(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, Comp.false_true(e))

def bool_eq(a: Bool, b: Bool, e: {Bool.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case True{} True{}:
      {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, lt_eq(e))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, gt_eq(e))

def word_eq.fin(-p: Nat, ab: Bool, bb: Bool, at: Word(p), bt: Word(p), c: Cmp, eq: {Word.cmp(p, at, bt) == c : Cmp}, e: {Word.cmp.fin(ab, bb, c) == EQ{} : Cmp}, ih: {Word.cmp(p, at, bt) == EQ{} : Cmp} -> {at == bt : Word(p)}) -> {WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}:
  match c:
    case LT{}:
      Empty.absurd({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, lt_eq(e))
    case GT{}:
      Empty.absurd({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, gt_eq(e))
    case EQ{}:
      %Equal.sym(Bool, ab, bb, bool_eq(ab, bb, e)) : {WCon{_, at} == WCon{bb, bt} : Word.Con<p>}
      %Equal.sym(Word(p), at, bt, ih(eq)) : {WCon{bb, _} == WCon{bb, bt} : Word.Con<p>}
      {==}

def word_eq(+n: Nat, a: Word(n), b: Word(n), e: {Word.cmp(n, a, b) == EQ{} : Cmp}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{ab, +at} WCon{bb, +bt}:
          word_eq.fin(p, ab, bb, at, bt, Word.cmp(p, at, bt), {==}, e, x => word_eq(p, at, bt, x))

def u32_eq(x: U32, y: U32, e: {U32.is_eq(x, y) == True{} : Bool}) -> {x == y : U32}:
  match x y:
    case U32{+wx} U32{+wy}:
      Equal.cong(Word(32n), U32, w => U32{w}, wx, wy, word_eq(32n, wx, wy, cmp_of_is_eq(Word.cmp(32n, wx, wy), e)))

def char_eq(a: Char, b: Char, e: {Char.is_eq(a, b) == True{} : Bool}) -> {a == b : Char}:
  match a b:
    case Chr{+x} Chr{+y}:
      Equal.cong(U32, Char, w => Chr{w}, x, y, u32_eq(x, y, e))

# `T.same` is equality.
def same_eq(a: String, b: String, +e: {T.same(a, b) == True{} : Bool}) -> {a == b : String}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, yt}:
      Empty.absurd({SNil{} == SCon{y, yt} : String}, Comp.false_true(e))
    case SCon{x, xt} SNil{}:
      Empty.absurd({SCon{x, xt} == SNil{} : String}, Comp.false_true(e))
    case SCon{+x, +xt} SCon{+y, +yt}:
      %Equal.sym(Char, x, y, char_eq(x, y, Comp.and_left(Char.is_eq(x, y), T.same(xt, yt), e))) : {SCon{_, xt} == SCon{y, yt} : String}
      %Equal.sym(String, xt, yt, same_eq(xt, yt, Comp.and_right(Char.is_eq(x, y), T.same(xt, yt), e))) : {SCon{y, _} == SCon{y, yt} : String}
      {==}

def app_nil(s: String) -> {s ++ SNil{} == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %Equal.sym(String, t ++ SNil{}, t, app_nil(t)) : {SCon{h, _} == SCon{h, t} : String}
      {==}

def main() -> Unit:
  Unit{}
