# Strings compare as they are: `String.eq` is `Cmp.is_eq` of `String.order`,
# a string equals itself, and two strings `String.eq` calls equal are one
# string. Base defines the comparison bit by bit, so the proofs are
# inductions down to the bit.
import Base

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

def truedisc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def false_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : {truedisc(_) : Type}
  Unit{}

def true_false(e: {True{} == False{} : Bool}) -> Empty:
  false_true(Equal.sym(Bool, True{}, False{}, e))

# Words
# -----

def word_refl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, word_refl(p, t)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
          {==}
        case WCon{True{}, t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, word_refl(p, t)) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
          {==}

# The bit comparison is EQ only when the bits agree and the rest is EQ.
def fin_eq(c: Cmp, h: Bool, e: {Word.cmp.fin(h, h, c) == EQ{} : Cmp}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, lt_eq(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, gt_eq(e))

def fin_ft(c: Cmp, e: {Word.cmp.fin(False{}, True{}, c) == EQ{} : Cmp}) -> Empty:
  match c:
    case LT{}:
      lt_eq(e)
    case EQ{}:
      lt_eq(e)
    case GT{}:
      gt_eq(e)

def fin_tf(c: Cmp, e: {Word.cmp.fin(True{}, False{}, c) == EQ{} : Cmp}) -> Empty:
  match c:
    case LT{}:
      lt_eq(e)
    case EQ{}:
      gt_eq(e)
    case GT{}:
      gt_eq(e)

# EQ at every bit is the same word.
def word_eq(n: Nat, a: Word(n), b: Word(n), e: {Word.cmp(n, a, b) == EQ{} : Cmp}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n++p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          %word_eq(p, at, bt, fin_eq(Word.cmp(p, at, bt), False{}, e)) : {WCon{False{}, at} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +at} WCon{True{}, +bt}:
          %word_eq(p, at, bt, fin_eq(Word.cmp(p, at, bt), True{}, e)) : {WCon{True{}, at} == WCon{True{}, _} : Word(1n+p)}
          {==}
        case WCon{False{}, at} WCon{True{}, bt}:
          Empty.absurd({WCon{False{}, at} == WCon{True{}, bt} : Word(1n+p)}, fin_ft(Word.cmp(p, at, bt), e))
        case WCon{True{}, at} WCon{False{}, bt}:
          Empty.absurd({WCon{True{}, at} == WCon{False{}, bt} : Word(1n+p)}, fin_tf(Word.cmp(p, at, bt), e))

# Strings
# -------

# The comparison hands the strings back beside the verdict; only the
# verdict is read.
def rec_order(h1: Char, h2: Char, rr: (String & String) & Cmp) -> {String.order.fin(String.cmp.rec(h1, h2, rr)) == String.order.fin(rr) : Cmp}:
  match rr:
    case (ab, c):
      match ab:
        case (a2, b2):
          {==}

def eq_order.of(rr: (String & String) & Cmp) -> {String.eq.fin(rr) == Cmp.is_eq(String.order.fin(rr)) : Bool}:
  match rr:
    case (ab, c):
      match ab:
        case (a2, b2):
          {==}

def eq_order(a: String, b: String) -> {String.eq(a, b) == Cmp.is_eq(String.order(a, b)) : Bool}:
  eq_order.of(String.cmp(a, b))

def char_refl(h: Char) -> {Char.cmp(h, h) == ((h, h), EQ{}) : (Char & Char) & Cmp}:
  match h:
    case Chr{U32{w}}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, word_refl(32n, w)) : {((Chr{U32{w}}, Chr{U32{w}}), _) == ((Chr{U32{w}}, Chr{U32{w}}), EQ{}) : (Char & Char) & Cmp}
      {==}

def order_refl(s: String) -> {String.order(s, s) == EQ{} : Cmp}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym((Char & Char) & Cmp, Char.cmp(h, h), ((h, h), EQ{}), char_refl(h)) : {String.order.fin(String.cmp.fin(t, t, _)) == EQ{} : Cmp}
      %Equal.sym(Cmp, String.order.fin(String.cmp.rec(h, h, String.cmp(t, t))), String.order.fin(String.cmp(t, t)), rec_order(h, h, String.cmp(t, t))) : {_ == EQ{} : Cmp}
      order_refl(t)

def verdict(rr: (Char & Char) & Cmp) -> Cmp:
  match rr:
    case (ab, c):
      c

def char_eq(x: Char, y: Char, e: {Char.cmp(x, y) == ((x, y), EQ{}) : (Char & Char) & Cmp}) -> {x == y : Char}:
  match x y:
    case Chr{U32{+w1}} Chr{U32{+w2}}:
      %word_eq(32n, w1, w2, Equal.cong((Char & Char) & Cmp, Cmp, rr => verdict(rr), ((Chr{U32{w1}}, Chr{U32{w2}}), Word.cmp(32n, w1, w2)), ((Chr{U32{w1}}, Chr{U32{w2}}), EQ{}), e)) : {Chr{U32{w1}} == Chr{U32{_}} : Char}
      {==}

def rec_eq(h1: Char, h2: Char, t1: String, t2: String, e: {String.order.fin(String.cmp.rec(h1, h2, String.cmp(t1, t2))) == EQ{} : Cmp}) -> {String.order(t1, t2) == EQ{} : Cmp}:
  %rec_order(h1, h2, String.cmp(t1, t2)) : {_ == EQ{} : Cmp}
  e

def order_eq.fin(c: Cmp, +w1: Word(32n), +w2: Word(32n), +t1: String, +t2: String, ew: {Word.cmp(32n, w1, w2) == c : Cmp}, e: {String.order.fin(String.cmp.fin(t1, t2, ((Chr{U32{w1}}, Chr{U32{w2}}), c))) == EQ{} : Cmp}, ih: {String.order(t1, t2) == EQ{} : Cmp} -> {t1 == t2 : String}) -> {SCon{Chr{U32{w1}}, t1} == SCon{Chr{U32{w2}}, t2} : String}:
  match c:
    case LT{}:
      Empty.absurd({SCon{Chr{U32{w1}}, t1} == SCon{Chr{U32{w2}}, t2} : String}, lt_eq(e))
    case GT{}:
      Empty.absurd({SCon{Chr{U32{w1}}, t1} == SCon{Chr{U32{w2}}, t2} : String}, gt_eq(e))
    case EQ{}:
      %word_eq(32n, w1, w2, ew) : {SCon{Chr{U32{w1}}, t1} == SCon{Chr{U32{_}}, t2} : String}
      %ih(rec_eq(Chr{U32{w1}}, Chr{U32{w2}}, t1, t2, e)) : {SCon{Chr{U32{w1}}, t1} == SCon{Chr{U32{w1}}, _} : String}
      {==}

# Two strings the comparison calls EQ are one string.
def order_eq(a: String, b: String, e: {String.order(a, b) == EQ{} : Cmp}) -> {a == b : String}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      Empty.absurd({SNil{} == SCon{h, t} : String}, lt_eq(e))
    case SCon{h, t} SNil{}:
      Empty.absurd({SCon{h, t} == SNil{} : String}, gt_eq(e))
    case SCon{Chr{U32{+w1}}, +t1} SCon{Chr{U32{+w2}}, +t2}:
      order_eq.fin(Word.cmp(32n, w1, w2), w1, w2, t1, t2, {==}, e, x => order_eq(t1, t2, x))

def is_eq_true(c: Cmp, e: {Cmp.is_eq(c) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, false_true(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, false_true(e))

def eq_true.of(+a: String, +b: String, e: {String.eq(a, b) == True{} : Bool}) -> {Cmp.is_eq(String.order(a, b)) == True{} : Bool}:
  %eq_order(a, b) : {_ == True{} : Bool}
  e

# Two strings `String.eq` calls equal are one string.
def eq_true(+a: String, +b: String, e: {String.eq(a, b) == True{} : Bool}) -> {a == b : String}:
  order_eq(a, b, is_eq_true(String.order(a, b), eq_true.of(a, b, e)))

def eq_refl(+a: String) -> {String.eq(a, a) == True{} : Bool}:
  %Equal.sym(Bool, String.eq(a, a), Cmp.is_eq(String.order(a, a)), eq_order(a, a)) : {_ == True{} : Bool}
  %Equal.sym(Cmp, String.order(a, a), EQ{}, order_refl(a)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

# A string ordered strictly against another is not it.
def lt_ne(+a: String, e: {String.order(a, a) == LT{} : Cmp}) -> Empty:
  lt_eq(Equal.trans(Cmp, LT{}, String.order(a, a), EQ{}, Equal.sym(Cmp, String.order(a, a), LT{}, e), order_refl(a)))

def gt_ne(+a: String, e: {String.order(a, a) == GT{} : Cmp}) -> Empty:
  gt_eq(Equal.trans(Cmp, GT{}, String.order(a, a), EQ{}, Equal.sym(Cmp, String.order(a, a), GT{}, e), order_refl(a)))

def main() -> IO(Unit):
  IO.print("ok")
