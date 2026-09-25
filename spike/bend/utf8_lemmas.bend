# The round trip the store's reading depends on: a string of Unicode
# scalar values, encoded as UTF-8 as the port writes it, is read back as
# text — as `read_to_string` reads it — as itself: `invalid` finds nothing
# wrong with the bytes, and `decode` gives back every character. Proven
# down to the bits of a character: a code point is taken apart into its
# thirty-two bits, the width `encode` gives it says which of them are
# clear, each bit `decode` puts back is shown to be the one it came from —
# one bit at a time, so that no case split multiplies another — and each
# byte is shown to be one the validator takes, the lead bytes by the few
# bits that decide them and the rest whatever bits they carry.
import Base
import ./utf8.bend as Utf8
import ./store.bend as Store

# A Unicode scalar value: at most U+10FFFF, and not a surrogate.
def scalar(+x: U32) -> Bool:
  Bool.and(U32.is_le(x, 1114111), Bool.or(U32.is_lt(x, 55296), U32.is_gt(x, 57343)))

def scalars(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{+x}, t}:
      Bool.and(scalar(x), scalars(t))

# Booleans and comparisons
# ------------------------

def disc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def false_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : {disc(_) : Type}
  Unit{}

def and_left(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_true(e))

def and_right(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, false_true(e))

def le_succ(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, false_true(e))
    case 1n+p 1n+q:
      le_succ(p, q, e)

# What `chr` asks of a code point, answered by a scalar value: none of
# its comparisons is taken apart, only what one says of the other.
def cond.low(b: Cmp, d: Cmp, h: {Bool.or(Cmp.is_lt(b), Cmp.is_gt(d)) == True{} : Bool}) -> {Bool.and(Cmp.is_ge(b), Cmp.is_le(d)) == False{} : Bool}:
  match b d:
    case LT{} _:
      {==}
    case EQ{} GT{}:
      {==}
    case GT{} GT{}:
      {==}
    case EQ{} LT{}:
      Empty.absurd({True{} == False{} : Bool}, false_true(h))
    case EQ{} EQ{}:
      Empty.absurd({True{} == False{} : Bool}, false_true(h))
    case GT{} LT{}:
      Empty.absurd({True{} == False{} : Bool}, false_true(h))
    case GT{} EQ{}:
      Empty.absurd({True{} == False{} : Bool}, false_true(h))

def cond.of(a: Cmp, b: Cmp, d: Cmp, h: {Bool.and(Cmp.is_le(a), Bool.or(Cmp.is_lt(b), Cmp.is_gt(d))) == True{} : Bool}) -> {Bool.or(Cmp.is_gt(a), Bool.and(Cmp.is_ge(b), Cmp.is_le(d))) == False{} : Bool}:
  match a:
    case LT{}:
      cond.low(b, d, h)
    case EQ{}:
      cond.low(b, d, h)
    case GT{}:
      Empty.absurd({True{} == False{} : Bool}, false_true(h))

# A scalar value is the character `chr` makes of it.
def chr_ok(+x: U32, h: {scalar(x) == True{} : Bool}) -> {Utf8.chr(x) == Chr{x} : Char}:
  +c = cond.of(U32.cmp(x, 1114111), U32.cmp(x, 55296), U32.cmp(x, 57343), h)
  %Equal.sym(Bool, Bool.or(U32.is_gt(x, 1114111), Bool.and(U32.is_ge(x, 55296), U32.is_le(x, 57343))), False{}, c) : {Utf8.chr.of(x, _) == Chr{x} : Char}
  {==}

# A word is never less than the word of no bits set.
def nlt0.fin(r: Cmp, b: Bool, e: {Cmp.is_lt(r) == False{} : Bool}) -> {Cmp.is_lt(Word.cmp.fin(b, False{}, r)) == False{} : Bool}:
  match r b:
    case LT{} _:
      Empty.absurd({Cmp.is_lt(Word.cmp.fin(b, False{}, LT{})) == False{} : Bool}, false_true(Equal.sym(Bool, True{}, False{}, e)))
    case EQ{} False{}:
      {==}
    case EQ{} True{}:
      {==}
    case GT{} _:
      {==}

def nlt0(+n: Nat, w: Word(n)) -> {Cmp.is_lt(Word.cmp(n, w, Word.zero(n))) == False{} : Bool}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, +t}:
          nlt0.fin(Word.cmp(p, t, Word.zero(p)), b, nlt0(p, t))

# Bits
# ----

# A code point from its bits, the least significant first.
def mk(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, +b28: Bool, +b29: Bool, +b30: Bool, +b31: Bool) -> U32:
  U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

def wbit(n: Nat, w: Word(n), k: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      match w k:
        case WCon{h, t} 0n:
          h
        case WCon{h, t} 1n+j:
          wbit(p, t, j)

# The bit at `k` of a code point.
def bit(x: U32, k: Nat) -> Bool:
  match x:
    case U32{v}:
      wbit(32n, v, k)

# Two code points are one where every bit of one is the other's.
def ext32(x: U32, y: U32, e0: {bit(x, 0n) == bit(y, 0n) : Bool}, e1: {bit(x, 1n) == bit(y, 1n) : Bool}, e2: {bit(x, 2n) == bit(y, 2n) : Bool}, e3: {bit(x, 3n) == bit(y, 3n) : Bool}, e4: {bit(x, 4n) == bit(y, 4n) : Bool}, e5: {bit(x, 5n) == bit(y, 5n) : Bool}, e6: {bit(x, 6n) == bit(y, 6n) : Bool}, e7: {bit(x, 7n) == bit(y, 7n) : Bool}, e8: {bit(x, 8n) == bit(y, 8n) : Bool}, e9: {bit(x, 9n) == bit(y, 9n) : Bool}, e10: {bit(x, 10n) == bit(y, 10n) : Bool}, e11: {bit(x, 11n) == bit(y, 11n) : Bool}, e12: {bit(x, 12n) == bit(y, 12n) : Bool}, e13: {bit(x, 13n) == bit(y, 13n) : Bool}, e14: {bit(x, 14n) == bit(y, 14n) : Bool}, e15: {bit(x, 15n) == bit(y, 15n) : Bool}, e16: {bit(x, 16n) == bit(y, 16n) : Bool}, e17: {bit(x, 17n) == bit(y, 17n) : Bool}, e18: {bit(x, 18n) == bit(y, 18n) : Bool}, e19: {bit(x, 19n) == bit(y, 19n) : Bool}, e20: {bit(x, 20n) == bit(y, 20n) : Bool}, e21: {bit(x, 21n) == bit(y, 21n) : Bool}, e22: {bit(x, 22n) == bit(y, 22n) : Bool}, e23: {bit(x, 23n) == bit(y, 23n) : Bool}, e24: {bit(x, 24n) == bit(y, 24n) : Bool}, e25: {bit(x, 25n) == bit(y, 25n) : Bool}, e26: {bit(x, 26n) == bit(y, 26n) : Bool}, e27: {bit(x, 27n) == bit(y, 27n) : Bool}, e28: {bit(x, 28n) == bit(y, 28n) : Bool}, e29: {bit(x, 29n) == bit(y, 29n) : Bool}, e30: {bit(x, 30n) == bit(y, 30n) : Bool}, e31: {bit(x, 31n) == bit(y, 31n) : Bool}) -> {x == y : U32}:
  match x y:
    case U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{y8, WCon{y9, WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %Equal.sym(Bool, x0, y0, e0) : {mk(_, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x1, y1, e1) : {mk(y0, _, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x2, y2, e2) : {mk(y0, y1, _, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x3, y3, e3) : {mk(y0, y1, y2, _, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x4, y4, e4) : {mk(y0, y1, y2, y3, _, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x5, y5, e5) : {mk(y0, y1, y2, y3, y4, _, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x6, y6, e6) : {mk(y0, y1, y2, y3, y4, y5, _, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x7, y7, e7) : {mk(y0, y1, y2, y3, y4, y5, y6, _, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x8, y8, e8) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, _, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x9, y9, e9) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, _, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x10, y10, e10) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, _, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x11, y11, e11) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, _, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x12, y12, e12) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, _, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x13, y13, e13) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, _, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x14, y14, e14) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, _, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x15, y15, e15) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, _, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x16, y16, e16) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, _, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x17, y17, e17) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, _, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x18, y18, e18) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, _, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x19, y19, e19) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, _, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x20, y20, e20) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, _, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x21, y21, e21) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, _, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x22, y22, e22) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, _, x23, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x23, y23, e23) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, _, x24, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x24, y24, e24) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, _, x25, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x25, y25, e25) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, _, x26, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x26, y26, e26) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, _, x27, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x27, y27, e27) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, _, x28, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x28, y28, e28) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, _, x29, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x29, y29, e29) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, _, x30, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x30, y30, e30) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, _, x31) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      %Equal.sym(Bool, x31, y31, e31) : {mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, _) == mk(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31) : U32}
      {==}

# What `decode` rebuilds from the bytes `encode` writes for a code point of
# each width: the payload of the lead byte, then six bits a continuation.
def x2(+m: U32) -> U32:
  Utf8.cont(((192 .|. (m >> 6n) : U32) .&. 31 : U32), (128 .|. (m .&. 63) : U32))

def x3(+m: U32) -> U32:
  Utf8.cont(Utf8.cont(((224 .|. (m >> 12n) : U32) .&. 15 : U32), (128 .|. ((m >> 6n) .&. 63) : U32)), (128 .|. (m .&. 63) : U32))

def x4(+m: U32) -> U32:
  Utf8.cont(Utf8.cont(Utf8.cont(((240 .|. (m >> 18n) : U32) .&. 7 : U32), (128 .|. ((m >> 12n) .&. 63) : U32)), (128 .|. ((m >> 6n) .&. 63) : U32)), (128 .|. (m .&. 63) : U32))

# The two-byte code points: 11 bits, the rest clear.
def two.b0(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool) -> {bit(x2(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 0n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 0n) : Bool}:
  match b0:
    case True{}:
      {==}
    case False{}:
      {==}

def two.b1(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool) -> {bit(x2(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 1n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 1n) : Bool}:
  match b1:
    case True{}:
      {==}
    case False{}:
      {==}

def two.b2(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool) -> {bit(x2(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 2n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2n) : Bool}:
  match b2:
    case True{}:
      {==}
    case False{}:
      {==}

def two.b3(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool) -> {bit(x2(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 3n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 3n) : Bool}:
  match b3:
    case True{}:
      {==}
    case False{}:
      {==}

def two.b4(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool) -> {bit(x2(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 4n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 4n) : Bool}:
  match b4:
    case True{}:
      {==}
    case False{}:
      {==}

def two.b5(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool) -> {bit(x2(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 5n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 5n) : Bool}:
  match b5:
    case True{}:
      {==}
    case False{}:
      {==}

def two.b6(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool) -> {bit(x2(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 6n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 6n) : Bool}:
  match b6:
    case True{}:
      {==}
    case False{}:
      {==}

def two.b7(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool) -> {bit(x2(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 7n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 7n) : Bool}:
  match b7:
    case True{}:
      {==}
    case False{}:
      {==}

def two.b8(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool) -> {bit(x2(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 8n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 8n) : Bool}:
  match b8:
    case True{}:
      {==}
    case False{}:
      {==}

def two.b9(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool) -> {bit(x2(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 9n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 9n) : Bool}:
  match b9:
    case True{}:
      {==}
    case False{}:
      {==}

def two.b10(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool) -> {bit(x2(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 10n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 10n) : Bool}:
  match b10:
    case True{}:
      {==}
    case False{}:
      {==}

def two.bits(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool) -> {x2(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) : U32}:
  ext32(x2(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), two.b0(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10), two.b1(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10), two.b2(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10), two.b3(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10), two.b4(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10), two.b5(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10), two.b6(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10), two.b7(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10), two.b8(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10), two.b9(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10), two.b10(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10), {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# The three-byte code points: 16 bits, the rest clear.
def three.b0(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> {bit(x3(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 0n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 0n) : Bool}:
  match b0:
    case True{}:
      {==}
    case False{}:
      {==}

def three.b1(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> {bit(x3(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 1n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 1n) : Bool}:
  match b1:
    case True{}:
      {==}
    case False{}:
      {==}

def three.b2(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> {bit(x3(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 2n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2n) : Bool}:
  match b2:
    case True{}:
      {==}
    case False{}:
      {==}

def three.b3(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> {bit(x3(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 3n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 3n) : Bool}:
  match b3:
    case True{}:
      {==}
    case False{}:
      {==}

def three.b4(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> {bit(x3(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 4n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 4n) : Bool}:
  match b4:
    case True{}:
      {==}
    case False{}:
      {==}

def three.b5(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> {bit(x3(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 5n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 5n) : Bool}:
  match b5:
    case True{}:
      {==}
    case False{}:
      {==}

def three.b6(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> {bit(x3(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 6n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 6n) : Bool}:
  match b6:
    case True{}:
      {==}
    case False{}:
      {==}

def three.b7(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> {bit(x3(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 7n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 7n) : Bool}:
  match b7:
    case True{}:
      {==}
    case False{}:
      {==}

def three.b8(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> {bit(x3(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 8n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 8n) : Bool}:
  match b8:
    case True{}:
      {==}
    case False{}:
      {==}

def three.b9(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> {bit(x3(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 9n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 9n) : Bool}:
  match b9:
    case True{}:
      {==}
    case False{}:
      {==}

def three.b10(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> {bit(x3(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 10n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 10n) : Bool}:
  match b10:
    case True{}:
      {==}
    case False{}:
      {==}

def three.b11(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> {bit(x3(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 11n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 11n) : Bool}:
  match b11:
    case True{}:
      {==}
    case False{}:
      {==}

def three.b12(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> {bit(x3(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 12n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 12n) : Bool}:
  match b12:
    case True{}:
      {==}
    case False{}:
      {==}

def three.b13(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> {bit(x3(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 13n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 13n) : Bool}:
  match b13:
    case True{}:
      {==}
    case False{}:
      {==}

def three.b14(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> {bit(x3(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 14n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 14n) : Bool}:
  match b14:
    case True{}:
      {==}
    case False{}:
      {==}

def three.b15(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> {bit(x3(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 15n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 15n) : Bool}:
  match b15:
    case True{}:
      {==}
    case False{}:
      {==}

def three.bits(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> {x3(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) : U32}:
  ext32(x3(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), three.b0(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15), three.b1(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15), three.b2(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15), three.b3(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15), three.b4(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15), three.b5(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15), three.b6(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15), three.b7(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15), three.b8(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15), three.b9(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15), three.b10(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15), three.b11(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15), three.b12(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15), three.b13(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15), three.b14(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15), three.b15(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15), {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# The four-byte code points: 21 bits, the rest clear.
def four.b0(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> {bit(x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 0n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 0n) : Bool}:
  match b0:
    case True{}:
      {==}
    case False{}:
      {==}

def four.b1(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> {bit(x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 1n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 1n) : Bool}:
  match b1:
    case True{}:
      {==}
    case False{}:
      {==}

def four.b2(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> {bit(x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 2n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2n) : Bool}:
  match b2:
    case True{}:
      {==}
    case False{}:
      {==}

def four.b3(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> {bit(x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 3n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 3n) : Bool}:
  match b3:
    case True{}:
      {==}
    case False{}:
      {==}

def four.b4(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> {bit(x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 4n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 4n) : Bool}:
  match b4:
    case True{}:
      {==}
    case False{}:
      {==}

def four.b5(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> {bit(x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 5n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 5n) : Bool}:
  match b5:
    case True{}:
      {==}
    case False{}:
      {==}

def four.b6(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> {bit(x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 6n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 6n) : Bool}:
  match b6:
    case True{}:
      {==}
    case False{}:
      {==}

def four.b7(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> {bit(x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 7n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 7n) : Bool}:
  match b7:
    case True{}:
      {==}
    case False{}:
      {==}

def four.b8(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> {bit(x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 8n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 8n) : Bool}:
  match b8:
    case True{}:
      {==}
    case False{}:
      {==}

def four.b9(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> {bit(x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 9n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 9n) : Bool}:
  match b9:
    case True{}:
      {==}
    case False{}:
      {==}

def four.b10(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> {bit(x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 10n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 10n) : Bool}:
  match b10:
    case True{}:
      {==}
    case False{}:
      {==}

def four.b11(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> {bit(x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 11n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 11n) : Bool}:
  match b11:
    case True{}:
      {==}
    case False{}:
      {==}

def four.b12(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> {bit(x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 12n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 12n) : Bool}:
  match b12:
    case True{}:
      {==}
    case False{}:
      {==}

def four.b13(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> {bit(x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 13n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 13n) : Bool}:
  match b13:
    case True{}:
      {==}
    case False{}:
      {==}

def four.b14(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> {bit(x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 14n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 14n) : Bool}:
  match b14:
    case True{}:
      {==}
    case False{}:
      {==}

def four.b15(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> {bit(x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 15n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 15n) : Bool}:
  match b15:
    case True{}:
      {==}
    case False{}:
      {==}

def four.b16(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> {bit(x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 16n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 16n) : Bool}:
  match b16:
    case True{}:
      {==}
    case False{}:
      {==}

def four.b17(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> {bit(x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 17n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 17n) : Bool}:
  match b17:
    case True{}:
      {==}
    case False{}:
      {==}

def four.b18(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> {bit(x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 18n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 18n) : Bool}:
  match b18:
    case True{}:
      {==}
    case False{}:
      {==}

def four.b19(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> {bit(x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 19n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 19n) : Bool}:
  match b19:
    case True{}:
      {==}
    case False{}:
      {==}

def four.b20(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> {bit(x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), 20n) == bit(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 20n) : Bool}:
  match b20:
    case True{}:
      {==}
    case False{}:
      {==}

def four.bits(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> {x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) : U32}:
  ext32(x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), four.b0(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20), four.b1(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20), four.b2(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20), four.b3(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20), four.b4(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20), four.b5(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20), four.b6(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20), four.b7(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20), four.b8(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20), four.b9(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20), four.b10(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20), four.b11(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20), four.b12(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20), four.b13(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20), four.b14(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20), four.b15(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20), four.b16(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20), four.b17(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20), four.b18(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20), four.b19(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20), four.b20(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20), {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# A two-byte code point decodes from its bytes as itself.
def two.leaf(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +rest: List<&2, U32>, t3: Bool) -> {Utf8.decode.step(Utf8.encode.char(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), rest, False{}, True{}, t3)) == Some{Utf8.Step{Chr{mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})}, rest}} : Maybe<&2, Utf8.Step>}:
  %Equal.sym(U32, x2(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), two.bits(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10)) : {Some{Utf8.Step{Chr{_}, rest}} == Some{Utf8.Step{Chr{mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})}, rest}} : Maybe<&2, Utf8.Step>}
  {==}

# A three-byte code point decodes from its bytes as itself.
def three.leaf(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +rest: List<&2, U32>, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> {Utf8.decode.step(Utf8.encode.char(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), rest, False{}, False{}, True{})) == Some{Utf8.Step{Chr{mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})}, rest}} : Maybe<&2, Utf8.Step>}:
  %Equal.sym(Bool, U32.is_lt((224 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) : U32), 224), False{}, nlt0(4n, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WNil{}}}}})) : {Some{Utf8.decode.lead((224 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32) <> (128 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) .&. 63) : U32) <> rest, U32.is_lt((224 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) : U32), 128), _, U32.is_lt((224 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) : U32), 240))} == Some{Utf8.Step{Chr{mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})}, rest}} : Maybe<&2, Utf8.Step>}
  %Equal.sym(U32, x3(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), three.bits(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15)) : {Some{Utf8.Step{Utf8.chr(_), rest}} == Some{Utf8.Step{Chr{mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})}, rest}} : Maybe<&2, Utf8.Step>}
  %Equal.sym(Char, Utf8.chr(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), Chr{mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})}, chr_ok(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), h)) : {Some{Utf8.Step{_, rest}} == Some{Utf8.Step{Chr{mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})}, rest}} : Maybe<&2, Utf8.Step>}
  {==}

# A four-byte code point decodes from its bytes as itself.
def four.leaf(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +rest: List<&2, U32>, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> {Utf8.decode.step(Utf8.encode.char(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), rest, False{}, False{}, False{})) == Some{Utf8.Step{Chr{mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})}, rest}} : Maybe<&2, Utf8.Step>}:
  %Equal.sym(Bool, U32.is_lt((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), 240), False{}, nlt0(3n, WCon{b18, WCon{b19, WCon{b20, WNil{}}}})) : {Some{Utf8.decode.lead((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32) <> (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32) <> (128 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) .&. 63) : U32) <> rest, U32.is_lt((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), 128), U32.is_lt((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), 224), _)} == Some{Utf8.Step{Chr{mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})}, rest}} : Maybe<&2, Utf8.Step>}
  %Equal.sym(U32, x4(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), four.bits(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20)) : {Some{Utf8.Step{Utf8.chr(_), rest}} == Some{Utf8.Step{Chr{mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})}, rest}} : Maybe<&2, Utf8.Step>}
  %Equal.sym(Char, Utf8.chr(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), Chr{mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})}, chr_ok(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), h)) : {Some{Utf8.Step{_, rest}} == Some{Utf8.Step{Chr{mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})}, rest}} : Maybe<&2, Utf8.Step>}
  {==}

# A code point `encode` writes in 2 bytes has no bit set above 10: what is
# to be shown of it is shown of one whose bits above are clear.
def two.t11(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b11:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(Equal.trans(Bool, False{}, U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048), True{}, Equal.sym(Bool, U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048), False{}, nlt0(11n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}})), eb)))
    case False{}:
      leaf(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, ea)

def two.t12(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b12:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      two.t11(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, P, leaf, ea, eb)

def two.t13(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b13:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      two.t12(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, P, leaf, ea, eb)

def two.t14(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b14:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      two.t13(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, P, leaf, ea, eb)

def two.t15(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b15:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      two.t14(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, P, leaf, ea, eb)

def two.t16(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b16:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      two.t15(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, P, leaf, ea, eb)

def two.t17(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b17:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      two.t16(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, P, leaf, ea, eb)

def two.t18(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b18:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      two.t17(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, P, leaf, ea, eb)

def two.t19(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b19:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      two.t18(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, P, leaf, ea, eb)

def two.t20(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b20:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      two.t19(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, P, leaf, ea, eb)

def two.t21(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b21:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      two.t20(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, P, leaf, ea, eb)

def two.t22(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b22:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      two.t21(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, P, leaf, ea, eb)

def two.t23(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b23:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      two.t22(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, P, leaf, ea, eb)

def two.t24(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b24:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      two.t23(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, P, leaf, ea, eb)

def two.t25(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, False{}, False{}, False{}, False{}, False{}, False{})):
  match b25:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, True{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      two.t24(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, P, leaf, ea, eb)

def two.t26(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, False{}, False{}, False{}, False{}, False{}), 2048) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, False{}, False{}, False{}, False{}, False{})):
  match b26:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, True{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      two.t25(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, P, leaf, ea, eb)

def two.t27(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, False{}, False{}, False{}, False{}), 128) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, False{}, False{}, False{}, False{}), 2048) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, False{}, False{}, False{}, False{})):
  match b27:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, True{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      two.t26(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, P, leaf, ea, eb)

def two.t28(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, +b28: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, False{}, False{}, False{}), 128) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, False{}, False{}, False{}), 2048) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, False{}, False{}, False{})):
  match b28:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, True{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      two.t27(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, P, leaf, ea, eb)

def two.t29(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, +b28: Bool, +b29: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, False{}, False{}), 128) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, False{}, False{}), 2048) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, False{}, False{})):
  match b29:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, True{}, False{}, False{})), false_true(eb))
    case False{}:
      two.t28(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, P, leaf, ea, eb)

def two.t30(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, +b28: Bool, +b29: Bool, +b30: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, False{}), 128) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, False{}), 2048) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, False{})):
  match b30:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, True{}, False{})), false_true(eb))
    case False{}:
      two.t29(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, P, leaf, ea, eb)

def two.t31(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, +b28: Bool, +b29: Bool, +b30: Bool, +b31: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31), 128) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31), 2048) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31)):
  match b31:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, True{})), false_true(eb))
    case False{}:
      two.t30(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, P, leaf, ea, eb)

def two.tree(+c: U32, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(c, 128) == False{} : Bool}, eb: {U32.is_lt(c, 2048) == True{} : Bool}) -> P(c):
  match c:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      two.t31(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, P, leaf, ea, eb)

# A code point `encode` writes in 3 bytes has no bit set above 15: what is
# to be shown of it is shown of one whose bits above are clear.
def three.t16(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == True{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b16:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(Equal.trans(Bool, False{}, U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536), True{}, Equal.sym(Bool, U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536), False{}, nlt0(16n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WNil{}}}}}}}}}}}}}}}}})), eb)))
    case False{}:
      leaf(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, ea, h)

def three.t17(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == True{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b17:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      three.t16(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, P, leaf, ea, eb, h)

def three.t18(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == True{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b18:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      three.t17(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, P, leaf, ea, eb, h)

def three.t19(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == True{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b19:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      three.t18(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, P, leaf, ea, eb, h)

def three.t20(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == True{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b20:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      three.t19(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, P, leaf, ea, eb, h)

def three.t21(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == True{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b21:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      three.t20(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, P, leaf, ea, eb, h)

def three.t22(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == True{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b22:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      three.t21(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, P, leaf, ea, eb, h)

def three.t23(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == True{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b23:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      three.t22(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, P, leaf, ea, eb, h)

def three.t24(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == True{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b24:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      three.t23(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, P, leaf, ea, eb, h)

def three.t25(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == True{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, False{}, False{}, False{}, False{}, False{}, False{})):
  match b25:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, True{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      three.t24(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, P, leaf, ea, eb, h)

def three.t26(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, False{}, False{}, False{}, False{}, False{}), 65536) == True{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, False{}, False{}, False{}, False{}, False{})):
  match b26:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, True{}, False{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      three.t25(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, P, leaf, ea, eb, h)

def three.t27(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, False{}, False{}, False{}, False{}), 2048) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, False{}, False{}, False{}, False{}), 65536) == True{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, False{}, False{}, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, False{}, False{}, False{}, False{})):
  match b27:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, True{}, False{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      three.t26(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, P, leaf, ea, eb, h)

def three.t28(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, +b28: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, False{}, False{}, False{}), 2048) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, False{}, False{}, False{}), 65536) == True{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, False{}, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, False{}, False{}, False{})):
  match b28:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, True{}, False{}, False{}, False{})), false_true(eb))
    case False{}:
      three.t27(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, P, leaf, ea, eb, h)

def three.t29(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, +b28: Bool, +b29: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, False{}, False{}), 2048) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, False{}, False{}), 65536) == True{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, False{}, False{})):
  match b29:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, True{}, False{}, False{})), false_true(eb))
    case False{}:
      three.t28(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, P, leaf, ea, eb, h)

def three.t30(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, +b28: Bool, +b29: Bool, +b30: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, False{}), 2048) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, False{}), 65536) == True{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, False{})):
  match b30:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, True{}, False{})), false_true(eb))
    case False{}:
      three.t29(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, P, leaf, ea, eb, h)

def three.t31(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, +b28: Bool, +b29: Bool, +b30: Bool, +b31: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31), 2048) == False{} : Bool}, eb: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31), 65536) == True{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31)) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31)):
  match b31:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, True{})), false_true(eb))
    case False{}:
      three.t30(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, P, leaf, ea, eb, h)

def three.tree(+c: U32, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(c, 2048) == False{} : Bool}, eb: {U32.is_lt(c, 65536) == True{} : Bool}, h: {scalar(c) == True{} : Bool}) -> P(c):
  match c:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      three.t31(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, P, leaf, ea, eb, h)

# A code point `encode` writes in 4 bytes has no bit set above 20: what is
# to be shown of it is shown of one whose bits above are clear.
def four.t21(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> @x16: Bool -> @x17: Bool -> @x18: Bool -> @x19: Bool -> @x20: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == False{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b21:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(h))
    case False{}:
      leaf(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, ea, h)

def four.t22(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> @x16: Bool -> @x17: Bool -> @x18: Bool -> @x19: Bool -> @x20: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == False{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b22:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(h))
    case False{}:
      four.t21(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, P, leaf, ea, h)

def four.t23(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> @x16: Bool -> @x17: Bool -> @x18: Bool -> @x19: Bool -> @x20: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == False{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b23:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(h))
    case False{}:
      four.t22(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, P, leaf, ea, h)

def four.t24(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> @x16: Bool -> @x17: Bool -> @x18: Bool -> @x19: Bool -> @x20: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == False{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, False{}, False{}, False{}, False{}, False{}, False{}, False{})):
  match b24:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(h))
    case False{}:
      four.t23(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, P, leaf, ea, h)

def four.t25(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> @x16: Bool -> @x17: Bool -> @x18: Bool -> @x19: Bool -> @x20: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == False{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, False{}, False{}, False{}, False{}, False{}, False{})):
  match b25:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, True{}, False{}, False{}, False{}, False{}, False{}, False{})), false_true(h))
    case False{}:
      four.t24(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, P, leaf, ea, h)

def four.t26(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> @x16: Bool -> @x17: Bool -> @x18: Bool -> @x19: Bool -> @x20: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, False{}, False{}, False{}, False{}, False{}), 65536) == False{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, False{}, False{}, False{}, False{}, False{})):
  match b26:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, True{}, False{}, False{}, False{}, False{}, False{})), false_true(h))
    case False{}:
      four.t25(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, P, leaf, ea, h)

def four.t27(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> @x16: Bool -> @x17: Bool -> @x18: Bool -> @x19: Bool -> @x20: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, False{}, False{}, False{}, False{}), 65536) == False{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, False{}, False{}, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, False{}, False{}, False{}, False{})):
  match b27:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, True{}, False{}, False{}, False{}, False{})), false_true(h))
    case False{}:
      four.t26(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, P, leaf, ea, h)

def four.t28(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, +b28: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> @x16: Bool -> @x17: Bool -> @x18: Bool -> @x19: Bool -> @x20: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, False{}, False{}, False{}), 65536) == False{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, False{}, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, False{}, False{}, False{})):
  match b28:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, True{}, False{}, False{}, False{})), false_true(h))
    case False{}:
      four.t27(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, P, leaf, ea, h)

def four.t29(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, +b28: Bool, +b29: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> @x16: Bool -> @x17: Bool -> @x18: Bool -> @x19: Bool -> @x20: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, False{}, False{}), 65536) == False{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, False{}, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, False{}, False{})):
  match b29:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, True{}, False{}, False{})), false_true(h))
    case False{}:
      four.t28(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, P, leaf, ea, h)

def four.t30(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, +b28: Bool, +b29: Bool, +b30: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> @x16: Bool -> @x17: Bool -> @x18: Bool -> @x19: Bool -> @x20: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, False{}), 65536) == False{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, False{})) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, False{})):
  match b30:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, True{}, False{})), false_true(h))
    case False{}:
      four.t29(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, P, leaf, ea, h)

def four.t31(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, +b28: Bool, +b29: Bool, +b30: Bool, +b31: Bool, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> @x16: Bool -> @x17: Bool -> @x18: Bool -> @x19: Bool -> @x20: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31), 65536) == False{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31)) == True{} : Bool}) -> P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31)):
  match b31:
    case True{}:
      Empty.absurd(P(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, True{})), false_true(h))
    case False{}:
      four.t30(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, P, leaf, ea, h)

def four.tree(+c: U32, -P: (U32 -> Type), leaf: (@x0: Bool -> @x1: Bool -> @x2: Bool -> @x3: Bool -> @x4: Bool -> @x5: Bool -> @x6: Bool -> @x7: Bool -> @x8: Bool -> @x9: Bool -> @x10: Bool -> @x11: Bool -> @x12: Bool -> @x13: Bool -> @x14: Bool -> @x15: Bool -> @x16: Bool -> @x17: Bool -> @x18: Bool -> @x19: Bool -> @x20: Bool -> {U32.is_lt(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == False{} : Bool} -> {scalar(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool} -> P(mk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}))), ea: {U32.is_lt(c, 65536) == False{} : Bool}, h: {scalar(c) == True{} : Bool}) -> P(c):
  match c:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      four.t31(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, P, leaf, ea, h)

# Every scalar value decodes from the bytes `encode` writes for it as
# itself, whichever width it is written in.
def point.w(+c: U32, +rest: List<&2, U32>, +h: {scalar(c) == True{} : Bool}, +one: Bool, e1: {U32.is_lt(c, 128) == one : Bool}, +two: Bool, e2: {U32.is_lt(c, 2048) == two : Bool}, +three: Bool, e3: {U32.is_lt(c, 65536) == three : Bool}) -> {Utf8.decode.step(Utf8.encode.char(c, rest, one, two, three)) == Some{Utf8.Step{Chr{c}, rest}} : Maybe<&2, Utf8.Step>}:
  match one two three:
    case True{} _ _:
      %Equal.sym(Bool, U32.is_lt(c, 128), True{}, e1) : {Some{Utf8.decode.lead(c, rest, _, U32.is_lt(c, 224), U32.is_lt(c, 240))} == Some{Utf8.Step{Chr{c}, rest}} : Maybe<&2, Utf8.Step>}
      {==}
    case False{} True{} _:
      two.tree(c, (m => {Utf8.decode.step(Utf8.encode.char(m, rest, False{}, True{}, three)) == Some{Utf8.Step{Chr{m}, rest}} : Maybe<&2, Utf8.Step>}), (x0 => x1 => x2 => x3 => x4 => x5 => x6 => x7 => x8 => x9 => x10 => ea => two.leaf(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, rest, three)), e1, e2)
    case False{} False{} True{}:
      three.tree(c, (m => {Utf8.decode.step(Utf8.encode.char(m, rest, False{}, False{}, True{})) == Some{Utf8.Step{Chr{m}, rest}} : Maybe<&2, Utf8.Step>}), (x0 => x1 => x2 => x3 => x4 => x5 => x6 => x7 => x8 => x9 => x10 => x11 => x12 => x13 => x14 => x15 => ea => eh => three.leaf(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, rest, eh)), e2, e3, h)
    case False{} False{} False{}:
      four.tree(c, (m => {Utf8.decode.step(Utf8.encode.char(m, rest, False{}, False{}, False{})) == Some{Utf8.Step{Chr{m}, rest}} : Maybe<&2, Utf8.Step>}), (x0 => x1 => x2 => x3 => x4 => x5 => x6 => x7 => x8 => x9 => x10 => x11 => x12 => x13 => x14 => x15 => x16 => x17 => x18 => x19 => x20 => ea => eh => four.leaf(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, rest, eh)), e3, h)

def point(+c: U32, +rest: List<&2, U32>, h: {scalar(c) == True{} : Bool}) -> {Utf8.decode.step(Utf8.encode.char(c, rest, U32.is_lt(c, 128), U32.is_lt(c, 2048), U32.is_lt(c, 65536))) == Some{Utf8.Step{Chr{c}, rest}} : Maybe<&2, Utf8.Step>}:
  point.w(c, rest, h, U32.is_lt(c, 128), {==}, U32.is_lt(c, 2048), {==}, U32.is_lt(c, 65536), {==})

# Validating
# ----------
#
# The same bytes are ones `invalid` takes, as `str::from_utf8` does: a lead
# byte of the width its code point needs, a second byte in the range that
# lead allows — narrower after `E0`, `ED`, `F0` and `F4`, which is where
# an overlong or surrogate sequence would be — and continuation bytes.

# A word is never more than the word of every bit set.
def ones(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{True{}, ones(p)}

def ngt1.fin(r: Cmp, b: Bool, e: {Cmp.is_gt(r) == False{} : Bool}) -> {Cmp.is_gt(Word.cmp.fin(b, True{}, r)) == False{} : Bool}:
  match r b:
    case GT{} _:
      Empty.absurd({Cmp.is_gt(Word.cmp.fin(b, True{}, GT{})) == False{} : Bool}, false_true(Equal.sym(Bool, True{}, False{}, e)))
    case EQ{} False{}:
      {==}
    case EQ{} True{}:
      {==}
    case LT{} _:
      {==}

def ngt1(+n: Nat, w: Word(n)) -> {Cmp.is_gt(Word.cmp(n, w, ones(n))) == False{} : Bool}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, +t}:
          ngt1.fin(Word.cmp(p, t, ones(p)), b, ngt1(p, t))

def ge_nlt(x: Cmp, e: {Cmp.is_lt(x) == False{} : Bool}) -> {Cmp.is_ge(x) == True{} : Bool}:
  match x:
    case LT{}:
      Empty.absurd({Cmp.is_ge(LT{}) == True{} : Bool}, false_true(Equal.sym(Bool, True{}, False{}, e)))
    case EQ{}:
      {==}
    case GT{}:
      {==}

def le_ngt(x: Cmp, e: {Cmp.is_gt(x) == False{} : Bool}) -> {Cmp.is_le(x) == True{} : Bool}:
  match x:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({Cmp.is_le(GT{}) == True{} : Bool}, false_true(Equal.sym(Bool, True{}, False{}, e)))

def and_zero.con(-p: Nat, b: Bool, -t: Word(p), e: {Word.and(p, t, Word.zero(p)) == Word.zero(p) : Word(p)}) -> {WCon{Bool.and(b, False{}), Word.and(p, t, Word.zero(p))} == WCon{False{}, Word.zero(p)} : Word.Con<p>}:
  match b:
    case True{}:
      %Equal.sym(Word(p), Word.and(p, t, Word.zero(p)), Word.zero(p), e) : {WCon{False{}, _} == WCon{False{}, Word.zero(p)} : Word.Con<p>}
      {==}
    case False{}:
      %Equal.sym(Word(p), Word.and(p, t, Word.zero(p)), Word.zero(p), e) : {WCon{False{}, _} == WCon{False{}, Word.zero(p)} : Word.Con<p>}
      {==}

# Masking with no bit set leaves none.
def and_zero(+n: Nat, w: Word(n)) -> {Word.and(n, w, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, +t}:
          and_zero.con(p, b, t, and_zero(p, t))

# A continuation byte, whatever six bits it carries, is one.
def cont6(+x0: Bool, +x1: Bool, +x2: Bool, +x3: Bool, +x4: Bool, +x5: Bool) -> {Utf8.v.cont(mk(x0, x1, x2, x3, x4, x5, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_ge(mk(x0, x1, x2, x3, x4, x5, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128), True{}, ge_nlt(U32.cmp(mk(x0, x1, x2, x3, x4, x5, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128), nlt0(6n, WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WNil{}}}}}}}))) : {Bool.and(_, U32.is_le(mk(x0, x1, x2, x3, x4, x5, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 191)) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le(mk(x0, x1, x2, x3, x4, x5, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 191), True{}, le_ngt(U32.cmp(mk(x0, x1, x2, x3, x4, x5, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 191), ngt1(6n, WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WNil{}}}}}}}))) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

# And so is what `encode` writes after a lead byte: the low six bits of
# anything, marked as a continuation.
def cont_low(m: U32) -> {Utf8.v.cont((128 .|. (m .&. 63) : U32)) == True{} : Bool}:
  match m:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, +t}}}}}}}:
      %Equal.sym(Word(26n), Word.and(26n, t, Word.zero(26n)), Word.zero(26n), and_zero(26n, t)) : {Utf8.v.cont(U32.or(128, U32{WCon{Bool.and(b0, True{}), WCon{Bool.and(b1, True{}), WCon{Bool.and(b2, True{}), WCon{Bool.and(b3, True{}), WCon{Bool.and(b4, True{}), WCon{Bool.and(b5, True{}), _}}}}}}})) == True{} : Bool}
      cont6(Bool.and(b0, True{}), Bool.and(b1, True{}), Bool.and(b2, True{}), Bool.and(b3, True{}), Bool.and(b4, True{}), Bool.and(b5, True{}))

# The steps of a sequence, each as its bytes allow.
def step_at(+i: Nat, +b: U32, +rest: List<&2, U32>, +k: Nat, ew: {Utf8.v.width(b) == 1n+k : Nat}) -> {Utf8.v.step(i, b <> rest) == Some{Utf8.v.tail(b, 1n+k, i, rest)} : Maybe<&2, Utf8.V>}:
  %Equal.sym(Nat, Utf8.v.width(b), 1n+k, ew) : {Some{Bool.pick(Utf8.V, Nat.is_eq(_, 0n), Utf8.V.Bad{Maybe.default(&2, String, Utf8.v.invalid(1n, i), SNil{})}, Utf8.v.tail(b, _, i, rest))} == Some{Utf8.v.tail(b, 1n+k, i, rest)} : Maybe<&2, Utf8.V>}
  {==}

def width1(+c: U32, e1: {U32.is_lt(c, 128) == True{} : Bool}) -> {Utf8.v.width(c) == 1n : Nat}:
  %Equal.sym(Bool, U32.is_lt(c, 128), True{}, e1) : {Bool.pick(Nat, _, 1n, Utf8.v.width.more(c)) == 1n : Nat}
  {==}

def tail1(+lead: U32, +i: Nat, rest: List<&2, U32>) -> {Utf8.v.tail(lead, 1n, i, rest) == Utf8.V.Next{rest, 1n} : Utf8.V}:
  match rest:
    case Nil{}:
      {==}
    case c1 <> r1:
      {==}

def tail2.done(+i: Nat, rest: List<&2, U32>) -> {Utf8.v.tail2(2n, i, rest) == Utf8.V.Next{rest, 2n} : Utf8.V}:
  match rest:
    case Nil{}:
      {==}
    case c2 <> r2:
      {==}

def tail3.done(+i: Nat, rest: List<&2, U32>) -> {Utf8.v.tail3(3n, i, rest) == Utf8.V.Next{rest, 3n} : Utf8.V}:
  match rest:
    case Nil{}:
      {==}
    case c3 <> r3:
      {==}

def tail2(+lead: U32, +i: Nat, +c1: U32, +rest: List<&2, U32>, e: {Utf8.v.cont(c1) == True{} : Bool}) -> {Utf8.v.tail(lead, 2n, i, c1 <> rest) == Utf8.V.Next{rest, 2n} : Utf8.V}:
  %Equal.sym(Bool, Utf8.v.cont(c1), True{}, e) : {Bool.pick(Utf8.V, Bool.not(_), Utf8.V.Bad{Maybe.default(&2, String, Utf8.v.invalid(1n, i), SNil{})}, Utf8.v.tail2(2n, i, rest)) == Utf8.V.Next{rest, 2n} : Utf8.V}
  tail2.done(i, rest)

def tail3(+lead: U32, +i: Nat, +c1: U32, +c2: U32, +rest: List<&2, U32>, e1: {Utf8.v.second(lead, c1) == True{} : Bool}, e2: {Utf8.v.cont(c2) == True{} : Bool}) -> {Utf8.v.tail(lead, 3n, i, c1 <> c2 <> rest) == Utf8.V.Next{rest, 3n} : Utf8.V}:
  %Equal.sym(Bool, Utf8.v.second(lead, c1), True{}, e1) : {Bool.pick(Utf8.V, Bool.not(_), Utf8.V.Bad{Maybe.default(&2, String, Utf8.v.invalid(1n, i), SNil{})}, Utf8.v.tail2(3n, i, c2 <> rest)) == Utf8.V.Next{rest, 3n} : Utf8.V}
  %Equal.sym(Bool, Utf8.v.cont(c2), True{}, e2) : {Bool.pick(Utf8.V, Bool.not(_), Utf8.V.Bad{Maybe.default(&2, String, Utf8.v.invalid(2n, i), SNil{})}, Utf8.v.tail3(3n, i, rest)) == Utf8.V.Next{rest, 3n} : Utf8.V}
  tail3.done(i, rest)

def tail4(+lead: U32, +i: Nat, +c1: U32, +c2: U32, +c3: U32, +rest: List<&2, U32>, e1: {Utf8.v.second(lead, c1) == True{} : Bool}, e2: {Utf8.v.cont(c2) == True{} : Bool}, e3: {Utf8.v.cont(c3) == True{} : Bool}) -> {Utf8.v.tail(lead, 4n, i, c1 <> c2 <> c3 <> rest) == Utf8.V.Next{rest, 4n} : Utf8.V}:
  %Equal.sym(Bool, Utf8.v.second(lead, c1), True{}, e1) : {Bool.pick(Utf8.V, Bool.not(_), Utf8.V.Bad{Maybe.default(&2, String, Utf8.v.invalid(1n, i), SNil{})}, Utf8.v.tail2(4n, i, c2 <> c3 <> rest)) == Utf8.V.Next{rest, 4n} : Utf8.V}
  %Equal.sym(Bool, Utf8.v.cont(c2), True{}, e2) : {Bool.pick(Utf8.V, Bool.not(_), Utf8.V.Bad{Maybe.default(&2, String, Utf8.v.invalid(2n, i), SNil{})}, Utf8.v.tail3(4n, i, c3 <> rest)) == Utf8.V.Next{rest, 4n} : Utf8.V}
  %Equal.sym(Bool, Utf8.v.cont(c3), True{}, e3) : {Bool.pick(Utf8.V, Bool.not(_), Utf8.V.Bad{Maybe.default(&2, String, Utf8.v.invalid(3n, i), SNil{})}, Utf8.V.Next{rest, 4n}) == Utf8.V.Next{rest, 4n} : Utf8.V}
  {==}

# Two bytes: the lead is `C2` to `DF`, since the code point is at least 128.
def width2(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool}) -> {Utf8.v.width((192 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) : U32)) == 2n : Nat}:
  match b6 b7 b8 b9 b10:
    case False{} False{} False{} False{} False{}:
      Empty.absurd({Utf8.v.width((192 .|. (mk(b0, b1, b2, b3, b4, b5, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) : U32)) == 2n : Nat}, false_true(Equal.sym(Bool, True{}, False{}, ea)))
    case False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{}:
      Empty.absurd({Utf8.v.width((192 .|. (mk(b0, b1, b2, b3, b4, b5, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) : U32)) == 2n : Nat}, false_true(Equal.sym(Bool, True{}, False{}, ea)))
    case True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{}:
      {==}

def v2.leaf(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +i: Nat, +rest: List<&2, U32>, t3: Bool, ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 128) == False{} : Bool}) -> {Utf8.v.step(i, Utf8.encode.char(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), rest, False{}, True{}, t3)) == Some{Utf8.V.Next{rest, 2n}} : Maybe<&2, Utf8.V>}:
  %Equal.sym(Maybe<&2, Utf8.V>, Utf8.v.step(i, (192 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) : U32) <> (128 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) .&. 63) : U32) <> rest), Some{Utf8.v.tail((192 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) : U32), 2n, i, (128 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) .&. 63) : U32) <> rest)}, step_at(i, (192 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) : U32), (128 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) .&. 63) : U32) <> rest, 1n, width2(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, ea))) : {_ == Some{Utf8.V.Next{rest, 2n}} : Maybe<&2, Utf8.V>}
  %Equal.sym(Utf8.V, Utf8.v.tail((192 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) : U32), 2n, i, (128 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) .&. 63) : U32) <> rest), Utf8.V.Next{rest, 2n}, tail2((192 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) : U32), i, (128 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) .&. 63) : U32), rest, cont_low(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})))) : {Some{_} == Some{Utf8.V.Next{rest, 2n}} : Maybe<&2, Utf8.V>}
  {==}

# Three bytes: any lead from `E0` to `EF`.
def width3(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> {Utf8.v.width((224 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) : U32)) == 3n : Nat}:
  match b12 b13 b14 b15:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

# After `E0` the second byte is `A0` to `BF`: bit 11 is set, as it is in a
# code point of three bytes with nothing set above it.
def e0.second(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool) -> {Utf8.v.second((224 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32)) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_ge((128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32), 160), True{}, ge_nlt(U32.cmp((128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32), 160), nlt0(5n, WCon{Bool.and(b6, True{}), WCon{Bool.and(b7, True{}), WCon{Bool.and(b8, True{}), WCon{Bool.and(b9, True{}), WCon{Bool.and(b10, True{}), WNil{}}}}}}))) : {Bool.and(_, U32.is_le((128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32), 191)) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le((128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32), 191), True{}, le_ngt(U32.cmp((128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32), 191), ngt1(5n, WCon{Bool.and(b6, True{}), WCon{Bool.and(b7, True{}), WCon{Bool.and(b8, True{}), WCon{Bool.and(b9, True{}), WCon{Bool.and(b10, True{}), WNil{}}}}}}))) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

# After `ED`, `80` to `9F`: bit 11 is clear, as it is in any scalar value
# whose bits above it are `1101`.
def ed.second(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool) -> {Utf8.v.second((224 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32)) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_ge((128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32), 128), True{}, ge_nlt(U32.cmp((128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32), 128), nlt0(5n, WCon{Bool.and(b6, True{}), WCon{Bool.and(b7, True{}), WCon{Bool.and(b8, True{}), WCon{Bool.and(b9, True{}), WCon{Bool.and(b10, True{}), WNil{}}}}}}))) : {Bool.and(_, U32.is_le((128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32), 159)) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le((128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32), 159), True{}, le_ngt(U32.cmp((128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32), 159), ngt1(5n, WCon{Bool.and(b6, True{}), WCon{Bool.and(b7, True{}), WCon{Bool.and(b8, True{}), WCon{Bool.and(b9, True{}), WCon{Bool.and(b10, True{}), WNil{}}}}}}))) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

# A code point whose bits from 11 up are `11011` is a surrogate.
def surrogate(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool) -> {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == False{} : Bool}:
  %Equal.sym(Bool, U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 55296), False{}, nlt0(11n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}})) : {Bool.and(U32.is_le(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 1114111), Bool.or(_, U32.is_gt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 57343))) == False{} : Bool}
  %Equal.sym(Bool, U32.is_gt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 57343), False{}, ngt1(11n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}})) : {Bool.and(U32.is_le(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 1114111), Bool.or(False{}, _)) == False{} : Bool}
  {==}

# The second byte of three is the one its lead allows.
def second3(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> {Utf8.v.second((224 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32)) == True{} : Bool}:
  match b11 b12 b13 b14 b15:
    case False{} False{} False{} False{} False{}:
      Empty.absurd({Utf8.v.second((224 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32)) == True{} : Bool}, false_true(Equal.sym(Bool, True{}, False{}, ea)))
    case False{} False{} False{} False{} True{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case False{} False{} False{} True{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case False{} False{} False{} True{} True{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case False{} False{} True{} False{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case False{} False{} True{} False{} True{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case False{} False{} True{} True{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case False{} False{} True{} True{} True{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, False{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case False{} True{} False{} False{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case False{} True{} False{} False{} True{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case False{} True{} False{} True{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case False{} True{} False{} True{} True{}:
      ed.second(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10)
    case False{} True{} True{} False{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case False{} True{} True{} False{} True{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, True{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case False{} True{} True{} True{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case False{} True{} True{} True{} True{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, False{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case True{} False{} False{} False{} False{}:
      e0.second(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10)
    case True{} False{} False{} False{} True{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case True{} False{} False{} True{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case True{} False{} False{} True{} True{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case True{} False{} True{} False{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case True{} False{} True{} False{} True{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case True{} False{} True{} True{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case True{} False{} True{} True{} True{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, False{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case True{} True{} False{} False{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case True{} True{} False{} False{} True{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case True{} True{} False{} True{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case True{} True{} False{} True{} True{}:
      Empty.absurd({Utf8.v.second((224 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32)) == True{} : Bool}, false_true(Equal.trans(Bool, False{}, scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), True{}, Equal.sym(Bool, scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})), False{}, surrogate(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10)), h)))
    case True{} True{} True{} False{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case True{} True{} True{} False{} True{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, True{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case True{} True{} True{} True{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))
    case True{} True{} True{} True{} True{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32))

def v3.leaf(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +i: Nat, +rest: List<&2, U32>, ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 2048) == False{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> {Utf8.v.step(i, Utf8.encode.char(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), rest, False{}, False{}, True{})) == Some{Utf8.V.Next{rest, 3n}} : Maybe<&2, Utf8.V>}:
  %Equal.sym(Maybe<&2, Utf8.V>, Utf8.v.step(i, (224 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) : U32) <> (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32) <> (128 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) .&. 63) : U32) <> rest), Some{Utf8.v.tail((224 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) : U32), 3n, i, (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32) <> (128 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) .&. 63) : U32) <> rest)}, step_at(i, (224 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32) <> (128 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) .&. 63) : U32) <> rest, 2n, width3(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15))) : {_ == Some{Utf8.V.Next{rest, 3n}} : Maybe<&2, Utf8.V>}
  %Equal.sym(Utf8.V, Utf8.v.tail((224 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) : U32), 3n, i, (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32) <> (128 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) .&. 63) : U32) <> rest), Utf8.V.Next{rest, 3n}, tail3((224 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) : U32), i, (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32), (128 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) .&. 63) : U32), rest, second3(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, ea, h), cont_low(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})))) : {Some{_} == Some{Utf8.V.Next{rest, 3n}} : Maybe<&2, Utf8.V>}
  {==}

# Four bytes: a lead from `F0` to `F4`, since the code point is at most
# U+10FFFF.
def width4(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> {Utf8.v.width((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32)) == 4n : Nat}:
  match b18 b19 b20:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      Empty.absurd({Utf8.v.width((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32)) == 4n : Nat}, false_true(h))
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      Empty.absurd({Utf8.v.width((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32)) == 4n : Nat}, false_true(h))
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      Empty.absurd({Utf8.v.width((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32)) == 4n : Nat}, false_true(h))

# After `F0` the second byte is `90` to `BF`: bit 16 or 17 is set, as one is
# in a code point of four bytes with nothing set above 17.
def f0.second.a(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> {Utf8.v.second((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32)) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_ge((128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32), 144), True{}, ge_nlt(U32.cmp((128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32), 144), nlt0(4n, WCon{Bool.and(b12, True{}), WCon{Bool.and(b13, True{}), WCon{Bool.and(b14, True{}), WCon{Bool.and(b15, True{}), WNil{}}}}}))) : {Bool.and(_, U32.is_le((128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32), 191)) == True{} : Bool}
  {==}

def f0.second.c(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> {Utf8.v.second((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32)) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_le((128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32), 191), True{}, le_ngt(U32.cmp((128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32), 191), ngt1(4n, WCon{Bool.and(b12, True{}), WCon{Bool.and(b13, True{}), WCon{Bool.and(b14, True{}), WCon{Bool.and(b15, True{}), WNil{}}}}}))) : {Bool.and(U32.is_ge((128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32), 144), _) == True{} : Bool}
  {==}

# After `F4`, `80` to `8F`: bits 16 and 17 are clear, as they are in any
# scalar value with bit 20 set.
def f4.second(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> {Utf8.v.second((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32)) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_ge((128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32), 128), True{}, ge_nlt(U32.cmp((128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32), 128), nlt0(4n, WCon{Bool.and(b12, True{}), WCon{Bool.and(b13, True{}), WCon{Bool.and(b14, True{}), WCon{Bool.and(b15, True{}), WNil{}}}}}))) : {Bool.and(_, U32.is_le((128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32), 143)) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le((128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32), 143), True{}, le_ngt(U32.cmp((128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32), 143), ngt1(4n, WCon{Bool.and(b12, True{}), WCon{Bool.and(b13, True{}), WCon{Bool.and(b14, True{}), WCon{Bool.and(b15, True{}), WNil{}}}}}))) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

# The second byte of four is the one its lead allows.
def second4(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == False{} : Bool}, h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> {Utf8.v.second((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32)) == True{} : Bool}:
  match b16 b17 b18 b19 b20:
    case False{} False{} False{} False{} False{}:
      Empty.absurd({Utf8.v.second((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32)) == True{} : Bool}, false_true(Equal.sym(Bool, True{}, False{}, ea)))
    case False{} False{} False{} False{} True{}:
      f4.second(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15)
    case False{} False{} False{} True{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n : U32))
    case False{} False{} False{} True{} True{}:
      Empty.absurd({Utf8.v.second((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32)) == True{} : Bool}, false_true(h))
    case False{} False{} True{} False{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n : U32))
    case False{} False{} True{} False{} True{}:
      Empty.absurd({Utf8.v.second((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32)) == True{} : Bool}, false_true(h))
    case False{} False{} True{} True{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n : U32))
    case False{} False{} True{} True{} True{}:
      Empty.absurd({Utf8.v.second((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, False{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32)) == True{} : Bool}, false_true(h))
    case False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{}:
      Empty.absurd({Utf8.v.second((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32)) == True{} : Bool}, false_true(h))
    case False{} True{} False{} True{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n : U32))
    case False{} True{} False{} True{} True{}:
      Empty.absurd({Utf8.v.second((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32)) == True{} : Bool}, false_true(h))
    case False{} True{} True{} False{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n : U32))
    case False{} True{} True{} False{} True{}:
      Empty.absurd({Utf8.v.second((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, True{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, True{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32)) == True{} : Bool}, false_true(h))
    case False{} True{} True{} True{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n : U32))
    case False{} True{} True{} True{} True{}:
      Empty.absurd({Utf8.v.second((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, False{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32)) == True{} : Bool}, false_true(h))
    case True{} False{} False{} False{} False{}:
      f0.second.a(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15)
    case True{} False{} False{} False{} True{}:
      Empty.absurd({Utf8.v.second((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32)) == True{} : Bool}, false_true(h))
    case True{} False{} False{} True{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n : U32))
    case True{} False{} False{} True{} True{}:
      Empty.absurd({Utf8.v.second((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32)) == True{} : Bool}, false_true(h))
    case True{} False{} True{} False{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n : U32))
    case True{} False{} True{} False{} True{}:
      Empty.absurd({Utf8.v.second((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32)) == True{} : Bool}, false_true(h))
    case True{} False{} True{} True{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n : U32))
    case True{} False{} True{} True{} True{}:
      Empty.absurd({Utf8.v.second((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, False{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, False{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32)) == True{} : Bool}, false_true(h))
    case True{} True{} False{} False{} False{}:
      f0.second.c(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15)
    case True{} True{} False{} False{} True{}:
      Empty.absurd({Utf8.v.second((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32)) == True{} : Bool}, false_true(h))
    case True{} True{} False{} True{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n : U32))
    case True{} True{} False{} True{} True{}:
      Empty.absurd({Utf8.v.second((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32)) == True{} : Bool}, false_true(h))
    case True{} True{} True{} False{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n : U32))
    case True{} True{} True{} False{} True{}:
      Empty.absurd({Utf8.v.second((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, True{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, True{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32)) == True{} : Bool}, false_true(h))
    case True{} True{} True{} True{} False{}:
      cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n : U32))
    case True{} True{} True{} True{} True{}:
      Empty.absurd({Utf8.v.second((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32)) == True{} : Bool}, false_true(h))

def v4.leaf(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +i: Nat, +rest: List<&2, U32>, ea: {U32.is_lt(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), 65536) == False{} : Bool}, +h: {scalar(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})) == True{} : Bool}) -> {Utf8.v.step(i, Utf8.encode.char(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}), rest, False{}, False{}, False{})) == Some{Utf8.V.Next{rest, 4n}} : Maybe<&2, Utf8.V>}:
  %Equal.sym(Maybe<&2, Utf8.V>, Utf8.v.step(i, (240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32) <> (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32) <> (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32) <> (128 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) .&. 63) : U32) <> rest), Some{Utf8.v.tail((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), 4n, i, (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32) <> (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32) <> (128 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) .&. 63) : U32) <> rest)}, step_at(i, (240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32) <> (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32) <> (128 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) .&. 63) : U32) <> rest, 3n, width4(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, h))) : {_ == Some{Utf8.V.Next{rest, 4n}} : Maybe<&2, Utf8.V>}
  %Equal.sym(Utf8.V, Utf8.v.tail((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), 4n, i, (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32) <> (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32) <> (128 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) .&. 63) : U32) <> rest), Utf8.V.Next{rest, 4n}, tail4((240 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 18n) : U32), i, (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 12n) .&. 63) : U32), (128 .|. ((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n) .&. 63) : U32), (128 .|. (mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) .&. 63) : U32), rest, second4(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, ea, h), cont_low((mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) >> 6n : U32)), cont_low(mk(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{})))) : {Some{_} == Some{Utf8.V.Next{rest, 4n}} : Maybe<&2, Utf8.V>}
  {==}

def one.byte(+i: Nat, +c: U32, +rest: List<&2, U32>, e1: {U32.is_lt(c, 128) == True{} : Bool}) -> {Utf8.v.step(i, c <> rest) == Some{Utf8.V.Next{rest, 1n}} : Maybe<&2, Utf8.V>}:
  %Equal.sym(Maybe<&2, Utf8.V>, Utf8.v.step(i, c <> rest), Some{Utf8.v.tail(c, 1n, i, rest)}, step_at(i, c, rest, 0n, width1(c, e1))) : {_ == Some{Utf8.V.Next{rest, 1n}} : Maybe<&2, Utf8.V>}
  %Equal.sym(Utf8.V, Utf8.v.tail(c, 1n, i, rest), Utf8.V.Next{rest, 1n}, tail1(c, i, rest)) : {Some{_} == Some{Utf8.V.Next{rest, 1n}} : Maybe<&2, Utf8.V>}
  {==}

# `invalid` steps over the bytes `encode` writes for a scalar value, all of
# them and no more, whichever width it is written in.
def vpoint.w(+i: Nat, +c: U32, +rest: List<&2, U32>, +h: {scalar(c) == True{} : Bool}, +one: Bool, e1: {U32.is_lt(c, 128) == one : Bool}, +two: Bool, e2: {U32.is_lt(c, 2048) == two : Bool}, +three: Bool, e3: {U32.is_lt(c, 65536) == three : Bool}) -> {Utf8.v.step(i, Utf8.encode.char(c, rest, one, two, three)) == Some{Utf8.V.Next{rest, Bool.pick(Nat, one, 1n, Bool.pick(Nat, two, 2n, Bool.pick(Nat, three, 3n, 4n)))}} : Maybe<&2, Utf8.V>}:
  match one two three:
    case True{} _ _:
      one.byte(i, c, rest, e1)
    case False{} True{} _:
      two.tree(c, (m => {Utf8.v.step(i, Utf8.encode.char(m, rest, False{}, True{}, three)) == Some{Utf8.V.Next{rest, 2n}} : Maybe<&2, Utf8.V>}), (x0 => x1 => x2 => x3 => x4 => x5 => x6 => x7 => x8 => x9 => x10 => ea => v2.leaf(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, i, rest, three, ea)), e1, e2)
    case False{} False{} True{}:
      three.tree(c, (m => {Utf8.v.step(i, Utf8.encode.char(m, rest, False{}, False{}, True{})) == Some{Utf8.V.Next{rest, 3n}} : Maybe<&2, Utf8.V>}), (x0 => x1 => x2 => x3 => x4 => x5 => x6 => x7 => x8 => x9 => x10 => x11 => x12 => x13 => x14 => x15 => ea => eh => v3.leaf(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, i, rest, ea, eh)), e2, e3, h)
    case False{} False{} False{}:
      four.tree(c, (m => {Utf8.v.step(i, Utf8.encode.char(m, rest, False{}, False{}, False{})) == Some{Utf8.V.Next{rest, 4n}} : Maybe<&2, Utf8.V>}), (x0 => x1 => x2 => x3 => x4 => x5 => x6 => x7 => x8 => x9 => x10 => x11 => x12 => x13 => x14 => x15 => x16 => x17 => x18 => x19 => x20 => ea => eh => v4.leaf(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, i, rest, ea, eh)), e3, h)

def vpoint(+i: Nat, +c: U32, +rest: List<&2, U32>, h: {scalar(c) == True{} : Bool}) -> {Utf8.v.step(i, Utf8.encode.char(c, rest, U32.is_lt(c, 128), U32.is_lt(c, 2048), U32.is_lt(c, 65536))) == Some{Utf8.V.Next{rest, Bool.pick(Nat, U32.is_lt(c, 128), 1n, Bool.pick(Nat, U32.is_lt(c, 2048), 2n, Bool.pick(Nat, U32.is_lt(c, 65536), 3n, 4n)))}} : Maybe<&2, Utf8.V>}:
  vpoint.w(i, c, rest, h, U32.is_lt(c, 128), {==}, U32.is_lt(c, 2048), {==}, U32.is_lt(c, 65536), {==})

# Strings
# -------

# A code point takes at least a byte.
def len.char(+c: U32, +rest: List<&2, U32>, one: Bool, two: Bool, three: Bool, +k: Nat, e: {Nat.is_le(k, List.length(&2, U32, rest)) == True{} : Bool}) -> {Nat.is_le(1n+k, List.length(&2, U32, Utf8.encode.char(c, rest, one, two, three))) == True{} : Bool}:
  match one two three:
    case True{} _ _:
      e
    case False{} True{} _:
      le_succ(k, List.length(&2, U32, rest), e)
    case False{} False{} True{}:
      le_succ(k, 1n+List.length(&2, U32, rest), le_succ(k, List.length(&2, U32, rest), e))
    case False{} False{} False{}:
      le_succ(k, 1n+1n+List.length(&2, U32, rest), le_succ(k, 1n+List.length(&2, U32, rest), le_succ(k, List.length(&2, U32, rest), e)))

def len_le(s: String) -> {Nat.is_le(String.length(s), List.length(&2, U32, Utf8.encode(s))) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, +t}:
      len.char(x, Utf8.encode(t), U32.is_lt(x, 128), U32.is_lt(x, 2048), U32.is_lt(x, 65536), String.length(t), len_le(t))

# With fuel for every character, the walk decodes each as itself.
def go(s: String, f: Nat, le: {Nat.is_le(String.length(s), f) == True{} : Bool}, +h: {scalars(s) == True{} : Bool}) -> {Utf8.decode.go(f, Utf8.decode.step(Utf8.encode(s))) == s : String}:
  match s f:
    case SNil{} 0n:
      {==}
    case SNil{} 1n+p:
      {==}
    case SCon{Chr{+x}, +t} 0n:
      Empty.absurd({Utf8.decode.go(0n, Utf8.decode.step(Utf8.encode(SCon{Chr{x}, t}))) == SCon{Chr{x}, t} : String}, false_true(le))
    case SCon{Chr{+x}, +t} 1n+p:
      %Equal.sym(Maybe<&2, Utf8.Step>, Utf8.decode.step(Utf8.encode.char(x, Utf8.encode(t), U32.is_lt(x, 128), U32.is_lt(x, 2048), U32.is_lt(x, 65536))), Some{Utf8.Step{Chr{x}, Utf8.encode(t)}}, point(x, Utf8.encode(t), and_left(scalar(x), scalars(t), h))) : {Utf8.decode.go(1n+p, _) == SCon{Chr{x}, t} : String}
      %Equal.sym(String, Utf8.decode.go(p, Utf8.decode.step(Utf8.encode(t))), t, go(t, p, le, and_right(scalar(x), scalars(t), h))) : {SCon{Chr{x}, _} == SCon{Chr{x}, t} : String}
      {==}

# A string of scalar values, encoded and decoded, is itself.
def decodes(+s: String, h: {scalars(s) == True{} : Bool}) -> {Utf8.decode(Utf8.encode(s)) == s : String}:
  go(s, List.length(&2, U32, Utf8.encode(s)), len_le(s), h)

# With fuel for every character, `invalid` walks the bytes to their end and
# finds nothing wrong.
def vgo(s: String, +i: Nat, f: Nat, le: {Nat.is_le(String.length(s), f) == True{} : Bool}, +h: {scalars(s) == True{} : Bool}) -> {Utf8.v.go(f, i, Utf8.v.step(i, Utf8.encode(s))) == None{} : Maybe<&2, String>}:
  match s f:
    case SNil{} 0n:
      {==}
    case SNil{} 1n+p:
      {==}
    case SCon{Chr{+x}, +t} 0n:
      Empty.absurd({Utf8.v.go(0n, i, Utf8.v.step(i, Utf8.encode(SCon{Chr{x}, t}))) == None{} : Maybe<&2, String>}, false_true(le))
    case SCon{Chr{+x}, +t} 1n+p:
      %Equal.sym(Maybe<&2, Utf8.V>, Utf8.v.step(i, Utf8.encode.char(x, Utf8.encode(t), U32.is_lt(x, 128), U32.is_lt(x, 2048), U32.is_lt(x, 65536))), Some{Utf8.V.Next{Utf8.encode(t), Bool.pick(Nat, U32.is_lt(x, 128), 1n, Bool.pick(Nat, U32.is_lt(x, 2048), 2n, Bool.pick(Nat, U32.is_lt(x, 65536), 3n, 4n)))}}, vpoint(i, x, Utf8.encode(t), and_left(scalar(x), scalars(t), h))) : {Utf8.v.go(1n+p, i, _) == None{} : Maybe<&2, String>}
      vgo(t, Nat.add(i, Bool.pick(Nat, U32.is_lt(x, 128), 1n, Bool.pick(Nat, U32.is_lt(x, 2048), 2n, Bool.pick(Nat, U32.is_lt(x, 65536), 3n, 4n)))), p, le, and_right(scalar(x), scalars(t), h))

# What the port writes for a string of scalar values, read back as the
# store reads a file as text — `read_to_string`, which refuses bytes that
# are not UTF-8 — is that string.
def reads_back(+s: String, +h: {scalars(s) == True{} : Bool}) -> {Store.utf8.of(Utf8.encode(s)) == Done{s} : Result<&2, &2, String, String>}:
  %Equal.sym(Maybe<&2, String>, Utf8.invalid(Utf8.encode(s)), None{}, vgo(s, 0n, List.length(&2, U32, Utf8.encode(s)), len_le(s), h)) : {Maybe.default(&2, Result<&2, &2, String, String>, Maybe.map(&2, String, Result<&2, &2, String, String>, m => Fail{m}, _), Done{Utf8.decode(Utf8.encode(s))}) == Done{s} : Result<&2, &2, String, String>}
  %Equal.sym(String, Utf8.decode(Utf8.encode(s)), s, decodes(s, h)) : {Done{_} == Done{s} : Result<&2, &2, String, String>}
  {==}

def main() -> Unit:
  Unit{}

