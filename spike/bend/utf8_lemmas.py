"""Write `utf8_lemmas.bend`: the proof that a string of Unicode scalar values,
encoded as UTF-8 and decoded again, is itself.

The proof works on the thirty-two bits of a code point, and says the same
thing of each of them, so most of it is written out rather than by hand: a
lemma per bit of each width, and a def per bit of the case analysis that
clears the bits above a width. Run it after changing either:

    python3 utf8_lemmas.py
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parent

N = 32
F = "False{}"
T = "True{}"


def bs(n, p="b"):
    return [f"{p}{i}" for i in range(n)]


def mk(args):
    assert len(args) == N
    return "mk(" + ", ".join(args) + ")"


def word(args, tail="WNil{}"):
    s = tail
    for a in reversed(args):
        s = "WCon{" + a + ", " + s + "}"
    return s


def params(names, ty="Bool"):
    return ", ".join(f"+{n}: {ty}" for n in names)


STEP = "Maybe<&2, Utf8.Step>"

out = []
w = out.append

w('''# The round trip the store's reading depends on: a string of Unicode
# scalar values, encoded as UTF-8 as the port writes it, decodes as itself.
# Proven down to the bits of a character: a code point is taken apart into
# its thirty-two bits, the width `encode` gives it says which of them are
# clear, and each bit `decode` puts back is shown to be the one it came
# from — one bit at a time, so that no case split multiplies another.
import Base
import ./utf8.bend as Utf8

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
''')

bnames = bs(N)
w("# A code point from its bits, the least significant first.")
w(f"def mk({params(bnames)}) -> U32:")
w(f"  U32{{{word(bnames)}}}")
w("")
w('''def wbit(n: Nat, w: Word(n), k: Nat) -> Bool:
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
''')

# ext32
xs, ys = bs(N, "x"), bs(N, "y")
eqs = ", ".join(f"e{i}: {{bit(x, {i}n) == bit(y, {i}n) : Bool}}" for i in range(N))
w("# Two code points are one where every bit of one is the other's.")
w(f"def ext32(x: U32, y: U32, {eqs}) -> {{x == y : U32}}:")
w("  match x y:")
w(f"    case U32{{{word(xs)}}} U32{{{word(ys)}}}:")
for i in range(N):
    cur = ys[:i] + ["_"] + xs[i + 1:]
    w(f"      %Equal.sym(Bool, x{i}, y{i}, e{i}) : {{{mk(cur)} == {mk(ys)} : U32}}")
w("      {==}")
w("")

w('''# What `decode` rebuilds from the bytes `encode` writes for a code point of
# each width: the payload of the lead byte, then six bits a continuation.
def x2(+m: U32) -> U32:
  Utf8.cont(((192 .|. (m >> 6n) : U32) .&. 31 : U32), (128 .|. (m .&. 63) : U32))

def x3(+m: U32) -> U32:
  Utf8.cont(Utf8.cont(((224 .|. (m >> 12n) : U32) .&. 15 : U32), (128 .|. ((m >> 6n) .&. 63) : U32)), (128 .|. (m .&. 63) : U32))

def x4(+m: U32) -> U32:
  Utf8.cont(Utf8.cont(Utf8.cont(((240 .|. (m >> 18n) : U32) .&. 7 : U32), (128 .|. ((m >> 12n) .&. 63) : U32)), (128 .|. ((m >> 6n) .&. 63) : U32)), (128 .|. (m .&. 63) : U32))
''')

WIDTHS = {2: 11, 3: 16, 4: 21}
NAMES = {2: "two", 3: "three", 4: "four"}

for width, free in WIDTHS.items():
    name = NAMES[width]
    fb = bs(free)
    m = mk(fb + [F] * (N - free))
    w(f"# The {name}-byte code points: {free} bits, the rest clear.")
    for k in range(free):
        w(f"def {name}.b{k}({params(fb)}) -> {{bit(x{width}({m}), {k}n) == bit({m}, {k}n) : Bool}}:")
        w(f"  match b{k}:")
        w("    case True{}:")
        w("      {==}")
        w("    case False{}:")
        w("      {==}")
        w("")
    args = ", ".join(fb)
    proofs = [f"{name}.b{k}({args})" for k in range(free)] + ["{==}"] * (N - free)
    w(f"def {name}.bits({params(fb)}) -> {{x{width}({m}) == {m} : U32}}:")
    w(f"  ext32(x{width}({m}), {m}, {', '.join(proofs)})")
    w("")

# leaves
def enc(width, m):
    if width == 2:
        return [f"(192 .|. ({m} >> 6n) : U32)", f"(128 .|. ({m} .&. 63) : U32)"]
    if width == 3:
        return [f"(224 .|. ({m} >> 12n) : U32)", f"(128 .|. (({m} >> 6n) .&. 63) : U32)", f"(128 .|. ({m} .&. 63) : U32)"]
    return [f"(240 .|. ({m} >> 18n) : U32)", f"(128 .|. (({m} >> 12n) .&. 63) : U32)", f"(128 .|. (({m} >> 6n) .&. 63) : U32)", f"(128 .|. ({m} .&. 63) : U32)"]


FLAGS = {2: "False{}, True{}, t3", 3: "False{}, False{}, True{}", 4: "False{}, False{}, False{}"}

for width, free in WIDTHS.items():
    name = NAMES[width]
    fb = bs(free)
    args = ", ".join(fb)
    m = mk(fb + [F] * (N - free))
    goal = f"{{Utf8.decode.step(Utf8.encode.char({m}, rest, {FLAGS[width]})) == Some{{Utf8.Step{{Chr{{{m}}}, rest}}}} : {STEP}}}"
    extra = ", t3: Bool" if width == 2 else f", h: {{scalar({m}) == True{{}} : Bool}}"
    w(f"# A {name}-byte code point decodes from its bytes as itself.")
    w(f"def {name}.leaf({params(fb)}, +rest: List<&2, U32>{extra}) -> {goal}:")
    if width == 2:
        w(f"  %Equal.sym(U32, x2({m}), {m}, two.bits({args})) : {{Some{{Utf8.Step{{Chr{{_}}, rest}}}} == Some{{Utf8.Step{{Chr{{{m}}}, rest}}}} : {STEP}}}")
        w("  {==}")
    else:
        e = enc(width, m)
        b1 = e[0]
        more = " <> ".join(e[1:]) + " <> rest"
        if width == 3:
            lead = f"Some{{Utf8.decode.lead({b1}, {more}, U32.is_lt({b1}, 128), _, U32.is_lt({b1}, 240))}}"
            w(f"  %Equal.sym(Bool, U32.is_lt({b1}, 224), False{{}}, nlt0(4n, {word(['b12', 'b13', 'b14', 'b15'])})) : {{{lead} == Some{{Utf8.Step{{Chr{{{m}}}, rest}}}} : {STEP}}}")
        else:
            lead = f"Some{{Utf8.decode.lead({b1}, {more}, U32.is_lt({b1}, 128), U32.is_lt({b1}, 224), _)}}"
            w(f"  %Equal.sym(Bool, U32.is_lt({b1}, 240), False{{}}, nlt0(3n, {word(['b18', 'b19', 'b20'])})) : {{{lead} == Some{{Utf8.Step{{Chr{{{m}}}, rest}}}} : {STEP}}}")
        w(f"  %Equal.sym(U32, x{width}({m}), {m}, {name}.bits({args})) : {{Some{{Utf8.Step{{Utf8.chr(_), rest}}}} == Some{{Utf8.Step{{Chr{{{m}}}, rest}}}} : {STEP}}}")
        w(f"  %Equal.sym(Char, Utf8.chr({m}), Chr{{{m}}}, chr_ok({m}, h)) : {{Some{{Utf8.Step{{_, rest}}}} == Some{{Utf8.Step{{Chr{{{m}}}, rest}}}} : {STEP}}}")
        w("  {==}")
    w("")

# trees
BOUND = {2: ("e2", "2048", 11), 3: ("e3", "65536", 16), 4: ("h", None, 21)}
for width, free in WIDTHS.items():
    name = NAMES[width]
    hyp, lim, top = BOUND[width]
    def hyps(m):
        if width == 2:
            return f"t3: Bool, e2: {{U32.is_lt({m}, 2048) == True{{}} : Bool}}"
        if width == 3:
            return f"e3: {{U32.is_lt({m}, 65536) == True{{}} : Bool}}, h: {{scalar({m}) == True{{}} : Bool}}"
        return f"h: {{scalar({m}) == True{{}} : Bool}}"
    hargs = {2: "t3, e2", 3: "e3, h", 4: "h"}[width]
    for j in range(free, N):
        low = bnames[:j]
        m = mk(bnames[:j + 1] + [F] * (N - 1 - j))
        mt = mk(low + [T] + [F] * (N - 1 - j))
        goal = lambda mm: f"{{Utf8.decode.step(Utf8.encode.char({mm}, rest, {FLAGS[width]})) == Some{{Utf8.Step{{Chr{{{mm}}}, rest}}}} : {STEP}}}"
        if j == free:
            w(f"# A code point `encode` writes in {width} bytes has no bit set above {free - 1}.")
        w(f"def {name}.t{j}({params(bnames[:j + 1])}, +rest: List<&2, U32>, {hyps(m)}) -> {goal(m)}:")
        w(f"  match b{j}:")
        w("    case True{}:")
        if width == 4 or j > top:
            w(f"      Empty.absurd({goal(mt)}, false_true({hyp}))")
        else:
            w(f"      Empty.absurd({goal(mt)}, false_true(Equal.trans(Bool, False{{}}, U32.is_lt({mt}, {lim}), True{{}}, Equal.sym(Bool, U32.is_lt({mt}, {lim}), False{{}}, nlt0({j}n, {word(low)})), {hyp})))")
        w("    case False{}:")
        if j == free:
            extra = ", t3" if width == 2 else ", h"
            w(f"      {name}.leaf({', '.join(bnames[:free])}, rest{extra})")
        else:
            w(f"      {name}.t{j - 1}({', '.join(low)}, rest, {hargs})")
        w("")
    if width == 2:
        sig = f"+c: U32, +rest: List<&2, U32>, t3: Bool, e2: {{U32.is_lt(c, 2048) == True{{}} : Bool}}"
    elif width == 3:
        sig = f"+c: U32, +rest: List<&2, U32>, e3: {{U32.is_lt(c, 65536) == True{{}} : Bool}}, h: {{scalar(c) == True{{}} : Bool}}"
    else:
        sig = f"+c: U32, +rest: List<&2, U32>, h: {{scalar(c) == True{{}} : Bool}}"
    w(f"def {name}.tree({sig}) -> {{Utf8.decode.step(Utf8.encode.char(c, rest, {FLAGS[width]})) == Some{{Utf8.Step{{Chr{{c}}, rest}}}} : {STEP}}}:")
    w("  match c:")
    w(f"    case U32{{{word(bnames)}}}:")
    w(f"      {name}.t31({', '.join(bnames)}, rest, {hargs})")
    w("")

w(f'''# Every scalar value decodes from the bytes `encode` writes for it as
# itself, whichever width it is written in.
def point.w(+c: U32, +rest: List<&2, U32>, h: {{scalar(c) == True{{}} : Bool}}, one: Bool, e1: {{U32.is_lt(c, 128) == one : Bool}}, two: Bool, e2: {{U32.is_lt(c, 2048) == two : Bool}}, three: Bool, e3: {{U32.is_lt(c, 65536) == three : Bool}}) -> {{Utf8.decode.step(Utf8.encode.char(c, rest, one, two, three)) == Some{{Utf8.Step{{Chr{{c}}, rest}}}} : {STEP}}}:
  match one two three:
    case True{{}} _ _:
      %Equal.sym(Bool, U32.is_lt(c, 128), True{{}}, e1) : {{Some{{Utf8.decode.lead(c, rest, _, U32.is_lt(c, 224), U32.is_lt(c, 240))}} == Some{{Utf8.Step{{Chr{{c}}, rest}}}} : {STEP}}}
      {{==}}
    case False{{}} True{{}} _:
      two.tree(c, rest, three, e2)
    case False{{}} False{{}} True{{}}:
      three.tree(c, rest, e3, h)
    case False{{}} False{{}} False{{}}:
      four.tree(c, rest, h)

def point(+c: U32, +rest: List<&2, U32>, h: {{scalar(c) == True{{}} : Bool}}) -> {{Utf8.decode.step(Utf8.encode.char(c, rest, U32.is_lt(c, 128), U32.is_lt(c, 2048), U32.is_lt(c, 65536))) == Some{{Utf8.Step{{Chr{{c}}, rest}}}} : {STEP}}}:
  point.w(c, rest, h, U32.is_lt(c, 128), {{==}}, U32.is_lt(c, 2048), {{==}}, U32.is_lt(c, 65536), {{==}})

# Strings
# -------

# A code point takes at least a byte.
def len.char(+c: U32, +rest: List<&2, U32>, one: Bool, two: Bool, three: Bool, +k: Nat, e: {{Nat.is_le(k, List.length(&2, U32, rest)) == True{{}} : Bool}}) -> {{Nat.is_le(1n+k, List.length(&2, U32, Utf8.encode.char(c, rest, one, two, three))) == True{{}} : Bool}}:
  match one two three:
    case True{{}} _ _:
      e
    case False{{}} True{{}} _:
      le_succ(k, List.length(&2, U32, rest), e)
    case False{{}} False{{}} True{{}}:
      le_succ(k, 1n+List.length(&2, U32, rest), le_succ(k, List.length(&2, U32, rest), e))
    case False{{}} False{{}} False{{}}:
      le_succ(k, 1n+1n+List.length(&2, U32, rest), le_succ(k, 1n+List.length(&2, U32, rest), le_succ(k, List.length(&2, U32, rest), e)))

def len_le(s: String) -> {{Nat.is_le(String.length(s), List.length(&2, U32, Utf8.encode(s))) == True{{}} : Bool}}:
  match s:
    case SNil{{}}:
      {{==}}
    case SCon{{Chr{{+x}}, +t}}:
      len.char(x, Utf8.encode(t), U32.is_lt(x, 128), U32.is_lt(x, 2048), U32.is_lt(x, 65536), String.length(t), len_le(t))

# With fuel for every character, the walk decodes each as itself.
def go(s: String, f: Nat, le: {{Nat.is_le(String.length(s), f) == True{{}} : Bool}}, +h: {{scalars(s) == True{{}} : Bool}}) -> {{Utf8.decode.go(f, Utf8.decode.step(Utf8.encode(s))) == s : String}}:
  match s f:
    case SNil{{}} 0n:
      {{==}}
    case SNil{{}} 1n+p:
      {{==}}
    case SCon{{Chr{{+x}}, +t}} 0n:
      Empty.absurd({{Utf8.decode.go(0n, Utf8.decode.step(Utf8.encode(SCon{{Chr{{x}}, t}}))) == SCon{{Chr{{x}}, t}} : String}}, false_true(le))
    case SCon{{Chr{{+x}}, +t}} 1n+p:
      %Equal.sym({STEP}, Utf8.decode.step(Utf8.encode.char(x, Utf8.encode(t), U32.is_lt(x, 128), U32.is_lt(x, 2048), U32.is_lt(x, 65536))), Some{{Utf8.Step{{Chr{{x}}, Utf8.encode(t)}}}}, point(x, Utf8.encode(t), and_left(scalar(x), scalars(t), h))) : {{Utf8.decode.go(1n+p, _) == SCon{{Chr{{x}}, t}} : String}}
      %Equal.sym(String, Utf8.decode.go(p, Utf8.decode.step(Utf8.encode(t))), t, go(t, p, le, and_right(scalar(x), scalars(t), h))) : {{SCon{{Chr{{x}}, _}} == SCon{{Chr{{x}}, t}} : String}}
      {{==}}

# A string of scalar values, encoded and decoded, is itself.
def reads_back(+s: String, h: {{scalars(s) == True{{}} : Bool}}) -> {{Utf8.decode(Utf8.encode(s)) == s : String}}:
  go(s, List.length(&2, U32, Utf8.encode(s)), len_le(s), h)

def main() -> Unit:
  Unit{{}}
''')

(ROOT / "utf8_lemmas.bend").write_text("\n".join(out) + "\n")
