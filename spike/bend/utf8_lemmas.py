"""Write `utf8_lemmas.bend`: the proof that a string of Unicode scalar values,
encoded as UTF-8, is read back as text as itself.

The proof works on the thirty-two bits of a code point, and says the same
thing of each of them, so most of it is written out rather than by hand: a
lemma per bit of each width, a def per bit of the case analysis that clears
the bits above a width, and a case per lead byte where the validator asks
which one it is. Run it after changing any of them:

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

# Cases on the bits above a width
# -------------------------------

MV = "Maybe<&2, Utf8.V>"
HYPS = {
    2: [("ea", lambda m: f"{{U32.is_lt({m}, 128) == False{{}} : Bool}}"), ("eb", lambda m: f"{{U32.is_lt({m}, 2048) == True{{}} : Bool}}")],
    3: [("ea", lambda m: f"{{U32.is_lt({m}, 2048) == False{{}} : Bool}}"), ("eb", lambda m: f"{{U32.is_lt({m}, 65536) == True{{}} : Bool}}"), ("h", lambda m: f"{{scalar({m}) == True{{}} : Bool}}")],
    4: [("ea", lambda m: f"{{U32.is_lt({m}, 65536) == False{{}} : Bool}}"), ("h", lambda m: f"{{scalar({m}) == True{{}} : Bool}}")],
}
# What the leaf is handed besides the bits.
LEAFH = {2: ["ea"], 3: ["ea", "h"], 4: ["ea", "h"]}
# The hypothesis that clears the bits above a width, the limit it names,
# and the top bit, where the comparison runs on into the bits below.
BOUND = {2: ("eb", "2048", 11), 3: ("eb", "65536", 16), 4: ("h", None, 21)}


def leaf_type(width, free):
    xs = bs(free, "x")
    mx = mk(xs + [F] * (N - free))
    parts = [f"@{x}: Bool" for x in xs]
    for hn in LEAFH[width]:
        parts.append(dict(HYPS[width])[hn](mx))
    return "(" + " -> ".join(parts) + f" -> P({mx}))"


for width, free in WIDTHS.items():
    name = NAMES[width]
    hyp, lim, top = BOUND[width]
    lt = leaf_type(width, free)
    hnames = [hn for hn, _ in HYPS[width]]
    for j in range(free, N):
        low = bnames[:j]
        m = mk(bnames[:j + 1] + [F] * (N - 1 - j))
        mt = mk(low + [T] + [F] * (N - 1 - j))
        hs = ", ".join(f"{hn}: {f(m)}" for hn, f in HYPS[width])
        if j == free:
            w(f"# A code point `encode` writes in {width} bytes has no bit set above {free - 1}: what is")
            w("# to be shown of it is shown of one whose bits above are clear.")
        w(f"def {name}.t{j}({params(bnames[:j + 1])}, -P: (U32 -> Type), leaf: {lt}, {hs}) -> P({m}):")
        w(f"  match b{j}:")
        w("    case True{}:")
        if width == 4 or j > top:
            w(f"      Empty.absurd(P({mt}), false_true({hyp}))")
        else:
            w(f"      Empty.absurd(P({mt}), false_true(Equal.trans(Bool, False{{}}, U32.is_lt({mt}, {lim}), True{{}}, Equal.sym(Bool, U32.is_lt({mt}, {lim}), False{{}}, nlt0({j}n, {word(low)})), {hyp})))")
        w("    case False{}:")
        if j == free:
            w(f"      leaf({', '.join(bnames[:free] + LEAFH[width])})")
        else:
            w(f"      {name}.t{j - 1}({', '.join(low)}, P, leaf, {', '.join(hnames)})")
        w("")
    hs = ", ".join(f"{hn}: {f('c')}" for hn, f in HYPS[width])
    w(f"def {name}.tree(+c: U32, -P: (U32 -> Type), leaf: {lt}, {hs}) -> P(c):")
    w("  match c:")
    w(f"    case U32{{{word(bnames)}}}:")
    w(f"      {name}.t31({', '.join(bnames)}, P, leaf, {', '.join(hnames)})")
    w("")


def lam(free, extra, body):
    return "(" + " => ".join(bs(free, "x") + extra) + " => " + body + ")"


xa = {fr: ", ".join(bs(fr, "x")) for fr in WIDTHS.values()}


def DEC(flags):
    return f"(m => {{Utf8.decode.step(Utf8.encode.char(m, rest, {flags})) == Some{{Utf8.Step{{Chr{{m}}, rest}}}} : {STEP}}})"


w(f"""# Every scalar value decodes from the bytes `encode` writes for it as
# itself, whichever width it is written in.
def point.w(+c: U32, +rest: List<&2, U32>, +h: {{scalar(c) == True{{}} : Bool}}, +one: Bool, e1: {{U32.is_lt(c, 128) == one : Bool}}, +two: Bool, e2: {{U32.is_lt(c, 2048) == two : Bool}}, +three: Bool, e3: {{U32.is_lt(c, 65536) == three : Bool}}) -> {{Utf8.decode.step(Utf8.encode.char(c, rest, one, two, three)) == Some{{Utf8.Step{{Chr{{c}}, rest}}}} : {STEP}}}:
  match one two three:
    case True{{}} _ _:
      %Equal.sym(Bool, U32.is_lt(c, 128), True{{}}, e1) : {{Some{{Utf8.decode.lead(c, rest, _, U32.is_lt(c, 224), U32.is_lt(c, 240))}} == Some{{Utf8.Step{{Chr{{c}}, rest}}}} : {STEP}}}
      {{==}}
    case False{{}} True{{}} _:
      two.tree(c, {DEC("False{}, True{}, three")}, {lam(11, ["ea"], f"two.leaf({xa[11]}, rest, three)")}, e1, e2)
    case False{{}} False{{}} True{{}}:
      three.tree(c, {DEC("False{}, False{}, True{}")}, {lam(16, ["ea", "eh"], f"three.leaf({xa[16]}, rest, eh)")}, e2, e3, h)
    case False{{}} False{{}} False{{}}:
      four.tree(c, {DEC("False{}, False{}, False{}")}, {lam(21, ["ea", "eh"], f"four.leaf({xa[21]}, rest, eh)")}, e3, h)

def point(+c: U32, +rest: List<&2, U32>, h: {{scalar(c) == True{{}} : Bool}}) -> {{Utf8.decode.step(Utf8.encode.char(c, rest, U32.is_lt(c, 128), U32.is_lt(c, 2048), U32.is_lt(c, 65536))) == Some{{Utf8.Step{{Chr{{c}}, rest}}}} : {STEP}}}:
  point.w(c, rest, h, U32.is_lt(c, 128), {{==}}, U32.is_lt(c, 2048), {{==}}, U32.is_lt(c, 65536), {{==}})
""")

w("""# Validating
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
""")

cx = bs(6, "x")
cb = mk(cx + [F, T] + [F] * 24)
cw6 = word(cx)
w("# A continuation byte, whatever six bits it carries, is one.")
w(f"def cont6({params(cx)}) -> {{Utf8.v.cont({cb}) == True{{}} : Bool}}:")
w(f"  %Equal.sym(Bool, U32.is_ge({cb}, 128), True{{}}, ge_nlt(U32.cmp({cb}, 128), nlt0(6n, {cw6}))) : {{Bool.and(_, U32.is_le({cb}, 191)) == True{{}} : Bool}}")
w(f"  %Equal.sym(Bool, U32.is_le({cb}, 191), True{{}}, le_ngt(U32.cmp({cb}, 191), ngt1(6n, {cw6}))) : {{Bool.and(True{{}}, _) == True{{}} : Bool}}")
w("  {==}")
w("")
lowb = bs(6)
andt = [f"Bool.and({x}, True{{}})" for x in lowb]
masked = "U32{" + word(andt, "_") + "}"
w("# And so is what `encode` writes after a lead byte: the low six bits of")
w("# anything, marked as a continuation.")
w("def cont_low(m: U32) -> {Utf8.v.cont((128 .|. (m .&. 63) : U32)) == True{} : Bool}:")
w("  match m:")
w(f"    case U32{{{word(lowb, '+t')}}}:")
w(f"      %Equal.sym(Word(26n), Word.and(26n, t, Word.zero(26n)), Word.zero(26n), and_zero(26n, t)) : {{Utf8.v.cont(U32.or(128, {masked})) == True{{}} : Bool}}")
w(f"      cont6({', '.join(andt)})")
w("")


def BAD(k):
    return f"Utf8.V.Bad{{Maybe.default(&2, String, Utf8.v.invalid({k}n, i), SNil{{}})}}"


w(f"""# The steps of a sequence, each as its bytes allow.
def step_at(+i: Nat, +b: U32, +rest: List<&2, U32>, +k: Nat, ew: {{Utf8.v.width(b) == 1n+k : Nat}}) -> {{Utf8.v.step(i, b <> rest) == Some{{Utf8.v.tail(b, 1n+k, i, rest)}} : {MV}}}:
  %Equal.sym(Nat, Utf8.v.width(b), 1n+k, ew) : {{Some{{Bool.pick(Utf8.V, Nat.is_eq(_, 0n), {BAD(1)}, Utf8.v.tail(b, _, i, rest))}} == Some{{Utf8.v.tail(b, 1n+k, i, rest)}} : {MV}}}
  {{==}}

def width1(+c: U32, e1: {{U32.is_lt(c, 128) == True{{}} : Bool}}) -> {{Utf8.v.width(c) == 1n : Nat}}:
  %Equal.sym(Bool, U32.is_lt(c, 128), True{{}}, e1) : {{Bool.pick(Nat, _, 1n, Utf8.v.width.more(c)) == 1n : Nat}}
  {{==}}

def tail1(+lead: U32, +i: Nat, rest: List<&2, U32>) -> {{Utf8.v.tail(lead, 1n, i, rest) == Utf8.V.Next{{rest, 1n}} : Utf8.V}}:
  match rest:
    case Nil{{}}:
      {{==}}
    case c1 <> r1:
      {{==}}

def tail2.done(+i: Nat, rest: List<&2, U32>) -> {{Utf8.v.tail2(2n, i, rest) == Utf8.V.Next{{rest, 2n}} : Utf8.V}}:
  match rest:
    case Nil{{}}:
      {{==}}
    case c2 <> r2:
      {{==}}

def tail3.done(+i: Nat, rest: List<&2, U32>) -> {{Utf8.v.tail3(3n, i, rest) == Utf8.V.Next{{rest, 3n}} : Utf8.V}}:
  match rest:
    case Nil{{}}:
      {{==}}
    case c3 <> r3:
      {{==}}

def tail2(+lead: U32, +i: Nat, +c1: U32, +rest: List<&2, U32>, e: {{Utf8.v.cont(c1) == True{{}} : Bool}}) -> {{Utf8.v.tail(lead, 2n, i, c1 <> rest) == Utf8.V.Next{{rest, 2n}} : Utf8.V}}:
  %Equal.sym(Bool, Utf8.v.cont(c1), True{{}}, e) : {{Bool.pick(Utf8.V, Bool.not(_), {BAD(1)}, Utf8.v.tail2(2n, i, rest)) == Utf8.V.Next{{rest, 2n}} : Utf8.V}}
  tail2.done(i, rest)

def tail3(+lead: U32, +i: Nat, +c1: U32, +c2: U32, +rest: List<&2, U32>, e1: {{Utf8.v.second(lead, c1) == True{{}} : Bool}}, e2: {{Utf8.v.cont(c2) == True{{}} : Bool}}) -> {{Utf8.v.tail(lead, 3n, i, c1 <> c2 <> rest) == Utf8.V.Next{{rest, 3n}} : Utf8.V}}:
  %Equal.sym(Bool, Utf8.v.second(lead, c1), True{{}}, e1) : {{Bool.pick(Utf8.V, Bool.not(_), {BAD(1)}, Utf8.v.tail2(3n, i, c2 <> rest)) == Utf8.V.Next{{rest, 3n}} : Utf8.V}}
  %Equal.sym(Bool, Utf8.v.cont(c2), True{{}}, e2) : {{Bool.pick(Utf8.V, Bool.not(_), {BAD(2)}, Utf8.v.tail3(3n, i, rest)) == Utf8.V.Next{{rest, 3n}} : Utf8.V}}
  tail3.done(i, rest)

def tail4(+lead: U32, +i: Nat, +c1: U32, +c2: U32, +c3: U32, +rest: List<&2, U32>, e1: {{Utf8.v.second(lead, c1) == True{{}} : Bool}}, e2: {{Utf8.v.cont(c2) == True{{}} : Bool}}, e3: {{Utf8.v.cont(c3) == True{{}} : Bool}}) -> {{Utf8.v.tail(lead, 4n, i, c1 <> c2 <> c3 <> rest) == Utf8.V.Next{{rest, 4n}} : Utf8.V}}:
  %Equal.sym(Bool, Utf8.v.second(lead, c1), True{{}}, e1) : {{Bool.pick(Utf8.V, Bool.not(_), {BAD(1)}, Utf8.v.tail2(4n, i, c2 <> c3 <> rest)) == Utf8.V.Next{{rest, 4n}} : Utf8.V}}
  %Equal.sym(Bool, Utf8.v.cont(c2), True{{}}, e2) : {{Bool.pick(Utf8.V, Bool.not(_), {BAD(2)}, Utf8.v.tail3(4n, i, c3 <> rest)) == Utf8.V.Next{{rest, 4n}} : Utf8.V}}
  %Equal.sym(Bool, Utf8.v.cont(c3), True{{}}, e3) : {{Bool.pick(Utf8.V, Bool.not(_), {BAD(3)}, Utf8.V.Next{{rest, 4n}}) == Utf8.V.Next{{rest, 4n}} : Utf8.V}}
  {{==}}
""")


def cases(vars_, fn):
    """A match over `vars_`, every combination spelled out; fn(values) gives the body."""
    import itertools
    w(f"  match {' '.join(vars_)}:")
    for vals in itertools.product([False, True], repeat=len(vars_)):
        pat = " ".join(T if v else F for v in vals)
        w(f"    case {pat}:")
        w(f"      {fn(dict(zip(vars_, vals)))}")


def val(v):
    return T if v else F


# Two bytes
fb = bs(11)
M2 = mk(fb + [F] * 21)
B = enc(2, M2)
w("# Two bytes: the lead is `C2` to `DF`, since the code point is at least 128.")
w(f"def width2({params(fb)}, ea: {{U32.is_lt({M2}, 128) == False{{}} : Bool}}) -> {{Utf8.v.width({B[0]}) == 2n : Nat}}:")


def w2body(v):
    mm = mk(bs(6) + [val(v[f"b{k}"]) for k in range(6, 11)] + [F] * 21)
    if not any(v[f"b{k}"] for k in range(7, 11)):
        return f"Empty.absurd({{Utf8.v.width({enc(2, mm)[0]}) == 2n : Nat}}, false_true(Equal.sym(Bool, True{{}}, False{{}}, ea)))"
    return "{==}"


cases([f"b{k}" for k in range(6, 11)], w2body)
w("")
w(f"def v2.leaf({params(fb)}, +i: Nat, +rest: List<&2, U32>, t3: Bool, ea: {{U32.is_lt({M2}, 128) == False{{}} : Bool}}) -> {{Utf8.v.step(i, Utf8.encode.char({M2}, rest, False{{}}, True{{}}, t3)) == Some{{Utf8.V.Next{{rest, 2n}}}} : {MV}}}:")
w(f"  %Equal.sym({MV}, Utf8.v.step(i, {B[0]} <> {B[1]} <> rest), Some{{Utf8.v.tail({B[0]}, 2n, i, {B[1]} <> rest)}}, step_at(i, {B[0]}, {B[1]} <> rest, 1n, width2({', '.join(fb)}, ea))) : {{_ == Some{{Utf8.V.Next{{rest, 2n}}}} : {MV}}}")
w(f"  %Equal.sym(Utf8.V, Utf8.v.tail({B[0]}, 2n, i, {B[1]} <> rest), Utf8.V.Next{{rest, 2n}}, tail2({B[0]}, i, {B[1]}, rest, cont_low({M2}))) : {{Some{{_}} == Some{{Utf8.V.Next{{rest, 2n}}}} : {MV}}}")
w("  {==}")
w("")

# Three bytes
fb = bs(16)
lo11 = bs(11)
M3 = mk(fb + [F] * 16)
B = enc(3, M3)
w("# Three bytes: any lead from `E0` to `EF`.")
w(f"def width3({params(fb)}) -> {{Utf8.v.width({B[0]}) == 3n : Nat}}:")
cases([f"b{k}" for k in range(12, 16)], lambda v: "{==}")
w("")
w5 = word([f"Bool.and(b{k}, True{{}})" for k in range(6, 11)])


def second_lemma(nm, bits_hi, lo_, hi_, comment):
    mm = mk(lo11 + bits_hi + [F] * 16)
    bb = enc(3, mm)
    w(comment)
    w(f"def {nm}({params(lo11)}) -> {{Utf8.v.second({bb[0]}, {bb[1]}) == True{{}} : Bool}}:")
    w(f"  %Equal.sym(Bool, U32.is_ge({bb[1]}, {lo_}), True{{}}, ge_nlt(U32.cmp({bb[1]}, {lo_}), nlt0(5n, {w5}))) : {{Bool.and(_, U32.is_le({bb[1]}, {hi_})) == True{{}} : Bool}}")
    w(f"  %Equal.sym(Bool, U32.is_le({bb[1]}, {hi_}), True{{}}, le_ngt(U32.cmp({bb[1]}, {hi_}), ngt1(5n, {w5}))) : {{Bool.and(True{{}}, _) == True{{}} : Bool}}")
    w("  {==}")
    w("")


second_lemma("e0.second", [T, F, F, F, F], 160, 191, "# After `E0` the second byte is `A0` to `BF`: bit 11 is set, as it is in a\n# code point of three bytes with nothing set above it.")
second_lemma("ed.second", [F, T, F, T, T], 128, 159, "# After `ED`, `80` to `9F`: bit 11 is clear, as it is in any scalar value\n# whose bits above it are `1101`.")
msur = mk(lo11 + [T, T, F, T, T] + [F] * 16)
w11 = word(lo11)
w("# A code point whose bits from 11 up are `11011` is a surrogate.")
w(f"def surrogate({params(lo11)}) -> {{scalar({msur}) == False{{}} : Bool}}:")
w(f"  %Equal.sym(Bool, U32.is_lt({msur}, 55296), False{{}}, nlt0(11n, {w11})) : {{Bool.and(U32.is_le({msur}, 1114111), Bool.or(_, U32.is_gt({msur}, 57343))) == False{{}} : Bool}}")
w(f"  %Equal.sym(Bool, U32.is_gt({msur}, 57343), False{{}}, ngt1(11n, {w11})) : {{Bool.and(U32.is_le({msur}, 1114111), Bool.or(False{{}}, _)) == False{{}} : Bool}}")
w("  {==}")
w("")
w("# The second byte of three is the one its lead allows.")
w(f"def second3({params(fb)}, ea: {{U32.is_lt({M3}, 2048) == False{{}} : Bool}}, h: {{scalar({M3}) == True{{}} : Bool}}) -> {{Utf8.v.second({B[0]}, {B[1]}) == True{{}} : Bool}}:")


def s3body(v):
    hi = [val(v[f"b{k}"]) for k in range(11, 16)]
    mm = mk(lo11 + hi + [F] * 16)
    bb = enc(3, mm)
    goal = f"{{Utf8.v.second({bb[0]}, {bb[1]}) == True{{}} : Bool}}"
    nib = [v[f"b{k}"] for k in range(12, 16)]
    args = ", ".join(lo11)
    if nib == [False, False, False, False]:
        if not v["b11"]:
            return f"Empty.absurd({goal}, false_true(Equal.sym(Bool, True{{}}, False{{}}, ea)))"
        return f"e0.second({args})"
    if nib == [True, False, True, True]:
        if v["b11"]:
            return f"Empty.absurd({goal}, false_true(Equal.trans(Bool, False{{}}, scalar({mm}), True{{}}, Equal.sym(Bool, scalar({mm}), False{{}}, surrogate({args})), h)))"
        return f"ed.second({args})"
    return f"cont_low(({mm} >> 6n : U32))"


cases([f"b{k}" for k in range(11, 16)], s3body)
w("")
w(f"def v3.leaf({params(fb)}, +i: Nat, +rest: List<&2, U32>, ea: {{U32.is_lt({M3}, 2048) == False{{}} : Bool}}, h: {{scalar({M3}) == True{{}} : Bool}}) -> {{Utf8.v.step(i, Utf8.encode.char({M3}, rest, False{{}}, False{{}}, True{{}})) == Some{{Utf8.V.Next{{rest, 3n}}}} : {MV}}}:")
w(f"  %Equal.sym({MV}, Utf8.v.step(i, {B[0]} <> {B[1]} <> {B[2]} <> rest), Some{{Utf8.v.tail({B[0]}, 3n, i, {B[1]} <> {B[2]} <> rest)}}, step_at(i, {B[0]}, {B[1]} <> {B[2]} <> rest, 2n, width3({', '.join(fb)}))) : {{_ == Some{{Utf8.V.Next{{rest, 3n}}}} : {MV}}}")
w(f"  %Equal.sym(Utf8.V, Utf8.v.tail({B[0]}, 3n, i, {B[1]} <> {B[2]} <> rest), Utf8.V.Next{{rest, 3n}}, tail3({B[0]}, i, {B[1]}, {B[2]}, rest, second3({', '.join(fb)}, ea, h), cont_low({M3}))) : {{Some{{_}} == Some{{Utf8.V.Next{{rest, 3n}}}} : {MV}}}")
w("  {==}")
w("")

# Four bytes
fb = bs(21)
lo16 = bs(16)
M4 = mk(fb + [F] * 11)
B = enc(4, M4)
w("# Four bytes: a lead from `F0` to `F4`, since the code point is at most")
w("# U+10FFFF.")
w(f"def width4({params(fb)}, h: {{scalar({M4}) == True{{}} : Bool}}) -> {{Utf8.v.width({B[0]}) == 4n : Nat}}:")


def w4body(v):
    lead = v["b18"] + 2 * v["b19"] + 4 * v["b20"]
    mm = mk(bs(18) + [val(v[f"b{k}"]) for k in range(18, 21)] + [F] * 11)
    if lead > 4:
        return f"Empty.absurd({{Utf8.v.width({enc(4, mm)[0]}) == 4n : Nat}}, false_true(h))"
    return "{==}"


cases(["b18", "b19", "b20"], w4body)
w("")
w4 = word([f"Bool.and(b{k}, True{{}})" for k in range(12, 16)])


def f_lemma(nm, hi, lo_, hi_, ge, le, comment):
    mm = mk(lo16 + hi + [F] * 11)
    bb = enc(4, mm)
    if comment:
        w(comment)
    w(f"def {nm}({params(lo16)}) -> {{Utf8.v.second({bb[0]}, {bb[1]}) == True{{}} : Bool}}:")
    if ge:
        w(f"  %Equal.sym(Bool, U32.is_ge({bb[1]}, {lo_}), True{{}}, ge_nlt(U32.cmp({bb[1]}, {lo_}), nlt0(4n, {w4}))) : {{Bool.and(_, U32.is_le({bb[1]}, {hi_})) == True{{}} : Bool}}")
    if le:
        first = "True{}" if ge else f"U32.is_ge({bb[1]}, {lo_})"
        w(f"  %Equal.sym(Bool, U32.is_le({bb[1]}, {hi_}), True{{}}, le_ngt(U32.cmp({bb[1]}, {hi_}), ngt1(4n, {w4}))) : {{Bool.and({first}, _) == True{{}} : Bool}}")
    w("  {==}")
    w("")


f_lemma("f0.second.a", [T, F, F, F, F], 144, 191, True, False, "# After `F0` the second byte is `90` to `BF`: bit 16 or 17 is set, as one is\n# in a code point of four bytes with nothing set above 17.")
f_lemma("f0.second.c", [T, T, F, F, F], 144, 191, False, True, "")
f_lemma("f4.second", [F, F, F, F, T], 128, 143, True, True, "# After `F4`, `80` to `8F`: bits 16 and 17 are clear, as they are in any\n# scalar value with bit 20 set.")
w("# The second byte of four is the one its lead allows.")
w(f"def second4({params(fb)}, ea: {{U32.is_lt({M4}, 65536) == False{{}} : Bool}}, h: {{scalar({M4}) == True{{}} : Bool}}) -> {{Utf8.v.second({B[0]}, {B[1]}) == True{{}} : Bool}}:")


def s4body(v):
    hi = [val(v[f"b{k}"]) for k in range(16, 21)]
    mm = mk(lo16 + hi + [F] * 11)
    bb = enc(4, mm)
    goal = f"{{Utf8.v.second({bb[0]}, {bb[1]}) == True{{}} : Bool}}"
    lead = v["b18"] + 2 * v["b19"] + 4 * v["b20"]
    b16, b17 = v["b16"], v["b17"]
    args = ", ".join(lo16)
    if lead > 4:
        return f"Empty.absurd({goal}, false_true(h))"
    if lead == 0:
        if not b16 and not b17:
            return f"Empty.absurd({goal}, false_true(Equal.sym(Bool, True{{}}, False{{}}, ea)))"
        if b16 and not b17:
            return f"f0.second.a({args})"
        if b16 and b17:
            return f"f0.second.c({args})"
        return "{==}"
    if lead == 4:
        if b16 or b17:
            return f"Empty.absurd({goal}, false_true(h))"
        return f"f4.second({args})"
    return f"cont_low(({mm} >> 12n : U32))"


cases([f"b{k}" for k in range(16, 21)], s4body)
w("")
w(f"def v4.leaf({params(fb)}, +i: Nat, +rest: List<&2, U32>, ea: {{U32.is_lt({M4}, 65536) == False{{}} : Bool}}, +h: {{scalar({M4}) == True{{}} : Bool}}) -> {{Utf8.v.step(i, Utf8.encode.char({M4}, rest, False{{}}, False{{}}, False{{}})) == Some{{Utf8.V.Next{{rest, 4n}}}} : {MV}}}:")
w(f"  %Equal.sym({MV}, Utf8.v.step(i, {B[0]} <> {B[1]} <> {B[2]} <> {B[3]} <> rest), Some{{Utf8.v.tail({B[0]}, 4n, i, {B[1]} <> {B[2]} <> {B[3]} <> rest)}}, step_at(i, {B[0]}, {B[1]} <> {B[2]} <> {B[3]} <> rest, 3n, width4({', '.join(fb)}, h))) : {{_ == Some{{Utf8.V.Next{{rest, 4n}}}} : {MV}}}")
w(f"  %Equal.sym(Utf8.V, Utf8.v.tail({B[0]}, 4n, i, {B[1]} <> {B[2]} <> {B[3]} <> rest), Utf8.V.Next{{rest, 4n}}, tail4({B[0]}, i, {B[1]}, {B[2]}, {B[3]}, rest, second4({', '.join(fb)}, ea, h), cont_low(({M4} >> 6n : U32)), cont_low({M4}))) : {{Some{{_}} == Some{{Utf8.V.Next{{rest, 4n}}}} : {MV}}}")
w("  {==}")
w("")


def VAL(flags, width):
    return f"(m => {{Utf8.v.step(i, Utf8.encode.char(m, rest, {flags})) == Some{{Utf8.V.Next{{rest, {width}n}}}} : {MV}}})"


WID = "Bool.pick(Nat, one, 1n, Bool.pick(Nat, two, 2n, Bool.pick(Nat, three, 3n, 4n)))"
WIDC = "Bool.pick(Nat, U32.is_lt(c, 128), 1n, Bool.pick(Nat, U32.is_lt(c, 2048), 2n, Bool.pick(Nat, U32.is_lt(c, 65536), 3n, 4n)))"
WIDX = WIDC.replace("(c,", "(x,")
w(f"""def one.byte(+i: Nat, +c: U32, +rest: List<&2, U32>, e1: {{U32.is_lt(c, 128) == True{{}} : Bool}}) -> {{Utf8.v.step(i, c <> rest) == Some{{Utf8.V.Next{{rest, 1n}}}} : {MV}}}:
  %Equal.sym({MV}, Utf8.v.step(i, c <> rest), Some{{Utf8.v.tail(c, 1n, i, rest)}}, step_at(i, c, rest, 0n, width1(c, e1))) : {{_ == Some{{Utf8.V.Next{{rest, 1n}}}} : {MV}}}
  %Equal.sym(Utf8.V, Utf8.v.tail(c, 1n, i, rest), Utf8.V.Next{{rest, 1n}}, tail1(c, i, rest)) : {{Some{{_}} == Some{{Utf8.V.Next{{rest, 1n}}}} : {MV}}}
  {{==}}

# `invalid` steps over the bytes `encode` writes for a scalar value, all of
# them and no more, whichever width it is written in.
def vpoint.w(+i: Nat, +c: U32, +rest: List<&2, U32>, +h: {{scalar(c) == True{{}} : Bool}}, +one: Bool, e1: {{U32.is_lt(c, 128) == one : Bool}}, +two: Bool, e2: {{U32.is_lt(c, 2048) == two : Bool}}, +three: Bool, e3: {{U32.is_lt(c, 65536) == three : Bool}}) -> {{Utf8.v.step(i, Utf8.encode.char(c, rest, one, two, three)) == Some{{Utf8.V.Next{{rest, {WID}}}}} : {MV}}}:
  match one two three:
    case True{{}} _ _:
      one.byte(i, c, rest, e1)
    case False{{}} True{{}} _:
      two.tree(c, {VAL("False{}, True{}, three", 2)}, {lam(11, ["ea"], f"v2.leaf({xa[11]}, i, rest, three, ea)")}, e1, e2)
    case False{{}} False{{}} True{{}}:
      three.tree(c, {VAL("False{}, False{}, True{}", 3)}, {lam(16, ["ea", "eh"], f"v3.leaf({xa[16]}, i, rest, ea, eh)")}, e2, e3, h)
    case False{{}} False{{}} False{{}}:
      four.tree(c, {VAL("False{}, False{}, False{}", 4)}, {lam(21, ["ea", "eh"], f"v4.leaf({xa[21]}, i, rest, ea, eh)")}, e3, h)

def vpoint(+i: Nat, +c: U32, +rest: List<&2, U32>, h: {{scalar(c) == True{{}} : Bool}}) -> {{Utf8.v.step(i, Utf8.encode.char(c, rest, U32.is_lt(c, 128), U32.is_lt(c, 2048), U32.is_lt(c, 65536))) == Some{{Utf8.V.Next{{rest, {WIDC}}}}} : {MV}}}:
  vpoint.w(i, c, rest, h, U32.is_lt(c, 128), {{==}}, U32.is_lt(c, 2048), {{==}}, U32.is_lt(c, 65536), {{==}})

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
def decodes(+s: String, h: {{scalars(s) == True{{}} : Bool}}) -> {{Utf8.decode(Utf8.encode(s)) == s : String}}:
  go(s, List.length(&2, U32, Utf8.encode(s)), len_le(s), h)

# With fuel for every character, `invalid` walks the bytes to their end and
# finds nothing wrong.
def vgo(s: String, +i: Nat, f: Nat, le: {{Nat.is_le(String.length(s), f) == True{{}} : Bool}}, +h: {{scalars(s) == True{{}} : Bool}}) -> {{Utf8.v.go(f, i, Utf8.v.step(i, Utf8.encode(s))) == None{{}} : Maybe<&2, String>}}:
  match s f:
    case SNil{{}} 0n:
      {{==}}
    case SNil{{}} 1n+p:
      {{==}}
    case SCon{{Chr{{+x}}, +t}} 0n:
      Empty.absurd({{Utf8.v.go(0n, i, Utf8.v.step(i, Utf8.encode(SCon{{Chr{{x}}, t}}))) == None{{}} : Maybe<&2, String>}}, false_true(le))
    case SCon{{Chr{{+x}}, +t}} 1n+p:
      %Equal.sym({MV}, Utf8.v.step(i, Utf8.encode.char(x, Utf8.encode(t), U32.is_lt(x, 128), U32.is_lt(x, 2048), U32.is_lt(x, 65536))), Some{{Utf8.V.Next{{Utf8.encode(t), {WIDX}}}}}, vpoint(i, x, Utf8.encode(t), and_left(scalar(x), scalars(t), h))) : {{Utf8.v.go(1n+p, i, _) == None{{}} : Maybe<&2, String>}}
      vgo(t, Nat.add(i, {WIDX}), p, le, and_right(scalar(x), scalars(t), h))

# What the port writes for a string of scalar values, read back as the
# store reads a file as text — `read_to_string`, which refuses bytes that
# are not UTF-8 — is that string.
def reads_back(+s: String, +h: {{scalars(s) == True{{}} : Bool}}) -> {{Store.utf8.of(Utf8.encode(s)) == Done{{s}} : Result<&2, &2, String, String>}}:
  %Equal.sym(Maybe<&2, String>, Utf8.invalid(Utf8.encode(s)), None{{}}, vgo(s, 0n, List.length(&2, U32, Utf8.encode(s)), len_le(s), h)) : {{Maybe.default(&2, Result<&2, &2, String, String>, Maybe.map(&2, String, Result<&2, &2, String, String>, m => Fail{{m}}, _), Done{{Utf8.decode(Utf8.encode(s))}}) == Done{{s}} : Result<&2, &2, String, String>}}
  %Equal.sym(String, Utf8.decode(Utf8.encode(s)), s, decodes(s, h)) : {{Done{{_}} == Done{{s}} : Result<&2, &2, String, String>}}
  {{==}}

def main() -> Unit:
  Unit{{}}
""")

import sys as _sys
(Path(_sys.argv[1]) if len(_sys.argv) > 1 else ROOT / "utf8_lemmas.bend").write_text("\n".join(out) + "\n")
