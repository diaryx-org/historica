# What Base's `Map` and `Set` hold. A `Map` is a crit-bit trie: each node
# names a bit position, a key goes low or high by its bit there, and a leaf
# holds one key. `Map.set` seeks the leaf a key's bits lead to, and either
# writes the value there (the same key) or splices a node in at the first
# bit where the two keys differ (`Map.diff`). The lemmas below say what that
# amounts to: a lookup after a write finds what was written, and every other
# key finds what it found before, in every map `Map.new` and `Map.set`
# build; and so a set built from a list holds exactly the list's strings.
#
# The proof goes down to the bit. A key's bit at a position is a bit of one
# of its characters, or whether it has a character there at all, and
# `Map.diff` is the first position two keys' bits differ at: they agree at
# every position before it (`agree_below_diff`) and differ at it
# (`split_at_diff`). That is a fact about `U32`'s shifts, masks and `xor`,
# which Base defines over `Word`, a list of bits, so it is proven by
# induction down a word. Above that, the trie is read through plain
# definitions — the leaf a key's bits lead to, and what a key finds — and
# the invariant every map `Map.set` builds keeps is stated as a type
# (`Wf`): every key below a node's low side has its bit clear there, every
# key below its high side has it set, and all its keys agree at every
# position before it.
import Base
import ./string_lemmas.bend as Str

# Nat
# ---

def add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def add_succ(n: Nat, -m: Nat) -> {Nat.add(n, 1n+m) == 1n+Nat.add(n, m) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, m) : {1n+Nat.add(p, 1n+m) == 1n+_ : Nat}
      {==}

def nat_disc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def succ_zero(-n: Nat, e: {1n+n == 0n : Nat}) -> Empty:
  %e : {nat_disc(_) : Type}
  Unit{}

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def succ_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, x => pred(x), 1n+a, 1n+b, e)

def cmp_eq(a: Nat, b: Nat, e: {Nat.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, Str.lt_eq(e))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, Str.gt_eq(e))
    case 1n+p 1n+q:
      %cmp_eq(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

# `a < b` and `b < c` give `a < c`.
def lt_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_lt(a, b) == True{} : Bool}, bc: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n _:
      Empty.absurd({Nat.is_lt(0n, c) == True{} : Bool}, Str.false_true(ab))
    case 1n+p 0n _:
      Empty.absurd({Nat.is_lt(1n+p, c) == True{} : Bool}, Str.false_true(ab))
    case _ 1n+q 0n:
      Empty.absurd({Nat.is_lt(a, 0n) == True{} : Bool}, Str.false_true(bc))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 1n+r:
      lt_trans(p, q, r, ab, bc)

# `a < b` and `b <= c` give `a < c`.
def lt_le(a: Nat, b: Nat, c: Nat, ab: {Nat.is_lt(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n _:
      Empty.absurd({Nat.is_lt(0n, c) == True{} : Bool}, Str.false_true(ab))
    case 1n+p 0n _:
      Empty.absurd({Nat.is_lt(1n+p, c) == True{} : Bool}, Str.false_true(ab))
    case _ 1n+q 0n:
      Empty.absurd({Nat.is_lt(a, 0n) == True{} : Bool}, Str.false_true(bc))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 1n+r:
      lt_le(p, q, r, ab, bc)

# Not `a < b` is `b <= a`.
def not_lt(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, Str.true_false(e))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      not_lt(p, q, e)

def lt_of(-a: Nat, -b: Nat, ec: {Nat.cmp(a, b) == LT{} : Cmp}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(a, b), LT{}, ec) : {Cmp.is_lt(_) == True{} : Bool}
  {==}

# `a <= b` is `a < b` or `a` is `b`.
def le_cases.go(+a: Nat, +b: Nat, c: Cmp, ec: {Nat.cmp(a, b) == c : Cmp}, e: {Cmp.is_le(c) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool} | {a == b : Nat}:
  match c:
    case LT{}:
      Inl{lt_of(a, b, ec)}
    case EQ{}:
      Inr{cmp_eq(a, b, ec)}
    case GT{}:
      Empty.absurd({Nat.is_lt(a, b) == True{} : Bool} | {a == b : Nat}, Str.false_true(e))

def le_cases(+a: Nat, +b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool} | {a == b : Nat}:
  le_cases.go(a, b, Nat.cmp(a, b), {==}, e)

# Bits of a word
# --------------

# The bit at `k` of a word, counting from the least significant; past its
# width a word has none set.
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

def pad_bit(p: Nat, t: Word(p), j: Nat) -> {wbit(1n+p, Word.shr.pad(p, t), j) == wbit(p, t, j) : Bool}:
  match p:
    case 0n:
      match j:
        case 0n:
          {==}
        case 1n+i:
          {==}
    case 1n+q:
      match t j:
        case WCon{c, u} 0n:
          {==}
        case WCon{c, u} 1n+i:
          pad_bit(q, u, i)

# A shift right moves every bit down one.
def shr_bit(n: Nat, w: Word(n), j: Nat) -> {wbit(n, Word.shr(n, w), j) == wbit(n, w, 1n+j) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          pad_bit(p, t, j)

def ws(w: Word(32n), k: Nat) -> Word(32n):
  match k:
    case 0n:
      w
    case 1n+j:
      Word.shr(32n, ws(w, j))

def shrn_is(+w: Word(32n), k: Nat) -> {U32.shrn(U32{w}, k) == U32{ws(w, k)} : U32}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(U32, U32.shrn(U32{w}, j), U32{ws(w, j)}, shrn_is(w, j)) : {U32.shr(_) == U32{ws(w, 1n+j)} : U32}
      {==}

def ws_bit(+w: Word(32n), k: Nat, +i: Nat) -> {wbit(32n, ws(w, k), i) == wbit(32n, w, Nat.add(i, k)) : Bool}:
  match k:
    case 0n:
      %Equal.sym(Nat, Nat.add(i, 0n), i, add_zero(i)) : {wbit(32n, w, i) == wbit(32n, w, _) : Bool}
      {==}
    case 1n++j:
      %Equal.sym(Bool, wbit(32n, Word.shr(32n, ws(w, j)), i), wbit(32n, ws(w, j), 1n+i), shr_bit(32n, ws(w, j), i)) : {_ == wbit(32n, w, Nat.add(i, 1n+j)) : Bool}
      %Equal.sym(Bool, wbit(32n, ws(w, j), 1n+i), wbit(32n, w, Nat.add(1n+i, j)), ws_bit(w, j, 1n+i)) : {_ == wbit(32n, w, Nat.add(i, 1n+j)) : Bool}
      %add_succ(i, j) : {wbit(32n, w, _) == wbit(32n, w, Nat.add(i, 1n+j)) : Bool}
      {==}

def and_zero(n: Nat, t: Word(n)) -> {Word.cmp(n, Word.and(n, t, Word.zero(n)), Word.zero(n)) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match t:
        case WCon{True{}, r}:
          %Equal.sym(Cmp, Word.cmp(p, Word.and(p, r, Word.zero(p)), Word.zero(p)), EQ{}, and_zero(p, r)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
          {==}
        case WCon{False{}, r}:
          %Equal.sym(Cmp, Word.cmp(p, Word.and(p, r, Word.zero(p)), Word.zero(p)), EQ{}, and_zero(p, r)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
          {==}

def head_bit(v: Word(32n)) -> {Map.bit.u(U32{v}, 0n) == wbit(32n, v, 0n) : Bool}:
  match v:
    case WCon{True{}, t}:
      %Equal.sym(Cmp, Word.cmp(31n, Word.and(31n, t, Word.zero(31n)), Word.zero(31n)), EQ{}, and_zero(31n, t)) : {Bool.not(Cmp.is_eq(Word.cmp.fin(True{}, False{}, _))) == True{} : Bool}
      {==}
    case WCon{False{}, t}:
      %Equal.sym(Cmp, Word.cmp(31n, Word.and(31n, t, Word.zero(31n)), Word.zero(31n)), EQ{}, and_zero(31n, t)) : {Bool.not(Cmp.is_eq(Word.cmp.fin(False{}, False{}, _))) == False{} : Bool}
      {==}

# `Map.bit.u(x, k)` — shift, mask with 1, compare with 0 — is bit `k`.
def bitu_is(+w: Word(32n), +k: Nat) -> {Map.bit.u(U32{w}, k) == wbit(32n, w, k) : Bool}:
  %Equal.sym(U32, U32.shrn(U32{w}, k), U32{ws(w, k)}, shrn_is(w, k)) : {U32.is_ne(U32.and(_, 1), 0) == wbit(32n, w, k) : Bool}
  %Equal.sym(Bool, Map.bit.u(U32{ws(w, k)}, 0n), wbit(32n, ws(w, k), 0n), head_bit(ws(w, k))) : {_ == wbit(32n, w, k) : Bool}
  ws_bit(w, k, 0n)

def xor_bit(n: Nat, a: Word(n), b: Word(n), k: Nat) -> {wbit(n, Word.xor(n, a, b), k) == Bool.xor(wbit(n, a, k), wbit(n, b, k)) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b k:
        case WCon{x, at} WCon{y, bt} 0n:
          {==}
        case WCon{x, at} WCon{y, bt} 1n+j:
          xor_bit(p, at, bt, j)

# The top of a word: one past its highest bit set, and 0 for a word with
# none.
def wtop.fin(r: Nat, h: Bool) -> Nat:
  match r:
    case 0n:
      match h:
        case False{}:
          0n
        case True{}:
          1n
    case 1n+q:
      2n+q

def wtop(n: Nat, w: Word(n)) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match w:
        case WCon{h, t}:
          wtop.fin(wtop(p, t), h)

def top_zero.at(r: Nat, h: Bool, e: {Nat.is_le(wtop.fin(r, h), 0n) == True{} : Bool}) -> {h == False{} : Bool}:
  match r:
    case 0n:
      match h:
        case False{}:
          {==}
        case True{}:
          Empty.absurd({True{} == False{} : Bool}, Str.false_true(e))
    case 1n+q:
      Empty.absurd({h == False{} : Bool}, Str.false_true(e))

def top_step(r: Nat, h: Bool, j: Nat, e: {Nat.is_le(wtop.fin(r, h), 1n+j) == True{} : Bool}) -> {Nat.is_le(r, j) == True{} : Bool}:
  match r:
    case 0n:
      match j:
        case 0n:
          {==}
        case 1n+i:
          {==}
    case 1n+q:
      e

# No bit is set at or above the top.
def above_top(n: Nat, w: Word(n), k: Nat, e: {Nat.is_le(wtop(n, w), k) == True{} : Bool}) -> {wbit(n, w, k) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      match w k:
        case WCon{h, +t} 0n:
          top_zero.at(wtop(p, t), h, e)
        case WCon{h, +t} 1n++j:
          above_top(p, t, j, top_step(wtop(p, t), h, j, e))

def top_one(r: Nat, h: Bool, e: {wtop.fin(r, h) == 1n : Nat}) -> {h == True{} : Bool}:
  match r:
    case 0n:
      match h:
        case False{}:
          Empty.absurd({False{} == True{} : Bool}, succ_zero(0n, Equal.sym(Nat, 0n, 1n, e)))
        case True{}:
          {==}
    case 1n++q:
      Empty.absurd({h == True{} : Bool}, succ_zero(q, succ_inj(1n+q, 0n, e)))

def top_two(r: Nat, h: Bool, i: Nat, e: {wtop.fin(r, h) == 2n+i : Nat}) -> {r == 1n+i : Nat}:
  match r:
    case 0n:
      match h:
        case False{}:
          Empty.absurd({0n == 1n+i : Nat}, succ_zero(1n+i, Equal.sym(Nat, 0n, 2n+i, e)))
        case True{}:
          Empty.absurd({0n == 1n+i : Nat}, succ_zero(i, Equal.sym(Nat, 0n, 1n+i, succ_inj(0n, 1n+i, e))))
    case 1n++q:
      succ_inj(1n+q, 1n+i, e)

# The bit just under the top is set.
def top_set(n: Nat, w: Word(n), m: Nat, e: {wtop(n, w) == 1n+m : Nat}) -> {wbit(n, w, m) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({wbit(0n, w, m) == True{} : Bool}, succ_zero(m, Equal.sym(Nat, 0n, 1n+m, e)))
    case 1n++p:
      match w m:
        case WCon{h, +t} 0n:
          top_one(wtop(p, t), h, e)
        case WCon{h, +t} 1n++i:
          top_set(p, t, i, top_two(wtop(p, t), h, i, e))

def iz(r: Nat) -> Bool:
  match r:
    case 0n:
      True{}
    case 1n+q:
      False{}

def zero_fin(c: Cmp, r: Nat, h: Bool, ih: {Cmp.is_eq(c) == iz(r) : Bool}) -> {Cmp.is_eq(Word.cmp.fin(h, False{}, c)) == iz(wtop.fin(r, h)) : Bool}:
  match c:
    case LT{}:
      match r:
        case 0n:
          Empty.absurd({Cmp.is_eq(Word.cmp.fin(h, False{}, LT{})) == iz(wtop.fin(0n, h)) : Bool}, Str.false_true(ih))
        case 1n+q:
          {==}
    case EQ{}:
      match r:
        case 0n:
          match h:
            case False{}:
              {==}
            case True{}:
              {==}
        case 1n+q:
          Empty.absurd({Cmp.is_eq(Word.cmp.fin(h, False{}, EQ{})) == iz(wtop.fin(1n+q, h)) : Bool}, Str.true_false(ih))
    case GT{}:
      match r:
        case 0n:
          Empty.absurd({Cmp.is_eq(Word.cmp.fin(h, False{}, GT{})) == iz(wtop.fin(0n, h)) : Bool}, Str.false_true(ih))
        case 1n+q:
          {==}

# A word is zero exactly where its top is.
def zero_is(n: Nat, w: Word(n)) -> {Cmp.is_eq(Word.cmp(n, w, Word.zero(n))) == iz(wtop(n, w)) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      match w:
        case WCon{h, +t}:
          zero_fin(Word.cmp(p, t, Word.zero(p)), wtop(p, t), h, zero_is(p, t))

def pad_top(p: Nat, t: Word(p)) -> {wtop(1n+p, Word.shr.pad(p, t)) == wtop(p, t) : Nat}:
  match p:
    case 0n:
      {==}
    case 1n++q:
      match t:
        case WCon{c, +u}:
          %Equal.sym(Nat, wtop(1n+q, Word.shr.pad(q, u)), wtop(q, u), pad_top(q, u)) : {wtop.fin(_, c) == wtop.fin(wtop(q, u), c) : Nat}
          {==}

def pred_fin(r: Nat, h: Bool) -> {pred(wtop.fin(r, h)) == r : Nat}:
  match r:
    case 0n:
      match h:
        case False{}:
          {==}
        case True{}:
          {==}
    case 1n+q:
      {==}

# A shift right takes one off the top.
def shr_top(n: Nat, w: Word(n)) -> {wtop(n, Word.shr(n, w)) == pred(wtop(n, w)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      match w:
        case WCon{h, +t}:
          %Equal.sym(Nat, pred(wtop.fin(wtop(p, t), h)), wtop(p, t), pred_fin(wtop(p, t), h)) : {wtop(1n+p, Word.shr.pad(p, t)) == _ : Nat}
          pad_top(p, t)

def top_le.fin(r: Nat, h: Bool, p: Nat, e: {Nat.is_le(r, p) == True{} : Bool}) -> {Nat.is_le(wtop.fin(r, h), 1n+p) == True{} : Bool}:
  match r:
    case 0n:
      match h:
        case False{}:
          {==}
        case True{}:
          match p:
            case 0n:
              {==}
            case 1n+q:
              {==}
    case 1n+q:
      e

def top_le(n: Nat, w: Word(n)) -> {Nat.is_le(wtop(n, w), n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      match w:
        case WCon{h, +t}:
          top_le.fin(wtop(p, t), h, p, top_le(p, t))

def le_zero(r: Nat, e: {Nat.is_le(r, 0n) == True{} : Bool}) -> {r == 0n : Nat}:
  match r:
    case 0n:
      {==}
    case 1n+q:
      Empty.absurd({1n+q == 0n : Nat}, Str.false_true(e))

def msb_le(-g: Nat, -a: Nat, -m: Nat, top: {a == m : Nat}, e: {Nat.is_le(1n+m, 1n+g) == True{} : Bool}) -> {Nat.is_le(a, g) == True{} : Bool}:
  %Equal.sym(Nat, a, m, top) : {Nat.is_le(_, g) == True{} : Bool}
  e

def msb_step(g: Nat, +w: Word(32n), r: Nat, er: {wtop(32n, w) == r : Nat}, e: {Nat.is_le(r, 1n+g) == True{} : Bool}, ih: @w2:Word(32n) -> {Nat.is_le(wtop(32n, w2), g) == True{} : Bool} -> {Map.msb.u(g, U32{w2}) == wtop(32n, w2) : Nat}) -> {Map.msb.u.if(g, U32{w}, iz(r)) == r : Nat}:
  match r:
    case 0n:
      {==}
    case 1n++m:
      +top = Equal.trans(Nat, wtop(32n, Word.shr(32n, w)), pred(wtop(32n, w)), m, shr_top(32n, w), Equal.cong(Nat, Nat, x => pred(x), wtop(32n, w), 1n+m, er))
      %Equal.sym(Nat, Map.msb.u(g, U32{Word.shr(32n, w)}), wtop(32n, Word.shr(32n, w)), ih(Word.shr(32n, w), msb_le(g, wtop(32n, Word.shr(32n, w)), m, top, e))) : {Nat.add(1n, _) == 1n+m : Nat}
      %Equal.sym(Nat, wtop(32n, Word.shr(32n, w)), m, top) : {Nat.add(1n, _) == 1n+m : Nat}
      {==}

# `Map.msb.u(32n, x)` is the top of `x`.
def msb_is(f: Nat, +w: Word(32n), e: {Nat.is_le(wtop(32n, w), f) == True{} : Bool}) -> {Map.msb.u(f, U32{w}) == wtop(32n, w) : Nat}:
  match f:
    case 0n:
      %Equal.sym(Nat, wtop(32n, w), 0n, le_zero(wtop(32n, w), e)) : {0n == _ : Nat}
      {==}
    case 1n++g:
      %Equal.sym(Bool, Cmp.is_eq(Word.cmp(32n, w, Word.zero(32n))), iz(wtop(32n, w)), zero_is(32n, w)) : {Map.msb.u.if(g, U32{w}, _) == wtop(32n, w) : Nat}
      msb_step(g, w, wtop(32n, w), {==}, e, w2 => e2 => msb_is(g, w2, e2))

# More Nat
# --------

def sub_zero(n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def lt_zero(q: Nat, e: {Nat.is_lt(q, 0n) == True{} : Bool}) -> Empty:
  match q:
    case 0n:
      Str.false_true(e)
    case 1n+p:
      Str.false_true(e)

def sub0(n: Nat) -> {Nat.sub(0n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

def le_weak(q: Nat, m: Nat, e: {Nat.is_le(q, m) == True{} : Bool}) -> {Nat.is_le(q, 1n+m) == True{} : Bool}:
  match q m:
    case 0n _:
      {==}
    case 1n+qp 0n:
      Empty.absurd({Nat.is_le(1n+qp, 1n) == True{} : Bool}, Str.false_true(e))
    case 1n+qp 1n+mp:
      le_weak(qp, mp, e)

def le0(x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# `q <= m` fails only past `m`, which is `1 + m` and more.
def gt_split(q: Nat, m: Nat, e: {Nat.is_le(q, m) == False{} : Bool}) -> {q == Nat.add(1n+m, Nat.sub(q, 1n+m)) : Nat}:
  match q m:
    case 0n _:
      Empty.absurd({0n == Nat.add(1n+m, Nat.sub(0n, 1n+m)) : Nat}, Str.true_false(Equal.trans(Bool, True{}, Nat.is_le(0n, m), False{}, Equal.sym(Bool, Nat.is_le(0n, m), True{}, le0(m)), e)))
    case 1n++r 0n:
      %Equal.sym(Nat, Nat.sub(r, 0n), r, sub_zero(r)) : {1n+r == 1n+_ : Nat}
      {==}
    case 1n++r 1n+mp:
      %gt_split(r, mp, e) : {1n+r == 1n+_ : Nat}
      {==}

def lt_succ(q: Nat, m: Nat, e: {Nat.is_lt(q, 1n+m) == True{} : Bool}) -> {Nat.is_le(q, m) == True{} : Bool}:
  match q m:
    case 0n _:
      le0(m)
    case 1n++qp 0n:
      Empty.absurd({Nat.is_le(1n+qp, 0n) == True{} : Bool}, lt_zero(qp, e))
    case 1n+qp 1n+mp:
      lt_succ(qp, mp, e)

def lt_sub(+q: Nat, m: Nat, t: Nat, e: {Nat.is_lt(q, Nat.sub(1n+m, t)) == True{} : Bool}) -> {Nat.is_le(q, m) == True{} : Bool}:
  match m t:
    case _ 0n:
      lt_succ(q, m, e)
    case 0n 1n++tp:
      Empty.absurd({Nat.is_le(q, 0n) == True{} : Bool}, lt_zero(q, Equal.trans(Bool, Nat.is_lt(q, 0n), Nat.is_lt(q, Nat.sub(0n, tp)), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(q, x), 0n, Nat.sub(0n, tp), Equal.sym(Nat, Nat.sub(0n, tp), 0n, sub0(tp))), e)))
    case 1n++mp 1n+tp:
      le_weak(q, mp, lt_sub(q, mp, tp, e))

def pos_sub(n: Nat, t: Nat, e: {Nat.is_lt(0n, Nat.sub(1n+n, t)) == True{} : Bool}) -> {Nat.is_le(t, n) == True{} : Bool}:
  match n t:
    case _ 0n:
      le0(n)
    case 0n 1n++tp:
      Empty.absurd({Nat.is_le(1n+tp, 0n) == True{} : Bool}, lt_zero(0n, Equal.trans(Bool, Nat.is_lt(0n, 0n), Nat.is_lt(0n, Nat.sub(0n, tp)), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(0n, x), 0n, Nat.sub(0n, tp), Equal.sym(Nat, Nat.sub(0n, tp), 0n, sub0(tp))), e)))
    case 1n+np 1n+tp:
      pos_sub(np, tp, e)

def lt_sub_pred(b: Nat, m: Nat, t: Nat, e: {Nat.is_lt(1n+b, Nat.sub(1n+m, t)) == True{} : Bool}) -> {Nat.is_lt(b, Nat.sub(m, t)) == True{} : Bool}:
  match m t:
    case _ 0n:
      %Equal.sym(Nat, Nat.sub(m, 0n), m, sub_zero(m)) : {Nat.is_lt(b, _) == True{} : Bool}
      e
    case 0n 1n++tp:
      Empty.absurd({Nat.is_lt(b, Nat.sub(0n, 1n+tp)) == True{} : Bool}, lt_zero(1n+b, Equal.trans(Bool, Nat.is_lt(1n+b, 0n), Nat.is_lt(1n+b, Nat.sub(0n, tp)), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(1n+b, x), 0n, Nat.sub(0n, tp), Equal.sym(Nat, Nat.sub(0n, tp), 0n, sub0(tp))), e)))
    case 1n+mp 1n+tp:
      lt_sub_pred(b, mp, tp, e)

def below_sub(b: Nat, +n: Nat, +t: Nat, e: {Nat.is_lt(b, Nat.sub(1n+n, t)) == True{} : Bool}) -> {Nat.is_le(t, Nat.sub(n, b)) == True{} : Bool}:
  match b n:
    case 0n _:
      %Equal.sym(Nat, Nat.sub(n, 0n), n, sub_zero(n)) : {Nat.is_le(t, _) == True{} : Bool}
      pos_sub(n, t, e)
    case 1n++bp 0n:
      Empty.absurd({Nat.is_le(t, Nat.sub(0n, 1n+bp)) == True{} : Bool}, lt_zero(bp, Equal.trans(Bool, Nat.is_lt(bp, 0n), Nat.is_lt(bp, Nat.sub(0n, t)), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(bp, x), 0n, Nat.sub(0n, t), Equal.sym(Nat, Nat.sub(0n, t), 0n, sub0(t))), lt_sub_pred(bp, 0n, t, e))))
    case 1n++bp 1n++np:
      below_sub(bp, np, t, lt_sub_pred(bp, 1n+np, t, e))

def sub_le(n: Nat, m: Nat) -> {Nat.is_le(Nat.sub(n, m), n) == True{} : Bool}:
  match n m:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      le_refl(1n+p)
    case 1n++p 1n++q:
      le_weak(Nat.sub(p, q), p, sub_le(p, q))

def sub_succ_l(x: Nat, n: Nat, e: {Nat.is_le(x, n) == True{} : Bool}) -> {Nat.sub(1n+n, x) == 1n+Nat.sub(n, x) : Nat}:
  match x n:
    case 0n _:
      %Equal.sym(Nat, Nat.sub(n, 0n), n, sub_zero(n)) : {1n+n == 1n+_ : Nat}
      {==}
    case 1n++xp 0n:
      Empty.absurd({Nat.sub(1n, 1n+xp) == 1n+Nat.sub(0n, 1n+xp) : Nat}, Str.false_true(e))
    case 1n+xp 1n+np:
      sub_succ_l(xp, np, e)

def sub_self(n: Nat) -> {Nat.sub(n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      sub_self(p)

# Twice subtracted from `n`, `m` comes back.
def sub_sub(m: Nat, n: Nat, e: {Nat.is_le(m, n) == True{} : Bool}) -> {Nat.sub(n, Nat.sub(n, m)) == m : Nat}:
  match m n:
    case 0n 0n:
      {==}
    case 0n 1n++np:
      %Equal.sym(Nat, Nat.sub(np, np), 0n, sub_self(np)) : {_ == 0n : Nat}
      {==}
    case 1n++mp 0n:
      Empty.absurd({Nat.sub(0n, Nat.sub(0n, 1n+mp)) == 1n+mp : Nat}, Str.false_true(e))
    case 1n++mp 1n++np:
      %Equal.sym(Nat, Nat.sub(1n+np, Nat.sub(np, mp)), 1n+Nat.sub(np, Nat.sub(np, mp)), sub_succ_l(Nat.sub(np, mp), np, sub_le(np, mp))) : {_ == 1n+mp : Nat}
      %Equal.sym(Nat, Nat.sub(np, Nat.sub(np, mp)), mp, sub_sub(mp, np, e)) : {1n+_ == 1n+mp : Nat}
      {==}

# Bools
# -----

def xor_false(x: Bool, y: Bool, e: {Bool.xor(x, y) == False{} : Bool}) -> {x == y : Bool}:
  match x y:
    case False{} False{}:
      {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, Str.true_false(e))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, Str.true_false(e))
    case True{} True{}:
      {==}

def xor_true(x: Bool, y: Bool, e: {Bool.xor(x, y) == True{} : Bool}) -> {x == Bool.not(y) : Bool}:
  match x y:
    case False{} False{}:
      Empty.absurd({False{} == True{} : Bool}, Str.false_true(e))
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      Empty.absurd({True{} == False{} : Bool}, Str.false_true(e))

# A word whose `xor` with another is zero is that word.
def fin_zero_c(h: Bool, c: Cmp, e: {Cmp.is_eq(Word.cmp.fin(h, False{}, c)) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, Str.false_true(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, Str.false_true(e))

def fin_zero_h(h: Bool, e: {Cmp.is_eq(Word.cmp.fin(h, False{}, EQ{})) == True{} : Bool}) -> {h == False{} : Bool}:
  match h:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Str.false_true(e))

def xor_bits_eq(x: Bool, y: Bool, e: {Bool.xor(x, y) == False{} : Bool}) -> {Word.cmp.fin(x, y, EQ{}) == EQ{} : Cmp}:
  match x y:
    case False{} False{}:
      {==}
    case False{} True{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, Str.true_false(e))
    case True{} False{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, Str.true_false(e))
    case True{} True{}:
      {==}

def xor_zero(n: Nat, a: Word(n), b: Word(n), +e: {Cmp.is_eq(Word.cmp(n, Word.xor(n, a, b), Word.zero(n))) == True{} : Bool}) -> {Word.cmp(n, a, b) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          +rest = fin_zero_c(Bool.xor(x, y), Word.cmp(p, Word.xor(p, at, bt), Word.zero(p)), e)
          +tail = xor_zero(p, at, bt, Equal.trans(Bool, Cmp.is_eq(Word.cmp(p, Word.xor(p, at, bt), Word.zero(p))), Cmp.is_eq(EQ{}), True{}, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), Word.cmp(p, Word.xor(p, at, bt), Word.zero(p)), EQ{}, rest), {==}))
          +hd = fin_zero_h(Bool.xor(x, y), Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(Bool.xor(x, y), False{}, EQ{})), Cmp.is_eq(Word.cmp.fin(Bool.xor(x, y), False{}, Word.cmp(p, Word.xor(p, at, bt), Word.zero(p)))), True{}, Equal.cong(Cmp, Bool, c => Cmp.is_eq(Word.cmp.fin(Bool.xor(x, y), False{}, c)), EQ{}, Word.cmp(p, Word.xor(p, at, bt), Word.zero(p)), Equal.sym(Cmp, Word.cmp(p, Word.xor(p, at, bt), Word.zero(p)), EQ{}, rest)), e))
          %Equal.sym(Cmp, Word.cmp(p, at, bt), EQ{}, tail) : {Word.cmp.fin(x, y, _) == EQ{} : Cmp}
          xor_bits_eq(x, y, hd)

# Bits of a key
# -------------

def sb(r: String & Bool) -> Bool:
  (s, b) = r
  b

# A key's bit at a position, as `Map.bit` reads it: at `33 * i` whether the
# key has an `i`th character, and at `33 * i + 1 + b` bit `31 - b` of it.
def bv(key: String, pos: Nat) -> Bool:
  sb(Map.bit(key, pos))

# The bit at an offset of one character.
def sc(r: Char & Bool) -> Bool:
  (c, b) = r
  b

def cb(c: Char, o: Nat) -> Bool:
  sc(Map.bit.chr(c, o))

def go_back(key: String, ci: Nat, off: Nat) -> {Map.bit.go(key, ci, off) == (key, sb(Map.bit.go(key, ci, off))) : String & Bool}:
  match key ci:
    case SNil{} _:
      {==}
    case SCon{Chr{x}, t} 0n:
      match off:
        case 0n:
          {==}
        case 1n+b:
          {==}
    case SCon{+c, +t} 1n++j:
      %Equal.sym(String & Bool, Map.bit.go(t, j, off), (t, sb(Map.bit.go(t, j, off))), go_back(t, j, off)) : {Map.bit.go.rec(c, _) == (SCon{c, t}, sb(Map.bit.go.rec(c, _))) : String & Bool}
      {==}

def at_back(+key: String, co: Nat & Nat) -> {Map.bit.at(key, co) == (key, sb(Map.bit.at(key, co))) : String & Bool}:
  match co:
    case (ci, off):
      go_back(key, ci, off)

# `Map.bit` hands the key back beside its bit.
def bit_back(+key: String, +pos: Nat) -> {Map.bit(key, pos) == (key, bv(key, pos)) : String & Bool}:
  at_back(key, Nat.divmod(pos, 33n))

def at_nil(co: Nat & Nat) -> {sb(Map.bit.at(SNil{}, co)) == False{} : Bool}:
  match co:
    case (ci, off):
      {==}

def bv_nil(+pos: Nat) -> {bv(SNil{}, pos) == False{} : Bool}:
  at_nil(Nat.divmod(pos, 33n))

def go_small(n: Nat, m: Nat, -d: Nat, +r: Nat, e: {Nat.is_le(n, m) == True{} : Bool}) -> {Nat.divmod.go(n, m, d, r) == (d, Nat.add(n, r)) : Nat & Nat}:
  match n m:
    case 0n _:
      {==}
    case 1n++np 0n:
      Empty.absurd({Nat.divmod.go(1n+np, 0n, d, r) == (d, Nat.add(1n+np, r)) : Nat & Nat}, Str.false_true(e))
    case 1n++np 1n++mp:
      %Equal.sym(Nat & Nat, Nat.divmod.go(np, mp, d, 1n+r), (d, Nat.add(np, 1n+r)), go_small(np, mp, d, 1n+r, e)) : {_ == (d, 1n+Nat.add(np, r)) : Nat & Nat}
      %add_succ(np, r) : {(d, Nat.add(np, 1n+r)) == (d, _) : Nat & Nat}
      {==}

def sb_chr(t: String, r: Char & Bool) -> {sb(Map.bit.go.chr(t, r)) == sc(r) : Bool}:
  match r:
    case (c, b):
      {==}

# Below 33 a position is a bit of the first character.
def bv_head(+c: Char, +t: String, +q: Nat, e: {Nat.is_le(q, 32n) == True{} : Bool}) -> {bv(SCon{c, t}, q) == cb(c, q) : Bool}:
  %Equal.sym(Nat & Nat, Nat.divmod.go(q, 32n, 0n, 0n), (0n, Nat.add(q, 0n)), go_small(q, 32n, 0n, 0n, e)) : {sb(Map.bit.at(SCon{c, t}, _)) == cb(c, q) : Bool}
  %Equal.sym(Bool, sb(Map.bit.go.chr(t, Map.bit.chr(c, Nat.add(q, 0n)))), sc(Map.bit.chr(c, Nat.add(q, 0n))), sb_chr(t, Map.bit.chr(c, Nat.add(q, 0n)))) : {_ == cb(c, q) : Bool}
  %Equal.sym(Nat, Nat.add(q, 0n), q, add_zero(q)) : {sc(Map.bit.chr(c, _)) == cb(c, q) : Bool}
  {==}

def dshift(r: Nat & Nat) -> Nat & Nat:
  (a, b) = r
  (1n+a, b)

def go_shift(n: Nat, m: Nat, d: Nat, r: Nat) -> {Nat.divmod.go(n, m, 1n+d, r) == dshift(Nat.divmod.go(n, m, d, r)) : Nat & Nat}:
  match n m:
    case 0n _:
      {==}
    case 1n+np 0n:
      go_shift(np, r, 1n+d, 0n)
    case 1n+np 1n+mp:
      go_shift(np, mp, d, 1n+r)

def sb_rec(c: Char, r: String & Bool) -> {sb(Map.bit.go.rec(c, r)) == sb(r) : Bool}:
  match r:
    case (s, b):
      {==}

def at_shift(c: Char, t: String, co: Nat & Nat) -> {sb(Map.bit.at(SCon{c, t}, dshift(co))) == sb(Map.bit.at(t, co)) : Bool}:
  match co:
    case (ci, off):
      sb_rec(c, Map.bit.go(t, ci, off))

# From 33 on, a position is a position of the rest of the key.
def bv_high(+c: Char, +t: String, +q: Nat) -> {bv(SCon{c, t}, Nat.add(33n, q)) == bv(t, q) : Bool}:
  %Equal.sym(Nat & Nat, Nat.divmod.go(q, 32n, 1n, 0n), dshift(Nat.divmod.go(q, 32n, 0n, 0n)), go_shift(q, 32n, 0n, 0n)) : {sb(Map.bit.at(SCon{c, t}, _)) == bv(t, q) : Bool}
  at_shift(c, t, Nat.divmod.go(q, 32n, 0n, 0n))

# Bit `1 + b` of a character is bit `31 - b` of its code.
def cb_bit(+w: Word(32n), +b: Nat) -> {cb(Chr{U32{w}}, 1n+b) == wbit(32n, w, Nat.sub(31n, b)) : Bool}:
  bitu_is(w, Nat.sub(31n, b))

# Where two keys part
# -------------------

def lt_diff33(-q: Nat, -d: Nat, e: {Nat.is_lt(Nat.add(33n, q), Nat.add(33n, d)) == True{} : Bool}) -> {Nat.is_lt(q, d) == True{} : Bool}:
  e

def b3.eq(+q: Nat, +w: Word(32n), +xt: String, +yt: String, s: Bool, +es: {Nat.is_le(q, 32n) == s : Bool}, e: {Nat.is_lt(q, Nat.add(33n, Map.diff(xt, yt))) == True{} : Bool}, ih: @q2:Nat -> {Nat.is_lt(q2, Map.diff(xt, yt)) == True{} : Bool} -> {bv(xt, q2) == bv(yt, q2) : Bool}) -> {bv(SCon{Chr{U32{w}}, xt}, q) == bv(SCon{Chr{U32{w}}, yt}, q) : Bool}:
  match s:
    case True{}:
      Equal.trans(Bool, bv(SCon{Chr{U32{w}}, xt}, q), cb(Chr{U32{w}}, q), bv(SCon{Chr{U32{w}}, yt}, q), bv_head(Chr{U32{w}}, xt, q, es), Equal.sym(Bool, bv(SCon{Chr{U32{w}}, yt}, q), cb(Chr{U32{w}}, q), bv_head(Chr{U32{w}}, yt, q, es)))
    case False{}:
      +q2 = Nat.sub(q, 33n)
      +split = gt_split(q, 32n, es)
      +lt = lt_diff33(q2, Map.diff(xt, yt), Equal.trans(Bool, Nat.is_lt(Nat.add(33n, q2), Nat.add(33n, Map.diff(xt, yt))), Nat.is_lt(q, Nat.add(33n, Map.diff(xt, yt))), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(x, Nat.add(33n, Map.diff(xt, yt))), Nat.add(33n, q2), q, Equal.sym(Nat, q, Nat.add(33n, q2), split)), e))
      %Equal.sym(Nat, q, Nat.add(33n, q2), split) : {bv(SCon{Chr{U32{w}}, xt}, _) == bv(SCon{Chr{U32{w}}, yt}, _) : Bool}
      %Equal.sym(Bool, bv(SCon{Chr{U32{w}}, xt}, Nat.add(33n, q2)), bv(xt, q2), bv_high(Chr{U32{w}}, xt, q2)) : {_ == bv(SCon{Chr{U32{w}}, yt}, Nat.add(33n, q2)) : Bool}
      %Equal.sym(Bool, bv(SCon{Chr{U32{w}}, yt}, Nat.add(33n, q2)), bv(yt, q2), bv_high(Chr{U32{w}}, yt, q2)) : {bv(xt, q2) == _ : Bool}
      ih(q2, lt)

def b3.chr(+wa: Word(32n), +wb: Word(32n), q: Nat, e: {Nat.is_lt(q, Nat.sub(33n, wtop(32n, Word.xor(32n, wa, wb)))) == True{} : Bool}) -> {cb(Chr{U32{wa}}, q) == cb(Chr{U32{wb}}, q) : Bool}:
  match q:
    case 0n:
      {==}
    case 1n++b:
      +z = Word.xor(32n, wa, wb)
      +k = Nat.sub(31n, b)
      +le = below_sub(1n+b, 32n, wtop(32n, z), e)
      +zb = above_top(32n, z, k, le)
      +xb = Equal.trans(Bool, Bool.xor(wbit(32n, wa, k), wbit(32n, wb, k)), wbit(32n, z, k), False{}, Equal.sym(Bool, wbit(32n, z, k), Bool.xor(wbit(32n, wa, k), wbit(32n, wb, k)), xor_bit(32n, wa, wb, k)), zb)
      +same = xor_false(wbit(32n, wa, k), wbit(32n, wb, k), xb)
      Equal.trans(Bool, cb(Chr{U32{wa}}, 1n+b), wbit(32n, wa, k), cb(Chr{U32{wb}}, 1n+b), cb_bit(wa, b), Equal.trans(Bool, wbit(32n, wa, k), wbit(32n, wb, k), cb(Chr{U32{wb}}, 1n+b), same, Equal.sym(Bool, cb(Chr{U32{wb}}, 1n+b), wbit(32n, wb, k), cb_bit(wb, b))))

def b3.ne(+wa: Word(32n), +wb: Word(32n), +xt: String, +yt: String, +q: Nat, e: {Nat.is_lt(q, Map.diff.chr(U32.xor(U32{wa}, U32{wb}))) == True{} : Bool}) -> {bv(SCon{Chr{U32{wa}}, xt}, q) == bv(SCon{Chr{U32{wb}}, yt}, q) : Bool}:
  +z = Word.xor(32n, wa, wb)
  +t = wtop(32n, z)
  +msb = msb_is(32n, z, top_le(32n, z))
  +e1 = Equal.trans(Bool, Nat.is_lt(q, Nat.sub(33n, t)), Nat.is_lt(q, Nat.sub(33n, Map.msb.u(32n, U32{z}))), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(q, Nat.sub(33n, x)), t, Map.msb.u(32n, U32{z}), Equal.sym(Nat, Map.msb.u(32n, U32{z}), t, msb)), e)
  +qle = lt_sub(q, 32n, t, e1)
  %Equal.sym(Bool, bv(SCon{Chr{U32{wa}}, xt}, q), cb(Chr{U32{wa}}, q), bv_head(Chr{U32{wa}}, xt, q, qle)) : {_ == bv(SCon{Chr{U32{wb}}, yt}, q) : Bool}
  %Equal.sym(Bool, bv(SCon{Chr{U32{wb}}, yt}, q), cb(Chr{U32{wb}}, q), bv_head(Chr{U32{wb}}, yt, q, qle)) : {cb(Chr{U32{wa}}, q) == _ : Bool}
  b3.chr(wa, wb, q, e1)

def b3.fin(c: Cmp, +wa: Word(32n), +wb: Word(32n), +xt: String, +yt: String, +q: Nat, ec: {Word.cmp(32n, wa, wb) == c : Cmp}, +e: {Nat.is_lt(q, Map.diff.fin(xt, yt, (Map.diff.chr(U32.xor(U32{wa}, U32{wb})), Cmp.is_eq(c)))) == True{} : Bool}, ih: @q2:Nat -> {Nat.is_lt(q2, Map.diff(xt, yt)) == True{} : Bool} -> {bv(xt, q2) == bv(yt, q2) : Bool}) -> {bv(SCon{Chr{U32{wa}}, xt}, q) == bv(SCon{Chr{U32{wb}}, yt}, q) : Bool}:
  match c:
    case LT{}:
      b3.ne(wa, wb, xt, yt, q, e)
    case EQ{}:
      %Str.word_eq(32n, wa, wb, ec) : {bv(SCon{Chr{U32{wa}}, xt}, q) == bv(SCon{Chr{U32{_}}, yt}, q) : Bool}
      b3.eq(q, wa, xt, yt, Nat.is_le(q, 32n), {==}, e, ih)
    case GT{}:
      b3.ne(wa, wb, xt, yt, q, e)

# Two keys agree at every position before `Map.diff` of them.
def agree_below_diff(a: String, b: String, +q: Nat, +e: {Nat.is_lt(q, Map.diff(a, b)) == True{} : Bool}) -> {bv(a, q) == bv(b, q) : Bool}:
  match a b:
    case SNil{} SNil{}:
      Empty.absurd({bv(SNil{}, q) == bv(SNil{}, q) : Bool}, lt_zero(q, e))
    case SNil{} SCon{h, t}:
      Empty.absurd({bv(SNil{}, q) == bv(SCon{h, t}, q) : Bool}, lt_zero(q, e))
    case SCon{h, t} SNil{}:
      Empty.absurd({bv(SCon{h, t}, q) == bv(SNil{}, q) : Bool}, lt_zero(q, e))
    case SCon{Chr{U32{+wa}}, +xt} SCon{Chr{U32{+wb}}, +yt}:
      b3.fin(Word.cmp(32n, wa, wb), wa, wb, xt, yt, q, {==}, e, q2 => e2 => agree_below_diff(xt, yt, q2, e2))

def eq_rec(h1: Char, h2: Char, rr: (String & String) & Cmp) -> {String.eq.fin(String.cmp.rec(h1, h2, rr)) == String.eq.fin(rr) : Bool}:
  match rr:
    case (ab, c):
      match ab:
        case (a2, b2):
          {==}

def b1.ne(+wa: Word(32n), +wb: Word(32n), +xt: String, +yt: String, r: Nat, +er: {wtop(32n, Word.xor(32n, wa, wb)) == r : Nat}, ne: {Word.cmp(32n, wa, wb) == EQ{} : Cmp} -> Empty) -> {bv(SCon{Chr{U32{wa}}, xt}, Map.diff.chr(U32.xor(U32{wa}, U32{wb}))) == Bool.not(bv(SCon{Chr{U32{wb}}, yt}, Map.diff.chr(U32.xor(U32{wa}, U32{wb})))) : Bool}:
  match r:
    case 0n:
      +z = Word.xor(32n, wa, wb)
      +isz = Equal.trans(Bool, Cmp.is_eq(Word.cmp(32n, z, Word.zero(32n))), iz(wtop(32n, z)), True{}, zero_is(32n, z), Equal.cong(Nat, Bool, x => iz(x), wtop(32n, z), 0n, er))
      Empty.absurd({bv(SCon{Chr{U32{wa}}, xt}, Map.diff.chr(U32.xor(U32{wa}, U32{wb}))) == Bool.not(bv(SCon{Chr{U32{wb}}, yt}, Map.diff.chr(U32.xor(U32{wa}, U32{wb})))) : Bool}, ne(xor_zero(32n, wa, wb, isz)))
    case 1n++m:
      +z = Word.xor(32n, wa, wb)
      +msb = Equal.trans(Nat, Map.msb.u(32n, U32{z}), wtop(32n, z), 1n+m, msb_is(32n, z, top_le(32n, z)), er)
      +m31 = Equal.trans(Bool, Nat.is_le(1n+m, 32n), Nat.is_le(wtop(32n, z), 32n), True{}, Equal.cong(Nat, Bool, x => Nat.is_le(x, 32n), 1n+m, wtop(32n, z), Equal.sym(Nat, wtop(32n, z), 1n+m, er)), top_le(32n, z))
      +o = sub_succ_l(m, 31n, m31)
      +k = Nat.sub(31n, m)
      +ole = sub_le(31n, m)
      +bit = Equal.trans(Bool, Bool.xor(wbit(32n, wa, m), wbit(32n, wb, m)), wbit(32n, z, m), True{}, Equal.sym(Bool, wbit(32n, z, m), Bool.xor(wbit(32n, wa, m), wbit(32n, wb, m)), xor_bit(32n, wa, wb, m)), top_set(32n, z, m, er))
      %Equal.sym(Nat, Map.msb.u(32n, U32{z}), 1n+m, msb) : {bv(SCon{Chr{U32{wa}}, xt}, Nat.sub(33n, _)) == Bool.not(bv(SCon{Chr{U32{wb}}, yt}, Nat.sub(33n, _))) : Bool}
      %Equal.sym(Nat, Nat.sub(32n, m), 1n+k, o) : {bv(SCon{Chr{U32{wa}}, xt}, _) == Bool.not(bv(SCon{Chr{U32{wb}}, yt}, _)) : Bool}
      %Equal.sym(Bool, bv(SCon{Chr{U32{wa}}, xt}, 1n+k), cb(Chr{U32{wa}}, 1n+k), bv_head(Chr{U32{wa}}, xt, 1n+k, ole)) : {_ == Bool.not(bv(SCon{Chr{U32{wb}}, yt}, 1n+k)) : Bool}
      %Equal.sym(Bool, bv(SCon{Chr{U32{wb}}, yt}, 1n+k), cb(Chr{U32{wb}}, 1n+k), bv_head(Chr{U32{wb}}, yt, 1n+k, ole)) : {cb(Chr{U32{wa}}, 1n+k) == Bool.not(_) : Bool}
      %Equal.sym(Bool, cb(Chr{U32{wa}}, 1n+k), wbit(32n, wa, Nat.sub(31n, k)), cb_bit(wa, k)) : {_ == Bool.not(cb(Chr{U32{wb}}, 1n+k)) : Bool}
      %Equal.sym(Bool, cb(Chr{U32{wb}}, 1n+k), wbit(32n, wb, Nat.sub(31n, k)), cb_bit(wb, k)) : {wbit(32n, wa, Nat.sub(31n, k)) == Bool.not(_) : Bool}
      %Equal.sym(Nat, Nat.sub(31n, k), m, sub_sub(m, 31n, m31)) : {wbit(32n, wa, _) == Bool.not(wbit(32n, wb, _)) : Bool}
      xor_true(wbit(32n, wa, m), wbit(32n, wb, m), bit)

def b1.fin(c: Cmp, +wa: Word(32n), +wb: Word(32n), +xt: String, +yt: String, +ec: {Word.cmp(32n, wa, wb) == c : Cmp}, e: {String.eq.fin(String.cmp.fin(xt, yt, ((Chr{U32{wa}}, Chr{U32{wb}}), c))) == False{} : Bool}, ih: {String.eq(xt, yt) == False{} : Bool} -> {bv(xt, Map.diff(xt, yt)) == Bool.not(bv(yt, Map.diff(xt, yt))) : Bool}) -> {bv(SCon{Chr{U32{wa}}, xt}, Map.diff.fin(xt, yt, (Map.diff.chr(U32.xor(U32{wa}, U32{wb})), Cmp.is_eq(c)))) == Bool.not(bv(SCon{Chr{U32{wb}}, yt}, Map.diff.fin(xt, yt, (Map.diff.chr(U32.xor(U32{wa}, U32{wb})), Cmp.is_eq(c))))) : Bool}:
  match c:
    case LT{}:
      b1.ne(wa, wb, xt, yt, wtop(32n, Word.xor(32n, wa, wb)), {==}, x => Str.lt_eq(Equal.trans(Cmp, LT{}, Word.cmp(32n, wa, wb), EQ{}, Equal.sym(Cmp, Word.cmp(32n, wa, wb), LT{}, ec), x)))
    case EQ{}:
      +e2 = Equal.trans(Bool, String.eq(xt, yt), String.eq.fin(String.cmp.rec(Chr{U32{wa}}, Chr{U32{wb}}, String.cmp(xt, yt))), False{}, Equal.sym(Bool, String.eq.fin(String.cmp.rec(Chr{U32{wa}}, Chr{U32{wb}}, String.cmp(xt, yt))), String.eq(xt, yt), eq_rec(Chr{U32{wa}}, Chr{U32{wb}}, String.cmp(xt, yt))), e)
      +d = Map.diff(xt, yt)
      %Equal.sym(Bool, bv(SCon{Chr{U32{wa}}, xt}, Nat.add(33n, d)), bv(xt, d), bv_high(Chr{U32{wa}}, xt, d)) : {_ == Bool.not(bv(SCon{Chr{U32{wb}}, yt}, Nat.add(33n, d))) : Bool}
      %Equal.sym(Bool, bv(SCon{Chr{U32{wb}}, yt}, Nat.add(33n, d)), bv(yt, d), bv_high(Chr{U32{wb}}, yt, d)) : {bv(xt, d) == Bool.not(_) : Bool}
      ih(e2)
    case GT{}:
      b1.ne(wa, wb, xt, yt, wtop(32n, Word.xor(32n, wa, wb)), {==}, x => Str.gt_eq(Equal.trans(Cmp, GT{}, Word.cmp(32n, wa, wb), EQ{}, Equal.sym(Cmp, Word.cmp(32n, wa, wb), GT{}, ec), x)))

# Two keys that are not one key differ at `Map.diff` of them.
def split_at_diff(a: String, b: String, +e: {String.eq(a, b) == False{} : Bool}) -> {bv(a, Map.diff(a, b)) == Bool.not(bv(b, Map.diff(a, b))) : Bool}:
  match a b:
    case SNil{} SNil{}:
      Empty.absurd({False{} == True{} : Bool}, Str.true_false(e))
    case SNil{} SCon{Chr{x}, t}:
      {==}
    case SCon{Chr{x}, t} SNil{}:
      {==}
    case SCon{Chr{U32{+wa}}, +xt} SCon{Chr{U32{+wb}}, +yt}:
      b1.fin(Word.cmp(32n, wa, wb), wa, wb, xt, yt, {==}, e, x => split_at_diff(xt, yt, x))

def main() -> IO(Unit):
  IO.print("ok")
