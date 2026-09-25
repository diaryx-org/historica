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

def cmp_eq(+a: Nat, +b: Nat, +e: {Nat.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Nat}:
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
def lt_trans(+a: Nat, +b: Nat, +c: Nat, +ab: {Nat.is_lt(a, b) == True{} : Bool}, +bc: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
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
def lt_le(+a: Nat, +b: Nat, +c: Nat, +ab: {Nat.is_lt(a, b) == True{} : Bool}, +bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
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
def not_lt(a: Nat, b: Nat, +e: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
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
def le_cases.go(+a: Nat, +b: Nat, c: Cmp, +ec: {Nat.cmp(a, b) == c : Cmp}, e: {Cmp.is_le(c) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool} | {a == b : Nat}:
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

def pad_bit(p: Nat, t: Word(p), +j: Nat) -> {wbit(1n+p, Word.shr.pad(p, t), j) == wbit(p, t, j) : Bool}:
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

def ws(+w: Word(32n), k: Nat) -> Word(32n):
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

def xor_bit(n: Nat, +a: Word(n), b: Word(n), k: Nat) -> {wbit(n, Word.xor(n, a, b), k) == Bool.xor(wbit(n, a, k), wbit(n, b, k)) : Bool}:
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

def top_zero.at(r: Nat, +h: Bool, +e: {Nat.is_le(wtop.fin(r, h), 0n) == True{} : Bool}) -> {h == False{} : Bool}:
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
def above_top(n: Nat, w: Word(n), k: Nat, +e: {Nat.is_le(wtop(n, w), k) == True{} : Bool}) -> {wbit(n, w, k) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      match w k:
        case WCon{h, +t} 0n:
          top_zero.at(wtop(p, t), h, e)
        case WCon{h, +t} 1n++j:
          above_top(p, t, j, top_step(wtop(p, t), h, j, e))

def top_one(r: Nat, +h: Bool, +e: {wtop.fin(r, h) == 1n : Nat}) -> {h == True{} : Bool}:
  match r:
    case 0n:
      match h:
        case False{}:
          Empty.absurd({False{} == True{} : Bool}, succ_zero(0n, Equal.sym(Nat, 0n, 1n, e)))
        case True{}:
          {==}
    case 1n++q:
      Empty.absurd({h == True{} : Bool}, succ_zero(q, succ_inj(1n+q, 0n, e)))

def top_two(r: Nat, h: Bool, +i: Nat, +e: {wtop.fin(r, h) == 2n+i : Nat}) -> {r == 1n+i : Nat}:
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
def top_set(n: Nat, +w: Word(n), +m: Nat, +e: {wtop(n, w) == 1n+m : Nat}) -> {wbit(n, w, m) == True{} : Bool}:
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

def zero_fin(c: Cmp, +r: Nat, +h: Bool, +ih: {Cmp.is_eq(c) == iz(r) : Bool}) -> {Cmp.is_eq(Word.cmp.fin(h, False{}, c)) == iz(wtop.fin(r, h)) : Bool}:
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

def msb_step(+g: Nat, +w: Word(32n), r: Nat, er: {wtop(32n, w) == r : Nat}, e: {Nat.is_le(r, 1n+g) == True{} : Bool}, ih: @w2:Word(32n) -> {Nat.is_le(wtop(32n, w2), g) == True{} : Bool} -> {Map.msb.u(g, U32{w2}) == wtop(32n, w2) : Nat}) -> {Map.msb.u.if(g, U32{w}, iz(r)) == r : Nat}:
  match r:
    case 0n:
      {==}
    case 1n++m:
      +top = Equal.trans(Nat, wtop(32n, Word.shr(32n, w)), pred(wtop(32n, w)), m, shr_top(32n, w), Equal.cong(Nat, Nat, x => pred(x), wtop(32n, w), 1n+m, er))
      %Equal.sym(Nat, Map.msb.u(g, U32{Word.shr(32n, w)}), wtop(32n, Word.shr(32n, w)), ih(Word.shr(32n, w), msb_le(g, wtop(32n, Word.shr(32n, w)), m, top, e))) : {Nat.add(1n, _) == 1n+m : Nat}
      %Equal.sym(Nat, wtop(32n, Word.shr(32n, w)), m, top) : {Nat.add(1n, _) == 1n+m : Nat}
      {==}

# `Map.msb.u(32n, x)` is the top of `x`.
def msb_is(f: Nat, +w: Word(32n), +e: {Nat.is_le(wtop(32n, w), f) == True{} : Bool}) -> {Map.msb.u(f, U32{w}) == wtop(32n, w) : Nat}:
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

def lt_zero(q: Nat, +e: {Nat.is_lt(q, 0n) == True{} : Bool}) -> Empty:
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

def le_weak(q: Nat, m: Nat, +e: {Nat.is_le(q, m) == True{} : Bool}) -> {Nat.is_le(q, 1n+m) == True{} : Bool}:
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
def gt_split(q: Nat, +m: Nat, +e: {Nat.is_le(q, m) == False{} : Bool}) -> {q == Nat.add(1n+m, Nat.sub(q, 1n+m)) : Nat}:
  match q m:
    case 0n _:
      Empty.absurd({0n == Nat.add(1n+m, Nat.sub(0n, 1n+m)) : Nat}, Str.true_false(Equal.trans(Bool, True{}, Nat.is_le(0n, m), False{}, Equal.sym(Bool, Nat.is_le(0n, m), True{}, le0(m)), e)))
    case 1n++r 0n:
      %Equal.sym(Nat, Nat.sub(r, 0n), r, sub_zero(r)) : {1n+r == 1n+_ : Nat}
      {==}
    case 1n++r 1n+mp:
      %gt_split(r, mp, e) : {1n+r == 1n+_ : Nat}
      {==}

def lt_succ(q: Nat, +m: Nat, +e: {Nat.is_lt(q, 1n+m) == True{} : Bool}) -> {Nat.is_le(q, m) == True{} : Bool}:
  match q m:
    case 0n _:
      le0(m)
    case 1n++qp 0n:
      Empty.absurd({Nat.is_le(1n+qp, 0n) == True{} : Bool}, lt_zero(qp, e))
    case 1n+qp 1n+mp:
      lt_succ(qp, mp, e)

def lt_sub(+q: Nat, +m: Nat, t: Nat, +e: {Nat.is_lt(q, Nat.sub(1n+m, t)) == True{} : Bool}) -> {Nat.is_le(q, m) == True{} : Bool}:
  match m t:
    case _ 0n:
      lt_succ(q, m, e)
    case 0n 1n++tp:
      Empty.absurd({Nat.is_le(q, 0n) == True{} : Bool}, lt_zero(q, Equal.trans(Bool, Nat.is_lt(q, 0n), Nat.is_lt(q, Nat.sub(0n, tp)), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(q, x), 0n, Nat.sub(0n, tp), Equal.sym(Nat, Nat.sub(0n, tp), 0n, sub0(tp))), e)))
    case 1n++mp 1n+tp:
      le_weak(q, mp, lt_sub(q, mp, tp, e))

def pos_sub(+n: Nat, t: Nat, +e: {Nat.is_lt(0n, Nat.sub(1n+n, t)) == True{} : Bool}) -> {Nat.is_le(t, n) == True{} : Bool}:
  match n t:
    case _ 0n:
      le0(n)
    case 0n 1n++tp:
      Empty.absurd({Nat.is_le(1n+tp, 0n) == True{} : Bool}, lt_zero(0n, Equal.trans(Bool, Nat.is_lt(0n, 0n), Nat.is_lt(0n, Nat.sub(0n, tp)), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(0n, x), 0n, Nat.sub(0n, tp), Equal.sym(Nat, Nat.sub(0n, tp), 0n, sub0(tp))), e)))
    case 1n+np 1n+tp:
      pos_sub(np, tp, e)

def lt_sub_pred(+b: Nat, +m: Nat, t: Nat, +e: {Nat.is_lt(1n+b, Nat.sub(1n+m, t)) == True{} : Bool}) -> {Nat.is_lt(b, Nat.sub(m, t)) == True{} : Bool}:
  match m t:
    case _ 0n:
      %Equal.sym(Nat, Nat.sub(m, 0n), m, sub_zero(m)) : {Nat.is_lt(b, _) == True{} : Bool}
      e
    case 0n 1n++tp:
      Empty.absurd({Nat.is_lt(b, Nat.sub(0n, 1n+tp)) == True{} : Bool}, lt_zero(1n+b, Equal.trans(Bool, Nat.is_lt(1n+b, 0n), Nat.is_lt(1n+b, Nat.sub(0n, tp)), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(1n+b, x), 0n, Nat.sub(0n, tp), Equal.sym(Nat, Nat.sub(0n, tp), 0n, sub0(tp))), e)))
    case 1n+mp 1n+tp:
      lt_sub_pred(b, mp, tp, e)

def below_sub(b: Nat, +n: Nat, +t: Nat, +e: {Nat.is_lt(b, Nat.sub(1n+n, t)) == True{} : Bool}) -> {Nat.is_le(t, Nat.sub(n, b)) == True{} : Bool}:
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

def sub_succ_l(x: Nat, +n: Nat, +e: {Nat.is_le(x, n) == True{} : Bool}) -> {Nat.sub(1n+n, x) == 1n+Nat.sub(n, x) : Nat}:
  match x n:
    case 0n _:
      %Equal.sym(Nat, Nat.sub(n, 0n), n, sub_zero(n)) : {1n+n == 1n+_ : Nat}
      {==}
    case 1n++xp 0n:
      Empty.absurd({Nat.sub(1n, 1n+xp) == 1n+Nat.sub(0n, 1n+xp) : Nat}, Str.false_true(e))
    case 1n+xp 1n+np:
      sub_succ_l(xp, np, e)

def sub_self(+n: Nat) -> {Nat.sub(n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      sub_self(p)

# Twice subtracted from `n`, `m` comes back.
def sub_sub(m: Nat, n: Nat, +e: {Nat.is_le(m, n) == True{} : Bool}) -> {Nat.sub(n, Nat.sub(n, m)) == m : Nat}:
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

def xor_false(x: Bool, y: Bool, +e: {Bool.xor(x, y) == False{} : Bool}) -> {x == y : Bool}:
  match x y:
    case False{} False{}:
      {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, Str.true_false(e))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, Str.true_false(e))
    case True{} True{}:
      {==}

def xor_true(x: Bool, y: Bool, +e: {Bool.xor(x, y) == True{} : Bool}) -> {x == Bool.not(y) : Bool}:
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
def fin_zero_c(h: Bool, c: Cmp, +e: {Cmp.is_eq(Word.cmp.fin(h, False{}, c)) == True{} : Bool}) -> {c == EQ{} : Cmp}:
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

def xor_bits_eq(x: Bool, y: Bool, +e: {Bool.xor(x, y) == False{} : Bool}) -> {Word.cmp.fin(x, y, EQ{}) == EQ{} : Cmp}:
  match x y:
    case False{} False{}:
      {==}
    case False{} True{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, Str.true_false(e))
    case True{} False{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, Str.true_false(e))
    case True{} True{}:
      {==}

def xor_zero(n: Nat, +a: Word(n), b: Word(n), +e: {Cmp.is_eq(Word.cmp(n, Word.xor(n, a, b), Word.zero(n))) == True{} : Bool}) -> {Word.cmp(n, a, b) == EQ{} : Cmp}:
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

def go_back(key: String, ci: Nat, +off: Nat) -> {Map.bit.go(key, ci, off) == (key, sb(Map.bit.go(key, ci, off))) : String & Bool}:
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

def go_small(n: Nat, m: Nat, -d: Nat, +r: Nat, +e: {Nat.is_le(n, m) == True{} : Bool}) -> {Nat.divmod.go(n, m, d, r) == (d, Nat.add(n, r)) : Nat & Nat}:
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

def go_shift(n: Nat, m: Nat, +d: Nat, +r: Nat) -> {Nat.divmod.go(n, m, 1n+d, r) == dshift(Nat.divmod.go(n, m, d, r)) : Nat & Nat}:
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
def split_at_diff(+a: String, b: String, +e: {String.eq(a, b) == False{} : Bool}) -> {bv(a, Map.diff(a, b)) == Bool.not(bv(b, Map.diff(a, b))) : Bool}:
  match a b:
    case SNil{} SNil{}:
      Empty.absurd({False{} == True{} : Bool}, Str.true_false(e))
    case SNil{} SCon{Chr{x}, t}:
      {==}
    case SCon{Chr{x}, t} SNil{}:
      {==}
    case SCon{Chr{U32{+wa}}, +xt} SCon{Chr{U32{+wb}}, +yt}:
      b1.fin(Word.cmp(32n, wa, wb), wa, wb, xt, yt, {==}, e, x => split_at_diff(xt, yt, x))

# The trie, read plainly
# ----------------------

# The key at the leaf a key's bits lead to.
def reach(-V: Data, m: Map<&2, V>, +j: String) -> Maybe<&2, String>:
  match m:
    case MTip{}:
      None{}
    case MLeaf{k, v}:
      Some{k}
    case MNode{pos, lo, hi}:
      Bool.pick(Maybe<&2, String>, bv(j, pos), reach(V, hi, j), reach(V, lo, j))

# What a key finds: the value at the leaf its bits lead to, where that
# leaf's key is it.
def found(-V: Data, m: Map<&2, V>, +j: String) -> Maybe<&2, V>:
  match m:
    case MTip{}:
      None{}
    case MLeaf{k, v}:
      Bool.pick(Maybe<&2, V>, String.eq(j, k), Some{v}, None{})
    case MNode{pos, lo, hi}:
      Bool.pick(Maybe<&2, V>, bv(j, pos), found(V, hi, j), found(V, lo, j))

# Whether a key is at some leaf.
def mem(-V: Data, m: Map<&2, V>, +a: String) -> Bool:
  match m:
    case MTip{}:
      False{}
    case MLeaf{k, v}:
      String.eq(a, k)
    case MNode{pos, lo, hi}:
      Bool.or(mem(V, lo, a), mem(V, hi, a))

# `Map.put`: the value written at the leaf the key's bits lead to.
def cput(-V: Data, m: Map<&2, V>, +k: String, +x: V) -> Map<&2, V>:
  match m:
    case MTip{}:
      MLeaf{k, x}
    case MLeaf{k1, v}:
      MLeaf{k1, x}
    case MNode{+pos, +lo, +hi}:
      Bool.pick(Map<&2, V>, bv(k, pos), MNode{pos, lo, cput(V, hi, k, x)}, MNode{pos, cput(V, lo, k, x), hi})

# `Map.ins.splice`: a node at `p` holding the new leaf on the side of its
# bit there, and what was here on the other.
def csplice(-V: Data, +p: Nat, +k: String, +x: V, +rest: Map<&2, V>) -> Map<&2, V>:
  Bool.pick(Map<&2, V>, bv(k, p), MNode{p, rest, MLeaf{k, x}}, MNode{p, MLeaf{k, x}, rest})

# `Map.ins`: down the key's bits past every node before `p`, and spliced in
# there.
def cins(-V: Data, m: Map<&2, V>, +k: String, +x: V, +p: Nat) -> Map<&2, V>:
  match m:
    case MTip{}:
      MLeaf{k, x}
    case MLeaf{k1, v}:
      csplice(V, p, k, x, MLeaf{k1, v})
    case MNode{+q, +lo, +hi}:
      Bool.pick(Map<&2, V>, Nat.is_lt(q, p), Bool.pick(Map<&2, V>, bv(k, q), MNode{q, lo, cins(V, hi, k, x, p)}, MNode{q, cins(V, lo, k, x, p), hi}), csplice(V, p, k, x, MNode{q, lo, hi}))

def cfin(-V: Data, +m: Map<&2, V>, +k: String, +x: V, +k0: String, c: Cmp) -> Map<&2, V>:
  match c:
    case LT{}:
      cins(V, m, k, x, Map.diff(k, k0))
    case EQ{}:
      cput(V, m, k, x)
    case GT{}:
      cins(V, m, k, x, Map.diff(k, k0))

def cset.of(-V: Data, m: Map<&2, V>, +k: String, +x: V, r: Maybe<&2, String>) -> Map<&2, V>:
  match r:
    case None{}:
      MLeaf{k, x}
    case Some{+k0}:
      cfin(V, m, k, x, k0, String.order(k, k0))

# `Map.set`: the leaf the key's bits lead to, and then its value written
# there where the leaf's key is it, and otherwise a node spliced in at the
# first position the two keys part.
def cset(-V: Data, +m: Map<&2, V>, +k: String, +x: V) -> Map<&2, V>:
  cset.of(V, m, k, x, reach(V, m, k))

# Base's functions, read plainly
# ------------------------------

def cmp_fin_back(c: Cmp, +h1: Char, +h2: Char, +t1: String, +t2: String, ih: {String.cmp(t1, t2) == ((t1, t2), String.order(t1, t2)) : (String & String) & Cmp}) -> {String.cmp.fin(t1, t2, ((h1, h2), c)) == ((SCon{h1, t1}, SCon{h2, t2}), String.order.fin(String.cmp.fin(t1, t2, ((h1, h2), c)))) : (String & String) & Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      %Equal.sym((String & String) & Cmp, String.cmp(t1, t2), ((t1, t2), String.order(t1, t2)), ih) : {String.cmp.rec(h1, h2, _) == ((SCon{h1, t1}, SCon{h2, t2}), String.order.fin(String.cmp.rec(h1, h2, _))) : (String & String) & Cmp}
      {==}
    case GT{}:
      {==}

# `String.cmp` hands both strings back beside its verdict.
def cmp_back(a: String, b: String) -> {String.cmp(a, b) == ((a, b), String.order(a, b)) : (String & String) & Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      {==}
    case SCon{h, t} SNil{}:
      {==}
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      cmp_fin_back(U32.cmp(x, y), Chr{x}, Chr{y}, t1, t2, cmp_back(t1, t2))

def seek_node(-V: Data, +pos: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +key: String, b: Bool, +eb: {bv(key, pos) == b : Bool}, ilo: {Map.seek(&2, V, lo, key) == (lo, key, reach(V, lo, key)) : Map<&2, V> & String & Maybe<&2, String>}, ihi: {Map.seek(&2, V, hi, key) == (hi, key, reach(V, hi, key)) : Map<&2, V> & String & Maybe<&2, String>}) -> {Map.seek.bit(&2, V, lo, hi, pos, (key, bv(key, pos))) == (MNode{pos, lo, hi}, key, Bool.pick(Maybe<&2, String>, bv(key, pos), reach(V, hi, key), reach(V, lo, key))) : Map<&2, V> & String & Maybe<&2, String>}:
  match b:
    case False{}:
      %Equal.sym(Bool, bv(key, pos), False{}, eb) : {Map.seek.bit(&2, V, lo, hi, pos, (key, _)) == (MNode{pos, lo, hi}, key, Bool.pick(Maybe<&2, String>, _, reach(V, hi, key), reach(V, lo, key))) : Map<&2, V> & String & Maybe<&2, String>}
      %Equal.sym(Map<&2, V> & String & Maybe<&2, String>, Map.seek(&2, V, lo, key), (lo, key, reach(V, lo, key)), ilo) : {Map.lo(&2, V, String & Maybe<&2, String>, pos, hi, _) == (MNode{pos, lo, hi}, key, reach(V, lo, key)) : Map<&2, V> & String & Maybe<&2, String>}
      {==}
    case True{}:
      %Equal.sym(Bool, bv(key, pos), True{}, eb) : {Map.seek.bit(&2, V, lo, hi, pos, (key, _)) == (MNode{pos, lo, hi}, key, Bool.pick(Maybe<&2, String>, _, reach(V, hi, key), reach(V, lo, key))) : Map<&2, V> & String & Maybe<&2, String>}
      %Equal.sym(Map<&2, V> & String & Maybe<&2, String>, Map.seek(&2, V, hi, key), (hi, key, reach(V, hi, key)), ihi) : {Map.hi(&2, V, String & Maybe<&2, String>, pos, lo, _) == (MNode{pos, lo, hi}, key, reach(V, hi, key)) : Map<&2, V> & String & Maybe<&2, String>}
      {==}

# `Map.seek` hands the map and the key back beside the leaf it reached.
def seek_is(-V: Data, m: Map<&2, V>, +key: String) -> {Map.seek(&2, V, m, key) == (m, key, reach(V, m, key)) : Map<&2, V> & String & Maybe<&2, String>}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k, +v}:
      {==}
    case MNode{+pos, +lo, +hi}:
      %Equal.sym(String & Bool, Map.bit(key, pos), (key, bv(key, pos)), bit_back(key, pos)) : {Map.seek.bit(&2, V, lo, hi, pos, _) == (MNode{pos, lo, hi}, key, reach(V, MNode{pos, lo, hi}, key)) : Map<&2, V> & String & Maybe<&2, String>}
      seek_node(V, pos, lo, hi, key, bv(key, pos), {==}, seek_is(V, lo, key), seek_is(V, hi, key))

def put_node(-V: Data, +pos: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +key: String, +x: V, b: Bool, +eb: {bv(key, pos) == b : Bool}, ilo: {Map.put(&2, V, lo, key, x) == cput(V, lo, key, x) : Map<&2, V>}, ihi: {Map.put(&2, V, hi, key, x) == cput(V, hi, key, x) : Map<&2, V>}) -> {Map.put.bit(&2, V, x, pos, lo, hi, (key, bv(key, pos))) == Bool.pick(Map<&2, V>, bv(key, pos), MNode{pos, lo, cput(V, hi, key, x)}, MNode{pos, cput(V, lo, key, x), hi}) : Map<&2, V>}:
  match b:
    case False{}:
      %Equal.sym(Bool, bv(key, pos), False{}, eb) : {Map.put.bit(&2, V, x, pos, lo, hi, (key, _)) == Bool.pick(Map<&2, V>, _, MNode{pos, lo, cput(V, hi, key, x)}, MNode{pos, cput(V, lo, key, x), hi}) : Map<&2, V>}
      %Equal.sym(Map<&2, V>, Map.put(&2, V, lo, key, x), cput(V, lo, key, x), ilo) : {MNode{pos, _, hi} == MNode{pos, cput(V, lo, key, x), hi} : Map<&2, V>}
      {==}
    case True{}:
      %Equal.sym(Bool, bv(key, pos), True{}, eb) : {Map.put.bit(&2, V, x, pos, lo, hi, (key, _)) == Bool.pick(Map<&2, V>, _, MNode{pos, lo, cput(V, hi, key, x)}, MNode{pos, cput(V, lo, key, x), hi}) : Map<&2, V>}
      %Equal.sym(Map<&2, V>, Map.put(&2, V, hi, key, x), cput(V, hi, key, x), ihi) : {MNode{pos, lo, _} == MNode{pos, lo, cput(V, hi, key, x)} : Map<&2, V>}
      {==}

def put_is(-V: Data, m: Map<&2, V>, +key: String, +x: V) -> {Map.put(&2, V, m, key, x) == cput(V, m, key, x) : Map<&2, V>}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{k, v}:
      {==}
    case MNode{+pos, +lo, +hi}:
      %Equal.sym(String & Bool, Map.bit(key, pos), (key, bv(key, pos)), bit_back(key, pos)) : {Map.put.bit(&2, V, x, pos, lo, hi, _) == cput(V, MNode{pos, lo, hi}, key, x) : Map<&2, V>}
      put_node(V, pos, lo, hi, key, x, bv(key, pos), {==}, put_is(V, lo, key, x), put_is(V, hi, key, x))

def splice_bit(-V: Data, +p: Nat, +key: String, +x: V, +rest: Map<&2, V>, b: Bool, +eb: {bv(key, p) == b : Bool}) -> {Map.ins.splice.bit(&2, V, x, rest, p, (key, bv(key, p))) == csplice(V, p, key, x, rest) : Map<&2, V>}:
  match b:
    case False{}:
      %Equal.sym(Bool, bv(key, p), False{}, eb) : {Map.ins.splice.bit(&2, V, x, rest, p, (key, _)) == Bool.pick(Map<&2, V>, _, MNode{p, rest, MLeaf{key, x}}, MNode{p, MLeaf{key, x}, rest}) : Map<&2, V>}
      {==}
    case True{}:
      %Equal.sym(Bool, bv(key, p), True{}, eb) : {Map.ins.splice.bit(&2, V, x, rest, p, (key, _)) == Bool.pick(Map<&2, V>, _, MNode{p, rest, MLeaf{key, x}}, MNode{p, MLeaf{key, x}, rest}) : Map<&2, V>}
      {==}

def splice_is(-V: Data, +p: Nat, +key: String, +x: V, +rest: Map<&2, V>) -> {Map.ins.splice(&2, V, p, key, x, rest) == csplice(V, p, key, x, rest) : Map<&2, V>}:
  %Equal.sym(String & Bool, Map.bit(key, p), (key, bv(key, p)), bit_back(key, p)) : {Map.ins.splice.bit(&2, V, x, rest, p, _) == csplice(V, p, key, x, rest) : Map<&2, V>}
  splice_bit(V, p, key, x, rest, bv(key, p), {==})

def ins_deep(-V: Data, +q: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +key: String, +x: V, +p: Nat, b: Bool, +eb: {bv(key, q) == b : Bool}, ilo: {Map.ins(&2, V, lo, key, x, p) == cins(V, lo, key, x, p) : Map<&2, V>}, ihi: {Map.ins(&2, V, hi, key, x, p) == cins(V, hi, key, x, p) : Map<&2, V>}) -> {Map.ins.deep(&2, V, x, lo, hi, p, q, (key, bv(key, q))) == Bool.pick(Map<&2, V>, bv(key, q), MNode{q, lo, cins(V, hi, key, x, p)}, MNode{q, cins(V, lo, key, x, p), hi}) : Map<&2, V>}:
  match b:
    case False{}:
      %Equal.sym(Bool, bv(key, q), False{}, eb) : {Map.ins.deep(&2, V, x, lo, hi, p, q, (key, _)) == Bool.pick(Map<&2, V>, _, MNode{q, lo, cins(V, hi, key, x, p)}, MNode{q, cins(V, lo, key, x, p), hi}) : Map<&2, V>}
      %Equal.sym(Map<&2, V>, Map.ins(&2, V, lo, key, x, p), cins(V, lo, key, x, p), ilo) : {MNode{q, _, hi} == MNode{q, cins(V, lo, key, x, p), hi} : Map<&2, V>}
      {==}
    case True{}:
      %Equal.sym(Bool, bv(key, q), True{}, eb) : {Map.ins.deep(&2, V, x, lo, hi, p, q, (key, _)) == Bool.pick(Map<&2, V>, _, MNode{q, lo, cins(V, hi, key, x, p)}, MNode{q, cins(V, lo, key, x, p), hi}) : Map<&2, V>}
      %Equal.sym(Map<&2, V>, Map.ins(&2, V, hi, key, x, p), cins(V, hi, key, x, p), ihi) : {MNode{q, lo, _} == MNode{q, lo, cins(V, hi, key, x, p)} : Map<&2, V>}
      {==}

def ins_if(-V: Data, +q: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +key: String, +x: V, +p: Nat, t: Bool, +et: {Nat.is_lt(q, p) == t : Bool}, ilo: {Map.ins(&2, V, lo, key, x, p) == cins(V, lo, key, x, p) : Map<&2, V>}, ihi: {Map.ins(&2, V, hi, key, x, p) == cins(V, hi, key, x, p) : Map<&2, V>}) -> {Map.ins.if(&2, V, key, x, lo, hi, q, p, Nat.is_lt(q, p)) == cins(V, MNode{q, lo, hi}, key, x, p) : Map<&2, V>}:
  match t:
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(q, p), False{}, et) : {Map.ins.if(&2, V, key, x, lo, hi, q, p, _) == Bool.pick(Map<&2, V>, _, Bool.pick(Map<&2, V>, bv(key, q), MNode{q, lo, cins(V, hi, key, x, p)}, MNode{q, cins(V, lo, key, x, p), hi}), csplice(V, p, key, x, MNode{q, lo, hi})) : Map<&2, V>}
      splice_is(V, p, key, x, MNode{q, lo, hi})
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(q, p), True{}, et) : {Map.ins.if(&2, V, key, x, lo, hi, q, p, _) == Bool.pick(Map<&2, V>, _, Bool.pick(Map<&2, V>, bv(key, q), MNode{q, lo, cins(V, hi, key, x, p)}, MNode{q, cins(V, lo, key, x, p), hi}), csplice(V, p, key, x, MNode{q, lo, hi})) : Map<&2, V>}
      %Equal.sym(String & Bool, Map.bit(key, q), (key, bv(key, q)), bit_back(key, q)) : {Map.ins.deep(&2, V, x, lo, hi, p, q, _) == Bool.pick(Map<&2, V>, bv(key, q), MNode{q, lo, cins(V, hi, key, x, p)}, MNode{q, cins(V, lo, key, x, p), hi}) : Map<&2, V>}
      ins_deep(V, q, lo, hi, key, x, p, bv(key, q), {==}, ilo, ihi)

def ins_is(-V: Data, m: Map<&2, V>, +key: String, +x: V, +p: Nat) -> {Map.ins(&2, V, m, key, x, p) == cins(V, m, key, x, p) : Map<&2, V>}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k, +v}:
      splice_is(V, p, key, x, MLeaf{k, v})
    case MNode{+q, +lo, +hi}:
      ins_if(V, q, lo, hi, key, x, p, Nat.is_lt(q, p), {==}, ins_is(V, lo, key, x, p), ins_is(V, hi, key, x, p))

def set_fin(-V: Data, +m: Map<&2, V>, +key: String, +x: V, +k0: String, c: Cmp, +ec: {String.order(key, k0) == c : Cmp}) -> {Map.set.fin.go(&2, V, m, key, x, ((key, k0), String.order(key, k0))) == cfin(V, m, key, x, k0, String.order(key, k0)) : Map<&2, V>}:
  match c:
    case LT{}:
      %Equal.sym(Cmp, String.order(key, k0), LT{}, ec) : {Map.set.fin.go(&2, V, m, key, x, ((key, k0), _)) == cfin(V, m, key, x, k0, _) : Map<&2, V>}
      ins_is(V, m, key, x, Map.diff(key, k0))
    case EQ{}:
      %Equal.sym(Cmp, String.order(key, k0), EQ{}, ec) : {Map.set.fin.go(&2, V, m, key, x, ((key, k0), _)) == cfin(V, m, key, x, k0, _) : Map<&2, V>}
      put_is(V, m, key, x)
    case GT{}:
      %Equal.sym(Cmp, String.order(key, k0), GT{}, ec) : {Map.set.fin.go(&2, V, m, key, x, ((key, k0), _)) == cfin(V, m, key, x, k0, _) : Map<&2, V>}
      ins_is(V, m, key, x, Map.diff(key, k0))

def set_go(-V: Data, +m: Map<&2, V>, +key: String, +x: V, r: Maybe<&2, String>, +er: {reach(V, m, key) == r : Maybe<&2, String>}) -> {Map.set.go(&2, V, x, (m, key, reach(V, m, key))) == cset.of(V, m, key, x, reach(V, m, key)) : Map<&2, V>}:
  match r:
    case None{}:
      %Equal.sym(Maybe<&2, String>, reach(V, m, key), None{}, er) : {Map.set.go(&2, V, x, (m, key, _)) == cset.of(V, m, key, x, _) : Map<&2, V>}
      {==}
    case Some{+k0}:
      %Equal.sym(Maybe<&2, String>, reach(V, m, key), Some{k0}, er) : {Map.set.go(&2, V, x, (m, key, _)) == cset.of(V, m, key, x, _) : Map<&2, V>}
      %Equal.sym((String & String) & Cmp, String.cmp(key, k0), ((key, k0), String.order(key, k0)), cmp_back(key, k0)) : {Map.set.fin.go(&2, V, m, key, x, _) == cfin(V, m, key, x, k0, String.order(key, k0)) : Map<&2, V>}
      set_fin(V, m, key, x, k0, String.order(key, k0), {==})

# `Map.set` is `cset`.
def set_is(-V: Data, +m: Map<&2, V>, +key: String, +x: V) -> {Map.set(&2, V, m, key, x) == cset(V, m, key, x) : Map<&2, V>}:
  %Equal.sym(Map<&2, V> & String & Maybe<&2, String>, Map.seek(&2, V, m, key), (m, key, reach(V, m, key)), seek_is(V, m, key)) : {Map.set.go(&2, V, x, _) == cset(V, m, key, x) : Map<&2, V>}
  set_go(V, m, key, x, reach(V, m, key), {==})

def gv(-V: Data, r: Map<&2, V> & V) -> V:
  (m, v) = r
  v

def hv(-V: Data, r: Map<&2, V> & Bool) -> Bool:
  (m, b) = r
  b

def lo_v(-V: Data, +pos: Nat, +hi: Map<&2, V>, r: Map<&2, V> & V) -> {gv(V, Map.lo(&2, V, V, pos, hi, r)) == gv(V, r) : V}:
  match r:
    case (m, v):
      {==}

def hi_v(-V: Data, +pos: Nat, +lo: Map<&2, V>, r: Map<&2, V> & V) -> {gv(V, Map.hi(&2, V, V, pos, lo, r)) == gv(V, r) : V}:
  match r:
    case (m, v):
      {==}

def lo_h(-V: Data, +pos: Nat, +hi: Map<&2, V>, r: Map<&2, V> & Bool) -> {hv(V, Map.lo(&2, V, Bool, pos, hi, r)) == hv(V, r) : Bool}:
  match r:
    case (m, b):
      {==}

def hi_h(-V: Data, +pos: Nat, +lo: Map<&2, V>, r: Map<&2, V> & Bool) -> {hv(V, Map.hi(&2, V, Bool, pos, lo, r)) == hv(V, r) : Bool}:
  match r:
    case (m, b):
      {==}

def get_leaf(-V: Data, +d: V, +v: V, +j: String, +k: String, c: Cmp) -> {gv(V, Map.get.leaf(V, d, v, ((j, k), c))) == Maybe.default(&2, V, Bool.pick(Maybe<&2, V>, Cmp.is_eq(c), Some{v}, None{}), d) : V}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def get_node(-V: Data, +d: V, +pos: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +j: String, b: Bool, +eb: {bv(j, pos) == b : Bool}, ilo: {gv(V, Map.get(V, d, lo, j)) == Maybe.default(&2, V, found(V, lo, j), d) : V}, ihi: {gv(V, Map.get(V, d, hi, j)) == Maybe.default(&2, V, found(V, hi, j), d) : V}) -> {gv(V, Map.get.bit(V, d, lo, hi, pos, (j, bv(j, pos)))) == Maybe.default(&2, V, Bool.pick(Maybe<&2, V>, bv(j, pos), found(V, hi, j), found(V, lo, j)), d) : V}:
  match b:
    case False{}:
      %Equal.sym(Bool, bv(j, pos), False{}, eb) : {gv(V, Map.get.bit(V, d, lo, hi, pos, (j, _))) == Maybe.default(&2, V, Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, lo, j)), d) : V}
      %Equal.sym(V, gv(V, Map.lo(&2, V, V, pos, hi, Map.get(V, d, lo, j))), gv(V, Map.get(V, d, lo, j)), lo_v(V, pos, hi, Map.get(V, d, lo, j))) : {_ == Maybe.default(&2, V, found(V, lo, j), d) : V}
      ilo
    case True{}:
      %Equal.sym(Bool, bv(j, pos), True{}, eb) : {gv(V, Map.get.bit(V, d, lo, hi, pos, (j, _))) == Maybe.default(&2, V, Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, lo, j)), d) : V}
      %Equal.sym(V, gv(V, Map.hi(&2, V, V, pos, lo, Map.get(V, d, hi, j))), gv(V, Map.get(V, d, hi, j)), hi_v(V, pos, lo, Map.get(V, d, hi, j))) : {_ == Maybe.default(&2, V, found(V, hi, j), d) : V}
      ihi

# What `Map.get` answers is what the key finds, or the default.
def get_is(-V: Data, +d: V, m: Map<&2, V>, +j: String) -> {gv(V, Map.get(V, d, m, j)) == Maybe.default(&2, V, found(V, m, j), d) : V}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k, +v}:
      %Equal.sym((String & String) & Cmp, String.cmp(j, k), ((j, k), String.order(j, k)), cmp_back(j, k)) : {gv(V, Map.get.leaf(V, d, v, _)) == Maybe.default(&2, V, Bool.pick(Maybe<&2, V>, String.eq.fin(_), Some{v}, None{}), d) : V}
      get_leaf(V, d, v, j, k, String.order(j, k))
    case MNode{+pos, +lo, +hi}:
      %Equal.sym(String & Bool, Map.bit(j, pos), (j, bv(j, pos)), bit_back(j, pos)) : {gv(V, Map.get.bit(V, d, lo, hi, pos, _)) == Maybe.default(&2, V, found(V, MNode{pos, lo, hi}, j), d) : V}
      get_node(V, d, pos, lo, hi, j, bv(j, pos), {==}, get_is(V, d, lo, j), get_is(V, d, hi, j))

def has_leaf(-V: Data, +v: V, +j: String, +k: String, c: Cmp) -> {hv(V, Map.has.leaf(&2, V, v, ((j, k), c))) == Maybe.is_some(&2, V, Bool.pick(Maybe<&2, V>, Cmp.is_eq(c), Some{v}, None{})) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def has_node(-V: Data, +pos: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +j: String, b: Bool, +eb: {bv(j, pos) == b : Bool}, ilo: {hv(V, Map.has(&2, V, lo, j)) == Maybe.is_some(&2, V, found(V, lo, j)) : Bool}, ihi: {hv(V, Map.has(&2, V, hi, j)) == Maybe.is_some(&2, V, found(V, hi, j)) : Bool}) -> {hv(V, Map.has.bit(&2, V, lo, hi, pos, (j, bv(j, pos)))) == Maybe.is_some(&2, V, Bool.pick(Maybe<&2, V>, bv(j, pos), found(V, hi, j), found(V, lo, j))) : Bool}:
  match b:
    case False{}:
      %Equal.sym(Bool, bv(j, pos), False{}, eb) : {hv(V, Map.has.bit(&2, V, lo, hi, pos, (j, _))) == Maybe.is_some(&2, V, Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, lo, j))) : Bool}
      %Equal.sym(Bool, hv(V, Map.lo(&2, V, Bool, pos, hi, Map.has(&2, V, lo, j))), hv(V, Map.has(&2, V, lo, j)), lo_h(V, pos, hi, Map.has(&2, V, lo, j))) : {_ == Maybe.is_some(&2, V, found(V, lo, j)) : Bool}
      ilo
    case True{}:
      %Equal.sym(Bool, bv(j, pos), True{}, eb) : {hv(V, Map.has.bit(&2, V, lo, hi, pos, (j, _))) == Maybe.is_some(&2, V, Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, lo, j))) : Bool}
      %Equal.sym(Bool, hv(V, Map.hi(&2, V, Bool, pos, lo, Map.has(&2, V, hi, j))), hv(V, Map.has(&2, V, hi, j)), hi_h(V, pos, lo, Map.has(&2, V, hi, j))) : {_ == Maybe.is_some(&2, V, found(V, hi, j)) : Bool}
      ihi

# What `Map.has` answers is whether the key finds anything.
def has_is(-V: Data, m: Map<&2, V>, +j: String) -> {hv(V, Map.has(&2, V, m, j)) == Maybe.is_some(&2, V, found(V, m, j)) : Bool}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k, +v}:
      %Equal.sym((String & String) & Cmp, String.cmp(j, k), ((j, k), String.order(j, k)), cmp_back(j, k)) : {hv(V, Map.has.leaf(&2, V, v, _)) == Maybe.is_some(&2, V, Bool.pick(Maybe<&2, V>, String.eq.fin(_), Some{v}, None{})) : Bool}
      has_leaf(V, v, j, k, String.order(j, k))
    case MNode{+pos, +lo, +hi}:
      %Equal.sym(String & Bool, Map.bit(j, pos), (j, bv(j, pos)), bit_back(j, pos)) : {hv(V, Map.has.bit(&2, V, lo, hi, pos, _)) == Maybe.is_some(&2, V, found(V, MNode{pos, lo, hi}, j)) : Bool}
      has_node(V, pos, lo, hi, j, bv(j, pos), {==}, has_is(V, lo, j), has_is(V, hi, j))

# Small facts
# -----------

def pick_same(-T: Type, b: Bool, -x: T) -> {Bool.pick(T, b, x, x) == x : T}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def or_false_l(a: Bool, b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Str.true_false(e))

def or_false_r(a: Bool, b: Bool, +e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case False{}:
      e
    case True{}:
      Empty.absurd({b == False{} : Bool}, Str.true_false(e))

def or_true_r(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def or_false_id(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def or_comm(a: Bool, b: Bool) -> {Bool.or(a, b) == Bool.or(b, a) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def or_assoc(a: Bool, b: Bool, c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def or_swap(a: Bool, b: Bool, c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(b, Bool.or(a, c)) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def not_self(+x: Bool, +e: {x == Bool.not(x) : Bool}) -> Empty:
  match x:
    case False{}:
      Str.false_true(e)
    case True{}:
      Str.true_false(e)

# `x` is `not y` both ways round.
def flip(x: Bool, y: Bool, +e: {x == Bool.not(y) : Bool}) -> {y == Bool.not(x) : Bool}:
  match x y:
    case False{} False{}:
      Empty.absurd({False{} == True{} : Bool}, Str.false_true(e))
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      Empty.absurd({True{} == False{} : Bool}, Str.true_false(e))

def unsome(-A: Data, +d: A, m: Maybe<&2, A>) -> A:
  Maybe.default(&2, A, m, d)

def some_inj(-A: Data, +a: A, +b: A, e: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  Equal.cong(Maybe<&2, A>, A, z => Maybe.default(&2, A, z, a), Some{a}, Some{b}, e)

def maybe_disc(-A: Data, m: Maybe<&2, A>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some(-A: Data, -b: A, e: {None{} == Some{b} : Maybe<&2, A>}) -> Empty:
  %e : {maybe_disc(A, _) : Type}
  Unit{}

def eq_of_order(+a: String, +b: String, c: Cmp, ec: {String.order(a, b) == c : Cmp}) -> {String.eq(a, b) == Cmp.is_eq(c) : Bool}:
  %ec : {String.eq(a, b) == Cmp.is_eq(_) : Bool}
  Str.eq_order(a, b)

def eq_flip.go(+a: String, +b: String, s: Bool, +es: {String.eq(b, a) == s : Bool}, e: {String.eq(a, b) == False{} : Bool}) -> {String.eq(b, a) == False{} : Bool}:
  match s:
    case False{}:
      es
    case True{}:
      +ba = Str.eq_true(b, a, es)
      Empty.absurd({String.eq(b, a) == False{} : Bool}, Str.true_false(Equal.trans(Bool, True{}, String.eq(a, b), False{}, Equal.trans(Bool, True{}, String.eq(a, a), String.eq(a, b), Equal.sym(Bool, String.eq(a, a), True{}, Str.eq_refl(a)), Equal.cong(String, Bool, z => String.eq(a, z), a, b, Equal.sym(String, b, a, ba))), e)))

def eq_flip(+a: String, +b: String, e: {String.eq(a, b) == False{} : Bool}) -> {String.eq(b, a) == False{} : Bool}:
  eq_flip.go(a, b, String.eq(b, a), {==}, e)

# A key finds what was written for it
# ------------------------------------

def found_leaf_k(-V: Data, +k: String, +x: V) -> {found(V, MLeaf{k, x}, k) == Some{x} : Maybe<&2, V>}:
  %Equal.sym(Bool, String.eq(k, k), True{}, Str.eq_refl(k)) : {Bool.pick(Maybe<&2, V>, _, Some{x}, None{}) == Some{x} : Maybe<&2, V>}
  {==}

def found_leaf_other(-V: Data, +k: String, +x: V, +j: String, e: {String.eq(j, k) == False{} : Bool}) -> {found(V, MLeaf{k, x}, j) == None{} : Maybe<&2, V>}:
  %Equal.sym(Bool, String.eq(j, k), False{}, e) : {Bool.pick(Maybe<&2, V>, _, Some{x}, None{}) == None{} : Maybe<&2, V>}
  {==}

def splice_same(-V: Data, +p: Nat, +k: String, +x: V, +rest: Map<&2, V>, b: Bool, +eb: {bv(k, p) == b : Bool}) -> {found(V, csplice(V, p, k, x, rest), k) == Some{x} : Maybe<&2, V>}:
  match b:
    case True{}:
      %Equal.sym(Bool, bv(k, p), True{}, eb) : {found(V, Bool.pick(Map<&2, V>, _, MNode{p, rest, MLeaf{k, x}}, MNode{p, MLeaf{k, x}, rest}), k) == Some{x} : Maybe<&2, V>}
      %Equal.sym(Bool, bv(k, p), True{}, eb) : {Bool.pick(Maybe<&2, V>, _, found(V, MLeaf{k, x}, k), found(V, rest, k)) == Some{x} : Maybe<&2, V>}
      found_leaf_k(V, k, x)
    case False{}:
      %Equal.sym(Bool, bv(k, p), False{}, eb) : {found(V, Bool.pick(Map<&2, V>, _, MNode{p, rest, MLeaf{k, x}}, MNode{p, MLeaf{k, x}, rest}), k) == Some{x} : Maybe<&2, V>}
      %Equal.sym(Bool, bv(k, p), False{}, eb) : {Bool.pick(Maybe<&2, V>, _, found(V, rest, k), found(V, MLeaf{k, x}, k)) == Some{x} : Maybe<&2, V>}
      found_leaf_k(V, k, x)

def ins_same.deep(-V: Data, +q: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +k: String, +x: V, +p: Nat, b: Bool, +eb: {bv(k, q) == b : Bool}, ilo: {found(V, cins(V, lo, k, x, p), k) == Some{x} : Maybe<&2, V>}, ihi: {found(V, cins(V, hi, k, x, p), k) == Some{x} : Maybe<&2, V>}) -> {found(V, Bool.pick(Map<&2, V>, bv(k, q), MNode{q, lo, cins(V, hi, k, x, p)}, MNode{q, cins(V, lo, k, x, p), hi}), k) == Some{x} : Maybe<&2, V>}:
  match b:
    case True{}:
      %Equal.sym(Bool, bv(k, q), True{}, eb) : {found(V, Bool.pick(Map<&2, V>, _, MNode{q, lo, cins(V, hi, k, x, p)}, MNode{q, cins(V, lo, k, x, p), hi}), k) == Some{x} : Maybe<&2, V>}
      %Equal.sym(Bool, bv(k, q), True{}, eb) : {Bool.pick(Maybe<&2, V>, _, found(V, cins(V, hi, k, x, p), k), found(V, lo, k)) == Some{x} : Maybe<&2, V>}
      ihi
    case False{}:
      %Equal.sym(Bool, bv(k, q), False{}, eb) : {found(V, Bool.pick(Map<&2, V>, _, MNode{q, lo, cins(V, hi, k, x, p)}, MNode{q, cins(V, lo, k, x, p), hi}), k) == Some{x} : Maybe<&2, V>}
      %Equal.sym(Bool, bv(k, q), False{}, eb) : {Bool.pick(Maybe<&2, V>, _, found(V, hi, k), found(V, cins(V, lo, k, x, p), k)) == Some{x} : Maybe<&2, V>}
      ilo

def ins_same.node(-V: Data, +q: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +k: String, +x: V, +p: Nat, t: Bool, +et: {Nat.is_lt(q, p) == t : Bool}, ilo: {found(V, cins(V, lo, k, x, p), k) == Some{x} : Maybe<&2, V>}, ihi: {found(V, cins(V, hi, k, x, p), k) == Some{x} : Maybe<&2, V>}) -> {found(V, cins(V, MNode{q, lo, hi}, k, x, p), k) == Some{x} : Maybe<&2, V>}:
  match t:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(q, p), True{}, et) : {found(V, Bool.pick(Map<&2, V>, _, Bool.pick(Map<&2, V>, bv(k, q), MNode{q, lo, cins(V, hi, k, x, p)}, MNode{q, cins(V, lo, k, x, p), hi}), csplice(V, p, k, x, MNode{q, lo, hi})), k) == Some{x} : Maybe<&2, V>}
      ins_same.deep(V, q, lo, hi, k, x, p, bv(k, q), {==}, ilo, ihi)
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(q, p), False{}, et) : {found(V, Bool.pick(Map<&2, V>, _, Bool.pick(Map<&2, V>, bv(k, q), MNode{q, lo, cins(V, hi, k, x, p)}, MNode{q, cins(V, lo, k, x, p), hi}), csplice(V, p, k, x, MNode{q, lo, hi})), k) == Some{x} : Maybe<&2, V>}
      splice_same(V, p, k, x, MNode{q, lo, hi}, bv(k, p), {==})

# A key finds what `cins` wrote for it, wherever it was spliced in.
def ins_same(-V: Data, m: Map<&2, V>, +k: String, +x: V, +p: Nat) -> {found(V, cins(V, m, k, x, p), k) == Some{x} : Maybe<&2, V>}:
  match m:
    case MTip{}:
      found_leaf_k(V, k, x)
    case MLeaf{+k1, +v}:
      splice_same(V, p, k, x, MLeaf{k1, v}, bv(k, p), {==})
    case MNode{+q, +lo, +hi}:
      ins_same.node(V, q, lo, hi, k, x, p, Nat.is_lt(q, p), {==}, ins_same(V, lo, k, x, p), ins_same(V, hi, k, x, p))

def put_same.node(-V: Data, +pos: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +k: String, +x: V, +k0: String, b: Bool, +eb: {bv(k, pos) == b : Bool}, +er: {Bool.pick(Maybe<&2, String>, bv(k, pos), reach(V, hi, k), reach(V, lo, k)) == Some{k0} : Maybe<&2, String>}, ilo: {reach(V, lo, k) == Some{k0} : Maybe<&2, String>} -> {found(V, cput(V, lo, k, x), k) == Some{x} : Maybe<&2, V>}, ihi: {reach(V, hi, k) == Some{k0} : Maybe<&2, String>} -> {found(V, cput(V, hi, k, x), k) == Some{x} : Maybe<&2, V>}) -> {found(V, Bool.pick(Map<&2, V>, bv(k, pos), MNode{pos, lo, cput(V, hi, k, x)}, MNode{pos, cput(V, lo, k, x), hi}), k) == Some{x} : Maybe<&2, V>}:
  match b:
    case True{}:
      +r = Equal.trans(Maybe<&2, String>, reach(V, hi, k), Bool.pick(Maybe<&2, String>, bv(k, pos), reach(V, hi, k), reach(V, lo, k)), Some{k0}, Equal.cong(Bool, Maybe<&2, String>, z => Bool.pick(Maybe<&2, String>, z, reach(V, hi, k), reach(V, lo, k)), True{}, bv(k, pos), Equal.sym(Bool, bv(k, pos), True{}, eb)), er)
      %Equal.sym(Bool, bv(k, pos), True{}, eb) : {found(V, Bool.pick(Map<&2, V>, _, MNode{pos, lo, cput(V, hi, k, x)}, MNode{pos, cput(V, lo, k, x), hi}), k) == Some{x} : Maybe<&2, V>}
      %Equal.sym(Bool, bv(k, pos), True{}, eb) : {Bool.pick(Maybe<&2, V>, _, found(V, cput(V, hi, k, x), k), found(V, lo, k)) == Some{x} : Maybe<&2, V>}
      ihi(r)
    case False{}:
      +r = Equal.trans(Maybe<&2, String>, reach(V, lo, k), Bool.pick(Maybe<&2, String>, bv(k, pos), reach(V, hi, k), reach(V, lo, k)), Some{k0}, Equal.cong(Bool, Maybe<&2, String>, z => Bool.pick(Maybe<&2, String>, z, reach(V, hi, k), reach(V, lo, k)), False{}, bv(k, pos), Equal.sym(Bool, bv(k, pos), False{}, eb)), er)
      %Equal.sym(Bool, bv(k, pos), False{}, eb) : {found(V, Bool.pick(Map<&2, V>, _, MNode{pos, lo, cput(V, hi, k, x)}, MNode{pos, cput(V, lo, k, x), hi}), k) == Some{x} : Maybe<&2, V>}
      %Equal.sym(Bool, bv(k, pos), False{}, eb) : {Bool.pick(Maybe<&2, V>, _, found(V, hi, k), found(V, cput(V, lo, k, x), k)) == Some{x} : Maybe<&2, V>}
      ilo(r)

# Where the leaf a key's bits lead to is that key, `cput` writes there.
def put_same(-V: Data, m: Map<&2, V>, +k: String, +x: V, +k0: String, +er: {reach(V, m, k) == Some{k0} : Maybe<&2, String>}, +ek: {String.eq(k, k0) == True{} : Bool}) -> {found(V, cput(V, m, k, x), k) == Some{x} : Maybe<&2, V>}:
  match m:
    case MTip{}:
      found_leaf_k(V, k, x)
    case MLeaf{+k1, v}:
      %Equal.sym(String, k1, k0, some_inj(String, k1, k0, er)) : {found(V, MLeaf{_, x}, k) == Some{x} : Maybe<&2, V>}
      %Equal.sym(Bool, String.eq(k, k0), True{}, ek) : {Bool.pick(Maybe<&2, V>, _, Some{x}, None{}) == Some{x} : Maybe<&2, V>}
      {==}
    case MNode{+pos, +lo, +hi}:
      put_same.node(V, pos, lo, hi, k, x, k0, bv(k, pos), {==}, er, e2 => put_same(V, lo, k, x, k0, e2, ek), e2 => put_same(V, hi, k, x, k0, e2, ek))

def set_fin_same(-V: Data, +m: Map<&2, V>, +k: String, +x: V, +k0: String, er: {reach(V, m, k) == Some{k0} : Maybe<&2, String>}, c: Cmp, +ec: {String.order(k, k0) == c : Cmp}) -> {found(V, cfin(V, m, k, x, k0, String.order(k, k0)), k) == Some{x} : Maybe<&2, V>}:
  match c:
    case LT{}:
      %Equal.sym(Cmp, String.order(k, k0), LT{}, ec) : {found(V, cfin(V, m, k, x, k0, _), k) == Some{x} : Maybe<&2, V>}
      ins_same(V, m, k, x, Map.diff(k, k0))
    case EQ{}:
      %Equal.sym(Cmp, String.order(k, k0), EQ{}, ec) : {found(V, cfin(V, m, k, x, k0, _), k) == Some{x} : Maybe<&2, V>}
      put_same(V, m, k, x, k0, er, eq_of_order(k, k0, EQ{}, ec))
    case GT{}:
      %Equal.sym(Cmp, String.order(k, k0), GT{}, ec) : {found(V, cfin(V, m, k, x, k0, _), k) == Some{x} : Maybe<&2, V>}
      ins_same(V, m, k, x, Map.diff(k, k0))

def set_same.of(-V: Data, +m: Map<&2, V>, +k: String, +x: V, r: Maybe<&2, String>, +er: {reach(V, m, k) == r : Maybe<&2, String>}) -> {found(V, cset.of(V, m, k, x, reach(V, m, k)), k) == Some{x} : Maybe<&2, V>}:
  match r:
    case None{}:
      %Equal.sym(Maybe<&2, String>, reach(V, m, k), None{}, er) : {found(V, cset.of(V, m, k, x, _), k) == Some{x} : Maybe<&2, V>}
      found_leaf_k(V, k, x)
    case Some{+k0}:
      %Equal.sym(Maybe<&2, String>, reach(V, m, k), Some{k0}, er) : {found(V, cset.of(V, m, k, x, _), k) == Some{x} : Maybe<&2, V>}
      set_fin_same(V, m, k, x, k0, er, String.order(k, k0), {==})

# A key finds what was just written for it, in any map at all.
def set_same(-V: Data, +m: Map<&2, V>, +k: String, +x: V) -> {found(V, cset(V, m, k, x), k) == Some{x} : Maybe<&2, V>}:
  set_same.of(V, m, k, x, reach(V, m, k), {==})

# What `Map.set` keeps
# --------------------

# Every key at a leaf of `m` has bit `b` at `p`.
def Side(-V: Data, +m: Map<&2, V>, +p: Nat, b: Bool) -> Type:
  @a:String -> {mem(V, m, a) == True{} : Bool} -> {bv(a, p) == b : Bool}

# Every two keys at leaves of `m` agree at every position before `p`.
def Near(-V: Data, +m: Map<&2, V>, p: Nat) -> Type:
  @a:String -> @c:String -> @q:Nat -> {mem(V, m, a) == True{} : Bool} -> {mem(V, m, c) == True{} : Bool} -> {Nat.is_lt(q, p) == True{} : Bool} -> {bv(a, q) == bv(c, q) : Bool}

# The invariant is a `Bool`, so that a proof of it can be used as often as
# a proof needs; `Side` and `Near` above are what it gives.
def beq(x: Bool, +y: Bool) -> Bool:
  match x:
    case False{}:
      Bool.not(y)
    case True{}:
      y

# Whether two keys agree at every position before `p`.
def agree(+a: String, +r: String, +p: Nat) -> Bool:
  match p:
    case 0n:
      True{}
    case 1n++q:
      Bool.and(agree(a, r, q), beq(bv(a, q), bv(r, q)))

# Whether every key of `m` has bit `b` at `p`.
def sides(-V: Data, +m: Map<&2, V>, +p: Nat, +b: Bool) -> Bool:
  match m:
    case MTip{}:
      True{}
    case MLeaf{k, v}:
      beq(bv(k, p), b)
    case MNode{q, lo, hi}:
      Bool.and(sides(V, lo, p, b), sides(V, hi, p, b))

# Whether every key of `m` agrees with `r` before `p`.
def agrees(-V: Data, m: Map<&2, V>, +r: String, +p: Nat) -> Bool:
  match m:
    case MTip{}:
      True{}
    case MLeaf{k, v}:
      agree(k, r, p)
    case MNode{q, lo, hi}:
      Bool.and(agrees(V, lo, r, p), agrees(V, hi, r, p))

# The leftmost key.
def rep(-V: Data, m: Map<&2, V>) -> String:
  match m:
    case MTip{}:
      SNil{}
    case MLeaf{k, v}:
      k
    case MNode{q, lo, hi}:
      rep(V, lo)

# A trie as `Map.set` builds it: no empty subtree, and at each node the
# keys below its low side have its bit clear, those below its high side
# have it set, and all its keys agree at every position before it.
def wf(-V: Data, m: Map<&2, V>) -> Bool:
  match m:
    case MTip{}:
      False{}
    case MLeaf{k, v}:
      True{}
    case MNode{+p, +lo, +hi}:
      Bool.and(wf(V, lo), Bool.and(wf(V, hi), Bool.and(sides(V, lo, p, False{}), Bool.and(sides(V, hi, p, True{}), agrees(V, MNode{p, lo, hi}, rep(V, lo), p)))))

# Every map `Map.new` and `Map.set` build: empty, or a trie as above.
def wft(-V: Data, m: Map<&2, V>) -> Bool:
  match m:
    case MTip{}:
      True{}
    case MLeaf{k, v}:
      True{}
    case MNode{+p, +lo, +hi}:
      wf(V, MNode{p, lo, hi})

def Wf(-V: Data, m: Map<&2, V>) -> Data:
  {wf(V, m) == True{} : Bool}

def Wf.top(-V: Data, m: Map<&2, V>) -> Data:
  {wft(V, m) == True{} : Bool}

def and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Str.false_true(e))
    case True{}:
      {==}

def and_r(a: Bool, -b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      Empty.absurd({b == True{} : Bool}, Str.false_true(e))
    case True{}:
      e

def beq_true(x: Bool, y: Bool, +e: {beq(x, y) == True{} : Bool}) -> {x == y : Bool}:
  match x y:
    case False{} False{}:
      {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, Str.false_true(e))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, Str.false_true(e))
    case True{} True{}:
      {==}

def beq_refl(x: Bool) -> {beq(x, x) == True{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

def wf_lo(-V: Data, +p: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +w: Wf(V, MNode{p, lo, hi})) -> {wf(V, lo) == True{} : Bool}:
  and_l(wf(V, lo), Bool.and(wf(V, hi), Bool.and(sides(V, lo, p, False{}), Bool.and(sides(V, hi, p, True{}), agrees(V, MNode{p, lo, hi}, rep(V, lo), p)))), w)

def wf_r1(-V: Data, +p: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +w: Wf(V, MNode{p, lo, hi})) -> {Bool.and(wf(V, hi), Bool.and(sides(V, lo, p, False{}), Bool.and(sides(V, hi, p, True{}), agrees(V, MNode{p, lo, hi}, rep(V, lo), p)))) == True{} : Bool}:
  and_r(wf(V, lo), Bool.and(wf(V, hi), Bool.and(sides(V, lo, p, False{}), Bool.and(sides(V, hi, p, True{}), agrees(V, MNode{p, lo, hi}, rep(V, lo), p)))), w)

def wf_hi(-V: Data, +p: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +w: Wf(V, MNode{p, lo, hi})) -> {wf(V, hi) == True{} : Bool}:
  and_l(wf(V, hi), Bool.and(sides(V, lo, p, False{}), Bool.and(sides(V, hi, p, True{}), agrees(V, MNode{p, lo, hi}, rep(V, lo), p))), wf_r1(V, p, lo, hi, w))

def wf_r2(-V: Data, +p: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +w: Wf(V, MNode{p, lo, hi})) -> {Bool.and(sides(V, lo, p, False{}), Bool.and(sides(V, hi, p, True{}), agrees(V, MNode{p, lo, hi}, rep(V, lo), p))) == True{} : Bool}:
  and_r(wf(V, hi), Bool.and(sides(V, lo, p, False{}), Bool.and(sides(V, hi, p, True{}), agrees(V, MNode{p, lo, hi}, rep(V, lo), p))), wf_r1(V, p, lo, hi, w))

def wf_slo(-V: Data, +p: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +w: Wf(V, MNode{p, lo, hi})) -> {sides(V, lo, p, False{}) == True{} : Bool}:
  and_l(sides(V, lo, p, False{}), Bool.and(sides(V, hi, p, True{}), agrees(V, MNode{p, lo, hi}, rep(V, lo), p)), wf_r2(V, p, lo, hi, w))

def wf_r3(-V: Data, +p: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +w: Wf(V, MNode{p, lo, hi})) -> {Bool.and(sides(V, hi, p, True{}), agrees(V, MNode{p, lo, hi}, rep(V, lo), p)) == True{} : Bool}:
  and_r(sides(V, lo, p, False{}), Bool.and(sides(V, hi, p, True{}), agrees(V, MNode{p, lo, hi}, rep(V, lo), p)), wf_r2(V, p, lo, hi, w))

def wf_shi(-V: Data, +p: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +w: Wf(V, MNode{p, lo, hi})) -> {sides(V, hi, p, True{}) == True{} : Bool}:
  and_l(sides(V, hi, p, True{}), agrees(V, MNode{p, lo, hi}, rep(V, lo), p), wf_r3(V, p, lo, hi, w))

def wf_near(-V: Data, +p: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +w: Wf(V, MNode{p, lo, hi})) -> {agrees(V, MNode{p, lo, hi}, rep(V, lo), p) == True{} : Bool}:
  and_r(sides(V, hi, p, True{}), agrees(V, MNode{p, lo, hi}, rep(V, lo), p), wf_r3(V, p, lo, hi, w))

def mem_or(-V: Data, +lo: Map<&2, V>, +hi: Map<&2, V>, +a: String, +s: Bool, es: {mem(V, lo, a) == s : Bool}, ea: {Bool.or(mem(V, lo, a), mem(V, hi, a)) == True{} : Bool}) -> {Bool.or(s, mem(V, hi, a)) == True{} : Bool}:
  Equal.trans(Bool, Bool.or(s, mem(V, hi, a)), Bool.or(mem(V, lo, a), mem(V, hi, a)), True{}, Equal.cong(Bool, Bool, z => Bool.or(z, mem(V, hi, a)), s, mem(V, lo, a), Equal.sym(Bool, mem(V, lo, a), s, es)), ea)

def sides_use.node(-V: Data, +lo: Map<&2, V>, +hi: Map<&2, V>, +p: Nat, +b: Bool, +a: String, ea: {Bool.or(mem(V, lo, a), mem(V, hi, a)) == True{} : Bool}, s: Bool, +es: {mem(V, lo, a) == s : Bool}, ilo: {mem(V, lo, a) == True{} : Bool} -> {bv(a, p) == b : Bool}, ihi: {mem(V, hi, a) == True{} : Bool} -> {bv(a, p) == b : Bool}) -> {bv(a, p) == b : Bool}:
  match s:
    case True{}:
      ilo(es)
    case False{}:
      ihi(mem_or(V, lo, hi, a, False{}, es, ea))

# A key of `m` has the bit `sides` says every key of it has.
def sides_use(-V: Data, m: Map<&2, V>, +p: Nat, +b: Bool, +e: {sides(V, m, p, b) == True{} : Bool}, +a: String, +ea: {mem(V, m, a) == True{} : Bool}) -> {bv(a, p) == b : Bool}:
  match m:
    case MTip{}:
      Empty.absurd({bv(a, p) == b : Bool}, Str.false_true(ea))
    case MLeaf{+k, v}:
      %Equal.sym(String, a, k, Str.eq_true(a, k, ea)) : {bv(_, p) == b : Bool}
      beq_true(bv(k, p), b, e)
    case MNode{q, +lo, +hi}:
      sides_use.node(V, lo, hi, p, b, a, ea, mem(V, lo, a), {==}, x => sides_use(V, lo, p, b, and_l(sides(V, lo, p, b), sides(V, hi, p, b), e), a, x), x => sides_use(V, hi, p, b, and_r(sides(V, lo, p, b), sides(V, hi, p, b), e), a, x))

def agrees_use.node(-V: Data, +lo: Map<&2, V>, +hi: Map<&2, V>, +r: String, +p: Nat, +a: String, ea: {Bool.or(mem(V, lo, a), mem(V, hi, a)) == True{} : Bool}, s: Bool, +es: {mem(V, lo, a) == s : Bool}, ilo: {mem(V, lo, a) == True{} : Bool} -> {agree(a, r, p) == True{} : Bool}, ihi: {mem(V, hi, a) == True{} : Bool} -> {agree(a, r, p) == True{} : Bool}) -> {agree(a, r, p) == True{} : Bool}:
  match s:
    case True{}:
      ilo(es)
    case False{}:
      ihi(mem_or(V, lo, hi, a, False{}, es, ea))

# A key of `m` agrees with `r` where `agrees` says every key of it does.
def agrees_use(-V: Data, m: Map<&2, V>, +r: String, +p: Nat, +e: {agrees(V, m, r, p) == True{} : Bool}, +a: String, +ea: {mem(V, m, a) == True{} : Bool}) -> {agree(a, r, p) == True{} : Bool}:
  match m:
    case MTip{}:
      Empty.absurd({agree(a, r, p) == True{} : Bool}, Str.false_true(ea))
    case MLeaf{+k, v}:
      %Equal.sym(String, a, k, Str.eq_true(a, k, ea)) : {agree(_, r, p) == True{} : Bool}
      e
    case MNode{q, +lo, +hi}:
      agrees_use.node(V, lo, hi, r, p, a, ea, mem(V, lo, a), {==}, x => agrees_use(V, lo, r, p, and_l(agrees(V, lo, r, p), agrees(V, hi, r, p), e), a, x), x => agrees_use(V, hi, r, p, and_r(agrees(V, lo, r, p), agrees(V, hi, r, p), e), a, x))

def agree_use.go(+a: String, +r: String, +p: Nat, +e: {Bool.and(agree(a, r, p), beq(bv(a, p), bv(r, p))) == True{} : Bool}, +q: Nat, c: {Nat.is_lt(q, p) == True{} : Bool} | {q == p : Nat}, ih: {Nat.is_lt(q, p) == True{} : Bool} -> {bv(a, q) == bv(r, q) : Bool}) -> {bv(a, q) == bv(r, q) : Bool}:
  match c:
    case Inl{lt}:
      ih(lt)
    case Inr{+same}:
      %Equal.sym(Nat, q, p, same) : {bv(a, _) == bv(r, _) : Bool}
      beq_true(bv(a, p), bv(r, p), and_r(agree(a, r, p), beq(bv(a, p), bv(r, p)), e))

# Keys that agree before `p` have the same bit at every position before it.
def agree_use(+a: String, +r: String, p: Nat, +e: {agree(a, r, p) == True{} : Bool}, +q: Nat, +eq: {Nat.is_lt(q, p) == True{} : Bool}) -> {bv(a, q) == bv(r, q) : Bool}:
  match p:
    case 0n:
      Empty.absurd({bv(a, q) == bv(r, q) : Bool}, lt_zero(q, eq))
    case 1n++pp:
      agree_use.go(a, r, pp, e, q, le_cases(q, pp, lt_succ(q, pp, eq)), x => agree_use(a, r, pp, and_l(agree(a, r, pp), beq(bv(a, pp), bv(r, pp)), e), q, x))

def side_fn(-V: Data, +m: Map<&2, V>, +p: Nat, +b: Bool, +e: {sides(V, m, p, b) == True{} : Bool}) -> Side(V, m, p, b):
  +a => ea => sides_use(V, m, p, b, e, a, ea)

def near_fn(-V: Data, +m: Map<&2, V>, +r: String, +p: Nat, +e: {agrees(V, m, r, p) == True{} : Bool}) -> Near(V, m, p):
  +a => +c => +q => ea => ec => +eq => Equal.trans(Bool, bv(a, q), bv(r, q), bv(c, q), agree_use(a, r, p, agrees_use(V, m, r, p, e, a, ea), q, eq), Equal.sym(Bool, bv(c, q), bv(r, q), agree_use(c, r, p, agrees_use(V, m, r, p, e, c, ec), q, eq)))

def pick_reach(-V: Data, +pos: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +k: String, -r: Maybe<&2, String>, +b: Bool, eb: {bv(k, pos) == b : Bool}, er: {Bool.pick(Maybe<&2, String>, bv(k, pos), reach(V, hi, k), reach(V, lo, k)) == r : Maybe<&2, String>}) -> {Bool.pick(Maybe<&2, String>, b, reach(V, hi, k), reach(V, lo, k)) == r : Maybe<&2, String>}:
  Equal.trans(Maybe<&2, String>, Bool.pick(Maybe<&2, String>, b, reach(V, hi, k), reach(V, lo, k)), Bool.pick(Maybe<&2, String>, bv(k, pos), reach(V, hi, k), reach(V, lo, k)), r, Equal.cong(Bool, Maybe<&2, String>, z => Bool.pick(Maybe<&2, String>, z, reach(V, hi, k), reach(V, lo, k)), b, bv(k, pos), Equal.sym(Bool, bv(k, pos), b, eb)), er)

def wf_reach.node(-V: Data, +pos: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +k: String, b: Bool, +eb: {bv(k, pos) == b : Bool}, +e: {Bool.pick(Maybe<&2, String>, bv(k, pos), reach(V, hi, k), reach(V, lo, k)) == None{} : Maybe<&2, String>}, ilo: {reach(V, lo, k) == None{} : Maybe<&2, String>} -> Empty, ihi: {reach(V, hi, k) == None{} : Maybe<&2, String>} -> Empty) -> Empty:
  match b:
    case True{}:
      ihi(pick_reach(V, pos, lo, hi, k, None{}, True{}, eb, e))
    case False{}:
      ilo(pick_reach(V, pos, lo, hi, k, None{}, False{}, eb, e))

# In a trie every key's bits lead to a leaf.
def wf_reach(-V: Data, m: Map<&2, V>, +w: Wf(V, m), +k: String, +e: {reach(V, m, k) == None{} : Maybe<&2, String>}) -> Empty:
  match m:
    case MTip{}:
      Str.false_true(w)
    case MLeaf{k1, v}:
      none_some(String, k1, Equal.sym(Maybe<&2, String>, Some{k1}, None{}, e))
    case MNode{+pos, +lo, +hi}:
      wf_reach.node(V, pos, lo, hi, k, bv(k, pos), {==}, e, e2 => wf_reach(V, lo, wf_lo(V, pos, lo, hi, w), k, e2), e2 => wf_reach(V, hi, wf_hi(V, pos, lo, hi, w), k, e2))

def reach_mem.node(-V: Data, +pos: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +k: String, +k0: String, b: Bool, +eb: {bv(k, pos) == b : Bool}, +er: {Bool.pick(Maybe<&2, String>, bv(k, pos), reach(V, hi, k), reach(V, lo, k)) == Some{k0} : Maybe<&2, String>}, ilo: {reach(V, lo, k) == Some{k0} : Maybe<&2, String>} -> {mem(V, lo, k0) == True{} : Bool}, ihi: {reach(V, hi, k) == Some{k0} : Maybe<&2, String>} -> {mem(V, hi, k0) == True{} : Bool}) -> {Bool.or(mem(V, lo, k0), mem(V, hi, k0)) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, mem(V, hi, k0), True{}, ihi(pick_reach(V, pos, lo, hi, k, Some{k0}, True{}, eb, er))) : {Bool.or(mem(V, lo, k0), _) == True{} : Bool}
      or_true_r(mem(V, lo, k0))
    case False{}:
      %Equal.sym(Bool, mem(V, lo, k0), True{}, ilo(pick_reach(V, pos, lo, hi, k, Some{k0}, False{}, eb, er))) : {Bool.or(_, mem(V, hi, k0)) == True{} : Bool}
      {==}

# The leaf a key's bits lead to is a key of the map.
def reach_mem(-V: Data, m: Map<&2, V>, +k: String, +k0: String, +er: {reach(V, m, k) == Some{k0} : Maybe<&2, String>}) -> {mem(V, m, k0) == True{} : Bool}:
  match m:
    case MTip{}:
      Empty.absurd({False{} == True{} : Bool}, none_some(String, k0, er))
    case MLeaf{+k1, v}:
      %Equal.sym(String, k1, k0, some_inj(String, k1, k0, er)) : {String.eq(k0, _) == True{} : Bool}
      Str.eq_refl(k0)
    case MNode{+pos, +lo, +hi}:
      reach_mem.node(V, pos, lo, hi, k, k0, bv(k, pos), {==}, er, e2 => reach_mem(V, lo, k, k0, e2), e2 => reach_mem(V, hi, k, k0, e2))

def found_none.node(-V: Data, +pos: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +j: String, ilo: {found(V, lo, j) == None{} : Maybe<&2, V>}, ihi: {found(V, hi, j) == None{} : Maybe<&2, V>}) -> {Bool.pick(Maybe<&2, V>, bv(j, pos), found(V, hi, j), found(V, lo, j)) == None{} : Maybe<&2, V>}:
  %Equal.sym(Maybe<&2, V>, found(V, hi, j), None{}, ihi) : {Bool.pick(Maybe<&2, V>, bv(j, pos), _, found(V, lo, j)) == None{} : Maybe<&2, V>}
  %Equal.sym(Maybe<&2, V>, found(V, lo, j), None{}, ilo) : {Bool.pick(Maybe<&2, V>, bv(j, pos), None{}, _) == None{} : Maybe<&2, V>}
  pick_same(Maybe<&2, V>, bv(j, pos), None{})

# A key that is at no leaf finds nothing.
def found_none(-V: Data, m: Map<&2, V>, +j: String, +e: {mem(V, m, j) == False{} : Bool}) -> {found(V, m, j) == None{} : Maybe<&2, V>}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k, +v}:
      %Equal.sym(Bool, String.eq(j, k), False{}, e) : {Bool.pick(Maybe<&2, V>, _, Some{v}, None{}) == None{} : Maybe<&2, V>}
      {==}
    case MNode{+pos, +lo, +hi}:
      found_none.node(V, pos, lo, hi, j, found_none(V, lo, j, or_false_l(mem(V, lo, j), mem(V, hi, j), e)), found_none(V, hi, j, or_false_r(mem(V, lo, j), mem(V, hi, j), e)))

# Every other key finds what it found before
# -------------------------------------------

def reach_side.go(-V: Data, +q: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +k: String, +k0: String, slo: Side(V, lo, q, False{}), shi: Side(V, hi, q, True{}), b: Bool, +eb: {bv(k, q) == b : Bool}, +er: {Bool.pick(Maybe<&2, String>, bv(k, q), reach(V, hi, k), reach(V, lo, k)) == Some{k0} : Maybe<&2, String>}) -> {bv(k0, q) == bv(k, q) : Bool}:
  match b:
    case True{}:
      Equal.trans(Bool, bv(k0, q), True{}, bv(k, q), shi(k0, reach_mem(V, hi, k, k0, pick_reach(V, q, lo, hi, k, Some{k0}, True{}, eb, er))), Equal.sym(Bool, bv(k, q), True{}, eb))
    case False{}:
      Equal.trans(Bool, bv(k0, q), False{}, bv(k, q), slo(k0, reach_mem(V, lo, k, k0, pick_reach(V, q, lo, hi, k, Some{k0}, False{}, eb, er))), Equal.sym(Bool, bv(k, q), False{}, eb))

# The leaf a key's bits lead to has the key's bit at every node on the way.
def reach_side(-V: Data, +q: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, slo: Side(V, lo, q, False{}), shi: Side(V, hi, q, True{}), +k: String, +k0: String, er: {reach(V, MNode{q, lo, hi}, k) == Some{k0} : Maybe<&2, String>}) -> {bv(k0, q) == bv(k, q) : Bool}:
  reach_side.go(V, q, lo, hi, k, k0, slo, shi, bv(k, q), {==}, er)

def p_below.go(-V: Data, +q: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, slo: Side(V, lo, q, False{}), shi: Side(V, hi, q, True{}), +k: String, +k0: String, er: {reach(V, MNode{q, lo, hi}, k) == Some{k0} : Maybe<&2, String>}, ekk0: {String.eq(k, k0) == False{} : Bool}, r: {Nat.is_lt(Map.diff(k, k0), q) == True{} : Bool} | {Map.diff(k, k0) == q : Nat}) -> {Nat.is_lt(Map.diff(k, k0), q) == True{} : Bool}:
  match r:
    case Inl{lt}:
      lt
    case Inr{+same}:
      +rs = reach_side(V, q, lo, hi, slo, shi, k, k0, er)
      +sp = Equal.trans(Bool, bv(k, q), bv(k, Map.diff(k, k0)), Bool.not(bv(k0, q)), Equal.cong(Nat, Bool, z => bv(k, z), q, Map.diff(k, k0), Equal.sym(Nat, Map.diff(k, k0), q, same)), Equal.trans(Bool, bv(k, Map.diff(k, k0)), Bool.not(bv(k0, Map.diff(k, k0))), Bool.not(bv(k0, q)), split_at_diff(k, k0, ekk0), Equal.cong(Nat, Bool, z => Bool.not(bv(k0, z)), Map.diff(k, k0), q, same)))
      Empty.absurd({Nat.is_lt(Map.diff(k, k0), q) == True{} : Bool}, not_self(bv(k0, q), Equal.trans(Bool, bv(k0, q), bv(k, q), Bool.not(bv(k0, q)), rs, sp)))

# Where `Map.ins` stops at a node, the node is past where the new key and
# the leaf it reached part.
def p_below(-V: Data, +q: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, slo: Side(V, lo, q, False{}), shi: Side(V, hi, q, True{}), +k: String, +k0: String, er: {reach(V, MNode{q, lo, hi}, k) == Some{k0} : Maybe<&2, String>}, ekk0: {String.eq(k, k0) == False{} : Bool}, et: {Nat.is_lt(q, Map.diff(k, k0)) == False{} : Bool}) -> {Nat.is_lt(Map.diff(k, k0), q) == True{} : Bool}:
  p_below.go(V, q, lo, hi, slo, shi, k, k0, er, ekk0, le_cases(Map.diff(k, k0), q, not_lt(q, Map.diff(k, k0), et)))

# Every key under that node is on the other side of the parting from the
# new key.
def far_node(-V: Data, +q: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, slo: Side(V, lo, q, False{}), shi: Side(V, hi, q, True{}), near: Near(V, MNode{q, lo, hi}, q), +k: String, +k0: String, +er: {reach(V, MNode{q, lo, hi}, k) == Some{k0} : Maybe<&2, String>}, +ekk0: {String.eq(k, k0) == False{} : Bool}, et: {Nat.is_lt(q, Map.diff(k, k0)) == False{} : Bool}, +a: String, ea: {mem(V, MNode{q, lo, hi}, a) == True{} : Bool}) -> {bv(a, Map.diff(k, k0)) == Bool.not(bv(k, Map.diff(k, k0))) : Bool}:
  +pq = p_below(V, q, lo, hi, slo, shi, k, k0, er, ekk0, et)
  +n1 = near(a, k0, Map.diff(k, k0), ea, reach_mem(V, MNode{q, lo, hi}, k, k0, er), pq)
  Equal.trans(Bool, bv(a, Map.diff(k, k0)), bv(k0, Map.diff(k, k0)), Bool.not(bv(k, Map.diff(k, k0))), n1, flip(bv(k, Map.diff(k, k0)), bv(k0, Map.diff(k, k0)), split_at_diff(k, k0, ekk0)))

def leaf_far(-V: Data, +k: String, +k0: String, ekk0: {String.eq(k, k0) == False{} : Bool}, +k1: String, -v: V, er: {Some{k1} == Some{k0} : Maybe<&2, String>}, +a: String, ea: {mem(V, MLeaf{k1, v}, a) == True{} : Bool}) -> {bv(a, Map.diff(k, k0)) == Bool.not(bv(k, Map.diff(k, k0))) : Bool}:
  +ak0 = Equal.trans(String, a, k1, k0, Str.eq_true(a, k1, ea), some_inj(String, k1, k0, er))
  %Equal.sym(String, a, k0, ak0) : {bv(_, Map.diff(k, k0)) == Bool.not(bv(k, Map.diff(k, k0))) : Bool}
  flip(bv(k, Map.diff(k, k0)), bv(k0, Map.diff(k, k0)), split_at_diff(k, k0, ekk0))

def rest_none.go(-V: Data, +rest: Map<&2, V>, +j: String, +p: Nat, +k: String, far: @a:String -> {mem(V, rest, a) == True{} : Bool} -> {bv(a, p) == Bool.not(bv(k, p)) : Bool}, e: {bv(j, p) == bv(k, p) : Bool}, s: Bool, es: {mem(V, rest, j) == s : Bool}) -> {found(V, rest, j) == None{} : Maybe<&2, V>}:
  match s:
    case False{}:
      found_none(V, rest, j, es)
    case True{}:
      Empty.absurd({found(V, rest, j) == None{} : Maybe<&2, V>}, not_self(bv(k, p), Equal.trans(Bool, bv(k, p), bv(j, p), Bool.not(bv(k, p)), Equal.sym(Bool, bv(j, p), bv(k, p), e), far(j, es))))

def rest_none(-V: Data, +rest: Map<&2, V>, +j: String, +p: Nat, +k: String, far: @a:String -> {mem(V, rest, a) == True{} : Bool} -> {bv(a, p) == Bool.not(bv(k, p)) : Bool}, e: {bv(j, p) == bv(k, p) : Bool}) -> {found(V, rest, j) == None{} : Maybe<&2, V>}:
  rest_none.go(V, rest, j, p, k, far, e, mem(V, rest, j), {==})

# A node spliced in where every key already there is on the far side
# changes nothing another key finds.
def splice_other.go(-V: Data, +p: Nat, +k: String, +x: V, +rest: Map<&2, V>, +j: String, +ejk: {String.eq(j, k) == False{} : Bool}, far: @a:String -> {mem(V, rest, a) == True{} : Bool} -> {bv(a, p) == Bool.not(bv(k, p)) : Bool}, b: Bool, +eb: {bv(k, p) == b : Bool}, c: Bool, +ec: {bv(j, p) == c : Bool}) -> {found(V, csplice(V, p, k, x, rest), j) == found(V, rest, j) : Maybe<&2, V>}:
  match b c:
    case True{} True{}:
      %Equal.sym(Bool, bv(k, p), True{}, eb) : {found(V, Bool.pick(Map<&2, V>, _, MNode{p, rest, MLeaf{k, x}}, MNode{p, MLeaf{k, x}, rest}), j) == found(V, rest, j) : Maybe<&2, V>}
      %Equal.sym(Bool, bv(j, p), True{}, ec) : {Bool.pick(Maybe<&2, V>, _, found(V, MLeaf{k, x}, j), found(V, rest, j)) == found(V, rest, j) : Maybe<&2, V>}
      Equal.trans(Maybe<&2, V>, found(V, MLeaf{k, x}, j), None{}, found(V, rest, j), found_leaf_other(V, k, x, j, ejk), Equal.sym(Maybe<&2, V>, found(V, rest, j), None{}, rest_none(V, rest, j, p, k, far, Equal.trans(Bool, bv(j, p), True{}, bv(k, p), ec, Equal.sym(Bool, bv(k, p), True{}, eb)))))
    case True{} False{}:
      %Equal.sym(Bool, bv(k, p), True{}, eb) : {found(V, Bool.pick(Map<&2, V>, _, MNode{p, rest, MLeaf{k, x}}, MNode{p, MLeaf{k, x}, rest}), j) == found(V, rest, j) : Maybe<&2, V>}
      %Equal.sym(Bool, bv(j, p), False{}, ec) : {Bool.pick(Maybe<&2, V>, _, found(V, MLeaf{k, x}, j), found(V, rest, j)) == found(V, rest, j) : Maybe<&2, V>}
      {==}
    case False{} True{}:
      %Equal.sym(Bool, bv(k, p), False{}, eb) : {found(V, Bool.pick(Map<&2, V>, _, MNode{p, rest, MLeaf{k, x}}, MNode{p, MLeaf{k, x}, rest}), j) == found(V, rest, j) : Maybe<&2, V>}
      %Equal.sym(Bool, bv(j, p), True{}, ec) : {Bool.pick(Maybe<&2, V>, _, found(V, rest, j), found(V, MLeaf{k, x}, j)) == found(V, rest, j) : Maybe<&2, V>}
      {==}
    case False{} False{}:
      %Equal.sym(Bool, bv(k, p), False{}, eb) : {found(V, Bool.pick(Map<&2, V>, _, MNode{p, rest, MLeaf{k, x}}, MNode{p, MLeaf{k, x}, rest}), j) == found(V, rest, j) : Maybe<&2, V>}
      %Equal.sym(Bool, bv(j, p), False{}, ec) : {Bool.pick(Maybe<&2, V>, _, found(V, rest, j), found(V, MLeaf{k, x}, j)) == found(V, rest, j) : Maybe<&2, V>}
      Equal.trans(Maybe<&2, V>, found(V, MLeaf{k, x}, j), None{}, found(V, rest, j), found_leaf_other(V, k, x, j, ejk), Equal.sym(Maybe<&2, V>, found(V, rest, j), None{}, rest_none(V, rest, j, p, k, far, Equal.trans(Bool, bv(j, p), False{}, bv(k, p), ec, Equal.sym(Bool, bv(k, p), False{}, eb)))))

def splice_other(-V: Data, +p: Nat, +k: String, +x: V, +rest: Map<&2, V>, +j: String, ejk: {String.eq(j, k) == False{} : Bool}, far: @a:String -> {mem(V, rest, a) == True{} : Bool} -> {bv(a, p) == Bool.not(bv(k, p)) : Bool}) -> {found(V, csplice(V, p, k, x, rest), j) == found(V, rest, j) : Maybe<&2, V>}:
  splice_other.go(V, p, k, x, rest, j, ejk, far, bv(k, p), {==}, bv(j, p), {==})

# Down one side of a node, the other key goes the same way or never meets
# what changed.
def other.node(-V: Data, +pos: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +lo2: Map<&2, V>, +hi2: Map<&2, V>, +k: String, +k0: String, +j: String, b: Bool, +eb: {bv(k, pos) == b : Bool}, c: Bool, +ec: {bv(j, pos) == c : Bool}, +er: {Bool.pick(Maybe<&2, String>, bv(k, pos), reach(V, hi, k), reach(V, lo, k)) == Some{k0} : Maybe<&2, String>}, ilo: {reach(V, lo, k) == Some{k0} : Maybe<&2, String>} -> {found(V, lo2, j) == found(V, lo, j) : Maybe<&2, V>}, ihi: {reach(V, hi, k) == Some{k0} : Maybe<&2, String>} -> {found(V, hi2, j) == found(V, hi, j) : Maybe<&2, V>}) -> {found(V, Bool.pick(Map<&2, V>, bv(k, pos), MNode{pos, lo, hi2}, MNode{pos, lo2, hi}), j) == Bool.pick(Maybe<&2, V>, bv(j, pos), found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}:
  match b c:
    case True{} True{}:
      %Equal.sym(Bool, bv(k, pos), True{}, eb) : {found(V, Bool.pick(Map<&2, V>, _, MNode{pos, lo, hi2}, MNode{pos, lo2, hi}), j) == Bool.pick(Maybe<&2, V>, bv(j, pos), found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}
      %Equal.sym(Bool, bv(j, pos), True{}, ec) : {Bool.pick(Maybe<&2, V>, _, found(V, hi2, j), found(V, lo, j)) == Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}
      ihi(pick_reach(V, pos, lo, hi, k, Some{k0}, True{}, eb, er))
    case True{} False{}:
      %Equal.sym(Bool, bv(k, pos), True{}, eb) : {found(V, Bool.pick(Map<&2, V>, _, MNode{pos, lo, hi2}, MNode{pos, lo2, hi}), j) == Bool.pick(Maybe<&2, V>, bv(j, pos), found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}
      %Equal.sym(Bool, bv(j, pos), False{}, ec) : {Bool.pick(Maybe<&2, V>, _, found(V, hi2, j), found(V, lo, j)) == Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}
      {==}
    case False{} True{}:
      %Equal.sym(Bool, bv(k, pos), False{}, eb) : {found(V, Bool.pick(Map<&2, V>, _, MNode{pos, lo, hi2}, MNode{pos, lo2, hi}), j) == Bool.pick(Maybe<&2, V>, bv(j, pos), found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}
      %Equal.sym(Bool, bv(j, pos), True{}, ec) : {Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, lo2, j)) == Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}
      {==}
    case False{} False{}:
      %Equal.sym(Bool, bv(k, pos), False{}, eb) : {found(V, Bool.pick(Map<&2, V>, _, MNode{pos, lo, hi2}, MNode{pos, lo2, hi}), j) == Bool.pick(Maybe<&2, V>, bv(j, pos), found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}
      %Equal.sym(Bool, bv(j, pos), False{}, ec) : {Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, lo2, j)) == Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}
      ilo(pick_reach(V, pos, lo, hi, k, Some{k0}, False{}, eb, er))

# Writing a key's value where its leaf is changes nothing another key
# finds.
def put_other(-V: Data, m: Map<&2, V>, +k: String, +x: V, +k0: String, +j: String, +er: {reach(V, m, k) == Some{k0} : Maybe<&2, String>}, +ek: {String.eq(k, k0) == True{} : Bool}, +ejk: {String.eq(j, k) == False{} : Bool}) -> {found(V, cput(V, m, k, x), j) == found(V, m, j) : Maybe<&2, V>}:
  match m:
    case MTip{}:
      found_leaf_other(V, k, x, j, ejk)
    case MLeaf{+k1, +v}:
      +k1k = Equal.trans(String, k1, k0, k, some_inj(String, k1, k0, er), Equal.sym(String, k, k0, Str.eq_true(k, k0, ek)))
      +ejk1 = Equal.trans(Bool, String.eq(j, k1), String.eq(j, k), False{}, Equal.cong(String, Bool, z => String.eq(j, z), k1, k, k1k), ejk)
      Equal.trans(Maybe<&2, V>, found(V, MLeaf{k1, x}, j), None{}, found(V, MLeaf{k1, v}, j), found_leaf_other(V, k1, x, j, ejk1), Equal.sym(Maybe<&2, V>, found(V, MLeaf{k1, v}, j), None{}, found_leaf_other(V, k1, v, j, ejk1)))
    case MNode{+pos, +lo, +hi}:
      other.node(V, pos, lo, hi, cput(V, lo, k, x), cput(V, hi, k, x), k, k0, j, bv(k, pos), {==}, bv(j, pos), {==}, er, e2 => put_other(V, lo, k, x, k0, j, e2, ek, ejk), e2 => put_other(V, hi, k, x, k0, j, e2, ek, ejk))

def ins_other.node(-V: Data, +q: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, slo: Side(V, lo, q, False{}), shi: Side(V, hi, q, True{}), near: Near(V, MNode{q, lo, hi}, q), +k: String, +x: V, +k0: String, +j: String, +er: {reach(V, MNode{q, lo, hi}, k) == Some{k0} : Maybe<&2, String>}, ekk0: {String.eq(k, k0) == False{} : Bool}, ejk: {String.eq(j, k) == False{} : Bool}, t: Bool, +et: {Nat.is_lt(q, Map.diff(k, k0)) == t : Bool}, ilo: {reach(V, lo, k) == Some{k0} : Maybe<&2, String>} -> {found(V, cins(V, lo, k, x, Map.diff(k, k0)), j) == found(V, lo, j) : Maybe<&2, V>}, ihi: {reach(V, hi, k) == Some{k0} : Maybe<&2, String>} -> {found(V, cins(V, hi, k, x, Map.diff(k, k0)), j) == found(V, hi, j) : Maybe<&2, V>}) -> {found(V, cins(V, MNode{q, lo, hi}, k, x, Map.diff(k, k0)), j) == found(V, MNode{q, lo, hi}, j) : Maybe<&2, V>}:
  match t:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(q, Map.diff(k, k0)), True{}, et) : {found(V, Bool.pick(Map<&2, V>, _, Bool.pick(Map<&2, V>, bv(k, q), MNode{q, lo, cins(V, hi, k, x, Map.diff(k, k0))}, MNode{q, cins(V, lo, k, x, Map.diff(k, k0)), hi}), csplice(V, Map.diff(k, k0), k, x, MNode{q, lo, hi})), j) == found(V, MNode{q, lo, hi}, j) : Maybe<&2, V>}
      other.node(V, q, lo, hi, cins(V, lo, k, x, Map.diff(k, k0)), cins(V, hi, k, x, Map.diff(k, k0)), k, k0, j, bv(k, q), {==}, bv(j, q), {==}, er, ilo, ihi)
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(q, Map.diff(k, k0)), False{}, et) : {found(V, Bool.pick(Map<&2, V>, _, Bool.pick(Map<&2, V>, bv(k, q), MNode{q, lo, cins(V, hi, k, x, Map.diff(k, k0))}, MNode{q, cins(V, lo, k, x, Map.diff(k, k0)), hi}), csplice(V, Map.diff(k, k0), k, x, MNode{q, lo, hi})), j) == found(V, MNode{q, lo, hi}, j) : Maybe<&2, V>}
      splice_other(V, Map.diff(k, k0), k, x, MNode{q, lo, hi}, j, ejk, a => ea => far_node(V, q, lo, hi, slo, shi, near, k, k0, er, ekk0, et, a, ea))

# A node spliced in for a new key changes nothing another key finds.
def ins_other(-V: Data, m: Map<&2, V>, +w: Wf(V, m), +k: String, +x: V, +k0: String, +j: String, +er: {reach(V, m, k) == Some{k0} : Maybe<&2, String>}, +ekk0: {String.eq(k, k0) == False{} : Bool}, +ejk: {String.eq(j, k) == False{} : Bool}) -> {found(V, cins(V, m, k, x, Map.diff(k, k0)), j) == found(V, m, j) : Maybe<&2, V>}:
  match m:
    case MTip{}:
      Empty.absurd({found(V, MLeaf{k, x}, j) == None{} : Maybe<&2, V>}, Str.false_true(w))
    case MLeaf{+k1, +v}:
      splice_other(V, Map.diff(k, k0), k, x, MLeaf{k1, v}, j, ejk, a => ea => leaf_far(V, k, k0, ekk0, k1, v, er, a, ea))
    case MNode{+q, +lo, +hi}:
      ins_other.node(V, q, lo, hi, side_fn(V, lo, q, False{}, wf_slo(V, q, lo, hi, w)), side_fn(V, hi, q, True{}, wf_shi(V, q, lo, hi, w)), near_fn(V, MNode{q, lo, hi}, rep(V, lo), q, wf_near(V, q, lo, hi, w)), k, x, k0, j, er, ekk0, ejk, Nat.is_lt(q, Map.diff(k, k0)), {==}, e2 => ins_other(V, lo, wf_lo(V, q, lo, hi, w), k, x, k0, j, e2, ekk0, ejk), e2 => ins_other(V, hi, wf_hi(V, q, lo, hi, w), k, x, k0, j, e2, ekk0, ejk))

def set_other.fin(-V: Data, +m: Map<&2, V>, +w: Wf(V, m), +k: String, +x: V, +k0: String, +j: String, +er: {reach(V, m, k) == Some{k0} : Maybe<&2, String>}, +ejk: {String.eq(j, k) == False{} : Bool}, c: Cmp, +ec: {String.order(k, k0) == c : Cmp}) -> {found(V, cfin(V, m, k, x, k0, String.order(k, k0)), j) == found(V, m, j) : Maybe<&2, V>}:
  match c:
    case LT{}:
      %Equal.sym(Cmp, String.order(k, k0), LT{}, ec) : {found(V, cfin(V, m, k, x, k0, _), j) == found(V, m, j) : Maybe<&2, V>}
      ins_other(V, m, w, k, x, k0, j, er, eq_of_order(k, k0, LT{}, ec), ejk)
    case EQ{}:
      %Equal.sym(Cmp, String.order(k, k0), EQ{}, ec) : {found(V, cfin(V, m, k, x, k0, _), j) == found(V, m, j) : Maybe<&2, V>}
      put_other(V, m, k, x, k0, j, er, eq_of_order(k, k0, EQ{}, ec), ejk)
    case GT{}:
      %Equal.sym(Cmp, String.order(k, k0), GT{}, ec) : {found(V, cfin(V, m, k, x, k0, _), j) == found(V, m, j) : Maybe<&2, V>}
      ins_other(V, m, w, k, x, k0, j, er, eq_of_order(k, k0, GT{}, ec), ejk)

def set_other.of(-V: Data, +m: Map<&2, V>, +w: Wf(V, m), +k: String, +x: V, +j: String, ejk: {String.eq(j, k) == False{} : Bool}, r: Maybe<&2, String>, +er: {reach(V, m, k) == r : Maybe<&2, String>}) -> {found(V, cset.of(V, m, k, x, reach(V, m, k)), j) == found(V, m, j) : Maybe<&2, V>}:
  match r:
    case None{}:
      Empty.absurd({found(V, cset.of(V, m, k, x, reach(V, m, k)), j) == found(V, m, j) : Maybe<&2, V>}, wf_reach(V, m, w, k, er))
    case Some{+k0}:
      %Equal.sym(Maybe<&2, String>, reach(V, m, k), Some{k0}, er) : {found(V, cset.of(V, m, k, x, _), j) == found(V, m, j) : Maybe<&2, V>}
      set_other.fin(V, m, w, k, x, k0, j, er, ejk, String.order(k, k0), {==})

def set_other(-V: Data, +m: Map<&2, V>, w: Wf(V, m), +k: String, +x: V, +j: String, ejk: {String.eq(j, k) == False{} : Bool}) -> {found(V, cset(V, m, k, x), j) == found(V, m, j) : Maybe<&2, V>}:
  set_other.of(V, m, w, k, x, j, ejk, reach(V, m, k), {==})

# In every map `Map.new` and `Map.set` build, writing one key changes
# nothing any other key finds.
def set_other_top(-V: Data, m: Map<&2, V>, w: Wf.top(V, m), +k: String, +x: V, +j: String, +ejk: {String.eq(j, k) == False{} : Bool}) -> {found(V, cset(V, m, k, x), j) == found(V, m, j) : Maybe<&2, V>}:
  match m:
    case MTip{}:
      found_leaf_other(V, k, x, j, ejk)
    case MLeaf{+k1, +v}:
      set_other(V, MLeaf{k1, v}, {==}, k, x, j, ejk)
    case MNode{+p, +lo, +hi}:
      set_other(V, MNode{p, lo, hi}, w, k, x, j, ejk)

# `Map.set` keeps the invariant
# -----------------------------

def and_t(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

def and_true_id(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def and_comm(a: Bool, b: Bool) -> {Bool.and(a, b) == Bool.and(b, a) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def and_assoc(a: Bool, b: Bool, c: Bool) -> {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def and_swap(a: Bool, b: Bool, c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(b, Bool.and(a, c)) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def le_lt(+q: Nat, d: Nat, +e: {Nat.is_le(1n+q, d) == True{} : Bool}) -> {Nat.is_lt(q, d) == True{} : Bool}:
  match q d:
    case _ 0n:
      Empty.absurd({Nat.is_lt(q, 0n) == True{} : Bool}, Str.false_true(e))
    case 0n 1n+dp:
      {==}
    case 1n+qp 1n+dp:
      le_lt(qp, dp, e)

def lt_le_weak(+a: Nat, +b: Nat, +e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n _:
      le0(b)
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, Str.false_true(e))
    case 1n+ap 1n+bp:
      lt_le_weak(ap, bp, e)

# Agreeing before a position
# --------------------------

def agree_refl(+a: String, p: Nat) -> {agree(a, a, p) == True{} : Bool}:
  match p:
    case 0n:
      {==}
    case 1n++q:
      and_t(agree(a, a, q), beq(bv(a, q), bv(a, q)), agree_refl(a, q), beq_refl(bv(a, q)))

def agree_sym(+a: String, +b: String, p: Nat, +e: {agree(a, b, p) == True{} : Bool}) -> {agree(b, a, p) == True{} : Bool}:
  match p:
    case 0n:
      {==}
    case 1n++q:
      +same = beq_true(bv(a, q), bv(b, q), and_r(agree(a, b, q), beq(bv(a, q), bv(b, q)), e))
      +bq = Equal.trans(Bool, beq(bv(b, q), bv(a, q)), beq(bv(b, q), bv(b, q)), True{}, Equal.cong(Bool, Bool, z => beq(bv(b, q), z), bv(a, q), bv(b, q), same), beq_refl(bv(b, q)))
      and_t(agree(b, a, q), beq(bv(b, q), bv(a, q)), agree_sym(a, b, q, and_l(agree(a, b, q), beq(bv(a, q), bv(b, q)), e)), bq)

def agree_trans(+a: String, +b: String, +c: String, p: Nat, +e1: {agree(a, b, p) == True{} : Bool}, +e2: {agree(b, c, p) == True{} : Bool}) -> {agree(a, c, p) == True{} : Bool}:
  match p:
    case 0n:
      {==}
    case 1n++q:
      +s1 = beq_true(bv(a, q), bv(b, q), and_r(agree(a, b, q), beq(bv(a, q), bv(b, q)), e1))
      +s2 = beq_true(bv(b, q), bv(c, q), and_r(agree(b, c, q), beq(bv(b, q), bv(c, q)), e2))
      +bq = Equal.trans(Bool, beq(bv(a, q), bv(c, q)), beq(bv(c, q), bv(c, q)), True{}, Equal.cong(Bool, Bool, z => beq(z, bv(c, q)), bv(a, q), bv(c, q), Equal.trans(Bool, bv(a, q), bv(b, q), bv(c, q), s1, s2)), beq_refl(bv(c, q)))
      and_t(agree(a, c, q), beq(bv(a, q), bv(c, q)), agree_trans(a, b, c, q, and_l(agree(a, b, q), beq(bv(a, q), bv(b, q)), e1), and_l(agree(b, c, q), beq(bv(b, q), bv(c, q)), e2)), bq)

def agree_mono.go(+a: String, +b: String, +q: Nat, +e: {agree(a, b, 1n+q) == True{} : Bool}, +p2: Nat, c: {Nat.is_lt(p2, 1n+q) == True{} : Bool} | {p2 == 1n+q : Nat}, ih: {Nat.is_le(p2, q) == True{} : Bool} -> {agree(a, b, p2) == True{} : Bool}) -> {agree(a, b, p2) == True{} : Bool}:
  match c:
    case Inl{lt}:
      ih(lt_succ(p2, q, lt))
    case Inr{+same}:
      %Equal.sym(Nat, p2, 1n+q, same) : {agree(a, b, _) == True{} : Bool}
      e

# Agreeing before a position is agreeing before any earlier one.
def agree_mono(+a: String, +b: String, p: Nat, +e: {agree(a, b, p) == True{} : Bool}, +p2: Nat, +le: {Nat.is_le(p2, p) == True{} : Bool}) -> {agree(a, b, p2) == True{} : Bool}:
  match p:
    case 0n:
      %Equal.sym(Nat, p2, 0n, le_zero(p2, le)) : {agree(a, b, _) == True{} : Bool}
      {==}
    case 1n++q:
      agree_mono.go(a, b, q, e, p2, le_cases(p2, 1n+q, le), x => agree_mono(a, b, q, and_l(agree(a, b, q), beq(bv(a, q), bv(b, q)), e), p2, x))

def agree_below(+a: String, +b: String, n: Nat, +le: {Nat.is_le(n, Map.diff(a, b)) == True{} : Bool}) -> {agree(a, b, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++q:
      +lt = le_lt(q, Map.diff(a, b), le)
      +same = agree_below_diff(a, b, q, lt)
      +bq = Equal.trans(Bool, beq(bv(a, q), bv(b, q)), beq(bv(b, q), bv(b, q)), True{}, Equal.cong(Bool, Bool, z => beq(z, bv(b, q)), bv(a, q), bv(b, q), same), beq_refl(bv(b, q)))
      and_t(agree(a, b, q), beq(bv(a, q), bv(b, q)), agree_below(a, b, q, lt_le_weak(q, Map.diff(a, b), lt)), bq)

# Two keys agree before `Map.diff` of them.
def agree_diff(+a: String, +b: String) -> {agree(a, b, Map.diff(a, b)) == True{} : Bool}:
  agree_below(a, b, Map.diff(a, b), le_refl(Map.diff(a, b)))

# Keys of a subtree
# -----------------

def sides_of_agrees(-V: Data, m: Map<&2, V>, +r: String, +q: Nat, +e: {agrees(V, m, r, q) == True{} : Bool}, +p: Nat, +pq: {Nat.is_lt(p, q) == True{} : Bool}) -> {sides(V, m, p, bv(r, p)) == True{} : Bool}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k, v}:
      %Equal.sym(Bool, bv(k, p), bv(r, p), agree_use(k, r, q, e, p, pq)) : {beq(_, bv(r, p)) == True{} : Bool}
      beq_refl(bv(r, p))
    case MNode{qq, +lo, +hi}:
      and_t(sides(V, lo, p, bv(r, p)), sides(V, hi, p, bv(r, p)), sides_of_agrees(V, lo, r, q, and_l(agrees(V, lo, r, q), agrees(V, hi, r, q), e), p, pq), sides_of_agrees(V, hi, r, q, and_r(agrees(V, lo, r, q), agrees(V, hi, r, q), e), p, pq))

def agrees_trans(-V: Data, m: Map<&2, V>, +r1: String, +r2: String, +p: Nat, +e: {agrees(V, m, r1, p) == True{} : Bool}, +e2: {agree(r1, r2, p) == True{} : Bool}) -> {agrees(V, m, r2, p) == True{} : Bool}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k, v}:
      agree_trans(k, r1, r2, p, e, e2)
    case MNode{qq, +lo, +hi}:
      and_t(agrees(V, lo, r2, p), agrees(V, hi, r2, p), agrees_trans(V, lo, r1, r2, p, and_l(agrees(V, lo, r1, p), agrees(V, hi, r1, p), e), e2), agrees_trans(V, hi, r1, r2, p, and_r(agrees(V, lo, r1, p), agrees(V, hi, r1, p), e), e2))

def agrees_mono(-V: Data, m: Map<&2, V>, +r: String, +p: Nat, +e: {agrees(V, m, r, p) == True{} : Bool}, +p2: Nat, +le: {Nat.is_le(p2, p) == True{} : Bool}) -> {agrees(V, m, r, p2) == True{} : Bool}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k, v}:
      agree_mono(k, r, p, e, p2, le)
    case MNode{qq, +lo, +hi}:
      and_t(agrees(V, lo, r, p2), agrees(V, hi, r, p2), agrees_mono(V, lo, r, p, and_l(agrees(V, lo, r, p), agrees(V, hi, r, p), e), p2, le), agrees_mono(V, hi, r, p, and_r(agrees(V, lo, r, p), agrees(V, hi, r, p), e), p2, le))

# Where every key agrees with one key of the subtree, every key agrees with
# any other.
def agrees_switch(-V: Data, +m: Map<&2, V>, +r: String, +r2: String, +p: Nat, +e: {agrees(V, m, r, p) == True{} : Bool}, er2: {mem(V, m, r2) == True{} : Bool}) -> {agrees(V, m, r2, p) == True{} : Bool}:
  agrees_trans(V, m, r, r2, p, e, agree_sym(r2, r, p, agrees_use(V, m, r, p, e, r2, er2)))

def rep_mem(-V: Data, m: Map<&2, V>, +w: {wf(V, m) == True{} : Bool}) -> {mem(V, m, rep(V, m)) == True{} : Bool}:
  match m:
    case MTip{}:
      Empty.absurd({False{} == True{} : Bool}, Str.false_true(w))
    case MLeaf{+k, v}:
      Str.eq_refl(k)
    case MNode{+p, +lo, +hi}:
      %Equal.sym(Bool, mem(V, lo, rep(V, lo)), True{}, rep_mem(V, lo, wf_lo(V, p, lo, hi, w))) : {Bool.or(_, mem(V, hi, rep(V, lo))) == True{} : Bool}
      {==}

# What `cins` and `cput` do to a subtree's keys
# ----------------------------------------------

def mem_splice.go(-V: Data, +p: Nat, +k: String, +x: V, +rest: Map<&2, V>, +a: String, c: Bool, +ec: {bv(k, p) == c : Bool}) -> {mem(V, csplice(V, p, k, x, rest), a) == Bool.or(String.eq(a, k), mem(V, rest, a)) : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, bv(k, p), True{}, ec) : {mem(V, Bool.pick(Map<&2, V>, _, MNode{p, rest, MLeaf{k, x}}, MNode{p, MLeaf{k, x}, rest}), a) == Bool.or(String.eq(a, k), mem(V, rest, a)) : Bool}
      or_comm(mem(V, rest, a), String.eq(a, k))
    case False{}:
      %Equal.sym(Bool, bv(k, p), False{}, ec) : {mem(V, Bool.pick(Map<&2, V>, _, MNode{p, rest, MLeaf{k, x}}, MNode{p, MLeaf{k, x}, rest}), a) == Bool.or(String.eq(a, k), mem(V, rest, a)) : Bool}
      {==}

def mem_splice(-V: Data, +p: Nat, +k: String, +x: V, +rest: Map<&2, V>, +a: String) -> {mem(V, csplice(V, p, k, x, rest), a) == Bool.or(String.eq(a, k), mem(V, rest, a)) : Bool}:
  mem_splice.go(V, p, k, x, rest, a, bv(k, p), {==})

def mem_ins.deep(-V: Data, +q: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +k: String, +x: V, +p: Nat, +a: String, dir: Bool, +ed: {bv(k, q) == dir : Bool}, ilo: {mem(V, cins(V, lo, k, x, p), a) == Bool.or(String.eq(a, k), mem(V, lo, a)) : Bool}, ihi: {mem(V, cins(V, hi, k, x, p), a) == Bool.or(String.eq(a, k), mem(V, hi, a)) : Bool}) -> {mem(V, Bool.pick(Map<&2, V>, bv(k, q), MNode{q, lo, cins(V, hi, k, x, p)}, MNode{q, cins(V, lo, k, x, p), hi}), a) == Bool.or(String.eq(a, k), Bool.or(mem(V, lo, a), mem(V, hi, a))) : Bool}:
  match dir:
    case True{}:
      %Equal.sym(Bool, bv(k, q), True{}, ed) : {mem(V, Bool.pick(Map<&2, V>, _, MNode{q, lo, cins(V, hi, k, x, p)}, MNode{q, cins(V, lo, k, x, p), hi}), a) == Bool.or(String.eq(a, k), Bool.or(mem(V, lo, a), mem(V, hi, a))) : Bool}
      %Equal.sym(Bool, mem(V, cins(V, hi, k, x, p), a), Bool.or(String.eq(a, k), mem(V, hi, a)), ihi) : {Bool.or(mem(V, lo, a), _) == Bool.or(String.eq(a, k), Bool.or(mem(V, lo, a), mem(V, hi, a))) : Bool}
      or_swap(mem(V, lo, a), String.eq(a, k), mem(V, hi, a))
    case False{}:
      %Equal.sym(Bool, bv(k, q), False{}, ed) : {mem(V, Bool.pick(Map<&2, V>, _, MNode{q, lo, cins(V, hi, k, x, p)}, MNode{q, cins(V, lo, k, x, p), hi}), a) == Bool.or(String.eq(a, k), Bool.or(mem(V, lo, a), mem(V, hi, a))) : Bool}
      %Equal.sym(Bool, mem(V, cins(V, lo, k, x, p), a), Bool.or(String.eq(a, k), mem(V, lo, a)), ilo) : {Bool.or(_, mem(V, hi, a)) == Bool.or(String.eq(a, k), Bool.or(mem(V, lo, a), mem(V, hi, a))) : Bool}
      or_assoc(String.eq(a, k), mem(V, lo, a), mem(V, hi, a))

def mem_ins.node(-V: Data, +q: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +k: String, +x: V, +p: Nat, +a: String, t: Bool, +et: {Nat.is_lt(q, p) == t : Bool}, +ilo: {mem(V, cins(V, lo, k, x, p), a) == Bool.or(String.eq(a, k), mem(V, lo, a)) : Bool}, +ihi: {mem(V, cins(V, hi, k, x, p), a) == Bool.or(String.eq(a, k), mem(V, hi, a)) : Bool}) -> {mem(V, cins(V, MNode{q, lo, hi}, k, x, p), a) == Bool.or(String.eq(a, k), Bool.or(mem(V, lo, a), mem(V, hi, a))) : Bool}:
  match t:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(q, p), True{}, et) : {mem(V, Bool.pick(Map<&2, V>, _, Bool.pick(Map<&2, V>, bv(k, q), MNode{q, lo, cins(V, hi, k, x, p)}, MNode{q, cins(V, lo, k, x, p), hi}), csplice(V, p, k, x, MNode{q, lo, hi})), a) == Bool.or(String.eq(a, k), Bool.or(mem(V, lo, a), mem(V, hi, a))) : Bool}
      mem_ins.deep(V, q, lo, hi, k, x, p, a, bv(k, q), {==}, ilo, ihi)
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(q, p), False{}, et) : {mem(V, Bool.pick(Map<&2, V>, _, Bool.pick(Map<&2, V>, bv(k, q), MNode{q, lo, cins(V, hi, k, x, p)}, MNode{q, cins(V, lo, k, x, p), hi}), csplice(V, p, k, x, MNode{q, lo, hi})), a) == Bool.or(String.eq(a, k), Bool.or(mem(V, lo, a), mem(V, hi, a))) : Bool}
      mem_splice(V, p, k, x, MNode{q, lo, hi}, a)

def mem_ins(-V: Data, m: Map<&2, V>, +k: String, +x: V, +p: Nat, +a: String) -> {mem(V, cins(V, m, k, x, p), a) == Bool.or(String.eq(a, k), mem(V, m, a)) : Bool}:
  match m:
    case MTip{}:
      Equal.sym(Bool, Bool.or(String.eq(a, k), mem(V, MTip{}, a)), String.eq(a, k), or_false_id(String.eq(a, k)))
    case MLeaf{+k1, +v}:
      mem_splice(V, p, k, x, MLeaf{k1, v}, a)
    case MNode{+q, +lo, +hi}:
      mem_ins.node(V, q, lo, hi, k, x, p, a, Nat.is_lt(q, p), {==}, mem_ins(V, lo, k, x, p, a), mem_ins(V, hi, k, x, p, a))

def sides_splice.go(-V: Data, +p: Nat, +k: String, +x: V, +rest: Map<&2, V>, +s: Nat, +b: Bool, c: Bool, +ec: {bv(k, p) == c : Bool}) -> {sides(V, csplice(V, p, k, x, rest), s, b) == Bool.and(beq(bv(k, s), b), sides(V, rest, s, b)) : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, bv(k, p), True{}, ec) : {sides(V, Bool.pick(Map<&2, V>, _, MNode{p, rest, MLeaf{k, x}}, MNode{p, MLeaf{k, x}, rest}), s, b) == Bool.and(beq(bv(k, s), b), sides(V, rest, s, b)) : Bool}
      and_comm(sides(V, rest, s, b), beq(bv(k, s), b))
    case False{}:
      %Equal.sym(Bool, bv(k, p), False{}, ec) : {sides(V, Bool.pick(Map<&2, V>, _, MNode{p, rest, MLeaf{k, x}}, MNode{p, MLeaf{k, x}, rest}), s, b) == Bool.and(beq(bv(k, s), b), sides(V, rest, s, b)) : Bool}
      {==}

def sides_splice(-V: Data, +p: Nat, +k: String, +x: V, +rest: Map<&2, V>, +s: Nat, +b: Bool) -> {sides(V, csplice(V, p, k, x, rest), s, b) == Bool.and(beq(bv(k, s), b), sides(V, rest, s, b)) : Bool}:
  sides_splice.go(V, p, k, x, rest, s, b, bv(k, p), {==})

def sides_ins.deep(-V: Data, +q: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +k: String, +x: V, +p: Nat, +s: Nat, +b: Bool, dir: Bool, +ed: {bv(k, q) == dir : Bool}, ilo: {sides(V, cins(V, lo, k, x, p), s, b) == Bool.and(beq(bv(k, s), b), sides(V, lo, s, b)) : Bool}, ihi: {sides(V, cins(V, hi, k, x, p), s, b) == Bool.and(beq(bv(k, s), b), sides(V, hi, s, b)) : Bool}) -> {sides(V, Bool.pick(Map<&2, V>, bv(k, q), MNode{q, lo, cins(V, hi, k, x, p)}, MNode{q, cins(V, lo, k, x, p), hi}), s, b) == Bool.and(beq(bv(k, s), b), Bool.and(sides(V, lo, s, b), sides(V, hi, s, b))) : Bool}:
  match dir:
    case True{}:
      %Equal.sym(Bool, bv(k, q), True{}, ed) : {sides(V, Bool.pick(Map<&2, V>, _, MNode{q, lo, cins(V, hi, k, x, p)}, MNode{q, cins(V, lo, k, x, p), hi}), s, b) == Bool.and(beq(bv(k, s), b), Bool.and(sides(V, lo, s, b), sides(V, hi, s, b))) : Bool}
      %Equal.sym(Bool, sides(V, cins(V, hi, k, x, p), s, b), Bool.and(beq(bv(k, s), b), sides(V, hi, s, b)), ihi) : {Bool.and(sides(V, lo, s, b), _) == Bool.and(beq(bv(k, s), b), Bool.and(sides(V, lo, s, b), sides(V, hi, s, b))) : Bool}
      and_swap(sides(V, lo, s, b), beq(bv(k, s), b), sides(V, hi, s, b))
    case False{}:
      %Equal.sym(Bool, bv(k, q), False{}, ed) : {sides(V, Bool.pick(Map<&2, V>, _, MNode{q, lo, cins(V, hi, k, x, p)}, MNode{q, cins(V, lo, k, x, p), hi}), s, b) == Bool.and(beq(bv(k, s), b), Bool.and(sides(V, lo, s, b), sides(V, hi, s, b))) : Bool}
      %Equal.sym(Bool, sides(V, cins(V, lo, k, x, p), s, b), Bool.and(beq(bv(k, s), b), sides(V, lo, s, b)), ilo) : {Bool.and(_, sides(V, hi, s, b)) == Bool.and(beq(bv(k, s), b), Bool.and(sides(V, lo, s, b), sides(V, hi, s, b))) : Bool}
      and_assoc(beq(bv(k, s), b), sides(V, lo, s, b), sides(V, hi, s, b))

def sides_ins.node(-V: Data, +q: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +k: String, +x: V, +p: Nat, +s: Nat, +b: Bool, t: Bool, +et: {Nat.is_lt(q, p) == t : Bool}, +ilo: {sides(V, cins(V, lo, k, x, p), s, b) == Bool.and(beq(bv(k, s), b), sides(V, lo, s, b)) : Bool}, +ihi: {sides(V, cins(V, hi, k, x, p), s, b) == Bool.and(beq(bv(k, s), b), sides(V, hi, s, b)) : Bool}) -> {sides(V, cins(V, MNode{q, lo, hi}, k, x, p), s, b) == Bool.and(beq(bv(k, s), b), Bool.and(sides(V, lo, s, b), sides(V, hi, s, b))) : Bool}:
  match t:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(q, p), True{}, et) : {sides(V, Bool.pick(Map<&2, V>, _, Bool.pick(Map<&2, V>, bv(k, q), MNode{q, lo, cins(V, hi, k, x, p)}, MNode{q, cins(V, lo, k, x, p), hi}), csplice(V, p, k, x, MNode{q, lo, hi})), s, b) == Bool.and(beq(bv(k, s), b), Bool.and(sides(V, lo, s, b), sides(V, hi, s, b))) : Bool}
      sides_ins.deep(V, q, lo, hi, k, x, p, s, b, bv(k, q), {==}, ilo, ihi)
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(q, p), False{}, et) : {sides(V, Bool.pick(Map<&2, V>, _, Bool.pick(Map<&2, V>, bv(k, q), MNode{q, lo, cins(V, hi, k, x, p)}, MNode{q, cins(V, lo, k, x, p), hi}), csplice(V, p, k, x, MNode{q, lo, hi})), s, b) == Bool.and(beq(bv(k, s), b), Bool.and(sides(V, lo, s, b), sides(V, hi, s, b))) : Bool}
      sides_splice(V, p, k, x, MNode{q, lo, hi}, s, b)

def sides_ins(-V: Data, m: Map<&2, V>, +k: String, +x: V, +p: Nat, +s: Nat, +b: Bool) -> {sides(V, cins(V, m, k, x, p), s, b) == Bool.and(beq(bv(k, s), b), sides(V, m, s, b)) : Bool}:
  match m:
    case MTip{}:
      Equal.sym(Bool, Bool.and(beq(bv(k, s), b), sides(V, MTip{}, s, b)), beq(bv(k, s), b), and_true_id(beq(bv(k, s), b)))
    case MLeaf{+k1, +v}:
      sides_splice(V, p, k, x, MLeaf{k1, v}, s, b)
    case MNode{+q, +lo, +hi}:
      sides_ins.node(V, q, lo, hi, k, x, p, s, b, Nat.is_lt(q, p), {==}, sides_ins(V, lo, k, x, p, s, b), sides_ins(V, hi, k, x, p, s, b))

def agrees_splice.go(-V: Data, +p: Nat, +k: String, +x: V, +rest: Map<&2, V>, +r: String, +s: Nat, c: Bool, +ec: {bv(k, p) == c : Bool}) -> {agrees(V, csplice(V, p, k, x, rest), r, s) == Bool.and(agree(k, r, s), agrees(V, rest, r, s)) : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, bv(k, p), True{}, ec) : {agrees(V, Bool.pick(Map<&2, V>, _, MNode{p, rest, MLeaf{k, x}}, MNode{p, MLeaf{k, x}, rest}), r, s) == Bool.and(agree(k, r, s), agrees(V, rest, r, s)) : Bool}
      and_comm(agrees(V, rest, r, s), agree(k, r, s))
    case False{}:
      %Equal.sym(Bool, bv(k, p), False{}, ec) : {agrees(V, Bool.pick(Map<&2, V>, _, MNode{p, rest, MLeaf{k, x}}, MNode{p, MLeaf{k, x}, rest}), r, s) == Bool.and(agree(k, r, s), agrees(V, rest, r, s)) : Bool}
      {==}

def agrees_splice(-V: Data, +p: Nat, +k: String, +x: V, +rest: Map<&2, V>, +r: String, +s: Nat) -> {agrees(V, csplice(V, p, k, x, rest), r, s) == Bool.and(agree(k, r, s), agrees(V, rest, r, s)) : Bool}:
  agrees_splice.go(V, p, k, x, rest, r, s, bv(k, p), {==})

def agrees_ins.deep(-V: Data, +q: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +k: String, +x: V, +p: Nat, +r: String, +s: Nat, dir: Bool, +ed: {bv(k, q) == dir : Bool}, ilo: {agrees(V, cins(V, lo, k, x, p), r, s) == Bool.and(agree(k, r, s), agrees(V, lo, r, s)) : Bool}, ihi: {agrees(V, cins(V, hi, k, x, p), r, s) == Bool.and(agree(k, r, s), agrees(V, hi, r, s)) : Bool}) -> {agrees(V, Bool.pick(Map<&2, V>, bv(k, q), MNode{q, lo, cins(V, hi, k, x, p)}, MNode{q, cins(V, lo, k, x, p), hi}), r, s) == Bool.and(agree(k, r, s), Bool.and(agrees(V, lo, r, s), agrees(V, hi, r, s))) : Bool}:
  match dir:
    case True{}:
      %Equal.sym(Bool, bv(k, q), True{}, ed) : {agrees(V, Bool.pick(Map<&2, V>, _, MNode{q, lo, cins(V, hi, k, x, p)}, MNode{q, cins(V, lo, k, x, p), hi}), r, s) == Bool.and(agree(k, r, s), Bool.and(agrees(V, lo, r, s), agrees(V, hi, r, s))) : Bool}
      %Equal.sym(Bool, agrees(V, cins(V, hi, k, x, p), r, s), Bool.and(agree(k, r, s), agrees(V, hi, r, s)), ihi) : {Bool.and(agrees(V, lo, r, s), _) == Bool.and(agree(k, r, s), Bool.and(agrees(V, lo, r, s), agrees(V, hi, r, s))) : Bool}
      and_swap(agrees(V, lo, r, s), agree(k, r, s), agrees(V, hi, r, s))
    case False{}:
      %Equal.sym(Bool, bv(k, q), False{}, ed) : {agrees(V, Bool.pick(Map<&2, V>, _, MNode{q, lo, cins(V, hi, k, x, p)}, MNode{q, cins(V, lo, k, x, p), hi}), r, s) == Bool.and(agree(k, r, s), Bool.and(agrees(V, lo, r, s), agrees(V, hi, r, s))) : Bool}
      %Equal.sym(Bool, agrees(V, cins(V, lo, k, x, p), r, s), Bool.and(agree(k, r, s), agrees(V, lo, r, s)), ilo) : {Bool.and(_, agrees(V, hi, r, s)) == Bool.and(agree(k, r, s), Bool.and(agrees(V, lo, r, s), agrees(V, hi, r, s))) : Bool}
      and_assoc(agree(k, r, s), agrees(V, lo, r, s), agrees(V, hi, r, s))

def agrees_ins.node(-V: Data, +q: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +k: String, +x: V, +p: Nat, +r: String, +s: Nat, t: Bool, +et: {Nat.is_lt(q, p) == t : Bool}, +ilo: {agrees(V, cins(V, lo, k, x, p), r, s) == Bool.and(agree(k, r, s), agrees(V, lo, r, s)) : Bool}, +ihi: {agrees(V, cins(V, hi, k, x, p), r, s) == Bool.and(agree(k, r, s), agrees(V, hi, r, s)) : Bool}) -> {agrees(V, cins(V, MNode{q, lo, hi}, k, x, p), r, s) == Bool.and(agree(k, r, s), Bool.and(agrees(V, lo, r, s), agrees(V, hi, r, s))) : Bool}:
  match t:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(q, p), True{}, et) : {agrees(V, Bool.pick(Map<&2, V>, _, Bool.pick(Map<&2, V>, bv(k, q), MNode{q, lo, cins(V, hi, k, x, p)}, MNode{q, cins(V, lo, k, x, p), hi}), csplice(V, p, k, x, MNode{q, lo, hi})), r, s) == Bool.and(agree(k, r, s), Bool.and(agrees(V, lo, r, s), agrees(V, hi, r, s))) : Bool}
      agrees_ins.deep(V, q, lo, hi, k, x, p, r, s, bv(k, q), {==}, ilo, ihi)
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(q, p), False{}, et) : {agrees(V, Bool.pick(Map<&2, V>, _, Bool.pick(Map<&2, V>, bv(k, q), MNode{q, lo, cins(V, hi, k, x, p)}, MNode{q, cins(V, lo, k, x, p), hi}), csplice(V, p, k, x, MNode{q, lo, hi})), r, s) == Bool.and(agree(k, r, s), Bool.and(agrees(V, lo, r, s), agrees(V, hi, r, s))) : Bool}
      agrees_splice(V, p, k, x, MNode{q, lo, hi}, r, s)

def agrees_ins(-V: Data, m: Map<&2, V>, +k: String, +x: V, +p: Nat, +r: String, +s: Nat) -> {agrees(V, cins(V, m, k, x, p), r, s) == Bool.and(agree(k, r, s), agrees(V, m, r, s)) : Bool}:
  match m:
    case MTip{}:
      Equal.sym(Bool, Bool.and(agree(k, r, s), agrees(V, MTip{}, r, s)), agree(k, r, s), and_true_id(agree(k, r, s)))
    case MLeaf{+k1, +v}:
      agrees_splice(V, p, k, x, MLeaf{k1, v}, r, s)
    case MNode{+q, +lo, +hi}:
      agrees_ins.node(V, q, lo, hi, k, x, p, r, s, Nat.is_lt(q, p), {==}, agrees_ins(V, lo, k, x, p, r, s), agrees_ins(V, hi, k, x, p, r, s))

def sides_put.go(-V: Data, +pp: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +k: String, +x: V, +s: Nat, +b: Bool, c: Bool, +ec: {bv(k, pp) == c : Bool}, ilo: {sides(V, cput(V, lo, k, x), s, b) == sides(V, lo, s, b) : Bool}, ihi: {sides(V, cput(V, hi, k, x), s, b) == sides(V, hi, s, b) : Bool}) -> {sides(V, Bool.pick(Map<&2, V>, bv(k, pp), MNode{pp, lo, cput(V, hi, k, x)}, MNode{pp, cput(V, lo, k, x), hi}), s, b) == Bool.and(sides(V, lo, s, b), sides(V, hi, s, b)) : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, bv(k, pp), True{}, ec) : {sides(V, Bool.pick(Map<&2, V>, _, MNode{pp, lo, cput(V, hi, k, x)}, MNode{pp, cput(V, lo, k, x), hi}), s, b) == Bool.and(sides(V, lo, s, b), sides(V, hi, s, b)) : Bool}
      %Equal.sym(Bool, sides(V, cput(V, hi, k, x), s, b), sides(V, hi, s, b), ihi) : {Bool.and(sides(V, lo, s, b), _) == Bool.and(sides(V, lo, s, b), sides(V, hi, s, b)) : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, bv(k, pp), False{}, ec) : {sides(V, Bool.pick(Map<&2, V>, _, MNode{pp, lo, cput(V, hi, k, x)}, MNode{pp, cput(V, lo, k, x), hi}), s, b) == Bool.and(sides(V, lo, s, b), sides(V, hi, s, b)) : Bool}
      %Equal.sym(Bool, sides(V, cput(V, lo, k, x), s, b), sides(V, lo, s, b), ilo) : {Bool.and(_, sides(V, hi, s, b)) == Bool.and(sides(V, lo, s, b), sides(V, hi, s, b)) : Bool}
      {==}

def sides_put(-V: Data, m: Map<&2, V>, +w: {wf(V, m) == True{} : Bool}, +k: String, +x: V, +s: Nat, +b: Bool) -> {sides(V, cput(V, m, k, x), s, b) == sides(V, m, s, b) : Bool}:
  match m:
    case MTip{}:
      Empty.absurd({sides(V, MLeaf{k, x}, s, b) == sides(V, MTip{}, s, b) : Bool}, Str.false_true(w))
    case MLeaf{k1, v}:
      {==}
    case MNode{+pp, +lo, +hi}:
      sides_put.go(V, pp, lo, hi, k, x, s, b, bv(k, pp), {==}, sides_put(V, lo, wf_lo(V, pp, lo, hi, w), k, x, s, b), sides_put(V, hi, wf_hi(V, pp, lo, hi, w), k, x, s, b))

def agrees_put.go(-V: Data, +pp: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +k: String, +x: V, +r: String, +s: Nat, c: Bool, +ec: {bv(k, pp) == c : Bool}, ilo: {agrees(V, cput(V, lo, k, x), r, s) == agrees(V, lo, r, s) : Bool}, ihi: {agrees(V, cput(V, hi, k, x), r, s) == agrees(V, hi, r, s) : Bool}) -> {agrees(V, Bool.pick(Map<&2, V>, bv(k, pp), MNode{pp, lo, cput(V, hi, k, x)}, MNode{pp, cput(V, lo, k, x), hi}), r, s) == Bool.and(agrees(V, lo, r, s), agrees(V, hi, r, s)) : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, bv(k, pp), True{}, ec) : {agrees(V, Bool.pick(Map<&2, V>, _, MNode{pp, lo, cput(V, hi, k, x)}, MNode{pp, cput(V, lo, k, x), hi}), r, s) == Bool.and(agrees(V, lo, r, s), agrees(V, hi, r, s)) : Bool}
      %Equal.sym(Bool, agrees(V, cput(V, hi, k, x), r, s), agrees(V, hi, r, s), ihi) : {Bool.and(agrees(V, lo, r, s), _) == Bool.and(agrees(V, lo, r, s), agrees(V, hi, r, s)) : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, bv(k, pp), False{}, ec) : {agrees(V, Bool.pick(Map<&2, V>, _, MNode{pp, lo, cput(V, hi, k, x)}, MNode{pp, cput(V, lo, k, x), hi}), r, s) == Bool.and(agrees(V, lo, r, s), agrees(V, hi, r, s)) : Bool}
      %Equal.sym(Bool, agrees(V, cput(V, lo, k, x), r, s), agrees(V, lo, r, s), ilo) : {Bool.and(_, agrees(V, hi, r, s)) == Bool.and(agrees(V, lo, r, s), agrees(V, hi, r, s)) : Bool}
      {==}

def agrees_put(-V: Data, m: Map<&2, V>, +w: {wf(V, m) == True{} : Bool}, +k: String, +x: V, +r: String, +s: Nat) -> {agrees(V, cput(V, m, k, x), r, s) == agrees(V, m, r, s) : Bool}:
  match m:
    case MTip{}:
      Empty.absurd({agrees(V, MLeaf{k, x}, r, s) == agrees(V, MTip{}, r, s) : Bool}, Str.false_true(w))
    case MLeaf{k1, v}:
      {==}
    case MNode{+pp, +lo, +hi}:
      agrees_put.go(V, pp, lo, hi, k, x, r, s, bv(k, pp), {==}, agrees_put(V, lo, wf_lo(V, pp, lo, hi, w), k, x, r, s), agrees_put(V, hi, wf_hi(V, pp, lo, hi, w), k, x, r, s))

def rep_put.go(-V: Data, +pp: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +k: String, +x: V, c: Bool, +ec: {bv(k, pp) == c : Bool}, ilo: {rep(V, cput(V, lo, k, x)) == rep(V, lo) : String}) -> {rep(V, Bool.pick(Map<&2, V>, bv(k, pp), MNode{pp, lo, cput(V, hi, k, x)}, MNode{pp, cput(V, lo, k, x), hi})) == rep(V, lo) : String}:
  match c:
    case True{}:
      %Equal.sym(Bool, bv(k, pp), True{}, ec) : {rep(V, Bool.pick(Map<&2, V>, _, MNode{pp, lo, cput(V, hi, k, x)}, MNode{pp, cput(V, lo, k, x), hi})) == rep(V, lo) : String}
      {==}
    case False{}:
      %Equal.sym(Bool, bv(k, pp), False{}, ec) : {rep(V, Bool.pick(Map<&2, V>, _, MNode{pp, lo, cput(V, hi, k, x)}, MNode{pp, cput(V, lo, k, x), hi})) == rep(V, lo) : String}
      ilo

def rep_put(-V: Data, m: Map<&2, V>, +w: {wf(V, m) == True{} : Bool}, +k: String, +x: V) -> {rep(V, cput(V, m, k, x)) == rep(V, m) : String}:
  match m:
    case MTip{}:
      Empty.absurd({k == SNil{} : String}, Str.false_true(w))
    case MLeaf{k1, v}:
      {==}
    case MNode{+pp, +lo, +hi}:
      rep_put.go(V, pp, lo, hi, k, x, bv(k, pp), {==}, rep_put(V, lo, wf_lo(V, pp, lo, hi, w), k, x))

def wf_put.go(-V: Data, +pp: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +w: {wf(V, MNode{pp, lo, hi}) == True{} : Bool}, +k: String, +x: V, c: Bool, +ec: {bv(k, pp) == c : Bool}, ilo: {wf(V, cput(V, lo, k, x)) == True{} : Bool}, ihi: {wf(V, cput(V, hi, k, x)) == True{} : Bool}) -> {wf(V, Bool.pick(Map<&2, V>, bv(k, pp), MNode{pp, lo, cput(V, hi, k, x)}, MNode{pp, cput(V, lo, k, x), hi})) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, bv(k, pp), True{}, ec) : {wf(V, Bool.pick(Map<&2, V>, _, MNode{pp, lo, cput(V, hi, k, x)}, MNode{pp, cput(V, lo, k, x), hi})) == True{} : Bool}
      +r = rep(V, lo)
      +near = wf_near(V, pp, lo, hi, w)
      +nlo = and_l(agrees(V, lo, r, pp), agrees(V, hi, r, pp), near)
      +nhi = and_r(agrees(V, lo, r, pp), agrees(V, hi, r, pp), near)
      +wlo = wf_lo(V, pp, lo, hi, w)
      +whi = wf_hi(V, pp, lo, hi, w)
      and_t(wf(V, lo), Bool.and(wf(V, cput(V, hi, k, x)), Bool.and(sides(V, lo, pp, False{}), Bool.and(sides(V, cput(V, hi, k, x), pp, True{}), agrees(V, MNode{pp, lo, cput(V, hi, k, x)}, r, pp)))), wlo, and_t(wf(V, cput(V, hi, k, x)), Bool.and(sides(V, lo, pp, False{}), Bool.and(sides(V, cput(V, hi, k, x), pp, True{}), agrees(V, MNode{pp, lo, cput(V, hi, k, x)}, r, pp))), ihi, and_t(sides(V, lo, pp, False{}), Bool.and(sides(V, cput(V, hi, k, x), pp, True{}), agrees(V, MNode{pp, lo, cput(V, hi, k, x)}, r, pp)), wf_slo(V, pp, lo, hi, w), and_t(sides(V, cput(V, hi, k, x), pp, True{}), agrees(V, MNode{pp, lo, cput(V, hi, k, x)}, r, pp), Equal.trans(Bool, sides(V, cput(V, hi, k, x), pp, True{}), sides(V, hi, pp, True{}), True{}, sides_put(V, hi, whi, k, x, pp, True{}), wf_shi(V, pp, lo, hi, w)), and_t(agrees(V, lo, r, pp), agrees(V, cput(V, hi, k, x), r, pp), nlo, Equal.trans(Bool, agrees(V, cput(V, hi, k, x), r, pp), agrees(V, hi, r, pp), True{}, agrees_put(V, hi, whi, k, x, r, pp), nhi))))))
    case False{}:
      %Equal.sym(Bool, bv(k, pp), False{}, ec) : {wf(V, Bool.pick(Map<&2, V>, _, MNode{pp, lo, cput(V, hi, k, x)}, MNode{pp, cput(V, lo, k, x), hi})) == True{} : Bool}
      +r = rep(V, lo)
      +near = wf_near(V, pp, lo, hi, w)
      +nlo = and_l(agrees(V, lo, r, pp), agrees(V, hi, r, pp), near)
      +nhi = and_r(agrees(V, lo, r, pp), agrees(V, hi, r, pp), near)
      +wlo = wf_lo(V, pp, lo, hi, w)
      +whi = wf_hi(V, pp, lo, hi, w)
      +r2 = rep(V, cput(V, lo, k, x))
      +rr = rep_put(V, lo, wlo, k, x)
      +ag = Equal.trans(Bool, Bool.and(agrees(V, cput(V, lo, k, x), r2, pp), agrees(V, hi, r2, pp)), Bool.and(agrees(V, cput(V, lo, k, x), r, pp), agrees(V, hi, r, pp)), True{}, Equal.cong(String, Bool, z => Bool.and(agrees(V, cput(V, lo, k, x), z, pp), agrees(V, hi, z, pp)), r2, r, rr), and_t(agrees(V, cput(V, lo, k, x), r, pp), agrees(V, hi, r, pp), Equal.trans(Bool, agrees(V, cput(V, lo, k, x), r, pp), agrees(V, lo, r, pp), True{}, agrees_put(V, lo, wlo, k, x, r, pp), nlo), nhi))
      and_t(wf(V, cput(V, lo, k, x)), Bool.and(wf(V, hi), Bool.and(sides(V, cput(V, lo, k, x), pp, False{}), Bool.and(sides(V, hi, pp, True{}), agrees(V, MNode{pp, cput(V, lo, k, x), hi}, r2, pp)))), ilo, and_t(wf(V, hi), Bool.and(sides(V, cput(V, lo, k, x), pp, False{}), Bool.and(sides(V, hi, pp, True{}), agrees(V, MNode{pp, cput(V, lo, k, x), hi}, r2, pp))), whi, and_t(sides(V, cput(V, lo, k, x), pp, False{}), Bool.and(sides(V, hi, pp, True{}), agrees(V, MNode{pp, cput(V, lo, k, x), hi}, r2, pp)), Equal.trans(Bool, sides(V, cput(V, lo, k, x), pp, False{}), sides(V, lo, pp, False{}), True{}, sides_put(V, lo, wlo, k, x, pp, False{}), wf_slo(V, pp, lo, hi, w)), and_t(sides(V, hi, pp, True{}), agrees(V, MNode{pp, cput(V, lo, k, x), hi}, r2, pp), wf_shi(V, pp, lo, hi, w), ag))))

# Writing a value where the key's leaf is keeps the invariant.
def wf_put(-V: Data, m: Map<&2, V>, +w: {wf(V, m) == True{} : Bool}, +k: String, +x: V) -> {wf(V, cput(V, m, k, x)) == True{} : Bool}:
  match m:
    case MTip{}:
      Empty.absurd({True{} == True{} : Bool}, Str.false_true(w))
    case MLeaf{k1, v}:
      {==}
    case MNode{+pp, +lo, +hi}:
      wf_put.go(V, pp, lo, hi, w, k, x, bv(k, pp), {==}, wf_put(V, lo, wf_lo(V, pp, lo, hi, w), k, x), wf_put(V, hi, wf_hi(V, pp, lo, hi, w), k, x))

def wf_splice.go(-V: Data, +p: Nat, +k: String, +x: V, +rest: Map<&2, V>, +ew: {wf(V, rest) == True{} : Bool}, +es: {sides(V, rest, p, Bool.not(bv(k, p))) == True{} : Bool}, +ea: {agrees(V, rest, k, p) == True{} : Bool}, c: Bool, +ec: {bv(k, p) == c : Bool}) -> {wf(V, csplice(V, p, k, x, rest)) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, bv(k, p), True{}, ec) : {wf(V, Bool.pick(Map<&2, V>, _, MNode{p, rest, MLeaf{k, x}}, MNode{p, MLeaf{k, x}, rest})) == True{} : Bool}
      +rr = rep(V, rest)
      +rm = rep_mem(V, rest, ew)
      +esf = Equal.trans(Bool, sides(V, rest, p, Bool.not(True{})), sides(V, rest, p, Bool.not(bv(k, p))), True{}, Equal.cong(Bool, Bool, z => sides(V, rest, p, Bool.not(z)), True{}, bv(k, p), Equal.sym(Bool, bv(k, p), True{}, ec)), es)
      +bt = Equal.cong(Bool, Bool, z => beq(z, True{}), bv(k, p), True{}, ec)
      and_t(wf(V, rest), Bool.and(True{}, Bool.and(sides(V, rest, p, False{}), Bool.and(beq(bv(k, p), True{}), agrees(V, MNode{p, rest, MLeaf{k, x}}, rr, p)))), ew, and_t(True{}, Bool.and(sides(V, rest, p, False{}), Bool.and(beq(bv(k, p), True{}), agrees(V, MNode{p, rest, MLeaf{k, x}}, rr, p))), {==}, and_t(sides(V, rest, p, False{}), Bool.and(beq(bv(k, p), True{}), agrees(V, MNode{p, rest, MLeaf{k, x}}, rr, p)), esf, and_t(beq(bv(k, p), True{}), agrees(V, MNode{p, rest, MLeaf{k, x}}, rr, p), bt, and_t(agrees(V, rest, rr, p), agree(k, rr, p), agrees_switch(V, rest, k, rr, p, ea, rm), agree_sym(rr, k, p, agrees_use(V, rest, k, p, ea, rr, rm)))))))
    case False{}:
      %Equal.sym(Bool, bv(k, p), False{}, ec) : {wf(V, Bool.pick(Map<&2, V>, _, MNode{p, rest, MLeaf{k, x}}, MNode{p, MLeaf{k, x}, rest})) == True{} : Bool}
      +est = Equal.trans(Bool, sides(V, rest, p, Bool.not(False{})), sides(V, rest, p, Bool.not(bv(k, p))), True{}, Equal.cong(Bool, Bool, z => sides(V, rest, p, Bool.not(z)), False{}, bv(k, p), Equal.sym(Bool, bv(k, p), False{}, ec)), es)
      +bf = Equal.cong(Bool, Bool, z => beq(z, False{}), bv(k, p), False{}, ec)
      and_t(True{}, Bool.and(wf(V, rest), Bool.and(beq(bv(k, p), False{}), Bool.and(sides(V, rest, p, True{}), agrees(V, MNode{p, MLeaf{k, x}, rest}, k, p)))), {==}, and_t(wf(V, rest), Bool.and(beq(bv(k, p), False{}), Bool.and(sides(V, rest, p, True{}), agrees(V, MNode{p, MLeaf{k, x}, rest}, k, p))), ew, and_t(beq(bv(k, p), False{}), Bool.and(sides(V, rest, p, True{}), agrees(V, MNode{p, MLeaf{k, x}, rest}, k, p)), bf, and_t(sides(V, rest, p, True{}), agrees(V, MNode{p, MLeaf{k, x}, rest}, k, p), est, and_t(agree(k, k, p), agrees(V, rest, k, p), agree_refl(k, p), ea)))))

# A node spliced in at `p` over a trie whose keys all have the other bit
# there, and agree with the new key before it, is a trie.
def wf_splice(-V: Data, +p: Nat, +k: String, +x: V, +rest: Map<&2, V>, +ew: {wf(V, rest) == True{} : Bool}, +es: {sides(V, rest, p, Bool.not(bv(k, p))) == True{} : Bool}, +ea: {agrees(V, rest, k, p) == True{} : Bool}) -> {wf(V, csplice(V, p, k, x, rest)) == True{} : Bool}:
  wf_splice.go(V, p, k, x, rest, ew, es, ea, bv(k, p), {==})

def wf_ins.deep(-V: Data, +q: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +w: {wf(V, MNode{q, lo, hi}) == True{} : Bool}, +k: String, +x: V, +k0: String, +er: {reach(V, MNode{q, lo, hi}, k) == Some{k0} : Maybe<&2, String>}, +et: {Nat.is_lt(q, Map.diff(k, k0)) == True{} : Bool}, dir: Bool, +ed: {bv(k, q) == dir : Bool}, ilo: {reach(V, lo, k) == Some{k0} : Maybe<&2, String>} -> {wf(V, cins(V, lo, k, x, Map.diff(k, k0))) == True{} : Bool}, ihi: {reach(V, hi, k) == Some{k0} : Maybe<&2, String>} -> {wf(V, cins(V, hi, k, x, Map.diff(k, k0))) == True{} : Bool}) -> {wf(V, Bool.pick(Map<&2, V>, bv(k, q), MNode{q, lo, cins(V, hi, k, x, Map.diff(k, k0))}, MNode{q, cins(V, lo, k, x, Map.diff(k, k0)), hi})) == True{} : Bool}:
  match dir:
    case True{}:
      %Equal.sym(Bool, bv(k, q), True{}, ed) : {wf(V, Bool.pick(Map<&2, V>, _, MNode{q, lo, cins(V, hi, k, x, Map.diff(k, k0))}, MNode{q, cins(V, lo, k, x, Map.diff(k, k0)), hi})) == True{} : Bool}
      +r = rep(V, lo)
      +near = wf_near(V, q, lo, hi, w)
      +ak0 = agrees_use(V, MNode{q, lo, hi}, r, q, near, k0, reach_mem(V, MNode{q, lo, hi}, k, k0, er))
      +akr = agree_trans(k, k0, r, q, agree_mono(k, k0, Map.diff(k, k0), agree_diff(k, k0), q, lt_le_weak(q, Map.diff(k, k0), et)), ak0)
      +ch = cins(V, hi, k, x, Map.diff(k, k0))
      +wh = ihi(pick_reach(V, q, lo, hi, k, Some{k0}, True{}, ed, er))
      +sh = Equal.trans(Bool, sides(V, ch, q, True{}), Bool.and(beq(bv(k, q), True{}), sides(V, hi, q, True{})), True{}, sides_ins(V, hi, k, x, Map.diff(k, k0), q, True{}), and_t(beq(bv(k, q), True{}), sides(V, hi, q, True{}), Equal.cong(Bool, Bool, z => beq(z, True{}), bv(k, q), True{}, ed), wf_shi(V, q, lo, hi, w)))
      +ah = Equal.trans(Bool, agrees(V, ch, r, q), Bool.and(agree(k, r, q), agrees(V, hi, r, q)), True{}, agrees_ins(V, hi, k, x, Map.diff(k, k0), r, q), and_t(agree(k, r, q), agrees(V, hi, r, q), akr, and_r(agrees(V, lo, r, q), agrees(V, hi, r, q), near)))
      and_t(wf(V, lo), Bool.and(wf(V, ch), Bool.and(sides(V, lo, q, False{}), Bool.and(sides(V, ch, q, True{}), agrees(V, MNode{q, lo, ch}, r, q)))), wf_lo(V, q, lo, hi, w), and_t(wf(V, ch), Bool.and(sides(V, lo, q, False{}), Bool.and(sides(V, ch, q, True{}), agrees(V, MNode{q, lo, ch}, r, q))), wh, and_t(sides(V, lo, q, False{}), Bool.and(sides(V, ch, q, True{}), agrees(V, MNode{q, lo, ch}, r, q)), wf_slo(V, q, lo, hi, w), and_t(sides(V, ch, q, True{}), agrees(V, MNode{q, lo, ch}, r, q), sh, and_t(agrees(V, lo, r, q), agrees(V, ch, r, q), and_l(agrees(V, lo, r, q), agrees(V, hi, r, q), near), ah)))))
    case False{}:
      %Equal.sym(Bool, bv(k, q), False{}, ed) : {wf(V, Bool.pick(Map<&2, V>, _, MNode{q, lo, cins(V, hi, k, x, Map.diff(k, k0))}, MNode{q, cins(V, lo, k, x, Map.diff(k, k0)), hi})) == True{} : Bool}
      +r = rep(V, lo)
      +near = wf_near(V, q, lo, hi, w)
      +ak0 = agrees_use(V, MNode{q, lo, hi}, r, q, near, k0, reach_mem(V, MNode{q, lo, hi}, k, k0, er))
      +akr = agree_trans(k, k0, r, q, agree_mono(k, k0, Map.diff(k, k0), agree_diff(k, k0), q, lt_le_weak(q, Map.diff(k, k0), et)), ak0)
      +cl = cins(V, lo, k, x, Map.diff(k, k0))
      +wl = ilo(pick_reach(V, q, lo, hi, k, Some{k0}, False{}, ed, er))
      +r2 = rep(V, cl)
      +sl = Equal.trans(Bool, sides(V, cl, q, False{}), Bool.and(beq(bv(k, q), False{}), sides(V, lo, q, False{})), True{}, sides_ins(V, lo, k, x, Map.diff(k, k0), q, False{}), and_t(beq(bv(k, q), False{}), sides(V, lo, q, False{}), Equal.cong(Bool, Bool, z => beq(z, False{}), bv(k, q), False{}, ed), wf_slo(V, q, lo, hi, w)))
      +al = Equal.trans(Bool, agrees(V, cl, r, q), Bool.and(agree(k, r, q), agrees(V, lo, r, q)), True{}, agrees_ins(V, lo, k, x, Map.diff(k, k0), r, q), and_t(agree(k, r, q), agrees(V, lo, r, q), akr, and_l(agrees(V, lo, r, q), agrees(V, hi, r, q), near)))
      +old = and_t(agrees(V, cl, r, q), agrees(V, hi, r, q), al, and_r(agrees(V, lo, r, q), agrees(V, hi, r, q), near))
      +m2 = Equal.trans(Bool, Bool.or(mem(V, cl, r2), mem(V, hi, r2)), Bool.or(True{}, mem(V, hi, r2)), True{}, Equal.cong(Bool, Bool, z => Bool.or(z, mem(V, hi, r2)), mem(V, cl, r2), True{}, rep_mem(V, cl, wl)), {==})
      +ag = agrees_switch(V, MNode{q, cl, hi}, r, r2, q, old, m2)
      and_t(wf(V, cl), Bool.and(wf(V, hi), Bool.and(sides(V, cl, q, False{}), Bool.and(sides(V, hi, q, True{}), agrees(V, MNode{q, cl, hi}, r2, q)))), wl, and_t(wf(V, hi), Bool.and(sides(V, cl, q, False{}), Bool.and(sides(V, hi, q, True{}), agrees(V, MNode{q, cl, hi}, r2, q))), wf_hi(V, q, lo, hi, w), and_t(sides(V, cl, q, False{}), Bool.and(sides(V, hi, q, True{}), agrees(V, MNode{q, cl, hi}, r2, q)), sl, and_t(sides(V, hi, q, True{}), agrees(V, MNode{q, cl, hi}, r2, q), wf_shi(V, q, lo, hi, w), ag))))

def wf_ins.node(-V: Data, +q: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +w: {wf(V, MNode{q, lo, hi}) == True{} : Bool}, +k: String, +x: V, +k0: String, +er: {reach(V, MNode{q, lo, hi}, k) == Some{k0} : Maybe<&2, String>}, +ekk0: {String.eq(k, k0) == False{} : Bool}, t: Bool, +et: {Nat.is_lt(q, Map.diff(k, k0)) == t : Bool}, ilo: {reach(V, lo, k) == Some{k0} : Maybe<&2, String>} -> {wf(V, cins(V, lo, k, x, Map.diff(k, k0))) == True{} : Bool}, ihi: {reach(V, hi, k) == Some{k0} : Maybe<&2, String>} -> {wf(V, cins(V, hi, k, x, Map.diff(k, k0))) == True{} : Bool}) -> {wf(V, cins(V, MNode{q, lo, hi}, k, x, Map.diff(k, k0))) == True{} : Bool}:
  match t:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(q, Map.diff(k, k0)), True{}, et) : {wf(V, Bool.pick(Map<&2, V>, _, Bool.pick(Map<&2, V>, bv(k, q), MNode{q, lo, cins(V, hi, k, x, Map.diff(k, k0))}, MNode{q, cins(V, lo, k, x, Map.diff(k, k0)), hi}), csplice(V, Map.diff(k, k0), k, x, MNode{q, lo, hi}))) == True{} : Bool}
      wf_ins.deep(V, q, lo, hi, w, k, x, k0, er, et, bv(k, q), {==}, ilo, ihi)
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(q, Map.diff(k, k0)), False{}, et) : {wf(V, Bool.pick(Map<&2, V>, _, Bool.pick(Map<&2, V>, bv(k, q), MNode{q, lo, cins(V, hi, k, x, Map.diff(k, k0))}, MNode{q, cins(V, lo, k, x, Map.diff(k, k0)), hi}), csplice(V, Map.diff(k, k0), k, x, MNode{q, lo, hi}))) == True{} : Bool}
      +d = Map.diff(k, k0)
      +pq = p_below(V, q, lo, hi, side_fn(V, lo, q, False{}, wf_slo(V, q, lo, hi, w)), side_fn(V, hi, q, True{}, wf_shi(V, q, lo, hi, w)), k, k0, er, ekk0, et)
      +r = rep(V, lo)
      +near = wf_near(V, q, lo, hi, w)
      +ak0 = agrees_use(V, MNode{q, lo, hi}, r, q, near, k0, reach_mem(V, MNode{q, lo, hi}, k, k0, er))
      +cr = Equal.trans(Bool, bv(r, d), bv(k0, d), Bool.not(bv(k, d)), Equal.sym(Bool, bv(k0, d), bv(r, d), agree_use(k0, r, q, ak0, d, pq)), flip(bv(k, d), bv(k0, d), split_at_diff(k, k0, ekk0)))
      +es = Equal.trans(Bool, sides(V, MNode{q, lo, hi}, d, Bool.not(bv(k, d))), sides(V, MNode{q, lo, hi}, d, bv(r, d)), True{}, Equal.cong(Bool, Bool, z => sides(V, MNode{q, lo, hi}, d, z), Bool.not(bv(k, d)), bv(r, d), Equal.sym(Bool, bv(r, d), Bool.not(bv(k, d)), cr)), sides_of_agrees(V, MNode{q, lo, hi}, r, q, near, d, pq))
      +le = lt_le_weak(d, q, pq)
      +ea = agrees_trans(V, MNode{q, lo, hi}, r, k, d, agrees_mono(V, MNode{q, lo, hi}, r, q, near, d, le), agree_trans(r, k0, k, d, agree_sym(k0, r, d, agree_mono(k0, r, q, ak0, d, le)), agree_sym(k, k0, d, agree_diff(k, k0))))
      wf_splice(V, d, k, x, MNode{q, lo, hi}, w, es, ea)

# A node spliced in for a new key keeps the invariant.
def wf_ins(-V: Data, m: Map<&2, V>, +w: {wf(V, m) == True{} : Bool}, +k: String, +x: V, +k0: String, +er: {reach(V, m, k) == Some{k0} : Maybe<&2, String>}, +ekk0: {String.eq(k, k0) == False{} : Bool}) -> {wf(V, cins(V, m, k, x, Map.diff(k, k0))) == True{} : Bool}:
  match m:
    case MTip{}:
      Empty.absurd({True{} == True{} : Bool}, Str.false_true(w))
    case MLeaf{+k1, +v}:
      +d = Map.diff(k, k0)
      +k1k0 = some_inj(String, k1, k0, er)
      +f = flip(bv(k, d), bv(k0, d), split_at_diff(k, k0, ekk0))
      +es = Equal.trans(Bool, beq(bv(k1, d), Bool.not(bv(k, d))), beq(bv(k0, d), Bool.not(bv(k, d))), True{}, Equal.cong(String, Bool, z => beq(bv(z, d), Bool.not(bv(k, d))), k1, k0, k1k0), Equal.trans(Bool, beq(bv(k0, d), Bool.not(bv(k, d))), beq(Bool.not(bv(k, d)), Bool.not(bv(k, d))), True{}, Equal.cong(Bool, Bool, z => beq(z, Bool.not(bv(k, d))), bv(k0, d), Bool.not(bv(k, d)), f), beq_refl(Bool.not(bv(k, d)))))
      +ea = Equal.trans(Bool, agree(k1, k, d), agree(k0, k, d), True{}, Equal.cong(String, Bool, z => agree(z, k, d), k1, k0, k1k0), agree_sym(k, k0, d, agree_diff(k, k0)))
      wf_splice(V, d, k, x, MLeaf{k1, v}, {==}, es, ea)
    case MNode{+q, +lo, +hi}:
      wf_ins.node(V, q, lo, hi, w, k, x, k0, er, ekk0, Nat.is_lt(q, Map.diff(k, k0)), {==}, e2 => wf_ins(V, lo, wf_lo(V, q, lo, hi, w), k, x, k0, e2, ekk0), e2 => wf_ins(V, hi, wf_hi(V, q, lo, hi, w), k, x, k0, e2, ekk0))

def wf_set.fin(-V: Data, +m: Map<&2, V>, +w: {wf(V, m) == True{} : Bool}, +k: String, +x: V, +k0: String, +er: {reach(V, m, k) == Some{k0} : Maybe<&2, String>}, c: Cmp, +ec: {String.order(k, k0) == c : Cmp}) -> {wf(V, cfin(V, m, k, x, k0, String.order(k, k0))) == True{} : Bool}:
  match c:
    case LT{}:
      %Equal.sym(Cmp, String.order(k, k0), LT{}, ec) : {wf(V, cfin(V, m, k, x, k0, _)) == True{} : Bool}
      wf_ins(V, m, w, k, x, k0, er, eq_of_order(k, k0, LT{}, ec))
    case EQ{}:
      %Equal.sym(Cmp, String.order(k, k0), EQ{}, ec) : {wf(V, cfin(V, m, k, x, k0, _)) == True{} : Bool}
      wf_put(V, m, w, k, x)
    case GT{}:
      %Equal.sym(Cmp, String.order(k, k0), GT{}, ec) : {wf(V, cfin(V, m, k, x, k0, _)) == True{} : Bool}
      wf_ins(V, m, w, k, x, k0, er, eq_of_order(k, k0, GT{}, ec))

def wf_set.of(-V: Data, +m: Map<&2, V>, +w: {wf(V, m) == True{} : Bool}, +k: String, +x: V, r: Maybe<&2, String>, +er: {reach(V, m, k) == r : Maybe<&2, String>}) -> {wf(V, cset.of(V, m, k, x, reach(V, m, k))) == True{} : Bool}:
  match r:
    case None{}:
      Empty.absurd({wf(V, cset.of(V, m, k, x, reach(V, m, k))) == True{} : Bool}, wf_reach(V, m, w, k, er))
    case Some{+k0}:
      %Equal.sym(Maybe<&2, String>, reach(V, m, k), Some{k0}, er) : {wf(V, cset.of(V, m, k, x, _)) == True{} : Bool}
      wf_set.fin(V, m, w, k, x, k0, er, String.order(k, k0), {==})

def wf_set(-V: Data, +m: Map<&2, V>, +w: {wf(V, m) == True{} : Bool}, +k: String, +x: V) -> {wf(V, cset(V, m, k, x)) == True{} : Bool}:
  wf_set.of(V, m, w, k, x, reach(V, m, k), {==})

def wft_of(-V: Data, m: Map<&2, V>, +e: {wf(V, m) == True{} : Bool}) -> {wft(V, m) == True{} : Bool}:
  match m:
    case MTip{}:
      Empty.absurd({True{} == True{} : Bool}, Str.false_true(e))
    case MLeaf{k, v}:
      {==}
    case MNode{p, lo, hi}:
      e

# Every map `Map.new` and `Map.set` build keeps the invariant.
def wft_set(-V: Data, m: Map<&2, V>, +w: {wft(V, m) == True{} : Bool}, +k: String, +x: V) -> {wft(V, cset(V, m, k, x)) == True{} : Bool}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k1, +v}:
      wft_of(V, cset(V, MLeaf{k1, v}, k, x), wf_set(V, MLeaf{k1, v}, {==}, k, x))
    case MNode{+p, +lo, +hi}:
      wft_of(V, cset(V, MNode{p, lo, hi}, k, x), wf_set(V, MNode{p, lo, hi}, w, k, x))

# What Base's `Map` and `Set` hold
# --------------------------------

# `Map.new` holds nothing.
def get_new(-V: Data, +d: V, +k: String) -> {gv(V, Map.get(V, d, Map.new(&2, V), k)) == d : V}:
  {==}

def has_new(-V: Data, +k: String) -> {hv(V, Map.has(&2, V, Map.new(&2, V), k)) == False{} : Bool}:
  {==}

# Every map `Map.new` and `Map.set` build is a trie: `Wf.top` holds of
# `Map.new`, and `Map.set` keeps it.
def wf_new(-V: Data) -> Wf.top(V, Map.new(&2, V)):
  {==}

def wf_set_map(-V: Data, +m: Map<&2, V>, +w: Wf.top(V, m), +k: String, +x: V) -> Wf.top(V, Map.set(&2, V, m, k, x)):
  %Equal.sym(Map<&2, V>, Map.set(&2, V, m, k, x), cset(V, m, k, x), set_is(V, m, k, x)) : {wft(V, _) == True{} : Bool}
  wft_set(V, m, w, k, x)

# A key finds what was just written for it, in any map at all.
def get_set_same(-V: Data, +d: V, +m: Map<&2, V>, +k: String, +x: V) -> {gv(V, Map.get(V, d, Map.set(&2, V, m, k, x), k)) == x : V}:
  %Equal.sym(V, gv(V, Map.get(V, d, Map.set(&2, V, m, k, x), k)), Maybe.default(&2, V, found(V, Map.set(&2, V, m, k, x), k), d), get_is(V, d, Map.set(&2, V, m, k, x), k)) : {_ == x : V}
  %Equal.sym(Map<&2, V>, Map.set(&2, V, m, k, x), cset(V, m, k, x), set_is(V, m, k, x)) : {Maybe.default(&2, V, found(V, _, k), d) == x : V}
  %Equal.sym(Maybe<&2, V>, found(V, cset(V, m, k, x), k), Some{x}, set_same(V, m, k, x)) : {Maybe.default(&2, V, _, d) == x : V}
  {==}

def has_set_same(-V: Data, +m: Map<&2, V>, +k: String, +x: V) -> {hv(V, Map.has(&2, V, Map.set(&2, V, m, k, x), k)) == True{} : Bool}:
  %Equal.sym(Bool, hv(V, Map.has(&2, V, Map.set(&2, V, m, k, x), k)), Maybe.is_some(&2, V, found(V, Map.set(&2, V, m, k, x), k)), has_is(V, Map.set(&2, V, m, k, x), k)) : {_ == True{} : Bool}
  %Equal.sym(Map<&2, V>, Map.set(&2, V, m, k, x), cset(V, m, k, x), set_is(V, m, k, x)) : {Maybe.is_some(&2, V, found(V, _, k)) == True{} : Bool}
  %Equal.sym(Maybe<&2, V>, found(V, cset(V, m, k, x), k), Some{x}, set_same(V, m, k, x)) : {Maybe.is_some(&2, V, _) == True{} : Bool}
  {==}

# In every map `Map.new` and `Map.set` build, writing one key changes what
# no other key finds.
def get_set_other(-V: Data, +d: V, +m: Map<&2, V>, +w: Wf.top(V, m), +k: String, +x: V, +j: String, ejk: {String.eq(j, k) == False{} : Bool}) -> {gv(V, Map.get(V, d, Map.set(&2, V, m, k, x), j)) == gv(V, Map.get(V, d, m, j)) : V}:
  %Equal.sym(V, gv(V, Map.get(V, d, Map.set(&2, V, m, k, x), j)), Maybe.default(&2, V, found(V, Map.set(&2, V, m, k, x), j), d), get_is(V, d, Map.set(&2, V, m, k, x), j)) : {_ == gv(V, Map.get(V, d, m, j)) : V}
  %Equal.sym(V, gv(V, Map.get(V, d, m, j)), Maybe.default(&2, V, found(V, m, j), d), get_is(V, d, m, j)) : {Maybe.default(&2, V, found(V, Map.set(&2, V, m, k, x), j), d) == _ : V}
  %Equal.sym(Map<&2, V>, Map.set(&2, V, m, k, x), cset(V, m, k, x), set_is(V, m, k, x)) : {Maybe.default(&2, V, found(V, _, j), d) == Maybe.default(&2, V, found(V, m, j), d) : V}
  %Equal.sym(Maybe<&2, V>, found(V, cset(V, m, k, x), j), found(V, m, j), set_other_top(V, m, w, k, x, j, ejk)) : {Maybe.default(&2, V, _, d) == Maybe.default(&2, V, found(V, m, j), d) : V}
  {==}

def has_set_other(-V: Data, +m: Map<&2, V>, +w: Wf.top(V, m), +k: String, +x: V, +j: String, ejk: {String.eq(j, k) == False{} : Bool}) -> {hv(V, Map.has(&2, V, Map.set(&2, V, m, k, x), j)) == hv(V, Map.has(&2, V, m, j)) : Bool}:
  %Equal.sym(Bool, hv(V, Map.has(&2, V, Map.set(&2, V, m, k, x), j)), Maybe.is_some(&2, V, found(V, Map.set(&2, V, m, k, x), j)), has_is(V, Map.set(&2, V, m, k, x), j)) : {_ == hv(V, Map.has(&2, V, m, j)) : Bool}
  %Equal.sym(Bool, hv(V, Map.has(&2, V, m, j)), Maybe.is_some(&2, V, found(V, m, j)), has_is(V, m, j)) : {Maybe.is_some(&2, V, found(V, Map.set(&2, V, m, k, x), j)) == _ : Bool}
  %Equal.sym(Map<&2, V>, Map.set(&2, V, m, k, x), cset(V, m, k, x), set_is(V, m, k, x)) : {Maybe.is_some(&2, V, found(V, _, j)) == Maybe.is_some(&2, V, found(V, m, j)) : Bool}
  %Equal.sym(Maybe<&2, V>, found(V, cset(V, m, k, x), j), found(V, m, j), set_other_top(V, m, w, k, x, j, ejk)) : {Maybe.is_some(&2, V, _) == Maybe.is_some(&2, V, found(V, m, j)) : Bool}
  {==}

# What `Set.has` answers of a set built from a list: whether the list has
# the string, as `Rev.member` reads it.
def listed(xs: List<&2, String>, +k: String) -> Bool:
  List.contains(~String, ~(a => b => String.eq(a, b)), xs, k)

def from_list.step(+s: Set(), +h: String, +t: List<&2, String>, +k: String, e: Bool, +ee: {String.eq(h, k) == e : Bool}, w: Wf.top(Unit, s)) -> {Bool.or(listed(t, k), hv(Unit, Set.has(Set.add(s, h), k))) == Bool.or(Bool.or(String.eq(h, k), listed(t, k)), hv(Unit, Set.has(s, k))) : Bool}:
  match e:
    case True{}:
      +hk = Str.eq_true(h, k, ee)
      +hs = Equal.trans(Bool, hv(Unit, Set.has(Set.add(s, h), k)), hv(Unit, Set.has(Set.add(s, h), h)), True{}, Equal.cong(String, Bool, z => hv(Unit, Set.has(Set.add(s, h), z)), k, h, Equal.sym(String, h, k, hk)), has_set_same(Unit, s, h, Unit{}))
      %Equal.sym(Bool, String.eq(h, k), True{}, ee) : {Bool.or(listed(t, k), hv(Unit, Set.has(Set.add(s, h), k))) == Bool.or(Bool.or(_, listed(t, k)), hv(Unit, Set.has(s, k))) : Bool}
      %Equal.sym(Bool, hv(Unit, Set.has(Set.add(s, h), k)), True{}, hs) : {Bool.or(listed(t, k), _) == True{} : Bool}
      or_true_r(listed(t, k))
    case False{}:
      %Equal.sym(Bool, String.eq(h, k), False{}, ee) : {Bool.or(listed(t, k), hv(Unit, Set.has(Set.add(s, h), k))) == Bool.or(Bool.or(_, listed(t, k)), hv(Unit, Set.has(s, k))) : Bool}
      %Equal.sym(Bool, hv(Unit, Set.has(Set.add(s, h), k)), hv(Unit, Set.has(s, k)), has_set_other(Unit, s, w, h, Unit{}, k, eq_flip(h, k, ee))) : {Bool.or(listed(t, k), _) == Bool.or(listed(t, k), hv(Unit, Set.has(s, k))) : Bool}
      {==}

def from_list_go(xs: List<&2, String>, +s: Set(), +w: Wf.top(Unit, s), +k: String) -> {hv(Unit, Set.has(Set.from_list.go(xs, s), k)) == Bool.or(listed(xs, k), hv(Unit, Set.has(s, k))) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %Equal.sym(Bool, hv(Unit, Set.has(Set.from_list.go(t, Set.add(s, h)), k)), Bool.or(listed(t, k), hv(Unit, Set.has(Set.add(s, h), k))), from_list_go(t, Set.add(s, h), wf_set_map(Unit, s, w, h, Unit{}), k)) : {_ == Bool.or(Bool.or(String.eq(h, k), listed(t, k)), hv(Unit, Set.has(s, k))) : Bool}
      from_list.step(s, h, t, k, String.eq(h, k), {==}, w)

# A set built from a list holds exactly the list's strings.
def set_from_list(+xs: List<&2, String>, +k: String) -> {hv(Unit, Set.has(Set.from_list(xs), k)) == listed(xs, k) : Bool}:
  %Equal.sym(Bool, hv(Unit, Set.has(Set.from_list.go(xs, Set.new()), k)), Bool.or(listed(xs, k), False{}), from_list_go(xs, Set.new(), {==}, k)) : {_ == listed(xs, k) : Bool}
  or_false_id(listed(xs, k))

# The same for `Set`, whose `add` is `Map.set` of `Unit{}`.
def set_has_new(+k: String) -> {hv(Unit, Set.has(Set.new(), k)) == False{} : Bool}:
  {==}

def set_add_same(+s: Set(), +k: String) -> {hv(Unit, Set.has(Set.add(s, k), k)) == True{} : Bool}:
  has_set_same(Unit, s, k, Unit{})

def set_add_other(+s: Set(), +w: Wf.top(Unit, s), +k: String, +j: String, ejk: {String.eq(j, k) == False{} : Bool}) -> {hv(Unit, Set.has(Set.add(s, k), j)) == hv(Unit, Set.has(s, j)) : Bool}:
  has_set_other(Unit, s, w, k, Unit{}, j, ejk)

def set_wf_add(+s: Set(), +w: Wf.top(Unit, s), +k: String) -> Wf.top(Unit, Set.add(s, k)):
  wf_set_map(Unit, s, w, k, Unit{})

def set_wf_go(xs: List<&2, String>, +s: Set(), +w: Wf.top(Unit, s)) -> Wf.top(Unit, Set.from_list.go(xs, s)):
  match xs:
    case Nil{}:
      w
    case +h <> t:
      set_wf_go(t, Set.add(s, h), set_wf_add(s, w, h))

# A set built from a list is one `Set.add` goes on keeping.
def set_wf_from_list(xs: List<&2, String>) -> Wf.top(Unit, Set.from_list(xs)):
  set_wf_go(xs, Set.new(), {==})

# `Map.from_list`
# ---------------

# The value a list of pairs gives a key: the one beside the last time the
# key appears, or none.
def last.or(-V: Data, r: Maybe<&2, V>, hit: Bool, +v: V) -> Maybe<&2, V>:
  match r:
    case None{}:
      Bool.pick(Maybe<&2, V>, hit, Some{v}, None{})
    case Some{a}:
      Some{a}

def last_value(-V: Data, kvs: List<&2, Sigma<&2, &2, String, _ => V>>, +k: String) -> Maybe<&2, V>:
  match kvs:
    case Nil{}:
      None{}
    case (j, v) <> t:
      last.or(V, last_value(V, t, k), String.eq(j, k), v)

def maybe_or(-V: Data, a: Maybe<&2, V>, b: Maybe<&2, V>) -> Maybe<&2, V>:
  match a:
    case None{}:
      b
    case Some{x}:
      Some{x}

def found_set(-V: Data, +m: Map<&2, V>, +w: Wf.top(V, m), +j: String, +v: V, +k: String, hit: Bool, +eh: {String.eq(j, k) == hit : Bool}) -> {found(V, Map.set(&2, V, m, j, v), k) == maybe_or(V, Bool.pick(Maybe<&2, V>, hit, Some{v}, None{}), found(V, m, k)) : Maybe<&2, V>}:
  match hit:
    case True{}:
      %Equal.sym(Map<&2, V>, Map.set(&2, V, m, j, v), cset(V, m, j, v), set_is(V, m, j, v)) : {found(V, _, k) == Some{v} : Maybe<&2, V>}
      +jk = Str.eq_true(j, k, eh)
      %jk : {found(V, cset(V, m, j, v), _) == Some{v} : Maybe<&2, V>}
      set_same(V, m, j, v)
    case False{}:
      %Equal.sym(Map<&2, V>, Map.set(&2, V, m, j, v), cset(V, m, j, v), set_is(V, m, j, v)) : {found(V, _, k) == found(V, m, k) : Maybe<&2, V>}
      set_other_top(V, m, w, j, v, k, eq_flip(j, k, eh))

def from_list_step(-V: Data, +m: Map<&2, V>, +w: Wf.top(V, m), +j: String, +v: V, +k: String, r: Maybe<&2, V>) -> {maybe_or(V, r, found(V, Map.set(&2, V, m, j, v), k)) == maybe_or(V, last.or(V, r, String.eq(j, k), v), found(V, m, k)) : Maybe<&2, V>}:
  match r:
    case None{}:
      found_set(V, m, w, j, v, k, String.eq(j, k), {==})
    case Some{a}:
      {==}

def from_list_found(-V: Data, kvs: List<&2, Sigma<&2, &2, String, _ => V>>, +m: Map<&2, V>, +w: Wf.top(V, m), +k: String) -> {found(V, Map.from_list.go(&2, V, kvs, m), k) == maybe_or(V, last_value(V, kvs, k), found(V, m, k)) : Maybe<&2, V>}:
  match kvs:
    case Nil{}:
      {==}
    case (+j, +v) <> +t:
      %Equal.sym(Maybe<&2, V>, found(V, Map.from_list.go(&2, V, t, Map.set(&2, V, m, j, v)), k), maybe_or(V, last_value(V, t, k), found(V, Map.set(&2, V, m, j, v), k)), from_list_found(V, t, Map.set(&2, V, m, j, v), wf_set_map(V, m, w, j, v), k)) : {_ == maybe_or(V, last.or(V, last_value(V, t, k), String.eq(j, k), v), found(V, m, k)) : Maybe<&2, V>}
      from_list_step(V, m, w, j, v, k, last_value(V, t, k))

def maybe_or_none(-V: Data, a: Maybe<&2, V>) -> {maybe_or(V, a, None{}) == a : Maybe<&2, V>}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      {==}

# A map built from a list of pairs gives each key the value beside the
# last time the key appears, and the default where it never does.
def get_from_list(-V: Data, +d: V, +kvs: List<&2, Sigma<&2, &2, String, _ => V>>, +k: String) -> {gv(V, Map.get(V, d, Map.from_list(&2, V, kvs), k)) == Maybe.default(&2, V, last_value(V, kvs, k), d) : V}:
  %Equal.sym(V, gv(V, Map.get(V, d, Map.from_list(&2, V, kvs), k)), Maybe.default(&2, V, found(V, Map.from_list(&2, V, kvs), k), d), get_is(V, d, Map.from_list(&2, V, kvs), k)) : {_ == Maybe.default(&2, V, last_value(V, kvs, k), d) : V}
  %Equal.sym(Maybe<&2, V>, found(V, Map.from_list.go(&2, V, kvs, MTip{}), k), maybe_or(V, last_value(V, kvs, k), None{}), from_list_found(V, kvs, MTip{}, {==}, k)) : {Maybe.default(&2, V, _, d) == Maybe.default(&2, V, last_value(V, kvs, k), d) : V}
  %Equal.sym(Maybe<&2, V>, maybe_or(V, last_value(V, kvs, k), None{}), last_value(V, kvs, k), maybe_or_none(V, last_value(V, kvs, k))) : {Maybe.default(&2, V, _, d) == Maybe.default(&2, V, last_value(V, kvs, k), d) : V}
  {==}

def has_from_list(-V: Data, +kvs: List<&2, Sigma<&2, &2, String, _ => V>>, +k: String) -> {hv(V, Map.has(&2, V, Map.from_list(&2, V, kvs), k)) == Maybe.is_some(&2, V, last_value(V, kvs, k)) : Bool}:
  %Equal.sym(Bool, hv(V, Map.has(&2, V, Map.from_list(&2, V, kvs), k)), Maybe.is_some(&2, V, found(V, Map.from_list(&2, V, kvs), k)), has_is(V, Map.from_list(&2, V, kvs), k)) : {_ == Maybe.is_some(&2, V, last_value(V, kvs, k)) : Bool}
  %Equal.sym(Maybe<&2, V>, found(V, Map.from_list.go(&2, V, kvs, MTip{}), k), maybe_or(V, last_value(V, kvs, k), None{}), from_list_found(V, kvs, MTip{}, {==}, k)) : {Maybe.is_some(&2, V, _) == Maybe.is_some(&2, V, last_value(V, kvs, k)) : Bool}
  %Equal.sym(Maybe<&2, V>, maybe_or(V, last_value(V, kvs, k), None{}), last_value(V, kvs, k), maybe_or_none(V, last_value(V, kvs, k))) : {Maybe.is_some(&2, V, _) == Maybe.is_some(&2, V, last_value(V, kvs, k)) : Bool}
  {==}

# `Map.keys`
# ----------

def eq_sym.go(+a: String, +b: String, s: Bool, +es: {String.eq(a, b) == s : Bool}) -> {String.eq(a, b) == String.eq(b, a) : Bool}:
  match s:
    case True{}:
      +ab = Str.eq_true(a, b, es)
      %ab : {String.eq(a, _) == String.eq(_, a) : Bool}
      {==}
    case False{}:
      Equal.trans(Bool, String.eq(a, b), False{}, String.eq(b, a), es, Equal.sym(Bool, String.eq(b, a), False{}, eq_flip(a, b, es)))

def eq_sym(+a: String, +b: String) -> {String.eq(a, b) == String.eq(b, a) : Bool}:
  eq_sym.go(a, b, String.eq(a, b), {==})

def keys_go(-V: Data, m: Map<&2, V>, +acc: List<&2, String>, +a: String) -> {listed(Map.keys.go(&2, V, m, acc), a) == Bool.or(mem(V, m, a), listed(acc, a)) : Bool}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k, v}:
      %eq_sym(k, a) : {Bool.or(String.eq(k, a), listed(acc, a)) == Bool.or(_, listed(acc, a)) : Bool}
      {==}
    case MNode{p, +lo, +hi}:
      %Equal.sym(Bool, listed(Map.keys.go(&2, V, lo, Map.keys.go(&2, V, hi, acc)), a), Bool.or(mem(V, lo, a), listed(Map.keys.go(&2, V, hi, acc), a)), keys_go(V, lo, Map.keys.go(&2, V, hi, acc), a)) : {_ == Bool.or(Bool.or(mem(V, lo, a), mem(V, hi, a)), listed(acc, a)) : Bool}
      %Equal.sym(Bool, listed(Map.keys.go(&2, V, hi, acc), a), Bool.or(mem(V, hi, a), listed(acc, a)), keys_go(V, hi, acc, a)) : {Bool.or(mem(V, lo, a), _) == Bool.or(Bool.or(mem(V, lo, a), mem(V, hi, a)), listed(acc, a)) : Bool}
      Equal.sym(Bool, Bool.or(Bool.or(mem(V, lo, a), mem(V, hi, a)), listed(acc, a)), Bool.or(mem(V, lo, a), Bool.or(mem(V, hi, a), listed(acc, a))), or_assoc(mem(V, lo, a), mem(V, hi, a), listed(acc, a)))

# `Map.keys` lists every key at a leaf, and nothing else.
def keys_mem(-V: Data, +m: Map<&2, V>, +a: String) -> {listed(Map.keys(&2, V, m), a) == mem(V, m, a) : Bool}:
  Equal.trans(Bool, listed(Map.keys(&2, V, m), a), Bool.or(mem(V, m, a), False{}), mem(V, m, a), keys_go(V, m, Nil{}, a), or_false_id(mem(V, m, a)))

def found_complete.node(-V: Data, +p: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +w: {wf(V, MNode{p, lo, hi}) == True{} : Bool}, +a: String, ea: {Bool.or(mem(V, lo, a), mem(V, hi, a)) == True{} : Bool}, s: Bool, +es: {mem(V, lo, a) == s : Bool}, ilo: {mem(V, lo, a) == True{} : Bool} -> {Maybe.is_some(&2, V, found(V, lo, a)) == True{} : Bool}, ihi: {mem(V, hi, a) == True{} : Bool} -> {Maybe.is_some(&2, V, found(V, hi, a)) == True{} : Bool}) -> {Maybe.is_some(&2, V, Bool.pick(Maybe<&2, V>, bv(a, p), found(V, hi, a), found(V, lo, a))) == True{} : Bool}:
  match s:
    case True{}:
      %Equal.sym(Bool, bv(a, p), False{}, sides_use(V, lo, p, False{}, wf_slo(V, p, lo, hi, w), a, es)) : {Maybe.is_some(&2, V, Bool.pick(Maybe<&2, V>, _, found(V, hi, a), found(V, lo, a))) == True{} : Bool}
      ilo(es)
    case False{}:
      +eh = mem_or(V, lo, hi, a, False{}, es, ea)
      %Equal.sym(Bool, bv(a, p), True{}, sides_use(V, hi, p, True{}, wf_shi(V, p, lo, hi, w), a, eh)) : {Maybe.is_some(&2, V, Bool.pick(Maybe<&2, V>, _, found(V, hi, a), found(V, lo, a))) == True{} : Bool}
      ihi(eh)

# In a trie, every key at a leaf finds something.
def found_complete(-V: Data, m: Map<&2, V>, +w: {wf(V, m) == True{} : Bool}, +a: String, e: {mem(V, m, a) == True{} : Bool}) -> {Maybe.is_some(&2, V, found(V, m, a)) == True{} : Bool}:
  match m:
    case MTip{}:
      Empty.absurd({False{} == True{} : Bool}, Str.false_true(w))
    case MLeaf{+k, +v}:
      %Equal.sym(Bool, String.eq(a, k), True{}, e) : {Maybe.is_some(&2, V, Bool.pick(Maybe<&2, V>, _, Some{v}, None{})) == True{} : Bool}
      {==}
    case MNode{+p, +lo, +hi}:
      found_complete.node(V, p, lo, hi, w, a, e, mem(V, lo, a), {==}, x => found_complete(V, lo, wf_lo(V, p, lo, hi, w), a, x), x => found_complete(V, hi, wf_hi(V, p, lo, hi, w), a, x))

def keys_has.go(-V: Data, +m: Map<&2, V>, +w: {wf(V, m) == True{} : Bool}, +a: String, s: Bool, +es: {mem(V, m, a) == s : Bool}) -> {mem(V, m, a) == Maybe.is_some(&2, V, found(V, m, a)) : Bool}:
  match s:
    case True{}:
      Equal.trans(Bool, mem(V, m, a), True{}, Maybe.is_some(&2, V, found(V, m, a)), es, Equal.sym(Bool, Maybe.is_some(&2, V, found(V, m, a)), True{}, found_complete(V, m, w, a, es)))
    case False{}:
      %Equal.sym(Maybe<&2, V>, found(V, m, a), None{}, found_none(V, m, a, es)) : {mem(V, m, a) == Maybe.is_some(&2, V, _) : Bool}
      es

# In every map `Map.new` and `Map.set` build, `Map.keys` lists exactly the
# keys `Map.has` holds.
def keys_has(-V: Data, m: Map<&2, V>, +w: Wf.top(V, m), +a: String) -> {listed(Map.keys(&2, V, m), a) == hv(V, Map.has(&2, V, m, a)) : Bool}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k, +v}:
      Equal.trans(Bool, listed(Map.keys(&2, V, MLeaf{k, v}), a), mem(V, MLeaf{k, v}, a), hv(V, Map.has(&2, V, MLeaf{k, v}, a)), keys_mem(V, MLeaf{k, v}, a), Equal.trans(Bool, mem(V, MLeaf{k, v}, a), Maybe.is_some(&2, V, found(V, MLeaf{k, v}, a)), hv(V, Map.has(&2, V, MLeaf{k, v}, a)), keys_has.go(V, MLeaf{k, v}, {==}, a, mem(V, MLeaf{k, v}, a), {==}), Equal.sym(Bool, hv(V, Map.has(&2, V, MLeaf{k, v}, a)), Maybe.is_some(&2, V, found(V, MLeaf{k, v}, a)), has_is(V, MLeaf{k, v}, a))))
    case MNode{+p, +lo, +hi}:
      Equal.trans(Bool, listed(Map.keys(&2, V, MNode{p, lo, hi}), a), mem(V, MNode{p, lo, hi}, a), hv(V, Map.has(&2, V, MNode{p, lo, hi}, a)), keys_mem(V, MNode{p, lo, hi}, a), Equal.trans(Bool, mem(V, MNode{p, lo, hi}, a), Maybe.is_some(&2, V, found(V, MNode{p, lo, hi}, a)), hv(V, Map.has(&2, V, MNode{p, lo, hi}, a)), keys_has.go(V, MNode{p, lo, hi}, w, a, mem(V, MNode{p, lo, hi}, a), {==}), Equal.sym(Bool, hv(V, Map.has(&2, V, MNode{p, lo, hi}, a)), Maybe.is_some(&2, V, found(V, MNode{p, lo, hi}, a)), has_is(V, MNode{p, lo, hi}, a))))

# `Map.pop` and `Map.del`
# -----------------------

# A node whose low side emptied is its high side, and the other way round.
def collapse_lo(-V: Data, +p: Nat, lo: Map<&2, V>, +hi: Map<&2, V>) -> Map<&2, V>:
  match lo:
    case MTip{}:
      hi
    case MLeaf{k, v}:
      MNode{p, MLeaf{k, v}, hi}
    case MNode{q, a, b}:
      MNode{p, MNode{q, a, b}, hi}

def collapse_hi(-V: Data, +p: Nat, +lo: Map<&2, V>, hi: Map<&2, V>) -> Map<&2, V>:
  match hi:
    case MTip{}:
      lo
    case MLeaf{k, v}:
      MNode{p, lo, MLeaf{k, v}}
    case MNode{q, a, b}:
      MNode{p, lo, MNode{q, a, b}}

# `Map.del`: the leaf the key's bits lead to taken away where its key is
# the key, and a node left with one side replaced by that side.
def cdel(-V: Data, m: Map<&2, V>, +k: String) -> Map<&2, V>:
  match m:
    case MTip{}:
      MTip{}
    case MLeaf{+k1, +v}:
      Bool.pick(Map<&2, V>, String.eq(k, k1), MTip{}, MLeaf{k1, v})
    case MNode{+p, +lo, +hi}:
      Bool.pick(Map<&2, V>, bv(k, p), collapse_hi(V, p, lo, cdel(V, hi, k)), collapse_lo(V, p, cdel(V, lo, k), hi))

def pop_lo_is(-V: Data, +p: Nat, +hi: Map<&2, V>, x: Map<&2, V>, -r: Maybe<&2, V>) -> {Map.pop.lo(&2, V, p, hi, (x, r)) == (collapse_lo(V, p, x, hi), r) : Map<&2, V> & Maybe<&2, V>}:
  match x:
    case MTip{}:
      {==}
    case MLeaf{k, v}:
      {==}
    case MNode{q, a, b}:
      {==}

def pop_hi_is(-V: Data, +p: Nat, +lo: Map<&2, V>, x: Map<&2, V>, -r: Maybe<&2, V>) -> {Map.pop.hi(&2, V, p, lo, (x, r)) == (collapse_hi(V, p, lo, x), r) : Map<&2, V> & Maybe<&2, V>}:
  match x:
    case MTip{}:
      {==}
    case MLeaf{k, v}:
      {==}
    case MNode{q, a, b}:
      {==}

def pop_leaf(-V: Data, +v: V, +k: String, +k1: String, c: Cmp) -> {Map.pop.leaf(&2, V, v, ((k, k1), c)) == (Bool.pick(Map<&2, V>, Cmp.is_eq(c), MTip{}, MLeaf{k1, v}), Bool.pick(Maybe<&2, V>, Cmp.is_eq(c), Some{v}, None{})) : Map<&2, V> & Maybe<&2, V>}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def pop_node(-V: Data, +p: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +k: String, b: Bool, +eb: {bv(k, p) == b : Bool}, ilo: {Map.pop(&2, V, lo, k) == (cdel(V, lo, k), found(V, lo, k)) : Map<&2, V> & Maybe<&2, V>}, ihi: {Map.pop(&2, V, hi, k) == (cdel(V, hi, k), found(V, hi, k)) : Map<&2, V> & Maybe<&2, V>}) -> {Map.pop.bit(&2, V, lo, hi, p, (k, bv(k, p))) == (Bool.pick(Map<&2, V>, bv(k, p), collapse_hi(V, p, lo, cdel(V, hi, k)), collapse_lo(V, p, cdel(V, lo, k), hi)), Bool.pick(Maybe<&2, V>, bv(k, p), found(V, hi, k), found(V, lo, k))) : Map<&2, V> & Maybe<&2, V>}:
  match b:
    case True{}:
      %Equal.sym(Bool, bv(k, p), True{}, eb) : {Map.pop.bit(&2, V, lo, hi, p, (k, _)) == (Bool.pick(Map<&2, V>, _, collapse_hi(V, p, lo, cdel(V, hi, k)), collapse_lo(V, p, cdel(V, lo, k), hi)), Bool.pick(Maybe<&2, V>, _, found(V, hi, k), found(V, lo, k))) : Map<&2, V> & Maybe<&2, V>}
      %Equal.sym(Map<&2, V> & Maybe<&2, V>, Map.pop(&2, V, hi, k), (cdel(V, hi, k), found(V, hi, k)), ihi) : {Map.pop.hi(&2, V, p, lo, _) == (collapse_hi(V, p, lo, cdel(V, hi, k)), found(V, hi, k)) : Map<&2, V> & Maybe<&2, V>}
      pop_hi_is(V, p, lo, cdel(V, hi, k), found(V, hi, k))
    case False{}:
      %Equal.sym(Bool, bv(k, p), False{}, eb) : {Map.pop.bit(&2, V, lo, hi, p, (k, _)) == (Bool.pick(Map<&2, V>, _, collapse_hi(V, p, lo, cdel(V, hi, k)), collapse_lo(V, p, cdel(V, lo, k), hi)), Bool.pick(Maybe<&2, V>, _, found(V, hi, k), found(V, lo, k))) : Map<&2, V> & Maybe<&2, V>}
      %Equal.sym(Map<&2, V> & Maybe<&2, V>, Map.pop(&2, V, lo, k), (cdel(V, lo, k), found(V, lo, k)), ilo) : {Map.pop.lo(&2, V, p, hi, _) == (collapse_lo(V, p, cdel(V, lo, k), hi), found(V, lo, k)) : Map<&2, V> & Maybe<&2, V>}
      pop_lo_is(V, p, hi, cdel(V, lo, k), found(V, lo, k))

# `Map.pop` hands back `cdel` of the map and what the key found in it.
def pop_is(-V: Data, m: Map<&2, V>, +k: String) -> {Map.pop(&2, V, m, k) == (cdel(V, m, k), found(V, m, k)) : Map<&2, V> & Maybe<&2, V>}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k1, +v}:
      %Equal.sym((String & String) & Cmp, String.cmp(k, k1), ((k, k1), String.order(k, k1)), cmp_back(k, k1)) : {Map.pop.leaf(&2, V, v, _) == (Bool.pick(Map<&2, V>, String.eq.fin(_), MTip{}, MLeaf{k1, v}), Bool.pick(Maybe<&2, V>, String.eq.fin(_), Some{v}, None{})) : Map<&2, V> & Maybe<&2, V>}
      pop_leaf(V, v, k, k1, String.order(k, k1))
    case MNode{+p, +lo, +hi}:
      %Equal.sym(String & Bool, Map.bit(k, p), (k, bv(k, p)), bit_back(k, p)) : {Map.pop.bit(&2, V, lo, hi, p, _) == (cdel(V, MNode{p, lo, hi}, k), found(V, MNode{p, lo, hi}, k)) : Map<&2, V> & Maybe<&2, V>}
      pop_node(V, p, lo, hi, k, bv(k, p), {==}, pop_is(V, lo, k), pop_is(V, hi, k))

def pv(-V: Data, r: Map<&2, V> & Maybe<&2, V>) -> Maybe<&2, V>:
  (m, x) = r
  x

# What `Map.pop` hands back is what the key finds, in any map at all.
def pop_found(-V: Data, +m: Map<&2, V>, +k: String) -> {pv(V, Map.pop(&2, V, m, k)) == found(V, m, k) : Maybe<&2, V>}:
  %Equal.sym(Map<&2, V> & Maybe<&2, V>, Map.pop(&2, V, m, k), (cdel(V, m, k), found(V, m, k)), pop_is(V, m, k)) : {pv(V, _) == found(V, m, k) : Maybe<&2, V>}
  {==}

def del_is(-V: Data, +m: Map<&2, V>, +k: String) -> {Map.del(&2, V, m, k) == cdel(V, m, k) : Map<&2, V>}:
  %Equal.sym(Map<&2, V> & Maybe<&2, V>, Map.pop(&2, V, m, k), (cdel(V, m, k), found(V, m, k)), pop_is(V, m, k)) : {Map.del.fin(&2, V, _) == cdel(V, m, k) : Map<&2, V>}
  {==}

def side_none.go(-V: Data, +m: Map<&2, V>, +p: Nat, +b: Bool, +e: {sides(V, m, p, b) == True{} : Bool}, +j: String, ej: {bv(j, p) == Bool.not(b) : Bool}, +s: Bool, +es: {mem(V, m, j) == s : Bool}) -> {found(V, m, j) == None{} : Maybe<&2, V>}:
  match s:
    case False{}:
      found_none(V, m, j, es)
    case True{}:
      Empty.absurd({found(V, m, j) == None{} : Maybe<&2, V>}, not_self(b, Equal.trans(Bool, b, bv(j, p), Bool.not(b), Equal.sym(Bool, bv(j, p), b, sides_use(V, m, p, b, e, j, es)), ej)))

# A key a side's `Side` sets apart from `j` holds nothing `j` finds.
def side_none(-V: Data, +m: Map<&2, V>, +p: Nat, +b: Bool, +e: {sides(V, m, p, b) == True{} : Bool}, +j: String, ej: {bv(j, p) == Bool.not(b) : Bool}) -> {found(V, m, j) == None{} : Maybe<&2, V>}:
  side_none.go(V, m, p, b, e, j, ej, mem(V, m, j), {==})


def del_leaf_same(-V: Data, +k: String, +k1: String, +v: V, e: Bool, +ee: {String.eq(k, k1) == e : Bool}) -> {found(V, Bool.pick(Map<&2, V>, String.eq(k, k1), MTip{}, MLeaf{k1, v}), k) == None{} : Maybe<&2, V>}:
  match e:
    case True{}:
      %Equal.sym(Bool, String.eq(k, k1), True{}, ee) : {found(V, Bool.pick(Map<&2, V>, _, MTip{}, MLeaf{k1, v}), k) == None{} : Maybe<&2, V>}
      {==}
    case False{}:
      %Equal.sym(Bool, String.eq(k, k1), False{}, ee) : {found(V, Bool.pick(Map<&2, V>, _, MTip{}, MLeaf{k1, v}), k) == None{} : Maybe<&2, V>}
      found_leaf_other(V, k1, v, k, ee)

def del_same.hi(-V: Data, +p: Nat, +lo: Map<&2, V>, x: Map<&2, V>, +k: String, +eb: {bv(k, p) == True{} : Bool}, +ih: {found(V, x, k) == None{} : Maybe<&2, V>}, +slo: {sides(V, lo, p, False{}) == True{} : Bool}) -> {found(V, collapse_hi(V, p, lo, x), k) == None{} : Maybe<&2, V>}:
  match x:
    case MTip{}:
      side_none(V, lo, p, False{}, slo, k, eb)
    case MLeaf{+a, +v}:
      %Equal.sym(Bool, bv(k, p), True{}, eb) : {Bool.pick(Maybe<&2, V>, _, found(V, MLeaf{a, v}, k), found(V, lo, k)) == None{} : Maybe<&2, V>}
      ih
    case MNode{+q, +a, +b}:
      %Equal.sym(Bool, bv(k, p), True{}, eb) : {Bool.pick(Maybe<&2, V>, _, found(V, MNode{q, a, b}, k), found(V, lo, k)) == None{} : Maybe<&2, V>}
      ih

def del_same.lo(-V: Data, +p: Nat, x: Map<&2, V>, +hi: Map<&2, V>, +k: String, +eb: {bv(k, p) == False{} : Bool}, +ih: {found(V, x, k) == None{} : Maybe<&2, V>}, +shi: {sides(V, hi, p, True{}) == True{} : Bool}) -> {found(V, collapse_lo(V, p, x, hi), k) == None{} : Maybe<&2, V>}:
  match x:
    case MTip{}:
      side_none(V, hi, p, True{}, shi, k, eb)
    case MLeaf{+a, +v}:
      %Equal.sym(Bool, bv(k, p), False{}, eb) : {Bool.pick(Maybe<&2, V>, _, found(V, hi, k), found(V, MLeaf{a, v}, k)) == None{} : Maybe<&2, V>}
      ih
    case MNode{+q, +a, +b}:
      %Equal.sym(Bool, bv(k, p), False{}, eb) : {Bool.pick(Maybe<&2, V>, _, found(V, hi, k), found(V, MNode{q, a, b}, k)) == None{} : Maybe<&2, V>}
      ih

def del_same.node(-V: Data, +p: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +w: {wf(V, MNode{p, lo, hi}) == True{} : Bool}, +k: String, b: Bool, +eb: {bv(k, p) == b : Bool}, ilo: {found(V, cdel(V, lo, k), k) == None{} : Maybe<&2, V>}, ihi: {found(V, cdel(V, hi, k), k) == None{} : Maybe<&2, V>}) -> {found(V, Bool.pick(Map<&2, V>, bv(k, p), collapse_hi(V, p, lo, cdel(V, hi, k)), collapse_lo(V, p, cdel(V, lo, k), hi)), k) == None{} : Maybe<&2, V>}:
  match b:
    case True{}:
      %Equal.sym(Bool, bv(k, p), True{}, eb) : {found(V, Bool.pick(Map<&2, V>, _, collapse_hi(V, p, lo, cdel(V, hi, k)), collapse_lo(V, p, cdel(V, lo, k), hi)), k) == None{} : Maybe<&2, V>}
      del_same.hi(V, p, lo, cdel(V, hi, k), k, eb, ihi, wf_slo(V, p, lo, hi, w))
    case False{}:
      %Equal.sym(Bool, bv(k, p), False{}, eb) : {found(V, Bool.pick(Map<&2, V>, _, collapse_hi(V, p, lo, cdel(V, hi, k)), collapse_lo(V, p, cdel(V, lo, k), hi)), k) == None{} : Maybe<&2, V>}
      del_same.lo(V, p, cdel(V, lo, k), hi, k, eb, ilo, wf_shi(V, p, lo, hi, w))

# In a trie, a key finds nothing once `cdel` took it away.
def del_same(-V: Data, m: Map<&2, V>, +w: {wf(V, m) == True{} : Bool}, +k: String) -> {found(V, cdel(V, m, k), k) == None{} : Maybe<&2, V>}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k1, +v}:
      del_leaf_same(V, k, k1, v, String.eq(k, k1), {==})
    case MNode{+p, +lo, +hi}:
      del_same.node(V, p, lo, hi, w, k, bv(k, p), {==}, del_same(V, lo, wf_lo(V, p, lo, hi, w), k), del_same(V, hi, wf_hi(V, p, lo, hi, w), k))

def del_leaf_other(-V: Data, +k: String, +k1: String, +v: V, +j: String, ejk: {String.eq(j, k) == False{} : Bool}, e: Bool, +ee: {String.eq(k, k1) == e : Bool}) -> {found(V, Bool.pick(Map<&2, V>, String.eq(k, k1), MTip{}, MLeaf{k1, v}), j) == found(V, MLeaf{k1, v}, j) : Maybe<&2, V>}:
  match e:
    case True{}:
      %Equal.sym(Bool, String.eq(k, k1), True{}, ee) : {found(V, Bool.pick(Map<&2, V>, _, MTip{}, MLeaf{k1, v}), j) == found(V, MLeaf{k1, v}, j) : Maybe<&2, V>}
      +kk1 = Str.eq_true(k, k1, ee)
      %kk1 : {None{} == found(V, MLeaf{_, v}, j) : Maybe<&2, V>}
      Equal.sym(Maybe<&2, V>, found(V, MLeaf{k, v}, j), None{}, found_leaf_other(V, k, v, j, ejk))
    case False{}:
      %Equal.sym(Bool, String.eq(k, k1), False{}, ee) : {found(V, Bool.pick(Map<&2, V>, _, MTip{}, MLeaf{k1, v}), j) == found(V, MLeaf{k1, v}, j) : Maybe<&2, V>}
      {==}

def del_other.hi(-V: Data, +p: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, x: Map<&2, V>, +j: String, c: Bool, +ec: {bv(j, p) == c : Bool}, +ih: {found(V, x, j) == found(V, hi, j) : Maybe<&2, V>}, +slo: {sides(V, lo, p, False{}) == True{} : Bool}) -> {found(V, collapse_hi(V, p, lo, x), j) == Bool.pick(Maybe<&2, V>, bv(j, p), found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}:
  match x c:
    case MTip{} True{}:
      %Equal.sym(Bool, bv(j, p), True{}, ec) : {found(V, lo, j) == Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}
      Equal.trans(Maybe<&2, V>, found(V, lo, j), None{}, found(V, hi, j), side_none(V, lo, p, False{}, slo, j, ec), ih)
    case MTip{} False{}:
      %Equal.sym(Bool, bv(j, p), False{}, ec) : {found(V, lo, j) == Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}
      {==}
    case MLeaf{+a, +v} True{}:
      %Equal.sym(Bool, bv(j, p), True{}, ec) : {Bool.pick(Maybe<&2, V>, _, found(V, MLeaf{a, v}, j), found(V, lo, j)) == Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}
      ih
    case MLeaf{+a, +v} False{}:
      %Equal.sym(Bool, bv(j, p), False{}, ec) : {Bool.pick(Maybe<&2, V>, _, found(V, MLeaf{a, v}, j), found(V, lo, j)) == Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}
      {==}
    case MNode{+q, +a, +b} True{}:
      %Equal.sym(Bool, bv(j, p), True{}, ec) : {Bool.pick(Maybe<&2, V>, _, found(V, MNode{q, a, b}, j), found(V, lo, j)) == Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}
      ih
    case MNode{+q, +a, +b} False{}:
      %Equal.sym(Bool, bv(j, p), False{}, ec) : {Bool.pick(Maybe<&2, V>, _, found(V, MNode{q, a, b}, j), found(V, lo, j)) == Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}
      {==}

def del_other.lo(-V: Data, +p: Nat, +lo: Map<&2, V>, x: Map<&2, V>, +hi: Map<&2, V>, +j: String, c: Bool, +ec: {bv(j, p) == c : Bool}, +ih: {found(V, x, j) == found(V, lo, j) : Maybe<&2, V>}, +shi: {sides(V, hi, p, True{}) == True{} : Bool}) -> {found(V, collapse_lo(V, p, x, hi), j) == Bool.pick(Maybe<&2, V>, bv(j, p), found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}:
  match x c:
    case MTip{} True{}:
      %Equal.sym(Bool, bv(j, p), True{}, ec) : {found(V, hi, j) == Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}
      {==}
    case MTip{} False{}:
      %Equal.sym(Bool, bv(j, p), False{}, ec) : {found(V, hi, j) == Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}
      Equal.trans(Maybe<&2, V>, found(V, hi, j), None{}, found(V, lo, j), side_none(V, hi, p, True{}, shi, j, ec), ih)
    case MLeaf{+a, +v} True{}:
      %Equal.sym(Bool, bv(j, p), True{}, ec) : {Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, MLeaf{a, v}, j)) == Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}
      {==}
    case MLeaf{+a, +v} False{}:
      %Equal.sym(Bool, bv(j, p), False{}, ec) : {Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, MLeaf{a, v}, j)) == Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}
      ih
    case MNode{+q, +a, +b} True{}:
      %Equal.sym(Bool, bv(j, p), True{}, ec) : {Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, MNode{q, a, b}, j)) == Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}
      {==}
    case MNode{+q, +a, +b} False{}:
      %Equal.sym(Bool, bv(j, p), False{}, ec) : {Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, MNode{q, a, b}, j)) == Bool.pick(Maybe<&2, V>, _, found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}
      ih

def del_other.node(-V: Data, +p: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +w: {wf(V, MNode{p, lo, hi}) == True{} : Bool}, +k: String, +j: String, b: Bool, +eb: {bv(k, p) == b : Bool}, ilo: {found(V, cdel(V, lo, k), j) == found(V, lo, j) : Maybe<&2, V>}, ihi: {found(V, cdel(V, hi, k), j) == found(V, hi, j) : Maybe<&2, V>}) -> {found(V, Bool.pick(Map<&2, V>, bv(k, p), collapse_hi(V, p, lo, cdel(V, hi, k)), collapse_lo(V, p, cdel(V, lo, k), hi)), j) == Bool.pick(Maybe<&2, V>, bv(j, p), found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}:
  match b:
    case True{}:
      %Equal.sym(Bool, bv(k, p), True{}, eb) : {found(V, Bool.pick(Map<&2, V>, _, collapse_hi(V, p, lo, cdel(V, hi, k)), collapse_lo(V, p, cdel(V, lo, k), hi)), j) == Bool.pick(Maybe<&2, V>, bv(j, p), found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}
      del_other.hi(V, p, lo, hi, cdel(V, hi, k), j, bv(j, p), {==}, ihi, wf_slo(V, p, lo, hi, w))
    case False{}:
      %Equal.sym(Bool, bv(k, p), False{}, eb) : {found(V, Bool.pick(Map<&2, V>, _, collapse_hi(V, p, lo, cdel(V, hi, k)), collapse_lo(V, p, cdel(V, lo, k), hi)), j) == Bool.pick(Maybe<&2, V>, bv(j, p), found(V, hi, j), found(V, lo, j)) : Maybe<&2, V>}
      del_other.lo(V, p, lo, cdel(V, lo, k), hi, j, bv(j, p), {==}, ilo, wf_shi(V, p, lo, hi, w))

# In a trie, taking one key away changes nothing another key finds.
def del_other(-V: Data, m: Map<&2, V>, +w: {wf(V, m) == True{} : Bool}, +k: String, +j: String, +ejk: {String.eq(j, k) == False{} : Bool}) -> {found(V, cdel(V, m, k), j) == found(V, m, j) : Maybe<&2, V>}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k1, +v}:
      del_leaf_other(V, k, k1, v, j, ejk, String.eq(k, k1), {==})
    case MNode{+p, +lo, +hi}:
      del_other.node(V, p, lo, hi, w, k, j, bv(k, p), {==}, del_other(V, lo, wf_lo(V, p, lo, hi, w), k, j, ejk), del_other(V, hi, wf_hi(V, p, lo, hi, w), k, j, ejk))

# What `cdel` keeps of a subtree's keys, and of the invariant
# ------------------------------------------------------------

def sides_del.leaf(-V: Data, +k: String, +k1: String, +v: V, +s: Nat, +b: Bool, +e: {sides(V, MLeaf{k1, v}, s, b) == True{} : Bool}, c: Bool, +ec: {String.eq(k, k1) == c : Bool}) -> {sides(V, Bool.pick(Map<&2, V>, String.eq(k, k1), MTip{}, MLeaf{k1, v}), s, b) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, String.eq(k, k1), True{}, ec) : {sides(V, Bool.pick(Map<&2, V>, _, MTip{}, MLeaf{k1, v}), s, b) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, String.eq(k, k1), False{}, ec) : {sides(V, Bool.pick(Map<&2, V>, _, MTip{}, MLeaf{k1, v}), s, b) == True{} : Bool}
      e

def sides_del.hi(-V: Data, +p: Nat, +lo: Map<&2, V>, x: Map<&2, V>, +s: Nat, +b: Bool, +elo: {sides(V, lo, s, b) == True{} : Bool}, +ex: {sides(V, x, s, b) == True{} : Bool}) -> {sides(V, collapse_hi(V, p, lo, x), s, b) == True{} : Bool}:
  match x:
    case MTip{}:
      elo
    case MLeaf{+a, +v}:
      and_t(sides(V, lo, s, b), sides(V, MLeaf{a, v}, s, b), elo, ex)
    case MNode{+q, +a, +b2}:
      and_t(sides(V, lo, s, b), sides(V, MNode{q, a, b2}, s, b), elo, ex)

def sides_del.lo(-V: Data, +p: Nat, x: Map<&2, V>, +hi: Map<&2, V>, +s: Nat, +b: Bool, +ex: {sides(V, x, s, b) == True{} : Bool}, +ehi: {sides(V, hi, s, b) == True{} : Bool}) -> {sides(V, collapse_lo(V, p, x, hi), s, b) == True{} : Bool}:
  match x:
    case MTip{}:
      ehi
    case MLeaf{+a, +v}:
      and_t(sides(V, MLeaf{a, v}, s, b), sides(V, hi, s, b), ex, ehi)
    case MNode{+q, +a, +b2}:
      and_t(sides(V, MNode{q, a, b2}, s, b), sides(V, hi, s, b), ex, ehi)

def sides_del.node(-V: Data, +p: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +k: String, +s: Nat, +b: Bool, +e: {sides(V, MNode{p, lo, hi}, s, b) == True{} : Bool}, c: Bool, +ec: {bv(k, p) == c : Bool}, ilo: {sides(V, cdel(V, lo, k), s, b) == True{} : Bool}, ihi: {sides(V, cdel(V, hi, k), s, b) == True{} : Bool}) -> {sides(V, Bool.pick(Map<&2, V>, bv(k, p), collapse_hi(V, p, lo, cdel(V, hi, k)), collapse_lo(V, p, cdel(V, lo, k), hi)), s, b) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, bv(k, p), True{}, ec) : {sides(V, Bool.pick(Map<&2, V>, _, collapse_hi(V, p, lo, cdel(V, hi, k)), collapse_lo(V, p, cdel(V, lo, k), hi)), s, b) == True{} : Bool}
      sides_del.hi(V, p, lo, cdel(V, hi, k), s, b, and_l(sides(V, lo, s, b), sides(V, hi, s, b), e), ihi)
    case False{}:
      %Equal.sym(Bool, bv(k, p), False{}, ec) : {sides(V, Bool.pick(Map<&2, V>, _, collapse_hi(V, p, lo, cdel(V, hi, k)), collapse_lo(V, p, cdel(V, lo, k), hi)), s, b) == True{} : Bool}
      sides_del.lo(V, p, cdel(V, lo, k), hi, s, b, ilo, and_r(sides(V, lo, s, b), sides(V, hi, s, b), e))

# Taking a key away keeps what `sides` says of every key.
def sides_del(-V: Data, m: Map<&2, V>, +k: String, +s: Nat, +b: Bool, +e: {sides(V, m, s, b) == True{} : Bool}) -> {sides(V, cdel(V, m, k), s, b) == True{} : Bool}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k1, +v}:
      sides_del.leaf(V, k, k1, v, s, b, e, String.eq(k, k1), {==})
    case MNode{+p, +lo, +hi}:
      sides_del.node(V, p, lo, hi, k, s, b, e, bv(k, p), {==}, sides_del(V, lo, k, s, b, and_l(sides(V, lo, s, b), sides(V, hi, s, b), e)), sides_del(V, hi, k, s, b, and_r(sides(V, lo, s, b), sides(V, hi, s, b), e)))

def agrees_del.leaf(-V: Data, +k: String, +k1: String, +v: V, +r: String, +s: Nat, +e: {agrees(V, MLeaf{k1, v}, r, s) == True{} : Bool}, c: Bool, +ec: {String.eq(k, k1) == c : Bool}) -> {agrees(V, Bool.pick(Map<&2, V>, String.eq(k, k1), MTip{}, MLeaf{k1, v}), r, s) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, String.eq(k, k1), True{}, ec) : {agrees(V, Bool.pick(Map<&2, V>, _, MTip{}, MLeaf{k1, v}), r, s) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, String.eq(k, k1), False{}, ec) : {agrees(V, Bool.pick(Map<&2, V>, _, MTip{}, MLeaf{k1, v}), r, s) == True{} : Bool}
      e

def agrees_del.hi(-V: Data, +p: Nat, +lo: Map<&2, V>, x: Map<&2, V>, +r: String, +s: Nat, +elo: {agrees(V, lo, r, s) == True{} : Bool}, +ex: {agrees(V, x, r, s) == True{} : Bool}) -> {agrees(V, collapse_hi(V, p, lo, x), r, s) == True{} : Bool}:
  match x:
    case MTip{}:
      elo
    case MLeaf{+a, +v}:
      and_t(agrees(V, lo, r, s), agrees(V, MLeaf{a, v}, r, s), elo, ex)
    case MNode{+q, +a, +b2}:
      and_t(agrees(V, lo, r, s), agrees(V, MNode{q, a, b2}, r, s), elo, ex)

def agrees_del.lo(-V: Data, +p: Nat, x: Map<&2, V>, +hi: Map<&2, V>, +r: String, +s: Nat, +ex: {agrees(V, x, r, s) == True{} : Bool}, +ehi: {agrees(V, hi, r, s) == True{} : Bool}) -> {agrees(V, collapse_lo(V, p, x, hi), r, s) == True{} : Bool}:
  match x:
    case MTip{}:
      ehi
    case MLeaf{+a, +v}:
      and_t(agrees(V, MLeaf{a, v}, r, s), agrees(V, hi, r, s), ex, ehi)
    case MNode{+q, +a, +b2}:
      and_t(agrees(V, MNode{q, a, b2}, r, s), agrees(V, hi, r, s), ex, ehi)

def agrees_del.node(-V: Data, +p: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +k: String, +r: String, +s: Nat, +e: {agrees(V, MNode{p, lo, hi}, r, s) == True{} : Bool}, c: Bool, +ec: {bv(k, p) == c : Bool}, ilo: {agrees(V, cdel(V, lo, k), r, s) == True{} : Bool}, ihi: {agrees(V, cdel(V, hi, k), r, s) == True{} : Bool}) -> {agrees(V, Bool.pick(Map<&2, V>, bv(k, p), collapse_hi(V, p, lo, cdel(V, hi, k)), collapse_lo(V, p, cdel(V, lo, k), hi)), r, s) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, bv(k, p), True{}, ec) : {agrees(V, Bool.pick(Map<&2, V>, _, collapse_hi(V, p, lo, cdel(V, hi, k)), collapse_lo(V, p, cdel(V, lo, k), hi)), r, s) == True{} : Bool}
      agrees_del.hi(V, p, lo, cdel(V, hi, k), r, s, and_l(agrees(V, lo, r, s), agrees(V, hi, r, s), e), ihi)
    case False{}:
      %Equal.sym(Bool, bv(k, p), False{}, ec) : {agrees(V, Bool.pick(Map<&2, V>, _, collapse_hi(V, p, lo, cdel(V, hi, k)), collapse_lo(V, p, cdel(V, lo, k), hi)), r, s) == True{} : Bool}
      agrees_del.lo(V, p, cdel(V, lo, k), hi, r, s, ilo, and_r(agrees(V, lo, r, s), agrees(V, hi, r, s), e))

# Taking a key away keeps what `agrees` says of every key.
def agrees_del(-V: Data, m: Map<&2, V>, +k: String, +r: String, +s: Nat, +e: {agrees(V, m, r, s) == True{} : Bool}) -> {agrees(V, cdel(V, m, k), r, s) == True{} : Bool}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k1, +v}:
      agrees_del.leaf(V, k, k1, v, r, s, e, String.eq(k, k1), {==})
    case MNode{+p, +lo, +hi}:
      agrees_del.node(V, p, lo, hi, k, r, s, e, bv(k, p), {==}, agrees_del(V, lo, k, r, s, and_l(agrees(V, lo, r, s), agrees(V, hi, r, s), e)), agrees_del(V, hi, k, r, s, and_r(agrees(V, lo, r, s), agrees(V, hi, r, s), e)))

def wf_del.leaf(-V: Data, +k: String, +k1: String, +v: V, c: Bool, +ec: {String.eq(k, k1) == c : Bool}) -> {wft(V, Bool.pick(Map<&2, V>, String.eq(k, k1), MTip{}, MLeaf{k1, v})) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, String.eq(k, k1), True{}, ec) : {wft(V, Bool.pick(Map<&2, V>, _, MTip{}, MLeaf{k1, v})) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, String.eq(k, k1), False{}, ec) : {wft(V, Bool.pick(Map<&2, V>, _, MTip{}, MLeaf{k1, v})) == True{} : Bool}
      {==}

def wf_del.hi(-V: Data, +p: Nat, +lo: Map<&2, V>, x: Map<&2, V>, +wlo: {wf(V, lo) == True{} : Bool}, +slo: {sides(V, lo, p, False{}) == True{} : Bool}, +alo: {agrees(V, lo, rep(V, lo), p) == True{} : Bool}, wx: {wft(V, x) == True{} : Bool}, +sx: {sides(V, x, p, True{}) == True{} : Bool}, +ax: {agrees(V, x, rep(V, lo), p) == True{} : Bool}) -> {wft(V, collapse_hi(V, p, lo, x)) == True{} : Bool}:
  match x:
    case MTip{}:
      wft_of(V, lo, wlo)
    case MLeaf{+a, +v}:
      and_t(wf(V, lo), Bool.and(True{}, Bool.and(sides(V, lo, p, False{}), Bool.and(sides(V, MLeaf{a, v}, p, True{}), agrees(V, MNode{p, lo, MLeaf{a, v}}, rep(V, lo), p)))), wlo, and_t(True{}, Bool.and(sides(V, lo, p, False{}), Bool.and(sides(V, MLeaf{a, v}, p, True{}), agrees(V, MNode{p, lo, MLeaf{a, v}}, rep(V, lo), p))), {==}, and_t(sides(V, lo, p, False{}), Bool.and(sides(V, MLeaf{a, v}, p, True{}), agrees(V, MNode{p, lo, MLeaf{a, v}}, rep(V, lo), p)), slo, and_t(sides(V, MLeaf{a, v}, p, True{}), agrees(V, MNode{p, lo, MLeaf{a, v}}, rep(V, lo), p), sx, and_t(agrees(V, lo, rep(V, lo), p), agrees(V, MLeaf{a, v}, rep(V, lo), p), alo, ax)))))
    case MNode{+q, +a, +b}:
      and_t(wf(V, lo), Bool.and(wf(V, MNode{q, a, b}), Bool.and(sides(V, lo, p, False{}), Bool.and(sides(V, MNode{q, a, b}, p, True{}), agrees(V, MNode{p, lo, MNode{q, a, b}}, rep(V, lo), p)))), wlo, and_t(wf(V, MNode{q, a, b}), Bool.and(sides(V, lo, p, False{}), Bool.and(sides(V, MNode{q, a, b}, p, True{}), agrees(V, MNode{p, lo, MNode{q, a, b}}, rep(V, lo), p))), wx, and_t(sides(V, lo, p, False{}), Bool.and(sides(V, MNode{q, a, b}, p, True{}), agrees(V, MNode{p, lo, MNode{q, a, b}}, rep(V, lo), p)), slo, and_t(sides(V, MNode{q, a, b}, p, True{}), agrees(V, MNode{p, lo, MNode{q, a, b}}, rep(V, lo), p), sx, and_t(agrees(V, lo, rep(V, lo), p), agrees(V, MNode{q, a, b}, rep(V, lo), p), alo, ax)))))

def wf_del.lo(-V: Data, +p: Nat, x: Map<&2, V>, +hi: Map<&2, V>, +r: String, +wx: {wft(V, x) == True{} : Bool}, +sx: {sides(V, x, p, False{}) == True{} : Bool}, +ax: {agrees(V, x, r, p) == True{} : Bool}, +whi: {wf(V, hi) == True{} : Bool}, +shi: {sides(V, hi, p, True{}) == True{} : Bool}, +ahi: {agrees(V, hi, r, p) == True{} : Bool}) -> {wft(V, collapse_lo(V, p, x, hi)) == True{} : Bool}:
  match x:
    case MTip{}:
      wft_of(V, hi, whi)
    case MLeaf{+a, +v}:
      +ag = agrees_switch(V, MNode{p, MLeaf{a, v}, hi}, r, a, p, and_t(agrees(V, MLeaf{a, v}, r, p), agrees(V, hi, r, p), ax, ahi), Equal.trans(Bool, Bool.or(String.eq(a, a), mem(V, hi, a)), Bool.or(True{}, mem(V, hi, a)), True{}, Equal.cong(Bool, Bool, z => Bool.or(z, mem(V, hi, a)), String.eq(a, a), True{}, Str.eq_refl(a)), {==}))
      and_t(True{}, Bool.and(wf(V, hi), Bool.and(sides(V, MLeaf{a, v}, p, False{}), Bool.and(sides(V, hi, p, True{}), agrees(V, MNode{p, MLeaf{a, v}, hi}, a, p)))), {==}, and_t(wf(V, hi), Bool.and(sides(V, MLeaf{a, v}, p, False{}), Bool.and(sides(V, hi, p, True{}), agrees(V, MNode{p, MLeaf{a, v}, hi}, a, p))), whi, and_t(sides(V, MLeaf{a, v}, p, False{}), Bool.and(sides(V, hi, p, True{}), agrees(V, MNode{p, MLeaf{a, v}, hi}, a, p)), sx, and_t(sides(V, hi, p, True{}), agrees(V, MNode{p, MLeaf{a, v}, hi}, a, p), shi, ag))))
    case MNode{+q, +a, +b}:
      +ra = rep(V, a)
      +ag = agrees_switch(V, MNode{p, MNode{q, a, b}, hi}, r, ra, p, and_t(agrees(V, MNode{q, a, b}, r, p), agrees(V, hi, r, p), ax, ahi), Equal.trans(Bool, Bool.or(mem(V, MNode{q, a, b}, ra), mem(V, hi, ra)), Bool.or(True{}, mem(V, hi, ra)), True{}, Equal.cong(Bool, Bool, z => Bool.or(z, mem(V, hi, ra)), mem(V, MNode{q, a, b}, ra), True{}, rep_mem(V, MNode{q, a, b}, wx)), {==}))
      and_t(wf(V, MNode{q, a, b}), Bool.and(wf(V, hi), Bool.and(sides(V, MNode{q, a, b}, p, False{}), Bool.and(sides(V, hi, p, True{}), agrees(V, MNode{p, MNode{q, a, b}, hi}, ra, p)))), wx, and_t(wf(V, hi), Bool.and(sides(V, MNode{q, a, b}, p, False{}), Bool.and(sides(V, hi, p, True{}), agrees(V, MNode{p, MNode{q, a, b}, hi}, ra, p))), whi, and_t(sides(V, MNode{q, a, b}, p, False{}), Bool.and(sides(V, hi, p, True{}), agrees(V, MNode{p, MNode{q, a, b}, hi}, ra, p)), sx, and_t(sides(V, hi, p, True{}), agrees(V, MNode{p, MNode{q, a, b}, hi}, ra, p), shi, ag))))

def wf_del.node(-V: Data, +p: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>, +w: {wf(V, MNode{p, lo, hi}) == True{} : Bool}, +k: String, c: Bool, +ec: {bv(k, p) == c : Bool}, ilo: {wft(V, cdel(V, lo, k)) == True{} : Bool}, ihi: {wft(V, cdel(V, hi, k)) == True{} : Bool}) -> {wft(V, Bool.pick(Map<&2, V>, bv(k, p), collapse_hi(V, p, lo, cdel(V, hi, k)), collapse_lo(V, p, cdel(V, lo, k), hi))) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, bv(k, p), True{}, ec) : {wft(V, Bool.pick(Map<&2, V>, _, collapse_hi(V, p, lo, cdel(V, hi, k)), collapse_lo(V, p, cdel(V, lo, k), hi))) == True{} : Bool}
      +r = rep(V, lo)
      +near = wf_near(V, p, lo, hi, w)
      wf_del.hi(V, p, lo, cdel(V, hi, k), wf_lo(V, p, lo, hi, w), wf_slo(V, p, lo, hi, w), and_l(agrees(V, lo, r, p), agrees(V, hi, r, p), near), ihi, sides_del(V, hi, k, p, True{}, wf_shi(V, p, lo, hi, w)), agrees_del(V, hi, k, r, p, and_r(agrees(V, lo, r, p), agrees(V, hi, r, p), near)))
    case False{}:
      %Equal.sym(Bool, bv(k, p), False{}, ec) : {wft(V, Bool.pick(Map<&2, V>, _, collapse_hi(V, p, lo, cdel(V, hi, k)), collapse_lo(V, p, cdel(V, lo, k), hi))) == True{} : Bool}
      +r = rep(V, lo)
      +near = wf_near(V, p, lo, hi, w)
      wf_del.lo(V, p, cdel(V, lo, k), hi, r, ilo, sides_del(V, lo, k, p, False{}, wf_slo(V, p, lo, hi, w)), agrees_del(V, lo, k, r, p, and_l(agrees(V, lo, r, p), agrees(V, hi, r, p), near)), wf_hi(V, p, lo, hi, w), wf_shi(V, p, lo, hi, w), and_r(agrees(V, lo, r, p), agrees(V, hi, r, p), near))

# Taking a key away from a trie leaves a map `Map.new` and `Map.set` could
# have built.
def wf_del(-V: Data, m: Map<&2, V>, +w: {wf(V, m) == True{} : Bool}, +k: String) -> {wft(V, cdel(V, m, k)) == True{} : Bool}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k1, +v}:
      wf_del.leaf(V, k, k1, v, String.eq(k, k1), {==})
    case MNode{+p, +lo, +hi}:
      wf_del.node(V, p, lo, hi, w, k, bv(k, p), {==}, wf_del(V, lo, wf_lo(V, p, lo, hi, w), k), wf_del(V, hi, wf_hi(V, p, lo, hi, w), k))

# `Map.del`, `Map.pop` and `Set.del`, as a caller asks
# ----------------------------------------------------

def wf_of_top(-V: Data, m: Map<&2, V>, +w: Wf.top(V, m), +k: String) -> {wft(V, cdel(V, m, k)) == True{} : Bool}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k1, +v}:
      wf_del(V, MLeaf{k1, v}, {==}, k)
    case MNode{+p, +lo, +hi}:
      wf_del(V, MNode{p, lo, hi}, w, k)

def wf_del_map(-V: Data, +m: Map<&2, V>, +w: Wf.top(V, m), +k: String) -> Wf.top(V, Map.del(&2, V, m, k)):
  %Equal.sym(Map<&2, V>, Map.del(&2, V, m, k), cdel(V, m, k), del_is(V, m, k)) : {wft(V, _) == True{} : Bool}
  wf_of_top(V, m, w, k)

def del_same_top(-V: Data, m: Map<&2, V>, +w: Wf.top(V, m), +k: String) -> {found(V, cdel(V, m, k), k) == None{} : Maybe<&2, V>}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k1, +v}:
      del_same(V, MLeaf{k1, v}, {==}, k)
    case MNode{+p, +lo, +hi}:
      del_same(V, MNode{p, lo, hi}, w, k)

def del_other_top(-V: Data, m: Map<&2, V>, +w: Wf.top(V, m), +k: String, +j: String, +ejk: {String.eq(j, k) == False{} : Bool}) -> {found(V, cdel(V, m, k), j) == found(V, m, j) : Maybe<&2, V>}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k1, +v}:
      del_other(V, MLeaf{k1, v}, {==}, k, j, ejk)
    case MNode{+p, +lo, +hi}:
      del_other(V, MNode{p, lo, hi}, w, k, j, ejk)

# After `Map.del` the key finds nothing, and every other key what it did.
def get_del_same(-V: Data, +d: V, +m: Map<&2, V>, +w: Wf.top(V, m), +k: String) -> {gv(V, Map.get(V, d, Map.del(&2, V, m, k), k)) == d : V}:
  %Equal.sym(V, gv(V, Map.get(V, d, Map.del(&2, V, m, k), k)), Maybe.default(&2, V, found(V, Map.del(&2, V, m, k), k), d), get_is(V, d, Map.del(&2, V, m, k), k)) : {_ == d : V}
  %Equal.sym(Map<&2, V>, Map.del(&2, V, m, k), cdel(V, m, k), del_is(V, m, k)) : {Maybe.default(&2, V, found(V, _, k), d) == d : V}
  %Equal.sym(Maybe<&2, V>, found(V, cdel(V, m, k), k), None{}, del_same_top(V, m, w, k)) : {Maybe.default(&2, V, _, d) == d : V}
  {==}

def has_del_same(-V: Data, +m: Map<&2, V>, +w: Wf.top(V, m), +k: String) -> {hv(V, Map.has(&2, V, Map.del(&2, V, m, k), k)) == False{} : Bool}:
  %Equal.sym(Bool, hv(V, Map.has(&2, V, Map.del(&2, V, m, k), k)), Maybe.is_some(&2, V, found(V, Map.del(&2, V, m, k), k)), has_is(V, Map.del(&2, V, m, k), k)) : {_ == False{} : Bool}
  %Equal.sym(Map<&2, V>, Map.del(&2, V, m, k), cdel(V, m, k), del_is(V, m, k)) : {Maybe.is_some(&2, V, found(V, _, k)) == False{} : Bool}
  %Equal.sym(Maybe<&2, V>, found(V, cdel(V, m, k), k), None{}, del_same_top(V, m, w, k)) : {Maybe.is_some(&2, V, _) == False{} : Bool}
  {==}

def get_del_other(-V: Data, +d: V, +m: Map<&2, V>, +w: Wf.top(V, m), +k: String, +j: String, ejk: {String.eq(j, k) == False{} : Bool}) -> {gv(V, Map.get(V, d, Map.del(&2, V, m, k), j)) == gv(V, Map.get(V, d, m, j)) : V}:
  %Equal.sym(V, gv(V, Map.get(V, d, Map.del(&2, V, m, k), j)), Maybe.default(&2, V, found(V, Map.del(&2, V, m, k), j), d), get_is(V, d, Map.del(&2, V, m, k), j)) : {_ == gv(V, Map.get(V, d, m, j)) : V}
  %Equal.sym(V, gv(V, Map.get(V, d, m, j)), Maybe.default(&2, V, found(V, m, j), d), get_is(V, d, m, j)) : {Maybe.default(&2, V, found(V, Map.del(&2, V, m, k), j), d) == _ : V}
  %Equal.sym(Map<&2, V>, Map.del(&2, V, m, k), cdel(V, m, k), del_is(V, m, k)) : {Maybe.default(&2, V, found(V, _, j), d) == Maybe.default(&2, V, found(V, m, j), d) : V}
  %Equal.sym(Maybe<&2, V>, found(V, cdel(V, m, k), j), found(V, m, j), del_other_top(V, m, w, k, j, ejk)) : {Maybe.default(&2, V, _, d) == Maybe.default(&2, V, found(V, m, j), d) : V}
  {==}

def has_del_other(-V: Data, +m: Map<&2, V>, +w: Wf.top(V, m), +k: String, +j: String, ejk: {String.eq(j, k) == False{} : Bool}) -> {hv(V, Map.has(&2, V, Map.del(&2, V, m, k), j)) == hv(V, Map.has(&2, V, m, j)) : Bool}:
  %Equal.sym(Bool, hv(V, Map.has(&2, V, Map.del(&2, V, m, k), j)), Maybe.is_some(&2, V, found(V, Map.del(&2, V, m, k), j)), has_is(V, Map.del(&2, V, m, k), j)) : {_ == hv(V, Map.has(&2, V, m, j)) : Bool}
  %Equal.sym(Bool, hv(V, Map.has(&2, V, m, j)), Maybe.is_some(&2, V, found(V, m, j)), has_is(V, m, j)) : {Maybe.is_some(&2, V, found(V, Map.del(&2, V, m, k), j)) == _ : Bool}
  %Equal.sym(Map<&2, V>, Map.del(&2, V, m, k), cdel(V, m, k), del_is(V, m, k)) : {Maybe.is_some(&2, V, found(V, _, j)) == Maybe.is_some(&2, V, found(V, m, j)) : Bool}
  %Equal.sym(Maybe<&2, V>, found(V, cdel(V, m, k), j), found(V, m, j), del_other_top(V, m, w, k, j, ejk)) : {Maybe.is_some(&2, V, _) == Maybe.is_some(&2, V, found(V, m, j)) : Bool}
  {==}

# What `Map.pop` hands back beside the map is what `Map.get` finds, and the
# map it hands back is `Map.del`'s.
def pop_get(-V: Data, +d: V, +m: Map<&2, V>, +k: String) -> {Maybe.default(&2, V, pv(V, Map.pop(&2, V, m, k)), d) == gv(V, Map.get(V, d, m, k)) : V}:
  %Equal.sym(Maybe<&2, V>, pv(V, Map.pop(&2, V, m, k)), found(V, m, k), pop_found(V, m, k)) : {Maybe.default(&2, V, _, d) == gv(V, Map.get(V, d, m, k)) : V}
  Equal.sym(V, gv(V, Map.get(V, d, m, k)), Maybe.default(&2, V, found(V, m, k), d), get_is(V, d, m, k))

def pm(-V: Data, r: Map<&2, V> & Maybe<&2, V>) -> Map<&2, V>:
  (m, x) = r
  m

def pop_map(-V: Data, +m: Map<&2, V>, +k: String) -> {pm(V, Map.pop(&2, V, m, k)) == Map.del(&2, V, m, k) : Map<&2, V>}:
  %Equal.sym(Map<&2, V> & Maybe<&2, V>, Map.pop(&2, V, m, k), (cdel(V, m, k), found(V, m, k)), pop_is(V, m, k)) : {pm(V, _) == Map.del.fin(&2, V, _) : Map<&2, V>}
  {==}

def set_del_same(+s: Set(), +w: Wf.top(Unit, s), +k: String) -> {hv(Unit, Set.has(Set.del(s, k), k)) == False{} : Bool}:
  has_del_same(Unit, s, w, k)

def set_del_other(+s: Set(), +w: Wf.top(Unit, s), +k: String, +j: String, ejk: {String.eq(j, k) == False{} : Bool}) -> {hv(Unit, Set.has(Set.del(s, k), j)) == hv(Unit, Set.has(s, j)) : Bool}:
  has_del_other(Unit, s, w, k, j, ejk)

def set_wf_del(+s: Set(), +w: Wf.top(Unit, s), +k: String) -> Wf.top(Unit, Set.del(s, k)):
  wf_del_map(Unit, s, w, k)

def main() -> IO(Unit):
  IO.print("ok")
