# The comparison the Rust tool draws: `similar`'s Histogram diff, as
# `historica::diff` calls it — `capture_diff_slices(Algorithm::Histogram, ..)`,
# which is the algorithm behind a `Compact` pass and a `Replace` hook. This is
# that pipeline, step for step, over similar 3.2.0: the preflight that answers
# a nearly disjoint pair with one replacement, the Histogram search for a rare
# anchor, the Myers search it falls back to where every shared line is common
# (with Myers' own preflight, its heuristics and its exact small-side search),
# and the compaction that slides each run of changes to where it groups.
#
# `Ops.diff` is a longest common subsequence, and is what the proofs in
# `diff_lemmas.bend` are about; it agrees with this wherever a change has one
# alignment. Where a change has two, this is the one the Rust tool picked, so
# what `diff` and `blame` print over the folder and across `--onto` is what it
# prints.
#
# Items are compared as the Rust `Item` compares them — text, terminator, and
# whether the text was forgotten — and are numbered first, so everything below
# compares numbers. Sequences are read by index through `UMap`, a trie over the
# index's bits, which is `Data` and so can be read from anywhere without being
# threaded; Rust's vectors are indexed in place, and this is the persistent
# stand-in for them.

import Base
import ./ops.bend as Ops
import ./utf8.bend as Utf8

# Numbers
# -------

# The bias that lets a `U32` hold a signed number: `k` is stored as `k + B`,
# and sums and negations of biased numbers wrap back into place.
def B() -> U32:
  2147483648

def span(+lo: U32, +hi: U32) -> U32:
  Bool.pick(U32, U32.is_lt(lo, hi), (hi - lo : U32), 0)

def sat_sub(+a: U32, +b: U32) -> U32:
  Bool.pick(U32, U32.is_ge(a, b), (a - b : U32), 0)

def babs(+x: U32) -> U32:
  Bool.pick(U32, U32.is_ge(x, B()), (x - B() : U32), (B() - x : U32))

def isqrt.go(fuel: Nat, +x: U32, +r: U32, +bit: U32) -> U32:
  match fuel:
    case 0n:
      r
    case 1n+q:
      +t = (r + bit : U32)
      isqrt.go(q, x, Bool.pick(U32, U32.is_le((t * t : U32), x), t, r), U32.shr(bit))

def isqrt(+x: U32) -> U32:
  isqrt.go(16n, x, 0, 32768)

def clamp(+x: U32, +lo: U32, +hi: U32) -> U32:
  U32.min(U32.max(x, lo), hi)

def odd(+k: U32) -> Bool:
  U32.is_eq(U32.and(k, 1), 1)

# Tables
# ------

# A table from numbers to numbers: a trie over the key's bits, low bit first.
type UMap is Data:
  UNone{}
  UNode{here: U32, has: Bool, e: UMap, o: UMap}

def umap.get(fuel: Nat, m: UMap, +k: U32, d: U32, z: Bool, bit: Bool) -> U32:
  match fuel m z bit:
    case 0n _ _ _:
      d
    case 1n+f UNone{} _ _:
      d
    case 1n+f UNode{here, has, e, o} True{} _:
      Bool.pick(U32, has, here, d)
    case 1n+f UNode{here, has, e, o} False{} False{}:
      +k2 = U32.shr(k)
      umap.get(f, e, k2, d, U32.is_eq(k2, 0), odd(k2))
    case 1n+f UNode{here, has, e, o} False{} True{}:
      +k2 = U32.shr(k)
      umap.get(f, o, k2, d, U32.is_eq(k2, 0), odd(k2))

def umap.set(fuel: Nat, m: UMap, +k: U32, v: U32, z: Bool, bit: Bool) -> UMap:
  match fuel m z bit:
    case 0n _ _ _:
      UNone{}
    case 1n+f UNone{} True{} _:
      UNode{v, True{}, UNone{}, UNone{}}
    case 1n+f UNone{} False{} False{}:
      +k2 = U32.shr(k)
      UNode{0, False{}, umap.set(f, UNone{}, k2, v, U32.is_eq(k2, 0), odd(k2)), UNone{}}
    case 1n+f UNone{} False{} True{}:
      +k2 = U32.shr(k)
      UNode{0, False{}, UNone{}, umap.set(f, UNone{}, k2, v, U32.is_eq(k2, 0), odd(k2))}
    case 1n+f UNode{here, has, e, o} True{} _:
      UNode{v, True{}, e, o}
    case 1n+f UNode{here, has, e, o} False{} False{}:
      +k2 = U32.shr(k)
      UNode{here, has, umap.set(f, e, k2, v, U32.is_eq(k2, 0), odd(k2)), o}
    case 1n+f UNode{here, has, e, o} False{} True{}:
      +k2 = U32.shr(k)
      UNode{here, has, e, umap.set(f, o, k2, v, U32.is_eq(k2, 0), odd(k2))}

def at_or(m: UMap, +k: U32, d: U32) -> U32:
  umap.get(34n, m, k, d, U32.is_eq(k, 0), odd(k))

def at(m: UMap, +k: U32) -> U32:
  at_or(m, k, 0)

def put(m: UMap, +k: U32, v: U32) -> UMap:
  umap.set(34n, m, k, v, U32.is_eq(k, 0), odd(k))

# Where each value stands in a range, in order, and how often.
type Bucket is Data:
  Bucket{places: List<&2, U32>, count: U32}

type PMap is Data:
  PNone{}
  PNode{here: List<&2, U32>, count: U32, e: PMap, o: PMap}

def pmap.get(fuel: Nat, m: PMap, +k: U32, z: Bool, bit: Bool) -> Bucket:
  match fuel m z bit:
    case 0n _ _ _:
      Bucket{Nil{}, 0}
    case 1n+f PNone{} _ _:
      Bucket{Nil{}, 0}
    case 1n+f PNode{here, count, e, o} True{} _:
      Bucket{here, count}
    case 1n+f PNode{here, count, e, o} False{} False{}:
      +k2 = U32.shr(k)
      pmap.get(f, e, k2, U32.is_eq(k2, 0), odd(k2))
    case 1n+f PNode{here, count, e, o} False{} True{}:
      +k2 = U32.shr(k)
      pmap.get(f, o, k2, U32.is_eq(k2, 0), odd(k2))

# Put `i` in front of what `k` holds.
def pmap.push(fuel: Nat, m: PMap, +k: U32, i: U32, z: Bool, bit: Bool) -> PMap:
  match fuel m z bit:
    case 0n _ _ _:
      PNone{}
    case 1n+f PNone{} True{} _:
      PNode{[i], 1, PNone{}, PNone{}}
    case 1n+f PNone{} False{} False{}:
      +k2 = U32.shr(k)
      PNode{Nil{}, 0, pmap.push(f, PNone{}, k2, i, U32.is_eq(k2, 0), odd(k2)), PNone{}}
    case 1n+f PNone{} False{} True{}:
      +k2 = U32.shr(k)
      PNode{Nil{}, 0, PNone{}, pmap.push(f, PNone{}, k2, i, U32.is_eq(k2, 0), odd(k2))}
    case 1n+f PNode{here, count, e, o} True{} _:
      PNode{i <> here, (count + 1 : U32), e, o}
    case 1n+f PNode{here, count, e, o} False{} False{}:
      +k2 = U32.shr(k)
      PNode{here, count, pmap.push(f, e, k2, i, U32.is_eq(k2, 0), odd(k2)), o}
    case 1n+f PNode{here, count, e, o} False{} True{}:
      +k2 = U32.shr(k)
      PNode{here, count, e, pmap.push(f, o, k2, i, U32.is_eq(k2, 0), odd(k2))}

def bucket(m: PMap, +k: U32) -> Bucket:
  pmap.get(34n, m, k, U32.is_eq(k, 0), odd(k))

def push(m: PMap, +k: U32, i: U32) -> PMap:
  pmap.push(34n, m, k, i, U32.is_eq(k, 0), odd(k))

def bucket.count(b: Bucket) -> U32:
  match b:
    case Bucket{places, count}:
      count

def bucket.places(b: Bucket) -> List<&2, U32>:
  match b:
    case Bucket{places, count}:
      places

# The two sides
# -------------

type Seqs is Data:
  Seqs{old: UMap, new: UMap}

def old_at(s: Seqs, +i: U32) -> U32:
  match s:
    case Seqs{old, new}:
      at(old, i)

def new_at(s: Seqs, +j: U32) -> U32:
  match s:
    case Seqs{old, new}:
      at(new, j)

def same_at(+s: Seqs, +i: U32, +j: U32) -> Bool:
  U32.is_eq(old_at(s, i), new_at(s, j))

def pre.go(fuel: Nat, +s: Seqs, +o: U32, +n: U32, acc: U32, same: Bool) -> U32:
  match fuel same:
    case 0n _:
      acc
    case 1n+f False{}:
      acc
    case 1n+f True{}:
      +o2 = (o + 1 : U32)
      +n2 = (n + 1 : U32)
      pre.go(f, s, o2, n2, (acc + 1 : U32), same_at(s, o2, n2))

# How many items the two ranges share at their start.
def pre(+s: Seqs, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32) -> U32:
  pre.go(U32.to_nat(U32.min(span(olo, ohi), span(nlo, nhi))), s, olo, nlo, 0, same_at(s, olo, nlo))

def suf.go(fuel: Nat, +s: Seqs, +o: U32, +n: U32, acc: U32, same: Bool) -> U32:
  match fuel same:
    case 0n _:
      acc
    case 1n+f False{}:
      acc
    case 1n+f True{}:
      +o2 = (o - 1 : U32)
      +n2 = (n - 1 : U32)
      suf.go(f, s, o2, n2, (acc + 1 : U32), same_at(s, o2, n2))

# How many they share at their end.
def suf(+s: Seqs, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32) -> U32:
  +o = (ohi - 1 : U32)
  +n = (nhi - 1 : U32)
  suf.go(U32.to_nat(U32.min(span(olo, ohi), span(nlo, nhi))), s, o, n, 0, same_at(s, o, n))

# Operations
# ----------

# What the hooks are told: a run both sides share, a run only the old side
# has, and a run only the new side has, each with where it stands on both.
type Op is Data:
  Same{o: U32, n: U32, len: U32}
  Lose{o: U32, len: U32, n: U32}
  Gain{o: U32, n: U32, len: U32}

def op.len(op: Op) -> U32:
  match op:
    case Same{o, n, len}:
      len
    case Lose{o, len, n}:
      len
    case Gain{o, n, len}:
      len

def op.o(op: Op) -> U32:
  match op:
    case Same{o, n, len}:
      o
    case Lose{o, len, n}:
      o
    case Gain{o, n, len}:
      o

def op.n(op: Op) -> U32:
  match op:
    case Same{o, n, len}:
      n
    case Lose{o, len, n}:
      n
    case Gain{o, n, len}:
      n

# Where an operation ends on each side.
def op.o_end(op: Op) -> U32:
  match op:
    case Same{o, n, len}:
      (o + len : U32)
    case Lose{o, len, n}:
      (o + len : U32)
    case Gain{o, n, len}:
      o

def op.n_end(op: Op) -> U32:
  match op:
    case Same{o, n, len}:
      (n + len : U32)
    case Lose{o, len, n}:
      n
    case Gain{o, n, len}:
      (n + len : U32)

# 0, 1 and 2 for a shared run, a loss and a gain.
def op.tag(op: Op) -> U32:
  match op:
    case Same{o, n, len}:
      0
    case Lose{o, len, n}:
      1
    case Gain{o, n, len}:
      2

# `DiffOp::adjust`: the indices move by `di` and the length by `dl`, each
# down where its flag says so.
def op.adjust(op: Op, +down_i: Bool, +di: U32, +down_l: Bool, +dl: U32) -> Op:
  match op:
    case Same{+o, +n, +len}:
      Same{Bool.pick(U32, down_i, (o - di : U32), (o + di : U32)),
           Bool.pick(U32, down_i, (n - di : U32), (n + di : U32)),
           Bool.pick(U32, down_l, (len - dl : U32), (len + dl : U32))}
    case Lose{+o, +len, +n}:
      Lose{Bool.pick(U32, down_i, (o - di : U32), (o + di : U32)),
           Bool.pick(U32, down_l, (len - dl : U32), (len + dl : U32)),
           Bool.pick(U32, down_i, (n - di : U32), (n + di : U32))}
    case Gain{+o, +n, +len}:
      Gain{Bool.pick(U32, down_i, (o - di : U32), (o + di : U32)),
           Bool.pick(U32, down_i, (n - di : U32), (n + di : U32)),
           Bool.pick(U32, down_l, (len - dl : U32), (len + dl : U32))}

def op.shift_left(op: Op, +a: U32) -> Op:
  op.adjust(op, True{}, a, False{}, 0)

def op.shift_right(op: Op, +a: U32) -> Op:
  op.adjust(op, False{}, a, False{}, 0)

def op.grow_left(op: Op, +a: U32) -> Op:
  op.adjust(op, True{}, a, False{}, a)

def op.grow_right(op: Op, +a: U32) -> Op:
  op.adjust(op, False{}, 0, False{}, a)

def op.shrink_left(op: Op, +a: U32) -> Op:
  op.adjust(op, False{}, 0, True{}, a)

def op.shrink_right(op: Op, +a: U32) -> Op:
  op.adjust(op, False{}, a, True{}, a)

# The same operation standing elsewhere: a loss at another new index, a gain
# at another old one.
def op.with_n(op: Op, +at: U32) -> Op:
  match op:
    case Same{o, n, len}:
      Same{o, n, len}
    case Lose{o, len, n}:
      Lose{o, len, at}
    case Gain{o, n, len}:
      Gain{o, n, len}

def op.with_o(op: Op, +at: U32) -> Op:
  match op:
    case Same{o, n, len}:
      Same{o, n, len}
    case Lose{o, len, n}:
      Lose{o, len, n}
    case Gain{o, n, len}:
      Gain{at, n, len}

# Emitted in reverse, as every walk below collects them.
def same_if(+o: U32, +n: U32, +len: U32, +acc: List<&2, Op>) -> List<&2, Op>:
  Bool.pick(List<&2, Op>, U32.is_gt(len, 0), Same{o, n, len} <> acc, acc)

def lose_if(+o: U32, +len: U32, +n: U32, +acc: List<&2, Op>) -> List<&2, Op>:
  Bool.pick(List<&2, Op>, U32.is_gt(len, 0), Lose{o, len, n} <> acc, acc)

def gain_if(+o: U32, +n: U32, +len: U32, +acc: List<&2, Op>) -> List<&2, Op>:
  Bool.pick(List<&2, Op>, U32.is_gt(len, 0), Gain{o, n, len} <> acc, acc)

# Myers
# -----

# `similar`'s Myers is a middle-snake bisection with three additions over
# the textbook one: a peel of a long shared run past a short one-sided shift
# (`try_emit_front_anchor`), an exact table search where one side is at most
# 64 items and the other at least 512 (`maybe_emit_small_side_exact`), and a
# cost cap past which the bisection splits at the best diagonal it has seen
# rather than the one that is provably shortest. A split that is exact
# searches both halves exactly; a heuristic one searches the half it has not
# explored with heuristics again.

# A split the heuristics would take: where, how far it got, and from which
# end.
type Split is Data:
  Split{o: U32, n: U32, progress: U32, forward: Bool}

# Where to bisect, and whether each half is searched with heuristics.
type Cut is Data:
  Cut{o: U32, n: U32, left: Bool, right: Bool}

def better.of(+bo: U32, +bn: U32, +bp: U32, +bf: Bool, cand: Split) -> Maybe<&2, Split>:
  match cand:
    case Split{+co, +cn, +cp, +cf}:
      Bool.pick(Maybe<&2, Split>, U32.is_gt(cp, bp), Some{Split{co, cn, cp, cf}}, Some{Split{bo, bn, bp, bf}})

def better(best: Maybe<&2, Split>, cand: Split) -> Maybe<&2, Split>:
  match best:
    case None{}:
      Some{cand}
    case Some{Split{bo, bn, bp, bf}}:
      better.of(bo, bn, bp, bf, cand)

def better.if(c: Bool, best: Maybe<&2, Split>, cand: Split) -> Maybe<&2, Split>:
  match c:
    case True{}:
      better(best, cand)
    case False{}:
      best

def interior(+o: U32, +n: U32, +bn: U32, +bm: U32) -> Bool:
  Bool.and(Bool.and(U32.is_le(o, bn), U32.is_le(n, bm)),
           Bool.and(Bool.or(U32.is_ne(o, 0), U32.is_ne(n, 0)), Bool.or(U32.is_ne(o, bn), U32.is_ne(n, bm))))

# `clamp_diagonal_point`: `x` on diagonal `k`, held inside the grid.
type Clamped is Data:
  Clamped{ok: Bool, o: U32, n: U32}

def clamp_diag(+x: U32, +kb: U32, +n: U32, +m: U32) -> Clamped:
  +neg = U32.is_lt(kb, B())
  +ka = babs(kb)
  +lo = Bool.pick(U32, neg, 0, ka)
  +hi = Bool.pick(U32, neg, U32.min(n, sat_sub(m, ka)), U32.min(n, (m + ka : U32)))
  +ox = clamp(x, lo, hi)
  Clamped{Bool.and(Bool.not(Bool.and(neg, U32.is_gt(ka, m))), U32.is_le(lo, hi)), ox, Bool.pick(U32, neg, (ox + ka : U32), (ox - ka : U32))}

def clamped.fwd_ok(c: Clamped, +n: U32, +m: U32) -> Bool:
  match c:
    case Clamped{ok, +o, +p}:
      Bool.and(ok, interior(o, p, n, m))

def clamped.fwd(c: Clamped) -> Split:
  match c:
    case Clamped{ok, +o, +p}:
      Split{o, p, (o + p : U32), True{}}

def clamped.bwd_ok(c: Clamped, +n: U32, +m: U32) -> Bool:
  match c:
    case Clamped{ok, +o, +p}:
      Bool.and(ok, interior((n - o : U32), (m - p : U32), n, m))

def clamped.bwd(c: Clamped, +n: U32, +m: U32) -> Split:
  match c:
    case Clamped{ok, +o, +p}:
      Split{(n - o : U32), (m - p : U32), (o + p : U32), False{}}

# What one search holds: the two sequences, the box, `delta` biased, its
# parity, whether heuristics are on, and the offset of the diagonal tables.
type Ctx is Data:
  Ctx{s: Seqs, olo: U32, ohi: U32, nlo: U32, nhi: U32, dl: U32, par: Bool, heur: Bool, dmax: U32}

def ctx.olo(c: Ctx) -> U32:
  match c:
    case Ctx{s, olo, ohi, nlo, nhi, dl, par, heur, dmax}:
      olo

def ctx.nlo(c: Ctx) -> U32:
  match c:
    case Ctx{s, olo, ohi, nlo, nhi, dl, par, heur, dmax}:
      nlo

def ctx.cap(c: Ctx, +d: U32) -> Bool:
  match c:
    case Ctx{s, +olo, +ohi, +nlo, +nhi, dl, par, heur, dmax}:
      Bool.and(heur, U32.is_ge(d, U32.max(isqrt((((ohi - olo : U32) + nhi : U32) - nlo : U32)), 256)))

# A diagonal's slot: `k` counted from `-dmax`.
def vkey(+kb: U32, +dmax: U32) -> U32:
  ((kb + B() : U32) + dmax : U32)

# One pass of the search: the diagonal table it writes, the best
# heuristic split from its own end, the best good split so far, and the
# exact split if it met the other pass.
type Pass is Data:
  Pass{v: UMap, split: Maybe<&2, Split>, good: Maybe<&2, Split>, found: Maybe<&2, Cut>}

def adv.fwd(+s: Seqs, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32, +x0: U32, +y0: U32, go: Bool) -> U32:
  match go:
    case True{}:
      pre(s, (olo + x0 : U32), ohi, (nlo + y0 : U32), nhi)
    case False{}:
      0

def adv.bwd(+s: Seqs, +olo: U32, +nlo: U32, +n: U32, +m: U32, +x0: U32, +y0: U32, go: Bool) -> U32:
  match go:
    case True{}:
      suf(s, olo, ((olo + n : U32) - x0 : U32), nlo, ((nlo + m : U32) - y0 : U32))
    case False{}:
      0

def fwd.at(+s: Seqs, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32, +dl: U32, +par: Bool, +heur: Bool, +dmax: U32, +d: U32, +kb: U32, +vb: UMap, st: Pass) -> Pass:
  match st:
    case Pass{+v, split, good, found}:
      +n = (ohi - olo : U32)
      +m = (nhi - nlo : U32)
      +lo = U32.is_eq(kb, (B() - d : U32))
      +hi = U32.is_eq(kb, (B() + d : U32))
      +a = at(v, vkey((kb - 1 : U32), dmax))
      +b = at(v, vkey((kb + 1 : U32), dmax))
      +x0 = Bool.pick(U32, Bool.or(lo, Bool.and(Bool.not(hi), U32.is_lt(a, b))), b, (a + 1 : U32))
      +y0 = ((x0 + B() : U32) - kb : U32)
      +x = (x0 + adv.fwd(s, olo, ohi, nlo, nhi, x0, y0, Bool.and(U32.is_lt(x0, n), U32.is_lt(y0, m))) : U32)
      +kd = ((kb + B() : U32) - dl : U32)
      +hit = Bool.and(par, Bool.and(U32.is_lt(babs(kd), d), U32.is_ge((x + at(vb, vkey((0 - kd : U32), dmax)) : U32), n)))
      +cl = clamp_diag(x, kb, n, m)
      +useful = sat_sub((x + y0 : U32), babs(kb))
      +goodish = Bool.and(Bool.and(U32.is_gt(d, 256), U32.is_ge((x - x0 : U32), 20)),
                          Bool.and(Bool.and(U32.is_lt(x, n), U32.is_lt(y0, m)),
                                   Bool.and(U32.is_gt(useful, (4 * d : U32)), interior(x0, y0, n, m))))
      Pass{put(v, vkey(kb, dmax), x),
           better.if(Bool.and(heur, clamped.fwd_ok(cl, n, m)), split, clamped.fwd(cl)),
           better.if(Bool.and(heur, goodish), good, Split{x0, y0, useful, True{}}),
           Bool.pick(Maybe<&2, Cut>, hit, Some{Cut{(x0 + olo : U32), (y0 + nlo : U32), False{}, False{}}}, found)}

def bwd.at(+s: Seqs, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32, +dl: U32, +par: Bool, +heur: Bool, +dmax: U32, +d: U32, +kb: U32, +vf: UMap, st: Pass) -> Pass:
  match st:
    case Pass{+v, split, good, found}:
      +n = (ohi - olo : U32)
      +m = (nhi - nlo : U32)
      +lo = U32.is_eq(kb, (B() - d : U32))
      +hi = U32.is_eq(kb, (B() + d : U32))
      +a = at(v, vkey((kb - 1 : U32), dmax))
      +b = at(v, vkey((kb + 1 : U32), dmax))
      +x0 = Bool.pick(U32, Bool.or(lo, Bool.and(Bool.not(hi), U32.is_lt(a, b))), b, (a + 1 : U32))
      +y0 = ((x0 + B() : U32) - kb : U32)
      +adv = adv.bwd(s, olo, nlo, n, m, x0, y0, Bool.and(U32.is_lt(x0, n), U32.is_lt(y0, m)))
      +x = (x0 + adv : U32)
      +y = (y0 + adv : U32)
      +kd = ((kb + B() : U32) - dl : U32)
      +hit = Bool.and(Bool.not(par), Bool.and(U32.is_le(babs(kd), d), U32.is_ge((x + at(vf, vkey((0 - kd : U32), dmax)) : U32), n)))
      +cl = clamp_diag(x, kb, n, m)
      +useful = sat_sub((x + y : U32), babs(kb))
      +goodish = Bool.and(Bool.and(U32.is_gt(d, 256), U32.is_ge(adv, 20)),
                          Bool.and(Bool.and(U32.is_lt(x, n), U32.is_lt(y, m)), U32.is_gt(useful, (4 * d : U32))))
      Pass{put(v, vkey(kb, dmax), x),
           better.if(Bool.and(heur, clamped.bwd_ok(cl, n, m)), split, clamped.bwd(cl, n, m)),
           better.if(Bool.and(heur, goodish), good, Split{(n - x : U32), (m - y : U32), useful, False{}}),
           Bool.pick(Maybe<&2, Cut>, hit, Some{Cut{((n - x : U32) + olo : U32), ((m - y : U32) + nlo : U32), False{}, False{}}}, found)}

def fwd.step(c: Ctx, +d: U32, +kb: U32, +vb: UMap, st: Pass) -> Pass:
  match c:
    case Ctx{s, olo, ohi, nlo, nhi, dl, par, heur, dmax}:
      fwd.at(s, olo, ohi, nlo, nhi, dl, par, heur, dmax, d, kb, vb, st)

def bwd.step(c: Ctx, +d: U32, +kb: U32, +vf: UMap, st: Pass) -> Pass:
  match c:
    case Ctx{s, olo, ohi, nlo, nhi, dl, par, heur, dmax}:
      bwd.at(s, olo, ohi, nlo, nhi, dl, par, heur, dmax, d, kb, vf, st)

# Diagonals `d` down to `-d`, two at a time, until one pass meets the other.
def fwd.go(fuel: Nat, st: Pass, +c: Ctx, +d: U32, +kb: U32, +vb: UMap) -> Pass:
  match fuel st:
    case 0n Pass{v, sp, g, None{}}:
      Pass{v, sp, g, None{}}
    case 0n Pass{v, sp, g, Some{cut}}:
      Pass{v, sp, g, Some{cut}}
    case 1n+q Pass{v, sp, g, Some{cut}}:
      Pass{v, sp, g, Some{cut}}
    case 1n+q Pass{v, sp, g, None{}}:
      fwd.go(q, fwd.step(c, d, kb, vb, Pass{v, sp, g, None{}}), c, d, (kb - 2 : U32), vb)

def bwd.go(fuel: Nat, st: Pass, +c: Ctx, +d: U32, +kb: U32, +vf: UMap) -> Pass:
  match fuel st:
    case 0n Pass{v, sp, g, None{}}:
      Pass{v, sp, g, None{}}
    case 0n Pass{v, sp, g, Some{cut}}:
      Pass{v, sp, g, Some{cut}}
    case 1n+q Pass{v, sp, g, Some{cut}}:
      Pass{v, sp, g, Some{cut}}
    case 1n+q Pass{v, sp, g, None{}}:
      bwd.go(q, bwd.step(c, d, kb, vf, Pass{v, sp, g, None{}}), c, d, (kb - 2 : U32), vf)

# A round is over when a split is decided, or goes again with its tables.
type Round is Data:
  Over{cut: Maybe<&2, Cut>}
  Again{vf: UMap, vb: UMap}

# A heuristic split searches the half it came from exactly, and the other
# with heuristics still on.
def heuristic.of(+o: U32, +n: U32, +forward: Bool, +olo: U32, +nlo: U32) -> Cut:
  Cut{(olo + o : U32), (nlo + n : U32), Bool.not(forward), forward}

def heuristic(sp: Split, +olo: U32, +nlo: U32) -> Cut:
  match sp:
    case Split{o, n, p, forward}:
      heuristic.of(o, n, forward, olo, nlo)

def pick_split.b(+fo: U32, +fn: U32, +fp: U32, +ff: Bool, b: Maybe<&2, Split>) -> Maybe<&2, Split>:
  match b:
    case None{}:
      Some{Split{fo, fn, fp, ff}}
    case Some{Split{+bo, +bn, +bp, +bf}}:
      Bool.pick(Maybe<&2, Split>, U32.is_gt(fp, bp), Some{Split{fo, fn, fp, ff}}, Some{Split{bo, bn, bp, bf}})

def pick_split(f: Maybe<&2, Split>, b: Maybe<&2, Split>) -> Maybe<&2, Split>:
  match f:
    case None{}:
      b
    case Some{Split{fo, fn, fp, ff}}:
      pick_split.b(fo, fn, fp, ff, b)

def cut_of(ms: Maybe<&2, Split>, +olo: U32, +nlo: U32) -> Maybe<&2, Cut>:
  match ms:
    case None{}:
      None{}
    case Some{sp}:
      Some{heuristic(sp, olo, nlo)}

def snake.cost(+c: Ctx, vf: UMap, vb: UMap, fs: Maybe<&2, Split>, bs: Maybe<&2, Split>, over: Bool) -> Round:
  match over:
    case False{}:
      Again{vf, vb}
    case True{}:
      Over{cut_of(pick_split(fs, bs), ctx.olo(c), ctx.nlo(c))}

def snake.decide(+c: Ctx, +d: U32, vf: UMap, vb: UMap, fs: Maybe<&2, Split>, bs: Maybe<&2, Split>, good: Maybe<&2, Split>) -> Round:
  match good:
    case Some{sp}:
      Over{Some{heuristic(sp, ctx.olo(c), ctx.nlo(c))}}
    case None{}:
      snake.cost(c, vf, vb, fs, bs, ctx.cap(c, d))

def snake.round.b(+c: Ctx, +d: U32, vf: UMap, fs: Maybe<&2, Split>, pb: Pass) -> Round:
  match pb:
    case Pass{vb, bs, good, Some{cut}}:
      Over{Some{cut}}
    case Pass{vb, bs, good, None{}}:
      snake.decide(c, d, vf, vb, fs, bs, good)

def snake.round.f(+c: Ctx, +d: U32, vb: UMap, pf: Pass) -> Round:
  match pf:
    case Pass{vf, fs, fg, Some{cut}}:
      Over{Some{cut}}
    case Pass{+vf, fs, fg, None{}}:
      snake.round.b(c, d, vf, fs, bwd.go(U32.to_nat((d + 1 : U32)), Pass{vb, None{}, fg, None{}}, c, d, (B() + d : U32), vf))

def snake.round(+c: Ctx, +d: U32, vf: UMap, +vb: UMap) -> Round:
  snake.round.f(c, d, vb, fwd.go(U32.to_nat((d + 1 : U32)), Pass{vf, None{}, None{}, None{}}, c, d, (B() + d : U32), vb))

def snake.go(fuel: Nat, r: Round, +c: Ctx, +d: U32) -> Maybe<&2, Cut>:
  match fuel r:
    case 0n Over{cut}:
      cut
    case 0n Again{vf, vb}:
      None{}
    case 1n+q Over{cut}:
      cut
    case 1n+q Again{vf, vb}:
      +d2 = (d + 1 : U32)
      snake.go(q, snake.round(c, d2, vf, vb), c, d2)

# `find_middle_snake`: `None` only where the rounds run out undecided.
def middle_snake(+s: Seqs, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32, +heur: Bool) -> Maybe<&2, Cut>:
  +n = (ohi - olo : U32)
  +m = (nhi - nlo : U32)
  +dmax = (U32.shr(((n + m : U32) + 1 : U32)) + 1 : U32)
  +c = {Ctx{s, olo, ohi, nlo, nhi, ((n + B() : U32) - m : U32), odd((n - m : U32)), heur, dmax} : Ctx}
  snake.go(U32.to_nat((dmax - 1 : U32)), snake.round(c, 0, UNone{}, UNone{}), c, 0)

# The front anchor: past a shift of at most four items on the longer side, a
# shared run of 96 or more is taken as it stands, before any search.
type Best is Data:
  Best{skip: U32, common: U32, stop: Bool}

def skip.common(+s: Seqs, +o: U32, +oe: U32, +n: U32, +ne: U32, go: Bool) -> U32:
  match go:
    case True{}:
      pre(s, o, oe, n, ne)
    case False{}:
      0

def skip.go(fuel: Nat, b: Best, +s: Seqs, +ins: Bool, +o: U32, +oe: U32, +n: U32, +ne: U32, +k: U32) -> Best:
  match fuel b:
    case 0n Best{skip, common, stop}:
      Best{skip, common, stop}
    case 1n+q Best{skip, common, True{}}:
      Best{skip, common, True{}}
    case 1n+q Best{skip, +common, False{}}:
      +oo = Bool.pick(U32, ins, o, (o + k : U32))
      +nn = Bool.pick(U32, ins, (n + k : U32), n)
      +c = skip.common(s, oo, oe, nn, ne, same_at(s, oo, nn))
      +take = Bool.and(U32.is_ge(c, 96), U32.is_gt(c, common))
      skip.go(q, Best{Bool.pick(U32, take, k, skip), Bool.pick(U32, take, c, common), Bool.and(take, U32.is_ge(c, 768))}, s, ins, o, oe, n, ne, (k + 1 : U32))

# What the front anchor has emitted, reversed, where the two ranges now
# start, and whether the last try moved them.
type Front is Data:
  Front{ops: List<&2, Op>, o: U32, n: U32, moved: Bool}

def front.apply(+ops: List<&2, Op>, +o: U32, +n: U32, +ins: Bool, b: Best) -> Front:
  match b:
    case Best{+skip, +common, stop}:
      +found = U32.is_gt(common, 0)
      +os = Bool.pick(U32, ins, 0, skip)
      +ns = Bool.pick(U32, ins, skip, 0)
      +shift = Bool.pick(Op, ins, Gain{o, n, skip}, Lose{o, skip, n})
      Front{Bool.pick(List<&2, Op>, found, Same{(o + os : U32), (n + ns : U32), common} <> shift <> ops, ops),
            Bool.pick(U32, found, ((o + os : U32) + common : U32), o),
            Bool.pick(U32, found, ((n + ns : U32) + common : U32), n),
            found}

def front.try.at(+s: Seqs, +ops: List<&2, Op>, +o: U32, +oe: U32, +n: U32, +ne: U32, go: Bool) -> Front:
  match go:
    case False{}:
      Front{ops, o, n, False{}}
    case True{}:
      +ol = (oe - o : U32)
      +nl = (ne - n : U32)
      +ins = U32.is_gt(nl, ol)
      +most = U32.min((Bool.pick(U32, ins, nl, ol) - 1 : U32), 4)
      front.apply(ops, o, n, ins, skip.go(U32.to_nat(most), Best{0, 0, False{}}, s, ins, o, oe, n, ne, 1))

def front.try(+s: Seqs, +ops: List<&2, Op>, +o: U32, +oe: U32, +n: U32, +ne: U32, go: Bool) -> Front:
  match go:
    case False{}:
      Front{ops, o, n, False{}}
    case True{}:
      +ol = (oe - o : U32)
      +nl = (ne - n : U32)
      +small = U32.min(ol, nl)
      +large = U32.max(ol, nl)
      front.try.at(s, ops, o, oe, n, ne, Bool.and(Bool.and(U32.is_gt(ol, 96), U32.is_gt(nl, 96)), U32.is_ge(large, (small * 2 : U32))))

def front.go(fuel: Nat, f: Front, +s: Seqs, +oe: U32, +ne: U32) -> Front:
  match fuel f:
    case 0n Front{ops, o, n, moved}:
      Front{ops, o, n, moved}
    case 1n+q Front{ops, o, n, False{}}:
      Front{ops, o, n, False{}}
    case 1n+q Front{ops, +o, +n, True{}}:
      front.go(q, front.try(s, ops, o, oe, n, ne, Bool.and(U32.is_lt(o, oe), U32.is_lt(n, ne))), s, oe, ne)

# The exact search where one side is small: a table of common-subsequence
# lengths over the small side's rows, walked from the start. Rows are the old
# side where it is the shorter (`emit_small_old_exact`) and the new side
# otherwise (`emit_small_new_exact`); the walk is the same either way, and
# only what it emits is turned round.
type Rc is Data:
  Rc{s: Seqs, olo: U32, nlo: U32, rows_old: Bool, w: U32}

def rc.w(r: Rc) -> U32:
  match r:
    case Rc{s, olo, nlo, rows_old, w}:
      w

def rc.eq(r: Rc, +i: U32, +j: U32) -> Bool:
  match r:
    case Rc{+s, +olo, +nlo, +rows_old, w}:
      Bool.pick(Bool, rows_old, same_at(s, (olo + i : U32), (nlo + j : U32)), same_at(s, (olo + j : U32), (nlo + i : U32)))

def dp.at(+dp: UMap, +w: U32, +i: U32, +j: U32) -> U32:
  at(dp, ((i * w : U32) + j : U32))

def fill.cols(fuel: Nat, +dp: UMap, +r: Rc, +i: U32, +j: U32) -> UMap:
  match fuel:
    case 0n:
      dp
    case 1n+q:
      +w = rc.w(r)
      +i1 = (i + 1 : U32)
      +v = Bool.pick(U32, rc.eq(r, i, j), (dp.at(dp, w, i1, (j + 1 : U32)) + 1 : U32), U32.max(dp.at(dp, w, i1, j), dp.at(dp, w, i, (j + 1 : U32))))
      fill.cols(q, put(dp, ((i * w : U32) + j : U32), v), r, i, (j - 1 : U32))

def fill.rows(fuel: Nat, +dp: UMap, +r: Rc, +i: U32, +c: U32) -> UMap:
  match fuel:
    case 0n:
      dp
    case 1n+q:
      fill.rows(q, fill.cols(U32.to_nat(c), dp, r, i, (c - 1 : U32)), r, (i - 1 : U32), c)

# The walk takes a shared item where the table says it is on a longest path.
def dp.match(+r: Rc, +dp: UMap, +i: U32, +j: U32) -> Bool:
  +w = rc.w(r)
  Bool.and(rc.eq(r, i, j), U32.is_eq(dp.at(dp, w, i, j), (dp.at(dp, w, (i + 1 : U32), (j + 1 : U32)) + 1 : U32)))

def dp.down(+r: Rc, +dp: UMap, +i: U32, +j: U32) -> Bool:
  +w = rc.w(r)
  U32.is_ge(dp.at(dp, w, (i + 1 : U32), j), dp.at(dp, w, i, (j + 1 : U32)))

def run.go(fuel: Nat, +r: Rc, +dp: UMap, +i: U32, +j: U32, acc: U32, go: Bool) -> U32:
  match fuel go:
    case 0n _:
      acc
    case 1n+q False{}:
      acc
    case 1n+q True{}:
      +i2 = (i + 1 : U32)
      +j2 = (j + 1 : U32)
      run.go(q, r, dp, i2, j2, (acc + 1 : U32), dp.match(r, dp, i2, j2))

def rows.go(fuel: Nat, +r: Rc, +dp: UMap, +i: U32, +j: U32, go: Bool) -> U32:
  match fuel go:
    case 0n _:
      i
    case 1n+q False{}:
      i
    case 1n+q True{}:
      +i2 = (i + 1 : U32)
      rows.go(q, r, dp, i2, j, Bool.and(Bool.not(dp.match(r, dp, i2, j)), dp.down(r, dp, i2, j)))

def cols.go(fuel: Nat, +r: Rc, +dp: UMap, +i: U32, +j: U32, go: Bool) -> U32:
  match fuel go:
    case 0n _:
      j
    case 1n+q False{}:
      j
    case 1n+q True{}:
      +j2 = (j + 1 : U32)
      cols.go(q, r, dp, i, j2, Bool.and(Bool.not(dp.match(r, dp, i, j2)), Bool.not(dp.down(r, dp, i, j2))))

# What a run of the walk is on the two sides.
def rc.shared(r: Rc, +si: U32, +sj: U32, +len: U32) -> Op:
  match r:
    case Rc{s, +olo, +nlo, rows_old, w}:
      Bool.pick(Op, rows_old, Same{(olo + si : U32), (nlo + sj : U32), len}, Same{(olo + sj : U32), (nlo + si : U32), len})

def rc.down(r: Rc, +si: U32, +len: U32, +j: U32) -> Op:
  match r:
    case Rc{s, +olo, +nlo, rows_old, w}:
      Bool.pick(Op, rows_old, Lose{(olo + si : U32), len, (nlo + j : U32)}, Gain{(olo + j : U32), (nlo + si : U32), len})

def rc.across(r: Rc, +i: U32, +sj: U32, +len: U32) -> Op:
  match r:
    case Rc{s, +olo, +nlo, rows_old, w}:
      Bool.pick(Op, rows_old, Gain{(olo + i : U32), (nlo + sj : U32), len}, Lose{(olo + sj : U32), len, (nlo + i : U32)})

type Walk is Data:
  Walk{i: U32, j: U32, ops: List<&2, Op>}

def walk.side(+r: Rc, +dp: UMap, +rn: U32, +cn: U32, +i: U32, +j: U32, ops: List<&2, Op>, down: Bool) -> Walk:
  match down:
    case True{}:
      +i2 = rows.go(U32.to_nat((rn - i : U32)), r, dp, i, j, True{})
      Walk{i2, j, rc.down(r, i, (i2 - i : U32), j) <> ops}
    case False{}:
      +j2 = cols.go(U32.to_nat((cn - j : U32)), r, dp, i, j, True{})
      Walk{i, j2, rc.across(r, i, j, (j2 - j : U32)) <> ops}

def walk.branch(+r: Rc, +dp: UMap, +rn: U32, +cn: U32, +i: U32, +j: U32, ops: List<&2, Op>, hit: Bool) -> Walk:
  match hit:
    case True{}:
      +len = run.go(U32.to_nat(U32.min((rn - i : U32), (cn - j : U32))), r, dp, i, j, 0, True{})
      Walk{(i + len : U32), (j + len : U32), rc.shared(r, i, j, len) <> ops}
    case False{}:
      walk.side(r, dp, rn, cn, i, j, ops, dp.down(r, dp, i, j))

def walk.one(w: Walk, +r: Rc, +dp: UMap, +rn: U32, +cn: U32) -> Walk:
  match w:
    case Walk{+i, +j, ops}:
      walk.branch(r, dp, rn, cn, i, j, ops, dp.match(r, dp, i, j))

def walk.more(w: Walk, +rn: U32, +cn: U32) -> Bool:
  match w:
    case Walk{i, j, ops}:
      Bool.and(U32.is_lt(i, rn), U32.is_lt(j, cn))

def walk.go(fuel: Nat, +w: Walk, +r: Rc, +dp: UMap, +rn: U32, +cn: U32, go: Bool) -> Walk:
  match fuel go:
    case 0n _:
      w
    case 1n+q False{}:
      w
    case 1n+q True{}:
      +w2 = walk.one(w, r, dp, rn, cn)
      walk.go(q, w2, r, dp, rn, cn, walk.more(w2, rn, cn))

def walk.tail(w: Walk, +r: Rc, +rn: U32, +cn: U32) -> List<&2, Op>:
  match w:
    case Walk{+i, +j, +ops}:
      Bool.pick(List<&2, Op>, U32.is_lt(i, rn), rc.down(r, i, (rn - i : U32), j) <> ops,
        Bool.pick(List<&2, Op>, U32.is_lt(j, cn), rc.across(r, i, j, (cn - j : U32)) <> ops, ops))

def small.ok(+ol: U32, +nl: U32) -> Bool:
  +small = U32.min(ol, nl)
  Bool.and(Bool.and(U32.is_gt(small, 0), U32.is_le(small, 64)),
           Bool.and(U32.is_ge(U32.max(ol, nl), 512), U32.is_le((ol * nl : U32), 64000000)))

# The ops, reversed.
def small.exact(+s: Seqs, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32) -> List<&2, Op>:
  +ol = (ohi - olo : U32)
  +nl = (nhi - nlo : U32)
  +rows_old = U32.is_le(ol, nl)
  +rn = Bool.pick(U32, rows_old, ol, nl)
  +cn = Bool.pick(U32, rows_old, nl, ol)
  +r = {Rc{s, olo, nlo, rows_old, (cn + 1 : U32)} : Rc}
  +dp = fill.rows(U32.to_nat(rn), UNone{}, r, (rn - 1 : U32), cn)
  walk.tail(walk.go(U32.to_nat(((rn + cn : U32) + 1 : U32)), Walk{0, 0, Nil{}}, r, dp, rn, cn, True{}), r, rn, cn)

# The bisection, as a stack of jobs rather than a recursion: a box still to
# search, or an operation to emit. The jobs are taken from the front, so the
# operations come out in the order `conquer` would have emitted them.
type Job is Data:
  Conquer{olo: U32, ohi: U32, nlo: U32, nhi: U32, heur: Bool}
  Put{op: Op}

def puts_rev(ops: List<&2, Op>, acc: List<&2, Job>) -> List<&2, Job>:
  match ops:
    case Nil{}:
      acc
    case op <> rest:
      puts_rev(rest, Put{op} <> acc)

def conquer.split(+fo: U32, +oe: U32, +fn: U32, +ne: U32, tail: List<&2, Job>, cut: Maybe<&2, Cut>) -> List<&2, Job>:
  match cut:
    case Some{Cut{+co, +cn, l, r}}:
      Conquer{fo, co, fn, cn, l} <> Conquer{co, oe, cn, ne, r} <> tail
    case None{}:
      Put{Lose{fo, (oe - fo : U32), fn}} <> Put{Gain{fo, fn, (ne - fn : U32)}} <> tail

def conquer.small(+s: Seqs, +fo: U32, +oe: U32, +fn: U32, +ne: U32, +heur: Bool, tail: List<&2, Job>, small: Bool) -> List<&2, Job>:
  match small:
    case True{}:
      puts_rev(small.exact(s, fo, oe, fn, ne), tail)
    case False{}:
      conquer.split(fo, oe, fn, ne, tail, middle_snake(s, fo, oe, fn, ne, heur))

def conquer.old_empty(+s: Seqs, +fo: U32, +oe: U32, +fn: U32, +ne: U32, +heur: Bool, tail: List<&2, Job>, empty: Bool) -> List<&2, Job>:
  match empty:
    case True{}:
      Put{Gain{fo, fn, (ne - fn : U32)}} <> tail
    case False{}:
      conquer.small(s, fo, oe, fn, ne, heur, tail, small.ok((oe - fo : U32), (ne - fn : U32)))

def conquer.new_empty(+s: Seqs, +fo: U32, +oe: U32, +fn: U32, +ne: U32, +heur: Bool, tail: List<&2, Job>, empty: Bool) -> List<&2, Job>:
  match empty:
    case True{}:
      Put{Lose{fo, (oe - fo : U32), fn}} <> tail
    case False{}:
      conquer.old_empty(s, fo, oe, fn, ne, heur, tail, U32.is_ge(fo, oe))

def conquer.mid(+s: Seqs, +fo: U32, +oe: U32, +fn: U32, +ne: U32, +heur: Bool, tail: List<&2, Job>, both: Bool) -> List<&2, Job>:
  match both:
    case True{}:
      tail
    case False{}:
      conquer.new_empty(s, fo, oe, fn, ne, heur, tail, U32.is_ge(fn, ne))

def conquer.front(+s: Seqs, +oe: U32, +ne: U32, +heur: Bool, tail: List<&2, Job>, f: Front) -> List<&2, Job>:
  match f:
    case Front{ops, +fo, +fn, moved}:
      puts_rev(ops, conquer.mid(s, fo, oe, fn, ne, heur, tail, Bool.and(U32.is_ge(fo, oe), U32.is_ge(fn, ne))))

def conquer(+s: Seqs, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32, +heur: Bool, +rest: List<&2, Job>) -> List<&2, Job>:
  +pl = pre(s, olo, ohi, nlo, nhi)
  +o1 = (olo + pl : U32)
  +n1 = (nlo + pl : U32)
  +sl = suf(s, o1, ohi, n1, nhi)
  +oe = (ohi - sl : U32)
  +ne = (nhi - sl : U32)
  +tail = Bool.pick(List<&2, Job>, U32.is_gt(sl, 0), Put{Same{oe, ne, sl}} <> rest, rest)
  +f = front.go(U32.to_nat((span(o1, oe) + 1 : U32)), front.try(s, Nil{}, o1, oe, n1, ne, Bool.and(U32.is_lt(o1, oe), U32.is_lt(n1, ne))), s, oe, ne)
  +body = conquer.front(s, oe, ne, heur, tail, f)
  Bool.pick(List<&2, Job>, U32.is_gt(pl, 0), Put{Same{olo, nlo, pl}} <> body, body)

def myers.run(fuel: Nat, +s: Seqs, jobs: List<&2, Job>, acc: List<&2, Op>) -> List<&2, Op>:
  match fuel jobs:
    case 0n _:
      acc
    case 1n+q Nil{}:
      acc
    case 1n+q Put{op} <> rest:
      myers.run(q, s, rest, op <> acc)
    case 1n+q Conquer{olo, ohi, nlo, nhi, heur} <> rest:
      myers.run(q, s, conquer(s, olo, ohi, nlo, nhi, heur, rest), acc)

def fuel.of(+ol: U32, +nl: U32) -> Nat:
  U32.to_nat(((ol + nl : U32) * 8 + 64 : U32))

# `diff_deadline_pretrimmed`, with the trimmed prefix and suffix given. The
# ops, reversed, onto `acc`.
def myers.middle(+s: Seqs, +o1: U32, +oe: U32, +n1: U32, +ne: U32, +heur: Bool, +acc: List<&2, Op>, kind: U32) -> List<&2, Op>:
  match kind:
    case 0:
      acc
    case 1:
      Gain{o1, n1, (ne - n1 : U32)} <> acc
    case 2:
      Lose{o1, (oe - o1 : U32), n1} <> acc
    case _:
      myers.run(fuel.of((oe - o1 : U32), (ne - n1 : U32)), s, [Conquer{o1, oe, n1, ne, heur}], acc)

def myers.pretrimmed(+s: Seqs, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32, +pl: U32, +sl: U32, +heur: Bool, acc: List<&2, Op>) -> List<&2, Op>:
  +o1 = (olo + pl : U32)
  +n1 = (nlo + pl : U32)
  +oe = (ohi - sl : U32)
  +ne = (nhi - sl : U32)
  +oz = U32.is_ge(o1, oe)
  +nz = U32.is_ge(n1, ne)
  +kind = Bool.pick(U32, Bool.and(oz, nz), 0, Bool.pick(U32, oz, 1, Bool.pick(U32, nz, 2, 3)))
  same_if(oe, ne, sl, myers.middle(s, o1, oe, n1, ne, heur, same_if(olo, nlo, pl, acc), kind))

# `diff_deadline_impl`: trim, then search.
def myers.impl(+s: Seqs, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32, +heur: Bool, acc: List<&2, Op>) -> List<&2, Op>:
  +pl = pre(s, olo, ohi, nlo, nhi)
  +sl = suf(s, (olo + pl : U32), ohi, (nlo + pl : U32), nhi)
  myers.pretrimmed(s, olo, ohi, nlo, nhi, pl, sl, heur, acc)

# Myers' preflight
# ----------------

# `should_scan`: both sides long, and neither end, nor anything within eight
# of it, shared.
def probe.go(fuel: Nat, +s: Seqs, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32, +k: U32, acc: Bool) -> Bool:
  match fuel:
    case 0n:
      acc
    case 1n+q:
      +ol = (ohi - 1 : U32)
      +nl = (nhi - 1 : U32)
      +hit = Bool.or(Bool.or(same_at(s, olo, (nlo + k : U32)), same_at(s, (olo + k : U32), nlo)),
                     Bool.or(same_at(s, ol, (nl - k : U32)), same_at(s, (ol - k : U32), nl)))
      probe.go(q, s, olo, ohi, nlo, nhi, (k + 1 : U32), Bool.and(acc, Bool.not(hit)))

def should_scan(+s: Seqs, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32) -> Bool:
  +big = Bool.and(U32.is_ge(span(olo, ohi), 512), U32.is_ge(span(nlo, nhi), 512))
  +ends = Bool.not(Bool.or(same_at(s, olo, nlo), same_at(s, (ohi - 1 : U32), (nhi - 1 : U32))))
  Bool.and(big, Bool.and(ends, probe.go(Bool.pick(Nat, big, 8n, 0n), s, olo, ohi, nlo, nhi, 1, True{})))

def seqs.old(s: Seqs) -> UMap:
  match s:
    case Seqs{old, new}:
      old

def seqs.new(s: Seqs) -> UMap:
  match s:
    case Seqs{old, new}:
      new

# How often each value occurs in `seq` from `i` on.
def count.go(fuel: Nat, +m: UMap, +seq: UMap, +i: U32) -> UMap:
  match fuel:
    case 0n:
      m
    case 1n+q:
      +v = at(seq, i)
      count.go(q, put(m, v, (at(m, v) + 1 : U32)), seq, (i + 1 : U32))

# `record_actions`: 0 to discard a record the other side never holds, 1 to
# keep one it holds rarely, 2 to look at one it holds often.
def act(+c: U32, +lim: U32) -> U32:
  Bool.pick(U32, U32.is_eq(c, 0), 0, Bool.pick(U32, U32.is_lt(c, lim), 1, 2))

def acts.go(fuel: Nat, acts: UMap, +seq: UMap, +lo: U32, +opp: UMap, +lim: U32, +k: U32) -> UMap:
  match fuel:
    case 0n:
      acts
    case 1n+q:
      acts.go(q, put(acts, k, act(at(opp, at(seq, (lo + k : U32))), lim)), seq, lo, opp, lim, (k + 1 : U32))

type Scanned is Data:
  Scanned{d: U32, v: U32, stop: Bool}

def scan.go(fuel: Nat, st: Scanned, +acts: UMap, +pos: U32, +down: Bool) -> Scanned:
  match fuel st:
    case 0n Scanned{d, v, stop}:
      Scanned{d, v, stop}
    case 1n+q Scanned{d, v, True{}}:
      Scanned{d, v, True{}}
    case 1n+q Scanned{+d, +v, False{}}:
      +a = at(acts, pos)
      scan.go(q, Scanned{Bool.pick(U32, U32.is_eq(a, 0), (d + 1 : U32), d), Bool.pick(U32, U32.is_eq(a, 2), (v + 1 : U32), v), U32.is_eq(a, 1)},
              acts, Bool.pick(U32, down, (pos - 1 : U32), (pos + 1 : U32)), down)

def scanned.d(s: Scanned) -> U32:
  match s:
    case Scanned{d, v, stop}:
      d

def scanned.v(s: Scanned) -> U32:
  match s:
    case Scanned{d, v, stop}:
      v

# `discard_confusing_record`: a common record among discards, with too few
# others like it to its sides to be worth matching.
def confusing(+acts: UMap, +idx: U32, +len: U32) -> Bool:
  +l = scan.go(U32.to_nat(U32.min(idx, 100)), Scanned{0, 0, False{}}, acts, (idx - 1 : U32), True{})
  +r = scan.go(U32.to_nat(U32.min(((len - idx : U32) - 1 : U32), 100)), Scanned{0, 0, False{}}, acts, (idx + 1 : U32), False{})
  +ds = (scanned.d(l) + scanned.d(r) : U32)
  +vs = ((scanned.v(l) + scanned.v(r) : U32) + 1 : U32)
  Bool.and(Bool.and(U32.is_gt(scanned.d(l), 0), U32.is_gt(scanned.d(r), 0)), U32.is_lt((vs * 4 : U32), (vs + ds : U32)))

def keep.of(+acts: UMap, +idx: U32, +len: U32, a: U32) -> Bool:
  match a:
    case 0:
      False{}
    case 1:
      True{}
    case _:
      Bool.not(confusing(acts, idx, len))

type Kept is Data:
  Kept{vals: UMap, idx: UMap, count: U32}

def kept.push(st: Kept, v: U32, i: U32) -> Kept:
  match st:
    case Kept{vals, idx, +count}:
      Kept{put(vals, count, v), put(idx, count, i), (count + 1 : U32)}

def kept.add(st: Kept, v: U32, i: U32, go: Bool) -> Kept:
  match go:
    case True{}:
      kept.push(st, v, i)
    case False{}:
      st

def keep.go(fuel: Nat, st: Kept, +acts: UMap, +len: U32, +seq: UMap, +lo: U32, +k: U32) -> Kept:
  match fuel:
    case 0n:
      st
    case 1n+q:
      +i = (lo + k : U32)
      keep.go(q, kept.add(st, at(seq, i), i, keep.of(acts, k, len, at(acts, k))), acts, len, seq, lo, (k + 1 : U32))

def kept.count(st: Kept) -> U32:
  match st:
    case Kept{vals, idx, count}:
      count

# What the preflight hands the search: the ranges as they are, or each side
# with its discarded records taken out, and where the rest stood.
type Reduced is Data:
  Trimmed{}
  Reduction{ov: UMap, oi: UMap, ol: U32, nv: UMap, ni: UMap, nl: U32}

def reduce.new(ov: UMap, oi: UMap, ol: U32, kn: Kept) -> Reduced:
  match kn:
    case Kept{nv, ni, nl}:
      Reduction{ov, oi, ol, nv, ni, nl}

def reduce.both(ko: Kept, kn: Kept) -> Reduced:
  match ko:
    case Kept{ov, oi, ol}:
      reduce.new(ov, oi, ol, kn)

def reduce.fin(ko: Kept, kn: Kept, all: Bool) -> Reduced:
  match all:
    case True{}:
      Trimmed{}
    case False{}:
      reduce.both(ko, kn)

def reduce.of(+ol: U32, +nl: U32, +ko: Kept, +kn: Kept) -> Reduced:
  reduce.fin(ko, kn, Bool.and(U32.is_eq(kept.count(ko), ol), U32.is_eq(kept.count(kn), nl)))

def reduce.at(+s: Seqs, +o1: U32, +oe: U32, +n1: U32, +ne: U32) -> Reduced:
  +ol = (oe - o1 : U32)
  +nl = (ne - n1 : U32)
  +so = seqs.old(s)
  +sn = seqs.new(s)
  +oc = count.go(U32.to_nat(ol), UNone{}, so, o1)
  +nc = count.go(U32.to_nat(nl), UNone{}, sn, n1)
  +oa = acts.go(U32.to_nat(ol), UNone{}, so, o1, nc, clamp(isqrt(ol), 1, 1024), 0)
  +na = acts.go(U32.to_nat(nl), UNone{}, sn, n1, oc, clamp(isqrt(nl), 1, 1024), 0)
  reduce.of(ol, nl, keep.go(U32.to_nat(ol), Kept{UNone{}, UNone{}, 0}, oa, ol, so, o1, 0),
                    keep.go(U32.to_nat(nl), Kept{UNone{}, UNone{}, 0}, na, nl, sn, n1, 0))

def reduce(+s: Seqs, +o1: U32, +oe: U32, +n1: U32, +ne: U32, scan: Bool) -> Reduced:
  match scan:
    case False{}:
      Trimmed{}
    case True{}:
      reduce.at(s, o1, oe, n1, ne)

# `ReducedDiffHook`: the reduced search's shared runs, put back where their
# records stood, with everything between them lost and gained.
type Hook is Data:
  Hook{oc: U32, nc: U32, acc: List<&2, Op>}

def hook.gaps(h: Hook, +oa: U32, +na: U32) -> Hook:
  match h:
    case Hook{+oc, +nc, acc}:
      +oc2 = U32.max(oc, oa)
      Hook{oc2, U32.max(nc, na), gain_if(oc2, nc, span(nc, na), lose_if(oc, span(oc, oa), nc, acc))}

def hook.same(h: Hook, +oa: U32, +na: U32, +run: U32) -> Hook:
  match h:
    case Hook{oc, nc, acc}:
      Hook{(oa + run : U32), (na + run : U32), Same{oa, na, run} <> acc}

def hook.acc(h: Hook) -> List<&2, Op>:
  match h:
    case Hook{oc, nc, acc}:
      acc

def run.len.go(fuel: Nat, +oi: UMap, +ni: UMap, +a: U32, +b: U32, +oa: U32, +na: U32, +run: U32, go: Bool) -> U32:
  match fuel go:
    case 0n _:
      run
    case 1n+q False{}:
      run
    case 1n+q True{}:
      +r2 = (run + 1 : U32)
      run.len.go(q, oi, ni, a, b, oa, na, r2,
        Bool.and(U32.is_eq(at(oi, (a + r2 : U32)), (oa + r2 : U32)), U32.is_eq(at(ni, (b + r2 : U32)), (na + r2 : U32))))

def eq.go(fuel: Nat, h: Hook, +oi: UMap, +ni: UMap, +ri: U32, +rj: U32, +len: U32, +off: U32, go: Bool) -> Hook:
  match fuel go:
    case 0n _:
      h
    case 1n+q False{}:
      h
    case 1n+q True{}:
      +a = (ri + off : U32)
      +b = (rj + off : U32)
      +oa = at(oi, a)
      +na = at(ni, b)
      +run = run.len.go(U32.to_nat(((len - off : U32) - 1 : U32)), oi, ni, a, b, oa, na, 1,
        Bool.and(U32.is_eq(at(oi, (a + 1 : U32)), (oa + 1 : U32)), U32.is_eq(at(ni, (b + 1 : U32)), (na + 1 : U32))))
      +off2 = (off + run : U32)
      eq.go(q, hook.same(hook.gaps(h, oa, na), oa, na, run), oi, ni, ri, rj, len, off2, U32.is_lt(off2, len))

def translate(ops: List<&2, Op>, h: Hook, +oi: UMap, +ni: UMap) -> Hook:
  match ops:
    case Nil{}:
      h
    case Same{o, n, +len} <> rest:
      translate(rest, eq.go(U32.to_nat(len), h, oi, ni, o, n, len, 0, U32.is_gt(len, 0)), oi, ni)
    case Lose{o, len, n} <> rest:
      translate(rest, h, oi, ni)
    case Gain{o, n, len} <> rest:
      translate(rest, h, oi, ni)

def myers.reduced(+s: Seqs, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32, +pl: U32, +sl: U32, r: Reduced) -> List<&2, Op>:
  match r:
    case Trimmed{}:
      myers.pretrimmed(s, olo, ohi, nlo, nhi, pl, sl, True{}, Nil{})
    case Reduction{ov, oi, +ol, nv, ni, +nl}:
      +oe = (ohi - sl : U32)
      +ne = (nhi - sl : U32)
      +inner = List.reverse(&2, Op, myers.impl(Seqs{ov, nv}, 0, ol, 0, nl, True{}, Nil{}))
      +h = translate(inner, Hook{(olo + pl : U32), (nlo + pl : U32), same_if(olo, nlo, pl, Nil{})}, oi, ni)
      same_if(oe, ne, sl, hook.acc(hook.gaps(h, oe, ne)))

# `myers::diff_deadline`, reversed.
def myers.diff(+s: Seqs, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32) -> List<&2, Op>:
  +pl = pre(s, olo, ohi, nlo, nhi)
  +o1 = (olo + pl : U32)
  +n1 = (nlo + pl : U32)
  +sl = suf(s, o1, ohi, n1, nhi)
  +oe = (ohi - sl : U32)
  +ne = (nhi - sl : U32)
  myers.reduced(s, olo, ohi, nlo, nhi, pl, sl, reduce(s, o1, oe, n1, ne, should_scan(s, o1, oe, n1, ne)))

# Histogram
# ---------

# `find_anchor`: the longest run the two ranges share, grown in both
# directions from a pair of equal items whose value the old range holds at
# most 64 times; ties go to the rarer run, then the earlier one. A diagonal
# already covered as far as this item is not grown again.
type Anchor is Data:
  Anchor{o: U32, n: U32, len: U32, count: U32}

type Search is Data:
  Hit{a: Anchor}
  Miss{}
  Fall{}

type Scan is Data:
  Scan{has: Bool, best: Maybe<&2, Anchor>, covered: UMap}

def places.go(fuel: Nat, m: PMap, +s: Seqs, +i: U32) -> PMap:
  match fuel:
    case 0n:
      m
    case 1n+q:
      places.go(q, push(m, old_at(s, i), i), s, (i - 1 : U32))

type Ext is Data:
  Ext{o: U32, n: U32, mc: U32}

def back.go(fuel: Nat, +s: Seqs, +pos: PMap, +olo: U32, +nlo: U32, +o: U32, +n: U32, +mc: U32, go: Bool) -> Ext:
  match fuel go:
    case 0n _:
      Ext{o, n, mc}
    case 1n+q False{}:
      Ext{o, n, mc}
    case 1n+q True{}:
      +o2 = (o - 1 : U32)
      +n2 = (n - 1 : U32)
      back.go(q, s, pos, olo, nlo, o2, n2, U32.min(mc, bucket.count(bucket(pos, old_at(s, o2)))),
        Bool.and(Bool.and(U32.is_gt(o2, olo), U32.is_gt(n2, nlo)), same_at(s, (o2 - 1 : U32), (n2 - 1 : U32))))

def ahead.go(fuel: Nat, +s: Seqs, +pos: PMap, +ohi: U32, +nhi: U32, +o: U32, +n: U32, +mc: U32, go: Bool) -> Ext:
  match fuel go:
    case 0n _:
      Ext{o, n, mc}
    case 1n+q False{}:
      Ext{o, n, mc}
    case 1n+q True{}:
      +o2 = (o + 1 : U32)
      +n2 = (n + 1 : U32)
      ahead.go(q, s, pos, ohi, nhi, o2, n2, U32.min(mc, bucket.count(bucket(pos, old_at(s, o2)))),
        Bool.and(Bool.and(U32.is_lt((o2 + 1 : U32), ohi), U32.is_lt((n2 + 1 : U32), nhi)), same_at(s, (o2 + 1 : U32), (n2 + 1 : U32))))

def anchor.beats(+co: U32, +cn: U32, +cl: U32, +cc: U32, +bo: U32, +bn: U32, +bl: U32, +bc: U32) -> Bool:
  Bool.or(U32.is_gt(cl, bl),
    Bool.and(U32.is_eq(cl, bl),
      Bool.or(U32.is_lt(cc, bc),
        Bool.and(U32.is_eq(cc, bc),
          Bool.or(U32.is_lt(co, bo), Bool.and(U32.is_eq(co, bo), U32.is_lt(cn, bn)))))))

def better_anchor.of(+bo: U32, +bn: U32, +bl: U32, +bc: U32, c: Anchor) -> Maybe<&2, Anchor>:
  match c:
    case Anchor{+co, +cn, +cl, +cc}:
      Bool.pick(Maybe<&2, Anchor>, anchor.beats(co, cn, cl, cc, bo, bn, bl, bc), Some{Anchor{co, cn, cl, cc}}, Some{Anchor{bo, bn, bl, bc}})

def better_anchor(best: Maybe<&2, Anchor>, c: Anchor) -> Maybe<&2, Anchor>:
  match best:
    case None{}:
      Some{c}
    case Some{Anchor{bo, bn, bl, bc}}:
      better_anchor.of(bo, bn, bl, bc, c)

def cand.fin(has: Bool, best: Maybe<&2, Anchor>, covered: UMap, +key: U32, +cov: U32, +os: U32, +ns: U32, f: Ext) -> Scan:
  match f:
    case Ext{+oe, +ne, mc}:
      Scan{has, better_anchor(best, Anchor{os, ns, ((oe - os : U32) + 1 : U32), mc}), put(covered, key, U32.max(cov, (ne + 1 : U32)))}

def cand.ext(has: Bool, best: Maybe<&2, Anchor>, covered: UMap, +key: U32, +cov: U32, +s: Seqs, +pos: PMap, +ohi: U32, +nhi: U32, +i: U32, +j: U32, b: Ext) -> Scan:
  match b:
    case Ext{+os, +ns, +mc}:
      cand.fin(has, best, covered, key, cov, os, ns,
        ahead.go(U32.to_nat(U32.min(span((i + 1 : U32), ohi), span((j + 1 : U32), nhi))), s, pos, ohi, nhi, i, j, mc,
          Bool.and(Bool.and(U32.is_lt((i + 1 : U32), ohi), U32.is_lt((j + 1 : U32), nhi)), same_at(s, (i + 1 : U32), (j + 1 : U32)))))

def cand.do(has: Bool, best: Maybe<&2, Anchor>, covered: UMap, +key: U32, +cov: U32, +s: Seqs, +pos: PMap, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32, +j: U32, +cnt: U32, +i: U32, skip: Bool) -> Scan:
  match skip:
    case True{}:
      Scan{has, best, covered}
    case False{}:
      cand.ext(has, best, covered, key, cov, s, pos, ohi, nhi, i, j,
        back.go(U32.to_nat(U32.min((i - olo : U32), (j - nlo : U32))), s, pos, olo, nlo, i, j, cnt,
          Bool.and(Bool.and(U32.is_gt(i, olo), U32.is_gt(j, nlo)), same_at(s, (i - 1 : U32), (j - 1 : U32)))))

def cand.one(st: Scan, +s: Seqs, +pos: PMap, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32, +j: U32, +cnt: U32, +i: U32) -> Scan:
  match st:
    case Scan{has, best, +covered}:
      +key = Bool.pick(U32, U32.is_ge(i, j), ((i - j : U32) * 2 : U32), (((j - i : U32) * 2 : U32) + 1 : U32))
      +cov = at(covered, key)
      cand.do(has, best, covered, key, cov, s, pos, olo, ohi, nlo, nhi, j, cnt, i, U32.is_lt(j, cov))

def cands.go(places: List<&2, U32>, st: Scan, +s: Seqs, +pos: PMap, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32, +j: U32, +cnt: U32) -> Scan:
  match places:
    case Nil{}:
      st
    case i <> rest:
      cands.go(rest, cand.one(st, s, pos, olo, ohi, nlo, nhi, j, cnt, i), s, pos, olo, ohi, nlo, nhi, j, cnt)

def scan.has(st: Scan) -> Scan:
  match st:
    case Scan{has, best, covered}:
      Scan{True{}, best, covered}

def j.cands(st: Scan, +s: Seqs, +pos: PMap, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32, +j: U32, places: List<&2, U32>, +cnt: U32, ok: Bool) -> Scan:
  match ok:
    case False{}:
      st
    case True{}:
      cands.go(places, st, s, pos, olo, ohi, nlo, nhi, j, cnt)

def j.has(st: Scan, +s: Seqs, +pos: PMap, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32, +j: U32, places: List<&2, U32>, +cnt: U32, present: Bool) -> Scan:
  match present:
    case False{}:
      st
    case True{}:
      j.cands(scan.has(st), s, pos, olo, ohi, nlo, nhi, j, places, cnt, U32.is_le(cnt, 64))

def j.bucket(st: Scan, +s: Seqs, +pos: PMap, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32, +j: U32, b: Bucket) -> Scan:
  match b:
    case Bucket{places, +count}:
      j.has(st, s, pos, olo, ohi, nlo, nhi, j, places, count, U32.is_gt(count, 0))

def jloop(fuel: Nat, st: Scan, +s: Seqs, +pos: PMap, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32, +j: U32) -> Scan:
  match fuel:
    case 0n:
      st
    case 1n+q:
      jloop(q, j.bucket(st, s, pos, olo, ohi, nlo, nhi, j, bucket(pos, new_at(s, j))), s, pos, olo, ohi, nlo, nhi, (j + 1 : U32))

def search.of(st: Scan) -> Search:
  match st:
    case Scan{has, Some{a}, covered}:
      Hit{a}
    case Scan{has, None{}, covered}:
      Bool.pick(Search, has, Fall{}, Miss{})

def find_anchor(+s: Seqs, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32) -> Search:
  +pos = places.go(U32.to_nat((ohi - olo : U32)), PNone{}, s, (ohi - 1 : U32))
  search.of(jloop(U32.to_nat((nhi - nlo : U32)), Scan{False{}, None{}, UNone{}}, s, pos, olo, ohi, nlo, nhi, nlo))

# `diff_impl`, as a stack of tasks: a range still to compare, an operation,
# or the operations a Myers fallback produced, reversed.
type Task is Data:
  Compare{olo: U32, ohi: U32, nlo: U32, nhi: U32}
  Say{op: Op}
  Said{ops: List<&2, Op>}

def hist.search(+s: Seqs, +o1: U32, +oe: U32, +n1: U32, +ne: U32, tail: List<&2, Task>, r: Search) -> List<&2, Task>:
  match r:
    case Hit{Anchor{+ao, +an, +al, c}}:
      Compare{o1, ao, n1, an} <> Say{Same{ao, an, al}} <> Compare{(ao + al : U32), oe, (an + al : U32), ne} <> tail
    case Miss{}:
      Say{Lose{o1, (oe - o1 : U32), n1}} <> Say{Gain{oe, n1, (ne - n1 : U32)}} <> tail
    case Fall{}:
      Said{myers.diff(s, o1, oe, n1, ne)} <> tail

def hist.new_empty(+s: Seqs, +o1: U32, +oe: U32, +n1: U32, +ne: U32, tail: List<&2, Task>, empty: Bool) -> List<&2, Task>:
  match empty:
    case True{}:
      Say{Lose{o1, (oe - o1 : U32), n1}} <> tail
    case False{}:
      hist.search(s, o1, oe, n1, ne, tail, find_anchor(s, o1, oe, n1, ne))

def hist.mid(+s: Seqs, +o1: U32, +oe: U32, +n1: U32, +ne: U32, +tail: List<&2, Task>, empty: Bool) -> List<&2, Task>:
  match empty:
    case True{}:
      Bool.pick(List<&2, Task>, U32.is_lt(n1, ne), Say{Gain{o1, n1, (ne - n1 : U32)}} <> tail, tail)
    case False{}:
      hist.new_empty(s, o1, oe, n1, ne, tail, U32.is_ge(n1, ne))

def hist.trim(+s: Seqs, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32, +rest: List<&2, Task>) -> List<&2, Task>:
  +pl = pre(s, olo, ohi, nlo, nhi)
  +o1 = (olo + pl : U32)
  +n1 = (nlo + pl : U32)
  +sl = suf(s, o1, ohi, n1, nhi)
  +oe = (ohi - sl : U32)
  +ne = (nhi - sl : U32)
  +tail = Bool.pick(List<&2, Task>, U32.is_gt(sl, 0), Say{Same{oe, ne, sl}} <> rest, rest)
  +body = hist.mid(s, o1, oe, n1, ne, tail, U32.is_ge(o1, oe))
  Bool.pick(List<&2, Task>, U32.is_gt(pl, 0), Say{Same{olo, nlo, pl}} <> body, body)

def hist.step(+s: Seqs, +olo: U32, +ohi: U32, +nlo: U32, +nhi: U32, +rest: List<&2, Task>, kind: U32) -> List<&2, Task>:
  match kind:
    case 0:
      rest
    case 1:
      Say{Gain{olo, nlo, (nhi - nlo : U32)}} <> rest
    case 2:
      Say{Lose{olo, (ohi - olo : U32), nlo}} <> rest
    case _:
      hist.trim(s, olo, ohi, nlo, nhi, rest)

def hist.kind(+olo: U32, +ohi: U32, +nlo: U32, +nhi: U32) -> U32:
  +oz = U32.is_ge(olo, ohi)
  +nz = U32.is_ge(nlo, nhi)
  Bool.pick(U32, Bool.and(oz, nz), 0, Bool.pick(U32, oz, 1, Bool.pick(U32, nz, 2, 3)))

def hist.run(fuel: Nat, +s: Seqs, tasks: List<&2, Task>, acc: List<&2, Op>) -> List<&2, Op>:
  match fuel tasks:
    case 0n _:
      acc
    case 1n+q Nil{}:
      acc
    case 1n+q Say{op} <> rest:
      hist.run(q, s, rest, op <> acc)
    case 1n+q Said{ops} <> rest:
      hist.run(q, s, rest, List.append(&2, Op, ops, acc))
    case 1n+q Compare{+olo, +ohi, +nlo, +nhi} <> rest:
      hist.run(q, s, hist.step(s, olo, ohi, nlo, nhi, rest, hist.kind(olo, ohi, nlo, nhi)), acc)

# The preflight: two long sides sharing almost nothing are one replacement.
def exceeds.set(fuel: Nat, m: UMap, +s: Seqs, +i: U32) -> UMap:
  match fuel:
    case 0n:
      m
    case 1n+q:
      exceeds.set(q, put(m, old_at(s, i), 1), s, (i + 1 : U32))

def exceeds.count(fuel: Nat, +m: UMap, +s: Seqs, +j: U32, acc: U32) -> U32:
  match fuel:
    case 0n:
      acc
    case 1n+q:
      exceeds.count(q, m, s, (j + 1 : U32), (acc + at(m, new_at(s, j)) : U32))

def disjoint(+s: Seqs, +ol: U32, +nl: U32, scan: Bool) -> Bool:
  match scan:
    case False{}:
      False{}
    case True{}:
      +budget = clamp(U32.div(U32.min(ol, nl), 1024), 1, 64)
      U32.is_le(exceeds.count(U32.to_nat(nl), exceeds.set(U32.to_nat(ol), UNone{}, s, 0), s, 0, 0), budget)

def histogram.of(+s: Seqs, +ol: U32, +nl: U32, fast: Bool) -> List<&2, Op>:
  match fast:
    case True{}:
      [Lose{0, ol, 0}, Gain{0, 0, nl}]
    case False{}:
      +pl = pre(s, 0, ol, 0, nl)
      +sl = suf(s, pl, ol, pl, nl)
      +oe = (ol - sl : U32)
      +ne = (nl - sl : U32)
      +last = Bool.pick(List<&2, Task>, U32.is_gt(sl, 0), [Say{Same{oe, ne, sl}}], Nil{})
      List.reverse(&2, Op, hist.run(fuel.of(ol, nl), s, Compare{pl, oe, pl, ne} <> last, same_if(0, 0, pl, Nil{})))

# The operations, in order, before compaction.
def histogram(+s: Seqs, +ol: U32, +nl: U32) -> List<&2, Op>:
  histogram.of(s, ol, nl, disjoint(s, ol, nl, should_scan(s, 0, ol, 0, nl)))

# Compaction
# ----------

# `cleanup_diff_ops`: each loss, and then each gain, is slid up as far as the
# items it passes allow and then down, merging with its neighbours of the
# same kind — so a change that could stand in several places stands where
# its neighbours make it one run. The list is a zipper: `before` reversed,
# and the operation being moved at the head of `after`.
type Slide is Data:
  Slide{before: List<&2, Op>, after: List<&2, Op>}

type Moved is Data:
  Moving{z: Slide}
  Rested{z: Slide}

def op.empty(op: Op) -> Bool:
  U32.is_eq(op.len(op), 0)

def op.is_same(op: Op) -> Bool:
  U32.is_eq(op.tag(op), 0)

# `swap_adjacent_insert_delete`: the two trade places, each keeping the
# span the pair covered on the side it does not touch.
def op.moved_to(op: Op, +o: U32, +n: U32) -> Op:
  op.with_n(op.with_o(op, o), n)

def head_is_lose(ops: List<&2, Op>) -> Bool:
  match ops:
    case Nil{}:
      False{}
    case op <> rest:
      U32.is_eq(op.tag(op), 1)

# The shared run after the one being moved grows to the left, or a new one
# starts there.
def grow_after(ops: List<&2, Op>, +k: U32, +o: U32, +n: U32) -> List<&2, Op>:
  match ops:
    case Nil{}:
      [Same{o, n, k}]
    case +next <> +rest:
      Bool.pick(List<&2, Op>, op.is_same(next), op.grow_left(next, k) <> rest, Same{o, n, k} <> next <> rest)

# The shared run before it grows to the right, or a new one ends there.
def grow_before(ops: List<&2, Op>, +k: U32, +o: U32, +n: U32) -> List<&2, Op>:
  match ops:
    case Nil{}:
      [Same{o, n, k}]
    case +prev <> +rest:
      Bool.pick(List<&2, Op>, op.is_same(prev), op.grow_right(prev, k) <> rest, Same{o, n, k} <> prev <> rest)

def up.slide(+prev: Op, +bs: List<&2, Op>, +this: Op, rest: List<&2, Op>, +k: U32, +o: U32, +n: U32) -> Moved:
  +after = {op.shift_left(this, k) <> grow_after(rest, k, o, n) : List<&2, Op>}
  +shrunk = op.shrink_left(prev, k)
  Bool.pick(Moved, op.empty(shrunk), Moving{Slide{bs, after}}, Moving{Slide{shrunk <> bs, after}})

def up.stall(+prev: Op, +bs: List<&2, Op>, +this: Op, +rest: List<&2, Op>) -> Moved:
  Bool.pick(Moved, op.empty(prev), Moving{Slide{bs, this <> rest}}, Rested{Slide{prev <> bs, this <> rest}})

def up.shared(+prev: Op, +bs: List<&2, Op>, +this: Op, +rest: List<&2, Op>, +k: U32, +o: U32, +n: U32, go: Bool) -> Moved:
  match go:
    case True{}:
      up.slide(prev, bs, this, rest, k, o, n)
    case False{}:
      up.stall(prev, bs, this, rest)

def up.gain(+s: Seqs, +prev: Op, +bs: List<&2, Op>, +this: Op, +rest: List<&2, Op>) -> Moved:
  +k = suf(s, op.o(prev), op.o_end(prev), op.n(this), op.n_end(this))
  up.shared(prev, bs, this, rest, k, (op.o_end(prev) - k : U32), (op.n_end(this) - k : U32), U32.is_gt(k, 0))

def up.lose(+s: Seqs, +prev: Op, +bs: List<&2, Op>, +this: Op, +rest: List<&2, Op>, ok: Bool) -> Moved:
  match ok:
    case False{}:
      Rested{Slide{prev <> bs, this <> rest}}
    case True{}:
      +k = suf(s, op.o(this), op.o_end(this), op.n(prev), op.n_end(prev))
      up.shared(prev, bs, this, rest, k, (op.o_end(this) - k : U32), (op.n_end(prev) - k : U32), U32.is_gt(k, 0))

def up.equal(+s: Seqs, +prev: Op, +bs: List<&2, Op>, +this: Op, +rest: List<&2, Op>, gain: Bool) -> Moved:
  match gain:
    case True{}:
      up.gain(s, prev, bs, this, rest)
    case False{}:
      up.lose(s, prev, bs, this, rest, head_is_lose(bs))

def up.other(+prev: Op, bs: List<&2, Op>, +this: Op, rest: List<&2, Op>, same: Bool) -> Moved:
  match same:
    case True{}:
      Moving{Slide{bs, op.grow_right(prev, op.len(this)) <> rest}}
    case False{}:
      Moving{Slide{bs, op.moved_to(this, op.o(prev), op.n(prev)) <> op.moved_to(prev, op.o_end(this), op.n_end(this)) <> rest}}

def up.case(+s: Seqs, +prev: Op, +bs: List<&2, Op>, +this: Op, +rest: List<&2, Op>, +tt: U32, pt: U32) -> Moved:
  match pt:
    case 0:
      up.equal(s, prev, bs, this, rest, U32.is_eq(tt, 2))
    case _:
      up.other(prev, bs, this, rest, U32.is_eq(tt, op.tag(prev)))

def up.step(+s: Seqs, z: Slide) -> Moved:
  match z:
    case Slide{Nil{}, after}:
      Rested{Slide{Nil{}, after}}
    case Slide{prev <> bs, Nil{}}:
      Rested{Slide{prev <> bs, Nil{}}}
    case Slide{+prev <> bs, +this <> rest}:
      up.case(s, prev, bs, this, rest, op.tag(this), op.tag(prev))

def down.slide(+bs: List<&2, Op>, +this: Op, +next: Op, +rest: List<&2, Op>, +k: U32, +o: U32, +n: U32) -> Moved:
  +before = grow_before(bs, k, o, n)
  +moved = op.shift_right(this, k)
  +shrunk = op.shrink_right(next, k)
  Bool.pick(Moved, op.empty(shrunk), Moving{Slide{before, moved <> rest}}, Moving{Slide{before, moved <> shrunk <> rest}})

def down.stall(+bs: List<&2, Op>, +this: Op, +next: Op, +rest: List<&2, Op>) -> Moved:
  Bool.pick(Moved, op.empty(next), Moving{Slide{bs, this <> rest}}, Rested{Slide{bs, this <> next <> rest}})

def down.shared(+bs: List<&2, Op>, +this: Op, +next: Op, +rest: List<&2, Op>, +k: U32, +o: U32, +n: U32, go: Bool) -> Moved:
  match go:
    case True{}:
      down.slide(bs, this, next, rest, k, o, n)
    case False{}:
      down.stall(bs, this, next, rest)

def down.gain(+s: Seqs, +bs: List<&2, Op>, +this: Op, +next: Op, +rest: List<&2, Op>) -> Moved:
  +k = pre(s, op.o(next), op.o_end(next), op.n(this), op.n_end(this))
  down.shared(bs, this, next, rest, k, op.o(next), op.n(this), U32.is_gt(k, 0))

def down.lose(+s: Seqs, +bs: List<&2, Op>, +this: Op, +next: Op, +rest: List<&2, Op>, ok: Bool) -> Moved:
  match ok:
    case False{}:
      Rested{Slide{bs, this <> next <> rest}}
    case True{}:
      +k = pre(s, op.o(this), op.o_end(this), op.n(next), op.n_end(next))
      down.shared(bs, this, next, rest, k, op.o(this), op.n(this), U32.is_gt(k, 0))

def down.equal(+s: Seqs, +bs: List<&2, Op>, +this: Op, +next: Op, +rest: List<&2, Op>, gain: Bool) -> Moved:
  match gain:
    case True{}:
      down.gain(s, bs, this, next, rest)
    case False{}:
      down.lose(s, bs, this, next, rest, head_is_lose(rest))

def down.other(bs: List<&2, Op>, +this: Op, +next: Op, rest: List<&2, Op>, same: Bool) -> Moved:
  match same:
    case True{}:
      Moving{Slide{bs, op.grow_right(this, op.len(next)) <> rest}}
    case False{}:
      Moving{Slide{op.moved_to(next, op.o(this), op.n(this)) <> bs, op.moved_to(this, op.o_end(next), op.n_end(next)) <> rest}}

def down.case(+s: Seqs, +bs: List<&2, Op>, +this: Op, +next: Op, +rest: List<&2, Op>, +tt: U32, nt: U32) -> Moved:
  match nt:
    case 0:
      down.equal(s, bs, this, next, rest, U32.is_eq(tt, 2))
    case _:
      down.other(bs, this, next, rest, U32.is_eq(tt, op.tag(next)))

def down.step(+s: Seqs, z: Slide) -> Moved:
  match z:
    case Slide{bs, Nil{}}:
      Rested{Slide{bs, Nil{}}}
    case Slide{bs, this <> Nil{}}:
      Rested{Slide{bs, [this]}}
    case Slide{bs, +this <> +next <> rest}:
      down.case(s, bs, this, next, rest, op.tag(this), op.tag(next))

def up.go(fuel: Nat, m: Moved, +s: Seqs) -> Slide:
  match fuel m:
    case 0n Moving{z}:
      z
    case 0n Rested{z}:
      z
    case 1n+q Rested{z}:
      z
    case 1n+q Moving{z}:
      up.go(q, up.step(s, z), s)

def down.go(fuel: Nat, m: Moved, +s: Seqs) -> Slide:
  match fuel m:
    case 0n Moving{z}:
      z
    case 0n Rested{z}:
      z
    case 1n+q Rested{z}:
      z
    case 1n+q Moving{z}:
      down.go(q, down.step(s, z), s)

def advance(z: Slide) -> Slide:
  match z:
    case Slide{bs, Nil{}}:
      Slide{bs, Nil{}}
    case Slide{bs, cur <> rest}:
      Slide{cur <> bs, rest}

def pass.one(+s: Seqs, +fu: Nat, z: Slide, hit: Bool) -> Slide:
  match hit:
    case True{}:
      advance(down.go(fu, down.step(s, up.go(fu, up.step(s, z), s)), s))
    case False{}:
      advance(z)

def pass.go(fuel: Nat, z: Slide, +s: Seqs, +fu: Nat, +tag: U32) -> Slide:
  match fuel z:
    case 0n Slide{bs, rest}:
      Slide{bs, rest}
    case 1n+q Slide{bs, Nil{}}:
      Slide{bs, Nil{}}
    case 1n+q Slide{bs, +cur <> rest}:
      pass.go(q, pass.one(s, fu, Slide{bs, cur <> rest}, U32.is_eq(op.tag(cur), tag)), s, fu, tag)

def unslide(z: Slide) -> List<&2, Op>:
  match z:
    case Slide{bs, rest}:
      List.append(&2, Op, List.reverse(&2, Op, bs), rest)

# `normalize_diff_op_cursors`: a loss stands at the new side's cursor and a
# gain at the old side's.
def norm.go(ops: List<&2, Op>, +oc: U32, +nc: U32, acc: List<&2, Op>) -> List<&2, Op>:
  match ops:
    case Nil{}:
      List.reverse(&2, Op, acc)
    case Same{+o, +n, +len} <> rest:
      norm.go(rest, (o + len : U32), (n + len : U32), Same{o, n, len} <> acc)
    case Lose{+o, +len, n} <> rest:
      norm.go(rest, (o + len : U32), nc, Lose{o, len, nc} <> acc)
    case Gain{o, +n, +len} <> rest:
      norm.go(rest, oc, (n + len : U32), Gain{oc, n, len} <> acc)

def normalize(ops: List<&2, Op>) -> List<&2, Op>:
  match ops:
    case Nil{}:
      Nil{}
    case +first <> rest:
      norm.go(first <> rest, op.o(first), op.n(first), Nil{})

def compact(+s: Seqs, ops: List<&2, Op>, +fu: Nat) -> List<&2, Op>:
  normalize(unslide(pass.go(fu, Slide{Nil{}, unslide(pass.go(fu, Slide{Nil{}, ops}, s, fu, 1))}, s, fu, 2)))

# Items
# -----

# The Rust `Item`'s equality: the text and terminator of a line, and a
# forgotten item equal to any other forgotten one with the same terminator.
def key.of(text: String, +terminated: Bool, forgotten: Bool) -> String:
  match forgotten:
    case True{}:
      SCon{Chr{88}, SCon{Bool.pick(Char, terminated, Chr{116}, Chr{102}), SNil{}}}
    case False{}:
      SCon{Bool.pick(Char, terminated, Chr{116}, Chr{102}), text}

def key(it: Ops.Item) -> String:
  match it:
    case Ops.Item{text, terminated, forgotten}:
      key.of(text, terminated, forgotten)

type Interned is Data:
  Interned{pool: Ops.Pool, ids: UMap, len: U32}

def intern.go(items: List<&2, Ops.Item>, r: Ops.Pool & U32, +i: U32, m: UMap) -> Interned:
  match items r:
    case Nil{} Tuple{p, h}:
      Interned{p, put(m, i, h), (i + 1 : U32)}
    case it <> rest Tuple{p, h}:
      intern.go(rest, Ops.intern.keyed(p, key(it)), (i + 1 : U32), put(m, i, h))

def intern(items: List<&2, Ops.Item>, p: Ops.Pool) -> Interned:
  match items:
    case Nil{}:
      Interned{p, UNone{}, 0}
    case it <> rest:
      intern.go(rest, Ops.intern.keyed(p, key(it)), 0, UNone{})

type Sides is Data:
  Sides{s: Seqs, ol: U32, nl: U32}

def sides.fin(oids: UMap, ol: U32, b: Interned) -> Sides:
  match b:
    case Interned{p, nids, nl}:
      Sides{Seqs{oids, nids}, ol, nl}

def sides.of(a: Interned, new: List<&2, Ops.Item>) -> Sides:
  match a:
    case Interned{p, ids, len}:
      sides.fin(ids, len, intern(new, p))

def sides(old: List<&2, Ops.Item>, new: List<&2, Ops.Item>) -> Sides:
  sides.of(intern(old, Ops.pool()), new)

def ops.of(d: Sides) -> List<&2, Op>:
  match d:
    case Sides{+s, +ol, +nl}:
      compact(s, histogram(s, ol, nl), fuel.of(ol, nl))

# `capture_diff_slices(Algorithm::Histogram, old, new)`, before the `Replace`
# hook groups it: every shared run, loss and gain, in order.
def ops(old: List<&2, Ops.Item>, new: List<&2, Ops.Item>) -> List<&2, Op>:
  ops.of(sides(old, new))

# Myers over words
# ----------------

# `capture_diff_slices(Algorithm::Myers, ..)`, which `diff` draws the
# emphasis inside a changed line with: the Myers search behind its own
# preflight, compacted, over whatever the caller numbers.
def intern.words.go(ws: List<&2, String>, r: Ops.Pool & U32, +i: U32, m: UMap) -> Interned:
  match ws r:
    case Nil{} Tuple{p, h}:
      Interned{p, put(m, i, h), (i + 1 : U32)}
    case w <> rest Tuple{p, h}:
      intern.words.go(rest, Ops.intern.keyed(p, w), (i + 1 : U32), put(m, i, h))

def intern.words(ws: List<&2, String>, p: Ops.Pool) -> Interned:
  match ws:
    case Nil{}:
      Interned{p, UNone{}, 0}
    case w <> rest:
      intern.words.go(rest, Ops.intern.keyed(p, w), 0, UNone{})

def words.fin(oids: UMap, ol: U32, b: Interned) -> Sides:
  match b:
    case Interned{p, nids, nl}:
      Sides{Seqs{oids, nids}, ol, nl}

def words.of(a: Interned, new: List<&2, String>) -> Sides:
  match a:
    case Interned{p, ids, len}:
      words.fin(ids, len, intern.words(new, p))

def myers.words.of(d: Sides) -> List<&2, Op>:
  match d:
    case Sides{+s, +ol, +nl}:
      compact(s, List.reverse(&2, Op, myers.diff(s, 0, ol, 0, nl)), fuel.of(ol, nl))

def myers.words(old: List<&2, String>, new: List<&2, String>) -> List<&2, Op>:
  myers.words.of(words.of(intern.words(old, Ops.pool()), new))

# The document
# ------------

# The operations walked over the two item lists, as the moves `Ops.runs`
# groups: a loss and a gain between the same two shared runs are one block,
# anchored where the loss begins — which is what the `Replace` hook makes of
# them, and what `historica::diff` then writes.
type Walked is Data:
  Walked{old: List<&2, Ops.Item>, new: List<&2, Ops.Item>, moves: List<&2, Ops.Move>}

def walked.keep(fuel: Nat, w: Walked) -> Walked:
  match fuel w:
    case 0n Walked{old, new, moves}:
      Walked{old, new, moves}
    case 1n+q Walked{x <> xs, y <> ys, moves}:
      walked.keep(q, Walked{xs, ys, Ops.Keep{} <> moves})
    case 1n+q Walked{old, new, moves}:
      Walked{old, new, moves}

def walked.lose(fuel: Nat, w: Walked) -> Walked:
  match fuel w:
    case 0n Walked{old, new, moves}:
      Walked{old, new, moves}
    case 1n+q Walked{x <> xs, new, moves}:
      walked.lose(q, Walked{xs, new, Ops.Del{x} <> moves})
    case 1n+q Walked{Nil{}, new, moves}:
      Walked{Nil{}, new, moves}

def walked.gain(fuel: Nat, w: Walked) -> Walked:
  match fuel w:
    case 0n Walked{old, new, moves}:
      Walked{old, new, moves}
    case 1n+q Walked{old, y <> ys, moves}:
      walked.gain(q, Walked{old, ys, Ops.Ins{y} <> moves})
    case 1n+q Walked{old, Nil{}, moves}:
      Walked{old, Nil{}, moves}

def walked.go(ops: List<&2, Op>, w: Walked) -> Walked:
  match ops:
    case Nil{}:
      w
    case Same{o, n, len} <> rest:
      walked.go(rest, walked.keep(U32.to_nat(len), w))
    case Lose{o, len, n} <> rest:
      walked.go(rest, walked.lose(U32.to_nat(len), w))
    case Gain{o, n, len} <> rest:
      walked.go(rest, walked.gain(U32.to_nat(len), w))

def walked.moves(w: Walked) -> List<&2, Ops.Move>:
  match w:
    case Walked{old, new, moves}:
      List.reverse(&2, Ops.Move, moves)

# The moves, checked in one pass: a kept line the same on both sides, a
# lost line the parent's, a gained line the child's, and both sides used
# up. Moves that pass take the parent to the child (`LAWS.similar_diff_applies`).
def fit.item(a: Ops.Item, b: Ops.Item) -> Bool:
  match a b:
    case Ops.Item{x, n, f} Ops.Item{y, m, g}:
      Bool.and(String.eq(x, y), Bool.and(Bool.not(Bool.xor(n, m)), Bool.not(Bool.xor(f, g))))

def fit.head(+x: Ops.Item, ys: List<&2, Ops.Item>) -> Bool:
  match ys:
    case Nil{}:
      False{}
    case y <> rest:
      fit.item(x, y)

def fit.agrees(+x: Ops.Item, ys: List<&2, Ops.Item>) -> Bool:
  match ys:
    case Nil{}:
      False{}
    case y <> rest:
      Ops.agrees(x, y)

def fit.kept(xs: List<&2, Ops.Item>, ys: List<&2, Ops.Item>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      fit.head(x, ys)

def fit.tail(xs: List<&2, Ops.Item>) -> List<&2, Ops.Item>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      rest

def fit.empty(xs: List<&2, Ops.Item>, ys: List<&2, Ops.Item>) -> Bool:
  Bool.and(List.is_empty(&2, Ops.Item, xs), List.is_empty(&2, Ops.Item, ys))

def fit(es: List<&2, Ops.Move>, +old: List<&2, Ops.Item>, +new: List<&2, Ops.Item>) -> Bool:
  match es:
    case Nil{}:
      fit.empty(old, new)
    case Ops.Keep{} <> r:
      Bool.and(fit.kept(old, new), fit(r, fit.tail(old), fit.tail(new)))
    case Ops.Del{d} <> r:
      Bool.and(fit.agrees(d, old), fit(r, fit.tail(old), new))
    case Ops.Ins{y} <> r:
      Bool.and(fit.head(y, new), fit(r, old, fit.tail(new)))

# Moves that do not take the parent to the child would be a fault in the
# search above, which the crate's cases have not found; were there one, the
# longest common subsequence `Ops.diff` is proven to take them there.
def diff.checked(+parent: List<&2, Ops.Item>, +child: List<&2, Ops.Item>, moves: List<&2, Ops.Move>, ok: Bool) -> Maybe<&2, Ops.Doc>:
  match ok:
    case True{}:
      Ops.diff.of(Ops.script(Ops.runs(moves, 0n, Nil{}, Nil{}), 0n), Ops.state_digest(child))
    case False{}:
      Ops.diff(parent, child)

def diff.moves(+parent: List<&2, Ops.Item>, +child: List<&2, Ops.Item>, +moves: List<&2, Ops.Move>) -> Maybe<&2, Ops.Doc>:
  diff.checked(parent, child, moves, fit(moves, parent, child))

# The document that takes `parent` to `child`, or None where they agree:
# `historica::diff::diff`.
def diff(+parent: List<&2, Ops.Item>, +child: List<&2, Ops.Item>) -> Maybe<&2, Ops.Doc>:
  diff.moves(parent, child, walked.moves(walked.go(ops(parent, child), Walked{parent, child, Nil{}})))

# A check against the Rust crate
# ------------------------------

def show.op(op: Op) -> String:
  match op:
    case Same{o, n, len}:
      "E" ++ U32.show(o) ++ "," ++ U32.show(n) ++ "," ++ U32.show(len)
    case Lose{o, len, n}:
      "D" ++ U32.show(o) ++ "," ++ U32.show(len) ++ "," ++ U32.show(n)
    case Gain{o, n, len}:
      "I" ++ U32.show(o) ++ "," ++ U32.show(n) ++ "," ++ U32.show(len)

def show.ops(ops: List<&2, Op>) -> String:
  match ops:
    case Nil{}:
      SNil{}
    case op <> Nil{}:
      show.op(op)
    case op <> rest:
      show.op(op) ++ " " ++ show.ops(rest)

def tokens(parts: List<&2, String>, +acc: List<&2, Ops.Item>) -> List<&2, Ops.Item>:
  match parts:
    case Nil{}:
      List.reverse(&2, Ops.Item, acc)
    case +p <> rest:
      tokens(rest, Bool.pick(List<&2, Ops.Item>, String.is_empty(p), acc, Ops.line(p) <> acc))

def spaced(parts: List<&2, String>) -> List<&2, String>:
  match parts:
    case Nil{}:
      Nil{}
    case SNil{} <> rest:
      spaced(rest)
    case p <> rest:
      p <> spaced(rest)

# A line case's operations, and — so that the crate's cases also show the
# fallback in `diff` is never taken — a mark where the moves would not pass
# the check.
def case.lines(+old: List<&2, Ops.Item>, +new: List<&2, Ops.Item>) -> String:
  show.ops(ops(old, new)) ++ Bool.pick(String, fit(walked.moves(walked.go(ops(old, new), Walked{old, new, Nil{}})), old, new), "", " UNFIT")

# A case whose old side begins `M:` asks for Myers over the words, as the
# emphasis inside a changed line does; any other, for Histogram over lines.
def case.both(+a: String, b: String, myers: Bool) -> String:
  match myers:
    case True{}:
      show.ops(myers.words(spaced(String.split(String.drop(a, 2n), ' ')), spaced(String.split(b, ' '))))
    case False{}:
      case.lines(tokens(String.split(a, ' '), Nil{}), tokens(String.split(b, ' '), Nil{}))

def case.of(parts: List<&2, String>) -> String:
  match parts:
    case +a <> b <> Nil{}:
      case.both(a, b, String.starts_with(a, "M:"))
    case _:
      "?"

def cases(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      SNil{}
    case SNil{} <> rest:
      cases(rest)
    case l <> rest:
      case.of(String.split(l, '|')) ++ "\n" ++ cases(rest)

def main.of(args: List<&1, String>) -> IO(Unit):
  match args:
    case Nil{}:
      IO.print("similar.bend <cases>: one `old|new` a line, items spaced")
    case path <> rest:
      do IO<Unit>:
        bs : List<&2, U32> <- Utf8.read_file(path)
        IO.write(cases(String.lines(Utf8.decode(bs))))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    main.of(args)
