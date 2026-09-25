# What `log` presents is what it was shown. The walk that puts the
# revisions newest first — Kahn's algorithm, over a table of how many
# unprinted revisions name each digest as a parent and a table of the
# revisions not yet reached — prints each revision from its frontier, which
# it fills from the list it was given and from that second table, and then
# whatever it never reached, from the list again. So what holds of every
# revision it was shown holds of every revision it presents. The argument
# starts with the table: setting a key never invents a value, and popping
# one gives back a value the table held.
import Base
import ./commands.bend as Main
import ./revision.bend as Rev
import ./composition_lemmas.bend as Comp
import ./anchor_lemmas.bend as AL

# What is carried through the walk, of one revision: that where a filter
# admits it, its digest is one of these.
def ok(+fl: Main.Filter, +L: List<&2, String>, +f: Main.Full) -> Bool:
  Bool.or(Bool.not(Main.keeps(fl, f)), Rev.member(L, Main.id_of(f)))

def every(+fl: Main.Filter, +L: List<&2, String>, fs: List<&2, Main.Full>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case +f <> rest:
      Bool.and(ok(fl, L, f), every(fl, L, rest))

def mok(+fl: Main.Filter, +L: List<&2, String>, m: Maybe<&2, Main.Full>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+f}:
      ok(fl, L, f)

# The table
# ---------

def fok(+fl: Main.Filter, +L: List<&2, String>, m: Map<&2, Main.Full>) -> Bool:
  match m:
    case MTip{}:
      True{}
    case MLeaf{k, +v}:
      ok(fl, L, v)
    case MNode{p, lo, hi}:
      Bool.and(fok(fl, L, lo), fok(fl, L, hi))

def seek.m(r: Map<&2, Main.Full> & String & Maybe<&2, String>) -> Map<&2, Main.Full>:
  match r:
    case (m, rest):
      m

def lo_map(-p2: Nat, -hi: Map<&2, Main.Full>, r0: Map<&2, Main.Full> & String & Maybe<&2, String>) -> {seek.m(Map.lo(&2, Main.Full, String & Maybe<&2, String>, p2, hi, r0)) == MNode{p2, seek.m(r0), hi} : Map<&2, Main.Full>}:
  match r0:
    case (x, y):
      {==}

def hi_map(-p2: Nat, -lo: Map<&2, Main.Full>, r0: Map<&2, Main.Full> & String & Maybe<&2, String>) -> {seek.m(Map.hi(&2, Main.Full, String & Maybe<&2, String>, p2, lo, r0)) == MNode{p2, lo, seek.m(r0)} : Map<&2, Main.Full>}:
  match r0:
    case (x, y):
      {==}

def seek_bit(+fl: Main.Filter, +lo: Map<&2, Main.Full>, +hi: Map<&2, Main.Full>, +p2: Nat, kb: String & Bool, +L: List<&2, String>, +hl: {fok(fl, L, lo) == True{} : Bool}, +hh: {fok(fl, L, hi) == True{} : Bool}, il: @k2: String -> {fok(fl, L, seek.m(Map.seek(&2, Main.Full, lo, k2))) == True{} : Bool}, ih: @k2: String -> {fok(fl, L, seek.m(Map.seek(&2, Main.Full, hi, k2))) == True{} : Bool}) -> {fok(fl, L, seek.m(Map.seek.bit(&2, Main.Full, lo, hi, p2, kb))) == True{} : Bool}:
  match kb:
    case (+key2, b):
      match b:
        case False{}:
          (%Equal.sym(Map<&2, Main.Full>, seek.m(Map.lo(&2, Main.Full, String & Maybe<&2, String>, p2, hi, Map.seek(&2, Main.Full, lo, key2))), MNode{p2, seek.m(Map.seek(&2, Main.Full, lo, key2)), hi}, lo_map(p2, hi, Map.seek(&2, Main.Full, lo, key2))) : {fok(fl, L, _) == True{} : Bool}
            AL.and_intro(fok(fl, L, seek.m(Map.seek(&2, Main.Full, lo, key2))), fok(fl, L, hi), il(key2), hh))
        case True{}:
          (%Equal.sym(Map<&2, Main.Full>, seek.m(Map.hi(&2, Main.Full, String & Maybe<&2, String>, p2, lo, Map.seek(&2, Main.Full, hi, key2))), MNode{p2, lo, seek.m(Map.seek(&2, Main.Full, hi, key2))}, hi_map(p2, lo, Map.seek(&2, Main.Full, hi, key2))) : {fok(fl, L, _) == True{} : Bool}
            AL.and_intro(fok(fl, L, lo), fok(fl, L, seek.m(Map.seek(&2, Main.Full, hi, key2))), hl, ih(key2)))

# Seeking a key gives the map back as it was.
def seek_ok(+fl: Main.Filter, m: Map<&2, Main.Full>, +key: String, +L: List<&2, String>, +h: {fok(fl, L, m) == True{} : Bool}) -> {fok(fl, L, seek.m(Map.seek(&2, Main.Full, m, key))) == True{} : Bool}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k, +v}:
      h
    case MNode{+pos, +lo, +hi}:
      seek_bit(fl, lo, hi, pos, Map.bit(key, pos), L, Comp.and_left(fok(fl, L, lo), fok(fl, L, hi), h), Comp.and_right(fok(fl, L, lo), fok(fl, L, hi), h),
        k2 => seek_ok(fl, lo, k2, L, Comp.and_left(fok(fl, L, lo), fok(fl, L, hi), h)),
        k2 => seek_ok(fl, hi, k2, L, Comp.and_right(fok(fl, L, lo), fok(fl, L, hi), h)))

def splice_bit_ok(+fl: Main.Filter, +x: Main.Full, +rest: Map<&2, Main.Full>, +pb: Nat, kb: String & Bool, +L: List<&2, String>, +hr: {fok(fl, L, rest) == True{} : Bool}, +hx: {ok(fl, L, x) == True{} : Bool}) -> {fok(fl, L, Map.ins.splice.bit(&2, Main.Full, x, rest, pb, kb)) == True{} : Bool}:
  match kb:
    case (key2, b):
      match b:
        case False{}:
          AL.and_intro(ok(fl, L, x), fok(fl, L, rest), hx, hr)
        case True{}:
          AL.and_intro(fok(fl, L, rest), ok(fl, L, x), hr, hx)

def splice_ok(+fl: Main.Filter, +p: Nat, +key: String, +x: Main.Full, +rest: Map<&2, Main.Full>, +L: List<&2, String>, +hr: {fok(fl, L, rest) == True{} : Bool}, +hx: {ok(fl, L, x) == True{} : Bool}) -> {fok(fl, L, Map.ins.splice(&2, Main.Full, p, key, x, rest)) == True{} : Bool}:
  splice_bit_ok(fl, x, rest, p, Map.bit(key, p), L, hr, hx)

def deep_ok(+fl: Main.Filter, +x: Main.Full, +lo: Map<&2, Main.Full>, +hi: Map<&2, Main.Full>, +pb: Nat, +qb: Nat, kb: String & Bool, +L: List<&2, String>, +hl: {fok(fl, L, lo) == True{} : Bool}, +hh: {fok(fl, L, hi) == True{} : Bool}, il: @k2: String -> {fok(fl, L, Map.ins(&2, Main.Full, lo, k2, x, pb)) == True{} : Bool}, ih: @k2: String -> {fok(fl, L, Map.ins(&2, Main.Full, hi, k2, x, pb)) == True{} : Bool}) -> {fok(fl, L, Map.ins.deep(&2, Main.Full, x, lo, hi, pb, qb, kb)) == True{} : Bool}:
  match kb:
    case (+key2, b):
      match b:
        case False{}:
          AL.and_intro(fok(fl, L, Map.ins(&2, Main.Full, lo, key2, x, pb)), fok(fl, L, hi), il(key2), hh)
        case True{}:
          AL.and_intro(fok(fl, L, lo), fok(fl, L, Map.ins(&2, Main.Full, hi, key2, x, pb)), hl, ih(key2))

def ins_if_ok(+fl: Main.Filter, +key: String, +x: Main.Full, +lo: Map<&2, Main.Full>, +hi: Map<&2, Main.Full>, +p2: Nat, +pb: Nat, t: Bool, +L: List<&2, String>, +hl: {fok(fl, L, lo) == True{} : Bool}, +hh: {fok(fl, L, hi) == True{} : Bool}, +hx: {ok(fl, L, x) == True{} : Bool}, il: @k2: String -> {fok(fl, L, Map.ins(&2, Main.Full, lo, k2, x, pb)) == True{} : Bool}, ih: @k2: String -> {fok(fl, L, Map.ins(&2, Main.Full, hi, k2, x, pb)) == True{} : Bool}) -> {fok(fl, L, Map.ins.if(&2, Main.Full, key, x, lo, hi, p2, pb, t)) == True{} : Bool}:
  match t:
    case False{}:
      splice_ok(fl, pb, key, x, MNode{p2, lo, hi}, L, AL.and_intro(fok(fl, L, lo), fok(fl, L, hi), hl, hh), hx)
    case True{}:
      deep_ok(fl, x, lo, hi, pb, p2, Map.bit(key, p2), L, hl, hh, il, ih)

def ins_ok(+fl: Main.Filter, m: Map<&2, Main.Full>, +key: String, +x: Main.Full, +p: Nat, +L: List<&2, String>, +h: {fok(fl, L, m) == True{} : Bool}, +hx: {ok(fl, L, x) == True{} : Bool}) -> {fok(fl, L, Map.ins(&2, Main.Full, m, key, x, p)) == True{} : Bool}:
  match m:
    case MTip{}:
      hx
    case MLeaf{+k, +v}:
      splice_ok(fl, p, key, x, MLeaf{k, v}, L, h, hx)
    case MNode{+pos, +lo, +hi}:
      ins_if_ok(fl, key, x, lo, hi, pos, p, Nat.is_lt(pos, p), L, Comp.and_left(fok(fl, L, lo), fok(fl, L, hi), h), Comp.and_right(fok(fl, L, lo), fok(fl, L, hi), h), hx,
        k2 => ins_ok(fl, lo, k2, x, p, L, Comp.and_left(fok(fl, L, lo), fok(fl, L, hi), h), hx),
        k2 => ins_ok(fl, hi, k2, x, p, L, Comp.and_right(fok(fl, L, lo), fok(fl, L, hi), h), hx))

def put_bit_ok(+fl: Main.Filter, +x: Main.Full, +p2: Nat, +lo: Map<&2, Main.Full>, +hi: Map<&2, Main.Full>, kb: String & Bool, +L: List<&2, String>, +hl: {fok(fl, L, lo) == True{} : Bool}, +hh: {fok(fl, L, hi) == True{} : Bool}, il: @k2: String -> {fok(fl, L, Map.put(&2, Main.Full, lo, k2, x)) == True{} : Bool}, ih: @k2: String -> {fok(fl, L, Map.put(&2, Main.Full, hi, k2, x)) == True{} : Bool}) -> {fok(fl, L, Map.put.bit(&2, Main.Full, x, p2, lo, hi, kb)) == True{} : Bool}:
  match kb:
    case (+key2, b):
      match b:
        case False{}:
          AL.and_intro(fok(fl, L, Map.put(&2, Main.Full, lo, key2, x)), fok(fl, L, hi), il(key2), hh)
        case True{}:
          AL.and_intro(fok(fl, L, lo), fok(fl, L, Map.put(&2, Main.Full, hi, key2, x)), hl, ih(key2))

def put_ok(+fl: Main.Filter, m: Map<&2, Main.Full>, +key: String, +x: Main.Full, +L: List<&2, String>, +h: {fok(fl, L, m) == True{} : Bool}, +hx: {ok(fl, L, x) == True{} : Bool}) -> {fok(fl, L, Map.put(&2, Main.Full, m, key, x)) == True{} : Bool}:
  match m:
    case MTip{}:
      hx
    case MLeaf{k, v}:
      hx
    case MNode{+pos, +lo, +hi}:
      put_bit_ok(fl, x, pos, lo, hi, Map.bit(key, pos), L, Comp.and_left(fok(fl, L, lo), fok(fl, L, hi), h), Comp.and_right(fok(fl, L, lo), fok(fl, L, hi), h),
        k2 => put_ok(fl, lo, k2, x, L, Comp.and_left(fok(fl, L, lo), fok(fl, L, hi), h), hx),
        k2 => put_ok(fl, hi, k2, x, L, Comp.and_right(fok(fl, L, lo), fok(fl, L, hi), h), hx))

def fin_ok(+fl: Main.Filter, +m: Map<&2, Main.Full>, +key: String, +x: Main.Full, r: (String & String) & Cmp, +L: List<&2, String>, +h: {fok(fl, L, m) == True{} : Bool}, +hx: {ok(fl, L, x) == True{} : Bool}) -> {fok(fl, L, Map.set.fin.go(&2, Main.Full, m, key, x, r)) == True{} : Bool}:
  match r:
    case (kk, c):
      match kk:
        case (kb2, k2):
          match c:
            case LT{}:
              ins_ok(fl, m, key, x, Map.diff(kb2, k2), L, h, hx)
            case EQ{}:
              put_ok(fl, m, key, x, L, h, hx)
            case GT{}:
              ins_ok(fl, m, key, x, Map.diff(kb2, k2), L, h, hx)

def set_go_ok(+fl: Main.Filter, +x: Main.Full, r: Map<&2, Main.Full> & String & Maybe<&2, String>, +L: List<&2, String>, hr: {fok(fl, L, seek.m(r)) == True{} : Bool}, +hx: {ok(fl, L, x) == True{} : Bool}) -> {fok(fl, L, Map.set.go(&2, Main.Full, x, r)) == True{} : Bool}:
  match r:
    case (m2, rest):
      match rest:
        case (+key2, found):
          match found:
            case None{}:
              hx
            case Some{k}:
              fin_ok(fl, m2, key2, x, String.cmp(key2, k), L, hr, hx)

# Setting a key never invents a revision.
def set_ok(+fl: Main.Filter, +m: Map<&2, Main.Full>, +key: String, +x: Main.Full, +L: List<&2, String>, +h: {fok(fl, L, m) == True{} : Bool}, +hx: {ok(fl, L, x) == True{} : Bool}) -> {fok(fl, L, Map.set(&2, Main.Full, m, key, x)) == True{} : Bool}:
  set_go_ok(fl, x, Map.seek(&2, Main.Full, m, key), L, seek_ok(fl, m, key, L, h), hx)

# Popping a key gives back a table that holds only what it held, and a
# value it held.
def pok(+fl: Main.Filter, +L: List<&2, String>, r: Map<&2, Main.Full> & Maybe<&2, Main.Full>) -> Bool:
  match r:
    case (m, f):
      Bool.and(fok(fl, L, m), mok(fl, L, f))

def pop_leaf_ok(+fl: Main.Filter, +L: List<&2, String>, +v: Main.Full, r: (String & String) & Cmp, +hv: {ok(fl, L, v) == True{} : Bool}) -> {pok(fl, L, Map.pop.leaf(&2, Main.Full, v, r)) == True{} : Bool}:
  match r:
    case (kk, c):
      match kk:
        case (key2, k2):
          match c:
            case LT{}:
              AL.and_intro(ok(fl, L, v), True{}, hv, {==})
            case EQ{}:
              hv
            case GT{}:
              AL.and_intro(ok(fl, L, v), True{}, hv, {==})

def pop_lo_ok(+fl: Main.Filter, +L: List<&2, String>, +pos: Nat, +hi: Map<&2, Main.Full>, r0: Map<&2, Main.Full> & Maybe<&2, Main.Full>, +hh: {fok(fl, L, hi) == True{} : Bool}, +h0: {pok(fl, L, r0) == True{} : Bool}) -> {pok(fl, L, Map.pop.lo(&2, Main.Full, pos, hi, r0)) == True{} : Bool}:
  match r0:
    case (+lo, +r):
      match lo:
        case MTip{}:
          AL.and_intro(fok(fl, L, hi), mok(fl, L, r), hh, h0)
        case MLeaf{+k, +v}:
          AL.and_intro(Bool.and(ok(fl, L, v), fok(fl, L, hi)), mok(fl, L, r),
            AL.and_intro(ok(fl, L, v), fok(fl, L, hi), Comp.and_left(ok(fl, L, v), mok(fl, L, r), h0), hh),
            Comp.and_right(ok(fl, L, v), mok(fl, L, r), h0))
        case MNode{+p, +a, +b}:
          AL.and_intro(Bool.and(Bool.and(fok(fl, L, a), fok(fl, L, b)), fok(fl, L, hi)), mok(fl, L, r),
            AL.and_intro(Bool.and(fok(fl, L, a), fok(fl, L, b)), fok(fl, L, hi), Comp.and_left(Bool.and(fok(fl, L, a), fok(fl, L, b)), mok(fl, L, r), h0), hh),
            Comp.and_right(Bool.and(fok(fl, L, a), fok(fl, L, b)), mok(fl, L, r), h0))

def pop_hi_ok(+fl: Main.Filter, +L: List<&2, String>, +pos: Nat, +lo: Map<&2, Main.Full>, r0: Map<&2, Main.Full> & Maybe<&2, Main.Full>, +hl: {fok(fl, L, lo) == True{} : Bool}, +h0: {pok(fl, L, r0) == True{} : Bool}) -> {pok(fl, L, Map.pop.hi(&2, Main.Full, pos, lo, r0)) == True{} : Bool}:
  match r0:
    case (+hi, +r):
      match hi:
        case MTip{}:
          AL.and_intro(fok(fl, L, lo), mok(fl, L, r), hl, h0)
        case MLeaf{+k, +v}:
          AL.and_intro(Bool.and(fok(fl, L, lo), ok(fl, L, v)), mok(fl, L, r),
            AL.and_intro(fok(fl, L, lo), ok(fl, L, v), hl, Comp.and_left(ok(fl, L, v), mok(fl, L, r), h0)),
            Comp.and_right(ok(fl, L, v), mok(fl, L, r), h0))
        case MNode{+p, +a, +b}:
          AL.and_intro(Bool.and(fok(fl, L, lo), Bool.and(fok(fl, L, a), fok(fl, L, b))), mok(fl, L, r),
            AL.and_intro(fok(fl, L, lo), Bool.and(fok(fl, L, a), fok(fl, L, b)), hl, Comp.and_left(Bool.and(fok(fl, L, a), fok(fl, L, b)), mok(fl, L, r), h0)),
            Comp.and_right(Bool.and(fok(fl, L, a), fok(fl, L, b)), mok(fl, L, r), h0))

def pop_bit_ok(+fl: Main.Filter, +L: List<&2, String>, +lo: Map<&2, Main.Full>, +hi: Map<&2, Main.Full>, +p2: Nat, kb: String & Bool, +hl: {fok(fl, L, lo) == True{} : Bool}, +hh: {fok(fl, L, hi) == True{} : Bool}, il: @k2: String -> {pok(fl, L, Map.pop(&2, Main.Full, lo, k2)) == True{} : Bool}, ih: @k2: String -> {pok(fl, L, Map.pop(&2, Main.Full, hi, k2)) == True{} : Bool}) -> {pok(fl, L, Map.pop.bit(&2, Main.Full, lo, hi, p2, kb)) == True{} : Bool}:
  match kb:
    case (+key2, b):
      match b:
        case False{}:
          pop_lo_ok(fl, L, p2, hi, Map.pop(&2, Main.Full, lo, key2), hh, il(key2))
        case True{}:
          pop_hi_ok(fl, L, p2, lo, Map.pop(&2, Main.Full, hi, key2), hl, ih(key2))

def pop_ok(+fl: Main.Filter, +L: List<&2, String>, m: Map<&2, Main.Full>, +key: String, +h: {fok(fl, L, m) == True{} : Bool}) -> {pok(fl, L, Map.pop(&2, Main.Full, m, key)) == True{} : Bool}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k, +v}:
      pop_leaf_ok(fl, L, v, String.cmp(key, k), h)
    case MNode{+pos, +lo, +hi}:
      pop_bit_ok(fl, L, lo, hi, pos, Map.bit(key, pos), Comp.and_left(fok(fl, L, lo), fok(fl, L, hi), h), Comp.and_right(fok(fl, L, lo), fok(fl, L, hi), h),
        k2 => pop_ok(fl, L, lo, k2, Comp.and_left(fok(fl, L, lo), fok(fl, L, hi), h)),
        k2 => pop_ok(fl, L, hi, k2, Comp.and_right(fok(fl, L, lo), fok(fl, L, hi), h)))

# Lists
# -----

def app_ok(+fl: Main.Filter, +L: List<&2, String>, xs: List<&2, Main.Full>, +ys: List<&2, Main.Full>, +hx: {every(fl, L, xs) == True{} : Bool}, +hy: {every(fl, L, ys) == True{} : Bool}) -> {every(fl, L, List.append(&2, Main.Full, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +x <> +rest:
      AL.and_intro(ok(fl, L, x), every(fl, L, List.append(&2, Main.Full, rest, ys)), Comp.and_left(ok(fl, L, x), every(fl, L, rest), hx), app_ok(fl, L, rest, ys, Comp.and_right(ok(fl, L, x), every(fl, L, rest), hx), hy))

def revgo_ok(+fl: Main.Filter, +L: List<&2, String>, xs: List<&2, Main.Full>, +acc: List<&2, Main.Full>, +hx: {every(fl, L, xs) == True{} : Bool}, +ha: {every(fl, L, acc) == True{} : Bool}) -> {every(fl, L, List.reverse.go(&2, Main.Full, xs, acc)) == True{} : Bool}:
  match xs:
    case Nil{}:
      ha
    case +x <> +rest:
      revgo_ok(fl, L, rest, x <> acc, Comp.and_right(ok(fl, L, x), every(fl, L, rest), hx), AL.and_intro(ok(fl, L, x), every(fl, L, acc), Comp.and_left(ok(fl, L, x), every(fl, L, rest), hx), ha))

def keep_full_ok(+fl: Main.Filter, +L: List<&2, String>, b: Bool, +f: Main.Full, +rest: List<&2, Main.Full>, +hf: {ok(fl, L, f) == True{} : Bool}, +hr: {every(fl, L, rest) == True{} : Bool}) -> {every(fl, L, Main.keep_full(b, f, rest)) == True{} : Bool}:
  match b:
    case True{}:
      AL.and_intro(ok(fl, L, f), every(fl, L, rest), hf, hr)
    case False{}:
      hr

# What one step of a walk keeps or passes over, by what a set answers.
def keep_by_ok(+fl: Main.Filter, +L: List<&2, String>, +f: Main.Full, +rest: List<&2, Main.Full>, r: Set() & Bool, +hf: {ok(fl, L, f) == True{} : Bool}, +hr: {every(fl, L, rest) == True{} : Bool}) -> {every(fl, L, Main.ready.keep(f, rest, r)) == True{} : Bool}:
  match r:
    case (s, b):
      match b:
        case True{}:
          hr
        case False{}:
          AL.and_intro(ok(fl, L, f), every(fl, L, rest), hf, hr)

def left_by_ok(+fl: Main.Filter, +L: List<&2, String>, +f: Main.Full, +rest: List<&2, Main.Full>, r: Set() & Bool, +hf: {ok(fl, L, f) == True{} : Bool}, +hr: {every(fl, L, rest) == True{} : Bool}) -> {every(fl, L, Main.presentation.left.keep(f, rest, r)) == True{} : Bool}:
  match r:
    case (s, b):
      match b:
        case True{}:
          hr
        case False{}:
          AL.and_intro(ok(fl, L, f), every(fl, L, rest), hf, hr)

def remove_ok(+fl: Main.Filter, +L: List<&2, String>, fs: List<&2, Main.Full>, +id: String, +h: {every(fl, L, fs) == True{} : Bool}) -> {every(fl, L, Main.remove(fs, id)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Main.Full{+i, +change, +parents, +supersedes, +author, +when, +revised_by, +revised, +facts, +message} <> +rest:
      keep_full_ok(fl, L, Bool.not(String.eq(i, id)), Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}, Main.remove(rest, id),
        Comp.and_left(ok(fl, L, Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}), every(fl, L, rest), h),
        remove_ok(fl, L, rest, id, Comp.and_right(ok(fl, L, Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}), every(fl, L, rest), h)))

def ready_go_ok(+fl: Main.Filter, +L: List<&2, String>, fs: List<&2, Main.Full>, +named: Set(), +h: {every(fl, L, fs) == True{} : Bool}) -> {every(fl, L, Main.ready.go(fs, named)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Main.Full{+id, +change, +parents, +supersedes, +author, +when, +revised_by, +revised, +facts, +message} <> +rest:
      keep_by_ok(fl, L, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}, Main.ready.go(rest, named), Set.has(named, id),
        Comp.and_left(ok(fl, L, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}), every(fl, L, rest), h),
        ready_go_ok(fl, L, rest, named, Comp.and_right(ok(fl, L, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}), every(fl, L, rest), h)))

def left_ok(+fl: Main.Filter, +L: List<&2, String>, fs: List<&2, Main.Full>, +done: Set(), +h: {every(fl, L, fs) == True{} : Bool}) -> {every(fl, L, Main.presentation.left(fs, done)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Main.Full{+id, +change, +parents, +supersedes, +author, +when, +revised_by, +revised, +facts, +message} <> +rest:
      left_by_ok(fl, L, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}, Main.presentation.left(rest, done), Set.has(done, id),
        Comp.and_left(ok(fl, L, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}), every(fl, L, rest), h),
        left_ok(fl, L, rest, done, Comp.and_right(ok(fl, L, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}), every(fl, L, rest), h)))

def pick_full_ok(+fl: Main.Filter, +L: List<&2, String>, c: Bool, +f: Main.Full, +g: Main.Full, +hf: {ok(fl, L, f) == True{} : Bool}, +hg: {ok(fl, L, g) == True{} : Bool}) -> {ok(fl, L, Bool.pick(Main.Full, c, f, g)) == True{} : Bool}:
  match c:
    case True{}:
      hf
    case False{}:
      hg

def latest_go_ok(+fl: Main.Filter, +L: List<&2, String>, fs: List<&2, Main.Full>, +best: Main.Full, +hb: {ok(fl, L, best) == True{} : Bool}, +h: {every(fl, L, fs) == True{} : Bool}) -> {ok(fl, L, Main.latest.go(fs, best)) == True{} : Bool}:
  match fs:
    case Nil{}:
      hb
    case +f <> +rest:
      latest_go_ok(fl, L, rest, Bool.pick(Main.Full, Main.later(f, best), f, best), pick_full_ok(fl, L, Main.later(f, best), f, best, Comp.and_left(ok(fl, L, f), every(fl, L, rest), h), hb), Comp.and_right(ok(fl, L, f), every(fl, L, rest), h))

# The latest of the frontier is one of it.
def latest_ok(+fl: Main.Filter, +L: List<&2, String>, fs: List<&2, Main.Full>, +h: {every(fl, L, fs) == True{} : Bool}) -> {mok(fl, L, Main.latest(fs)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +rest:
      latest_go_ok(fl, L, rest, f, Comp.and_left(ok(fl, L, f), every(fl, L, rest), h), Comp.and_right(ok(fl, L, f), every(fl, L, rest), h))

# The walk
# --------

def dok(+fl: Main.Filter, +L: List<&2, String>, d: Main.Drop) -> Bool:
  match d:
    case Main.Drop{counts, waiting, ready}:
      Bool.and(fok(fl, L, waiting), every(fl, L, ready))

def wok(+fl: Main.Filter, +L: List<&2, String>, w: Main.Walk) -> Bool:
  match w:
    case Main.Walk{ready, printed, counts, waiting}:
      Bool.and(Bool.and(every(fl, L, ready), every(fl, L, printed)), fok(fl, L, waiting))

def waiting_ok(+fl: Main.Filter, +L: List<&2, String>, fs: List<&2, Main.Full>, +m: Map<&2, Main.Full>, +hm: {fok(fl, L, m) == True{} : Bool}, +h: {every(fl, L, fs) == True{} : Bool}) -> {fok(fl, L, Main.waiting.go(fs, m)) == True{} : Bool}:
  match fs:
    case Nil{}:
      hm
    case +f <> +rest:
      waiting_ok(fl, L, rest, Map.set(&2, Main.Full, m, Main.id_of(f), f), set_ok(fl, m, Main.id_of(f), f, L, hm, Comp.and_left(ok(fl, L, f), every(fl, L, rest), h)), Comp.and_right(ok(fl, L, f), every(fl, L, rest), h))

# A parent whose last child went out arrives from the table.
def arrive_ok(+fl: Main.Filter, +L: List<&2, String>, -counts: Map<&2, Nat>, +rd: List<&2, Main.Full>, r: Map<&2, Main.Full> & Maybe<&2, Main.Full>, +hr: {pok(fl, L, r) == True{} : Bool}, +h: {every(fl, L, rd) == True{} : Bool}) -> {dok(fl, L, Main.walk.arrive(counts, rd, r)) == True{} : Bool}:
  match r:
    case (+m, f):
      match f:
        case None{}:
          AL.and_intro(fok(fl, L, m), every(fl, L, rd), Comp.and_left(fok(fl, L, m), True{}, hr), h)
        case Some{+x}:
          AL.and_intro(fok(fl, L, m), Bool.and(ok(fl, L, x), every(fl, L, rd)), Comp.and_left(fok(fl, L, m), ok(fl, L, x), hr),
            AL.and_intro(ok(fl, L, x), every(fl, L, rd), Comp.and_right(fok(fl, L, m), ok(fl, L, x), hr), h))

def zero_ok(+fl: Main.Filter, +L: List<&2, String>, +key: String, -counts: Map<&2, Nat>, +waiting: Map<&2, Main.Full>, +rd: List<&2, Main.Full>, n: Nat, +hw: {fok(fl, L, waiting) == True{} : Bool}, +h: {every(fl, L, rd) == True{} : Bool}) -> {dok(fl, L, Main.walk.zero(key, counts, waiting, rd, n)) == True{} : Bool}:
  match n:
    case 0n:
      arrive_ok(fl, L, counts, rd, Map.pop(&2, Main.Full, waiting, key), pop_ok(fl, L, waiting, key, hw), h)
    case 1n+k:
      AL.and_intro(fok(fl, L, waiting), every(fl, L, rd), hw, h)

def dec_ok(+fl: Main.Filter, +L: List<&2, String>, +key: String, +waiting: Map<&2, Main.Full>, +rd: List<&2, Main.Full>, r: Map<&2, Nat> & Nat, +hw: {fok(fl, L, waiting) == True{} : Bool}, +h: {every(fl, L, rd) == True{} : Bool}) -> {dok(fl, L, Main.walk.dec(key, waiting, rd, r)) == True{} : Bool}:
  match r:
    case (m, n):
      match n:
        case 0n:
          AL.and_intro(fok(fl, L, waiting), every(fl, L, rd), hw, h)
        case 1n+k:
          zero_ok(fl, L, key, Map.set(&2, Nat, m, key, k), waiting, rd, k, hw, h)

# Every parent of the revision printed counted down, the table and the
# frontier still hold only what they held.
def parents_ok(+fl: Main.Filter, +L: List<&2, String>, ps: List<&2, String>, d: Main.Drop, +hd: {dok(fl, L, d) == True{} : Bool}) -> {dok(fl, L, Main.walk.parents(ps, d)) == True{} : Bool}:
  match ps:
    case Nil{}:
      hd
    case +p <> rest:
      match d:
        case Main.Drop{+counts, +waiting, +rd}:
          parents_ok(fl, L, rest, Main.walk.dec(p, waiting, rd, Map.get(Nat, 0n, counts, p)),
            dec_ok(fl, L, p, waiting, rd, Map.get(Nat, 0n, counts, p), Comp.and_left(fok(fl, L, waiting), every(fl, L, rd), hd), Comp.and_right(fok(fl, L, waiting), every(fl, L, rd), hd)))

def went_ok(+fl: Main.Filter, +L: List<&2, String>, +printed: List<&2, Main.Full>, d: Main.Drop, +hp: {every(fl, L, printed) == True{} : Bool}, +hd: {dok(fl, L, d) == True{} : Bool}) -> {wok(fl, L, Main.walk.went(printed, d)) == True{} : Bool}:
  match d:
    case Main.Drop{+counts, +waiting, +rd}:
      AL.and_intro(Bool.and(every(fl, L, rd), every(fl, L, printed)), fok(fl, L, waiting),
        AL.and_intro(every(fl, L, rd), every(fl, L, printed), Comp.and_right(fok(fl, L, waiting), every(fl, L, rd), hd), hp),
        Comp.and_left(fok(fl, L, waiting), every(fl, L, rd), hd))

def take_ok(+fl: Main.Filter, +L: List<&2, String>, +f: Main.Full, +ready: List<&2, Main.Full>, +printed: List<&2, Main.Full>, +counts: Map<&2, Nat>, +waiting: Map<&2, Main.Full>, +hf: {ok(fl, L, f) == True{} : Bool}, +hr: {every(fl, L, ready) == True{} : Bool}, +hp: {every(fl, L, printed) == True{} : Bool}, +hw: {fok(fl, L, waiting) == True{} : Bool}) -> {wok(fl, L, Main.walk.take(f, ready, printed, counts, waiting)) == True{} : Bool}:
  went_ok(fl, L, f <> printed, Main.walk.parents(Main.parents_of(f), Main.Drop{counts, waiting, Main.remove(ready, Main.id_of(f))}),
    AL.and_intro(ok(fl, L, f), every(fl, L, printed), hf, hp),
    parents_ok(fl, L, Main.parents_of(f), Main.Drop{counts, waiting, Main.remove(ready, Main.id_of(f))},
      AL.and_intro(fok(fl, L, waiting), every(fl, L, Main.remove(ready, Main.id_of(f))), hw, remove_ok(fl, L, ready, Main.id_of(f), hr))))

def pick_ok(+fl: Main.Filter, +L: List<&2, String>, +ready: List<&2, Main.Full>, +printed: List<&2, Main.Full>, +counts: Map<&2, Nat>, +waiting: Map<&2, Main.Full>, pick: Maybe<&2, Main.Full>, +hm: {mok(fl, L, pick) == True{} : Bool}, +hr: {every(fl, L, ready) == True{} : Bool}, +hp: {every(fl, L, printed) == True{} : Bool}, +hw: {fok(fl, L, waiting) == True{} : Bool}) -> {wok(fl, L, Main.walk.pick(ready, printed, counts, waiting, pick)) == True{} : Bool}:
  match pick:
    case None{}:
      AL.and_intro(every(fl, L, printed), fok(fl, L, waiting), hp, hw)
    case Some{+f}:
      take_ok(fl, L, f, ready, printed, counts, waiting, hm, hr, hp, hw)

def step_ok(+fl: Main.Filter, +L: List<&2, String>, w: Main.Walk, +h: {wok(fl, L, w) == True{} : Bool}) -> {wok(fl, L, Main.presentation.step(w)) == True{} : Bool}:
  match w:
    case Main.Walk{+ready, +printed, +counts, +waiting}:
      pick_ok(fl, L, ready, printed, counts, waiting, Main.latest(ready),
        latest_ok(fl, L, ready, Comp.and_left(every(fl, L, ready), every(fl, L, printed), Comp.and_left(Bool.and(every(fl, L, ready), every(fl, L, printed)), fok(fl, L, waiting), h))),
        Comp.and_left(every(fl, L, ready), every(fl, L, printed), Comp.and_left(Bool.and(every(fl, L, ready), every(fl, L, printed)), fok(fl, L, waiting), h)),
        Comp.and_right(every(fl, L, ready), every(fl, L, printed), Comp.and_left(Bool.and(every(fl, L, ready), every(fl, L, printed)), fok(fl, L, waiting), h)),
        Comp.and_right(Bool.and(every(fl, L, ready), every(fl, L, printed)), fok(fl, L, waiting), h))

def go_ok(+fl: Main.Filter, +L: List<&2, String>, fuel: Nat, +w: Main.Walk, +h: {wok(fl, L, w) == True{} : Bool}) -> {wok(fl, L, Main.presentation.go(fuel, w)) == True{} : Bool}:
  match fuel:
    case 0n:
      h
    case 1n+n:
      go_ok(fl, L, n, Main.presentation.step(w), step_ok(fl, L, w, h))

def printed_ok(+fl: Main.Filter, +L: List<&2, String>, w: Main.Walk, +h: {wok(fl, L, w) == True{} : Bool}) -> {every(fl, L, Main.presentation.printed(w)) == True{} : Bool}:
  match w:
    case Main.Walk{+ready, +printed, +counts, +waiting}:
      Comp.and_right(every(fl, L, ready), every(fl, L, printed), Comp.and_left(Bool.and(every(fl, L, ready), every(fl, L, printed)), fok(fl, L, waiting), h))

# What the walk printed, oldest last, then what it never reached.
def done_ok(+fl: Main.Filter, +L: List<&2, String>, +fs: List<&2, Main.Full>, +printed: List<&2, Main.Full>, +hf: {every(fl, L, fs) == True{} : Bool}, +hp: {every(fl, L, printed) == True{} : Bool}) -> {every(fl, L, Main.presentation.done(fs, printed)) == True{} : Bool}:
  app_ok(fl, L, List.reverse(&2, Main.Full, printed), Main.presentation.left(fs, Set.from_list(Main.ids(printed))),
    revgo_ok(fl, L, printed, Nil{}, hp, {==}),
    left_ok(fl, L, fs, Set.from_list(Main.ids(printed)), hf))

def of_ok(+fl: Main.Filter, +L: List<&2, String>, +fs: List<&2, Main.Full>, +ready: List<&2, Main.Full>, +hf: {every(fl, L, fs) == True{} : Bool}, +hr: {every(fl, L, ready) == True{} : Bool}) -> {every(fl, L, Main.presentation.of(fs, ready)) == True{} : Bool}:
  done_ok(fl, L, fs, Main.presentation.printed(Main.presentation.go(1n+List.length(&2, Main.Full, fs), Main.Walk{ready, Nil{}, Main.counts(fs), Main.waiting(fs)})), hf,
    printed_ok(fl, L, Main.presentation.go(1n+List.length(&2, Main.Full, fs), Main.Walk{ready, Nil{}, Main.counts(fs), Main.waiting(fs)}),
      go_ok(fl, L, 1n+List.length(&2, Main.Full, fs), Main.Walk{ready, Nil{}, Main.counts(fs), Main.waiting(fs)},
        AL.and_intro(Bool.and(every(fl, L, ready), True{}), fok(fl, L, Main.waiting(fs)),
          AL.and_intro(every(fl, L, ready), True{}, hr, {==}),
          waiting_ok(fl, L, fs, Map.new(&2, Main.Full), {==}, hf)))))

# Whatever holds of every revision `log` was shown holds of every revision
# it presents.
def presentation_ok(+fl: Main.Filter, +L: List<&2, String>, +fs: List<&2, Main.Full>, +h: {every(fl, L, fs) == True{} : Bool}) -> {every(fl, L, Main.presentation(fs)) == True{} : Bool}:
  of_ok(fl, L, fs, Main.ready(fs, fs), h, ready_go_ok(fl, L, fs, Set.from_list(Main.parents_named(fs)), h))
