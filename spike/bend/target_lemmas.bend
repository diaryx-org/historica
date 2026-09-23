# Every target names a revision the store holds. A target is a bookmark,
# `head`, a digest prefix or a change prefix; whichever it is, the revision
# it resolves to is one of the store's. The history the tool asks about heads
# and changes is a `Map` from digest to revision, so the argument starts
# with the map: setting a key never invents a value, so every revision the
# history holds is one the store's list held.
import Base
import ./revision.bend as Rev
import ./tree.bend as T
import ./text.bend as Tx
import ./bookmark.bend as Bm
import ./ident.bend as Id
import ./main.bend as Main
import ./string_lemmas.bend as S
import ./graph_lemmas.bend as GL
import ./composition_lemmas.bend as Comp
import ./anchor_lemmas.bend as AL

# The map
# -------

# Every revision a map holds has a digest in `L`.
def hok(m: Map<&2, Rev.Revision>, +L: List<&2, String>) -> Bool:
  match m:
    case MTip{}:
      True{}
    case MLeaf{k, v}:
      Rev.member(L, Rev.id_of(v))
    case MNode{p, lo, hi}:
      Bool.and(hok(lo, L), hok(hi, L))

def seek.m(r: Map<&2, Rev.Revision> & String & Maybe<&2, String>) -> Map<&2, Rev.Revision>:
  match r:
    case (m, rest):
      m

def lo_map(-p2: Nat, -hi: Map<&2, Rev.Revision>, r0: Map<&2, Rev.Revision> & String & Maybe<&2, String>) -> {seek.m(Map.lo(&2, Rev.Revision, String & Maybe<&2, String>, p2, hi, r0)) == MNode{p2, seek.m(r0), hi} : Map<&2, Rev.Revision>}:
  match r0:
    case (x, y):
      {==}

def hi_map(-p2: Nat, -lo: Map<&2, Rev.Revision>, r0: Map<&2, Rev.Revision> & String & Maybe<&2, String>) -> {seek.m(Map.hi(&2, Rev.Revision, String & Maybe<&2, String>, p2, lo, r0)) == MNode{p2, lo, seek.m(r0)} : Map<&2, Rev.Revision>}:
  match r0:
    case (x, y):
      {==}

def seek_bit(+lo: Map<&2, Rev.Revision>, +hi: Map<&2, Rev.Revision>, +p2: Nat, kb: String & Bool, +L: List<&2, String>, +hl: {hok(lo, L) == True{} : Bool}, +hh: {hok(hi, L) == True{} : Bool}, il: @k2: String -> {hok(seek.m(Map.seek(&2, Rev.Revision, lo, k2)), L) == True{} : Bool}, ih: @k2: String -> {hok(seek.m(Map.seek(&2, Rev.Revision, hi, k2)), L) == True{} : Bool}) -> {hok(seek.m(Map.seek.bit(&2, Rev.Revision, lo, hi, p2, kb)), L) == True{} : Bool}:
  match kb:
    case (+key2, b):
      match b:
        case False{}:
          (%Equal.sym(Map<&2, Rev.Revision>, seek.m(Map.lo(&2, Rev.Revision, String & Maybe<&2, String>, p2, hi, Map.seek(&2, Rev.Revision, lo, key2))), MNode{p2, seek.m(Map.seek(&2, Rev.Revision, lo, key2)), hi}, lo_map(p2, hi, Map.seek(&2, Rev.Revision, lo, key2))) : {hok(_, L) == True{} : Bool}
            AL.and_intro(hok(seek.m(Map.seek(&2, Rev.Revision, lo, key2)), L), hok(hi, L), il(key2), hh))
        case True{}:
          (%Equal.sym(Map<&2, Rev.Revision>, seek.m(Map.hi(&2, Rev.Revision, String & Maybe<&2, String>, p2, lo, Map.seek(&2, Rev.Revision, hi, key2))), MNode{p2, lo, seek.m(Map.seek(&2, Rev.Revision, hi, key2))}, hi_map(p2, lo, Map.seek(&2, Rev.Revision, hi, key2))) : {hok(_, L) == True{} : Bool}
            AL.and_intro(hok(lo, L), hok(seek.m(Map.seek(&2, Rev.Revision, hi, key2)), L), hl, ih(key2)))

# Seeking a key gives the map back as it was.
def seek_ok(m: Map<&2, Rev.Revision>, +key: String, +L: List<&2, String>, +h: {hok(m, L) == True{} : Bool}) -> {hok(seek.m(Map.seek(&2, Rev.Revision, m, key)), L) == True{} : Bool}:
  match m:
    case MTip{}:
      {==}
    case MLeaf{+k, +v}:
      h
    case MNode{+pos, +lo, +hi}:
      seek_bit(lo, hi, pos, Map.bit(key, pos), L, Comp.and_left(hok(lo, L), hok(hi, L), h), Comp.and_right(hok(lo, L), hok(hi, L), h),
        k2 => seek_ok(lo, k2, L, Comp.and_left(hok(lo, L), hok(hi, L), h)),
        k2 => seek_ok(hi, k2, L, Comp.and_right(hok(lo, L), hok(hi, L), h)))

def splice_bit_ok(+x: Rev.Revision, +rest: Map<&2, Rev.Revision>, +pb: Nat, kb: String & Bool, +L: List<&2, String>, +hr: {hok(rest, L) == True{} : Bool}, +hx: {Rev.member(L, Rev.id_of(x)) == True{} : Bool}) -> {hok(Map.ins.splice.bit(&2, Rev.Revision, x, rest, pb, kb), L) == True{} : Bool}:
  match kb:
    case (key2, b):
      match b:
        case False{}:
          AL.and_intro(Rev.member(L, Rev.id_of(x)), hok(rest, L), hx, hr)
        case True{}:
          AL.and_intro(hok(rest, L), Rev.member(L, Rev.id_of(x)), hr, hx)

def splice_ok(+p: Nat, +key: String, +x: Rev.Revision, +rest: Map<&2, Rev.Revision>, +L: List<&2, String>, +hr: {hok(rest, L) == True{} : Bool}, +hx: {Rev.member(L, Rev.id_of(x)) == True{} : Bool}) -> {hok(Map.ins.splice(&2, Rev.Revision, p, key, x, rest), L) == True{} : Bool}:
  splice_bit_ok(x, rest, p, Map.bit(key, p), L, hr, hx)

def deep_ok(+x: Rev.Revision, +lo: Map<&2, Rev.Revision>, +hi: Map<&2, Rev.Revision>, +pb: Nat, +qb: Nat, kb: String & Bool, +L: List<&2, String>, +hl: {hok(lo, L) == True{} : Bool}, +hh: {hok(hi, L) == True{} : Bool}, il: @k2: String -> {hok(Map.ins(&2, Rev.Revision, lo, k2, x, pb), L) == True{} : Bool}, ih: @k2: String -> {hok(Map.ins(&2, Rev.Revision, hi, k2, x, pb), L) == True{} : Bool}) -> {hok(Map.ins.deep(&2, Rev.Revision, x, lo, hi, pb, qb, kb), L) == True{} : Bool}:
  match kb:
    case (+key2, b):
      match b:
        case False{}:
          AL.and_intro(hok(Map.ins(&2, Rev.Revision, lo, key2, x, pb), L), hok(hi, L), il(key2), hh)
        case True{}:
          AL.and_intro(hok(lo, L), hok(Map.ins(&2, Rev.Revision, hi, key2, x, pb), L), hl, ih(key2))

def ins_if_ok(+key: String, +x: Rev.Revision, +lo: Map<&2, Rev.Revision>, +hi: Map<&2, Rev.Revision>, +p2: Nat, +pb: Nat, t: Bool, +L: List<&2, String>, +hl: {hok(lo, L) == True{} : Bool}, +hh: {hok(hi, L) == True{} : Bool}, +hx: {Rev.member(L, Rev.id_of(x)) == True{} : Bool}, il: @k2: String -> {hok(Map.ins(&2, Rev.Revision, lo, k2, x, pb), L) == True{} : Bool}, ih: @k2: String -> {hok(Map.ins(&2, Rev.Revision, hi, k2, x, pb), L) == True{} : Bool}) -> {hok(Map.ins.if(&2, Rev.Revision, key, x, lo, hi, p2, pb, t), L) == True{} : Bool}:
  match t:
    case False{}:
      splice_ok(pb, key, x, MNode{p2, lo, hi}, L, AL.and_intro(hok(lo, L), hok(hi, L), hl, hh), hx)
    case True{}:
      deep_ok(x, lo, hi, pb, p2, Map.bit(key, p2), L, hl, hh, il, ih)

def ins_ok(m: Map<&2, Rev.Revision>, +key: String, +x: Rev.Revision, +p: Nat, +L: List<&2, String>, +h: {hok(m, L) == True{} : Bool}, +hx: {Rev.member(L, Rev.id_of(x)) == True{} : Bool}) -> {hok(Map.ins(&2, Rev.Revision, m, key, x, p), L) == True{} : Bool}:
  match m:
    case MTip{}:
      hx
    case MLeaf{+k, +v}:
      splice_ok(p, key, x, MLeaf{k, v}, L, h, hx)
    case MNode{+pos, +lo, +hi}:
      ins_if_ok(key, x, lo, hi, pos, p, Nat.is_lt(pos, p), L, Comp.and_left(hok(lo, L), hok(hi, L), h), Comp.and_right(hok(lo, L), hok(hi, L), h), hx,
        k2 => ins_ok(lo, k2, x, p, L, Comp.and_left(hok(lo, L), hok(hi, L), h), hx),
        k2 => ins_ok(hi, k2, x, p, L, Comp.and_right(hok(lo, L), hok(hi, L), h), hx))

def put_bit_ok(+x: Rev.Revision, +p2: Nat, +lo: Map<&2, Rev.Revision>, +hi: Map<&2, Rev.Revision>, kb: String & Bool, +L: List<&2, String>, +hl: {hok(lo, L) == True{} : Bool}, +hh: {hok(hi, L) == True{} : Bool}, il: @k2: String -> {hok(Map.put(&2, Rev.Revision, lo, k2, x), L) == True{} : Bool}, ih: @k2: String -> {hok(Map.put(&2, Rev.Revision, hi, k2, x), L) == True{} : Bool}) -> {hok(Map.put.bit(&2, Rev.Revision, x, p2, lo, hi, kb), L) == True{} : Bool}:
  match kb:
    case (+key2, b):
      match b:
        case False{}:
          AL.and_intro(hok(Map.put(&2, Rev.Revision, lo, key2, x), L), hok(hi, L), il(key2), hh)
        case True{}:
          AL.and_intro(hok(lo, L), hok(Map.put(&2, Rev.Revision, hi, key2, x), L), hl, ih(key2))

def put_ok(m: Map<&2, Rev.Revision>, +key: String, +x: Rev.Revision, +L: List<&2, String>, +h: {hok(m, L) == True{} : Bool}, +hx: {Rev.member(L, Rev.id_of(x)) == True{} : Bool}) -> {hok(Map.put(&2, Rev.Revision, m, key, x), L) == True{} : Bool}:
  match m:
    case MTip{}:
      hx
    case MLeaf{k, v}:
      hx
    case MNode{+pos, +lo, +hi}:
      put_bit_ok(x, pos, lo, hi, Map.bit(key, pos), L, Comp.and_left(hok(lo, L), hok(hi, L), h), Comp.and_right(hok(lo, L), hok(hi, L), h),
        k2 => put_ok(lo, k2, x, L, Comp.and_left(hok(lo, L), hok(hi, L), h), hx),
        k2 => put_ok(hi, k2, x, L, Comp.and_right(hok(lo, L), hok(hi, L), h), hx))

def fin_ok(+m: Map<&2, Rev.Revision>, +key: String, +x: Rev.Revision, r: (String & String) & Cmp, +L: List<&2, String>, +h: {hok(m, L) == True{} : Bool}, +hx: {Rev.member(L, Rev.id_of(x)) == True{} : Bool}) -> {hok(Map.set.fin.go(&2, Rev.Revision, m, key, x, r), L) == True{} : Bool}:
  match r:
    case (kk, c):
      match kk:
        case (kb2, k2):
          match c:
            case LT{}:
              ins_ok(m, key, x, Map.diff(kb2, k2), L, h, hx)
            case EQ{}:
              put_ok(m, key, x, L, h, hx)
            case GT{}:
              ins_ok(m, key, x, Map.diff(kb2, k2), L, h, hx)

def set_go_ok(+x: Rev.Revision, r: Map<&2, Rev.Revision> & String & Maybe<&2, String>, +L: List<&2, String>, hr: {hok(seek.m(r), L) == True{} : Bool}, +hx: {Rev.member(L, Rev.id_of(x)) == True{} : Bool}) -> {hok(Map.set.go(&2, Rev.Revision, x, r), L) == True{} : Bool}:
  match r:
    case (m2, rest):
      match rest:
        case (+key2, found):
          match found:
            case None{}:
              hx
            case Some{k}:
              fin_ok(m2, key2, x, String.cmp(key2, k), L, hr, hx)

# Setting a key never invents a revision.
def set_ok(+m: Map<&2, Rev.Revision>, +key: String, +x: Rev.Revision, +L: List<&2, String>, +h: {hok(m, L) == True{} : Bool}, +hx: {Rev.member(L, Rev.id_of(x)) == True{} : Bool}) -> {hok(Map.set(&2, Rev.Revision, m, key, x), L) == True{} : Bool}:
  set_go_ok(x, Map.seek(&2, Rev.Revision, m, key), L, seek_ok(m, key, L, h), hx)

# Every revision of a list has a digest in `L`.
def all_in(rs: List<&2, Rev.Revision>, +L: List<&2, String>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> rest:
      Bool.and(Rev.member(L, Rev.id_of(r)), all_in(rest, L))

def vals_ok(m: Map<&2, Rev.Revision>, +acc: List<&2, Rev.Revision>, +L: List<&2, String>, +h: {hok(m, L) == True{} : Bool}, +ha: {all_in(acc, L) == True{} : Bool}) -> {all_in(Map.values.go(&2, Rev.Revision, m, acc), L) == True{} : Bool}:
  match m:
    case MTip{}:
      ha
    case MLeaf{k, +v}:
      AL.and_intro(Rev.member(L, Rev.id_of(v)), all_in(acc, L), h, ha)
    case MNode{p, +lo, +hi}:
      vals_ok(lo, Map.values.go(&2, Rev.Revision, hi, acc), L, Comp.and_left(hok(lo, L), hok(hi, L), h), vals_ok(hi, acc, L, Comp.and_right(hok(lo, L), hok(hi, L), h), ha))

def ids_in(rs: List<&2, Rev.Revision>, +L: List<&2, String>, +x: String, +ha: {all_in(rs, L) == True{} : Bool}, m: {Rev.member(Rev.ids(rs), x) == True{} : Bool}) -> {Rev.member(L, x) == True{} : Bool}:
  match rs:
    case Nil{}:
      Empty.absurd({Rev.member(L, x) == True{} : Bool}, S.false_true(m))
    case +r <> +rest:
      GL.member_cons({Rev.member(L, x) == True{} : Bool}, Rev.id_of(r), Rev.ids(rest), x, m,
        e => GL.member_at(L, Rev.id_of(r), x, e, Comp.and_left(Rev.member(L, Rev.id_of(r)), all_in(rest, L), ha)),
        t => ids_in(rest, L, x, Comp.and_right(Rev.member(L, Rev.id_of(r)), all_in(rest, L), ha), t))

def values_in(+h: Map<&2, Rev.Revision>, +L: List<&2, String>, +x: String, +hh: {hok(h, L) == True{} : Bool}, m: {Rev.member(Rev.ids(Rev.revisions(h)), x) == True{} : Bool}) -> {Rev.member(L, x) == True{} : Bool}:
  ids_in(Rev.revisions(h), L, x, vals_ok(h, Nil{}, L, hh, {==}), m)

# The history the tool builds holds only the store's revisions.
def hist_ok(fs: List<&2, Main.Full>, +h: Map<&2, Rev.Revision>, +L: List<&2, String>, +hh: {hok(h, L) == True{} : Bool}, +hs: {T.subset_ids(Main.ids(fs), L) == True{} : Bool}) -> {hok(Main.history.go(fs, h), L) == True{} : Bool}:
  match fs:
    case Nil{}:
      hh
    case Main.Full{+id, +change, +parents, +supersedes, author, when, revised_by, revised, facts, +message} <> +rest:
      hist_ok(rest, Map.set(&2, Rev.Revision, h, id, Rev.Revision{id, change, parents, supersedes, message}), L,
        set_ok(h, id, Rev.Revision{id, change, parents, supersedes, message}, L, hh, Comp.and_left(Rev.member(L, id), T.subset_ids(Main.ids(rest), L), hs)),
        Comp.and_right(Rev.member(L, id), T.subset_ids(Main.ids(rest), L), hs))

def history_ok(+fs: List<&2, Main.Full>) -> {hok(Main.history(fs), Main.ids(fs)) == True{} : Bool}:
  hist_ok(fs, Rev.empty(), Main.ids(fs), {==}, GL.subset_refl(Main.ids(fs)))

# The targets
# -----------

def rdisc(r: Result<&2, &2, String, String>) -> Type:
  match r:
    case Done{x}:
      Empty
    case Fail{e}:
      Unit

def fail_done(-e: String, -x: String, h: {Fail{e} == Done{x} : Result<&2, &2, String, String>}) -> Empty:
  %h : {rdisc(_) : Type}
  Unit{}

def done_eq(-a: String, -b: String, h: {Done{a} == Done{b} : Result<&2, &2, String, String>}) -> {a == b : String}:
  Equal.cong(Result<&2, &2, String, String>, String, r => Result.default(&2, &2, String, String, r, a), Done{a}, Done{b}, h)

def one_mem(+only: String, +id: String, e: {Done{only} == Done{id} : Result<&2, &2, String, String>}) -> {Rev.member([only], id) == True{} : Bool}:
  GL.member_at([only], only, id, done_eq(only, id, e), GL.member_head(only, Nil{}))

def one_of_mem(found: List<&2, String>, +p: String, +none: String, +what: String, +id: String, e: {Main.one_of(found, p, none, what) == Done{id} : Result<&2, &2, String, String>}) -> {Rev.member(found, id) == True{} : Bool}:
  match found:
    case Nil{}:
      Empty.absurd({Rev.member(Nil{}, id) == True{} : Bool}, fail_done(none ++ " `" ++ p ++ "`", id, e))
    case +only <> Nil{}:
      one_mem(only, id, e)
    case +x <> +y <> +r:
      Empty.absurd({Rev.member(x <> y <> r, id) == True{} : Bool}, fail_done("`" ++ p ++ "` could be " ++ Nat.show(List.length(&2, String, x <> y <> r)) ++ " " ++ what ++ ":" ++ Main.listed(x <> y <> r), id, e))

def head_mem(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, heads: List<&2, String>, +id: String, e: {Main.head_target(fs, bs, heads) == Done{id} : Result<&2, &2, String, String>}) -> {Rev.member(heads, id) == True{} : Bool}:
  match heads:
    case Nil{}:
      Empty.absurd({Rev.member(Nil{}, id) == True{} : Bool}, fail_done("this store holds no revisions yet", id, e))
    case +only <> Nil{}:
      one_mem(only, id, e)
    case +x <> +y <> +r:
      Empty.absurd({Rev.member(x <> y <> r, id) == True{} : Bool}, fail_done("this store has " ++ Nat.show(List.length(&2, String, x <> y <> r)) ++ " heads, so `head` names none of them; name one, or join them with `historica merge`:" ++ Main.described(fs, bs, List.sort(~String, ~(a => b => String.is_le(a, b)), x <> y <> r)), id, e))

def cur_mem(heads: List<&2, String>, cur: List<&2, String>, +x: String, m: {Rev.member(Main.current_heads.of(heads, cur), x) == True{} : Bool}) -> {Bool.or(Rev.member(heads, x), Rev.member(cur, x)) == True{} : Bool}:
  match cur:
    case Nil{}:
      AL.or_left(Rev.member(heads, x), Rev.member(Nil{}, x), m)
    case y <> r:
      AL.or_right(Rev.member(heads, x), Rev.member(y <> r, x), m)

# A change resolves to one of its current revisions.
def state_mem(cur: List<&2, String>, any: Bool, +change: String, +named: String, +id: String, e: {Main.current(Rev.change_state.of(any, cur), change, named) == Done{id} : Result<&2, &2, String, String>}) -> {Rev.member(cur, id) == True{} : Bool}:
  match cur:
    case Nil{}:
      match any:
        case True{}:
          Empty.absurd({Rev.member(Nil{}, id) == True{} : Bool}, fail_done("every revision of " ++ change ++ " was superseded by revisions of other changes, so " ++ named ++ " has no current revision", id, e))
        case False{}:
          Empty.absurd({Rev.member(Nil{}, id) == True{} : Bool}, fail_done(named ++ " names the change " ++ change ++ ", which no revision here claims", id, e))
    case +only <> Nil{}:
      one_mem(only, id, e)
    case +x <> +y <> +r:
      Empty.absurd({Rev.member(x <> y <> r, id) == True{} : Bool}, fail_done(change ++ " has " ++ Nat.show(List.length(&2, String, x <> y <> r)) ++ " current revisions, none superseding the others; name one of them:" ++ Main.listed(x <> y <> r), id, e))

def keep_rev_in(b: Bool, +x: Rev.Revision, rest: List<&2, Rev.Revision>, +L: List<&2, String>, hx: {Rev.member(L, Rev.id_of(x)) == True{} : Bool}, hr: {all_in(rest, L) == True{} : Bool}) -> {all_in(Rev.keep_revision(b, x, rest), L) == True{} : Bool}:
  match b:
    case True{}:
      AL.and_intro(Rev.member(L, Rev.id_of(x)), all_in(rest, L), hx, hr)
    case False{}:
      hr

def revof_in(rs: List<&2, Rev.Revision>, +c: String, +L: List<&2, String>, +ha: {all_in(rs, L) == True{} : Bool}) -> {all_in(Rev.revisions_of.go(rs, c), L) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Rev.Revision{+i, +c2, +ps, +ss, +msg} <> +rest:
      keep_rev_in(String.eq(c2, c), Rev.Revision{i, c2, ps, ss, msg}, Rev.revisions_of.go(rest, c), L,
        Comp.and_left(Rev.member(L, i), all_in(rest, L), ha),
        revof_in(rest, c, L, Comp.and_right(Rev.member(L, i), all_in(rest, L), ha)))

def change_mem(+h: Map<&2, Rev.Revision>, +c: String, +named: String, +id: String, +L: List<&2, String>, +hh: {hok(h, L) == True{} : Bool}, e: {Main.current(Rev.change_state(h, c), c, named) == Done{id} : Result<&2, &2, String, String>}) -> {Rev.member(L, id) == True{} : Bool}:
  ids_in(Rev.revisions_of.go(Rev.revisions(h), c), L, id, revof_in(Rev.revisions(h), c, L, vals_ok(h, Nil{}, L, hh, {==})),
    GL.without_sub(Rev.ids(Rev.revisions_of(h, c)), Rev.superseded(h), id,
      state_mem(Rev.without(Rev.ids(Rev.revisions_of(h, c)), Rev.superseded(h)), Bool.not(List.is_empty(&2, String, Rev.ids(Rev.revisions_of(h, c)))), c, named, id, e)))

def change_target_mem(found: Result<&2, &2, String, String>, +h: Map<&2, Rev.Revision>, +spelling: String, +id: String, +L: List<&2, String>, +hh: {hok(h, L) == True{} : Bool}, e: {Main.change_target(found, h, spelling) == Done{id} : Result<&2, &2, String, String>}) -> {Rev.member(L, id) == True{} : Bool}:
  match found:
    case Fail{err}:
      Empty.absurd({Rev.member(L, id) == True{} : Bool}, fail_done(err, id, e))
    case Done{+change}:
      change_mem(h, change, "`" ++ spelling ++ "`", id, L, hh, e)

def keep_sub(b: Bool, +y: String, +w: List<&2, String>, +rest: List<&2, String>, +x: String, m: {Rev.member(Rev.keep(b, y, w), x) == True{} : Bool}, ih: {Rev.member(w, x) == True{} : Bool} -> {Rev.member(rest, x) == True{} : Bool}) -> {Rev.member(y <> rest, x) == True{} : Bool}:
  match b:
    case True{}:
      GL.member_cons({Rev.member(y <> rest, x) == True{} : Bool}, y, w, x, m, h => GL.member_at(y <> rest, y, x, h, GL.member_head(y, rest)), t => GL.member_tail(y, rest, x, ih(t)))
    case False{}:
      GL.member_tail(y, rest, x, ih(m))

def prefix_mem(xs: List<&2, String>, +p: String, +x: String, m: {Rev.member(Main.with_prefix(xs, p), x) == True{} : Bool}) -> {Rev.member(xs, x) == True{} : Bool}:
  match xs:
    case Nil{}:
      m
    case +y <> +rest:
      keep_sub(String.starts_with(y, p), y, Main.with_prefix(rest, p), rest, x, m, t => prefix_mem(rest, p, x, t))

def pinned_mem(+fs: List<&2, Main.Full>, +name: String, +i: String, b: Bool, eb: {Rev.member(Main.ids(fs), i) == b : Bool}, +id: String, e: {Bool.pick(Result<&2, &2, String, String>, b, Done{i}, Fail{"the bookmark `" ++ name ++ "` names the revision " ++ i ++ ", which this store does not hold yet"}) == Done{id} : Result<&2, &2, String, String>}) -> {Rev.member(Main.ids(fs), id) == True{} : Bool}:
  match b:
    case True{}:
      GL.member_at(Main.ids(fs), i, id, done_eq(i, id, e), eb)
    case False{}:
      Empty.absurd({Rev.member(Main.ids(fs), id) == True{} : Bool}, fail_done("the bookmark `" ++ name ++ "` names the revision " ++ i ++ ", which this store does not hold yet", id, e))

def bookmarked_mem(+fs: List<&2, Main.Full>, +name: String, t: Bm.Target, +id: String, e: {Main.bookmarked(fs, name, t) == Done{id} : Result<&2, &2, String, String>}) -> {Rev.member(Main.ids(fs), id) == True{} : Bool}:
  match t:
    case Bm.Target.Revision{+i}:
      pinned_mem(fs, name, i, Rev.member(Main.ids(fs), i), {==}, id, e)
    case Bm.Target.Change{+c}:
      change_mem(Main.history(fs), c, "the bookmark `" ++ name ++ "`", id, Main.ids(fs), history_ok(fs), e)
    case Bm.Target.File{f}:
      Empty.absurd({Rev.member(Main.ids(fs), id) == True{} : Bool}, fail_done("the bookmark `" ++ name ++ "` names the file " ++ f ++ ", and a file is not a revision; a file is addressed at one, as `cat <target> file:" ++ name ++ "`", id, e))

def head_held(+fs: List<&2, Main.Full>, +id: String, m: {Rev.member(Rev.heads(Main.history(fs)), id) == True{} : Bool}) -> {Rev.member(Main.ids(fs), id) == True{} : Bool}:
  values_in(Main.history(fs), Main.ids(fs), id, history_ok(fs),
    GL.without_sub(Rev.ids(Rev.revisions(Main.history(fs))), Rev.all_parents(Rev.revisions(Main.history(fs))), id, m))

def spelled_mem(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +s: String, is_head: Bool, hex: Bool, change: Bool, +id: String, e: {Main.resolve.spelled(fs, bs, s, is_head, hex, change) == Done{id} : Result<&2, &2, String, String>}) -> {Rev.member(Main.ids(fs), id) == True{} : Bool}:
  match is_head:
    case True{}:
      AL.or_cases({Rev.member(Main.ids(fs), id) == True{} : Bool}, Rev.member(Rev.heads(Main.history(fs)), id), Rev.member(Rev.without(Rev.heads(Main.history(fs)), Rev.superseded(Main.history(fs))), id),
        cur_mem(Rev.heads(Main.history(fs)), Rev.without(Rev.heads(Main.history(fs)), Rev.superseded(Main.history(fs))), id, head_mem(fs, bs, Main.current_heads(Main.history(fs)), id, e)),
        l => head_held(fs, id, l),
        r => head_held(fs, id, GL.without_sub(Rev.heads(Main.history(fs)), Rev.superseded(Main.history(fs)), id, r)))
    case False{}:
      match hex:
        case True{}:
          prefix_mem(Main.ids(fs), s, id, one_of_mem(Main.with_prefix(Main.ids(fs), s), s, "no revision here has a digest starting", "revisions", id, e))
        case False{}:
          match change:
            case True{}:
              change_target_mem(Main.one_of(Main.with_prefix(Main.changes(fs), s), s, "no change here has an ID starting", "changes"), Main.history(fs), s, id, Main.ids(fs), history_ok(fs), e)
            case False{}:
              Empty.absurd({Rev.member(Main.ids(fs), id) == True{} : Bool}, fail_done("`" ++ s ++ "` is not a bookmark here, and it is spelled as neither a change ID (`k`–`z`) nor a digest (`0`–`9`, `a`–`f`)", id, e))

def named_mem(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +s: String, found: Maybe<&2, Bm.Target>, +id: String, e: {Main.resolve.named(fs, bs, s, found) == Done{id} : Result<&2, &2, String, String>}) -> {Rev.member(Main.ids(fs), id) == True{} : Bool}:
  match found:
    case Some{t}:
      bookmarked_mem(fs, s, t, id, e)
    case None{}:
      spelled_mem(fs, bs, s, String.eq(s, "head"), Main.all_chars(~(c => Main.is_hex(c)), s), Main.all_chars(~(c => Id.is_letter(c)), s), id, e)

# Every target names a revision the store holds.
def resolve_mem(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, spelling: String, +id: String, e: {Main.resolve(fs, bs, spelling) == Done{id} : Result<&2, &2, String, String>}) -> {Rev.member(Main.ids(fs), id) == True{} : Bool}:
  match spelling:
    case SNil{}:
      Empty.absurd({Rev.member(Main.ids(fs), id) == True{} : Bool}, fail_done("a target cannot be empty", id, e))
    case SCon{+c, +t}:
      named_mem(fs, bs, SCon{c, t}, Bm.find(bs, SCon{c, t}), id, e)
