# `log` lists only what its span names, every one a revision the store
# holds. The walk out from a target takes in the target, and after it only
# parents of revisions it has taken in, so every revision listed but the
# target is a parent of one listed; and it takes the target in first,
# wherever the store holds it. Of `a..b`, `a` is among what `a` reaches,
# so it is never listed, and what is listed is some of what `log b` lists.
import Base
import ./revision.bend as Rev
import ./commands.bend as Main
import ./string_lemmas.bend as S
import ./anchor_lemmas.bend as AL
import ./composition_lemmas.bend as Comp
import ./graph_lemmas.bend as GL
import ./chain_lemmas.bend as ChainL
import ./blamed_lemmas.bend as B

def or_cases(-R: Type, a: Bool, -b: Bool, e: {Bool.or(a, b) == True{} : Bool}, l: {a == True{} : Bool} -> R, r: {b == True{} : Bool} -> R) -> R:
  match a:
    case True{}:
      l({==})
    case False{}:
      r(e)

def mdisc(m: Maybe<&2, Main.Full>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

# Every revision of a list has its digest among `ids`.
def inids(+ids: List<&2, String>, xs: List<&2, Main.Full>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      Bool.and(Rev.member(ids, Main.id_of(x)), inids(ids, rest))

def inids_weak(+y: String, +ids: List<&2, String>, xs: List<&2, Main.Full>, +h: {inids(ids, xs) == True{} : Bool}) -> {inids(y <> ids, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Rev.member(y <> ids, Main.id_of(x)), inids(y <> ids, rest),
        GL.member_tail(y, ids, Main.id_of(x), Comp.and_left(Rev.member(ids, Main.id_of(x)), inids(ids, rest), h)),
        inids_weak(y, ids, rest, Comp.and_right(Rev.member(ids, Main.id_of(x)), inids(ids, rest), h)))

# Each revision of the store is one of the store's.
def inids_self(fs: List<&2, Main.Full>) -> {inids(Main.ids(fs), fs) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +rest:
      AL.and_intro(Rev.member(Main.id_of(f) <> Main.ids(rest), Main.id_of(f)), inids(Main.id_of(f) <> Main.ids(rest), rest),
        GL.member_head(Main.id_of(f), Main.ids(rest)), inids_weak(Main.id_of(f), Main.ids(rest), rest, inids_self(rest)))

# Every revision of a list is one of `ids` and in `R`.
def amongst(+ids: List<&2, String>, +R: List<&2, String>, xs: List<&2, Main.Full>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      Bool.and(Bool.and(Rev.member(ids, Main.id_of(x)), Rev.member(R, Main.id_of(x))), amongst(ids, R, rest))

def keep_case(b: Bool, +ids: List<&2, String>, +R: List<&2, String>, +x: Main.Full, +rest: List<&2, Main.Full>, +eb: {Rev.member(R, Main.id_of(x)) == b : Bool}, +hx: {Rev.member(ids, Main.id_of(x)) == True{} : Bool}, ih: {amongst(ids, R, Main.among(rest, R)) == True{} : Bool}) -> {amongst(ids, R, Main.keep_full(b, x, Main.among(rest, R))) == True{} : Bool}:
  match b:
    case True{}:
      AL.and_intro(Bool.and(Rev.member(ids, Main.id_of(x)), Rev.member(R, Main.id_of(x))), amongst(ids, R, Main.among(rest, R)), AL.and_intro(Rev.member(ids, Main.id_of(x)), Rev.member(R, Main.id_of(x)), hx, eb), ih)
    case False{}:
      ih

# What `among` keeps of revisions among `ids` is among `ids`, and in `R`.
def among_ok(+ids: List<&2, String>, +R: List<&2, String>, xs: List<&2, Main.Full>, +hs: {inids(ids, xs) == True{} : Bool}) -> {amongst(ids, R, Main.among(xs, R)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      keep_case(Rev.member(R, Main.id_of(x)), ids, R, x, rest, {==}, Comp.and_left(Rev.member(ids, Main.id_of(x)), inids(ids, rest), hs),
        among_ok(ids, R, rest, Comp.and_right(Rev.member(ids, Main.id_of(x)), inids(ids, rest), hs)))

# Every revision listed is one the store holds.
def held_of(xs: List<&2, Main.Full>, +fs: List<&2, Main.Full>, +R: List<&2, String>, +h: {amongst(Main.ids(fs), R, xs) == True{} : Bool}) -> {Main.span.held(fs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Rev.member(Main.ids(fs), Main.id_of(x)), Main.span.held(fs, rest),
        Comp.and_left(Rev.member(Main.ids(fs), Main.id_of(x)), Rev.member(R, Main.id_of(x)), Comp.and_left(Bool.and(Rev.member(Main.ids(fs), Main.id_of(x)), Rev.member(R, Main.id_of(x))), amongst(Main.ids(fs), R, rest), h)),
        held_of(rest, fs, R, Comp.and_right(Bool.and(Rev.member(Main.ids(fs), Main.id_of(x)), Rev.member(R, Main.id_of(x))), amongst(Main.ids(fs), R, rest), h)))

# What `without` keeps is not in what it takes away.
def without_out.of(b: Bool, +y: String, +rest: List<&2, String>, +ys: List<&2, String>, +x: String, +eb: {Rev.member(ys, y) == b : Bool}, m: {Rev.member(Rev.keep(Bool.not(b), y, Rev.without(rest, ys)), x) == True{} : Bool}, ih: {Rev.member(Rev.without(rest, ys), x) == True{} : Bool} -> {Rev.member(ys, x) == False{} : Bool}) -> {Rev.member(ys, x) == False{} : Bool}:
  match b:
    case True{}:
      ih(m)
    case False{}:
      GL.member_cons({Rev.member(ys, x) == False{} : Bool}, y, Rev.without(rest, ys), x, m, h => (%h : {Rev.member(ys, _) == False{} : Bool}; eb), ih)

def without_out(xs: List<&2, String>, +ys: List<&2, String>, +x: String, m: {Rev.member(Rev.without(xs, ys), x) == True{} : Bool}) -> {Rev.member(ys, x) == False{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Rev.member(ys, x) == False{} : Bool}, S.false_true(m))
    case +y <> +rest:
      without_out.of(Rev.member(ys, y), y, rest, ys, x, {==}, m, w => without_out(rest, ys, x, w))

# What is taken away is not kept.
def without_false(+xs: List<&2, String>, +ys: List<&2, String>, +x: String, +h: {Rev.member(ys, x) == True{} : Bool}) -> {Rev.member(Rev.without(xs, ys), x) == False{} : Bool}:
  AL.bool_cases({Rev.member(Rev.without(xs, ys), x) == False{} : Bool}, Rev.member(Rev.without(xs, ys), x),
    m => Empty.absurd({Rev.member(Rev.without(xs, ys), x) == False{} : Bool}, S.true_false(Equal.trans(Bool, True{}, Rev.member(ys, x), False{}, Equal.sym(Bool, Rev.member(ys, x), True{}, h), without_out(xs, ys, x, m)))),
    m => m)

# The walk takes in only the target and parents
# ---------------------------------------------

# A digest is linked to the walk from `t` where it is `t`, or a parent of
# the revision some digest the walk took in names.
def parent_in(m: Maybe<&2, Main.Full>, +x: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{g}:
      Rev.member(Main.parents_of(g), x)

def seen_parent(+fs: List<&2, Main.Full>, seen: List<&2, String>, +x: String) -> Bool:
  match seen:
    case Nil{}:
      False{}
    case +s <> rest:
      Bool.or(parent_in(Main.find(fs, s), x), seen_parent(fs, rest, x))

def linked(+fs: List<&2, Main.Full>, +t: String, +seen: List<&2, String>, +x: String) -> Bool:
  Bool.or(String.eq(x, t), seen_parent(fs, seen, x))

def all_linked(+fs: List<&2, Main.Full>, +t: String, +seen: List<&2, String>, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      Bool.and(linked(fs, t, seen, x), all_linked(fs, t, seen, rest))

# What the walk holds, waiting and taken in, is all linked to the target.
def inv(+fs: List<&2, Main.Full>, +t: String, r: Main.Reach) -> Bool:
  match r:
    case Main.Reach{+fr, +seen}:
      Bool.and(all_linked(fs, t, seen, fr), all_linked(fs, t, seen, seen))

def linked_weak(+fs: List<&2, Main.Full>, +t: String, +s: String, +seen: List<&2, String>, +x: String, h: {linked(fs, t, seen, x) == True{} : Bool}) -> {linked(fs, t, s <> seen, x) == True{} : Bool}:
  or_cases({linked(fs, t, s <> seen, x) == True{} : Bool}, String.eq(x, t), seen_parent(fs, seen, x), h,
    l => ChainL.or_l(String.eq(x, t), seen_parent(fs, s <> seen, x), l),
    r => ChainL.or_r(String.eq(x, t), seen_parent(fs, s <> seen, x), ChainL.or_r(parent_in(Main.find(fs, s), x), seen_parent(fs, seen, x), r)))

def all_weak(+fs: List<&2, Main.Full>, +t: String, +s: String, +seen: List<&2, String>, xs: List<&2, String>, +h: {all_linked(fs, t, seen, xs) == True{} : Bool}) -> {all_linked(fs, t, s <> seen, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(linked(fs, t, s <> seen, x), all_linked(fs, t, s <> seen, rest),
        linked_weak(fs, t, s, seen, x, Comp.and_left(linked(fs, t, seen, x), all_linked(fs, t, seen, rest), h)),
        all_weak(fs, t, s, seen, rest, Comp.and_right(linked(fs, t, seen, x), all_linked(fs, t, seen, rest), h)))

def all_app(xs: List<&2, String>, +ys: List<&2, String>, +fs: List<&2, Main.Full>, +t: String, +seen: List<&2, String>, +hx: {all_linked(fs, t, seen, xs) == True{} : Bool}, hy: {all_linked(fs, t, seen, ys) == True{} : Bool}) -> {all_linked(fs, t, seen, List.append(&2, String, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +x <> +rest:
      AL.and_intro(linked(fs, t, seen, x), all_linked(fs, t, seen, List.append(&2, String, rest, ys)),
        Comp.and_left(linked(fs, t, seen, x), all_linked(fs, t, seen, rest), hx),
        all_app(rest, ys, fs, t, seen, Comp.and_right(linked(fs, t, seen, x), all_linked(fs, t, seen, rest), hx), hy))

def held_weak(+y: String, +ys: List<&2, String>, xs: List<&2, String>, +h: {Main.all_held(ys, xs) == True{} : Bool}) -> {Main.all_held(y <> ys, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Rev.member(y <> ys, x), Main.all_held(y <> ys, rest),
        GL.member_tail(y, ys, x, Comp.and_left(Rev.member(ys, x), Main.all_held(ys, rest), h)),
        held_weak(y, ys, rest, Comp.and_right(Rev.member(ys, x), Main.all_held(ys, rest), h)))

def held_refl(xs: List<&2, String>) -> {Main.all_held(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Rev.member(x <> rest, x), Main.all_held(x <> rest, rest), GL.member_head(x, rest), held_weak(x, rest, rest, held_refl(rest)))

# The parents of a revision the walk takes in are linked through it.
def par_linked(ys: List<&2, String>, +fs: List<&2, Main.Full>, +t: String, +id: String, +seen: List<&2, String>, +f: Main.Full, +ef: {Main.find(fs, id) == Some{f} : Maybe<&2, Main.Full>}, +hs: {Main.all_held(Main.parents_of(f), ys) == True{} : Bool}) -> {all_linked(fs, t, id <> seen, ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +rest:
      +hy = Comp.and_left(Rev.member(Main.parents_of(f), y), Main.all_held(Main.parents_of(f), rest), hs)
      AL.and_intro(linked(fs, t, id <> seen, y), all_linked(fs, t, id <> seen, rest),
        ChainL.or_r(String.eq(y, t), seen_parent(fs, id <> seen, y), ChainL.or_l(parent_in(Main.find(fs, id), y), seen_parent(fs, seen, y), (%Equal.sym(Maybe<&2, Main.Full>, Main.find(fs, id), Some{f}, ef) : {parent_in(_, y) == True{} : Bool}; hy))),
        par_linked(rest, fs, t, id, seen, f, ef, Comp.and_right(Rev.member(Main.parents_of(f), y), Main.all_held(Main.parents_of(f), rest), hs)))

def reach_inv(already: Bool, +fs: List<&2, Main.Full>, +t: String, +id: String, +rest: List<&2, String>, +seen: List<&2, String>, +f: Main.Full, +ef: {Main.find(fs, id) == Some{f} : Maybe<&2, Main.Full>}, +hid: {linked(fs, t, seen, id) == True{} : Bool}, +hrest: {all_linked(fs, t, seen, rest) == True{} : Bool}, +hseen: {all_linked(fs, t, seen, seen) == True{} : Bool}) -> {inv(fs, t, Main.ancestry.reach(id, rest, seen, Main.parents_of(f), already)) == True{} : Bool}:
  match already:
    case True{}:
      AL.and_intro(all_linked(fs, t, seen, rest), all_linked(fs, t, seen, seen), hrest, hseen)
    case False{}:
      AL.and_intro(all_linked(fs, t, id <> seen, List.append(&2, String, rest, Main.parents_of(f))), all_linked(fs, t, id <> seen, id <> seen),
        all_app(rest, Main.parents_of(f), fs, t, id <> seen, all_weak(fs, t, id, seen, rest, hrest), par_linked(Main.parents_of(f), fs, t, id, seen, f, ef, held_refl(Main.parents_of(f)))),
        AL.and_intro(linked(fs, t, id <> seen, id), all_linked(fs, t, id <> seen, seen), linked_weak(fs, t, id, seen, id, hid), all_weak(fs, t, id, seen, seen, hseen)))

def next_inv(m: Maybe<&2, Main.Full>, +fs: List<&2, Main.Full>, +t: String, +id: String, +rest: List<&2, String>, +seen: List<&2, String>, +em: {Main.find(fs, id) == m : Maybe<&2, Main.Full>}, +h: {inv(fs, t, Main.Reach{id <> rest, seen}) == True{} : Bool}) -> {inv(fs, t, Main.ancestry.next(id, rest, seen, m)) == True{} : Bool}:
  match m:
    case None{}:
      +hf = Comp.and_left(Bool.and(linked(fs, t, seen, id), all_linked(fs, t, seen, rest)), all_linked(fs, t, seen, seen), h)
      AL.and_intro(all_linked(fs, t, seen, rest), all_linked(fs, t, seen, seen),
        Comp.and_right(linked(fs, t, seen, id), all_linked(fs, t, seen, rest), hf),
        Comp.and_right(Bool.and(linked(fs, t, seen, id), all_linked(fs, t, seen, rest)), all_linked(fs, t, seen, seen), h))
    case Some{+f}:
      +hf = Comp.and_left(Bool.and(linked(fs, t, seen, id), all_linked(fs, t, seen, rest)), all_linked(fs, t, seen, seen), h)
      reach_inv(Rev.member(seen, id), fs, t, id, rest, seen, f, em, Comp.and_left(linked(fs, t, seen, id), all_linked(fs, t, seen, rest), hf), Comp.and_right(linked(fs, t, seen, id), all_linked(fs, t, seen, rest), hf), Comp.and_right(Bool.and(linked(fs, t, seen, id), all_linked(fs, t, seen, rest)), all_linked(fs, t, seen, seen), h))

def step_inv(r: Main.Reach, +fs: List<&2, Main.Full>, +t: String, +h: {inv(fs, t, r) == True{} : Bool}) -> {inv(fs, t, Main.ancestry.step(fs, r)) == True{} : Bool}:
  match r:
    case Main.Reach{fr, +seen}:
      match fr:
        case Nil{}:
          h
        case +id <> +rest:
          next_inv(Main.find(fs, id), fs, t, id, rest, seen, {==}, h)

def go_inv(n: Nat, +fs: List<&2, Main.Full>, +t: String, +r: Main.Reach, +h: {inv(fs, t, r) == True{} : Bool}) -> {inv(fs, t, Main.ancestry.go(n, fs, r)) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+m:
      go_inv(m, fs, t, Main.ancestry.step(fs, r), step_inv(r, fs, t, h))

def seen_linked(r: Main.Reach, +fs: List<&2, Main.Full>, +t: String, h: {inv(fs, t, r) == True{} : Bool}) -> {all_linked(fs, t, Main.ancestry.seen(r), Main.ancestry.seen(r)) == True{} : Bool}:
  match r:
    case Main.Reach{+fr, +seen}:
      Comp.and_right(all_linked(fs, t, seen, fr), all_linked(fs, t, seen, seen), h)

# Everything the walk from `t` takes in is linked to `t`.
def reached_linked(+fs: List<&2, Main.Full>, +t: String) -> {all_linked(fs, t, Main.reached(fs, t), Main.reached(fs, t)) == True{} : Bool}:
  seen_linked(Main.ancestry.go(Nat.mul(2n, 1n+List.length(&2, Main.Full, fs)), fs, Main.Reach{[t], Nil{}}), fs, t,
    go_inv(Nat.mul(2n, 1n+List.length(&2, Main.Full, fs)), fs, t, Main.Reach{[t], Nil{}},
      AL.and_intro(Bool.and(linked(fs, t, Nil{}, t), True{}), True{}, AL.and_intro(linked(fs, t, Nil{}, t), True{}, ChainL.or_l(String.eq(t, t), False{}, S.eq_refl(t)), {==}), {==})))

# From linked digests to revisions listed
# --------------------------------------

def member_linked(xs: List<&2, String>, +fs: List<&2, Main.Full>, +t: String, +seen: List<&2, String>, +y: String, +h: {all_linked(fs, t, seen, xs) == True{} : Bool}, m: {Rev.member(xs, y) == True{} : Bool}) -> {linked(fs, t, seen, y) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({linked(fs, t, seen, y) == True{} : Bool}, S.false_true(m))
    case +x <> +rest:
      GL.member_cons({linked(fs, t, seen, y) == True{} : Bool}, x, rest, y, m,
        e => (%e : {linked(fs, t, seen, _) == True{} : Bool}; Comp.and_left(linked(fs, t, seen, x), all_linked(fs, t, seen, rest), h)),
        mr => member_linked(rest, fs, t, seen, y, Comp.and_right(linked(fs, t, seen, x), all_linked(fs, t, seen, rest), h), mr))

def keep_parented(b: Bool, +f: Main.Full, +xs: List<&2, Main.Full>, +y: String, h: {Main.parented(xs, y) == True{} : Bool}) -> {Main.parented(Main.keep_full(b, f, xs), y) == True{} : Bool}:
  match b:
    case True{}:
      ChainL.or_r(Rev.member(Main.parents_of(f), y), Main.parented(xs, y), h)
    case False{}:
      h

def find_parented_at(b: Bool, +i: String, +change: String, +parents: List<&2, String>, +supersedes: List<&2, String>, +author: String, +when: String, +revised_by: Maybe<&2, String>, +revised: Maybe<&2, String>, +facts: List<&2, Rev.Header>, +message: String, +rest: List<&2, Main.Full>, +R: List<&2, String>, +s: String, +y: String, +g: Main.Full, +eb: {String.eq(i, s) == b : Bool}, e: {Bool.pick(Maybe<&2, Main.Full>, b, Some{Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}}, Main.find(rest, s)) == Some{g} : Maybe<&2, Main.Full>}, +mR: {Rev.member(R, s) == True{} : Bool}, +mp: {Rev.member(Main.parents_of(g), y) == True{} : Bool}, ih: {Main.find(rest, s) == Some{g} : Maybe<&2, Main.Full>} -> {Main.parented(Main.among(rest, R), y) == True{} : Bool}) -> {Main.parented(Main.keep_full(Rev.member(R, i), Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}, Main.among(rest, R)), y) == True{} : Bool}:
  match b:
    case True{}:
      +d = B.some_eq_f(Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}, g, e)
      %Equal.sym(Bool, Rev.member(R, i), True{}, (%Equal.sym(String, i, s, S.eq_true(i, s, eb)) : {Rev.member(R, _) == True{} : Bool}; mR)) : {Main.parented(Main.keep_full(_, Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}, Main.among(rest, R)), y) == True{} : Bool}
      ChainL.or_l(Rev.member(parents, y), Main.parented(Main.among(rest, R), y), (%Equal.sym(Main.Full, Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}, g, d) : {Rev.member(Main.parents_of(_), y) == True{} : Bool}; mp))
    case False{}:
      keep_parented(Rev.member(R, i), Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}, Main.among(rest, R), y, ih(e))

# A parent of the revision a digest among `R` finds has a revision among
# those `among` keeps of `R` that it is a parent of.
def find_parented(fs: List<&2, Main.Full>, +R: List<&2, String>, +s: String, +y: String, +g: Main.Full, e: {Main.find(fs, s) == Some{g} : Maybe<&2, Main.Full>}, +mR: {Rev.member(R, s) == True{} : Bool}, +mp: {Rev.member(Main.parents_of(g), y) == True{} : Bool}) -> {Main.parented(Main.among(fs, R), y) == True{} : Bool}:
  match fs:
    case Nil{}:
      Empty.absurd({Main.parented(Main.among(Nil{}, R), y) == True{} : Bool}, (%e : {mdisc(_) : Type} Unit{}))
    case Main.Full{+i, +change, +parents, +supersedes, +author, +when, +revised_by, +revised, +facts, +message} <> +rest:
      find_parented_at(String.eq(i, s), i, change, parents, supersedes, author, when, revised_by, revised, facts, message, rest, R, s, y, g, {==}, e, mR, mp, h => find_parented(rest, R, s, y, g, h, mR, mp))

def pin_parented(m: Maybe<&2, Main.Full>, +fs: List<&2, Main.Full>, +R: List<&2, String>, +s: String, +y: String, +em: {Main.find(fs, s) == m : Maybe<&2, Main.Full>}, +mR: {Rev.member(R, s) == True{} : Bool}, h: {parent_in(m, y) == True{} : Bool}) -> {Main.parented(Main.among(fs, R), y) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Main.parented(Main.among(fs, R), y) == True{} : Bool}, S.false_true(h))
    case Some{+g}:
      find_parented(fs, R, s, y, g, em, mR, h)

def seen_parented(seen: List<&2, String>, +fs: List<&2, Main.Full>, +R: List<&2, String>, +y: String, +hs: {Main.all_held(R, seen) == True{} : Bool}, h: {seen_parent(fs, seen, y) == True{} : Bool}) -> {Main.parented(Main.among(fs, R), y) == True{} : Bool}:
  match seen:
    case Nil{}:
      Empty.absurd({Main.parented(Main.among(fs, R), y) == True{} : Bool}, S.false_true(h))
    case +s <> +rest:
      or_cases({Main.parented(Main.among(fs, R), y) == True{} : Bool}, parent_in(Main.find(fs, s), y), seen_parent(fs, rest, y), h,
        l => pin_parented(Main.find(fs, s), fs, R, s, y, {==}, Comp.and_left(Rev.member(R, s), Main.all_held(R, rest), hs), l),
        r => seen_parented(rest, fs, R, y, Comp.and_right(Rev.member(R, s), Main.all_held(R, rest), hs), r))

# A digest linked to the walk is the target, or a parent of a revision
# listed.
def linked_listed(+fs: List<&2, Main.Full>, +t: String, +R: List<&2, String>, +y: String, h: {linked(fs, t, R, y) == True{} : Bool}) -> {Bool.or(String.eq(y, t), Main.parented(Main.among(fs, R), y)) == True{} : Bool}:
  or_cases({Bool.or(String.eq(y, t), Main.parented(Main.among(fs, R), y)) == True{} : Bool}, String.eq(y, t), seen_parent(fs, R, y), h,
    l => ChainL.or_l(String.eq(y, t), Main.parented(Main.among(fs, R), y), l),
    r => ChainL.or_r(String.eq(y, t), Main.parented(Main.among(fs, R), y), seen_parented(R, fs, R, y, held_refl(R), r)))

# With a target
# -------------

# Every revision `log <t>` lists but `t` is a parent of one it lists.
def from_linked(xs: List<&2, Main.Full>, +fs: List<&2, Main.Full>, +t: String, +R: List<&2, String>, +hR: {all_linked(fs, t, R, R) == True{} : Bool}, +h: {amongst(Main.ids(fs), R, xs) == True{} : Bool}) -> {Main.span.linked(Main.among(fs, R), t, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      +hx = Comp.and_left(Bool.and(Rev.member(Main.ids(fs), Main.id_of(x)), Rev.member(R, Main.id_of(x))), amongst(Main.ids(fs), R, rest), h)
      AL.and_intro(Bool.or(String.eq(Main.id_of(x), t), Main.parented(Main.among(fs, R), Main.id_of(x))), Main.span.linked(Main.among(fs, R), t, rest),
        linked_listed(fs, t, R, Main.id_of(x), member_linked(R, fs, t, R, Main.id_of(x), hR, Comp.and_right(Rev.member(Main.ids(fs), Main.id_of(x)), Rev.member(R, Main.id_of(x)), hx))),
        from_linked(rest, fs, t, R, hR, Comp.and_right(Bool.and(Rev.member(Main.ids(fs), Main.id_of(x)), Rev.member(R, Main.id_of(x))), amongst(Main.ids(fs), R, rest), h)))

def reach_mono(already: Bool, +id: String, +rest: List<&2, String>, +seen: List<&2, String>, +ps: List<&2, String>, +x: String, h: {Rev.member(seen, x) == True{} : Bool}) -> {Rev.member(Main.ancestry.seen(Main.ancestry.reach(id, rest, seen, ps, already)), x) == True{} : Bool}:
  match already:
    case True{}:
      h
    case False{}:
      GL.member_tail(id, seen, x, h)

def next_mono(m: Maybe<&2, Main.Full>, +id: String, +rest: List<&2, String>, +seen: List<&2, String>, +x: String, h: {Rev.member(seen, x) == True{} : Bool}) -> {Rev.member(Main.ancestry.seen(Main.ancestry.next(id, rest, seen, m)), x) == True{} : Bool}:
  match m:
    case None{}:
      h
    case Some{+f}:
      reach_mono(Rev.member(seen, id), id, rest, seen, Main.parents_of(f), x, h)

def step_mono(r: Main.Reach, +fs: List<&2, Main.Full>, +x: String, h: {Rev.member(Main.ancestry.seen(r), x) == True{} : Bool}) -> {Rev.member(Main.ancestry.seen(Main.ancestry.step(fs, r)), x) == True{} : Bool}:
  match r:
    case Main.Reach{fr, +seen}:
      match fr:
        case Nil{}:
          h
        case +id <> +rest:
          next_mono(Main.find(fs, id), id, rest, seen, x, h)

# The walk forgets nothing it took in.
def go_mono(n: Nat, +fs: List<&2, Main.Full>, +r: Main.Reach, +x: String, h: {Rev.member(Main.ancestry.seen(r), x) == True{} : Bool}) -> {Rev.member(Main.ancestry.seen(Main.ancestry.go(n, fs, r)), x) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+m:
      go_mono(m, fs, Main.ancestry.step(fs, r), x, step_mono(r, fs, x, h))

def first_seen(mm: Maybe<&2, Main.Full>, +fs: List<&2, Main.Full>, +t: String, +em: {Main.find(fs, t) == mm : Maybe<&2, Main.Full>}, +h: {Rev.member(Main.ids(fs), t) == True{} : Bool}) -> {Rev.member(Main.ancestry.seen(Main.ancestry.next(t, Nil{}, Nil{}, mm)), t) == True{} : Bool}:
  match mm:
    case None{}:
      Empty.absurd({Rev.member(Main.ancestry.seen(Main.ancestry.next(t, Nil{}, Nil{}, None{})), t) == True{} : Bool}, S.true_false(Equal.trans(Bool, True{}, Rev.member(Main.ids(fs), t), False{}, Equal.sym(Bool, Rev.member(Main.ids(fs), t), True{}, h), ChainL.find_none(fs, t, em))))
    case Some{+f}:
      GL.member_head(t, Nil{})

# The walk from a revision the store holds takes that revision in.
def target_reached(+fs: List<&2, Main.Full>, +t: String, +h: {Rev.member(Main.ids(fs), t) == True{} : Bool}) -> {Rev.member(Main.reached(fs, t), t) == True{} : Bool}:
  go_mono(Nat.add(List.length(&2, Main.Full, fs), Nat.mul(1n, 1n+List.length(&2, Main.Full, fs))), fs, Main.ancestry.step(fs, Main.Reach{[t], Nil{}}), t, first_seen(Main.find(fs, t), fs, t, {==}, h))

def keep_member(b: Bool, +f: Main.Full, +xs: List<&2, Main.Full>, +t: String, h: {Rev.member(Main.ids(xs), t) == True{} : Bool}) -> {Rev.member(Main.ids(Main.keep_full(b, f, xs)), t) == True{} : Bool}:
  match b:
    case True{}:
      GL.member_tail(Main.id_of(f), Main.ids(xs), t, h)
    case False{}:
      h

# A revision held whose digest is in `R` is among what `among` keeps.
def listed_of(xs: List<&2, Main.Full>, +R: List<&2, String>, +t: String, hx: {Rev.member(Main.ids(xs), t) == True{} : Bool}, +hR: {Rev.member(R, t) == True{} : Bool}) -> {Rev.member(Main.ids(Main.among(xs, R)), t) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Rev.member(Main.ids(Main.among(Nil{}, R)), t) == True{} : Bool}, S.false_true(hx))
    case +f <> +rest:
      GL.member_cons({Rev.member(Main.ids(Main.among(f <> rest, R)), t) == True{} : Bool}, Main.id_of(f), Main.ids(rest), t, hx,
        +e => (%Equal.sym(Bool, Rev.member(R, Main.id_of(f)), True{}, (%Equal.sym(String, Main.id_of(f), t, e) : {Rev.member(R, _) == True{} : Bool}; hR)) : {Rev.member(Main.ids(Main.keep_full(_, f, Main.among(rest, R))), t) == True{} : Bool};
          GL.member_at(Main.id_of(f) <> Main.ids(Main.among(rest, R)), Main.id_of(f), t, e, GL.member_head(Main.id_of(f), Main.ids(Main.among(rest, R))))),
        m => keep_member(Rev.member(R, Main.id_of(f)), f, Main.among(rest, R), t, listed_of(rest, R, t, m, hR)))

def target_at(b: Bool, +fs: List<&2, Main.Full>, +t: String, +eb: {Rev.member(Main.ids(fs), t) == b : Bool}) -> {Bool.or(Bool.not(b), Rev.member(Main.ids(Main.among(fs, Main.reached(fs, t))), t)) == True{} : Bool}:
  match b:
    case True{}:
      listed_of(fs, Main.reached(fs, t), t, eb, target_reached(fs, t, eb))
    case False{}:
      {==}

# `log <t>` lists `t` wherever the store holds it.
def target_listed(+fs: List<&2, Main.Full>, +t: String) -> {Bool.or(Bool.not(Rev.member(Main.ids(fs), t)), Rev.member(Main.ids(Main.among(fs, Main.reached(fs, t))), t)) == True{} : Bool}:
  target_at(Rev.member(Main.ids(fs), t), fs, t, {==})

def from_ok(+fs: List<&2, Main.Full>, +t: String) -> {Main.span.from_ok(fs, t, Main.span.shown(fs, Main.Span.From{t})) == True{} : Bool}:
  +am = among_ok(Main.ids(fs), Main.reached(fs, t), fs, inids_self(fs))
  AL.and_intro(Main.span.held(fs, Main.among(fs, Main.reached(fs, t))), Bool.and(Bool.or(Bool.not(Rev.member(Main.ids(fs), t)), Rev.member(Main.ids(Main.among(fs, Main.reached(fs, t))), t)), Main.span.linked(Main.among(fs, Main.reached(fs, t)), t, Main.among(fs, Main.reached(fs, t)))),
    held_of(Main.among(fs, Main.reached(fs, t)), fs, Main.reached(fs, t), am),
    AL.and_intro(Bool.or(Bool.not(Rev.member(Main.ids(fs), t)), Rev.member(Main.ids(Main.among(fs, Main.reached(fs, t))), t)), Main.span.linked(Main.among(fs, Main.reached(fs, t)), t, Main.among(fs, Main.reached(fs, t))),
      target_listed(fs, t),
      from_linked(Main.among(fs, Main.reached(fs, t)), fs, t, Main.reached(fs, t), reached_linked(fs, t), am)))

# With `a..b`
# -----------

def keep_absent(b: Bool, +f: Main.Full, +xs: List<&2, Main.Full>, +a: String, hf: {String.eq(Main.id_of(f), a) == False{} : Bool}, h: {Rev.member(Main.ids(xs), a) == False{} : Bool}) -> {Rev.member(Main.ids(Main.keep_full(b, f, xs)), a) == False{} : Bool}:
  match b:
    case True{}:
      AL.or_false(String.eq(Main.id_of(f), a), Rev.member(Main.ids(xs), a), hf, h)
    case False{}:
      h

# What the store does not hold, nothing listed is.
def unheld_unlisted(xs: List<&2, Main.Full>, +R: List<&2, String>, +a: String, +h: {Rev.member(Main.ids(xs), a) == False{} : Bool}) -> {Rev.member(Main.ids(Main.among(xs, R)), a) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +f <> +rest:
      keep_absent(Rev.member(R, Main.id_of(f)), f, Main.among(rest, R), a,
        AL.or_false_l(String.eq(Main.id_of(f), a), Rev.member(Main.ids(rest), a), h),
        unheld_unlisted(rest, R, a, AL.or_false_r(String.eq(Main.id_of(f), a), Rev.member(Main.ids(rest), a), h)))

def out_at(b: Bool, +f: Main.Full, +xs: List<&2, Main.Full>, +R: List<&2, String>, +a: String, +eb: {Rev.member(R, Main.id_of(f)) == b : Bool}, +h: {Rev.member(R, a) == False{} : Bool}, ih: {Rev.member(Main.ids(xs), a) == False{} : Bool}) -> {Rev.member(Main.ids(Main.keep_full(b, f, xs)), a) == False{} : Bool}:
  match b:
    case True{}:
      AL.bool_cases({Rev.member(Main.ids(Main.keep_full(True{}, f, xs)), a) == False{} : Bool}, String.eq(Main.id_of(f), a),
        e => Empty.absurd({Rev.member(Main.ids(Main.keep_full(True{}, f, xs)), a) == False{} : Bool}, S.true_false(Equal.trans(Bool, True{}, Rev.member(R, a), False{}, Equal.sym(Bool, Rev.member(R, a), True{}, (%S.eq_true(Main.id_of(f), a, e) : {Rev.member(R, _) == True{} : Bool}; eb)), h))),
        e => AL.or_false(String.eq(Main.id_of(f), a), Rev.member(Main.ids(xs), a), e, ih))
    case False{}:
      ih

# What is not in `R`, nothing `among` keeps of `R` is.
def out_unlisted(xs: List<&2, Main.Full>, +R: List<&2, String>, +a: String, +h: {Rev.member(R, a) == False{} : Bool}) -> {Rev.member(Main.ids(Main.among(xs, R)), a) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +f <> +rest:
      out_at(Rev.member(R, Main.id_of(f)), f, Main.among(rest, R), R, a, {==}, h, out_unlisted(rest, R, a, h))

def a_at(b: Bool, +fs: List<&2, Main.Full>, +a: String, +bb: String, +eb: {Rev.member(Main.ids(fs), a) == b : Bool}) -> {Rev.member(Main.ids(Main.among(fs, Rev.without(Main.reached(fs, bb), Main.reached(fs, a)))), a) == False{} : Bool}:
  match b:
    case True{}:
      out_unlisted(fs, Rev.without(Main.reached(fs, bb), Main.reached(fs, a)), a, without_false(Main.reached(fs, bb), Main.reached(fs, a), a, target_reached(fs, a, eb)))
    case False{}:
      unheld_unlisted(fs, Rev.without(Main.reached(fs, bb), Main.reached(fs, a)), a, eb)

# `log a..b` never lists `a`.
def a_unlisted(+fs: List<&2, Main.Full>, +a: String, +b: String) -> {Rev.member(Main.ids(Main.among(fs, Rev.without(Main.reached(fs, b), Main.reached(fs, a)))), a) == False{} : Bool}:
  a_at(Rev.member(Main.ids(fs), a), fs, a, b, {==})

# Every revision `log a..b` lists is `b` or a parent of one `log b` lists.
def range_linked(xs: List<&2, Main.Full>, +fs: List<&2, Main.Full>, +a: String, +b: String, +hR: {all_linked(fs, b, Main.reached(fs, b), Main.reached(fs, b)) == True{} : Bool}, +h: {amongst(Main.ids(fs), Rev.without(Main.reached(fs, b), Main.reached(fs, a)), xs) == True{} : Bool}) -> {Main.span.linked(Main.among(fs, Main.reached(fs, b)), b, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      +hx = Comp.and_left(Bool.and(Rev.member(Main.ids(fs), Main.id_of(x)), Rev.member(Rev.without(Main.reached(fs, b), Main.reached(fs, a)), Main.id_of(x))), amongst(Main.ids(fs), Rev.without(Main.reached(fs, b), Main.reached(fs, a)), rest), h)
      +mw = Comp.and_right(Rev.member(Main.ids(fs), Main.id_of(x)), Rev.member(Rev.without(Main.reached(fs, b), Main.reached(fs, a)), Main.id_of(x)), hx)
      AL.and_intro(Bool.or(String.eq(Main.id_of(x), b), Main.parented(Main.among(fs, Main.reached(fs, b)), Main.id_of(x))), Main.span.linked(Main.among(fs, Main.reached(fs, b)), b, rest),
        linked_listed(fs, b, Main.reached(fs, b), Main.id_of(x), member_linked(Main.reached(fs, b), fs, b, Main.reached(fs, b), Main.id_of(x), hR, GL.without_sub(Main.reached(fs, b), Main.reached(fs, a), Main.id_of(x), mw))),
        range_linked(rest, fs, a, b, hR, Comp.and_right(Bool.and(Rev.member(Main.ids(fs), Main.id_of(x)), Rev.member(Rev.without(Main.reached(fs, b), Main.reached(fs, a)), Main.id_of(x))), amongst(Main.ids(fs), Rev.without(Main.reached(fs, b), Main.reached(fs, a)), rest), h)))

def range_ok(+fs: List<&2, Main.Full>, +a: String, +b: String) -> {Main.span.range_ok(fs, a, b, Main.span.shown(fs, Main.Span.Between{a, b})) == True{} : Bool}:
  +w = Rev.without(Main.reached(fs, b), Main.reached(fs, a))
  +am = among_ok(Main.ids(fs), w, fs, inids_self(fs))
  AL.and_intro(Main.span.held(fs, Main.among(fs, w)), Bool.and(Bool.not(Rev.member(Main.ids(Main.among(fs, w)), a)), Main.span.linked(Main.among(fs, Main.reached(fs, b)), b, Main.among(fs, w))),
    held_of(Main.among(fs, w), fs, w, am),
    AL.and_intro(Bool.not(Rev.member(Main.ids(Main.among(fs, w)), a)), Main.span.linked(Main.among(fs, Main.reached(fs, b)), b, Main.among(fs, w)),
      AL.not_true(Rev.member(Main.ids(Main.among(fs, w)), a), a_unlisted(fs, a, b)),
      range_linked(Main.among(fs, w), fs, a, b, reached_linked(fs, b), am)))

# `log` lists only what its span names.
def span_listed(+fs: List<&2, Main.Full>, +a: String, +b: String) -> {Bool.and(Main.span.from_ok(fs, b, Main.span.shown(fs, Main.Span.From{b})), Main.span.range_ok(fs, a, b, Main.span.shown(fs, Main.Span.Between{a, b}))) == True{} : Bool}:
  AL.and_intro(Main.span.from_ok(fs, b, Main.span.shown(fs, Main.Span.From{b})), Main.span.range_ok(fs, a, b, Main.span.shown(fs, Main.Span.Between{a, b})), from_ok(fs, b), range_ok(fs, a, b))
