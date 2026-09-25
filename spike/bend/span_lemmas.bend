# `log` lists what its span names, every one a revision the store holds.
# The walk out from a target takes in the target, and after it only
# parents of revisions it has taken in, so every revision listed but the
# target is a parent of one listed; and it takes the target in first,
# wherever the store holds it. It is given a step for each digest it
# starts from and each parent the store names, which is never fewer than
# it owes — a step for each digest waiting, and one for each parent of a
# revision not yet taken in — so it ends with nothing waiting; and then
# every parent the store holds of a revision it took in is one it took
# in, since each is taken in, waiting, or not the store's. Where the store
# files each revision once, the parents of a revision listed are the
# parents of the one the walk found, so none the store holds is left out.
# Of `a..b`, what is listed is what `log b` lists and `log a` does not, by
# what `among` keeps and `without` takes away.
import Base
import ./revision.bend as Rev
import ./commands.bend as Main
import ./string_lemmas.bend as S
import ./anchor_lemmas.bend as AL
import ./composition_lemmas.bend as Comp
import ./graph_lemmas.bend as GL
import ./chain_lemmas.bend as ChainL
import ./blamed_lemmas.bend as B
import ./position_lemmas.bend as Pos

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
  seen_linked(Main.ancestry.go(Main.reached.fuel(fs, [t]), fs, Main.Reach{[t], Nil{}}), fs, t,
    go_inv(Main.reached.fuel(fs, [t]), fs, t, Main.Reach{[t], Nil{}},
      AL.and_intro(Bool.and(linked(fs, t, Nil{}, t), True{}), True{}, AL.and_intro(linked(fs, t, Nil{}, t), True{}, ChainL.or_l(String.eq(t, t), False{}, S.eq_refl(t)), {==}), {==})))

# Arithmetic
# ----------

def le_trans(a: Nat, b: Nat, c: Nat, e1: {Nat.is_le(a, b) == True{} : Bool}, e2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      Empty.absurd({True{} == True{} : Bool}, Comp.false_true(e2))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, Comp.false_true(e1))
    case 1n+p 1n+q 0n:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(e2))
    case 1n+p 1n+q 1n+r:
      le_trans(p, q, r, e1, e2)

# is_le(x, y) implies is_le(c + x, c + y)
def add_le_l(c: Nat, -x: Nat, -y: Nat, e: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.add(c, x), Nat.add(c, y)) == True{} : Bool}:
  match c:
    case 0n:
      e
    case 1n+p:
      add_le_l(p, x, y, e)

# is_le(x, y) implies is_le(x, k + y)
def le_plus(k: Nat, +x: Nat, +y: Nat, e: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(x, Nat.add(k, y)) == True{} : Bool}:
  match k:
    case 0n:
      e
    case 1n++p:
      Comp.le_succ(x, Nat.add(p, y), le_plus(p, x, y, e))

# a + (c + b) is c + (a + b)
def add_swap(+a: Nat, c: Nat, -b: Nat) -> {Nat.add(a, Nat.add(c, b)) == Nat.add(c, Nat.add(a, b)) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+q:
      %Equal.sym(Nat, Nat.add(a, 1n+Nat.add(q, b)), 1n+Nat.add(a, Nat.add(q, b)), Pos.add_succ(a, Nat.add(q, b))) : {_ == 1n+Nat.add(q, Nat.add(a, b)) : Nat}
      %add_swap(a, q, b) : {1n+Nat.add(a, Nat.add(q, b)) == 1n+_ : Nat}
      {==}

def length_app(xs: List<&2, String>, -ys: List<&2, String>) -> {List.length(&2, String, List.append(&2, String, xs, ys)) == Nat.add(List.length(&2, String, xs), List.length(&2, String, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      %length_app(rest, ys) : {1n+List.length(&2, String, List.append(&2, String, rest, ys)) == 1n+_ : Nat}
      {==}

def eq_false_sym(+a: String, +b: String, h: {String.eq(a, b) == False{} : Bool}) -> {String.eq(b, a) == False{} : Bool}:
  AL.bool_cases({String.eq(b, a) == False{} : Bool}, String.eq(b, a),
    e => Empty.absurd({String.eq(b, a) == False{} : Bool}, S.true_false(Equal.trans(Bool, True{}, String.eq(a, b), False{}, (%Equal.sym(String, b, a, S.eq_true(b, a, e)) : {True{} == String.eq(a, _) : Bool}; Equal.sym(Bool, String.eq(a, a), True{}, S.eq_refl(a))), h))),
    e => e)

def not_false(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, S.false_true(h))
    case False{}:
      {==}

# What `find` finds
# -----------------

def find_cons(g: Main.Full, +rest: List<&2, Main.Full>, +s: String) -> {Main.find(g <> rest, s) == Bool.pick(Maybe<&2, Main.Full>, String.eq(Main.id_of(g), s), Some{g}, Main.find(rest, s)) : Maybe<&2, Main.Full>}:
  match g:
    case Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      {==}

def find_head(g: Main.Full, +rest: List<&2, Main.Full>) -> {Main.find(g <> rest, Main.id_of(g)) == Some{g} : Maybe<&2, Main.Full>}:
  match g:
    case Main.Full{+i, +change, +parents, +supersedes, +author, +when, +revised_by, +revised, +facts, +message}:
      %Equal.sym(Bool, String.eq(i, i), True{}, S.eq_refl(i)) : {Bool.pick(Maybe<&2, Main.Full>, _, Some{Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}}, Main.find(rest, i)) == Some{Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}} : Maybe<&2, Main.Full>}
      {==}

# What the store does not hold, `find` finds nothing of.
def find_absent(xs: List<&2, Main.Full>, +s: String, +h: {Rev.member(Main.ids(xs), s) == False{} : Bool}) -> {Main.find(xs, s) == None{} : Maybe<&2, Main.Full>}:
  match xs:
    case Nil{}:
      {==}
    case +g <> +rest:
      %Equal.sym(Maybe<&2, Main.Full>, Main.find(g <> rest, s), Bool.pick(Maybe<&2, Main.Full>, String.eq(Main.id_of(g), s), Some{g}, Main.find(rest, s)), find_cons(g, rest, s)) : {_ == None{} : Maybe<&2, Main.Full>}
      %Equal.sym(Bool, String.eq(Main.id_of(g), s), False{}, AL.or_false_l(String.eq(Main.id_of(g), s), Rev.member(Main.ids(rest), s), h)) : {Bool.pick(Maybe<&2, Main.Full>, _, Some{g}, Main.find(rest, s)) == None{} : Maybe<&2, Main.Full>}
      find_absent(rest, s, AL.or_false_r(String.eq(Main.id_of(g), s), Rev.member(Main.ids(rest), s), h))

# The walk has the steps it needs
# -------------------------------

# What the walk still owes: a step for each digest waiting, and one for
# each parent of a revision of the store it has not taken in.
def owed(fs: List<&2, Main.Full>, +seen: List<&2, String>) -> Nat:
  match fs:
    case Nil{}:
      0n
    case +f <> rest:
      Nat.add(Bool.pick(Nat, Rev.member(seen, Main.id_of(f)), 0n, List.length(&2, String, Main.parents_of(f))), owed(rest, seen))

def work(+fs: List<&2, Main.Full>, r: Main.Reach) -> Nat:
  match r:
    case Main.Reach{fr, +seen}:
      Nat.add(List.length(&2, String, fr), owed(fs, seen))

def waiting(r: Main.Reach) -> List<&2, String>:
  match r:
    case Main.Reach{fr, seen}:
      fr

# Before it takes anything in, the walk owes a step for each parent the
# store names.
def owed_nil(fs: List<&2, Main.Full>) -> {owed(fs, Nil{}) == Main.parent_count(fs) : Nat}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +rest:
      %owed_nil(rest) : {Nat.add(List.length(&2, String, Main.parents_of(f)), owed(rest, Nil{})) == Nat.add(List.length(&2, String, Main.parents_of(f)), _) : Nat}
      {==}

def owed_mono.at(b1: Bool, b2: Bool, +k: Nat, +A: Nat, +B: Nat, e: {Nat.is_le(A, B) == True{} : Bool}) -> {Nat.is_le(Nat.add(Bool.pick(Nat, Bool.or(b1, b2), 0n, k), A), Nat.add(Bool.pick(Nat, b2, 0n, k), B)) == True{} : Bool}:
  match b1 b2:
    case True{} True{}:
      e
    case True{} False{}:
      le_plus(k, A, B, e)
    case False{} True{}:
      e
    case False{} False{}:
      add_le_l(k, A, B, e)

# Taking a digest in owes no more than before.
def owed_mono(fs: List<&2, Main.Full>, +s: String, +seen: List<&2, String>) -> {Nat.is_le(owed(fs, s <> seen), owed(fs, seen)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +rest:
      owed_mono.at(String.eq(s, Main.id_of(f)), Rev.member(seen, Main.id_of(f)), List.length(&2, String, Main.parents_of(f)), owed(rest, s <> seen), owed(rest, seen), owed_mono(rest, s, seen))

def take_at(b: Bool, +g: Main.Full, +rest: List<&2, Main.Full>, +id: String, +seen: List<&2, String>, +f: Main.Full, +eb: {String.eq(Main.id_of(g), id) == b : Bool}, e: {Bool.pick(Maybe<&2, Main.Full>, b, Some{g}, Main.find(rest, id)) == Some{f} : Maybe<&2, Main.Full>}, +ns: {Rev.member(seen, id) == False{} : Bool}, ih: {Main.find(rest, id) == Some{f} : Maybe<&2, Main.Full>} -> {Nat.is_le(Nat.add(List.length(&2, String, Main.parents_of(f)), owed(rest, id <> seen)), owed(rest, seen)) == True{} : Bool}) -> {Nat.is_le(Nat.add(List.length(&2, String, Main.parents_of(f)), owed(g <> rest, id <> seen)), owed(g <> rest, seen)) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(String, Main.id_of(g), id, S.eq_true(Main.id_of(g), id, eb)) : {Nat.is_le(Nat.add(List.length(&2, String, Main.parents_of(f)), Nat.add(Bool.pick(Nat, Bool.or(String.eq(id, _), Rev.member(seen, _)), 0n, List.length(&2, String, Main.parents_of(g))), owed(rest, id <> seen))), Nat.add(Bool.pick(Nat, Rev.member(seen, _), 0n, List.length(&2, String, Main.parents_of(g))), owed(rest, seen))) == True{} : Bool}
      %Equal.sym(Bool, Rev.member(seen, id), False{}, ns) : {Nat.is_le(Nat.add(List.length(&2, String, Main.parents_of(f)), Nat.add(Bool.pick(Nat, Bool.or(String.eq(id, id), _), 0n, List.length(&2, String, Main.parents_of(g))), owed(rest, id <> seen))), Nat.add(Bool.pick(Nat, _, 0n, List.length(&2, String, Main.parents_of(g))), owed(rest, seen))) == True{} : Bool}
      %Equal.sym(Bool, String.eq(id, id), True{}, S.eq_refl(id)) : {Nat.is_le(Nat.add(List.length(&2, String, Main.parents_of(f)), Nat.add(Bool.pick(Nat, Bool.or(_, False{}), 0n, List.length(&2, String, Main.parents_of(g))), owed(rest, id <> seen))), Nat.add(Bool.pick(Nat, False{}, 0n, List.length(&2, String, Main.parents_of(g))), owed(rest, seen))) == True{} : Bool}
      %B.some_eq_f(g, f, e) : {Nat.is_le(Nat.add(List.length(&2, String, Main.parents_of(_)), owed(rest, id <> seen)), Nat.add(List.length(&2, String, Main.parents_of(g)), owed(rest, seen))) == True{} : Bool}
      add_le_l(List.length(&2, String, Main.parents_of(g)), owed(rest, id <> seen), owed(rest, seen), owed_mono(rest, id, seen))
    case False{}:
      %Equal.sym(Bool, String.eq(id, Main.id_of(g)), False{}, eq_false_sym(Main.id_of(g), id, eb)) : {Nat.is_le(Nat.add(List.length(&2, String, Main.parents_of(f)), Nat.add(Bool.pick(Nat, Bool.or(_, Rev.member(seen, Main.id_of(g))), 0n, List.length(&2, String, Main.parents_of(g))), owed(rest, id <> seen))), Nat.add(Bool.pick(Nat, Rev.member(seen, Main.id_of(g)), 0n, List.length(&2, String, Main.parents_of(g))), owed(rest, seen))) == True{} : Bool}
      %Equal.sym(Nat, Nat.add(List.length(&2, String, Main.parents_of(f)), Nat.add(Bool.pick(Nat, Rev.member(seen, Main.id_of(g)), 0n, List.length(&2, String, Main.parents_of(g))), owed(rest, id <> seen))), Nat.add(Bool.pick(Nat, Rev.member(seen, Main.id_of(g)), 0n, List.length(&2, String, Main.parents_of(g))), Nat.add(List.length(&2, String, Main.parents_of(f)), owed(rest, id <> seen))), add_swap(List.length(&2, String, Main.parents_of(f)), Bool.pick(Nat, Rev.member(seen, Main.id_of(g)), 0n, List.length(&2, String, Main.parents_of(g))), owed(rest, id <> seen))) : {Nat.is_le(_, Nat.add(Bool.pick(Nat, Rev.member(seen, Main.id_of(g)), 0n, List.length(&2, String, Main.parents_of(g))), owed(rest, seen))) == True{} : Bool}
      add_le_l(Bool.pick(Nat, Rev.member(seen, Main.id_of(g)), 0n, List.length(&2, String, Main.parents_of(g))), Nat.add(List.length(&2, String, Main.parents_of(f)), owed(rest, id <> seen)), owed(rest, seen), ih(e))

# Taking in a digest the walk has not, whose revision is `f`, owes the
# parents of `f` less than before.
def owed_take(fs: List<&2, Main.Full>, +id: String, +seen: List<&2, String>, +f: Main.Full, e: {Main.find(fs, id) == Some{f} : Maybe<&2, Main.Full>}, +ns: {Rev.member(seen, id) == False{} : Bool}) -> {Nat.is_le(Nat.add(List.length(&2, String, Main.parents_of(f)), owed(fs, id <> seen)), owed(fs, seen)) == True{} : Bool}:
  match fs:
    case Nil{}:
      Empty.absurd({Nat.is_le(Nat.add(List.length(&2, String, Main.parents_of(f)), owed(Nil{}, id <> seen)), owed(Nil{}, seen)) == True{} : Bool}, (%e : {mdisc(_) : Type} Unit{}))
    case +g <> +rest:
      take_at(String.eq(Main.id_of(g), id), g, rest, id, seen, f, {==}, Equal.trans(Maybe<&2, Main.Full>, Bool.pick(Maybe<&2, Main.Full>, String.eq(Main.id_of(g), id), Some{g}, Main.find(rest, id)), Main.find(g <> rest, id), Some{f}, Equal.sym(Maybe<&2, Main.Full>, Main.find(g <> rest, id), Bool.pick(Maybe<&2, Main.Full>, String.eq(Main.id_of(g), id), Some{g}, Main.find(rest, id)), find_cons(g, rest, id)), e), ns, h => owed_take(rest, id, seen, f, h, ns))

def reach_work(already: Bool, +fs: List<&2, Main.Full>, +id: String, +rest: List<&2, String>, +seen: List<&2, String>, +f: Main.Full, +ef: {Main.find(fs, id) == Some{f} : Maybe<&2, Main.Full>}, +ea: {Rev.member(seen, id) == already : Bool}) -> {Nat.is_le(1n+work(fs, Main.ancestry.reach(id, rest, seen, Main.parents_of(f), already)), work(fs, Main.Reach{id <> rest, seen})) == True{} : Bool}:
  match already:
    case True{}:
      Comp.le_refl(Nat.add(List.length(&2, String, rest), owed(fs, seen)))
    case False{}:
      %Equal.sym(Nat, List.length(&2, String, List.append(&2, String, rest, Main.parents_of(f))), Nat.add(List.length(&2, String, rest), List.length(&2, String, Main.parents_of(f))), length_app(rest, Main.parents_of(f))) : {Nat.is_le(1n+Nat.add(_, owed(fs, id <> seen)), 1n+Nat.add(List.length(&2, String, rest), owed(fs, seen))) == True{} : Bool}
      %Equal.sym(Nat, Nat.add(Nat.add(List.length(&2, String, rest), List.length(&2, String, Main.parents_of(f))), owed(fs, id <> seen)), Nat.add(List.length(&2, String, rest), Nat.add(List.length(&2, String, Main.parents_of(f)), owed(fs, id <> seen))), Pos.add_assoc(List.length(&2, String, rest), List.length(&2, String, Main.parents_of(f)), owed(fs, id <> seen))) : {Nat.is_le(1n+_, 1n+Nat.add(List.length(&2, String, rest), owed(fs, seen))) == True{} : Bool}
      add_le_l(List.length(&2, String, rest), Nat.add(List.length(&2, String, Main.parents_of(f)), owed(fs, id <> seen)), owed(fs, seen), owed_take(fs, id, seen, f, ef, ea))

def next_work(m: Maybe<&2, Main.Full>, +fs: List<&2, Main.Full>, +id: String, +rest: List<&2, String>, +seen: List<&2, String>, +em: {Main.find(fs, id) == m : Maybe<&2, Main.Full>}) -> {Nat.is_le(1n+work(fs, Main.ancestry.next(id, rest, seen, m)), work(fs, Main.Reach{id <> rest, seen})) == True{} : Bool}:
  match m:
    case None{}:
      Comp.le_refl(Nat.add(List.length(&2, String, rest), owed(fs, seen)))
    case Some{+f}:
      reach_work(Rev.member(seen, id), fs, id, rest, seen, f, em, {==})

def go_idle(n: Nat, +fs: List<&2, Main.Full>, +seen: List<&2, String>) -> {Main.ancestry.go(n, fs, Main.Reach{Nil{}, seen}) == Main.Reach{Nil{}, seen} : Main.Reach}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      go_idle(m, fs, seen)

# With as many steps as it owes, the walk ends with nothing waiting.
def go_waits(n: Nat, +fs: List<&2, Main.Full>, r: Main.Reach, h: {Nat.is_le(work(fs, r), n) == True{} : Bool}) -> {waiting(Main.ancestry.go(n, fs, r)) == Nil{} : List<&2, String>}:
  match n:
    case 0n:
      match r:
        case Main.Reach{fr, +seen}:
          match fr:
            case Nil{}:
              {==}
            case id <> +rest:
              Empty.absurd({waiting(Main.Reach{id <> rest, seen}) == Nil{} : List<&2, String>}, AL.le_zero(Nat.add(List.length(&2, String, rest), owed(fs, seen)), h))
    case 1n++m:
      match r:
        case Main.Reach{fr, +seen}:
          match fr:
            case Nil{}:
              %Equal.sym(Main.Reach, Main.ancestry.go(m, fs, Main.Reach{Nil{}, seen}), Main.Reach{Nil{}, seen}, go_idle(m, fs, seen)) : {waiting(_) == Nil{} : List<&2, String>}
              {==}
            case +id <> +rest:
              go_waits(m, fs, Main.ancestry.next(id, rest, seen, Main.find(fs, id)), le_trans(1n+work(fs, Main.ancestry.next(id, rest, seen, Main.find(fs, id))), work(fs, Main.Reach{id <> rest, seen}), 1n+m, next_work(Main.find(fs, id), fs, id, rest, seen, {==}), h))

# The walk starts owing no more steps than it is given.
def start_work(+fs: List<&2, Main.Full>, +t: String) -> {Nat.is_le(work(fs, Main.Reach{[t], Nil{}}), Main.reached.fuel(fs, [t])) == True{} : Bool}:
  %Equal.sym(Nat, owed(fs, Nil{}), Main.parent_count(fs), owed_nil(fs)) : {Nat.is_le(1n+_, 1n+Main.parent_count(fs)) == True{} : Bool}
  Comp.le_refl(Main.parent_count(fs))

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

# The walk from a revision the store holds takes that revision in: it is
# given a step at least, since it owes one for the revision itself.
def first_step(n: Nat, +fs: List<&2, Main.Full>, +t: String, le: {Nat.is_le(1n+owed(fs, Nil{}), n) == True{} : Bool}, +h: {Rev.member(Main.ids(fs), t) == True{} : Bool}) -> {Rev.member(Main.ancestry.seen(Main.ancestry.go(n, fs, Main.Reach{[t], Nil{}})), t) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Rev.member(Main.ancestry.seen(Main.ancestry.go(0n, fs, Main.Reach{[t], Nil{}})), t) == True{} : Bool}, AL.le_zero(owed(fs, Nil{}), le))
    case 1n+m:
      go_mono(m, fs, Main.ancestry.step(fs, Main.Reach{[t], Nil{}}), t, first_seen(Main.find(fs, t), fs, t, {==}, h))

def target_reached(+fs: List<&2, Main.Full>, +t: String, +h: {Rev.member(Main.ids(fs), t) == True{} : Bool}) -> {Rev.member(Main.reached(fs, t), t) == True{} : Bool}:
  first_step(Main.reached.fuel(fs, [t]), fs, t, start_work(fs, t), h)

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


# The walk leaves no parent behind
# --------------------------------

# A parent the walk owes nothing more: one taken in, one waiting, or one
# the store does not hold.
def covered(+H: List<&2, String>, +fr: List<&2, String>, +seen: List<&2, String>, +p: String) -> Bool:
  Bool.or(Rev.member(seen, p), Bool.or(Rev.member(fr, p), Bool.not(Rev.member(H, p))))

def all_covered(+H: List<&2, String>, +fr: List<&2, String>, +seen: List<&2, String>, ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case +p <> rest:
      Bool.and(covered(H, fr, seen, p), all_covered(H, fr, seen, rest))

def found_covered(+H: List<&2, String>, +fr: List<&2, String>, +seen: List<&2, String>, m: Maybe<&2, Main.Full>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{g}:
      all_covered(H, fr, seen, Main.parents_of(g))

def seen_covered(+fs: List<&2, Main.Full>, +H: List<&2, String>, +fr: List<&2, String>, +seen: List<&2, String>, ss: List<&2, String>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case +s <> rest:
      Bool.and(found_covered(H, fr, seen, Main.find(fs, s)), seen_covered(fs, H, fr, seen, rest))

# Every parent of a revision the walk took in is covered.
def cov(+fs: List<&2, Main.Full>, r: Main.Reach) -> Bool:
  match r:
    case Main.Reach{+fr, +seen}:
      seen_covered(fs, Main.ids(fs), fr, seen, seen)

def all_cov_member(xs: List<&2, String>, +H: List<&2, String>, +fr: List<&2, String>, +seen: List<&2, String>, +p: String, +h: {all_covered(H, fr, seen, xs) == True{} : Bool}, m: {Rev.member(xs, p) == True{} : Bool}) -> {covered(H, fr, seen, p) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({covered(H, fr, seen, p) == True{} : Bool}, S.false_true(m))
    case +x <> +rest:
      GL.member_cons({covered(H, fr, seen, p) == True{} : Bool}, x, rest, p, m,
        e => (%e : {covered(H, fr, seen, _) == True{} : Bool}; Comp.and_left(covered(H, fr, seen, x), all_covered(H, fr, seen, rest), h)),
        t => all_cov_member(rest, H, fr, seen, p, Comp.and_right(covered(H, fr, seen, x), all_covered(H, fr, seen, rest), h), t))

# What was covered stays covered where everything taken in and everything
# waiting before is covered after.
def cov_weak(+H: List<&2, String>, +fr: List<&2, String>, +seen: List<&2, String>, +fr2: List<&2, String>, +seen2: List<&2, String>, +p: String, +hs: {all_covered(H, fr2, seen2, seen) == True{} : Bool}, +hf: {all_covered(H, fr2, seen2, fr) == True{} : Bool}, h: {covered(H, fr, seen, p) == True{} : Bool}) -> {covered(H, fr2, seen2, p) == True{} : Bool}:
  or_cases({covered(H, fr2, seen2, p) == True{} : Bool}, Rev.member(seen, p), Bool.or(Rev.member(fr, p), Bool.not(Rev.member(H, p))), h,
    l => all_cov_member(seen, H, fr2, seen2, p, hs, l),
    r => or_cases({covered(H, fr2, seen2, p) == True{} : Bool}, Rev.member(fr, p), Bool.not(Rev.member(H, p)), r,
      m => all_cov_member(fr, H, fr2, seen2, p, hf, m),
      n => ChainL.or_r(Rev.member(seen2, p), Bool.or(Rev.member(fr2, p), Bool.not(Rev.member(H, p))), ChainL.or_r(Rev.member(fr2, p), Bool.not(Rev.member(H, p)), n))))

def all_cov_weak(ps: List<&2, String>, +H: List<&2, String>, +fr: List<&2, String>, +seen: List<&2, String>, +fr2: List<&2, String>, +seen2: List<&2, String>, +hs: {all_covered(H, fr2, seen2, seen) == True{} : Bool}, +hf: {all_covered(H, fr2, seen2, fr) == True{} : Bool}, +h: {all_covered(H, fr, seen, ps) == True{} : Bool}) -> {all_covered(H, fr2, seen2, ps) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +rest:
      AL.and_intro(covered(H, fr2, seen2, p), all_covered(H, fr2, seen2, rest),
        cov_weak(H, fr, seen, fr2, seen2, p, hs, hf, Comp.and_left(covered(H, fr, seen, p), all_covered(H, fr, seen, rest), h)),
        all_cov_weak(rest, H, fr, seen, fr2, seen2, hs, hf, Comp.and_right(covered(H, fr, seen, p), all_covered(H, fr, seen, rest), h)))

def found_cov_weak(m: Maybe<&2, Main.Full>, +H: List<&2, String>, +fr: List<&2, String>, +seen: List<&2, String>, +fr2: List<&2, String>, +seen2: List<&2, String>, +hs: {all_covered(H, fr2, seen2, seen) == True{} : Bool}, +hf: {all_covered(H, fr2, seen2, fr) == True{} : Bool}, h: {found_covered(H, fr, seen, m) == True{} : Bool}) -> {found_covered(H, fr2, seen2, m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+g}:
      all_cov_weak(Main.parents_of(g), H, fr, seen, fr2, seen2, hs, hf, h)

def seen_cov_weak(ss: List<&2, String>, +fs: List<&2, Main.Full>, +H: List<&2, String>, +fr: List<&2, String>, +seen: List<&2, String>, +fr2: List<&2, String>, +seen2: List<&2, String>, +hs: {all_covered(H, fr2, seen2, seen) == True{} : Bool}, +hf: {all_covered(H, fr2, seen2, fr) == True{} : Bool}, +h: {seen_covered(fs, H, fr, seen, ss) == True{} : Bool}) -> {seen_covered(fs, H, fr2, seen2, ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +rest:
      AL.and_intro(found_covered(H, fr2, seen2, Main.find(fs, s)), seen_covered(fs, H, fr2, seen2, rest),
        found_cov_weak(Main.find(fs, s), H, fr, seen, fr2, seen2, hs, hf, Comp.and_left(found_covered(H, fr, seen, Main.find(fs, s)), seen_covered(fs, H, fr, seen, rest), h)),
        seen_cov_weak(rest, fs, H, fr, seen, fr2, seen2, hs, hf, Comp.and_right(found_covered(H, fr, seen, Main.find(fs, s)), seen_covered(fs, H, fr, seen, rest), h)))

# Everything taken in is covered, and everything waiting.
def cov_seen(xs: List<&2, String>, +H: List<&2, String>, +fr: List<&2, String>, +seen: List<&2, String>, +h: {Main.all_held(seen, xs) == True{} : Bool}) -> {all_covered(H, fr, seen, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(covered(H, fr, seen, x), all_covered(H, fr, seen, rest),
        ChainL.or_l(Rev.member(seen, x), Bool.or(Rev.member(fr, x), Bool.not(Rev.member(H, x))), Comp.and_left(Rev.member(seen, x), Main.all_held(seen, rest), h)),
        cov_seen(rest, H, fr, seen, Comp.and_right(Rev.member(seen, x), Main.all_held(seen, rest), h)))

def cov_fr(xs: List<&2, String>, +H: List<&2, String>, +fr: List<&2, String>, +seen: List<&2, String>, +h: {Main.all_held(fr, xs) == True{} : Bool}) -> {all_covered(H, fr, seen, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(covered(H, fr, seen, x), all_covered(H, fr, seen, rest),
        ChainL.or_r(Rev.member(seen, x), Bool.or(Rev.member(fr, x), Bool.not(Rev.member(H, x))), ChainL.or_l(Rev.member(fr, x), Bool.not(Rev.member(H, x)), Comp.and_left(Rev.member(fr, x), Main.all_held(fr, rest), h))),
        cov_fr(rest, H, fr, seen, Comp.and_right(Rev.member(fr, x), Main.all_held(fr, rest), h)))

def held_app_l(xs: List<&2, String>, +rest: List<&2, String>, +pf: List<&2, String>, +h: {Main.all_held(rest, xs) == True{} : Bool}) -> {Main.all_held(List.append(&2, String, rest, pf), xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +more:
      AL.and_intro(Rev.member(List.append(&2, String, rest, pf), x), Main.all_held(List.append(&2, String, rest, pf), more),
        GL.append_left(rest, pf, x, Comp.and_left(Rev.member(rest, x), Main.all_held(rest, more), h)),
        held_app_l(more, rest, pf, Comp.and_right(Rev.member(rest, x), Main.all_held(rest, more), h)))

def held_app_r(xs: List<&2, String>, +rest: List<&2, String>, +pf: List<&2, String>, +h: {Main.all_held(pf, xs) == True{} : Bool}) -> {Main.all_held(List.append(&2, String, rest, pf), xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +more:
      AL.and_intro(Rev.member(List.append(&2, String, rest, pf), x), Main.all_held(List.append(&2, String, rest, pf), more),
        GL.append_right(rest, pf, x, Comp.and_left(Rev.member(pf, x), Main.all_held(pf, more), h)),
        held_app_r(more, rest, pf, Comp.and_right(Rev.member(pf, x), Main.all_held(pf, more), h)))

# A digest taken off the frontier and passed over, where it is covered
# without it, leaves everything covered.
def pass_cov(+fs: List<&2, Main.Full>, +id: String, +rest: List<&2, String>, +seen: List<&2, String>, +hid: {covered(Main.ids(fs), rest, seen, id) == True{} : Bool}, +h: {cov(fs, Main.Reach{id <> rest, seen}) == True{} : Bool}) -> {cov(fs, Main.Reach{rest, seen}) == True{} : Bool}:
  seen_cov_weak(seen, fs, Main.ids(fs), id <> rest, seen, rest, seen,
    cov_seen(seen, Main.ids(fs), rest, seen, held_refl(seen)),
    AL.and_intro(covered(Main.ids(fs), rest, seen, id), all_covered(Main.ids(fs), rest, seen, rest), hid, cov_fr(rest, Main.ids(fs), rest, seen, held_refl(rest))),
    h)

def reach_cov(already: Bool, +fs: List<&2, Main.Full>, +id: String, +rest: List<&2, String>, +seen: List<&2, String>, +f: Main.Full, +ef: {Main.find(fs, id) == Some{f} : Maybe<&2, Main.Full>}, +ea: {Rev.member(seen, id) == already : Bool}, +h: {cov(fs, Main.Reach{id <> rest, seen}) == True{} : Bool}) -> {cov(fs, Main.ancestry.reach(id, rest, seen, Main.parents_of(f), already)) == True{} : Bool}:
  match already:
    case True{}:
      pass_cov(fs, id, rest, seen, ChainL.or_l(Rev.member(seen, id), Bool.or(Rev.member(rest, id), Bool.not(Rev.member(Main.ids(fs), id))), ea), h)
    case False{}:
      AL.and_intro(found_covered(Main.ids(fs), List.append(&2, String, rest, Main.parents_of(f)), id <> seen, Main.find(fs, id)), seen_covered(fs, Main.ids(fs), List.append(&2, String, rest, Main.parents_of(f)), id <> seen, seen),
        (%Equal.sym(Maybe<&2, Main.Full>, Main.find(fs, id), Some{f}, ef) : {found_covered(Main.ids(fs), List.append(&2, String, rest, Main.parents_of(f)), id <> seen, _) == True{} : Bool}; cov_fr(Main.parents_of(f), Main.ids(fs), List.append(&2, String, rest, Main.parents_of(f)), id <> seen, held_app_r(Main.parents_of(f), rest, Main.parents_of(f), held_refl(Main.parents_of(f))))),
        seen_cov_weak(seen, fs, Main.ids(fs), id <> rest, seen, List.append(&2, String, rest, Main.parents_of(f)), id <> seen,
          cov_seen(seen, Main.ids(fs), List.append(&2, String, rest, Main.parents_of(f)), id <> seen, held_weak(id, seen, seen, held_refl(seen))),
          AL.and_intro(covered(Main.ids(fs), List.append(&2, String, rest, Main.parents_of(f)), id <> seen, id), all_covered(Main.ids(fs), List.append(&2, String, rest, Main.parents_of(f)), id <> seen, rest),
            ChainL.or_l(Rev.member(id <> seen, id), Bool.or(Rev.member(List.append(&2, String, rest, Main.parents_of(f)), id), Bool.not(Rev.member(Main.ids(fs), id))), GL.member_head(id, seen)),
            cov_fr(rest, Main.ids(fs), List.append(&2, String, rest, Main.parents_of(f)), id <> seen, held_app_l(rest, rest, Main.parents_of(f), held_refl(rest)))),
          h))

def next_cov(m: Maybe<&2, Main.Full>, +fs: List<&2, Main.Full>, +id: String, +rest: List<&2, String>, +seen: List<&2, String>, +em: {Main.find(fs, id) == m : Maybe<&2, Main.Full>}, +h: {cov(fs, Main.Reach{id <> rest, seen}) == True{} : Bool}) -> {cov(fs, Main.ancestry.next(id, rest, seen, m)) == True{} : Bool}:
  match m:
    case None{}:
      pass_cov(fs, id, rest, seen, ChainL.or_r(Rev.member(seen, id), Bool.or(Rev.member(rest, id), Bool.not(Rev.member(Main.ids(fs), id))), ChainL.or_r(Rev.member(rest, id), Bool.not(Rev.member(Main.ids(fs), id)), AL.not_true(Rev.member(Main.ids(fs), id), ChainL.find_none(fs, id, em)))), h)
    case Some{+f}:
      reach_cov(Rev.member(seen, id), fs, id, rest, seen, f, em, {==}, h)

def step_cov(r: Main.Reach, +fs: List<&2, Main.Full>, +h: {cov(fs, r) == True{} : Bool}) -> {cov(fs, Main.ancestry.step(fs, r)) == True{} : Bool}:
  match r:
    case Main.Reach{fr, +seen}:
      match fr:
        case Nil{}:
          h
        case +id <> +rest:
          next_cov(Main.find(fs, id), fs, id, rest, seen, {==}, h)

def go_cov(n: Nat, +fs: List<&2, Main.Full>, +r: Main.Reach, +h: {cov(fs, r) == True{} : Bool}) -> {cov(fs, Main.ancestry.go(n, fs, r)) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+m:
      go_cov(m, fs, Main.ancestry.step(fs, r), step_cov(r, fs, h))

def end_covered(r: Main.Reach, +fs: List<&2, Main.Full>, hw: {waiting(r) == Nil{} : List<&2, String>}, hc: {cov(fs, r) == True{} : Bool}) -> {seen_covered(fs, Main.ids(fs), Nil{}, Main.ancestry.seen(r), Main.ancestry.seen(r)) == True{} : Bool}:
  match r:
    case Main.Reach{fr, +seen}:
      %hw : {seen_covered(fs, Main.ids(fs), _, seen, seen) == True{} : Bool}
      hc

# When the walk from `t` ends, every parent the store holds of a revision
# it took in is one it took in.
def reached_covered(+fs: List<&2, Main.Full>, +t: String) -> {seen_covered(fs, Main.ids(fs), Nil{}, Main.reached(fs, t), Main.reached(fs, t)) == True{} : Bool}:
  end_covered(Main.ancestry.go(Main.reached.fuel(fs, [t]), fs, Main.Reach{[t], Nil{}}), fs,
    go_waits(Main.reached.fuel(fs, [t]), fs, Main.Reach{[t], Nil{}}, start_work(fs, t)),
    go_cov(Main.reached.fuel(fs, [t]), fs, Main.Reach{[t], Nil{}}, {==}))

# From the walk to what is listed
# -------------------------------

def member_cov(ss: List<&2, String>, +xs: List<&2, Main.Full>, +H: List<&2, String>, +fr: List<&2, String>, +R: List<&2, String>, +s: String, +h: {seen_covered(xs, H, fr, R, ss) == True{} : Bool}, m: {Rev.member(ss, s) == True{} : Bool}) -> {found_covered(H, fr, R, Main.find(xs, s)) == True{} : Bool}:
  match ss:
    case Nil{}:
      Empty.absurd({found_covered(H, fr, R, Main.find(xs, s)) == True{} : Bool}, S.false_true(m))
    case +y <> +more:
      GL.member_cons({found_covered(H, fr, R, Main.find(xs, s)) == True{} : Bool}, y, more, s, m,
        e => (%e : {found_covered(H, fr, R, Main.find(xs, _)) == True{} : Bool}; Comp.and_left(found_covered(H, fr, R, Main.find(xs, y)), seen_covered(xs, H, fr, R, more), h)),
        t => member_cov(more, xs, H, fr, R, s, Comp.and_right(found_covered(H, fr, R, Main.find(xs, y)), seen_covered(xs, H, fr, R, more), h), t))

def fc_rest(b: Bool, +g: Main.Full, +rest: List<&2, Main.Full>, +s: String, +H: List<&2, String>, +fr: List<&2, String>, +R: List<&2, String>, +eb: {String.eq(Main.id_of(g), s) == b : Bool}, +ni: {Rev.member(Main.ids(rest), Main.id_of(g)) == False{} : Bool}, h: {found_covered(H, fr, R, Bool.pick(Maybe<&2, Main.Full>, b, Some{g}, Main.find(rest, s))) == True{} : Bool}) -> {found_covered(H, fr, R, Main.find(rest, s)) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Maybe<&2, Main.Full>, Main.find(rest, s), None{}, find_absent(rest, s, (%S.eq_true(Main.id_of(g), s, eb) : {Rev.member(Main.ids(rest), _) == False{} : Bool}; ni))) : {found_covered(H, fr, R, _) == True{} : Bool}
      {==}
    case False{}:
      h

# Where the store files `g` once, what is covered of the store is covered
# of the rest of it.
def seen_cov_rest(ss: List<&2, String>, +g: Main.Full, +rest: List<&2, Main.Full>, +H: List<&2, String>, +fr: List<&2, String>, +R: List<&2, String>, +ni: {Rev.member(Main.ids(rest), Main.id_of(g)) == False{} : Bool}, +h: {seen_covered(g <> rest, H, fr, R, ss) == True{} : Bool}) -> {seen_covered(rest, H, fr, R, ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +more:
      AL.and_intro(found_covered(H, fr, R, Main.find(rest, s)), seen_covered(rest, H, fr, R, more),
        fc_rest(String.eq(Main.id_of(g), s), g, rest, s, H, fr, R, {==}, ni, (%find_cons(g, rest, s) : {found_covered(H, fr, R, _) == True{} : Bool}; Comp.and_left(found_covered(H, fr, R, Main.find(g <> rest, s)), seen_covered(g <> rest, H, fr, R, more), h))),
        seen_cov_rest(more, g, rest, H, fr, R, ni, Comp.and_right(found_covered(H, fr, R, Main.find(g <> rest, s)), seen_covered(g <> rest, H, fr, R, more), h)))

# A parent covered when the walk ends is one the store does not hold, or
# one listed.
def one_listed(+fs: List<&2, Main.Full>, +R: List<&2, String>, +p: String, h: {covered(Main.ids(fs), Nil{}, R, p) == True{} : Bool}) -> {Bool.or(Bool.not(Rev.member(Main.ids(fs), p)), Rev.member(Main.ids(Main.among(fs, R)), p)) == True{} : Bool}:
  or_cases({Bool.or(Bool.not(Rev.member(Main.ids(fs), p)), Rev.member(Main.ids(Main.among(fs, R)), p)) == True{} : Bool}, Rev.member(R, p), Bool.or(Rev.member(Nil{}, p), Bool.not(Rev.member(Main.ids(fs), p))), h,
    mr => AL.bool_cases({Bool.or(Bool.not(Rev.member(Main.ids(fs), p)), Rev.member(Main.ids(Main.among(fs, R)), p)) == True{} : Bool}, Rev.member(Main.ids(fs), p),
      mh => ChainL.or_r(Bool.not(Rev.member(Main.ids(fs), p)), Rev.member(Main.ids(Main.among(fs, R)), p), listed_of(fs, R, p, mh, mr)),
      nh => ChainL.or_l(Bool.not(Rev.member(Main.ids(fs), p)), Rev.member(Main.ids(Main.among(fs, R)), p), AL.not_true(Rev.member(Main.ids(fs), p), nh))),
    n => ChainL.or_l(Bool.not(Rev.member(Main.ids(fs), p)), Rev.member(Main.ids(Main.among(fs, R)), p), n))

def par_listed(ps: List<&2, String>, +fs: List<&2, Main.Full>, +R: List<&2, String>, +h: {all_covered(Main.ids(fs), Nil{}, R, ps) == True{} : Bool}) -> {Main.span.parents_listed(fs, Main.among(fs, R), ps) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +rest:
      AL.and_intro(Bool.or(Bool.not(Rev.member(Main.ids(fs), p)), Rev.member(Main.ids(Main.among(fs, R)), p)), Main.span.parents_listed(fs, Main.among(fs, R), rest),
        one_listed(fs, R, p, Comp.and_left(covered(Main.ids(fs), Nil{}, R, p), all_covered(Main.ids(fs), Nil{}, R, rest), h)),
        par_listed(rest, fs, R, Comp.and_right(covered(Main.ids(fs), Nil{}, R, p), all_covered(Main.ids(fs), Nil{}, R, rest), h)))

def closed_keep(b: Bool, +g: Main.Full, +rest: List<&2, Main.Full>, +fs: List<&2, Main.Full>, +R: List<&2, String>, +eb: {Rev.member(R, Main.id_of(g)) == b : Bool}, +hc: {seen_covered(g <> rest, Main.ids(fs), Nil{}, R, R) == True{} : Bool}, ih: {Main.span.closed(fs, Main.among(fs, R), Main.among(rest, R)) == True{} : Bool}) -> {Main.span.closed(fs, Main.among(fs, R), Main.keep_full(b, g, Main.among(rest, R))) == True{} : Bool}:
  match b:
    case True{}:
      AL.and_intro(Main.span.parents_listed(fs, Main.among(fs, R), Main.parents_of(g)), Main.span.closed(fs, Main.among(fs, R), Main.among(rest, R)),
        par_listed(Main.parents_of(g), fs, R, (%find_head(g, rest) : {found_covered(Main.ids(fs), Nil{}, R, _) == True{} : Bool}; member_cov(R, g <> rest, Main.ids(fs), Nil{}, R, Main.id_of(g), hc, eb))),
        ih)
    case False{}:
      ih

# Where each revision is filed once, every parent the store holds of a
# revision `among` keeps of what the walk took in is listed too.
def closed_among(xs: List<&2, Main.Full>, +fs: List<&2, Main.Full>, +R: List<&2, String>, +hd: {Main.span.filed_once(xs) == True{} : Bool}, +hc: {seen_covered(xs, Main.ids(fs), Nil{}, R, R) == True{} : Bool}) -> {Main.span.closed(fs, Main.among(fs, R), Main.among(xs, R)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +g <> +rest:
      closed_keep(Rev.member(R, Main.id_of(g)), g, rest, fs, R, {==}, hc,
        closed_among(rest, fs, R, Comp.and_right(Bool.not(Rev.member(Main.ids(rest), Main.id_of(g))), Main.span.filed_once(rest), hd),
          seen_cov_rest(R, g, rest, Main.ids(fs), Nil{}, R, not_false(Rev.member(Main.ids(rest), Main.id_of(g)), Comp.and_left(Bool.not(Rev.member(Main.ids(rest), Main.id_of(g))), Main.span.filed_once(rest), hd)), hc)))

def closed_at(b: Bool, +fs: List<&2, Main.Full>, +t: String, +eb: {Main.span.filed_once(fs) == b : Bool}) -> {Bool.or(Bool.not(b), Main.span.closed(fs, Main.among(fs, Main.reached(fs, t)), Main.among(fs, Main.reached(fs, t)))) == True{} : Bool}:
  match b:
    case True{}:
      closed_among(fs, fs, Main.reached(fs, t), eb, reached_covered(fs, t))
    case False{}:
      {==}

def from_ok(+fs: List<&2, Main.Full>, +t: String) -> {Main.span.from_ok(fs, t, Main.span.shown(fs, Main.Span.From{t})) == True{} : Bool}:
  +am = among_ok(Main.ids(fs), Main.reached(fs, t), fs, inids_self(fs))
  AL.and_intro(Bool.and(Main.span.held(fs, Main.among(fs, Main.reached(fs, t))), Bool.or(Bool.not(Rev.member(Main.ids(fs), t)), Rev.member(Main.ids(Main.among(fs, Main.reached(fs, t))), t))), Bool.and(Main.span.linked(Main.among(fs, Main.reached(fs, t)), t, Main.among(fs, Main.reached(fs, t))), Bool.or(Bool.not(Main.span.filed_once(fs)), Main.span.closed(fs, Main.among(fs, Main.reached(fs, t)), Main.among(fs, Main.reached(fs, t))))),
    AL.and_intro(Main.span.held(fs, Main.among(fs, Main.reached(fs, t))), Bool.or(Bool.not(Rev.member(Main.ids(fs), t)), Rev.member(Main.ids(Main.among(fs, Main.reached(fs, t))), t)),
      held_of(Main.among(fs, Main.reached(fs, t)), fs, Main.reached(fs, t), am),
      target_listed(fs, t)),
    AL.and_intro(Main.span.linked(Main.among(fs, Main.reached(fs, t)), t, Main.among(fs, Main.reached(fs, t))), Bool.or(Bool.not(Main.span.filed_once(fs)), Main.span.closed(fs, Main.among(fs, Main.reached(fs, t)), Main.among(fs, Main.reached(fs, t)))),
      from_linked(Main.among(fs, Main.reached(fs, t)), fs, t, Main.reached(fs, t), reached_linked(fs, t), am),
      closed_at(Main.span.filed_once(fs), fs, t, {==})))

# With `a..b`
# -----------

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

# Every revision `log a..b` lists is one `log b` lists and `log a` does
# not.
def parted_of(xs: List<&2, Main.Full>, +fs: List<&2, Main.Full>, +a: String, +b: String, +h: {amongst(Main.ids(fs), Rev.without(Main.reached(fs, b), Main.reached(fs, a)), xs) == True{} : Bool}) -> {Main.span.parted(fs, a, b, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      +hx = Comp.and_left(Bool.and(Rev.member(Main.ids(fs), Main.id_of(x)), Rev.member(Rev.without(Main.reached(fs, b), Main.reached(fs, a)), Main.id_of(x))), amongst(Main.ids(fs), Rev.without(Main.reached(fs, b), Main.reached(fs, a)), rest), h)
      +mw = Comp.and_right(Rev.member(Main.ids(fs), Main.id_of(x)), Rev.member(Rev.without(Main.reached(fs, b), Main.reached(fs, a)), Main.id_of(x)), hx)
      AL.and_intro(Bool.and(Rev.member(Main.ids(Main.among(fs, Main.reached(fs, b))), Main.id_of(x)), Bool.not(Rev.member(Main.ids(Main.among(fs, Main.reached(fs, a))), Main.id_of(x)))), Main.span.parted(fs, a, b, rest),
        AL.and_intro(Rev.member(Main.ids(Main.among(fs, Main.reached(fs, b))), Main.id_of(x)), Bool.not(Rev.member(Main.ids(Main.among(fs, Main.reached(fs, a))), Main.id_of(x))),
          listed_of(fs, Main.reached(fs, b), Main.id_of(x), Comp.and_left(Rev.member(Main.ids(fs), Main.id_of(x)), Rev.member(Rev.without(Main.reached(fs, b), Main.reached(fs, a)), Main.id_of(x)), hx), GL.without_sub(Main.reached(fs, b), Main.reached(fs, a), Main.id_of(x), mw)),
          AL.not_true(Rev.member(Main.ids(Main.among(fs, Main.reached(fs, a))), Main.id_of(x)), out_unlisted(fs, Main.reached(fs, a), Main.id_of(x), without_out(Main.reached(fs, b), Main.reached(fs, a), Main.id_of(x), mw)))),
        parted_of(rest, fs, a, b, Comp.and_right(Bool.and(Rev.member(Main.ids(fs), Main.id_of(x)), Rev.member(Rev.without(Main.reached(fs, b), Main.reached(fs, a)), Main.id_of(x))), amongst(Main.ids(fs), Rev.without(Main.reached(fs, b), Main.reached(fs, a)), rest), h)))

def kept_one(+fs: List<&2, Main.Full>, +a: String, +b: String, +y: String, +hy: {Rev.member(Main.ids(fs), y) == True{} : Bool}, +mb: {Rev.member(Main.reached(fs, b), y) == True{} : Bool}) -> {Bool.or(Rev.member(Main.ids(Main.among(fs, Main.reached(fs, a))), y), Rev.member(Main.ids(Main.among(fs, Rev.without(Main.reached(fs, b), Main.reached(fs, a)))), y)) == True{} : Bool}:
  AL.bool_cases({Bool.or(Rev.member(Main.ids(Main.among(fs, Main.reached(fs, a))), y), Rev.member(Main.ids(Main.among(fs, Rev.without(Main.reached(fs, b), Main.reached(fs, a)))), y)) == True{} : Bool}, Rev.member(Main.reached(fs, a), y),
    ma => ChainL.or_l(Rev.member(Main.ids(Main.among(fs, Main.reached(fs, a))), y), Rev.member(Main.ids(Main.among(fs, Rev.without(Main.reached(fs, b), Main.reached(fs, a)))), y), listed_of(fs, Main.reached(fs, a), y, hy, ma)),
    na => ChainL.or_r(Rev.member(Main.ids(Main.among(fs, Main.reached(fs, a))), y), Rev.member(Main.ids(Main.among(fs, Rev.without(Main.reached(fs, b), Main.reached(fs, a)))), y), listed_of(fs, Rev.without(Main.reached(fs, b), Main.reached(fs, a)), y, hy, GL.without_in(Main.reached(fs, b), Main.reached(fs, a), y, mb, na))))

# Every revision `log b` lists and `log a` does not, `log a..b` lists.
def kept_of(ys: List<&2, Main.Full>, +fs: List<&2, Main.Full>, +a: String, +b: String, +h: {amongst(Main.ids(fs), Main.reached(fs, b), ys) == True{} : Bool}) -> {Main.span.kept(fs, a, Main.among(fs, Rev.without(Main.reached(fs, b), Main.reached(fs, a))), ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +rest:
      +hy = Comp.and_left(Bool.and(Rev.member(Main.ids(fs), Main.id_of(y)), Rev.member(Main.reached(fs, b), Main.id_of(y))), amongst(Main.ids(fs), Main.reached(fs, b), rest), h)
      AL.and_intro(Bool.or(Rev.member(Main.ids(Main.among(fs, Main.reached(fs, a))), Main.id_of(y)), Rev.member(Main.ids(Main.among(fs, Rev.without(Main.reached(fs, b), Main.reached(fs, a)))), Main.id_of(y))), Main.span.kept(fs, a, Main.among(fs, Rev.without(Main.reached(fs, b), Main.reached(fs, a))), rest),
        kept_one(fs, a, b, Main.id_of(y), Comp.and_left(Rev.member(Main.ids(fs), Main.id_of(y)), Rev.member(Main.reached(fs, b), Main.id_of(y)), hy), Comp.and_right(Rev.member(Main.ids(fs), Main.id_of(y)), Rev.member(Main.reached(fs, b), Main.id_of(y)), hy)),
        kept_of(rest, fs, a, b, Comp.and_right(Bool.and(Rev.member(Main.ids(fs), Main.id_of(y)), Rev.member(Main.reached(fs, b), Main.id_of(y))), amongst(Main.ids(fs), Main.reached(fs, b), rest), h)))

def range_ok(+fs: List<&2, Main.Full>, +a: String, +b: String) -> {Main.span.range_ok(fs, a, b, Main.span.shown(fs, Main.Span.Between{a, b})) == True{} : Bool}:
  AL.and_intro(Main.span.parted(fs, a, b, Main.span.shown(fs, Main.Span.Between{a, b})), Main.span.kept(fs, a, Main.span.shown(fs, Main.Span.Between{a, b}), Main.span.shown(fs, Main.Span.From{b})),
    parted_of(Main.among(fs, Rev.without(Main.reached(fs, b), Main.reached(fs, a))), fs, a, b, among_ok(Main.ids(fs), Rev.without(Main.reached(fs, b), Main.reached(fs, a)), fs, inids_self(fs))),
    kept_of(Main.among(fs, Main.reached(fs, b)), fs, a, b, among_ok(Main.ids(fs), Main.reached(fs, b), fs, inids_self(fs))))

# `log` lists what its span names.
def span_listed(+fs: List<&2, Main.Full>, +a: String, +b: String) -> {Bool.and(Main.span.from_ok(fs, b, Main.span.shown(fs, Main.Span.From{b})), Main.span.range_ok(fs, a, b, Main.span.shown(fs, Main.Span.Between{a, b}))) == True{} : Bool}:
  AL.and_intro(Main.span.from_ok(fs, b, Main.span.shown(fs, Main.Span.From{b})), Main.span.range_ok(fs, a, b, Main.span.shown(fs, Main.Span.Between{a, b})), from_ok(fs, b), range_ok(fs, a, b))
