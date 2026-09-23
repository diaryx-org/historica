# Every walk keeps the invariant. `insert_at_gap` needs a view whose
# reading finishes within its fuel and reads no element twice; a run's own
# attaches keep that (`anchor_lemmas`), but in a merge an element also
# lands among siblings a concurrent event put there. So the first half of
# this file shows any fresh leaf, attached anywhere, keeps the invariant:
# the reading of the new tree is the old one with the leaf spliced in once
# where its parent's list is read, or not at all. The second half carries
# that through an event's actions and a whole walk, and concludes that an
# event which had seen every event walked before it reads its document
# exactly as plain replay does.
import Base
import ./ops.bend as Ops
import ./merge.bend as M
import ./replay_spec.bend as Spec
import ./cursor_spec.bend as Cursor
import ./composition_lemmas.bend as Comp
import ./replay_lemmas.bend as L
import ./merge_lemmas.bend as ML
import ./anchor_lemmas.bend as AL
import ./semantic_replay.bend as Block
import ./linear_lemmas.bend as Lin
import ./parser_lemmas.bend as PL

# Numbers
# -------

def sub0(x: Nat) -> {Nat.sub(0n, x) == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def sub_succ(q: Nat, a: Nat, le: {Nat.is_le(a, q) == True{} : Bool}) -> {Nat.sub(1n+q, a) == 1n+Nat.sub(q, a) : Nat}:
  match q a:
    case 0n 0n:
      {==}
    case 0n 1n+b:
      Empty.absurd({Nat.sub(1n, 1n+b) == 1n+Nat.sub(0n, 1n+b) : Nat}, Comp.false_true(le))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+b:
      sub_succ(p, b, le)

# Where an element hangs, read off its place.
def hangs_of(n: M.Node, +P: Maybe<&2, M.Name>, +R: Bool, +q: Maybe<&2, M.Name>, +r: Bool, hp: {M.Node.place(n) == M.Place{P, R} : M.Place}) -> {M.Node.hangs(n, q, r) == Bool.and(M.Name.same(P, q), Bool.not(Bool.xor(R, r))) : Bool}:
  match n:
    case M.Node{nm, it, +pl, d}:
      %Equal.sym(M.Place, pl, M.Place{P, R}, hp) : {M.Node.hangs(M.Node{nm, it, _, d}, q, r) == Bool.and(M.Name.same(P, q), Bool.not(Bool.xor(R, r))) : Bool}
      {==}

# Readings and fuel
# -----------------

# Past what a reading needs, more fuel reads the same.
def read_up(f: Nat, +t: List<&2, M.Node>, +L: List<&2, M.Node>, +h: {M.fits(f, t, L) == True{} : Bool}) -> {M.read_all(1n+f, t, L) == M.read_all(f, t, L) : List<&2, M.Node>}:
  match f:
    case 0n:
      %Equal.sym(List<&2, M.Node>, L, Nil{}, AL.nil_of_is_nil(L, h)) : {M.read_all(1n, t, _) == Nil{} : List<&2, M.Node>}
      {==}
    case 1n++p:
      match L:
        case Nil{}:
          {==}
        case +s <> +rest:
          AL.append_cong(M.read_all(1n+p, t, M.children(t, Some{M.Node.name(s)}, False{})), M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(1n+p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(1n+p, t, rest)), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)),
            read_up(p, t, M.children(t, Some{M.Node.name(s)}, False{}), Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h)),
            AL.cons_cong(s, List.append(&2, M.Node, M.read_all(1n+p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(1n+p, t, rest)), List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)),
              AL.append_cong(M.read_all(1n+p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(1n+p, t, rest), M.read_all(p, t, rest),
                read_up(p, t, M.children(t, Some{M.Node.name(s)}, True{}), Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h))),
                read_up(p, t, rest, Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h))))))

# Each sibling costs one fuel.
def fits_len(q: Nat, +t: List<&2, M.Node>, L: List<&2, M.Node>, h: {M.fits(q, t, L) == True{} : Bool}) -> {Nat.is_le(List.length(&2, M.Node, L), q) == True{} : Bool}:
  match q L:
    case 0n Nil{}:
      {==}
    case 0n s <> rest:
      Empty.absurd({Nat.is_le(List.length(&2, M.Node, s <> rest), 0n) == True{} : Bool}, Comp.false_true(h))
    case 1n++p Nil{}:
      {==}
    case 1n++p +s <> rest:
      fits_len(p, t, rest, Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h)))

# A reading of two lists is the first read, then the second with what fuel
# the first left.
def read_app(q: Nat, +t: List<&2, M.Node>, +A: List<&2, M.Node>, +B: List<&2, M.Node>) -> {M.read_all(q, t, List.append(&2, M.Node, A, B)) == List.append(&2, M.Node, M.read_all(q, t, A), M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B)) : List<&2, M.Node>}:
  match q:
    case 0n:
      Equal.sym(List<&2, M.Node>, M.read_all(Nat.sub(0n, List.length(&2, M.Node, A)), t, B), Nil{},
        Equal.trans(List<&2, M.Node>, M.read_all(Nat.sub(0n, List.length(&2, M.Node, A)), t, B), M.read_all(0n, t, B), Nil{},
          Equal.cong(Nat, List<&2, M.Node>, l => M.read_all(l, t, B), Nat.sub(0n, List.length(&2, M.Node, A)), 0n, sub0(List.length(&2, M.Node, A))),
          {==}))
    case 1n++p:
      match A:
        case Nil{}:
          {==}
        case +a <> +A2:
          Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, False{})), a <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.read_all(p, t, List.append(&2, M.Node, A2, B)))), List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, False{})), a <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, True{})), List.append(&2, M.Node, M.read_all(p, t, A2), M.read_all(Nat.sub(p, List.length(&2, M.Node, A2)), t, B)))), List.append(&2, M.Node, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, False{})), a <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.read_all(p, t, A2))), M.read_all(Nat.sub(p, List.length(&2, M.Node, A2)), t, B)),
            Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, False{})), a <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, True{})), l)), M.read_all(p, t, List.append(&2, M.Node, A2, B)), List.append(&2, M.Node, M.read_all(p, t, A2), M.read_all(Nat.sub(p, List.length(&2, M.Node, A2)), t, B)), read_app(p, t, A2, B)),
            Equal.sym(List<&2, M.Node>, List.append(&2, M.Node, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, False{})), a <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.read_all(p, t, A2))), M.read_all(Nat.sub(p, List.length(&2, M.Node, A2)), t, B)), List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, False{})), a <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, True{})), List.append(&2, M.Node, M.read_all(p, t, A2), M.read_all(Nat.sub(p, List.length(&2, M.Node, A2)), t, B)))),
              Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, False{})), a <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.read_all(p, t, A2))), M.read_all(Nat.sub(p, List.length(&2, M.Node, A2)), t, B)), List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, False{})), a <> List.append(&2, M.Node, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.read_all(p, t, A2)), M.read_all(Nat.sub(p, List.length(&2, M.Node, A2)), t, B))), List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, False{})), a <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, True{})), List.append(&2, M.Node, M.read_all(p, t, A2), M.read_all(Nat.sub(p, List.length(&2, M.Node, A2)), t, B)))),
                Lin.nappend_assoc(M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, False{})), a <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.read_all(p, t, A2)), M.read_all(Nat.sub(p, List.length(&2, M.Node, A2)), t, B)),
                Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, False{})), a <> l), List.append(&2, M.Node, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.read_all(p, t, A2)), M.read_all(Nat.sub(p, List.length(&2, M.Node, A2)), t, B)), List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, True{})), List.append(&2, M.Node, M.read_all(p, t, A2), M.read_all(Nat.sub(p, List.length(&2, M.Node, A2)), t, B))),
                  Lin.nappend_assoc(M.read_all(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.read_all(p, t, A2), M.read_all(Nat.sub(p, List.length(&2, M.Node, A2)), t, B))))))

def fits_app_l(q: Nat, +t: List<&2, M.Node>, A: List<&2, M.Node>, +B: List<&2, M.Node>, +h: {M.fits(q, t, List.append(&2, M.Node, A, B)) == True{} : Bool}) -> {M.fits(q, t, A) == True{} : Bool}:
  match q A:
    case 0n Nil{}:
      {==}
    case 0n a <> A2:
      Empty.absurd({M.fits(0n, t, a <> A2) == True{} : Bool}, Comp.false_true(h))
    case 1n++p Nil{}:
      {==}
    case 1n++p +a <> A2:
      AL.and_intro(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.fits(p, t, A2)),
        Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.fits(p, t, List.append(&2, M.Node, A2, B))), h),
        AL.and_intro(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.fits(p, t, A2),
          Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.fits(p, t, List.append(&2, M.Node, A2, B)), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.fits(p, t, List.append(&2, M.Node, A2, B))), h)),
          fits_app_l(p, t, A2, B, Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.fits(p, t, List.append(&2, M.Node, A2, B)), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.fits(p, t, List.append(&2, M.Node, A2, B))), h)))))

def fits_app_r(q: Nat, +t: List<&2, M.Node>, A: List<&2, M.Node>, +B: List<&2, M.Node>, h: {M.fits(q, t, List.append(&2, M.Node, A, B)) == True{} : Bool}) -> {M.fits(Nat.sub(q, List.length(&2, M.Node, A)), t, B) == True{} : Bool}:
  match q A:
    case 0n Nil{}:
      h
    case 0n a <> A2:
      Empty.absurd({M.fits(Nat.sub(0n, List.length(&2, M.Node, a <> A2)), t, B) == True{} : Bool}, Comp.false_true(h))
    case 1n++p Nil{}:
      h
    case 1n++p +a <> A2:
      fits_app_r(p, t, A2, B, Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.fits(p, t, List.append(&2, M.Node, A2, B)), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.fits(p, t, List.append(&2, M.Node, A2, B))), h)))

def fits_app(q: Nat, +t: List<&2, M.Node>, A: List<&2, M.Node>, +B: List<&2, M.Node>, +ha: {M.fits(q, t, A) == True{} : Bool}, hb: {M.fits(Nat.sub(q, List.length(&2, M.Node, A)), t, B) == True{} : Bool}) -> {M.fits(q, t, List.append(&2, M.Node, A, B)) == True{} : Bool}:
  match q A:
    case 0n Nil{}:
      hb
    case 0n a <> A2:
      Empty.absurd({M.fits(0n, t, List.append(&2, M.Node, a <> A2, B)) == True{} : Bool}, Comp.false_true(ha))
    case 1n++p Nil{}:
      hb
    case 1n++p +a <> A2:
      AL.and_intro(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.fits(p, t, List.append(&2, M.Node, A2, B))),
        Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.fits(p, t, A2)), ha),
        AL.and_intro(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.fits(p, t, List.append(&2, M.Node, A2, B)),
          Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.fits(p, t, A2), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.fits(p, t, A2)), ha)),
          fits_app(p, t, A2, B, Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.fits(p, t, A2), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(a)}, True{})), M.fits(p, t, A2)), ha)), hb)))

# Where an attach puts the element
# --------------------------------
#
# `attach` walks the list to the first name above the element's; so the
# tree splits there, and every sibling list of the element's place is its
# part before the split, the element, and its part after.
def apre.put(x: M.Node, r: List<&2, M.Node>, first: Bool) -> List<&2, M.Node>:
  match first:
    case True{}:
      Nil{}
    case False{}:
      x <> r

def apre(t: List<&2, M.Node>, +n: M.Node) -> List<&2, M.Node>:
  match t:
    case Nil{}:
      Nil{}
    case +x <> xs:
      apre.put(x, apre(xs, n), Cmp.is_lt(M.Name.cmp(M.Node.name(n), M.Node.name(x))))

def apost.put(x: M.Node, xs: List<&2, M.Node>, r: List<&2, M.Node>, first: Bool) -> List<&2, M.Node>:
  match first:
    case True{}:
      x <> xs
    case False{}:
      r

def apost(t: List<&2, M.Node>, +n: M.Node) -> List<&2, M.Node>:
  match t:
    case Nil{}:
      Nil{}
    case +x <> +xs:
      apost.put(x, xs, apost(xs, n), Cmp.is_lt(M.Name.cmp(M.Node.name(n), M.Node.name(x))))

def fput_app(x: M.Node, a: List<&2, M.Node>, +b: List<&2, M.Node>, h: Bool) -> {List.filter.put(M.Node, x, List.append(&2, M.Node, a, b), h) == List.append(&2, M.Node, List.filter.put(M.Node, x, a, h), b) : List<&2, M.Node>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

def split.at(+x: M.Node, +xs: List<&2, M.Node>, +n: M.Node, +q: Maybe<&2, M.Name>, +r: Bool, lt: Bool, ih: {M.children(xs, q, r) == List.append(&2, M.Node, M.children(apre(xs, n), q, r), M.children(apost(xs, n), q, r)) : List<&2, M.Node>}) -> {M.children(x <> xs, q, r) == List.append(&2, M.Node, M.children(apre.put(x, apre(xs, n), lt), q, r), M.children(apost.put(x, xs, apost(xs, n), lt), q, r)) : List<&2, M.Node>}:
  match lt:
    case True{}:
      {==}
    case False{}:
      Equal.trans(List<&2, M.Node>, List.filter.put(M.Node, x, M.children(xs, q, r), M.Node.hangs(x, q, r)), List.filter.put(M.Node, x, List.append(&2, M.Node, M.children(apre(xs, n), q, r), M.children(apost(xs, n), q, r)), M.Node.hangs(x, q, r)), List.append(&2, M.Node, List.filter.put(M.Node, x, M.children(apre(xs, n), q, r), M.Node.hangs(x, q, r)), M.children(apost(xs, n), q, r)),
        Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => List.filter.put(M.Node, x, l, M.Node.hangs(x, q, r)), M.children(xs, q, r), List.append(&2, M.Node, M.children(apre(xs, n), q, r), M.children(apost(xs, n), q, r)), ih),
        fput_app(x, M.children(apre(xs, n), q, r), M.children(apost(xs, n), q, r), M.Node.hangs(x, q, r)))

def children_split(t: List<&2, M.Node>, +n: M.Node, +q: Maybe<&2, M.Name>, +r: Bool) -> {M.children(t, q, r) == List.append(&2, M.Node, M.children(apre(t, n), q, r), M.children(apost(t, n), q, r)) : List<&2, M.Node>}:
  match t:
    case Nil{}:
      {==}
    case +x <> +xs:
      split.at(x, xs, n, q, r, Cmp.is_lt(M.Name.cmp(M.Node.name(n), M.Node.name(x))), children_split(xs, n, q, r))

def attach_split.at(+x: M.Node, +xs: List<&2, M.Node>, +n: M.Node, +q: Maybe<&2, M.Name>, +r: Bool, lt: Bool, +h: {M.Node.hangs(n, q, r) == True{} : Bool}, ih: {M.children(M.attach(xs, n), q, r) == List.append(&2, M.Node, M.children(apre(xs, n), q, r), n <> M.children(apost(xs, n), q, r)) : List<&2, M.Node>}) -> {M.children(M.attach.put(n, x, xs, M.attach(xs, n), lt), q, r) == List.append(&2, M.Node, M.children(apre.put(x, apre(xs, n), lt), q, r), n <> M.children(apost.put(x, xs, apost(xs, n), lt), q, r)) : List<&2, M.Node>}:
  match lt:
    case True{}:
      Lin.put_true(M.Node, n, M.children(x <> xs, q, r), M.Node.hangs(n, q, r), h)
    case False{}:
      Equal.trans(List<&2, M.Node>, List.filter.put(M.Node, x, M.children(M.attach(xs, n), q, r), M.Node.hangs(x, q, r)), List.filter.put(M.Node, x, List.append(&2, M.Node, M.children(apre(xs, n), q, r), n <> M.children(apost(xs, n), q, r)), M.Node.hangs(x, q, r)), List.append(&2, M.Node, List.filter.put(M.Node, x, M.children(apre(xs, n), q, r), M.Node.hangs(x, q, r)), n <> M.children(apost(xs, n), q, r)),
        Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => List.filter.put(M.Node, x, l, M.Node.hangs(x, q, r)), M.children(M.attach(xs, n), q, r), List.append(&2, M.Node, M.children(apre(xs, n), q, r), n <> M.children(apost(xs, n), q, r)), ih),
        fput_app(x, M.children(apre(xs, n), q, r), n <> M.children(apost(xs, n), q, r), M.Node.hangs(x, q, r)))

# At the element's own place: the part before, the element, the part after.
def children_attach_split(t: List<&2, M.Node>, +n: M.Node, +q: Maybe<&2, M.Name>, +r: Bool, +h: {M.Node.hangs(n, q, r) == True{} : Bool}) -> {M.children(M.attach(t, n), q, r) == List.append(&2, M.Node, M.children(apre(t, n), q, r), n <> M.children(apost(t, n), q, r)) : List<&2, M.Node>}:
  match t:
    case Nil{}:
      Lin.put_true(M.Node, n, Nil{}, M.Node.hangs(n, q, r), h)
    case +x <> +xs:
      attach_split.at(x, xs, n, q, r, Cmp.is_lt(M.Name.cmp(M.Node.name(n), M.Node.name(x))), h, children_attach_split(xs, n, q, r, h))

# Nothing hangs under a fresh element that is not its own parent.
def children_n(+t: List<&2, M.Node>, +n: M.Node, +P: Maybe<&2, M.Name>, +R: Bool, +r: Bool, hp: {M.Node.place(n) == M.Place{P, R} : M.Place}, fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, np: {M.Name.same(P, Some{M.Node.name(n)}) == False{} : Bool}) -> {M.children(M.attach(t, n), Some{M.Node.name(n)}, r) == Nil{} : List<&2, M.Node>}:
  Equal.trans(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(n)}, r), M.children(t, Some{M.Node.name(n)}, r), Nil{},
    AL.children_attach_other(t, n, Some{M.Node.name(n)}, r,
      Equal.trans(Bool, M.Node.hangs(n, Some{M.Node.name(n)}, r), Bool.and(M.Name.same(P, Some{M.Node.name(n)}), Bool.not(Bool.xor(R, r))), False{},
        hangs_of(n, P, R, Some{M.Node.name(n)}, r, hp),
        (%Equal.sym(Bool, M.Name.same(P, Some{M.Node.name(n)}), False{}, np) : {Bool.and(_, Bool.not(Bool.xor(R, r))) == False{} : Bool}
          {==}))),
    AL.children_none(t, M.Node.name(n), r, AL.not_of_true(M.hangs_under(t, M.Node.name(n)), Comp.and_right(Bool.not(M.named(t, M.Node.name(n))), Bool.not(M.hangs_under(t, M.Node.name(n))), fr))))

# Away from the element's place, sibling lists are as they were.
def chs_off(+t: List<&2, M.Node>, +n: M.Node, +P: Maybe<&2, M.Name>, +R: Bool, +q: Maybe<&2, M.Name>, +r: Bool, hp: {M.Node.place(n) == M.Place{P, R} : M.Place}, ns: {M.Name.same(P, q) == False{} : Bool}) -> {M.children(M.attach(t, n), q, r) == M.children(t, q, r) : List<&2, M.Node>}:
  AL.children_attach_other(t, n, q, r,
    Equal.trans(Bool, M.Node.hangs(n, q, r), Bool.and(M.Name.same(P, q), Bool.not(Bool.xor(R, r))), False{},
      hangs_of(n, P, R, q, r, hp),
      (%Equal.sym(Bool, M.Name.same(P, q), False{}, ns) : {Bool.and(_, Bool.not(Bool.xor(R, r))) == False{} : Bool}
        {==})))

def chs_side(+t: List<&2, M.Node>, +n: M.Node, +P: Maybe<&2, M.Name>, +R: Bool, +q: Maybe<&2, M.Name>, +r: Bool, hp: {M.Node.place(n) == M.Place{P, R} : M.Place}, x: {Bool.not(Bool.xor(R, r)) == False{} : Bool}) -> {M.children(M.attach(t, n), q, r) == M.children(t, q, r) : List<&2, M.Node>}:
  AL.children_attach_other(t, n, q, r,
    Equal.trans(Bool, M.Node.hangs(n, q, r), Bool.and(M.Name.same(P, q), Bool.not(Bool.xor(R, r))), False{},
      hangs_of(n, P, R, q, r, hp),
      (%Equal.sym(Bool, Bool.not(Bool.xor(R, r)), False{}, x) : {Bool.and(M.Name.same(P, q), _) == False{} : Bool}
        AL.and_false_r(M.Name.same(P, q)))))

# Whether a reading reaches the element's parent
# ----------------------------------------------

def rch(xs: List<&2, M.Node>, P: Maybe<&2, M.Name>) -> Bool:
  match P:
    case None{}:
      False{}
    case Some{p}:
      M.named(xs, p)

def rch_app(xs: List<&2, M.Node>, +ys: List<&2, M.Node>, P: Maybe<&2, M.Name>) -> {rch(List.append(&2, M.Node, xs, ys), P) == Bool.or(rch(xs, P), rch(ys, P)) : Bool}:
  match P:
    case None{}:
      {==}
    case Some{+p}:
      AL.named_append(xs, ys, p)

def rch_l(+xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +P: Maybe<&2, M.Name>, h: {rch(List.append(&2, M.Node, xs, ys), P) == False{} : Bool}) -> {rch(xs, P) == False{} : Bool}:
  AL.or_false_l(rch(xs, P), rch(ys, P), Equal.trans(Bool, Bool.or(rch(xs, P), rch(ys, P)), rch(List.append(&2, M.Node, xs, ys), P), False{}, Equal.sym(Bool, rch(List.append(&2, M.Node, xs, ys), P), Bool.or(rch(xs, P), rch(ys, P)), rch_app(xs, ys, P)), h))

def rch_r(+xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +P: Maybe<&2, M.Name>, h: {rch(List.append(&2, M.Node, xs, ys), P) == False{} : Bool}) -> {rch(ys, P) == False{} : Bool}:
  AL.or_false_r(rch(xs, P), rch(ys, P), Equal.trans(Bool, Bool.or(rch(xs, P), rch(ys, P)), rch(List.append(&2, M.Node, xs, ys), P), False{}, Equal.sym(Bool, rch(List.append(&2, M.Node, xs, ys), P), Bool.or(rch(xs, P), rch(ys, P)), rch_app(xs, ys, P)), h))

def same_off(P: Maybe<&2, M.Name>, +s: M.Node, +rest: List<&2, M.Node>, h: {rch(s <> rest, P) == False{} : Bool}) -> {M.Name.same(P, Some{M.Node.name(s)}) == False{} : Bool}:
  match P:
    case None{}:
      {==}
    case Some{+p}:
      AL.name_ne_sym(M.Node.name(s), p, AL.or_false_l(M.Name.eq(M.Node.name(s), p), M.named(rest, p), h))

def rch_tail(P: Maybe<&2, M.Name>, +s: M.Node, +rest: List<&2, M.Node>, h: {rch(s <> rest, P) == False{} : Bool}) -> {rch(rest, P) == False{} : Bool}:
  match P:
    case None{}:
      {==}
    case Some{+p}:
      AL.or_false_r(M.Name.eq(M.Node.name(s), p), M.named(rest, p), h)

def rch_up(+p: Nat, +t: List<&2, M.Node>, +X: List<&2, M.Node>, +P: Maybe<&2, M.Name>, +f: {M.fits(p, t, X) == True{} : Bool}, h: {rch(M.read_all(p, t, X), P) == False{} : Bool}) -> {rch(M.read_all(1n+p, t, X), P) == False{} : Bool}:
  Equal.trans(Bool, rch(M.read_all(1n+p, t, X), P), rch(M.read_all(p, t, X), P), False{}, Equal.cong(List<&2, M.Node>, Bool, l => rch(l, P), M.read_all(1n+p, t, X), M.read_all(p, t, X), read_up(p, t, X, f)), h)

# A reading that does not reach the parent
# ----------------------------------------
#
# Every sibling list it reads is as it was, so it reads the same.
def read_same(q: Nat, +t: List<&2, M.Node>, X: List<&2, M.Node>, +n: M.Node, +P: Maybe<&2, M.Name>, +R: Bool, +hp: {M.Node.place(n) == M.Place{P, R} : M.Place}, +h: {M.fits(q, t, X) == True{} : Bool}, +nr: {rch(M.read_all(q, t, X), P) == False{} : Bool}) -> {M.read_all(q, M.attach(t, n), X) == M.read_all(q, t, X) : List<&2, M.Node>}:
  match q:
    case 0n:
      {==}
    case 1n++p:
      match X:
        case Nil{}:
          {==}
        case +s <> +rest:
          AL.append_cong(M.read_all(p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{})), M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.read_all(p, M.attach(t, n), rest)), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)),
            Equal.trans(List<&2, M.Node>, M.read_all(p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{})), M.read_all(p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})),
              Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => M.read_all(p, M.attach(t, n), l), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{}), M.children(t, Some{M.Node.name(s)}, False{}), chs_off(t, n, P, R, Some{M.Node.name(s)}, False{}, hp, same_off(P, s, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), rch_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), P, nr)))),
              read_same(p, t, M.children(t, Some{M.Node.name(s)}, False{}), n, P, R, hp, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h), rch_l(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), P, nr))),
            AL.cons_cong(s, List.append(&2, M.Node, M.read_all(p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.read_all(p, M.attach(t, n), rest)), List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)),
              AL.append_cong(M.read_all(p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, M.attach(t, n), rest), M.read_all(p, t, rest),
                Equal.trans(List<&2, M.Node>, M.read_all(p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.read_all(p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})),
                  Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => M.read_all(p, M.attach(t, n), l), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{}), M.children(t, Some{M.Node.name(s)}, True{}), chs_off(t, n, P, R, Some{M.Node.name(s)}, True{}, hp, same_off(P, s, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), rch_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), P, nr)))),
                  read_same(p, t, M.children(t, Some{M.Node.name(s)}, True{}), n, P, R, hp, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h)), rch_l(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), P, rch_tail(P, s, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), rch_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), P, nr))))),
                read_same(p, t, rest, n, P, R, hp, Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h)), rch_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), P, rch_tail(P, s, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), rch_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), P, nr)))))))

def fits_same(q: Nat, +t: List<&2, M.Node>, X: List<&2, M.Node>, +n: M.Node, +P: Maybe<&2, M.Name>, +R: Bool, +hp: {M.Node.place(n) == M.Place{P, R} : M.Place}, +h: {M.fits(q, t, X) == True{} : Bool}, +nr: {rch(M.read_all(q, t, X), P) == False{} : Bool}) -> {M.fits(q, M.attach(t, n), X) == True{} : Bool}:
  match q:
    case 0n:
      h
    case 1n++p:
      match X:
        case Nil{}:
          {==}
        case +s <> +rest:
          %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, False{}), M.children(t, Some{M.Node.name(s)}, False{}), chs_off(t, n, P, R, Some{M.Node.name(s)}, False{}, hp, same_off(P, s, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), rch_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), P, nr)))) : {Bool.and(M.fits(p, M.attach(t, n), _), Bool.and(M.fits(p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.fits(p, M.attach(t, n), rest))) == True{} : Bool}
          %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, True{}), M.children(t, Some{M.Node.name(s)}, True{}), chs_off(t, n, P, R, Some{M.Node.name(s)}, True{}, hp, same_off(P, s, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), rch_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), P, nr)))) : {Bool.and(M.fits(p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, M.attach(t, n), _), M.fits(p, M.attach(t, n), rest))) == True{} : Bool}
          AL.and_intro(M.fits(p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, M.attach(t, n), rest)),
            fits_same(p, t, M.children(t, Some{M.Node.name(s)}, False{}), n, P, R, hp, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h), rch_l(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), P, nr)),
            AL.and_intro(M.fits(p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, M.attach(t, n), rest),
              fits_same(p, t, M.children(t, Some{M.Node.name(s)}, True{}), n, P, R, hp, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h)), rch_l(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), P, rch_tail(P, s, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), rch_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), P, nr)))),
              fits_same(p, t, rest, n, P, R, hp, Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), h)), rch_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), P, rch_tail(P, s, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), rch_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), P, nr))))))

# One fuel up, as the parent's list will be read.
def same_up(+p: Nat, +t: List<&2, M.Node>, +X: List<&2, M.Node>, +n: M.Node, +P: Maybe<&2, M.Name>, +R: Bool, +hp: {M.Node.place(n) == M.Place{P, R} : M.Place}, +f: {M.fits(p, t, X) == True{} : Bool}, +nr: {rch(M.read_all(p, t, X), P) == False{} : Bool}) -> {M.read_all(1n+p, M.attach(t, n), X) == M.read_all(p, t, X) : List<&2, M.Node>}:
  Equal.trans(List<&2, M.Node>, M.read_all(1n+p, M.attach(t, n), X), M.read_all(1n+p, t, X), M.read_all(p, t, X),
    read_same(1n+p, t, X, n, P, R, hp, AL.fits_mono(p, t, X, f), rch_up(p, t, X, P, f, nr)),
    read_up(p, t, X, f))

def fits_up(+p: Nat, +t: List<&2, M.Node>, +X: List<&2, M.Node>, +n: M.Node, +P: Maybe<&2, M.Name>, +R: Bool, +hp: {M.Node.place(n) == M.Place{P, R} : M.Place}, +f: {M.fits(p, t, X) == True{} : Bool}, +nr: {rch(M.read_all(p, t, X), P) == False{} : Bool}) -> {M.fits(1n+p, M.attach(t, n), X) == True{} : Bool}:
  fits_same(1n+p, t, X, n, P, R, hp, AL.fits_mono(p, t, X, f), rch_up(p, t, X, P, f, nr))

# The parent's own list
# ---------------------
#
# The element, fresh and childless, reads as itself between the siblings
# before it and those after.
def read_leaf(s: Nat, +t: List<&2, M.Node>, +n: M.Node, +P: Maybe<&2, M.Name>, +R: Bool, +B: List<&2, M.Node>, +hp: {M.Node.place(n) == M.Place{P, R} : M.Place}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +np: {M.Name.same(P, Some{M.Node.name(n)}) == False{} : Bool}) -> {M.read_all(1n+s, M.attach(t, n), n <> B) == n <> M.read_all(s, M.attach(t, n), B) : List<&2, M.Node>}:
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(n)}, False{}), Nil{}, children_n(t, n, P, R, False{}, hp, fr, np)) : {List.append(&2, M.Node, M.read_all(s, M.attach(t, n), _), n <> List.append(&2, M.Node, M.read_all(s, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(n)}, True{})), M.read_all(s, M.attach(t, n), B))) == n <> M.read_all(s, M.attach(t, n), B) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(n)}, True{}), Nil{}, children_n(t, n, P, R, True{}, hp, fr, np)) : {List.append(&2, M.Node, M.read_all(s, M.attach(t, n), Nil{}), n <> List.append(&2, M.Node, M.read_all(s, M.attach(t, n), _), M.read_all(s, M.attach(t, n), B))) == n <> M.read_all(s, M.attach(t, n), B) : List<&2, M.Node>}
  %Equal.sym(List<&2, M.Node>, M.read_all(s, M.attach(t, n), Nil{}), Nil{}, AL.read_nil(s, M.attach(t, n))) : {List.append(&2, M.Node, _, n <> List.append(&2, M.Node, _, M.read_all(s, M.attach(t, n), B))) == n <> M.read_all(s, M.attach(t, n), B) : List<&2, M.Node>}
  {==}

def fits_leaf(+s: Nat, +t: List<&2, M.Node>, +n: M.Node, +P: Maybe<&2, M.Name>, +R: Bool, +B: List<&2, M.Node>, +hp: {M.Node.place(n) == M.Place{P, R} : M.Place}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +np: {M.Name.same(P, Some{M.Node.name(n)}) == False{} : Bool}, hb: {M.fits(s, M.attach(t, n), B) == True{} : Bool}) -> {M.fits(1n+s, M.attach(t, n), n <> B) == True{} : Bool}:
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(n)}, False{}), Nil{}, children_n(t, n, P, R, False{}, hp, fr, np)) : {Bool.and(M.fits(s, M.attach(t, n), _), Bool.and(M.fits(s, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(n)}, True{})), M.fits(s, M.attach(t, n), B))) == True{} : Bool}
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(n)}, True{}), Nil{}, children_n(t, n, P, R, True{}, hp, fr, np)) : {Bool.and(M.fits(s, M.attach(t, n), Nil{}), Bool.and(M.fits(s, M.attach(t, n), _), M.fits(s, M.attach(t, n), B))) == True{} : Bool}
  AL.and_intro(M.fits(s, M.attach(t, n), Nil{}), Bool.and(M.fits(s, M.attach(t, n), Nil{}), M.fits(s, M.attach(t, n), B)), AL.fits_nil(s, M.attach(t, n)),
    AL.and_intro(M.fits(s, M.attach(t, n), Nil{}), M.fits(s, M.attach(t, n), B), AL.fits_nil(s, M.attach(t, n)), hb))

def li_read(+q: Nat, +t: List<&2, M.Node>, +n: M.Node, +P: Maybe<&2, M.Name>, +R: Bool, +hp: {M.Node.place(n) == M.Place{P, R} : M.Place}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +np: {M.Name.same(P, Some{M.Node.name(n)}) == False{} : Bool}, +A: List<&2, M.Node>, +B: List<&2, M.Node>, +h: {M.fits(q, t, List.append(&2, M.Node, A, B)) == True{} : Bool}, +nr: {rch(M.read_all(q, t, List.append(&2, M.Node, A, B)), P) == False{} : Bool}) -> {M.read_all(1n+q, M.attach(t, n), List.append(&2, M.Node, A, n <> B)) == List.append(&2, M.Node, M.read_all(q, t, A), n <> M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B)) : List<&2, M.Node>}:
  Equal.trans(List<&2, M.Node>, M.read_all(1n+q, M.attach(t, n), List.append(&2, M.Node, A, n <> B)), List.append(&2, M.Node, M.read_all(1n+q, M.attach(t, n), A), M.read_all(Nat.sub(1n+q, List.length(&2, M.Node, A)), M.attach(t, n), n <> B)), List.append(&2, M.Node, M.read_all(q, t, A), n <> M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B)),
    read_app(1n+q, M.attach(t, n), A, n <> B),
    AL.append_cong(M.read_all(1n+q, M.attach(t, n), A), M.read_all(q, t, A), M.read_all(Nat.sub(1n+q, List.length(&2, M.Node, A)), M.attach(t, n), n <> B), n <> M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B),
      same_up(q, t, A, n, P, R, hp, fits_app_l(q, t, A, B, h), rch_l(M.read_all(q, t, A), M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B), P, Equal.trans(Bool, rch(List.append(&2, M.Node, M.read_all(q, t, A), M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B)), P), rch(M.read_all(q, t, List.append(&2, M.Node, A, B)), P), False{}, Equal.cong(List<&2, M.Node>, Bool, l => rch(l, P), List.append(&2, M.Node, M.read_all(q, t, A), M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B)), M.read_all(q, t, List.append(&2, M.Node, A, B)), Equal.sym(List<&2, M.Node>, M.read_all(q, t, List.append(&2, M.Node, A, B)), List.append(&2, M.Node, M.read_all(q, t, A), M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B)), read_app(q, t, A, B))), nr))),
      Equal.trans(List<&2, M.Node>, M.read_all(Nat.sub(1n+q, List.length(&2, M.Node, A)), M.attach(t, n), n <> B), M.read_all(1n+Nat.sub(q, List.length(&2, M.Node, A)), M.attach(t, n), n <> B), n <> M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B),
        Equal.cong(Nat, List<&2, M.Node>, l => M.read_all(l, M.attach(t, n), n <> B), Nat.sub(1n+q, List.length(&2, M.Node, A)), 1n+Nat.sub(q, List.length(&2, M.Node, A)), sub_succ(q, List.length(&2, M.Node, A), fits_len(q, t, A, fits_app_l(q, t, A, B, h)))),
        Equal.trans(List<&2, M.Node>, M.read_all(1n+Nat.sub(q, List.length(&2, M.Node, A)), M.attach(t, n), n <> B), n <> M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), M.attach(t, n), B), n <> M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B),
          read_leaf(Nat.sub(q, List.length(&2, M.Node, A)), t, n, P, R, B, hp, fr, np),
          AL.cons_cong(n, M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), M.attach(t, n), B), M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B),
            read_same(Nat.sub(q, List.length(&2, M.Node, A)), t, B, n, P, R, hp, fits_app_r(q, t, A, B, h), rch_r(M.read_all(q, t, A), M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B), P, Equal.trans(Bool, rch(List.append(&2, M.Node, M.read_all(q, t, A), M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B)), P), rch(M.read_all(q, t, List.append(&2, M.Node, A, B)), P), False{}, Equal.cong(List<&2, M.Node>, Bool, l => rch(l, P), List.append(&2, M.Node, M.read_all(q, t, A), M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B)), M.read_all(q, t, List.append(&2, M.Node, A, B)), Equal.sym(List<&2, M.Node>, M.read_all(q, t, List.append(&2, M.Node, A, B)), List.append(&2, M.Node, M.read_all(q, t, A), M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B)), read_app(q, t, A, B))), nr))))))))

def li_fits(+q: Nat, +t: List<&2, M.Node>, +n: M.Node, +P: Maybe<&2, M.Name>, +R: Bool, +hp: {M.Node.place(n) == M.Place{P, R} : M.Place}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +np: {M.Name.same(P, Some{M.Node.name(n)}) == False{} : Bool}, +A: List<&2, M.Node>, +B: List<&2, M.Node>, +h: {M.fits(q, t, List.append(&2, M.Node, A, B)) == True{} : Bool}, +nr: {rch(M.read_all(q, t, List.append(&2, M.Node, A, B)), P) == False{} : Bool}) -> {M.fits(1n+q, M.attach(t, n), List.append(&2, M.Node, A, n <> B)) == True{} : Bool}:
  fits_app(1n+q, M.attach(t, n), A, n <> B,
    fits_up(q, t, A, n, P, R, hp, fits_app_l(q, t, A, B, h), rch_l(M.read_all(q, t, A), M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B), P, Equal.trans(Bool, rch(List.append(&2, M.Node, M.read_all(q, t, A), M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B)), P), rch(M.read_all(q, t, List.append(&2, M.Node, A, B)), P), False{}, Equal.cong(List<&2, M.Node>, Bool, l => rch(l, P), List.append(&2, M.Node, M.read_all(q, t, A), M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B)), M.read_all(q, t, List.append(&2, M.Node, A, B)), Equal.sym(List<&2, M.Node>, M.read_all(q, t, List.append(&2, M.Node, A, B)), List.append(&2, M.Node, M.read_all(q, t, A), M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B)), read_app(q, t, A, B))), nr))),
    (%Equal.sym(Nat, Nat.sub(1n+q, List.length(&2, M.Node, A)), 1n+Nat.sub(q, List.length(&2, M.Node, A)), sub_succ(q, List.length(&2, M.Node, A), fits_len(q, t, A, fits_app_l(q, t, A, B, h)))) : {M.fits(_, M.attach(t, n), n <> B) == True{} : Bool}
      fits_leaf(Nat.sub(q, List.length(&2, M.Node, A)), t, n, P, R, B, hp, fr, np,
        fits_same(Nat.sub(q, List.length(&2, M.Node, A)), t, B, n, P, R, hp, fits_app_r(q, t, A, B, h), rch_r(M.read_all(q, t, A), M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B), P, Equal.trans(Bool, rch(List.append(&2, M.Node, M.read_all(q, t, A), M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B)), P), rch(M.read_all(q, t, List.append(&2, M.Node, A, B)), P), False{}, Equal.cong(List<&2, M.Node>, Bool, l => rch(l, P), List.append(&2, M.Node, M.read_all(q, t, A), M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B)), M.read_all(q, t, List.append(&2, M.Node, A, B)), Equal.sym(List<&2, M.Node>, M.read_all(q, t, List.append(&2, M.Node, A, B)), List.append(&2, M.Node, M.read_all(q, t, A), M.read_all(Nat.sub(q, List.length(&2, M.Node, A)), t, B)), read_app(q, t, A, B))), nr))))))

# Reading no element twice
# ------------------------

def nap_l(+xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +x: M.Name, h: {M.named(List.append(&2, M.Node, xs, ys), x) == False{} : Bool}) -> {M.named(xs, x) == False{} : Bool}:
  AL.or_false_l(M.named(xs, x), M.named(ys, x), Equal.trans(Bool, Bool.or(M.named(xs, x), M.named(ys, x)), M.named(List.append(&2, M.Node, xs, ys), x), False{}, AL.named_split(xs, ys, x), h))

def nap_r(+xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +x: M.Name, h: {M.named(List.append(&2, M.Node, xs, ys), x) == False{} : Bool}) -> {M.named(ys, x) == False{} : Bool}:
  AL.or_false_r(M.named(xs, x), M.named(ys, x), Equal.trans(Bool, Bool.or(M.named(xs, x), M.named(ys, x)), M.named(List.append(&2, M.Node, xs, ys), x), False{}, AL.named_split(xs, ys, x), h))

def nap_t(+xs: List<&2, M.Node>, +ys: List<&2, M.Node>, +x: M.Name, h: {M.named(List.append(&2, M.Node, xs, ys), x) == True{} : Bool}) -> {Bool.or(M.named(xs, x), M.named(ys, x)) == True{} : Bool}:
  Equal.trans(Bool, Bool.or(M.named(xs, x), M.named(ys, x)), M.named(List.append(&2, M.Node, xs, ys), x), True{}, AL.named_split(xs, ys, x), h)

def nd_l(a: List<&2, M.Node>, +b: List<&2, M.Node>, +h: {M.nodup(List.append(&2, M.Node, a, b)) == True{} : Bool}) -> {M.nodup(a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case +x <> +xs:
      AL.and_intro(Bool.not(M.named(xs, M.Node.name(x))), M.nodup(xs),
        AL.not_true(M.named(xs, M.Node.name(x)), nap_l(xs, b, M.Node.name(x), AL.not_of_true(M.named(List.append(&2, M.Node, xs, b), M.Node.name(x)), Comp.and_left(Bool.not(M.named(List.append(&2, M.Node, xs, b), M.Node.name(x))), M.nodup(List.append(&2, M.Node, xs, b)), h)))),
        nd_l(xs, b, Comp.and_right(Bool.not(M.named(List.append(&2, M.Node, xs, b), M.Node.name(x))), M.nodup(List.append(&2, M.Node, xs, b)), h)))

def nd_r(a: List<&2, M.Node>, +b: List<&2, M.Node>, h: {M.nodup(List.append(&2, M.Node, a, b)) == True{} : Bool}) -> {M.nodup(b) == True{} : Bool}:
  match a:
    case Nil{}:
      h
    case +x <> +xs:
      nd_r(xs, b, Comp.and_right(Bool.not(M.named(List.append(&2, M.Node, xs, b), M.Node.name(x))), M.nodup(List.append(&2, M.Node, xs, b)), h))

def nd_sep_l(a: List<&2, M.Node>, +b: List<&2, M.Node>, +x: M.Name, +h: {M.nodup(List.append(&2, M.Node, a, b)) == True{} : Bool}, hx: {M.named(a, x) == True{} : Bool}) -> {M.named(b, x) == False{} : Bool}:
  match a:
    case Nil{}:
      Empty.absurd({M.named(b, x) == False{} : Bool}, Comp.false_true(hx))
    case +y <> +ys:
      AL.or_cases({M.named(b, x) == False{} : Bool}, M.Name.eq(M.Node.name(y), x), M.named(ys, x), hx,
        e => AL.named_transport(b, M.Node.name(y), x, AL.name_eq_equal(M.Node.name(y), x, e), nap_r(ys, b, M.Node.name(y), AL.not_of_true(M.named(List.append(&2, M.Node, ys, b), M.Node.name(y)), Comp.and_left(Bool.not(M.named(List.append(&2, M.Node, ys, b), M.Node.name(y))), M.nodup(List.append(&2, M.Node, ys, b)), h)))),
        e => nd_sep_l(ys, b, x, Comp.and_right(Bool.not(M.named(List.append(&2, M.Node, ys, b), M.Node.name(y))), M.nodup(List.append(&2, M.Node, ys, b)), h), e))

def nd_sep_r(a: List<&2, M.Node>, +b: List<&2, M.Node>, +x: M.Name, +h: {M.nodup(List.append(&2, M.Node, a, b)) == True{} : Bool}, +hx: {M.named(b, x) == True{} : Bool}) -> {M.named(a, x) == False{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case +y <> +ys:
      AL.or_false(M.Name.eq(M.Node.name(y), x), M.named(ys, x),
        AL.name_ne_sym(x, M.Node.name(y), AL.named_ne(b, x, M.Node.name(y), hx, nap_r(ys, b, M.Node.name(y), AL.not_of_true(M.named(List.append(&2, M.Node, ys, b), M.Node.name(y)), Comp.and_left(Bool.not(M.named(List.append(&2, M.Node, ys, b), M.Node.name(y))), M.nodup(List.append(&2, M.Node, ys, b)), h))))),
        nd_sep_r(ys, b, x, Comp.and_right(Bool.not(M.named(List.append(&2, M.Node, ys, b), M.Node.name(y))), M.nodup(List.append(&2, M.Node, ys, b)), h), hx))

def named_ins_false(U: List<&2, M.Node>, +n: M.Node, +V: List<&2, M.Node>, +x: M.Name, +h: {M.named(List.append(&2, M.Node, U, V), x) == False{} : Bool}, +hn: {M.Name.eq(M.Node.name(n), x) == False{} : Bool}) -> {M.named(List.append(&2, M.Node, U, n <> V), x) == False{} : Bool}:
  match U:
    case Nil{}:
      AL.or_false(M.Name.eq(M.Node.name(n), x), M.named(V, x), hn, h)
    case +u <> +U2:
      AL.or_false(M.Name.eq(M.Node.name(u), x), M.named(List.append(&2, M.Node, U2, n <> V), x),
        AL.or_false_l(M.Name.eq(M.Node.name(u), x), M.named(List.append(&2, M.Node, U2, V), x), h),
        named_ins_false(U2, n, V, x, AL.or_false_r(M.Name.eq(M.Node.name(u), x), M.named(List.append(&2, M.Node, U2, V), x), h), hn))

# A fresh element spliced into a reading that reads nothing twice.
def nodup_insert(U: List<&2, M.Node>, +n: M.Node, +V: List<&2, M.Node>, +nd: {M.nodup(List.append(&2, M.Node, U, V)) == True{} : Bool}, +fr: {M.named(List.append(&2, M.Node, U, V), M.Node.name(n)) == False{} : Bool}) -> {M.nodup(List.append(&2, M.Node, U, n <> V)) == True{} : Bool}:
  match U:
    case Nil{}:
      AL.and_intro(Bool.not(M.named(V, M.Node.name(n))), M.nodup(V), AL.not_true(M.named(V, M.Node.name(n)), fr), nd)
    case +u <> +U2:
      AL.and_intro(Bool.not(M.named(List.append(&2, M.Node, U2, n <> V), M.Node.name(u))), M.nodup(List.append(&2, M.Node, U2, n <> V)),
        AL.not_true(M.named(List.append(&2, M.Node, U2, n <> V), M.Node.name(u)), named_ins_false(U2, n, V, M.Node.name(u), AL.not_of_true(M.named(List.append(&2, M.Node, U2, V), M.Node.name(u)), Comp.and_left(Bool.not(M.named(List.append(&2, M.Node, U2, V), M.Node.name(u))), M.nodup(List.append(&2, M.Node, U2, V)), nd)), AL.name_ne_sym(M.Node.name(u), M.Node.name(n), AL.or_false_l(M.Name.eq(M.Node.name(u), M.Node.name(n)), M.named(List.append(&2, M.Node, U2, V), M.Node.name(n)), fr)))),
        nodup_insert(U2, n, V, Comp.and_right(Bool.not(M.named(List.append(&2, M.Node, U2, V), M.Node.name(u))), M.nodup(List.append(&2, M.Node, U2, V)), nd), AL.or_false_r(M.Name.eq(M.Node.name(u), M.Node.name(n)), M.named(List.append(&2, M.Node, U2, V), M.Node.name(n)), fr)))

# Rearranging readings
# --------------------

def rd3(-s: M.Node, -L1: List<&2, M.Node>, -L2: List<&2, M.Node>, -R1: List<&2, M.Node>, -R2: List<&2, M.Node>, -C1: List<&2, M.Node>, -C2: List<&2, M.Node>, eL: {L1 == L2 : List<&2, M.Node>}, eR: {R1 == R2 : List<&2, M.Node>}, eC: {C1 == C2 : List<&2, M.Node>}) -> {List.append(&2, M.Node, L1, s <> List.append(&2, M.Node, R1, C1)) == List.append(&2, M.Node, L2, s <> List.append(&2, M.Node, R2, C2)) : List<&2, M.Node>}:
  AL.append_cong(L1, L2, s <> List.append(&2, M.Node, R1, C1), s <> List.append(&2, M.Node, R2, C2), eL, AL.cons_cong(s, List.append(&2, M.Node, R1, C1), List.append(&2, M.Node, R2, C2), AL.append_cong(R1, R2, C1, C2, eR, eC)))

def asc1(+Ls: List<&2, M.Node>, -s: M.Node, +U: List<&2, M.Node>, -V: List<&2, M.Node>, -Cs: List<&2, M.Node>) -> {List.append(&2, M.Node, Ls, s <> List.append(&2, M.Node, List.append(&2, M.Node, U, V), Cs)) == List.append(&2, M.Node, List.append(&2, M.Node, Ls, s <> U), List.append(&2, M.Node, V, Cs)) : List<&2, M.Node>}:
  Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, Ls, s <> List.append(&2, M.Node, List.append(&2, M.Node, U, V), Cs)), List.append(&2, M.Node, Ls, s <> List.append(&2, M.Node, U, List.append(&2, M.Node, V, Cs))), List.append(&2, M.Node, List.append(&2, M.Node, Ls, s <> U), List.append(&2, M.Node, V, Cs)),
    AL.append_cong(Ls, Ls, s <> List.append(&2, M.Node, List.append(&2, M.Node, U, V), Cs), s <> List.append(&2, M.Node, U, List.append(&2, M.Node, V, Cs)), {==}, AL.cons_cong(s, List.append(&2, M.Node, List.append(&2, M.Node, U, V), Cs), List.append(&2, M.Node, U, List.append(&2, M.Node, V, Cs)), Lin.nappend_assoc(U, V, Cs))),
    Equal.sym(List<&2, M.Node>, List.append(&2, M.Node, List.append(&2, M.Node, Ls, s <> U), List.append(&2, M.Node, V, Cs)), List.append(&2, M.Node, Ls, s <> List.append(&2, M.Node, U, List.append(&2, M.Node, V, Cs))), Lin.nappend_assoc(Ls, s <> U, List.append(&2, M.Node, V, Cs))))

def asc2(+Ls: List<&2, M.Node>, -s: M.Node, +Rs: List<&2, M.Node>, -U: List<&2, M.Node>, -V: List<&2, M.Node>) -> {List.append(&2, M.Node, Ls, s <> List.append(&2, M.Node, Rs, List.append(&2, M.Node, U, V))) == List.append(&2, M.Node, List.append(&2, M.Node, Ls, s <> List.append(&2, M.Node, Rs, U)), V) : List<&2, M.Node>}:
  Equal.sym(List<&2, M.Node>, List.append(&2, M.Node, List.append(&2, M.Node, Ls, s <> List.append(&2, M.Node, Rs, U)), V), List.append(&2, M.Node, Ls, s <> List.append(&2, M.Node, Rs, List.append(&2, M.Node, U, V))),
    Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, List.append(&2, M.Node, Ls, s <> List.append(&2, M.Node, Rs, U)), V), List.append(&2, M.Node, Ls, s <> List.append(&2, M.Node, List.append(&2, M.Node, Rs, U), V)), List.append(&2, M.Node, Ls, s <> List.append(&2, M.Node, Rs, List.append(&2, M.Node, U, V))),
      Lin.nappend_assoc(Ls, s <> List.append(&2, M.Node, Rs, U), V),
      AL.append_cong(Ls, Ls, s <> List.append(&2, M.Node, List.append(&2, M.Node, Rs, U), V), s <> List.append(&2, M.Node, Rs, List.append(&2, M.Node, U, V)), {==}, AL.cons_cong(s, List.append(&2, M.Node, List.append(&2, M.Node, Rs, U), V), List.append(&2, M.Node, Rs, List.append(&2, M.Node, U, V)), Lin.nappend_assoc(Rs, U, V)))))


# The element's parent read somewhere below: in the right subtree of `s`,
# or after it.
def hit.miss2(-K: Type, +p: Nat, +t: List<&2, M.Node>, +s: M.Node, +rest: List<&2, M.Node>, +n: M.Node, +par: M.Name, c2: Bool, +ec2: {M.named(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par) == c2 : Bool}, +R: Bool, +hp: {M.Node.place(n) == M.Place{Some{par}, R} : M.Place}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +np: {M.Name.same(Some{par}, Some{M.Node.name(n)}) == False{} : Bool}, +hf: {M.fits(1n+p, t, s <> rest) == True{} : Bool}, +hd: {M.nodup(M.read_all(1n+p, t, s <> rest)) == True{} : Bool}, +hr: {M.named(M.read_all(1n+p, t, s <> rest), par) == True{} : Bool}, +e0: {M.Name.eq(M.Node.name(s), par) == False{} : Bool}, +ec1: {M.named(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par) == False{} : Bool}, +hMM: {M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par) == True{} : Bool}, ihR: {M.named(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par) == True{} : Bool} -> (@U: List<&2, M.Node> -> @V: List<&2, M.Node> -> {M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})) == List.append(&2, M.Node, U, V) : List<&2, M.Node>} -> {M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})) == List.append(&2, M.Node, U, n <> V) : List<&2, M.Node>} -> {M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})) == True{} : Bool} -> K) -> K, ihC: {M.named(M.read_all(p, t, rest), par) == True{} : Bool} -> (@U: List<&2, M.Node> -> @V: List<&2, M.Node> -> {M.read_all(p, t, rest) == List.append(&2, M.Node, U, V) : List<&2, M.Node>} -> {M.read_all(1n+p, M.attach(t, n), rest) == List.append(&2, M.Node, U, n <> V) : List<&2, M.Node>} -> {M.fits(1n+p, M.attach(t, n), rest) == True{} : Bool} -> K) -> K, k: @U: List<&2, M.Node> -> @V: List<&2, M.Node> -> {M.read_all(1n+p, t, s <> rest) == List.append(&2, M.Node, U, V) : List<&2, M.Node>} -> {M.read_all(2n+p, M.attach(t, n), s <> rest) == List.append(&2, M.Node, U, n <> V) : List<&2, M.Node>} -> {M.fits(2n+p, M.attach(t, n), s <> rest) == True{} : Bool} -> K) -> K:
  match c2:
    case True{}:
      ihR(ec2, +U2 => V2 => o2 => n2 => f2 => k(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> U2), List.append(&2, M.Node, V2, M.read_all(p, t, rest)),
        Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, List.append(&2, M.Node, U2, V2), M.read_all(p, t, rest))), List.append(&2, M.Node, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> U2), List.append(&2, M.Node, V2, M.read_all(p, t, rest))),
          Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, l, M.read_all(p, t, rest))), M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), List.append(&2, M.Node, U2, V2), o2),
          asc1(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s, U2, V2, M.read_all(p, t, rest))),
        Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.read_all(1n+p, M.attach(t, n), rest))), List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, List.append(&2, M.Node, U2, n <> V2), M.read_all(p, t, rest))), List.append(&2, M.Node, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> U2), n <> List.append(&2, M.Node, V2, M.read_all(p, t, rest))),
          rd3(s, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{})), M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), List.append(&2, M.Node, U2, n <> V2), M.read_all(1n+p, M.attach(t, n), rest), M.read_all(p, t, rest),
            Equal.trans(List<&2, M.Node>, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{})), M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => M.read_all(1n+p, M.attach(t, n), l), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{}), M.children(t, Some{M.Node.name(s)}, False{}), chs_off(t, n, Some{par}, R, Some{M.Node.name(s)}, False{}, hp, AL.name_ne_sym(M.Node.name(s), par, e0))), same_up(p, t, M.children(t, Some{M.Node.name(s)}, False{}), n, Some{par}, R, hp, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf), ec1)),
            Equal.trans(List<&2, M.Node>, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), List.append(&2, M.Node, U2, n <> V2), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => M.read_all(1n+p, M.attach(t, n), l), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{}), M.children(t, Some{M.Node.name(s)}, True{}), chs_off(t, n, Some{par}, R, Some{M.Node.name(s)}, True{}, hp, AL.name_ne_sym(M.Node.name(s), par, e0))), n2),
            same_up(p, t, rest, n, Some{par}, R, hp, Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf)), nd_sep_l(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), par, Comp.and_right(Bool.not(M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s))), M.nodup(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), nd_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), hd)), ec2))),
          asc1(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s, U2, n <> V2, M.read_all(p, t, rest))),
        (%Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, False{}), M.children(t, Some{M.Node.name(s)}, False{}), chs_off(t, n, Some{par}, R, Some{M.Node.name(s)}, False{}, hp, AL.name_ne_sym(M.Node.name(s), par, e0))) : {Bool.and(M.fits(1n+p, M.attach(t, n), _), Bool.and(M.fits(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.fits(1n+p, M.attach(t, n), rest))) == True{} : Bool}
          %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, True{}), M.children(t, Some{M.Node.name(s)}, True{}), chs_off(t, n, Some{par}, R, Some{M.Node.name(s)}, True{}, hp, AL.name_ne_sym(M.Node.name(s), par, e0))) : {Bool.and(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(1n+p, M.attach(t, n), _), M.fits(1n+p, M.attach(t, n), rest))) == True{} : Bool}
          AL.and_intro(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.fits(1n+p, M.attach(t, n), rest)), fits_up(p, t, M.children(t, Some{M.Node.name(s)}, False{}), n, Some{par}, R, hp, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf), ec1), AL.and_intro(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.fits(1n+p, M.attach(t, n), rest), f2, fits_up(p, t, rest, n, Some{par}, R, hp, Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf)), nd_sep_l(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), par, Comp.and_right(Bool.not(M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s))), M.nodup(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), nd_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), hd)), ec2)))))))
    case False{}:
      ihC(ML.or_left_false(M.named(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par), M.named(M.read_all(p, t, rest), par), nap_t(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), par, hMM), ec2), U3 => V3 => o3 => n3 => f3 => k(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), U3)), V3,
        Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), List.append(&2, M.Node, U3, V3))), List.append(&2, M.Node, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), U3)), V3),
          Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), l)), M.read_all(p, t, rest), List.append(&2, M.Node, U3, V3), o3),
          asc2(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), U3, V3)),
        Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.read_all(1n+p, M.attach(t, n), rest))), List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), List.append(&2, M.Node, U3, n <> V3))), List.append(&2, M.Node, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), U3)), n <> V3),
          rd3(s, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{})), M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(1n+p, M.attach(t, n), rest), List.append(&2, M.Node, U3, n <> V3),
            Equal.trans(List<&2, M.Node>, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{})), M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => M.read_all(1n+p, M.attach(t, n), l), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{}), M.children(t, Some{M.Node.name(s)}, False{}), chs_off(t, n, Some{par}, R, Some{M.Node.name(s)}, False{}, hp, AL.name_ne_sym(M.Node.name(s), par, e0))), same_up(p, t, M.children(t, Some{M.Node.name(s)}, False{}), n, Some{par}, R, hp, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf), ec1)),
            Equal.trans(List<&2, M.Node>, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => M.read_all(1n+p, M.attach(t, n), l), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{}), M.children(t, Some{M.Node.name(s)}, True{}), chs_off(t, n, Some{par}, R, Some{M.Node.name(s)}, True{}, hp, AL.name_ne_sym(M.Node.name(s), par, e0))), same_up(p, t, M.children(t, Some{M.Node.name(s)}, True{}), n, Some{par}, R, hp, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf)), ec2)),
            n3),
          asc2(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), U3, n <> V3)),
        (%Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, False{}), M.children(t, Some{M.Node.name(s)}, False{}), chs_off(t, n, Some{par}, R, Some{M.Node.name(s)}, False{}, hp, AL.name_ne_sym(M.Node.name(s), par, e0))) : {Bool.and(M.fits(1n+p, M.attach(t, n), _), Bool.and(M.fits(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.fits(1n+p, M.attach(t, n), rest))) == True{} : Bool}
          %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, True{}), M.children(t, Some{M.Node.name(s)}, True{}), chs_off(t, n, Some{par}, R, Some{M.Node.name(s)}, True{}, hp, AL.name_ne_sym(M.Node.name(s), par, e0))) : {Bool.and(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(1n+p, M.attach(t, n), _), M.fits(1n+p, M.attach(t, n), rest))) == True{} : Bool}
          AL.and_intro(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.fits(1n+p, M.attach(t, n), rest)), fits_up(p, t, M.children(t, Some{M.Node.name(s)}, False{}), n, Some{par}, R, hp, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf), ec1), AL.and_intro(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.fits(1n+p, M.attach(t, n), rest), fits_up(p, t, M.children(t, Some{M.Node.name(s)}, True{}), n, Some{par}, R, hp, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf)), ec2), f3)))))

# The element's parent read below `s`, which is not it.
def hit.miss(-K: Type, +p: Nat, +t: List<&2, M.Node>, +s: M.Node, +rest: List<&2, M.Node>, +n: M.Node, +par: M.Name, c1: Bool, +ec1: {M.named(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par) == c1 : Bool}, +R: Bool, +hp: {M.Node.place(n) == M.Place{Some{par}, R} : M.Place}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +np: {M.Name.same(Some{par}, Some{M.Node.name(n)}) == False{} : Bool}, +hf: {M.fits(1n+p, t, s <> rest) == True{} : Bool}, +hd: {M.nodup(M.read_all(1n+p, t, s <> rest)) == True{} : Bool}, +hr: {M.named(M.read_all(1n+p, t, s <> rest), par) == True{} : Bool}, +e0: {M.Name.eq(M.Node.name(s), par) == False{} : Bool}, ihL: {M.named(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par) == True{} : Bool} -> (@U: List<&2, M.Node> -> @V: List<&2, M.Node> -> {M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})) == List.append(&2, M.Node, U, V) : List<&2, M.Node>} -> {M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})) == List.append(&2, M.Node, U, n <> V) : List<&2, M.Node>} -> {M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})) == True{} : Bool} -> K) -> K, ihR: {M.named(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par) == True{} : Bool} -> (@U: List<&2, M.Node> -> @V: List<&2, M.Node> -> {M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})) == List.append(&2, M.Node, U, V) : List<&2, M.Node>} -> {M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})) == List.append(&2, M.Node, U, n <> V) : List<&2, M.Node>} -> {M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})) == True{} : Bool} -> K) -> K, ihC: {M.named(M.read_all(p, t, rest), par) == True{} : Bool} -> (@U: List<&2, M.Node> -> @V: List<&2, M.Node> -> {M.read_all(p, t, rest) == List.append(&2, M.Node, U, V) : List<&2, M.Node>} -> {M.read_all(1n+p, M.attach(t, n), rest) == List.append(&2, M.Node, U, n <> V) : List<&2, M.Node>} -> {M.fits(1n+p, M.attach(t, n), rest) == True{} : Bool} -> K) -> K, k: @U: List<&2, M.Node> -> @V: List<&2, M.Node> -> {M.read_all(1n+p, t, s <> rest) == List.append(&2, M.Node, U, V) : List<&2, M.Node>} -> {M.read_all(2n+p, M.attach(t, n), s <> rest) == List.append(&2, M.Node, U, n <> V) : List<&2, M.Node>} -> {M.fits(2n+p, M.attach(t, n), s <> rest) == True{} : Bool} -> K) -> K:
  match c1:
    case True{}:
      ihL(ec1, +U1 => V1 => o1 => n1 => f1 => k(U1, List.append(&2, M.Node, V1, s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))),
        Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), List.append(&2, M.Node, List.append(&2, M.Node, U1, V1), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), List.append(&2, M.Node, U1, List.append(&2, M.Node, V1, s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)))),
          Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => List.append(&2, M.Node, l, s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), List.append(&2, M.Node, U1, V1), o1),
          Lin.nappend_assoc(U1, V1, s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)))),
        Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.read_all(1n+p, M.attach(t, n), rest))), List.append(&2, M.Node, List.append(&2, M.Node, U1, n <> V1), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), List.append(&2, M.Node, U1, n <> List.append(&2, M.Node, V1, s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)))),
          rd3(s, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{})), List.append(&2, M.Node, U1, n <> V1), M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(1n+p, M.attach(t, n), rest), M.read_all(p, t, rest),
            Equal.trans(List<&2, M.Node>, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{})), M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), List.append(&2, M.Node, U1, n <> V1), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => M.read_all(1n+p, M.attach(t, n), l), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{}), M.children(t, Some{M.Node.name(s)}, False{}), chs_off(t, n, Some{par}, R, Some{M.Node.name(s)}, False{}, hp, AL.name_ne_sym(M.Node.name(s), par, e0))), n1),
            Equal.trans(List<&2, M.Node>, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => M.read_all(1n+p, M.attach(t, n), l), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{}), M.children(t, Some{M.Node.name(s)}, True{}), chs_off(t, n, Some{par}, R, Some{M.Node.name(s)}, True{}, hp, AL.name_ne_sym(M.Node.name(s), par, e0))), same_up(p, t, M.children(t, Some{M.Node.name(s)}, True{}), n, Some{par}, R, hp, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf)), nap_l(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), par, AL.or_false_r(M.Name.eq(M.Node.name(s), par), M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par), nd_sep_l(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par, hd, ec1))))),
            same_up(p, t, rest, n, Some{par}, R, hp, Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf)), nap_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), par, AL.or_false_r(M.Name.eq(M.Node.name(s), par), M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par), nd_sep_l(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par, hd, ec1))))),
          Lin.nappend_assoc(U1, n <> V1, s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)))),
        (%Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, False{}), M.children(t, Some{M.Node.name(s)}, False{}), chs_off(t, n, Some{par}, R, Some{M.Node.name(s)}, False{}, hp, AL.name_ne_sym(M.Node.name(s), par, e0))) : {Bool.and(M.fits(1n+p, M.attach(t, n), _), Bool.and(M.fits(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.fits(1n+p, M.attach(t, n), rest))) == True{} : Bool}
          %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, True{}), M.children(t, Some{M.Node.name(s)}, True{}), chs_off(t, n, Some{par}, R, Some{M.Node.name(s)}, True{}, hp, AL.name_ne_sym(M.Node.name(s), par, e0))) : {Bool.and(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(1n+p, M.attach(t, n), _), M.fits(1n+p, M.attach(t, n), rest))) == True{} : Bool}
          AL.and_intro(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.fits(1n+p, M.attach(t, n), rest)), f1, AL.and_intro(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.fits(1n+p, M.attach(t, n), rest), fits_up(p, t, M.children(t, Some{M.Node.name(s)}, True{}), n, Some{par}, R, hp, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf)), nap_l(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), par, AL.or_false_r(M.Name.eq(M.Node.name(s), par), M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par), nd_sep_l(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par, hd, ec1)))), fits_up(p, t, rest, n, Some{par}, R, hp, Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf)), nap_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), par, AL.or_false_r(M.Name.eq(M.Node.name(s), par), M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par), nd_sep_l(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par, hd, ec1)))))))))
    case False{}:
      hit.miss2(K, p, t, s, rest, n, par, M.named(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par), {==}, R, hp, fr, np, hf, hd, hr, e0, ec1,
        ML.or_left_false(M.Name.eq(M.Node.name(s), par), M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par), ML.or_left_false(M.named(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par), M.named(s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par), nap_t(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par, hr), ec1), e0),
        ihR, ihC, k)

# At `s`: either it is the element's parent, and its list on the
# element's side is spliced, or the parent is read below it.
def hit.at(-K: Type, +p: Nat, +t: List<&2, M.Node>, +s: M.Node, +rest: List<&2, M.Node>, +n: M.Node, +par: M.Name, b0: Bool, +e0: {M.Name.eq(M.Node.name(s), par) == b0 : Bool}, R: Bool, +hp: {M.Node.place(n) == M.Place{Some{par}, R} : M.Place}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +np: {M.Name.same(Some{par}, Some{M.Node.name(n)}) == False{} : Bool}, +hf: {M.fits(1n+p, t, s <> rest) == True{} : Bool}, +hd: {M.nodup(M.read_all(1n+p, t, s <> rest)) == True{} : Bool}, +hr: {M.named(M.read_all(1n+p, t, s <> rest), par) == True{} : Bool}, ihL: {M.named(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par) == True{} : Bool} -> (@U: List<&2, M.Node> -> @V: List<&2, M.Node> -> {M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})) == List.append(&2, M.Node, U, V) : List<&2, M.Node>} -> {M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})) == List.append(&2, M.Node, U, n <> V) : List<&2, M.Node>} -> {M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})) == True{} : Bool} -> K) -> K, ihR: {M.named(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), par) == True{} : Bool} -> (@U: List<&2, M.Node> -> @V: List<&2, M.Node> -> {M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})) == List.append(&2, M.Node, U, V) : List<&2, M.Node>} -> {M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})) == List.append(&2, M.Node, U, n <> V) : List<&2, M.Node>} -> {M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})) == True{} : Bool} -> K) -> K, ihC: {M.named(M.read_all(p, t, rest), par) == True{} : Bool} -> (@U: List<&2, M.Node> -> @V: List<&2, M.Node> -> {M.read_all(p, t, rest) == List.append(&2, M.Node, U, V) : List<&2, M.Node>} -> {M.read_all(1n+p, M.attach(t, n), rest) == List.append(&2, M.Node, U, n <> V) : List<&2, M.Node>} -> {M.fits(1n+p, M.attach(t, n), rest) == True{} : Bool} -> K) -> K, k: @U: List<&2, M.Node> -> @V: List<&2, M.Node> -> {M.read_all(1n+p, t, s <> rest) == List.append(&2, M.Node, U, V) : List<&2, M.Node>} -> {M.read_all(2n+p, M.attach(t, n), s <> rest) == List.append(&2, M.Node, U, n <> V) : List<&2, M.Node>} -> {M.fits(2n+p, M.attach(t, n), s <> rest) == True{} : Bool} -> K) -> K:
  match b0:
    case True{}:
      match R:
        case True{}:
          k(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> M.read_all(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, True{}))), List.append(&2, M.Node, M.read_all(Nat.sub(p, List.length(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, True{}))), t, M.children(apost(t, n), Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)),
            Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, List.append(&2, M.Node, M.read_all(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, True{})), M.read_all(Nat.sub(p, List.length(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, True{}))), t, M.children(apost(t, n), Some{M.Node.name(s)}, True{}))), M.read_all(p, t, rest))), List.append(&2, M.Node, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> M.read_all(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, True{}))), List.append(&2, M.Node, M.read_all(Nat.sub(p, List.length(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, True{}))), t, M.children(apost(t, n), Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))),
              Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, l, M.read_all(p, t, rest))), M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), List.append(&2, M.Node, M.read_all(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, True{})), M.read_all(Nat.sub(p, List.length(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, True{}))), t, M.children(apost(t, n), Some{M.Node.name(s)}, True{}))), Equal.trans(List<&2, M.Node>, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, List.append(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, True{}), M.children(apost(t, n), Some{M.Node.name(s)}, True{}))), List.append(&2, M.Node, M.read_all(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, True{})), M.read_all(Nat.sub(p, List.length(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, True{}))), t, M.children(apost(t, n), Some{M.Node.name(s)}, True{}))), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => M.read_all(p, t, l), M.children(t, Some{M.Node.name(s)}, True{}), List.append(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, True{}), M.children(apost(t, n), Some{M.Node.name(s)}, True{})), children_split(t, n, Some{M.Node.name(s)}, True{})), read_app(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, True{}), M.children(apost(t, n), Some{M.Node.name(s)}, True{})))),
              asc1(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s, M.read_all(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, True{})), M.read_all(Nat.sub(p, List.length(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, True{}))), t, M.children(apost(t, n), Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))),
            Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.read_all(1n+p, M.attach(t, n), rest))), List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, List.append(&2, M.Node, M.read_all(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, True{})), n <> M.read_all(Nat.sub(p, List.length(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, True{}))), t, M.children(apost(t, n), Some{M.Node.name(s)}, True{}))), M.read_all(p, t, rest))), List.append(&2, M.Node, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> M.read_all(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, True{}))), n <> List.append(&2, M.Node, M.read_all(Nat.sub(p, List.length(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, True{}))), t, M.children(apost(t, n), Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))),
              rd3(s, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{})), M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), List.append(&2, M.Node, M.read_all(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, True{})), n <> M.read_all(Nat.sub(p, List.length(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, True{}))), t, M.children(apost(t, n), Some{M.Node.name(s)}, True{}))), M.read_all(1n+p, M.attach(t, n), rest), M.read_all(p, t, rest),
                Equal.trans(List<&2, M.Node>, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{})), M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => M.read_all(1n+p, M.attach(t, n), l), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{}), M.children(t, Some{M.Node.name(s)}, False{}), chs_side(t, n, Some{par}, True{}, Some{M.Node.name(s)}, False{}, hp, {==})), same_up(p, t, M.children(t, Some{M.Node.name(s)}, False{}), n, Some{par}, R, hp, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf), nd_sep_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par, hd, AL.or_left(M.Name.eq(M.Node.name(s), par), M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par), e0)))),
                Equal.trans(List<&2, M.Node>, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.read_all(1n+p, M.attach(t, n), List.append(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, True{}), n <> M.children(apost(t, n), Some{M.Node.name(s)}, True{}))), List.append(&2, M.Node, M.read_all(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, True{})), n <> M.read_all(Nat.sub(p, List.length(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, True{}))), t, M.children(apost(t, n), Some{M.Node.name(s)}, True{}))), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => M.read_all(1n+p, M.attach(t, n), l), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{}), List.append(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, True{}), n <> M.children(apost(t, n), Some{M.Node.name(s)}, True{})), children_attach_split(t, n, Some{M.Node.name(s)}, True{}, Equal.trans(Bool, M.Node.hangs(n, Some{M.Node.name(s)}, True{}), Bool.and(M.Name.eq(par, M.Node.name(s)), Bool.not(Bool.xor(True{}, True{}))), True{}, hangs_of(n, Some{par}, True{}, Some{M.Node.name(s)}, True{}, hp), (%Equal.sym(Bool, M.Name.eq(par, M.Node.name(s)), True{}, Equal.trans(Bool, M.Name.eq(par, M.Node.name(s)), M.Name.eq(M.Node.name(s), par), True{}, AL.name_eq_sym(M.Node.name(s), par), e0)) : {Bool.and(_, Bool.not(Bool.xor(True{}, True{}))) == True{} : Bool} {==})))), li_read(p, t, n, Some{par}, True{}, hp, fr, np, M.children(apre(t, n), Some{M.Node.name(s)}, True{}), M.children(apost(t, n), Some{M.Node.name(s)}, True{}), (%children_split(t, n, Some{M.Node.name(s)}, True{}) : {M.fits(p, t, _) == True{} : Bool} Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf))), (%children_split(t, n, Some{M.Node.name(s)}, True{}) : {M.named(M.read_all(p, t, _), par) == False{} : Bool} nap_l(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), par, AL.named_transport(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s), par, AL.name_eq_equal(M.Node.name(s), par, e0), AL.not_of_true(M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s)), Comp.and_left(Bool.not(M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s))), M.nodup(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), nd_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), hd)))))))),
                same_up(p, t, rest, n, Some{par}, R, hp, Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf)), nap_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), par, AL.named_transport(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s), par, AL.name_eq_equal(M.Node.name(s), par, e0), AL.not_of_true(M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s)), Comp.and_left(Bool.not(M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s))), M.nodup(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), nd_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), hd))))))),
              asc1(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s, M.read_all(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, True{})), n <> M.read_all(Nat.sub(p, List.length(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, True{}))), t, M.children(apost(t, n), Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))),
            (%Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, False{}), M.children(t, Some{M.Node.name(s)}, False{}), chs_side(t, n, Some{par}, True{}, Some{M.Node.name(s)}, False{}, hp, {==})) : {Bool.and(M.fits(1n+p, M.attach(t, n), _), Bool.and(M.fits(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.fits(1n+p, M.attach(t, n), rest))) == True{} : Bool}
          %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, True{}), List.append(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, True{}), n <> M.children(apost(t, n), Some{M.Node.name(s)}, True{})), children_attach_split(t, n, Some{M.Node.name(s)}, True{}, Equal.trans(Bool, M.Node.hangs(n, Some{M.Node.name(s)}, True{}), Bool.and(M.Name.eq(par, M.Node.name(s)), Bool.not(Bool.xor(True{}, True{}))), True{}, hangs_of(n, Some{par}, True{}, Some{M.Node.name(s)}, True{}, hp), (%Equal.sym(Bool, M.Name.eq(par, M.Node.name(s)), True{}, Equal.trans(Bool, M.Name.eq(par, M.Node.name(s)), M.Name.eq(M.Node.name(s), par), True{}, AL.name_eq_sym(M.Node.name(s), par), e0)) : {Bool.and(_, Bool.not(Bool.xor(True{}, True{}))) == True{} : Bool} {==})))) : {Bool.and(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(1n+p, M.attach(t, n), _), M.fits(1n+p, M.attach(t, n), rest))) == True{} : Bool}
          AL.and_intro(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(1n+p, M.attach(t, n), List.append(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, True{}), n <> M.children(apost(t, n), Some{M.Node.name(s)}, True{}))), M.fits(1n+p, M.attach(t, n), rest)), fits_up(p, t, M.children(t, Some{M.Node.name(s)}, False{}), n, Some{par}, R, hp, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf), nd_sep_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par, hd, AL.or_left(M.Name.eq(M.Node.name(s), par), M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par), e0))), AL.and_intro(M.fits(1n+p, M.attach(t, n), List.append(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, True{}), n <> M.children(apost(t, n), Some{M.Node.name(s)}, True{}))), M.fits(1n+p, M.attach(t, n), rest), li_fits(p, t, n, Some{par}, True{}, hp, fr, np, M.children(apre(t, n), Some{M.Node.name(s)}, True{}), M.children(apost(t, n), Some{M.Node.name(s)}, True{}), (%children_split(t, n, Some{M.Node.name(s)}, True{}) : {M.fits(p, t, _) == True{} : Bool} Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf))), (%children_split(t, n, Some{M.Node.name(s)}, True{}) : {M.named(M.read_all(p, t, _), par) == False{} : Bool} nap_l(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), par, AL.named_transport(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s), par, AL.name_eq_equal(M.Node.name(s), par, e0), AL.not_of_true(M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s)), Comp.and_left(Bool.not(M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s))), M.nodup(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), nd_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), hd))))))), fits_up(p, t, rest, n, Some{par}, R, hp, Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf)), nap_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), par, AL.named_transport(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s), par, AL.name_eq_equal(M.Node.name(s), par, e0), AL.not_of_true(M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s)), Comp.and_left(Bool.not(M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s))), M.nodup(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), nd_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), hd))))))))))
        case False{}:
          k(M.read_all(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, False{})), List.append(&2, M.Node, M.read_all(Nat.sub(p, List.length(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, False{}))), t, M.children(apost(t, n), Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))),
            Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), List.append(&2, M.Node, List.append(&2, M.Node, M.read_all(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, False{})), M.read_all(Nat.sub(p, List.length(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, False{}))), t, M.children(apost(t, n), Some{M.Node.name(s)}, False{}))), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), List.append(&2, M.Node, M.read_all(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, False{})), List.append(&2, M.Node, M.read_all(Nat.sub(p, List.length(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, False{}))), t, M.children(apost(t, n), Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)))),
              Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => List.append(&2, M.Node, l, s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), List.append(&2, M.Node, M.read_all(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, False{})), M.read_all(Nat.sub(p, List.length(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, False{}))), t, M.children(apost(t, n), Some{M.Node.name(s)}, False{}))), Equal.trans(List<&2, M.Node>, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), M.read_all(p, t, List.append(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, False{}), M.children(apost(t, n), Some{M.Node.name(s)}, False{}))), List.append(&2, M.Node, M.read_all(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, False{})), M.read_all(Nat.sub(p, List.length(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, False{}))), t, M.children(apost(t, n), Some{M.Node.name(s)}, False{}))), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => M.read_all(p, t, l), M.children(t, Some{M.Node.name(s)}, False{}), List.append(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, False{}), M.children(apost(t, n), Some{M.Node.name(s)}, False{})), children_split(t, n, Some{M.Node.name(s)}, False{})), read_app(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, False{}), M.children(apost(t, n), Some{M.Node.name(s)}, False{})))),
              Lin.nappend_assoc(M.read_all(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, False{})), M.read_all(Nat.sub(p, List.length(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, False{}))), t, M.children(apost(t, n), Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)))),
            Equal.trans(List<&2, M.Node>, List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.read_all(1n+p, M.attach(t, n), rest))), List.append(&2, M.Node, List.append(&2, M.Node, M.read_all(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, False{})), n <> M.read_all(Nat.sub(p, List.length(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, False{}))), t, M.children(apost(t, n), Some{M.Node.name(s)}, False{}))), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), List.append(&2, M.Node, M.read_all(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, False{})), n <> List.append(&2, M.Node, M.read_all(Nat.sub(p, List.length(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, False{}))), t, M.children(apost(t, n), Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)))),
              rd3(s, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{})), List.append(&2, M.Node, M.read_all(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, False{})), n <> M.read_all(Nat.sub(p, List.length(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, False{}))), t, M.children(apost(t, n), Some{M.Node.name(s)}, False{}))), M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(1n+p, M.attach(t, n), rest), M.read_all(p, t, rest),
                Equal.trans(List<&2, M.Node>, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{})), M.read_all(1n+p, M.attach(t, n), List.append(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, False{}), n <> M.children(apost(t, n), Some{M.Node.name(s)}, False{}))), List.append(&2, M.Node, M.read_all(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, False{})), n <> M.read_all(Nat.sub(p, List.length(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, False{}))), t, M.children(apost(t, n), Some{M.Node.name(s)}, False{}))), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => M.read_all(1n+p, M.attach(t, n), l), M.children(M.attach(t, n), Some{M.Node.name(s)}, False{}), List.append(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, False{}), n <> M.children(apost(t, n), Some{M.Node.name(s)}, False{})), children_attach_split(t, n, Some{M.Node.name(s)}, False{}, Equal.trans(Bool, M.Node.hangs(n, Some{M.Node.name(s)}, False{}), Bool.and(M.Name.eq(par, M.Node.name(s)), Bool.not(Bool.xor(False{}, False{}))), True{}, hangs_of(n, Some{par}, False{}, Some{M.Node.name(s)}, False{}, hp), (%Equal.sym(Bool, M.Name.eq(par, M.Node.name(s)), True{}, Equal.trans(Bool, M.Name.eq(par, M.Node.name(s)), M.Name.eq(M.Node.name(s), par), True{}, AL.name_eq_sym(M.Node.name(s), par), e0)) : {Bool.and(_, Bool.not(Bool.xor(False{}, False{}))) == True{} : Bool} {==})))), li_read(p, t, n, Some{par}, False{}, hp, fr, np, M.children(apre(t, n), Some{M.Node.name(s)}, False{}), M.children(apost(t, n), Some{M.Node.name(s)}, False{}), (%children_split(t, n, Some{M.Node.name(s)}, False{}) : {M.fits(p, t, _) == True{} : Bool} Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf)), (%children_split(t, n, Some{M.Node.name(s)}, False{}) : {M.named(M.read_all(p, t, _), par) == False{} : Bool} nd_sep_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par, hd, AL.or_left(M.Name.eq(M.Node.name(s), par), M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par), e0))))),
                Equal.trans(List<&2, M.Node>, M.read_all(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.read_all(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => M.read_all(1n+p, M.attach(t, n), l), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{}), M.children(t, Some{M.Node.name(s)}, True{}), chs_side(t, n, Some{par}, False{}, Some{M.Node.name(s)}, True{}, hp, {==})), same_up(p, t, M.children(t, Some{M.Node.name(s)}, True{}), n, Some{par}, R, hp, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf)), nap_l(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), par, AL.named_transport(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s), par, AL.name_eq_equal(M.Node.name(s), par, e0), AL.not_of_true(M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s)), Comp.and_left(Bool.not(M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s))), M.nodup(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), nd_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), hd))))))),
                same_up(p, t, rest, n, Some{par}, R, hp, Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf)), nap_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), par, AL.named_transport(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s), par, AL.name_eq_equal(M.Node.name(s), par, e0), AL.not_of_true(M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s)), Comp.and_left(Bool.not(M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s))), M.nodup(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), nd_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), hd))))))),
              Lin.nappend_assoc(M.read_all(p, t, M.children(apre(t, n), Some{M.Node.name(s)}, False{})), n <> M.read_all(Nat.sub(p, List.length(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, False{}))), t, M.children(apost(t, n), Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)))),
            (%Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, False{}), List.append(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, False{}), n <> M.children(apost(t, n), Some{M.Node.name(s)}, False{})), children_attach_split(t, n, Some{M.Node.name(s)}, False{}, Equal.trans(Bool, M.Node.hangs(n, Some{M.Node.name(s)}, False{}), Bool.and(M.Name.eq(par, M.Node.name(s)), Bool.not(Bool.xor(False{}, False{}))), True{}, hangs_of(n, Some{par}, False{}, Some{M.Node.name(s)}, False{}, hp), (%Equal.sym(Bool, M.Name.eq(par, M.Node.name(s)), True{}, Equal.trans(Bool, M.Name.eq(par, M.Node.name(s)), M.Name.eq(M.Node.name(s), par), True{}, AL.name_eq_sym(M.Node.name(s), par), e0)) : {Bool.and(_, Bool.not(Bool.xor(False{}, False{}))) == True{} : Bool} {==})))) : {Bool.and(M.fits(1n+p, M.attach(t, n), _), Bool.and(M.fits(1n+p, M.attach(t, n), M.children(M.attach(t, n), Some{M.Node.name(s)}, True{})), M.fits(1n+p, M.attach(t, n), rest))) == True{} : Bool}
          %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), Some{M.Node.name(s)}, True{}), M.children(t, Some{M.Node.name(s)}, True{}), chs_side(t, n, Some{par}, False{}, Some{M.Node.name(s)}, True{}, hp, {==})) : {Bool.and(M.fits(1n+p, M.attach(t, n), List.append(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, False{}), n <> M.children(apost(t, n), Some{M.Node.name(s)}, False{}))), Bool.and(M.fits(1n+p, M.attach(t, n), _), M.fits(1n+p, M.attach(t, n), rest))) == True{} : Bool}
          AL.and_intro(M.fits(1n+p, M.attach(t, n), List.append(&2, M.Node, M.children(apre(t, n), Some{M.Node.name(s)}, False{}), n <> M.children(apost(t, n), Some{M.Node.name(s)}, False{}))), Bool.and(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.fits(1n+p, M.attach(t, n), rest)), li_fits(p, t, n, Some{par}, False{}, hp, fr, np, M.children(apre(t, n), Some{M.Node.name(s)}, False{}), M.children(apost(t, n), Some{M.Node.name(s)}, False{}), (%children_split(t, n, Some{M.Node.name(s)}, False{}) : {M.fits(p, t, _) == True{} : Bool} Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf)), (%children_split(t, n, Some{M.Node.name(s)}, False{}) : {M.named(M.read_all(p, t, _), par) == False{} : Bool} nd_sep_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par, hd, AL.or_left(M.Name.eq(M.Node.name(s), par), M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), par), e0)))), AL.and_intro(M.fits(1n+p, M.attach(t, n), M.children(t, Some{M.Node.name(s)}, True{})), M.fits(1n+p, M.attach(t, n), rest), fits_up(p, t, M.children(t, Some{M.Node.name(s)}, True{}), n, Some{par}, R, hp, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf)), nap_l(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), par, AL.named_transport(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s), par, AL.name_eq_equal(M.Node.name(s), par, e0), AL.not_of_true(M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s)), Comp.and_left(Bool.not(M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s))), M.nodup(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), nd_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), hd)))))), fits_up(p, t, rest, n, Some{par}, R, hp, Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf)), nap_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), par, AL.named_transport(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s), par, AL.name_eq_equal(M.Node.name(s), par, e0), AL.not_of_true(M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s)), Comp.and_left(Bool.not(M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s))), M.nodup(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), nd_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), hd))))))))))
    case False{}:
      hit.miss(K, p, t, s, rest, n, par, M.named(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), par), {==}, R, hp, fr, np, hf, hd, hr, e0, ihL, ihR, ihC, k)

# A reading that reaches the element's parent: once the element is
# attached it is the old reading with the element spliced in, and it still
# fits one fuel up.
def hit(-K: Type, q: Nat, +t: List<&2, M.Node>, X: List<&2, M.Node>, +n: M.Node, +par: M.Name, +R: Bool, +hp: {M.Node.place(n) == M.Place{Some{par}, R} : M.Place}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +np: {M.Name.same(Some{par}, Some{M.Node.name(n)}) == False{} : Bool}, +hf: {M.fits(q, t, X) == True{} : Bool}, +hd: {M.nodup(M.read_all(q, t, X)) == True{} : Bool}, hr: {M.named(M.read_all(q, t, X), par) == True{} : Bool}, k: @U: List<&2, M.Node> -> @V: List<&2, M.Node> -> {M.read_all(q, t, X) == List.append(&2, M.Node, U, V) : List<&2, M.Node>} -> {M.read_all(1n+q, M.attach(t, n), X) == List.append(&2, M.Node, U, n <> V) : List<&2, M.Node>} -> {M.fits(1n+q, M.attach(t, n), X) == True{} : Bool} -> K) -> K:
  match q:
    case 0n:
      Empty.absurd(K, Comp.false_true(hr))
    case 1n++p:
      match X:
        case Nil{}:
          Empty.absurd(K, Comp.false_true(hr))
        case +s <> +rest:
          hit.at(K, p, t, s, rest, n, par, M.Name.eq(M.Node.name(s), par), {==}, R, hp, fr, np, hf, hd, hr,
            h1 => k1 => hit(K, p, t, M.children(t, Some{M.Node.name(s)}, False{}), n, par, R, hp, fr, np, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf), nd_l(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), hd), h1, k1),
            h1 => k1 => hit(K, p, t, M.children(t, Some{M.Node.name(s)}, True{}), n, par, R, hp, fr, np, Comp.and_left(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf)), nd_l(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), Comp.and_right(Bool.not(M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s))), M.nodup(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), nd_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), hd))), h1, k1),
            h1 => k1 => hit(K, p, t, rest, n, par, R, hp, fr, np, Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest), Comp.and_right(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, False{})), Bool.and(M.fits(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.fits(p, t, rest)), hf)), nd_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), Comp.and_right(Bool.not(M.named(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), M.Node.name(s))), M.nodup(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest))), nd_r(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), hd))), h1, k1),
            k)

# Where the parent is read, the element is spliced in; where it is not,
# the reading is as it was.
def leaf_some(+t: List<&2, M.Node>, +n: M.Node, +par: M.Name, +R: Bool, c: Bool, +ec: {M.named(M.read_all(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), par) == c : Bool}, +hp: {M.Node.place(n) == M.Place{Some{par}, R} : M.Place}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +np: {M.Name.same(Some{par}, Some{M.Node.name(n)}) == False{} : Bool}, +inv: {M.invariant(t) == True{} : Bool}) -> {Bool.and(M.fits(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), M.children(t, None{}, True{})), M.nodup(M.read_all(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), M.children(t, None{}, True{})))) == True{} : Bool}:
  match c:
    case True{}:
      hit({Bool.and(M.fits(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), M.children(t, None{}, True{})), M.nodup(M.read_all(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), M.children(t, None{}, True{})))) == True{} : Bool}, 1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}), n, par, R, hp, fr, np, Comp.and_left(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.read_all(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}))), inv), Comp.and_right(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.read_all(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}))), inv), ec,
        U => V => +o => nw => f => (%Equal.sym(List<&2, M.Node>, M.read_all(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), M.children(t, None{}, True{})), List.append(&2, M.Node, U, n <> V), nw) : {Bool.and(M.fits(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), M.children(t, None{}, True{})), M.nodup(_)) == True{} : Bool}
          AL.and_intro(M.fits(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), M.children(t, None{}, True{})), M.nodup(List.append(&2, M.Node, U, n <> V)), f,
            nodup_insert(U, n, V, (%o : {M.nodup(_) == True{} : Bool} Comp.and_right(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.read_all(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}))), inv)), (%o : {M.named(_, M.Node.name(n)) == False{} : Bool} AL.order_sub(t, M.Node.name(n), AL.not_of_true(M.named(t, M.Node.name(n)), Comp.and_left(Bool.not(M.named(t, M.Node.name(n))), Bool.not(M.hangs_under(t, M.Node.name(n))), fr))))))))
    case False{}:
      %Equal.sym(List<&2, M.Node>, M.read_all(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), M.children(t, None{}, True{})), M.read_all(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), same_up(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}), n, Some{par}, R, hp, Comp.and_left(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.read_all(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}))), inv), ec)) : {Bool.and(M.fits(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), M.children(t, None{}, True{})), M.nodup(_)) == True{} : Bool}
      AL.and_intro(M.fits(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), M.children(t, None{}, True{})), M.nodup(M.read_all(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}))), fits_up(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}), n, Some{par}, R, hp, Comp.and_left(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.read_all(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}))), inv), ec), Comp.and_right(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.read_all(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}))), inv))

# The element as a new root, placed among the roots by name.
def leaf_root(+t: List<&2, M.Node>, +n: M.Node, +hp: {M.Node.place(n) == M.Place{None{}, True{}} : M.Place}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +np: {M.Name.same(None{}, Some{M.Node.name(n)}) == False{} : Bool}, +inv: {M.invariant(t) == True{} : Bool}) -> {Bool.and(M.fits(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), M.children(M.attach(t, n), None{}, True{})), M.nodup(M.read_all(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), M.children(M.attach(t, n), None{}, True{})))) == True{} : Bool}:
  %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), None{}, True{}), List.append(&2, M.Node, M.children(apre(t, n), None{}, True{}), n <> M.children(apost(t, n), None{}, True{})), children_attach_split(t, n, None{}, True{}, hangs_of(n, None{}, True{}, None{}, True{}, hp))) : {Bool.and(M.fits(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), _), M.nodup(M.read_all(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), _))) == True{} : Bool}
  %Equal.sym(List<&2, M.Node>, M.read_all(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), List.append(&2, M.Node, M.children(apre(t, n), None{}, True{}), n <> M.children(apost(t, n), None{}, True{}))), List.append(&2, M.Node, M.read_all(1n+List.length(&2, M.Node, t), t, M.children(apre(t, n), None{}, True{})), n <> M.read_all(Nat.sub(1n+List.length(&2, M.Node, t), List.length(&2, M.Node, M.children(apre(t, n), None{}, True{}))), t, M.children(apost(t, n), None{}, True{}))), li_read(1n+List.length(&2, M.Node, t), t, n, None{}, True{}, hp, fr, np, M.children(apre(t, n), None{}, True{}), M.children(apost(t, n), None{}, True{}), (%children_split(t, n, None{}, True{}) : {M.fits(1n+List.length(&2, M.Node, t), t, _) == True{} : Bool} Comp.and_left(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.read_all(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}))), inv)), {==})) : {Bool.and(M.fits(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), List.append(&2, M.Node, M.children(apre(t, n), None{}, True{}), n <> M.children(apost(t, n), None{}, True{}))), M.nodup(_)) == True{} : Bool}
  AL.and_intro(M.fits(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), List.append(&2, M.Node, M.children(apre(t, n), None{}, True{}), n <> M.children(apost(t, n), None{}, True{}))), M.nodup(List.append(&2, M.Node, M.read_all(1n+List.length(&2, M.Node, t), t, M.children(apre(t, n), None{}, True{})), n <> M.read_all(Nat.sub(1n+List.length(&2, M.Node, t), List.length(&2, M.Node, M.children(apre(t, n), None{}, True{}))), t, M.children(apost(t, n), None{}, True{})))),
    li_fits(1n+List.length(&2, M.Node, t), t, n, None{}, True{}, hp, fr, np, M.children(apre(t, n), None{}, True{}), M.children(apost(t, n), None{}, True{}), (%children_split(t, n, None{}, True{}) : {M.fits(1n+List.length(&2, M.Node, t), t, _) == True{} : Bool} Comp.and_left(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.read_all(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}))), inv)), {==}),
    nodup_insert(M.read_all(1n+List.length(&2, M.Node, t), t, M.children(apre(t, n), None{}, True{})), n, M.read_all(Nat.sub(1n+List.length(&2, M.Node, t), List.length(&2, M.Node, M.children(apre(t, n), None{}, True{}))), t, M.children(apost(t, n), None{}, True{})),
      (%read_app(1n+List.length(&2, M.Node, t), t, M.children(apre(t, n), None{}, True{}), M.children(apost(t, n), None{}, True{})) : {M.nodup(_) == True{} : Bool}
        %children_split(t, n, None{}, True{}) : {M.nodup(M.read_all(1n+List.length(&2, M.Node, t), t, _)) == True{} : Bool}
        Comp.and_right(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.read_all(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}))), inv)),
      (%read_app(1n+List.length(&2, M.Node, t), t, M.children(apre(t, n), None{}, True{}), M.children(apost(t, n), None{}, True{})) : {M.named(_, M.Node.name(n)) == False{} : Bool}
        %children_split(t, n, None{}, True{}) : {M.named(M.read_all(1n+List.length(&2, M.Node, t), t, _), M.Node.name(n)) == False{} : Bool}
        AL.order_sub(t, M.Node.name(n), AL.not_of_true(M.named(t, M.Node.name(n)), Comp.and_left(Bool.not(M.named(t, M.Node.name(n))), Bool.not(M.hangs_under(t, M.Node.name(n))), fr))))))

def leaf_none(+t: List<&2, M.Node>, +n: M.Node, R: Bool, +hp: {M.Node.place(n) == M.Place{None{}, R} : M.Place}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +np: {M.Name.same(None{}, Some{M.Node.name(n)}) == False{} : Bool}, +inv: {M.invariant(t) == True{} : Bool}) -> {Bool.and(M.fits(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), M.children(M.attach(t, n), None{}, True{})), M.nodup(M.read_all(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), M.children(M.attach(t, n), None{}, True{})))) == True{} : Bool}:
  match R:
    case True{}:
      leaf_root(t, n, hp, fr, np, inv)
    case False{}:
      %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), None{}, True{}), M.children(t, None{}, True{}), chs_side(t, n, None{}, False{}, None{}, True{}, hp, {==})) : {Bool.and(M.fits(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), _), M.nodup(M.read_all(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), _))) == True{} : Bool}
      %Equal.sym(List<&2, M.Node>, M.read_all(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), M.children(t, None{}, True{})), M.read_all(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), same_up(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}), n, None{}, False{}, hp, Comp.and_left(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.read_all(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}))), inv), {==})) : {Bool.and(M.fits(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), M.children(t, None{}, True{})), M.nodup(_)) == True{} : Bool}
      AL.and_intro(M.fits(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), M.children(t, None{}, True{})), M.nodup(M.read_all(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}))), fits_up(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}), n, None{}, False{}, hp, Comp.and_left(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.read_all(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}))), inv), {==}), Comp.and_right(M.fits(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), M.nodup(M.read_all(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{}))), inv))

def leaf_at(+t: List<&2, M.Node>, +n: M.Node, P: Maybe<&2, M.Name>, +R: Bool, +hp: {M.Node.place(n) == M.Place{P, R} : M.Place}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +np: {M.Name.same(P, Some{M.Node.name(n)}) == False{} : Bool}, +inv: {M.invariant(t) == True{} : Bool}) -> {Bool.and(M.fits(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), M.children(M.attach(t, n), None{}, True{})), M.nodup(M.read_all(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), M.children(M.attach(t, n), None{}, True{})))) == True{} : Bool}:
  match P:
    case None{}:
      leaf_none(t, n, R, hp, fr, np, inv)
    case Some{+par}:
      %Equal.sym(List<&2, M.Node>, M.children(M.attach(t, n), None{}, True{}), M.children(t, None{}, True{}), chs_off(t, n, Some{par}, R, None{}, True{}, hp, {==})) : {Bool.and(M.fits(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), _), M.nodup(M.read_all(1n+1n+List.length(&2, M.Node, t), M.attach(t, n), _))) == True{} : Bool}
      leaf_some(t, n, par, R, M.named(M.read_all(1n+List.length(&2, M.Node, t), t, M.children(t, None{}, True{})), par), {==}, hp, fr, np, inv)

# Any fresh element that is not its own parent, attached anywhere, keeps
# the invariant.
def invariant_leaf(+t: List<&2, M.Node>, +n: M.Node, +P: Maybe<&2, M.Name>, +R: Bool, +hp: {M.Node.place(n) == M.Place{P, R} : M.Place}, +fr: {M.fresh(t, M.Node.name(n)) == True{} : Bool}, +np: {M.Name.same(P, Some{M.Node.name(n)}) == False{} : Bool}, +inv: {M.invariant(t) == True{} : Bool}) -> {M.invariant(M.attach(t, n)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, M.Node, M.attach(t, n)), 1n+List.length(&2, M.Node, t), AL.attach_length(t, n)) : {Bool.and(M.fits(1n+_, M.attach(t, n), M.children(M.attach(t, n), None{}, True{})), M.nodup(M.read_all(1n+_, M.attach(t, n), M.children(M.attach(t, n), None{}, True{})))) == True{} : Bool}
  leaf_at(t, n, P, R, hp, fr, np, inv)

# An event's actions
# ------------------
#
# What `apply` needs of an event's actions: each element it attaches has a
# name its author mints no lower than the last, and hangs under a name the
# event had seen or minted before it (`aok`). Then every attach is a fresh
# leaf, and every mark keeps the invariant.
def pok(pl: M.Place, +W: List<&2, Nat>, +k: Nat, +m: Nat) -> Bool:
  match pl:
    case M.Place{p, r}:
      Lin.before.m(p, W, k, m)

def aok(acts: List<&2, M.Action>, +W: List<&2, Nat>, +k: Nat, +lo: Nat) -> Bool:
  match acts:
    case Nil{}:
      True{}
    case M.Attach{+a, it, pl} <> rest:
      Bool.and(Nat.is_le(lo, a), Bool.and(pok(pl, W, k, a), aok(rest, W, k, 1n+a)))
    case M.Delete{tg} <> rest:
      aok(rest, W, k, lo)

# The ordinal the event mints next, once the actions are done.
def mfin(acts: List<&2, M.Action>, lo: Nat) -> Nat:
  match acts:
    case Nil{}:
      lo
    case M.Attach{a, it, pl} <> rest:
      mfin(rest, 1n+a)
    case M.Delete{tg} <> rest:
      mfin(rest, lo)

def before_le(nm: M.Name, +W: List<&2, Nat>, +k: Nat, +m: Nat, +a: Nat, +le: {Nat.is_le(m, a) == True{} : Bool}, +h: {Lin.before(nm, W, k, m) == True{} : Bool}) -> {Lin.before(nm, W, k, a) == True{} : Bool}:
  match nm:
    case M.Name{+x, +o}:
      Lin.or_and_mono(Bool.and(Bool.not(Nat.is_eq(x, k)), M.has(W, x)), Nat.is_eq(x, k), Nat.is_lt(o, m), Nat.is_lt(o, a), h, e => Lin.lt_le_trans(o, m, a, e, le))

def before.m_le(p: Maybe<&2, M.Name>, +W: List<&2, Nat>, +k: Nat, +m: Nat, +a: Nat, +le: {Nat.is_le(m, a) == True{} : Bool}, +h: {Lin.before.m(p, W, k, m) == True{} : Bool}) -> {Lin.before.m(p, W, k, a) == True{} : Bool}:
  match p:
    case None{}:
      {==}
    case Some{x}:
      before_le(x, W, k, m, a, le, h)

def good_le(n: M.Node, +W: List<&2, Nat>, +k: Nat, +m: Nat, +a: Nat, +le: {Nat.is_le(m, a) == True{} : Bool}, +h: {Lin.good(n, W, k, m) == True{} : Bool}) -> {Lin.good(n, W, k, a) == True{} : Bool}:
  match n:
    case M.Node{+nm, +it, M.Place{+p, +r}, +d}:
      AL.and_intro(Lin.before(nm, W, k, a), Bool.and(Lin.before.m(p, W, k, a), Lin.all_has(d, k <> W)),
        before_le(nm, W, k, m, a, le, Comp.and_left(Lin.before(nm, W, k, m), Bool.and(Lin.before.m(p, W, k, m), Lin.all_has(d, k <> W)), h)),
        AL.and_intro(Lin.before.m(p, W, k, a), Lin.all_has(d, k <> W),
          before.m_le(p, W, k, m, a, le, Comp.and_left(Lin.before.m(p, W, k, m), Lin.all_has(d, k <> W), Comp.and_right(Lin.before(nm, W, k, m), Bool.and(Lin.before.m(p, W, k, m), Lin.all_has(d, k <> W)), h))),
          Comp.and_right(Lin.before.m(p, W, k, m), Lin.all_has(d, k <> W), Comp.and_right(Lin.before(nm, W, k, m), Bool.and(Lin.before.m(p, W, k, m), Lin.all_has(d, k <> W)), h))))

def goods_le(t: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +m: Nat, +a: Nat, +le: {Nat.is_le(m, a) == True{} : Bool}, +h: {Lin.goods(t, W, k, m) == True{} : Bool}) -> {Lin.goods(t, W, k, a) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +x <> +xs:
      AL.and_intro(Lin.good(x, W, k, a), Lin.goods(xs, W, k, a),
        good_le(x, W, k, m, a, le, Comp.and_left(Lin.good(x, W, k, m), Lin.goods(xs, W, k, m), h)),
        goods_le(xs, W, k, m, a, le, Comp.and_right(Lin.good(x, W, k, m), Lin.goods(xs, W, k, m), h)))

def pok_mono(pl: M.Place, +W: List<&2, Nat>, +k: Nat, +m: Nat, +h: {pok(pl, W, k, m) == True{} : Bool}) -> {pok(pl, W, k, 1n+m) == True{} : Bool}:
  match pl:
    case M.Place{+p, r}:
      Lin.before.m_mono(p, W, k, m, h)

def good_leaf(+k: Nat, +a: Nat, +it: Ops.Item, pl: M.Place, +W: List<&2, Nat>, +hp: {pok(pl, W, k, a) == True{} : Bool}) -> {Lin.good(M.Node{M.Name{k, a}, it, pl, Nil{}}, W, k, 1n+a) == True{} : Bool}:
  match pl:
    case M.Place{+p, +r}:
      AL.and_intro(Lin.before(M.Name{k, a}, W, k, 1n+a), Bool.and(Lin.before.m(p, W, k, 1n+a), True{}),
        Lin.before_self(W, k, a),
        AL.and_intro(Lin.before.m(p, W, k, 1n+a), True{}, Lin.before.m_mono(p, W, k, a, hp), {==}))

# One attach of the event's own: a fresh leaf, and the bound moves past it.
def attach_ok(+t: List<&2, M.Node>, +k: Nat, +a: Nat, +it: Ops.Item, pl: M.Place, +W: List<&2, Nat>, +hi: {M.invariant(t) == True{} : Bool}, +hg: {Lin.goods(t, W, k, a) == True{} : Bool}, +hp: {pok(pl, W, k, a) == True{} : Bool}) -> {Bool.and(M.invariant(M.attach(t, M.Node{M.Name{k, a}, it, pl, Nil{}})), Lin.goods(M.attach(t, M.Node{M.Name{k, a}, it, pl, Nil{}}), W, k, 1n+a)) == True{} : Bool}:
  match pl:
    case M.Place{+p, +r}:
      AL.and_intro(M.invariant(M.attach(t, M.Node{M.Name{k, a}, it, M.Place{p, r}, Nil{}})), Lin.goods(M.attach(t, M.Node{M.Name{k, a}, it, M.Place{p, r}, Nil{}}), W, k, 1n+a),
        invariant_leaf(t, M.Node{M.Name{k, a}, it, M.Place{p, r}, Nil{}}, p, r, {==}, Lin.fresh_of(t, W, k, a, hg), Lin.under_ne(p, W, k, a, hp), hi),
        Lin.goods_attach(t, M.Node{M.Name{k, a}, it, M.Place{p, r}, Nil{}}, W, k, 1n+a, good_leaf(k, a, it, M.Place{p, r}, W, hp), Lin.goods_mono(t, W, k, a, hg)))

# The event's actions, applied to the whole tree, keep the invariant and
# the bound.
def apply_ok(acts: List<&2, M.Action>, +t: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +lo: Nat, +hi: {M.invariant(t) == True{} : Bool}, +hg: {Lin.goods(t, W, k, lo) == True{} : Bool}, +ha: {aok(acts, W, k, lo) == True{} : Bool}) -> {Bool.and(M.invariant(M.apply(acts, t, k)), Lin.goods(M.apply(acts, t, k), W, k, mfin(acts, lo))) == True{} : Bool}:
  match acts:
    case Nil{}:
      AL.and_intro(M.invariant(t), Lin.goods(t, W, k, lo), hi, hg)
    case M.Attach{+a, +it, +pl} <> +rest:
      apply_ok(rest, M.attach(t, M.Node{M.Name{k, a}, it, pl, Nil{}}), W, k, 1n+a,
        Comp.and_left(M.invariant(M.attach(t, M.Node{M.Name{k, a}, it, pl, Nil{}})), Lin.goods(M.attach(t, M.Node{M.Name{k, a}, it, pl, Nil{}}), W, k, 1n+a), attach_ok(t, k, a, it, pl, W, hi, goods_le(t, W, k, lo, a, Comp.and_left(Nat.is_le(lo, a), Bool.and(pok(pl, W, k, a), aok(rest, W, k, 1n+a)), ha), hg), Comp.and_left(pok(pl, W, k, a), aok(rest, W, k, 1n+a), Comp.and_right(Nat.is_le(lo, a), Bool.and(pok(pl, W, k, a), aok(rest, W, k, 1n+a)), ha)))),
        Comp.and_right(M.invariant(M.attach(t, M.Node{M.Name{k, a}, it, pl, Nil{}})), Lin.goods(M.attach(t, M.Node{M.Name{k, a}, it, pl, Nil{}}), W, k, 1n+a), attach_ok(t, k, a, it, pl, W, hi, goods_le(t, W, k, lo, a, Comp.and_left(Nat.is_le(lo, a), Bool.and(pok(pl, W, k, a), aok(rest, W, k, 1n+a)), ha), hg), Comp.and_left(pok(pl, W, k, a), aok(rest, W, k, 1n+a), Comp.and_right(Nat.is_le(lo, a), Bool.and(pok(pl, W, k, a), aok(rest, W, k, 1n+a)), ha)))),
        Comp.and_right(pok(pl, W, k, a), aok(rest, W, k, 1n+a), Comp.and_right(Nat.is_le(lo, a), Bool.and(pok(pl, W, k, a), aok(rest, W, k, 1n+a)), ha)))
    case M.Delete{+tg} <> +rest:
      apply_ok(rest, M.mark(t, tg, k), W, k, lo, AL.invariant_mark(t, tg, k, hi), Lin.goods_mark(t, tg, k, W, k, lo, AL.or_left(Nat.is_eq(k, k), M.has(W, k), Comp.eq_refl(k)), hg), ha)

def aok_lower(b: List<&2, M.Action>, +W: List<&2, Nat>, +k: Nat, +l: Nat, +m: Nat, +le: {Nat.is_le(l, m) == True{} : Bool}, +h: {aok(b, W, k, m) == True{} : Bool}) -> {aok(b, W, k, l) == True{} : Bool}:
  match b:
    case Nil{}:
      {==}
    case M.Attach{+a, +it, +pl} <> +rest:
      AL.and_intro(Nat.is_le(l, a), Bool.and(pok(pl, W, k, a), aok(rest, W, k, 1n+a)),
        Lin.le_trans(l, m, a, le, Comp.and_left(Nat.is_le(m, a), Bool.and(pok(pl, W, k, a), aok(rest, W, k, 1n+a)), h)),
        Comp.and_right(Nat.is_le(m, a), Bool.and(pok(pl, W, k, a), aok(rest, W, k, 1n+a)), h))
    case M.Delete{tg} <> +rest:
      aok_lower(rest, W, k, l, m, le, h)

def aok_app(a: List<&2, M.Action>, +b: List<&2, M.Action>, +W: List<&2, Nat>, +k: Nat, +lo: Nat, +ha: {aok(a, W, k, lo) == True{} : Bool}, hb: {aok(b, W, k, mfin(a, lo)) == True{} : Bool}) -> {aok(List.append(&2, M.Action, a, b), W, k, lo) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case M.Attach{+x, +it, +pl} <> +rest:
      AL.and_intro(Nat.is_le(lo, x), Bool.and(pok(pl, W, k, x), aok(List.append(&2, M.Action, rest, b), W, k, 1n+x)),
        Comp.and_left(Nat.is_le(lo, x), Bool.and(pok(pl, W, k, x), aok(rest, W, k, 1n+x)), ha),
        AL.and_intro(pok(pl, W, k, x), aok(List.append(&2, M.Action, rest, b), W, k, 1n+x),
          Comp.and_left(pok(pl, W, k, x), aok(rest, W, k, 1n+x), Comp.and_right(Nat.is_le(lo, x), Bool.and(pok(pl, W, k, x), aok(rest, W, k, 1n+x)), ha)),
          aok_app(rest, b, W, k, 1n+x, Comp.and_right(pok(pl, W, k, x), aok(rest, W, k, 1n+x), Comp.and_right(Nat.is_le(lo, x), Bool.and(pok(pl, W, k, x), aok(rest, W, k, 1n+x)), ha)), hb)))
    case M.Delete{tg} <> +rest:
      aok_app(rest, b, W, k, lo, ha, hb)

def mfin_app(a: List<&2, M.Action>, +b: List<&2, M.Action>, +lo: Nat) -> {mfin(List.append(&2, M.Action, a, b), lo) == mfin(b, mfin(a, lo)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case M.Attach{+x, it, pl} <> rest:
      mfin_app(rest, b, 1n+x)
    case M.Delete{tg} <> rest:
      mfin_app(rest, b, lo)

def mfin_mono(b: List<&2, M.Action>, +l: Nat, +m: Nat, +le: {Nat.is_le(l, m) == True{} : Bool}) -> {Nat.is_le(mfin(b, l), mfin(b, m)) == True{} : Bool}:
  match b:
    case Nil{}:
      le
    case M.Attach{+x, it, pl} <> rest:
      Comp.le_refl(mfin(rest, 1n+x))
    case M.Delete{tg} <> rest:
      mfin_mono(rest, l, m, le)

# A delete's actions are deletes only.
def dels_only(acts: List<&2, M.Action>) -> Bool:
  match acts:
    case Nil{}:
      True{}
    case M.Attach{a, it, pl} <> rest:
      False{}
    case M.Delete{tg} <> rest:
      dels_only(rest)

def aok_dels(a: List<&2, M.Action>, +W: List<&2, Nat>, +k: Nat, +lo: Nat, +h: {dels_only(a) == True{} : Bool}) -> {aok(a, W, k, lo) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case M.Attach{x, it, pl} <> rest:
      Empty.absurd({aok(M.Attach{x, it, pl} <> rest, W, k, lo) == True{} : Bool}, Comp.false_true(h))
    case M.Delete{tg} <> rest:
      aok_dels(rest, W, k, lo, h)

def mfin_dels(a: List<&2, M.Action>, +lo: Nat, +h: {dels_only(a) == True{} : Bool}) -> {mfin(a, lo) == lo : Nat}:
  match a:
    case Nil{}:
      {==}
    case M.Attach{x, it, pl} <> rest:
      Empty.absurd({mfin(M.Attach{x, it, pl} <> rest, lo) == lo : Nat}, Comp.false_true(h))
    case M.Delete{tg} <> rest:
      mfin_dels(rest, lo, h)

def dmo(m: Maybe<&2, List<&2, M.Action>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{a}:
      dels_only(a)

def dels_agreed(+nm: M.Name, agreed: Bool, more: Maybe<&2, List<&2, M.Action>>, h: {dmo(more) == True{} : Bool}) -> {dmo(M.deletes.agreed(nm, more, agreed)) == True{} : Bool}:
  match agreed:
    case False{}:
      {==}
    case True{}:
      match more:
        case None{}:
          {==}
        case Some{a}:
          h

def dels_at(it: Ops.Item, more: Maybe<&2, List<&2, M.Action>>, found: Maybe<&2, M.Node>, h: {dmo(more) == True{} : Bool}) -> {dmo(M.deletes.at(it, more, found)) == True{} : Bool}:
  match found:
    case None{}:
      {==}
    case Some{M.Node{+nm, item, pl, d}}:
      dels_agreed(nm, Ops.agrees(it, item), more, h)

def deletes_dels(items: List<&2, Ops.Item>, +prepare: List<&2, M.Node>, +at: Nat) -> {dmo(M.deletes(items, prepare, at)) == True{} : Bool}:
  match items:
    case Nil{}:
      {==}
    case it <> +more:
      dels_at(it, M.deletes(more, prepare, 1n+at), List.get(&2, M.Node, prepare, at), deletes_dels(more, prepare, 1n+at))

# Names a view holds
# ------------------
#
# The elements a run counts positions in are all in its view, which only
# grows: so an insert's anchor is always a name the view holds.
def nv(xs: List<&2, M.Node>, +v: List<&2, M.Node>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(M.named(v, M.Node.name(x)), nv(rest, v))

def named_attach.at(+x: M.Node, +xs: List<&2, M.Node>, +n: M.Node, +nm: M.Name, lt: Bool, h: {M.named(x <> xs, nm) == True{} : Bool}, ih: {M.named(xs, nm) == True{} : Bool} -> {M.named(M.attach(xs, n), nm) == True{} : Bool}) -> {M.named(M.attach.put(n, x, xs, M.attach(xs, n), lt), nm) == True{} : Bool}:
  match lt:
    case True{}:
      AL.or_right(M.Name.eq(M.Node.name(n), nm), M.named(x <> xs, nm), h)
    case False{}:
      AL.or_cases({M.named(x <> M.attach(xs, n), nm) == True{} : Bool}, M.Name.eq(M.Node.name(x), nm), M.named(xs, nm), h,
        e => AL.or_left(M.Name.eq(M.Node.name(x), nm), M.named(M.attach(xs, n), nm), e),
        e => AL.or_right(M.Name.eq(M.Node.name(x), nm), M.named(M.attach(xs, n), nm), ih(e)))

def named_attach(v: List<&2, M.Node>, +n: M.Node, +nm: M.Name, h: {M.named(v, nm) == True{} : Bool}) -> {M.named(M.attach(v, n), nm) == True{} : Bool}:
  match v:
    case Nil{}:
      Empty.absurd({M.named([n], nm) == True{} : Bool}, Comp.false_true(h))
    case +x <> +xs:
      named_attach.at(x, xs, n, nm, Cmp.is_lt(M.Name.cmp(M.Node.name(n), M.Node.name(x))), h, e => named_attach(xs, n, nm, e))

def named_self.at(+x: M.Node, +xs: List<&2, M.Node>, +n: M.Node, lt: Bool, ih: {M.named(M.attach(xs, n), M.Node.name(n)) == True{} : Bool}) -> {M.named(M.attach.put(n, x, xs, M.attach(xs, n), lt), M.Node.name(n)) == True{} : Bool}:
  match lt:
    case True{}:
      AL.or_left(M.Name.eq(M.Node.name(n), M.Node.name(n)), M.named(x <> xs, M.Node.name(n)), AL.name_eq_refl(M.Node.name(n)))
    case False{}:
      AL.or_right(M.Name.eq(M.Node.name(x), M.Node.name(n)), M.named(M.attach(xs, n), M.Node.name(n)), ih)

def named_attach_self(v: List<&2, M.Node>, +n: M.Node) -> {M.named(M.attach(v, n), M.Node.name(n)) == True{} : Bool}:
  match v:
    case Nil{}:
      AL.or_left(M.Name.eq(M.Node.name(n), M.Node.name(n)), False{}, AL.name_eq_refl(M.Node.name(n)))
    case +x <> +xs:
      named_self.at(x, xs, n, Cmp.is_lt(M.Name.cmp(M.Node.name(n), M.Node.name(x))), named_attach_self(xs, n))

def nv_attach(P: List<&2, M.Node>, +v: List<&2, M.Node>, +n: M.Node, +h: {nv(P, v) == True{} : Bool}) -> {nv(P, M.attach(v, n)) == True{} : Bool}:
  match P:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(M.named(M.attach(v, n), M.Node.name(x)), nv(rest, M.attach(v, n)),
        named_attach(v, n, M.Node.name(x), Comp.and_left(M.named(v, M.Node.name(x)), nv(rest, v), h)),
        nv_attach(rest, v, n, Comp.and_right(M.named(v, M.Node.name(x)), nv(rest, v), h)))

def mnode_disc(m: Maybe<&2, M.Node>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

def nv_get(P: List<&2, M.Node>, +v: List<&2, M.Node>, i: Nat, +x: M.Node, +h: {nv(P, v) == True{} : Bool}, e: {List.get(&2, M.Node, P, i) == Some{x} : Maybe<&2, M.Node>}) -> {M.named(v, M.Node.name(x)) == True{} : Bool}:
  match P:
    case Nil{}:
      Empty.absurd({M.named(v, M.Node.name(x)) == True{} : Bool}, Comp.false_true(Equal.cong(Maybe<&2, M.Node>, Bool, m => mnode_disc(m), List.get(&2, M.Node, Nil{}, i), Some{x}, e)))
    case +y <> +ys:
      match i:
        case 0n:
          %ML.some_node(y, x, e) : {M.named(v, M.Node.name(_)) == True{} : Bool}
          Comp.and_left(M.named(v, M.Node.name(y)), nv(ys, v), h)
        case 1n+j:
          nv_get(ys, v, j, x, Comp.and_right(M.named(v, M.Node.name(y)), nv(ys, v), h), e)

def nv_weak(xs: List<&2, M.Node>, +y: M.Node, +ys: List<&2, M.Node>, +h: {nv(xs, ys) == True{} : Bool}) -> {nv(xs, y <> ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(M.named(y <> ys, M.Node.name(x)), nv(rest, y <> ys),
        AL.or_right(M.Name.eq(M.Node.name(y), M.Node.name(x)), M.named(ys, M.Node.name(x)), Comp.and_left(M.named(ys, M.Node.name(x)), nv(rest, ys), h)),
        nv_weak(rest, y, ys, Comp.and_right(M.named(ys, M.Node.name(x)), nv(rest, ys), h)))

def nv_self(v: List<&2, M.Node>) -> {nv(v, v) == True{} : Bool}:
  match v:
    case Nil{}:
      {==}
    case +x <> +xs:
      AL.and_intro(M.named(x <> xs, M.Node.name(x)), nv(xs, x <> xs),
        AL.or_left(M.Name.eq(M.Node.name(x), M.Node.name(x)), M.named(xs, M.Node.name(x)), AL.name_eq_refl(M.Node.name(x))),
        nv_weak(xs, x, xs, nv_self(xs)))

def nv_put(+x: M.Node, +xs: List<&2, M.Node>, +v: List<&2, M.Node>, b: Bool, hx: {M.named(v, M.Node.name(x)) == True{} : Bool}, h: {nv(xs, v) == True{} : Bool}) -> {nv(List.filter.put(M.Node, x, xs, b), v) == True{} : Bool}:
  match b:
    case True{}:
      AL.and_intro(M.named(v, M.Node.name(x)), nv(xs, v), hx, h)
    case False{}:
      h

def nv_children(t: List<&2, M.Node>, +q: Maybe<&2, M.Name>, +r: Bool, +v: List<&2, M.Node>, +h: {nv(t, v) == True{} : Bool}) -> {nv(M.children(t, q, r), v) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +x <> +xs:
      nv_put(x, M.children(xs, q, r), v, M.Node.hangs(x, q, r), Comp.and_left(M.named(v, M.Node.name(x)), nv(xs, v), h), nv_children(xs, q, r, v, Comp.and_right(M.named(v, M.Node.name(x)), nv(xs, v), h)))

def nv_append(a: List<&2, M.Node>, +b: List<&2, M.Node>, +v: List<&2, M.Node>, +ha: {nv(a, v) == True{} : Bool}, hb: {nv(b, v) == True{} : Bool}) -> {nv(List.append(&2, M.Node, a, b), v) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case +x <> +xs:
      AL.and_intro(M.named(v, M.Node.name(x)), nv(List.append(&2, M.Node, xs, b), v), Comp.and_left(M.named(v, M.Node.name(x)), nv(xs, v), ha), nv_append(xs, b, v, Comp.and_right(M.named(v, M.Node.name(x)), nv(xs, v), ha), hb))

def nv_read(f: Nat, +t: List<&2, M.Node>, L: List<&2, M.Node>, +ht: {nv(t, t) == True{} : Bool}, +hs: {nv(L, t) == True{} : Bool}) -> {nv(M.read_all(f, t, L), t) == True{} : Bool}:
  match f:
    case 0n:
      {==}
    case 1n++p:
      match L:
        case Nil{}:
          {==}
        case +s <> +rest:
          nv_append(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), t,
            nv_read(p, t, M.children(t, Some{M.Node.name(s)}, False{}), ht, nv_children(t, Some{M.Node.name(s)}, False{}, t, ht)),
            AL.and_intro(M.named(t, M.Node.name(s)), nv(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), t),
              Comp.and_left(M.named(t, M.Node.name(s)), nv(rest, t), hs),
              nv_append(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), t,
                nv_read(p, t, M.children(t, Some{M.Node.name(s)}, True{}), ht, nv_children(t, Some{M.Node.name(s)}, True{}, t, ht)),
                nv_read(p, t, rest, ht, Comp.and_right(M.named(t, M.Node.name(s)), nv(rest, t), hs)))))

def nv_standing(xs: List<&2, M.Node>, +v: List<&2, M.Node>, +h: {nv(xs, v) == True{} : Bool}) -> {nv(M.standing(xs), v) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      nv_put(x, M.standing(rest), v, M.Node.standing(x), Comp.and_left(M.named(v, M.Node.name(x)), nv(rest, v), h), nv_standing(rest, v, Comp.and_right(M.named(v, M.Node.name(x)), nv(rest, v), h)))

def nv_visible(+v: List<&2, M.Node>) -> {nv(M.visible(v), v) == True{} : Bool}:
  nv_standing(M.order(v), v, nv_read(1n+List.length(&2, M.Node, v), v, M.children(v, None{}, True{}), nv_self(v), nv_children(v, None{}, True{}, v, nv_self(v))))

# Where an insert anchors
# -----------------------

def ln(l: Maybe<&2, M.Name>, +v: List<&2, M.Node>) -> Bool:
  match l:
    case None{}:
      True{}
    case Some{nm}:
      M.named(v, nm)

def lokm(lm: Maybe<&2, Maybe<&2, M.Name>>, +v: List<&2, M.Node>) -> Bool:
  match lm:
    case None{}:
      True{}
    case Some{l}:
      ln(l, v)

def left_ok.at(+P: List<&2, M.Node>, +v: List<&2, M.Node>, +p: Nat, gm: Maybe<&2, M.Node>, eg: {List.get(&2, M.Node, P, p) == gm : Maybe<&2, M.Node>}, +h: {nv(P, v) == True{} : Bool}) -> {lokm(Maybe.map(&2, M.Node, Maybe<&2, M.Name>, x => Some{M.Node.name(x)}, gm), v) == True{} : Bool}:
  match gm:
    case None{}:
      {==}
    case Some{+x}:
      nv_get(P, v, p, x, h, eg)

def left_of_ok(+P: List<&2, M.Node>, +v: List<&2, M.Node>, at: Nat, +h: {nv(P, v) == True{} : Bool}) -> {lokm(M.left_of(P, at), v) == True{} : Bool}:
  match at:
    case 0n:
      {==}
    case 1n++p:
      left_ok.at(P, v, p, List.get(&2, M.Node, P, p), {==}, h)

def left_before(l: Maybe<&2, M.Name>, +v: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +m: Nat, +hg: {Lin.goods(v, W, k, m) == True{} : Bool}, hl: {ln(l, v) == True{} : Bool}) -> {Lin.before.m(l, W, k, m) == True{} : Bool}:
  match l:
    case None{}:
      {==}
    case Some{+nm}:
      Lin.named_before(v, nm, W, k, m, hg, hl)

def anchor_pok.of(+v: List<&2, M.Node>, +left: Maybe<&2, M.Name>, cs: List<&2, M.Node>, ecs: {M.children(v, left, True{}) == cs : List<&2, M.Node>}, +W: List<&2, Nat>, +k: Nat, +m: Nat, +hg: {Lin.goods(v, W, k, m) == True{} : Bool}, hl: {ln(left, v) == True{} : Bool}) -> {pok(M.anchor.of(v, left, cs), W, k, m) == True{} : Bool}:
  match cs:
    case Nil{}:
      left_before(left, v, W, k, m, hg, hl)
    case +c <> +more:
      Lin.named_before(v, M.leftmost(List.length(&2, M.Node, v), v, M.Node.name(c)), W, k, m, hg, AL.leftmost_named(List.length(&2, M.Node, v), v, M.Node.name(c), AL.children_named(v, left, True{}, M.Node.name(c), AL.head_named(v, left, True{}, c, more, ecs))))

# Fugue's anchor hangs the element under a name the view holds.
def anchor_pok(+v: List<&2, M.Node>, +left: Maybe<&2, M.Name>, +W: List<&2, Nat>, +k: Nat, +m: Nat, +hg: {Lin.goods(v, W, k, m) == True{} : Bool}, hl: {ln(left, v) == True{} : Bool}) -> {pok(M.anchor(v, left), W, k, m) == True{} : Bool}:
  anchor_pok.of(v, left, M.children(v, left, True{}), {==}, W, k, m, hg, hl)

# A run of inserted items
# -----------------------

def iok(r: M.Inserted, +P: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +m: Nat) -> Bool:
  match r:
    case M.Inserted{+v2, +acts, +m2}:
      Bool.and(Lin.goods(v2, W, k, m2), Bool.and(aok(acts, W, k, m), Bool.and(Nat.is_le(mfin(acts, m), m2), nv(P, v2))))

def iok_of(+m: Nat, +it: Ops.Item, +pl: M.Place, r: M.Inserted, +P: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +hp: {pok(pl, W, k, m) == True{} : Bool}, +h: {iok(r, P, W, k, 1n+m) == True{} : Bool}) -> {iok(M.inserts.of(m, it, pl, r), P, W, k, m) == True{} : Bool}:
  match r:
    case M.Inserted{+v2, +acts, +m2}:
      AL.and_intro(Lin.goods(v2, W, k, m2), Bool.and(aok(M.Attach{m, it, pl} <> acts, W, k, m), Bool.and(Nat.is_le(mfin(acts, 1n+m), m2), nv(P, v2))),
        Comp.and_left(Lin.goods(v2, W, k, m2), Bool.and(aok(acts, W, k, 1n+m), Bool.and(Nat.is_le(mfin(acts, 1n+m), m2), nv(P, v2))), h),
        AL.and_intro(aok(M.Attach{m, it, pl} <> acts, W, k, m), Bool.and(Nat.is_le(mfin(acts, 1n+m), m2), nv(P, v2)),
          AL.and_intro(Nat.is_le(m, m), Bool.and(pok(pl, W, k, m), aok(acts, W, k, 1n+m)), Comp.le_refl(m),
            AL.and_intro(pok(pl, W, k, m), aok(acts, W, k, 1n+m), hp, Comp.and_left(aok(acts, W, k, 1n+m), Bool.and(Nat.is_le(mfin(acts, 1n+m), m2), nv(P, v2)), Comp.and_right(Lin.goods(v2, W, k, m2), Bool.and(aok(acts, W, k, 1n+m), Bool.and(Nat.is_le(mfin(acts, 1n+m), m2), nv(P, v2))), h)))),
          Comp.and_right(aok(acts, W, k, 1n+m), Bool.and(Nat.is_le(mfin(acts, 1n+m), m2), nv(P, v2)), Comp.and_right(Lin.goods(v2, W, k, m2), Bool.and(aok(acts, W, k, 1n+m), Bool.and(Nat.is_le(mfin(acts, 1n+m), m2), nv(P, v2))), h))))

def ins_ok(items: List<&2, Ops.Item>, +v: List<&2, M.Node>, +k: Nat, +left: Maybe<&2, M.Name>, +m: Nat, +P: List<&2, M.Node>, +W: List<&2, Nat>, +hg: {Lin.goods(v, W, k, m) == True{} : Bool}, +hl: {ln(left, v) == True{} : Bool}, +hv: {nv(P, v) == True{} : Bool}) -> {iok(M.inserts(items, v, k, left, m), P, W, k, m) == True{} : Bool}:
  match items:
    case Nil{}:
      AL.and_intro(Lin.goods(v, W, k, m), Bool.and(True{}, Bool.and(Nat.is_le(m, m), nv(P, v))), hg, AL.and_intro(True{}, Bool.and(Nat.is_le(m, m), nv(P, v)), {==}, AL.and_intro(Nat.is_le(m, m), nv(P, v), Comp.le_refl(m), hv)))
    case +it <> +more:
      iok_of(m, it, M.anchor(v, left), M.inserts(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m), P, W, k,
        anchor_pok(v, left, W, k, m, hg, hl),
        ins_ok(more, M.attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}), k, Some{M.Name{k, m}}, 1n+m, P, W,
          Lin.goods_attach(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}, W, k, 1n+m, good_leaf(k, m, it, M.anchor(v, left), W, anchor_pok(v, left, W, k, m, hg, hl)), Lin.goods_mono(v, W, k, m, hg)),
          named_attach_self(v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}),
          nv_attach(P, v, M.Node{M.Name{k, m}, it, M.anchor(v, left), Nil{}}, hv)))

# A run
# -----
#
# Whatever the document: the view stays bounded by the event, its actions
# are ones `apply` can take, and the positions it counts stay in its view.
def rok(st: Maybe<&2, M.Running>, +P: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat) -> Bool:
  match st:
    case None{}:
      True{}
    case Some{M.Running{+v, +m, +acts}}:
      Bool.and(Lin.goods(v, W, k, m), Bool.and(aok(acts, W, k, 0n), Bool.and(Nat.is_le(mfin(acts, 0n), m), nv(P, v))))

def del_ok(+v: List<&2, M.Node>, +m: Nat, +acts: List<&2, M.Action>, new: Maybe<&2, List<&2, M.Action>>, +P: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +h: {rok(Some{M.Running{v, m, acts}}, P, W, k) == True{} : Bool}, +hd: {dmo(new) == True{} : Bool}) -> {rok(M.run.deleted(v, m, acts, new), P, W, k) == True{} : Bool}:
  match new:
    case None{}:
      {==}
    case Some{+a}:
      AL.and_intro(Lin.goods(v, W, k, m), Bool.and(aok(List.append(&2, M.Action, acts, a), W, k, 0n), Bool.and(Nat.is_le(mfin(List.append(&2, M.Action, acts, a), 0n), m), nv(P, v))),
        Comp.and_left(Lin.goods(v, W, k, m), Bool.and(aok(acts, W, k, 0n), Bool.and(Nat.is_le(mfin(acts, 0n), m), nv(P, v))), h),
        AL.and_intro(aok(List.append(&2, M.Action, acts, a), W, k, 0n), Bool.and(Nat.is_le(mfin(List.append(&2, M.Action, acts, a), 0n), m), nv(P, v)),
          aok_app(acts, a, W, k, 0n, Comp.and_left(aok(acts, W, k, 0n), Bool.and(Nat.is_le(mfin(acts, 0n), m), nv(P, v)), Comp.and_right(Lin.goods(v, W, k, m), Bool.and(aok(acts, W, k, 0n), Bool.and(Nat.is_le(mfin(acts, 0n), m), nv(P, v))), h)), aok_dels(a, W, k, mfin(acts, 0n), hd)),
          AL.and_intro(Nat.is_le(mfin(List.append(&2, M.Action, acts, a), 0n), m), nv(P, v),
            Equal.trans(Bool, Nat.is_le(mfin(List.append(&2, M.Action, acts, a), 0n), m), Nat.is_le(mfin(acts, 0n), m), True{},
              Equal.cong(Nat, Bool, l => Nat.is_le(l, m), mfin(List.append(&2, M.Action, acts, a), 0n), mfin(acts, 0n), Equal.trans(Nat, mfin(List.append(&2, M.Action, acts, a), 0n), mfin(a, mfin(acts, 0n)), mfin(acts, 0n), mfin_app(acts, a, 0n), mfin_dels(a, mfin(acts, 0n), hd))),
              Comp.and_left(Nat.is_le(mfin(acts, 0n), m), nv(P, v), Comp.and_right(aok(acts, W, k, 0n), Bool.and(Nat.is_le(mfin(acts, 0n), m), nv(P, v)), Comp.and_right(Lin.goods(v, W, k, m), Bool.and(aok(acts, W, k, 0n), Bool.and(Nat.is_le(mfin(acts, 0n), m), nv(P, v))), h)))),
            Comp.and_right(Nat.is_le(mfin(acts, 0n), m), nv(P, v), Comp.and_right(aok(acts, W, k, 0n), Bool.and(Nat.is_le(mfin(acts, 0n), m), nv(P, v)), Comp.and_right(Lin.goods(v, W, k, m), Bool.and(aok(acts, W, k, 0n), Bool.and(Nat.is_le(mfin(acts, 0n), m), nv(P, v))), h))))))

def inserted_ok(+acts: List<&2, M.Action>, r: M.Inserted, +P: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +m: Nat, +ha: {aok(acts, W, k, 0n) == True{} : Bool}, +hle: {Nat.is_le(mfin(acts, 0n), m) == True{} : Bool}, +hi: {iok(r, P, W, k, m) == True{} : Bool}) -> {rok(M.run.inserted(acts, r), P, W, k) == True{} : Bool}:
  match r:
    case M.Inserted{+v2, +new, +m2}:
      AL.and_intro(Lin.goods(v2, W, k, m2), Bool.and(aok(List.append(&2, M.Action, acts, new), W, k, 0n), Bool.and(Nat.is_le(mfin(List.append(&2, M.Action, acts, new), 0n), m2), nv(P, v2))),
        Comp.and_left(Lin.goods(v2, W, k, m2), Bool.and(aok(new, W, k, m), Bool.and(Nat.is_le(mfin(new, m), m2), nv(P, v2))), hi),
        AL.and_intro(aok(List.append(&2, M.Action, acts, new), W, k, 0n), Bool.and(Nat.is_le(mfin(List.append(&2, M.Action, acts, new), 0n), m2), nv(P, v2)),
          aok_app(acts, new, W, k, 0n, ha, aok_lower(new, W, k, mfin(acts, 0n), m, hle, Comp.and_left(aok(new, W, k, m), Bool.and(Nat.is_le(mfin(new, m), m2), nv(P, v2)), Comp.and_right(Lin.goods(v2, W, k, m2), Bool.and(aok(new, W, k, m), Bool.and(Nat.is_le(mfin(new, m), m2), nv(P, v2))), hi)))),
          AL.and_intro(Nat.is_le(mfin(List.append(&2, M.Action, acts, new), 0n), m2), nv(P, v2),
            Equal.trans(Bool, Nat.is_le(mfin(List.append(&2, M.Action, acts, new), 0n), m2), Nat.is_le(mfin(new, mfin(acts, 0n)), m2), True{},
              Equal.cong(Nat, Bool, l => Nat.is_le(l, m2), mfin(List.append(&2, M.Action, acts, new), 0n), mfin(new, mfin(acts, 0n)), mfin_app(acts, new, 0n)),
              Lin.le_trans(mfin(new, mfin(acts, 0n)), mfin(new, m), m2, mfin_mono(new, mfin(acts, 0n), m, hle), Comp.and_left(Nat.is_le(mfin(new, m), m2), nv(P, v2), Comp.and_right(aok(new, W, k, m), Bool.and(Nat.is_le(mfin(new, m), m2), nv(P, v2)), Comp.and_right(Lin.goods(v2, W, k, m2), Bool.and(aok(new, W, k, m), Bool.and(Nat.is_le(mfin(new, m), m2), nv(P, v2))), hi))))),
            Comp.and_right(Nat.is_le(mfin(new, m), m2), nv(P, v2), Comp.and_right(aok(new, W, k, m), Bool.and(Nat.is_le(mfin(new, m), m2), nv(P, v2)), Comp.and_right(Lin.goods(v2, W, k, m2), Bool.and(aok(new, W, k, m), Bool.and(Nat.is_le(mfin(new, m), m2), nv(P, v2))), hi))))))

def ins_step_ok(+items: List<&2, Ops.Item>, +v: List<&2, M.Node>, +k: Nat, +m: Nat, +acts: List<&2, M.Action>, left: Maybe<&2, Maybe<&2, M.Name>>, +P: List<&2, M.Node>, +W: List<&2, Nat>, +h: {rok(Some{M.Running{v, m, acts}}, P, W, k) == True{} : Bool}, hl: {lokm(left, v) == True{} : Bool}) -> {rok(M.run.insert(items, v, k, m, acts, left), P, W, k) == True{} : Bool}:
  match left:
    case None{}:
      {==}
    case Some{+l}:
      inserted_ok(acts, M.inserts(items, v, k, l, m), P, W, k, m,
        Comp.and_left(aok(acts, W, k, 0n), Bool.and(Nat.is_le(mfin(acts, 0n), m), nv(P, v)), Comp.and_right(Lin.goods(v, W, k, m), Bool.and(aok(acts, W, k, 0n), Bool.and(Nat.is_le(mfin(acts, 0n), m), nv(P, v))), h)),
        Comp.and_left(Nat.is_le(mfin(acts, 0n), m), nv(P, v), Comp.and_right(aok(acts, W, k, 0n), Bool.and(Nat.is_le(mfin(acts, 0n), m), nv(P, v)), Comp.and_right(Lin.goods(v, W, k, m), Bool.and(aok(acts, W, k, 0n), Bool.and(Nat.is_le(mfin(acts, 0n), m), nv(P, v))), h))),
        ins_ok(items, v, k, l, m, P, W,
          Comp.and_left(Lin.goods(v, W, k, m), Bool.and(aok(acts, W, k, 0n), Bool.and(Nat.is_le(mfin(acts, 0n), m), nv(P, v))), h),
          hl,
          Comp.and_right(Nat.is_le(mfin(acts, 0n), m), nv(P, v), Comp.and_right(aok(acts, W, k, 0n), Bool.and(Nat.is_le(mfin(acts, 0n), m), nv(P, v)), Comp.and_right(Lin.goods(v, W, k, m), Bool.and(aok(acts, W, k, 0n), Bool.and(Nat.is_le(mfin(acts, 0n), m), nv(P, v))), h)))))

def step_ok(st: Maybe<&2, M.Running>, op: Ops.Op, +k: Nat, +P: List<&2, M.Node>, +W: List<&2, Nat>, +h: {rok(st, P, W, k) == True{} : Bool}) -> {rok(M.run.step(st, op, k, P), P, W, k) == True{} : Bool}:
  match st:
    case None{}:
      {==}
    case Some{M.Running{+v, +m, +acts}}:
      match op:
        case Ops.Op{Ops.Delete{}, +at, +items}:
          del_ok(v, m, acts, M.deletes(items, P, at), P, W, k, h, deletes_dels(items, P, at))
        case Ops.Op{Ops.Insert{}, +at, +items}:
          ins_step_ok(items, v, k, m, acts, M.left_of(P, at), P, W, h, left_of_ok(P, v, at, Comp.and_right(Nat.is_le(mfin(acts, 0n), m), nv(P, v), Comp.and_right(aok(acts, W, k, 0n), Bool.and(Nat.is_le(mfin(acts, 0n), m), nv(P, v)), Comp.and_right(Lin.goods(v, W, k, m), Bool.and(aok(acts, W, k, 0n), Bool.and(Nat.is_le(mfin(acts, 0n), m), nv(P, v))), h)))))

def run_ok(ops: List<&2, Ops.Op>, +st: Maybe<&2, M.Running>, +k: Nat, +P: List<&2, M.Node>, +W: List<&2, Nat>, h: {rok(st, P, W, k) == True{} : Bool}) -> {rok(M.run(ops, st, k, P), P, W, k) == True{} : Bool}:
  match ops:
    case Nil{}:
      h
    case +op <> rest:
      run_ok(rest, M.run.step(st, op, k, P), k, P, W, step_ok(st, op, k, P, W, h))

# A view restricted from a bounded tree is bounded.
def keep.at(+y: Nat, +r: List<&2, Nat>, +V: List<&2, Nat>, b: Bool, hy: {M.has(V, y) == True{} : Bool}, h: {Lin.all_has(r, V) == True{} : Bool}) -> {Lin.all_has(List.filter.put(Nat, y, r, b), V) == True{} : Bool}:
  match b:
    case True{}:
      AL.and_intro(M.has(V, y), Lin.all_has(r, V), hy, h)
    case False{}:
      h

def all_has_keep(d: List<&2, Nat>, +S: List<&2, Nat>, +V: List<&2, Nat>, +h: {Lin.all_has(d, V) == True{} : Bool}) -> {Lin.all_has(M.keep(d, S), V) == True{} : Bool}:
  match d:
    case Nil{}:
      {==}
    case +y <> +ys:
      keep.at(y, M.keep(ys, S), V, M.has(S, y), Comp.and_left(M.has(V, y), Lin.all_has(ys, V), h), all_has_keep(ys, S, V, Comp.and_right(M.has(V, y), Lin.all_has(ys, V), h)))

# An event's view is bounded
# --------------------------

def good_restrict(x: M.Node, +S: List<&2, Nat>, +W: List<&2, Nat>, +k: Nat, +m: Nat, +h: {Lin.good(x, W, k, m) == True{} : Bool}) -> {Lin.good(M.Node.restrict(x, S), W, k, m) == True{} : Bool}:
  match x:
    case M.Node{+nm, +it, M.Place{+p, +r}, +d}:
      AL.and_intro(Lin.before(nm, W, k, m), Bool.and(Lin.before.m(p, W, k, m), Lin.all_has(M.keep(d, S), k <> W)),
        Comp.and_left(Lin.before(nm, W, k, m), Bool.and(Lin.before.m(p, W, k, m), Lin.all_has(d, k <> W)), h),
        AL.and_intro(Lin.before.m(p, W, k, m), Lin.all_has(M.keep(d, S), k <> W),
          Comp.and_left(Lin.before.m(p, W, k, m), Lin.all_has(d, k <> W), Comp.and_right(Lin.before(nm, W, k, m), Bool.and(Lin.before.m(p, W, k, m), Lin.all_has(d, k <> W)), h)),
          all_has_keep(d, S, k <> W, Comp.and_right(Lin.before.m(p, W, k, m), Lin.all_has(d, k <> W), Comp.and_right(Lin.before(nm, W, k, m), Bool.and(Lin.before.m(p, W, k, m), Lin.all_has(d, k <> W)), h)))))

def gput(+x: M.Node, +r: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +m: Nat, b: Bool, hx: {Lin.good(x, W, k, m) == True{} : Bool}, hr: {Lin.goods(r, W, k, m) == True{} : Bool}) -> {Lin.goods(List.filter.put(M.Node, x, r, b), W, k, m) == True{} : Bool}:
  match b:
    case True{}:
      AL.and_intro(Lin.good(x, W, k, m), Lin.goods(r, W, k, m), hx, hr)
    case False{}:
      hr

def goods_restrict(t: List<&2, M.Node>, +S: List<&2, Nat>, +W: List<&2, Nat>, +k: Nat, +m: Nat, +h: {Lin.goods(t, W, k, m) == True{} : Bool}) -> {Lin.goods(M.restrict(t, S), W, k, m) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +x <> +xs:
      gput(M.Node.restrict(x, S), M.restrict(xs, S), W, k, m, M.has(S, M.Node.author(x)),
        good_restrict(x, S, W, k, m, Comp.and_left(Lin.good(x, W, k, m), Lin.goods(xs, W, k, m), h)),
        goods_restrict(xs, S, W, k, m, Comp.and_right(Lin.good(x, W, k, m), Lin.goods(xs, W, k, m), h)))

def start_ok(+v: List<&2, M.Node>, +W: List<&2, Nat>, +k: Nat, +hg: {Lin.goods(v, W, k, 0n) == True{} : Bool}) -> {rok(Some{M.Running{v, 0n, Nil{}}}, M.visible(v), W, k) == True{} : Bool}:
  AL.and_intro(Lin.goods(v, W, k, 0n), Bool.and(True{}, Bool.and(Nat.is_le(0n, 0n), nv(M.visible(v), v))), hg,
    AL.and_intro(True{}, Bool.and(Nat.is_le(0n, 0n), nv(M.visible(v), v)), {==},
      AL.and_intro(Nat.is_le(0n, 0n), nv(M.visible(v), v), Comp.le_refl(0n), nv_visible(v))))

# The walk
# --------
#
# Every tree a walk builds keeps the invariant, and every name, parent and
# removal in it is by an event the walk has passed. Nothing about the
# graph is needed but that the order names each event once.
def wok(mt: Maybe<&2, List<&2, M.Node>>, +E: List<&2, Nat>) -> Bool:
  match mt:
    case None{}:
      True{}
    case Some{+t}:
      Bool.and(M.invariant(t), Lin.inw(t, E))

def revapp(o: List<&2, Nat>, E: List<&2, Nat>) -> List<&2, Nat>:
  match o:
    case Nil{}:
      E
    case x <> xs:
      revapp(xs, x <> E)

def fin_ok(st: Maybe<&2, M.Running>, +t: List<&2, M.Node>, +x: Nat, +E: List<&2, Nat>, +P: List<&2, M.Node>, +hr: {rok(st, P, E, x) == True{} : Bool}, +hi: {M.invariant(t) == True{} : Bool}, +hg: {Lin.goods(t, E, x, 0n) == True{} : Bool}) -> {wok(M.step.of(t, x, M.run.acts(st)), x <> E) == True{} : Bool}:
  match st:
    case None{}:
      {==}
    case Some{M.Running{+v, +m, +acts}}:
      AL.and_intro(M.invariant(M.apply(acts, t, x)), Lin.inw(M.apply(acts, t, x), x <> E),
        Comp.and_left(M.invariant(M.apply(acts, t, x)), Lin.goods(M.apply(acts, t, x), E, x, mfin(acts, 0n)), apply_ok(acts, t, E, x, 0n, hi, hg, Comp.and_left(aok(acts, E, x, 0n), Bool.and(Nat.is_le(mfin(acts, 0n), m), nv(P, v)), Comp.and_right(Lin.goods(v, E, x, m), Bool.and(aok(acts, E, x, 0n), Bool.and(Nat.is_le(mfin(acts, 0n), m), nv(P, v))), hr)))),
        Lin.goods_inw(M.apply(acts, t, x), E, x, mfin(acts, 0n), Comp.and_right(M.invariant(M.apply(acts, t, x)), Lin.goods(M.apply(acts, t, x), E, x, mfin(acts, 0n)), apply_ok(acts, t, E, x, 0n, hi, hg, Comp.and_left(aok(acts, E, x, 0n), Bool.and(Nat.is_le(mfin(acts, 0n), m), nv(P, v)), Comp.and_right(Lin.goods(v, E, x, m), Bool.and(aok(acts, E, x, 0n), Bool.and(Nat.is_le(mfin(acts, 0n), m), nv(P, v))), hr))))))

def subset_refl_n(a: List<&2, Nat>) -> {M.subset(a, a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case +x <> +xs:
      AL.and_intro(M.has(x <> xs, x), M.subset(xs, x <> xs),
        AL.or_left(Nat.is_eq(x, x), M.has(xs, x), Comp.eq_refl(x)),
        Lin.subset_weak(xs, xs, x, subset_refl_n(xs)))

# One event: whatever it states, the tree it leaves keeps the invariant.
def ev_ok(ev: Maybe<&2, M.Rev>, +t: List<&2, M.Node>, +x: Nat, +E: List<&2, Nat>, +hi: {M.invariant(t) == True{} : Bool}, +hn: {Lin.inw(t, E) == True{} : Bool}, +hk: {M.has(E, x) == False{} : Bool}) -> {wok(M.step(ev, t, x), x <> E) == True{} : Bool}:
  match ev:
    case None{}:
      {==}
    case Some{M.Rev{seen, None{}}}:
      AL.and_intro(M.invariant(t), Lin.inw(t, x <> E), hi, Lin.inw_sub(t, E, x <> E, Lin.subset_weak(E, E, x, subset_refl_n(E)), hn))
    case Some{M.Rev{+seen, Some{+ops}}}:
      fin_ok(M.run(ops, Some{M.Running{M.restrict(t, seen), 0n, Nil{}}}, x, M.visible(M.restrict(t, seen))), t, x, E, M.visible(M.restrict(t, seen)),
        run_ok(ops, Some{M.Running{M.restrict(t, seen), 0n, Nil{}}}, x, M.visible(M.restrict(t, seen)), E, start_ok(M.restrict(t, seen), E, x, goods_restrict(t, seen, E, x, 0n, Lin.inw_goods(t, E, x, hk, hn)))),
        hi, Lin.inw_goods(t, E, x, hk, hn))

def walk_none(o: List<&2, Nat>, +g: List<&2, M.Rev>) -> {M.walk(o, g, None{}) == None{} : Maybe<&2, List<&2, M.Node>>}:
  match o:
    case Nil{}:
      {==}
    case +e <> +rest:
      walk_none(rest, g)

def walk_step(+rest: List<&2, Nat>, +g: List<&2, M.Rev>, +x: Nat, +E: List<&2, Nat>, mt: Maybe<&2, List<&2, M.Node>>, +h: {wok(mt, x <> E) == True{} : Bool}, ih: @u: List<&2, M.Node> -> {M.invariant(u) == True{} : Bool} -> {Lin.inw(u, x <> E) == True{} : Bool} -> {wok(M.walk(rest, g, Some{u}), revapp(rest, x <> E)) == True{} : Bool}) -> {wok(M.walk(rest, g, mt), revapp(rest, x <> E)) == True{} : Bool}:
  match mt:
    case None{}:
      %Equal.sym(Maybe<&2, List<&2, M.Node>>, M.walk(rest, g, None{}), None{}, walk_none(rest, g)) : {wok(_, revapp(rest, x <> E)) == True{} : Bool}
      {==}
    case Some{+u}:
      ih(u, Comp.and_left(M.invariant(u), Lin.inw(u, x <> E), h), Comp.and_right(M.invariant(u), Lin.inw(u, x <> E), h))

def nk_cons(+E: List<&2, Nat>, +x: Nat, rest: List<&2, Nat>, +h1: {M.none_known(E, rest) == True{} : Bool}, +h2: {M.has(rest, x) == False{} : Bool}) -> {M.none_known(x <> E, rest) == True{} : Bool}:
  match rest:
    case Nil{}:
      {==}
    case +y <> +ys:
      AL.and_intro(Bool.not(M.has(x <> E, y)), M.none_known(x <> E, ys),
        AL.not_true(M.has(x <> E, y), AL.or_false(Nat.is_eq(x, y), M.has(E, y), ML.ne_sym(y, x, AL.or_false_l(Nat.is_eq(y, x), M.has(ys, x), h2)), AL.not_of_true(M.has(E, y), Comp.and_left(Bool.not(M.has(E, y)), M.none_known(E, ys), h1)))),
        nk_cons(E, x, ys, Comp.and_right(Bool.not(M.has(E, y)), M.none_known(E, ys), h1), AL.or_false_r(Nat.is_eq(y, x), M.has(ys, x), h2)))

def nk_nil(o: List<&2, Nat>) -> {M.none_known(Nil{}, o) == True{} : Bool}:
  match o:
    case Nil{}:
      {==}
    case y <> ys:
      AL.and_intro(True{}, M.none_known(Nil{}, ys), {==}, nk_nil(ys))

# Any order naming each event once builds trees that keep the invariant.
def walk_ok(o: List<&2, Nat>, +g: List<&2, M.Rev>, +t: List<&2, M.Node>, +E: List<&2, Nat>, +hi: {M.invariant(t) == True{} : Bool}, +hn: {Lin.inw(t, E) == True{} : Bool}, +hd: {M.distinct(o) == True{} : Bool}, +hk: {M.none_known(E, o) == True{} : Bool}) -> {wok(M.walk(o, g, Some{t}), revapp(o, E)) == True{} : Bool}:
  match o:
    case Nil{}:
      AL.and_intro(M.invariant(t), Lin.inw(t, E), hi, hn)
    case +x <> +rest:
      walk_step(rest, g, x, E, M.step(List.get(&2, M.Rev, g, x), t, x),
        ev_ok(List.get(&2, M.Rev, g, x), t, x, E, hi, hn, AL.not_of_true(M.has(E, x), Comp.and_left(Bool.not(M.has(E, x)), M.none_known(E, rest), hk))),
        u => h1 => h2 => walk_ok(rest, g, u, x <> E, h1, h2, Comp.and_right(Bool.not(M.has(rest, x)), M.distinct(rest), hd), nk_cons(E, x, rest, Comp.and_right(Bool.not(M.has(E, x)), M.none_known(E, rest), hk), AL.not_of_true(M.has(rest, x), Comp.and_left(Bool.not(M.has(rest, x)), M.distinct(rest), hd)))))

def subset_revapp(o: List<&2, Nat>, +E: List<&2, Nat>, +S: List<&2, Nat>, +h1: {M.subset(o, S) == True{} : Bool}, +h2: {M.subset(E, S) == True{} : Bool}) -> {M.subset(revapp(o, E), S) == True{} : Bool}:
  match o:
    case Nil{}:
      h2
    case +x <> +xs:
      subset_revapp(xs, x <> E, S, Comp.and_right(M.has(S, x), M.subset(xs, S), h1), AL.and_intro(M.has(S, x), M.subset(E, S), Comp.and_left(M.has(S, x), M.subset(xs, S), h1), h2))

def has_revapp_false(o: List<&2, Nat>, +E: List<&2, Nat>, +y: Nat, +h1: {M.has(o, y) == False{} : Bool}, +h2: {M.has(E, y) == False{} : Bool}) -> {M.has(revapp(o, E), y) == False{} : Bool}:
  match o:
    case Nil{}:
      h2
    case +x <> +xs:
      has_revapp_false(xs, x <> E, y, AL.or_false_r(Nat.is_eq(x, y), M.has(xs, y), h1), AL.or_false(Nat.is_eq(x, y), M.has(E, y), AL.or_false_l(Nat.is_eq(x, y), M.has(xs, y), h1), h2))

# An event that had seen everything walked
# ----------------------------------------
#
# Its view is the whole tree, which keeps the invariant however concurrent
# the history that built it; so its run is the cursor walk `linear_lemmas`
# simulates, and it leaves what plain application of its document leaves.
def fine_merged(st: Maybe<&2, M.Running>, +t: List<&2, M.Node>, +W: List<&2, Nat>, +e: Nat, +f: List<&2, Ops.Item>, h: {Lin.fine(st, t, W, e, f) == True{} : Bool}) -> {M.merged.of(M.step.of(t, e, M.run.acts(st))) == Some{f} : Maybe<&2, List<&2, Ops.Item>>}:
  match st:
    case None{}:
      Empty.absurd({M.merged.of(None{}) == Some{f} : Maybe<&2, List<&2, Ops.Item>>}, Comp.false_true(h))
    case Some{M.Running{v, m, +acts}}:
      Equal.cong(List<&2, Ops.Item>, Maybe<&2, List<&2, Ops.Item>>, x => Some{x}, M.file(M.apply(acts, t, e)), f,
        Lin.items_eq_equal(M.file(M.apply(acts, t, e)), f, Comp.and_right(Lin.inw(M.apply(acts, t, e), e <> W), Lin.items_eq(M.file(M.apply(acts, t, e)), f), Comp.and_right(M.invariant(M.apply(acts, t, e)), Bool.and(Lin.inw(M.apply(acts, t, e), e <> W), Lin.items_eq(M.file(M.apply(acts, t, e)), f)), h))))

def event_c(+t: List<&2, M.Node>, +W: List<&2, Nat>, +e: Nat, +past: List<&2, Nat>, +d: List<&2, Ops.Op>, +f1: List<&2, Ops.Item>, +hi: {M.invariant(t) == True{} : Bool}, +hn: {Lin.inw(t, W) == True{} : Bool}, +hk: {M.has(W, e) == False{} : Bool}, +hs: {M.subset(W, past) == True{} : Bool}, +ho: {Block.ordered_all(d, None{}, None{}) == True{} : Bool}, +ha: {Cursor.apply(M.file(t), Ops.Doc{None{}, None{}, d}) == Done{f1} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {M.merged.of(M.step(Some{M.Rev{past, Some{d}}}, t, e)) == Some{f1} : Maybe<&2, List<&2, Ops.Item>>}:
  %Equal.sym(List<&2, M.Node>, M.restrict(t, past), t, Lin.restrict_id(t, past, Lin.inw_sub(t, W, past, hs, hn))) : {M.merged.of(M.step.of(t, e, M.run.acts(M.run(d, Some{M.Running{_, 0n, Nil{}}}, e, M.visible(_))))) == Some{f1} : Maybe<&2, List<&2, Ops.Item>>}
  fine_merged(M.run(d, Some{M.Running{t, 0n, Nil{}}}, e, M.visible(t)), t, W, e, f1,
    (%Lin.restrict_id(t, W, hn) : {Lin.fine(M.run(d, Some{M.Running{_, 0n, Nil{}}}, e, M.visible(_)), t, W, e, f1) == True{} : Bool}
      Lin.step_fine(t, W, e, d, f1, hi, hn, hk,
        Lin.parser_strict(d, None{}, None{}, 0n, True{}, ho, Lin.rep_none(d), v => x => its => h1 => h2 => h3 => PL.le_zero(x)),
        (%Lin.len_file(M.visible(t)) : {Ops.in_range(d, _) == True{} : Bool}
          Lin.checked_range(Ops.in_range(d, List.length(&2, Ops.Item, M.file(t))), Cursor.walk(d, 0n, M.file(t)), f1, ha)),
        Lin.checked_walk(Cursor.walk(d, 0n, M.file(t)), f1, (%Lin.checked_range(Ops.in_range(d, List.length(&2, Ops.Item, M.file(t))), Cursor.walk(d, 0n, M.file(t)), f1, ha) : {Cursor.checked(_, None{}, Cursor.walk(d, 0n, M.file(t))) == Done{f1} : Result<&2, &2, String, List<&2, Ops.Item>>}
          ha)))))

def mitems(m: Maybe<&2, List<&2, Ops.Item>>) -> List<&2, Ops.Item>:
  match m:
    case None{}:
      Nil{}
    case Some{x}:
      x

def mis(m: Maybe<&2, List<&2, Ops.Item>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

def final_at(mt: Maybe<&2, List<&2, M.Node>>, +e: Nat, +past: List<&2, Nat>, +d: List<&2, Ops.Op>, -f0: List<&2, Ops.Item>, +f1: List<&2, Ops.Item>, +W: List<&2, Nat>, +hw: {wok(mt, W) == True{} : Bool}, +hk: {M.has(W, e) == False{} : Bool}, +hs: {M.subset(W, past) == True{} : Bool}, +ho: {Block.ordered_all(d, None{}, None{}) == True{} : Bool}, hm: {M.merged.of(mt) == Some{f0} : Maybe<&2, List<&2, Ops.Item>>}, +ha: {Cursor.apply(f0, Ops.Doc{None{}, None{}, d}) == Done{f1} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {M.merged.of(M.step.m(mt, Some{M.Rev{past, Some{d}}}, e)) == Some{f1} : Maybe<&2, List<&2, Ops.Item>>}:
  match mt:
    case None{}:
      Empty.absurd({M.merged.of(None{}) == Some{f1} : Maybe<&2, List<&2, Ops.Item>>}, Comp.false_true(Equal.cong(Maybe<&2, List<&2, Ops.Item>>, Bool, x => mis(x), None{}, Some{f0}, hm)))
    case Some{+t}:
      event_c(t, W, e, past, d, f1, Comp.and_left(M.invariant(t), Lin.inw(t, W), hw), Comp.and_right(M.invariant(t), Lin.inw(t, W), hw), hk, hs, ho,
        (%Equal.sym(List<&2, Ops.Item>, M.file(t), f0, Equal.cong(Maybe<&2, List<&2, Ops.Item>>, List<&2, Ops.Item>, x => mitems(x), Some{M.file(t)}, Some{f0}, hm)) : {Cursor.apply(_, Ops.Doc{None{}, None{}, d}) == Done{f1} : Result<&2, &2, String, List<&2, Ops.Item>>}
          ha))

# Every tree a walk builds keeps the invariant.
def walk_invariant_c(+g: List<&2, M.Rev>, +o: List<&2, Nat>, +t: List<&2, M.Node>, +hd: {M.distinct(o) == True{} : Bool}, e: {M.walk(o, g, Some{Nil{}}) == Some{t} : Maybe<&2, List<&2, M.Node>>}) -> {M.invariant(t) == True{} : Bool}:
  Comp.and_left(M.invariant(t), Lin.inw(t, revapp(o, Nil{})),
    (%e : {wok(_, revapp(o, Nil{})) == True{} : Bool}
      walk_ok(o, g, Nil{}, Nil{}, AL.invariant_nil(), {==}, hd, nk_nil(o))))


# The theorem: a history that walks to `f0`, extended by an event that had
# seen every event of it and states a document the parser would accept,
# walks to what applying that document to `f0` leaves.
def merge_extends_c(+g: List<&2, M.Rev>, +p: List<&2, Nat>, +e: Nat, +past: List<&2, Nat>, +d: List<&2, Ops.Op>, -f0: List<&2, Ops.Item>, +f1: List<&2, Ops.Item>, +hd: {M.distinct(p) == True{} : Bool}, +he: {M.has(p, e) == False{} : Bool}, +hs: {M.subset(p, past) == True{} : Bool}, +hg: {List.get(&2, M.Rev, g, e) == Some{M.Rev{past, Some{d}}} : Maybe<&2, M.Rev>}, +ho: {Block.ordered_all(d, None{}, None{}) == True{} : Bool}, +hm: {M.merged(g, p) == Some{f0} : Maybe<&2, List<&2, Ops.Item>>}, +ha: {Cursor.apply(f0, Ops.Doc{None{}, None{}, d}) == Done{f1} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {M.merged(g, List.append(&2, Nat, p, [e])) == Some{f1} : Maybe<&2, List<&2, Ops.Item>>}:
  %Equal.sym(Maybe<&2, List<&2, M.Node>>, M.walk(List.append(&2, Nat, p, [e]), g, Some{Nil{}}), M.step.m(M.walk(p, g, Some{Nil{}}), List.get(&2, M.Rev, g, e), e), ML.walk_append(p, e, g, Some{Nil{}})) : {M.merged.of(_) == Some{f1} : Maybe<&2, List<&2, Ops.Item>>}
  %Equal.sym(Maybe<&2, M.Rev>, List.get(&2, M.Rev, g, e), Some{M.Rev{past, Some{d}}}, hg) : {M.merged.of(M.step.m(M.walk(p, g, Some{Nil{}}), _, e)) == Some{f1} : Maybe<&2, List<&2, Ops.Item>>}
  final_at(M.walk(p, g, Some{Nil{}}), e, past, d, f0, f1, revapp(p, Nil{}),
    walk_ok(p, g, Nil{}, Nil{}, AL.invariant_nil(), {==}, hd, nk_nil(p)),
    has_revapp_false(p, Nil{}, e, he, {==}),
    subset_revapp(p, Nil{}, past, hs, {==}),
    ho, hm, ha)

def main() -> Unit:
  Unit{}
