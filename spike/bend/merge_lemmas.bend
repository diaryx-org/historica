# The merge converges: a graph's events replayed in any two causal orders
# build one tree. The argument is the one `merge.bend` is shaped for — an
# event's actions are decided on a view later events cannot alter, and the
# actions of two events that had not seen each other commute on the
# name-ordered tree — followed by a bubble sort: any causal order is the
# other with concurrent neighbours swapped.
import Base
import ./ops.bend as Ops
import ./merge.bend as M
import ./composition_lemmas.bend as Comp
import ./equality_lemmas.bend as Eq

# Comparisons
# -----------

def ltdisc(c: Cmp) -> Type:
  match c:
    case LT{}:
      Empty
    case EQ{}:
      Unit
    case GT{}:
      Unit

def eq_lt(e: {EQ{} == LT{} : Cmp}) -> Empty:
  %e : {ltdisc(_) : Type}
  Unit{}

def gt_lt(e: {GT{} == LT{} : Cmp}) -> Empty:
  %e : {ltdisc(_) : Type}
  Unit{}

def flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

def cmp_flip(a: Nat, b: Nat) -> {Nat.cmp(b, a) == flip(Nat.cmp(a, b)) : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      cmp_flip(ap, bp)

def cmp_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.cmp(a, b) == LT{} : Cmp}, bc: {Nat.cmp(b, c) == LT{} : Cmp}) -> {Nat.cmp(a, c) == LT{} : Cmp}:
  match a b c:
    case 0n 0n _:
      Empty.absurd({Nat.cmp(0n, c) == LT{} : Cmp}, eq_lt(ab))
    case 0n 1n+bp 0n:
      Empty.absurd({Nat.cmp(0n, 0n) == LT{} : Cmp}, gt_lt(bc))
    case 0n 1n+bp 1n+cp:
      {==}
    case 1n+ap 0n _:
      Empty.absurd({Nat.cmp(1n+ap, c) == LT{} : Cmp}, gt_lt(ab))
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.cmp(1n+ap, 0n) == LT{} : Cmp}, gt_lt(bc))
    case 1n+ap 1n+bp 1n+cp:
      cmp_trans(ap, bp, cp, ab, bc)

def cmp_eq(a: Nat, b: Nat, e: {Nat.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, Eq.lt_eq(e))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, Eq.gt_eq(e))
    case 1n+ap 1n+bp:
      Equal.cong(Nat, Nat, n => 1n+n, ap, bp, cmp_eq(ap, bp, e))

def is_eq_flip(c: Cmp) -> {Cmp.is_eq(flip(c)) == Cmp.is_eq(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def is_eq_sym(+a: Nat, +b: Nat) -> {Nat.is_eq(b, a) == Nat.is_eq(a, b) : Bool}:
  %Equal.sym(Cmp, Nat.cmp(b, a), flip(Nat.cmp(a, b)), cmp_flip(a, b)) : {Cmp.is_eq(_) == Nat.is_eq(a, b) : Bool}
  is_eq_flip(Nat.cmp(a, b))

def nat_eq(+a: Nat, +b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  cmp_eq(a, b, Eq.cmp_of_is_eq(Nat.cmp(a, b), e))

# Names: lexicographic, so the same three facts hold of `M.Name.cmp`.
def name_flip.of(c: Cmp, a2: Nat, b2: Nat) -> {M.Name.cmp.of(flip(c), b2, a2) == flip(M.Name.cmp.of(c, a2, b2)) : Cmp}:
  match c:
    case LT{}:
      {==}
    case GT{}:
      {==}
    case EQ{}:
      cmp_flip(a2, b2)

def name_flip(a: M.Name, b: M.Name) -> {M.Name.cmp(b, a) == flip(M.Name.cmp(a, b)) : Cmp}:
  match a b:
    case M.Name{+a1, +a2} M.Name{+b1, +b2}:
      %Equal.sym(Cmp, Nat.cmp(b1, a1), flip(Nat.cmp(a1, b1)), cmp_flip(a1, b1)) : {M.Name.cmp.of(_, b2, a2) == flip(M.Name.cmp.of(Nat.cmp(a1, b1), a2, b2)) : Cmp}
      name_flip.of(Nat.cmp(a1, b1), a2, b2)

def name_trans.of(+a1: Nat, +b1: Nat, +c1: Nat, +a2: Nat, +b2: Nat, +c2: Nat, x: Cmp, y: Cmp, ex: {Nat.cmp(a1, b1) == x : Cmp}, ey: {Nat.cmp(b1, c1) == y : Cmp}, ab: {M.Name.cmp.of(x, a2, b2) == LT{} : Cmp}, bc: {M.Name.cmp.of(y, b2, c2) == LT{} : Cmp}) -> {M.Name.cmp.of(Nat.cmp(a1, c1), a2, c2) == LT{} : Cmp}:
  match x y:
    case LT{} LT{}:
      %Equal.sym(Cmp, Nat.cmp(a1, c1), LT{}, cmp_trans(a1, b1, c1, ex, ey)) : {M.Name.cmp.of(_, a2, c2) == LT{} : Cmp}
      {==}
    case LT{} EQ{}:
      %cmp_eq(b1, c1, ey) : {M.Name.cmp.of(Nat.cmp(a1, _), a2, c2) == LT{} : Cmp}
      %Equal.sym(Cmp, Nat.cmp(a1, b1), LT{}, ex) : {M.Name.cmp.of(_, a2, c2) == LT{} : Cmp}
      {==}
    case LT{} GT{}:
      Empty.absurd({M.Name.cmp.of(Nat.cmp(a1, c1), a2, c2) == LT{} : Cmp}, gt_lt(bc))
    case EQ{} LT{}:
      %Equal.sym(Nat, a1, b1, cmp_eq(a1, b1, ex)) : {M.Name.cmp.of(Nat.cmp(_, c1), a2, c2) == LT{} : Cmp}
      %Equal.sym(Cmp, Nat.cmp(b1, c1), LT{}, ey) : {M.Name.cmp.of(_, a2, c2) == LT{} : Cmp}
      {==}
    case EQ{} EQ{}:
      %Equal.sym(Nat, a1, b1, cmp_eq(a1, b1, ex)) : {M.Name.cmp.of(Nat.cmp(_, c1), a2, c2) == LT{} : Cmp}
      %Equal.sym(Cmp, Nat.cmp(b1, c1), EQ{}, ey) : {M.Name.cmp.of(_, a2, c2) == LT{} : Cmp}
      cmp_trans(a2, b2, c2, ab, bc)
    case EQ{} GT{}:
      Empty.absurd({M.Name.cmp.of(Nat.cmp(a1, c1), a2, c2) == LT{} : Cmp}, gt_lt(bc))
    case GT{} _:
      Empty.absurd({M.Name.cmp.of(Nat.cmp(a1, c1), a2, c2) == LT{} : Cmp}, gt_lt(ab))

def name_trans(a: M.Name, b: M.Name, c: M.Name, ab: {M.Name.cmp(a, b) == LT{} : Cmp}, bc: {M.Name.cmp(b, c) == LT{} : Cmp}) -> {M.Name.cmp(a, c) == LT{} : Cmp}:
  match a b c:
    case M.Name{+a1, +a2} M.Name{+b1, +b2} M.Name{+c1, +c2}:
      name_trans.of(a1, b1, c1, a2, b2, c2, Nat.cmp(a1, b1), Nat.cmp(b1, c1), {==}, {==}, ab, bc)

def cmp_of_is_lt(c: Cmp, e: {Cmp.is_lt(c) == True{} : Bool}) -> {c == LT{} : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({EQ{} == LT{} : Cmp}, Comp.false_true(e))
    case GT{}:
      Empty.absurd({GT{} == LT{} : Cmp}, Comp.false_true(e))

def lt_gt(+a: Nat, +b: Nat, e: {Nat.cmp(a, b) == LT{} : Cmp}) -> {Nat.cmp(b, a) == GT{} : Cmp}:
  %Equal.sym(Cmp, Nat.cmp(b, a), flip(Nat.cmp(a, b)), cmp_flip(a, b)) : {_ == GT{} : Cmp}
  %Equal.sym(Cmp, Nat.cmp(a, b), LT{}, e) : {flip(_) == GT{} : Cmp}
  {==}

def lt_gt.back(+a: Nat, +b: Nat, e: {Nat.cmp(a, b) == GT{} : Cmp}) -> {Nat.cmp(b, a) == LT{} : Cmp}:
  %Equal.sym(Cmp, Nat.cmp(b, a), flip(Nat.cmp(a, b)), cmp_flip(a, b)) : {_ == LT{} : Cmp}
  %Equal.sym(Cmp, Nat.cmp(a, b), GT{}, e) : {flip(_) == LT{} : Cmp}
  {==}

# Joining removals
# ----------------
#
# Two events joining one element's removals: one list, whichever joined
# first. Induction on the list, with both comparisons against its head
# named so every case computes.
def ins_comm.at(+y: Nat, +ys: List<&2, Nat>, +f: Nat, +g: Nat, cf: Cmp, cg: Cmp, ef: {Nat.cmp(f, y) == cf : Cmp}, eg: {Nat.cmp(g, y) == cg : Cmp}, +fg: {Nat.cmp(f, g) == LT{} : Cmp}, ih: {M.ins(M.ins(ys, f), g) == M.ins(M.ins(ys, g), f) : List<&2, Nat>}) -> {M.ins(M.ins.put(f, y, ys, M.ins(ys, f), Cmp.is_lt(cf)), g) == M.ins(M.ins.put(g, y, ys, M.ins(ys, g), Cmp.is_lt(cg)), f) : List<&2, Nat>}:
  match cf cg:
    case LT{} LT{}:
      %Equal.sym(Cmp, Nat.cmp(g, f), GT{}, lt_gt(f, g, fg)) : {M.ins.put(g, f, y <> ys, M.ins(y <> ys, g), Cmp.is_lt(_)) == M.ins.put(f, g, y <> ys, M.ins(y <> ys, f), Cmp.is_lt(Nat.cmp(f, g))) : List<&2, Nat>}
      %Equal.sym(Cmp, Nat.cmp(f, g), LT{}, fg) : {f <> M.ins(y <> ys, g) == M.ins.put(f, g, y <> ys, M.ins(y <> ys, f), Cmp.is_lt(_)) : List<&2, Nat>}
      %Equal.sym(Cmp, Nat.cmp(g, y), LT{}, eg) : {f <> M.ins.put(g, y, ys, M.ins(ys, g), Cmp.is_lt(_)) == f <> g <> y <> ys : List<&2, Nat>}
      {==}
    case LT{} EQ{}:
      %Equal.sym(Cmp, Nat.cmp(g, f), GT{}, lt_gt(f, g, fg)) : {M.ins.put(g, f, y <> ys, M.ins(y <> ys, g), Cmp.is_lt(_)) == M.ins(y <> M.ins(ys, g), f) : List<&2, Nat>}
      %Equal.sym(Cmp, Nat.cmp(g, y), EQ{}, eg) : {f <> M.ins.put(g, y, ys, M.ins(ys, g), Cmp.is_lt(_)) == M.ins(y <> M.ins(ys, g), f) : List<&2, Nat>}
      %Equal.sym(Cmp, Nat.cmp(f, y), LT{}, ef) : {f <> y <> M.ins(ys, g) == M.ins.put(f, y, M.ins(ys, g), M.ins(M.ins(ys, g), f), Cmp.is_lt(_)) : List<&2, Nat>}
      {==}
    case LT{} GT{}:
      %Equal.sym(Cmp, Nat.cmp(g, f), GT{}, lt_gt(f, g, fg)) : {M.ins.put(g, f, y <> ys, M.ins(y <> ys, g), Cmp.is_lt(_)) == M.ins(y <> M.ins(ys, g), f) : List<&2, Nat>}
      %Equal.sym(Cmp, Nat.cmp(g, y), GT{}, eg) : {f <> M.ins.put(g, y, ys, M.ins(ys, g), Cmp.is_lt(_)) == M.ins(y <> M.ins(ys, g), f) : List<&2, Nat>}
      %Equal.sym(Cmp, Nat.cmp(f, y), LT{}, ef) : {f <> y <> M.ins(ys, g) == M.ins.put(f, y, M.ins(ys, g), M.ins(M.ins(ys, g), f), Cmp.is_lt(_)) : List<&2, Nat>}
      {==}
    case EQ{} LT{}:
      Empty.absurd({M.ins(y <> M.ins(ys, f), g) == M.ins(g <> y <> ys, f) : List<&2, Nat>}, eq_lt(Equal.trans(Cmp, EQ{}, Nat.cmp(f, y), LT{}, Equal.sym(Cmp, Nat.cmp(f, y), EQ{}, ef), cmp_trans(f, g, y, fg, eg))))
    case GT{} LT{}:
      Empty.absurd({M.ins(y <> M.ins(ys, f), g) == M.ins(g <> y <> ys, f) : List<&2, Nat>}, gt_lt(Equal.trans(Cmp, GT{}, Nat.cmp(f, y), LT{}, Equal.sym(Cmp, Nat.cmp(f, y), GT{}, ef), cmp_trans(f, g, y, fg, eg))))
    case EQ{} EQ{}:
      %Equal.sym(Cmp, Nat.cmp(g, y), EQ{}, eg) : {M.ins.put(g, y, M.ins(ys, f), M.ins(M.ins(ys, f), g), Cmp.is_lt(_)) == M.ins(y <> M.ins(ys, g), f) : List<&2, Nat>}
      %Equal.sym(Cmp, Nat.cmp(f, y), EQ{}, ef) : {y <> M.ins(M.ins(ys, f), g) == M.ins.put(f, y, M.ins(ys, g), M.ins(M.ins(ys, g), f), Cmp.is_lt(_)) : List<&2, Nat>}
      Equal.cong(List<&2, Nat>, List<&2, Nat>, l => y <> l, M.ins(M.ins(ys, f), g), M.ins(M.ins(ys, g), f), ih)
    case EQ{} GT{}:
      %Equal.sym(Cmp, Nat.cmp(g, y), GT{}, eg) : {M.ins.put(g, y, M.ins(ys, f), M.ins(M.ins(ys, f), g), Cmp.is_lt(_)) == M.ins(y <> M.ins(ys, g), f) : List<&2, Nat>}
      %Equal.sym(Cmp, Nat.cmp(f, y), EQ{}, ef) : {y <> M.ins(M.ins(ys, f), g) == M.ins.put(f, y, M.ins(ys, g), M.ins(M.ins(ys, g), f), Cmp.is_lt(_)) : List<&2, Nat>}
      Equal.cong(List<&2, Nat>, List<&2, Nat>, l => y <> l, M.ins(M.ins(ys, f), g), M.ins(M.ins(ys, g), f), ih)
    case GT{} EQ{}:
      %Equal.sym(Cmp, Nat.cmp(g, y), EQ{}, eg) : {M.ins.put(g, y, M.ins(ys, f), M.ins(M.ins(ys, f), g), Cmp.is_lt(_)) == M.ins(y <> M.ins(ys, g), f) : List<&2, Nat>}
      %Equal.sym(Cmp, Nat.cmp(f, y), GT{}, ef) : {y <> M.ins(M.ins(ys, f), g) == M.ins.put(f, y, M.ins(ys, g), M.ins(M.ins(ys, g), f), Cmp.is_lt(_)) : List<&2, Nat>}
      Equal.cong(List<&2, Nat>, List<&2, Nat>, l => y <> l, M.ins(M.ins(ys, f), g), M.ins(M.ins(ys, g), f), ih)
    case GT{} GT{}:
      %Equal.sym(Cmp, Nat.cmp(g, y), GT{}, eg) : {M.ins.put(g, y, M.ins(ys, f), M.ins(M.ins(ys, f), g), Cmp.is_lt(_)) == M.ins(y <> M.ins(ys, g), f) : List<&2, Nat>}
      %Equal.sym(Cmp, Nat.cmp(f, y), GT{}, ef) : {y <> M.ins(M.ins(ys, f), g) == M.ins.put(f, y, M.ins(ys, g), M.ins(M.ins(ys, g), f), Cmp.is_lt(_)) : List<&2, Nat>}
      Equal.cong(List<&2, Nat>, List<&2, Nat>, l => y <> l, M.ins(M.ins(ys, f), g), M.ins(M.ins(ys, g), f), ih)

def ins_comm.lt(d: List<&2, Nat>, +f: Nat, +g: Nat, +fg: {Nat.cmp(f, g) == LT{} : Cmp}) -> {M.ins(M.ins(d, f), g) == M.ins(M.ins(d, g), f) : List<&2, Nat>}:
  match d:
    case Nil{}:
      %Equal.sym(Cmp, Nat.cmp(g, f), GT{}, lt_gt(f, g, fg)) : {M.ins.put(g, f, Nil{}, M.ins(Nil{}, g), Cmp.is_lt(_)) == M.ins.put(f, g, Nil{}, M.ins(Nil{}, f), Cmp.is_lt(Nat.cmp(f, g))) : List<&2, Nat>}
      %Equal.sym(Cmp, Nat.cmp(f, g), LT{}, fg) : {f <> M.ins(Nil{}, g) == M.ins.put(f, g, Nil{}, M.ins(Nil{}, f), Cmp.is_lt(_)) : List<&2, Nat>}
      {==}
    case +y <> +ys:
      ins_comm.at(y, ys, f, g, Nat.cmp(f, y), Nat.cmp(g, y), {==}, {==}, fg, ins_comm.lt(ys, f, g, fg))

# Any two distinct events.
def ins_comm(+d: List<&2, Nat>, +f: Nat, +g: Nat, c: Cmp, +e: {Nat.cmp(f, g) == c : Cmp}, ne: {Cmp.is_eq(c) == False{} : Bool}) -> {M.ins(M.ins(d, f), g) == M.ins(M.ins(d, g), f) : List<&2, Nat>}:
  match c:
    case LT{}:
      ins_comm.lt(d, f, g, e)
    case EQ{}:
      Empty.absurd({M.ins(M.ins(d, f), g) == M.ins(M.ins(d, g), f) : List<&2, Nat>}, Comp.false_true(Equal.sym(Bool, True{}, False{}, ne)))
    case GT{}:
      Equal.sym(List<&2, Nat>, M.ins(M.ins(d, g), f), M.ins(M.ins(d, f), g), ins_comm.lt(d, g, f, lt_gt.back(f, g, e)))


def name_lt_gt(+a: M.Name, +b: M.Name, e: {M.Name.cmp(a, b) == LT{} : Cmp}) -> {M.Name.cmp(b, a) == GT{} : Cmp}:
  %Equal.sym(Cmp, M.Name.cmp(b, a), flip(M.Name.cmp(a, b)), name_flip(a, b)) : {_ == GT{} : Cmp}
  %Equal.sym(Cmp, M.Name.cmp(a, b), LT{}, e) : {flip(_) == GT{} : Cmp}
  {==}

def name_lt_gt.back(+a: M.Name, +b: M.Name, e: {M.Name.cmp(a, b) == GT{} : Cmp}) -> {M.Name.cmp(b, a) == LT{} : Cmp}:
  %Equal.sym(Cmp, M.Name.cmp(b, a), flip(M.Name.cmp(a, b)), name_flip(a, b)) : {_ == LT{} : Cmp}
  %Equal.sym(Cmp, M.Name.cmp(a, b), GT{}, e) : {flip(_) == LT{} : Cmp}
  {==}

def attach_comm.at(+y: M.Node, +ys: List<&2, M.Node>, +f: M.Node, +g: M.Node, cf: Cmp, cg: Cmp, ef: {M.Name.cmp(M.Node.name(f), M.Node.name(y)) == cf : Cmp}, eg: {M.Name.cmp(M.Node.name(g), M.Node.name(y)) == cg : Cmp}, +fg: {M.Name.cmp(M.Node.name(f), M.Node.name(g)) == LT{} : Cmp}, ih: {M.attach(M.attach(ys, f), g) == M.attach(M.attach(ys, g), f) : List<&2, M.Node>}) -> {M.attach(M.attach.put(f, y, ys, M.attach(ys, f), Cmp.is_lt(cf)), g) == M.attach(M.attach.put(g, y, ys, M.attach(ys, g), Cmp.is_lt(cg)), f) : List<&2, M.Node>}:
  match cf cg:
    case LT{} LT{}:
      %Equal.sym(Cmp, M.Name.cmp(M.Node.name(g), M.Node.name(f)), GT{}, name_lt_gt(M.Node.name(f), M.Node.name(g), fg)) : {M.attach.put(g, f, y <> ys, M.attach(y <> ys, g), Cmp.is_lt(_)) == M.attach.put(f, g, y <> ys, M.attach(y <> ys, f), Cmp.is_lt(M.Name.cmp(M.Node.name(f), M.Node.name(g)))) : List<&2, M.Node>}
      %Equal.sym(Cmp, M.Name.cmp(M.Node.name(f), M.Node.name(g)), LT{}, fg) : {f <> M.attach(y <> ys, g) == M.attach.put(f, g, y <> ys, M.attach(y <> ys, f), Cmp.is_lt(_)) : List<&2, M.Node>}
      %Equal.sym(Cmp, M.Name.cmp(M.Node.name(g), M.Node.name(y)), LT{}, eg) : {f <> M.attach.put(g, y, ys, M.attach(ys, g), Cmp.is_lt(_)) == f <> g <> y <> ys : List<&2, M.Node>}
      {==}
    case LT{} EQ{}:
      %Equal.sym(Cmp, M.Name.cmp(M.Node.name(g), M.Node.name(f)), GT{}, name_lt_gt(M.Node.name(f), M.Node.name(g), fg)) : {M.attach.put(g, f, y <> ys, M.attach(y <> ys, g), Cmp.is_lt(_)) == M.attach(y <> M.attach(ys, g), f) : List<&2, M.Node>}
      %Equal.sym(Cmp, M.Name.cmp(M.Node.name(g), M.Node.name(y)), EQ{}, eg) : {f <> M.attach.put(g, y, ys, M.attach(ys, g), Cmp.is_lt(_)) == M.attach(y <> M.attach(ys, g), f) : List<&2, M.Node>}
      %Equal.sym(Cmp, M.Name.cmp(M.Node.name(f), M.Node.name(y)), LT{}, ef) : {f <> y <> M.attach(ys, g) == M.attach.put(f, y, M.attach(ys, g), M.attach(M.attach(ys, g), f), Cmp.is_lt(_)) : List<&2, M.Node>}
      {==}
    case LT{} GT{}:
      %Equal.sym(Cmp, M.Name.cmp(M.Node.name(g), M.Node.name(f)), GT{}, name_lt_gt(M.Node.name(f), M.Node.name(g), fg)) : {M.attach.put(g, f, y <> ys, M.attach(y <> ys, g), Cmp.is_lt(_)) == M.attach(y <> M.attach(ys, g), f) : List<&2, M.Node>}
      %Equal.sym(Cmp, M.Name.cmp(M.Node.name(g), M.Node.name(y)), GT{}, eg) : {f <> M.attach.put(g, y, ys, M.attach(ys, g), Cmp.is_lt(_)) == M.attach(y <> M.attach(ys, g), f) : List<&2, M.Node>}
      %Equal.sym(Cmp, M.Name.cmp(M.Node.name(f), M.Node.name(y)), LT{}, ef) : {f <> y <> M.attach(ys, g) == M.attach.put(f, y, M.attach(ys, g), M.attach(M.attach(ys, g), f), Cmp.is_lt(_)) : List<&2, M.Node>}
      {==}
    case EQ{} LT{}:
      Empty.absurd({M.attach(y <> M.attach(ys, f), g) == M.attach(g <> y <> ys, f) : List<&2, M.Node>}, eq_lt(Equal.trans(Cmp, EQ{}, M.Name.cmp(M.Node.name(f), M.Node.name(y)), LT{}, Equal.sym(Cmp, M.Name.cmp(M.Node.name(f), M.Node.name(y)), EQ{}, ef), name_trans(M.Node.name(f), M.Node.name(g), M.Node.name(y), fg, eg))))
    case GT{} LT{}:
      Empty.absurd({M.attach(y <> M.attach(ys, f), g) == M.attach(g <> y <> ys, f) : List<&2, M.Node>}, gt_lt(Equal.trans(Cmp, GT{}, M.Name.cmp(M.Node.name(f), M.Node.name(y)), LT{}, Equal.sym(Cmp, M.Name.cmp(M.Node.name(f), M.Node.name(y)), GT{}, ef), name_trans(M.Node.name(f), M.Node.name(g), M.Node.name(y), fg, eg))))
    case EQ{} EQ{}:
      %Equal.sym(Cmp, M.Name.cmp(M.Node.name(g), M.Node.name(y)), EQ{}, eg) : {M.attach.put(g, y, M.attach(ys, f), M.attach(M.attach(ys, f), g), Cmp.is_lt(_)) == M.attach(y <> M.attach(ys, g), f) : List<&2, M.Node>}
      %Equal.sym(Cmp, M.Name.cmp(M.Node.name(f), M.Node.name(y)), EQ{}, ef) : {y <> M.attach(M.attach(ys, f), g) == M.attach.put(f, y, M.attach(ys, g), M.attach(M.attach(ys, g), f), Cmp.is_lt(_)) : List<&2, M.Node>}
      Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => y <> l, M.attach(M.attach(ys, f), g), M.attach(M.attach(ys, g), f), ih)
    case EQ{} GT{}:
      %Equal.sym(Cmp, M.Name.cmp(M.Node.name(g), M.Node.name(y)), GT{}, eg) : {M.attach.put(g, y, M.attach(ys, f), M.attach(M.attach(ys, f), g), Cmp.is_lt(_)) == M.attach(y <> M.attach(ys, g), f) : List<&2, M.Node>}
      %Equal.sym(Cmp, M.Name.cmp(M.Node.name(f), M.Node.name(y)), EQ{}, ef) : {y <> M.attach(M.attach(ys, f), g) == M.attach.put(f, y, M.attach(ys, g), M.attach(M.attach(ys, g), f), Cmp.is_lt(_)) : List<&2, M.Node>}
      Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => y <> l, M.attach(M.attach(ys, f), g), M.attach(M.attach(ys, g), f), ih)
    case GT{} EQ{}:
      %Equal.sym(Cmp, M.Name.cmp(M.Node.name(g), M.Node.name(y)), EQ{}, eg) : {M.attach.put(g, y, M.attach(ys, f), M.attach(M.attach(ys, f), g), Cmp.is_lt(_)) == M.attach(y <> M.attach(ys, g), f) : List<&2, M.Node>}
      %Equal.sym(Cmp, M.Name.cmp(M.Node.name(f), M.Node.name(y)), GT{}, ef) : {y <> M.attach(M.attach(ys, f), g) == M.attach.put(f, y, M.attach(ys, g), M.attach(M.attach(ys, g), f), Cmp.is_lt(_)) : List<&2, M.Node>}
      Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => y <> l, M.attach(M.attach(ys, f), g), M.attach(M.attach(ys, g), f), ih)
    case GT{} GT{}:
      %Equal.sym(Cmp, M.Name.cmp(M.Node.name(g), M.Node.name(y)), GT{}, eg) : {M.attach.put(g, y, M.attach(ys, f), M.attach(M.attach(ys, f), g), Cmp.is_lt(_)) == M.attach(y <> M.attach(ys, g), f) : List<&2, M.Node>}
      %Equal.sym(Cmp, M.Name.cmp(M.Node.name(f), M.Node.name(y)), GT{}, ef) : {y <> M.attach(M.attach(ys, f), g) == M.attach.put(f, y, M.attach(ys, g), M.attach(M.attach(ys, g), f), Cmp.is_lt(_)) : List<&2, M.Node>}
      Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => y <> l, M.attach(M.attach(ys, f), g), M.attach(M.attach(ys, g), f), ih)

def attach_comm.lt(d: List<&2, M.Node>, +f: M.Node, +g: M.Node, +fg: {M.Name.cmp(M.Node.name(f), M.Node.name(g)) == LT{} : Cmp}) -> {M.attach(M.attach(d, f), g) == M.attach(M.attach(d, g), f) : List<&2, M.Node>}:
  match d:
    case Nil{}:
      %Equal.sym(Cmp, M.Name.cmp(M.Node.name(g), M.Node.name(f)), GT{}, name_lt_gt(M.Node.name(f), M.Node.name(g), fg)) : {M.attach.put(g, f, Nil{}, M.attach(Nil{}, g), Cmp.is_lt(_)) == M.attach.put(f, g, Nil{}, M.attach(Nil{}, f), Cmp.is_lt(M.Name.cmp(M.Node.name(f), M.Node.name(g)))) : List<&2, M.Node>}
      %Equal.sym(Cmp, M.Name.cmp(M.Node.name(f), M.Node.name(g)), LT{}, fg) : {f <> M.attach(Nil{}, g) == M.attach.put(f, g, Nil{}, M.attach(Nil{}, f), Cmp.is_lt(_)) : List<&2, M.Node>}
      {==}
    case +y <> +ys:
      attach_comm.at(y, ys, f, g, M.Name.cmp(M.Node.name(f), M.Node.name(y)), M.Name.cmp(M.Node.name(g), M.Node.name(y)), {==}, {==}, fg, attach_comm.lt(ys, f, g, fg))

# Any two elements of distinct names.
def attach_comm(+d: List<&2, M.Node>, +f: M.Node, +g: M.Node, c: Cmp, +e: {M.Name.cmp(M.Node.name(f), M.Node.name(g)) == c : Cmp}, ne: {Cmp.is_eq(c) == False{} : Bool}) -> {M.attach(M.attach(d, f), g) == M.attach(M.attach(d, g), f) : List<&2, M.Node>}:
  match c:
    case LT{}:
      attach_comm.lt(d, f, g, e)
    case EQ{}:
      Empty.absurd({M.attach(M.attach(d, f), g) == M.attach(M.attach(d, g), f) : List<&2, M.Node>}, Comp.false_true(Equal.sym(Bool, True{}, False{}, ne)))
    case GT{}:
      Equal.sym(List<&2, M.Node>, M.attach(M.attach(d, g), f), M.attach(M.attach(d, f), g), attach_comm.lt(d, g, f, name_lt_gt.back(M.Node.name(f), M.Node.name(g), e)))

# Marking
# -------

def mark_name(x: M.Node, target: M.Name, by: Nat) -> {M.Node.name(M.Node.mark(x, target, by)) == M.Node.name(x) : M.Name}:
  match x:
    case M.Node{nm, it, pl, d}:
      {==}

def not_of_true(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Comp.false_true(e))

def true_false(e: {True{} == False{} : Bool}) -> Empty:
  Comp.false_true(Equal.sym(Bool, True{}, False{}, e))

def and_intro(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, Comp.false_true(ea))

# Two events joining one element's removals, or two different elements'.
def ins_if_comm(+d: List<&2, Nat>, +f: Nat, +g: Nat, hf: Bool, hg: Bool, c: Cmp, +e: {Nat.cmp(f, g) == c : Cmp}, ne: {Cmp.is_eq(c) == False{} : Bool}) -> {M.ins.if(M.ins.if(d, f, hf), g, hg) == M.ins.if(M.ins.if(d, g, hg), f, hf) : List<&2, Nat>}:
  match hf hg:
    case True{} True{}:
      ins_comm(d, f, g, c, e, ne)
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def node_mark_comm(x: M.Node, +n1: M.Name, +n2: M.Name, +f: Nat, +g: Nat, c: Cmp, +e: {Nat.cmp(f, g) == c : Cmp}, ne: {Cmp.is_eq(c) == False{} : Bool}) -> {M.Node.mark(M.Node.mark(x, n1, f), n2, g) == M.Node.mark(M.Node.mark(x, n2, g), n1, f) : M.Node}:
  match x:
    case M.Node{+nm, it, pl, d}:
      Equal.cong(List<&2, Nat>, M.Node, l => M.Node{nm, it, pl, l}, M.ins.if(M.ins.if(d, f, M.Name.eq(nm, n1)), g, M.Name.eq(nm, n2)), M.ins.if(M.ins.if(d, g, M.Name.eq(nm, n2)), f, M.Name.eq(nm, n1)),
        ins_if_comm(d, f, g, M.Name.eq(nm, n1), M.Name.eq(nm, n2), c, e, ne))

def mark_comm(t: List<&2, M.Node>, +n1: M.Name, +n2: M.Name, +f: Nat, +g: Nat, +c: Cmp, +e: {Nat.cmp(f, g) == c : Cmp}, +ne: {Cmp.is_eq(c) == False{} : Bool}) -> {M.mark(M.mark(t, n1, f), n2, g) == M.mark(M.mark(t, n2, g), n1, f) : List<&2, M.Node>}:
  match t:
    case Nil{}:
      {==}
    case x <> xs:
      %Equal.sym(M.Node, M.Node.mark(M.Node.mark(x, n1, f), n2, g), M.Node.mark(M.Node.mark(x, n2, g), n1, f), node_mark_comm(x, n1, n2, f, g, c, e, ne)) : {_ <> M.mark(M.mark(xs, n1, f), n2, g) == M.Node.mark(M.Node.mark(x, n2, g), n1, f) <> M.mark(M.mark(xs, n2, g), n1, f) : List<&2, M.Node>}
      Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => M.Node.mark(M.Node.mark(x, n2, g), n1, f) <> l, M.mark(M.mark(xs, n1, f), n2, g), M.mark(M.mark(xs, n2, g), n1, f), mark_comm(xs, n1, n2, f, g, c, e, ne))

# Marking one element and attaching another.
def attach_mark.at(+x: M.Node, +xs: List<&2, M.Node>, +a: M.Node, +n: M.Name, +by: Nat, lt: Bool, e: {Cmp.is_lt(M.Name.cmp(M.Node.name(a), M.Node.name(x))) == lt : Bool}, ma: {M.Node.mark(a, n, by) == a : M.Node}, ih: {M.mark(M.attach(xs, a), n, by) == M.attach(M.mark(xs, n, by), a) : List<&2, M.Node>}) -> {M.mark(M.attach.put(a, x, xs, M.attach(xs, a), lt), n, by) == M.attach.put(a, M.Node.mark(x, n, by), M.mark(xs, n, by), M.attach(M.mark(xs, n, by), a), Cmp.is_lt(M.Name.cmp(M.Node.name(a), M.Node.name(M.Node.mark(x, n, by))))) : List<&2, M.Node>}:
  match lt:
    case True{}:
      %Equal.sym(M.Name, M.Node.name(M.Node.mark(x, n, by)), M.Node.name(x), mark_name(x, n, by)) : {M.mark(a <> x <> xs, n, by) == M.attach.put(a, M.Node.mark(x, n, by), M.mark(xs, n, by), M.attach(M.mark(xs, n, by), a), Cmp.is_lt(M.Name.cmp(M.Node.name(a), _))) : List<&2, M.Node>}
      %Equal.sym(Bool, Cmp.is_lt(M.Name.cmp(M.Node.name(a), M.Node.name(x))), True{}, e) : {M.mark(a <> x <> xs, n, by) == M.attach.put(a, M.Node.mark(x, n, by), M.mark(xs, n, by), M.attach(M.mark(xs, n, by), a), _) : List<&2, M.Node>}
      %Equal.sym(M.Node, M.Node.mark(a, n, by), a, ma) : {_ <> M.Node.mark(x, n, by) <> M.mark(xs, n, by) == a <> M.Node.mark(x, n, by) <> M.mark(xs, n, by) : List<&2, M.Node>}
      {==}
    case False{}:
      %Equal.sym(M.Name, M.Node.name(M.Node.mark(x, n, by)), M.Node.name(x), mark_name(x, n, by)) : {M.mark(x <> M.attach(xs, a), n, by) == M.attach.put(a, M.Node.mark(x, n, by), M.mark(xs, n, by), M.attach(M.mark(xs, n, by), a), Cmp.is_lt(M.Name.cmp(M.Node.name(a), _))) : List<&2, M.Node>}
      %Equal.sym(Bool, Cmp.is_lt(M.Name.cmp(M.Node.name(a), M.Node.name(x))), False{}, e) : {M.mark(x <> M.attach(xs, a), n, by) == M.attach.put(a, M.Node.mark(x, n, by), M.mark(xs, n, by), M.attach(M.mark(xs, n, by), a), _) : List<&2, M.Node>}
      Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => M.Node.mark(x, n, by) <> l, M.mark(M.attach(xs, a), n, by), M.attach(M.mark(xs, n, by), a), ih)

def attach_mark(t: List<&2, M.Node>, +a: M.Node, +n: M.Name, +by: Nat, +ma: {M.Node.mark(a, n, by) == a : M.Node}) -> {M.mark(M.attach(t, a), n, by) == M.attach(M.mark(t, n, by), a) : List<&2, M.Node>}:
  match t:
    case Nil{}:
      %Equal.sym(M.Node, M.Node.mark(a, n, by), a, ma) : {_ <> Nil{} == a <> Nil{} : List<&2, M.Node>}
      {==}
    case +x <> +xs:
      attach_mark.at(x, xs, a, n, by, Cmp.is_lt(M.Name.cmp(M.Node.name(a), M.Node.name(x))), {==}, ma, attach_mark(xs, a, n, by, ma))

# An element of one author is never a target of another's delete.
def name_ne.of(c: Cmp, +m: Nat, +m2: Nat, e: {Cmp.is_eq(c) == False{} : Bool}) -> {Cmp.is_eq(M.Name.cmp.of(c, m, m2)) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case GT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_eq(Nat.cmp(m, m2)) == False{} : Bool}, true_false(e))

def name_ne(+f: Nat, +m: Nat, +a: Nat, +m2: Nat, ne: {Nat.is_eq(f, a) == False{} : Bool}) -> {M.Name.eq(M.Name{f, m}, M.Name{a, m2}) == False{} : Bool}:
  name_ne.of(Nat.cmp(f, a), m, m2, ne)

def unmarked(+f: Nat, +m: Nat, it: Ops.Item, pl: M.Place, d: List<&2, Nat>, +a: Nat, +m2: Nat, +by: Nat, ne: {Nat.is_eq(f, a) == False{} : Bool}) -> {M.Node.mark(M.Node{M.Name{f, m}, it, pl, d}, M.Name{a, m2}, by) == M.Node{M.Name{f, m}, it, pl, d} : M.Node}:
  %Equal.sym(Bool, M.Name.eq(M.Name{f, m}, M.Name{a, m2}), False{}, name_ne(f, m, a, m2, ne)) : {M.Node{M.Name{f, m}, it, pl, M.ins.if(d, by, _)} == M.Node{M.Name{f, m}, it, pl, d} : M.Node}
  {==}

# The view
# --------
#
# What an event does not know, it does not see: an element attached by an
# author outside `seen`, or a removal marked by one, leaves the view alone.
def restrict_attach.at(+x: M.Node, +xs: List<&2, M.Node>, +a: M.Node, +seen: List<&2, Nat>, lt: Bool, na: {M.has(seen, M.Node.author(a)) == False{} : Bool}, ih: {M.restrict(M.attach(xs, a), seen) == M.restrict(xs, seen) : List<&2, M.Node>}) -> {M.restrict(M.attach.put(a, x, xs, M.attach(xs, a), lt), seen) == M.restrict(x <> xs, seen) : List<&2, M.Node>}:
  match lt:
    case True{}:
      %Equal.sym(Bool, M.has(seen, M.Node.author(a)), False{}, na) : {List.filter.put(M.Node, M.Node.restrict(a, seen), M.restrict(x <> xs, seen), _) == M.restrict(x <> xs, seen) : List<&2, M.Node>}
      {==}
    case False{}:
      Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => List.filter.put(M.Node, M.Node.restrict(x, seen), l, M.has(seen, M.Node.author(x))), M.restrict(M.attach(xs, a), seen), M.restrict(xs, seen), ih)

def restrict_attach(t: List<&2, M.Node>, +a: M.Node, +seen: List<&2, Nat>, +na: {M.has(seen, M.Node.author(a)) == False{} : Bool}) -> {M.restrict(M.attach(t, a), seen) == M.restrict(t, seen) : List<&2, M.Node>}:
  match t:
    case Nil{}:
      %Equal.sym(Bool, M.has(seen, M.Node.author(a)), False{}, na) : {List.filter.put(M.Node, M.Node.restrict(a, seen), Nil{}, _) == Nil{} : List<&2, M.Node>}
      {==}
    case +x <> +xs:
      restrict_attach.at(x, xs, a, seen, Cmp.is_lt(M.Name.cmp(M.Node.name(a), M.Node.name(x))), na, restrict_attach(xs, a, seen, na))

def keep_ins.at(+y: Nat, +ys: List<&2, Nat>, +by: Nat, +seen: List<&2, Nat>, lt: Bool, nb: {M.has(seen, by) == False{} : Bool}, ih: {M.keep(M.ins(ys, by), seen) == M.keep(ys, seen) : List<&2, Nat>}) -> {M.keep(M.ins.put(by, y, ys, M.ins(ys, by), lt), seen) == M.keep(y <> ys, seen) : List<&2, Nat>}:
  match lt:
    case True{}:
      %Equal.sym(Bool, M.has(seen, by), False{}, nb) : {List.filter.put(Nat, by, M.keep(y <> ys, seen), _) == M.keep(y <> ys, seen) : List<&2, Nat>}
      {==}
    case False{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, l => List.filter.put(Nat, y, l, M.has(seen, y)), M.keep(M.ins(ys, by), seen), M.keep(ys, seen), ih)

def keep_ins(d: List<&2, Nat>, +by: Nat, +seen: List<&2, Nat>, +nb: {M.has(seen, by) == False{} : Bool}) -> {M.keep(M.ins(d, by), seen) == M.keep(d, seen) : List<&2, Nat>}:
  match d:
    case Nil{}:
      %Equal.sym(Bool, M.has(seen, by), False{}, nb) : {List.filter.put(Nat, by, Nil{}, _) == Nil{} : List<&2, Nat>}
      {==}
    case +y <> +ys:
      keep_ins.at(y, ys, by, seen, Nat.is_lt(by, y), nb, keep_ins(ys, by, seen, nb))

def keep_ins_if(+d: List<&2, Nat>, +by: Nat, hit: Bool, +seen: List<&2, Nat>, nb: {M.has(seen, by) == False{} : Bool}) -> {M.keep(M.ins.if(d, by, hit), seen) == M.keep(d, seen) : List<&2, Nat>}:
  match hit:
    case True{}:
      keep_ins(d, by, seen, nb)
    case False{}:
      {==}

def restrict_marked(x: M.Node, +n: M.Name, +by: Nat, +seen: List<&2, Nat>, nb: {M.has(seen, by) == False{} : Bool}) -> {M.Node.restrict(M.Node.mark(x, n, by), seen) == M.Node.restrict(x, seen) : M.Node}:
  match x:
    case M.Node{+nm, it, pl, +d}:
      Equal.cong(List<&2, Nat>, M.Node, l => M.Node{nm, it, pl, l}, M.keep(M.ins.if(d, by, M.Name.eq(nm, n)), seen), M.keep(d, seen), keep_ins_if(d, by, M.Name.eq(nm, n), seen, nb))

def mark_author(x: M.Node, n: M.Name, by: Nat) -> {M.Node.author(M.Node.mark(x, n, by)) == M.Node.author(x) : Nat}:
  match x:
    case M.Node{M.Name{a, m}, it, pl, d}:
      {==}

def restrict_mark(t: List<&2, M.Node>, +n: M.Name, +by: Nat, +seen: List<&2, Nat>, +nb: {M.has(seen, by) == False{} : Bool}) -> {M.restrict(M.mark(t, n, by), seen) == M.restrict(t, seen) : List<&2, M.Node>}:
  match t:
    case Nil{}:
      {==}
    case +x <> xs:
      %Equal.sym(Nat, M.Node.author(M.Node.mark(x, n, by)), M.Node.author(x), mark_author(x, n, by)) : {List.filter.put(M.Node, M.Node.restrict(M.Node.mark(x, n, by), seen), M.restrict(M.mark(xs, n, by), seen), M.has(seen, _)) == M.restrict(x <> xs, seen) : List<&2, M.Node>}
      %Equal.sym(M.Node, M.Node.restrict(M.Node.mark(x, n, by), seen), M.Node.restrict(x, seen), restrict_marked(x, n, by, seen, nb)) : {List.filter.put(M.Node, _, M.restrict(M.mark(xs, n, by), seen), M.has(seen, M.Node.author(x))) == M.restrict(x <> xs, seen) : List<&2, M.Node>}
      Equal.cong(List<&2, M.Node>, List<&2, M.Node>, l => List.filter.put(M.Node, M.Node.restrict(x, seen), l, M.has(seen, M.Node.author(x))), M.restrict(M.mark(xs, n, by), seen), M.restrict(xs, seen), restrict_mark(xs, n, by, seen, nb))

def restrict_one(+t: List<&2, M.Node>, +by: Nat, act: M.Action, +seen: List<&2, Nat>, +nb: {M.has(seen, by) == False{} : Bool}) -> {M.restrict(M.one(t, by, act), seen) == M.restrict(t, seen) : List<&2, M.Node>}:
  match act:
    case M.Attach{m, it, pl}:
      restrict_attach(t, M.Node{M.Name{by, m}, it, pl, Nil{}}, seen, nb)
    case M.Delete{target}:
      restrict_mark(t, target, by, seen, nb)

def restrict_apply(acts: List<&2, M.Action>, +t: List<&2, M.Node>, +by: Nat, +seen: List<&2, Nat>, +nb: {M.has(seen, by) == False{} : Bool}) -> {M.restrict(M.apply(acts, t, by), seen) == M.restrict(t, seen) : List<&2, M.Node>}:
  match acts:
    case Nil{}:
      {==}
    case +a <> rest:
      Equal.trans(List<&2, M.Node>, M.restrict(M.apply(rest, M.one(t, by, a), by), seen), M.restrict(M.one(t, by, a), seen), M.restrict(t, seen),
        restrict_apply(rest, M.one(t, by, a), by, seen, nb),
        restrict_one(t, by, a, seen, nb))

# Commuting actions
# -----------------
#
# Actions of two events that had not seen each other: neither deletes what
# the other wrote, so attach and mark commute in every pairing.
def avoid.one(act: M.Action, f: Nat) -> Bool:
  match act:
    case M.Attach{m, it, pl}:
      True{}
    case M.Delete{M.Name{a, m}}:
      Bool.not(Nat.is_eq(f, a))

def avoid(acts: List<&2, M.Action>, +f: Nat) -> Bool:
  match acts:
    case Nil{}:
      True{}
    case a <> rest:
      Bool.and(avoid.one(a, f), avoid(rest, f))

def one_comm(+t: List<&2, M.Node>, +f: Nat, +g: Nat, a: M.Action, b: M.Action, +ne: {Nat.is_eq(f, g) == False{} : Bool}, ta: {avoid.one(a, g) == True{} : Bool}, tb: {avoid.one(b, f) == True{} : Bool}) -> {M.one(M.one(t, f, a), g, b) == M.one(M.one(t, g, b), f, a) : List<&2, M.Node>}:
  match a b:
    case M.Attach{+m, +it, +pl} M.Attach{+m2, +it2, +pl2}:
      attach_comm(t, M.Node{M.Name{f, m}, it, pl, Nil{}}, M.Node{M.Name{g, m2}, it2, pl2, Nil{}}, M.Name.cmp(M.Name{f, m}, M.Name{g, m2}), {==}, name_ne(f, m, g, m2, ne))
    case M.Attach{+m, +it, +pl} M.Delete{M.Name{+a, +m2}}:
      attach_mark(t, M.Node{M.Name{f, m}, it, pl, Nil{}}, M.Name{a, m2}, g, unmarked(f, m, it, pl, Nil{}, a, m2, g, not_of_true(Nat.is_eq(f, a), tb)))
    case M.Delete{M.Name{+a, +m}} M.Attach{+m2, +it, +pl}:
      Equal.sym(List<&2, M.Node>, M.mark(M.attach(t, M.Node{M.Name{g, m2}, it, pl, Nil{}}), M.Name{a, m}, f), M.attach(M.mark(t, M.Name{a, m}, f), M.Node{M.Name{g, m2}, it, pl, Nil{}}),
        attach_mark(t, M.Node{M.Name{g, m2}, it, pl, Nil{}}, M.Name{a, m}, f, unmarked(g, m2, it, pl, Nil{}, a, m, f, not_of_true(Nat.is_eq(g, a), ta))))
    case M.Delete{n1} M.Delete{n2}:
      mark_comm(t, n1, n2, f, g, Nat.cmp(f, g), {==}, ne)

def apply_one(acts: List<&2, M.Action>, +t: List<&2, M.Node>, +f: Nat, +g: Nat, +b: M.Action, +ne: {Nat.is_eq(f, g) == False{} : Bool}, +ta: {avoid(acts, g) == True{} : Bool}, +tb: {avoid.one(b, f) == True{} : Bool}) -> {M.apply(acts, M.one(t, g, b), f) == M.one(M.apply(acts, t, f), g, b) : List<&2, M.Node>}:
  match acts:
    case Nil{}:
      {==}
    case +a <> rest:
      %one_comm(t, f, g, a, b, ne, Comp.and_left(avoid.one(a, g), avoid(rest, g), ta), tb) : {M.apply(rest, _, f) == M.one(M.apply(rest, M.one(t, f, a), f), g, b) : List<&2, M.Node>}
      apply_one(rest, M.one(t, f, a), f, g, b, ne, Comp.and_right(avoid.one(a, g), avoid(rest, g), ta), tb)

def apply_comm(bs: List<&2, M.Action>, +fa: List<&2, M.Action>, +t: List<&2, M.Node>, +f: Nat, +g: Nat, +ne: {Nat.is_eq(f, g) == False{} : Bool}, +ta: {avoid(fa, g) == True{} : Bool}, +tb: {avoid(bs, f) == True{} : Bool}) -> {M.apply(bs, M.apply(fa, t, f), g) == M.apply(fa, M.apply(bs, t, g), f) : List<&2, M.Node>}:
  match bs:
    case Nil{}:
      {==}
    case +b <> rest:
      %apply_one(fa, t, f, g, b, ne, ta, Comp.and_left(avoid.one(b, f), avoid(rest, f), tb)) : {M.apply(rest, _, g) == M.apply(fa, M.apply(rest, M.one(t, g, b), g), f) : List<&2, M.Node>}
      apply_comm(rest, fa, M.one(t, g, b), f, g, ne, ta, Comp.and_right(avoid.one(b, f), avoid(rest, f), tb))

# What an event deletes, it saw
# -----------------------------
#
# A delete's target comes from the view, whose elements were all written by
# events the author had seen; so no action of one event touches an element
# of an event it had not.
def authors_in(ns: List<&2, M.Node>, +seen: List<&2, Nat>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(M.has(seen, M.Node.author(x)), authors_in(rest, seen))

def restrict_author(x: M.Node, seen: List<&2, Nat>) -> {M.Node.author(M.Node.restrict(x, seen)) == M.Node.author(x) : Nat}:
  match x:
    case M.Node{M.Name{a, m}, it, pl, d}:
      {==}

def restrict_authors.at(+x: M.Node, +xs: List<&2, M.Node>, +seen: List<&2, Nat>, h: Bool, eq: {M.has(seen, M.Node.author(x)) == h : Bool}, ih: {authors_in(M.restrict(xs, seen), seen) == True{} : Bool}) -> {authors_in(List.filter.put(M.Node, M.Node.restrict(x, seen), M.restrict(xs, seen), h), seen) == True{} : Bool}:
  match h:
    case True{}:
      %Equal.sym(Nat, M.Node.author(M.Node.restrict(x, seen)), M.Node.author(x), restrict_author(x, seen)) : {Bool.and(M.has(seen, _), authors_in(M.restrict(xs, seen), seen)) == True{} : Bool}
      %Equal.sym(Bool, M.has(seen, M.Node.author(x)), True{}, eq) : {Bool.and(_, authors_in(M.restrict(xs, seen), seen)) == True{} : Bool}
      ih
    case False{}:
      ih

def restrict_authors(t: List<&2, M.Node>, +seen: List<&2, Nat>) -> {authors_in(M.restrict(t, seen), seen) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +x <> +xs:
      restrict_authors.at(x, xs, seen, M.has(seen, M.Node.author(x)), {==}, restrict_authors(xs, seen))

def children_authors.at(+x: M.Node, +xs: List<&2, M.Node>, +seen: List<&2, Nat>, +p: Maybe<&2, M.Name>, +r: Bool, hang: Bool, hx: {M.has(seen, M.Node.author(x)) == True{} : Bool}, ih: {authors_in(M.children(xs, p, r), seen) == True{} : Bool}) -> {authors_in(List.filter.put(M.Node, x, M.children(xs, p, r), hang), seen) == True{} : Bool}:
  match hang:
    case True{}:
      and_intro(M.has(seen, M.Node.author(x)), authors_in(M.children(xs, p, r), seen), hx, ih)
    case False{}:
      ih

def children_authors(t: List<&2, M.Node>, +p: Maybe<&2, M.Name>, +r: Bool, +seen: List<&2, Nat>, +h: {authors_in(t, seen) == True{} : Bool}) -> {authors_in(M.children(t, p, r), seen) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +x <> +xs:
      children_authors.at(x, xs, seen, p, r, M.Node.hangs(x, p, r), Comp.and_left(M.has(seen, M.Node.author(x)), authors_in(xs, seen), h), children_authors(xs, p, r, seen, Comp.and_right(M.has(seen, M.Node.author(x)), authors_in(xs, seen), h)))

def append_authors(a: List<&2, M.Node>, +b: List<&2, M.Node>, +seen: List<&2, Nat>, +ha: {authors_in(a, seen) == True{} : Bool}, hb: {authors_in(b, seen) == True{} : Bool}) -> {authors_in(List.append(&2, M.Node, a, b), seen) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case +x <> +xs:
      and_intro(M.has(seen, M.Node.author(x)), authors_in(List.append(&2, M.Node, xs, b), seen), Comp.and_left(M.has(seen, M.Node.author(x)), authors_in(xs, seen), ha), append_authors(xs, b, seen, Comp.and_right(M.has(seen, M.Node.author(x)), authors_in(xs, seen), ha), hb))

def read_authors(fuel: Nat, +t: List<&2, M.Node>, siblings: List<&2, M.Node>, +seen: List<&2, Nat>, +ht: {authors_in(t, seen) == True{} : Bool}, +hs: {authors_in(siblings, seen) == True{} : Bool}) -> {authors_in(M.read_all(fuel, t, siblings), seen) == True{} : Bool}:
  match fuel:
    case 0n:
      {==}
    case 1n++p:
      match siblings:
        case Nil{}:
          {==}
        case +s <> +rest:
          append_authors(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, False{})), s <> List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), seen,
            read_authors(p, t, M.children(t, Some{M.Node.name(s)}, False{}), seen, ht, children_authors(t, Some{M.Node.name(s)}, False{}, seen, ht)),
            and_intro(M.has(seen, M.Node.author(s)), authors_in(List.append(&2, M.Node, M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest)), seen),
              Comp.and_left(M.has(seen, M.Node.author(s)), authors_in(rest, seen), hs),
              append_authors(M.read_all(p, t, M.children(t, Some{M.Node.name(s)}, True{})), M.read_all(p, t, rest), seen,
                read_authors(p, t, M.children(t, Some{M.Node.name(s)}, True{}), seen, ht, children_authors(t, Some{M.Node.name(s)}, True{}, seen, ht)),
                read_authors(p, t, rest, seen, ht, Comp.and_right(M.has(seen, M.Node.author(s)), authors_in(rest, seen), hs)))))

def standing_authors.at(+x: M.Node, +xs: List<&2, M.Node>, +seen: List<&2, Nat>, up: Bool, hx: {M.has(seen, M.Node.author(x)) == True{} : Bool}, ih: {authors_in(M.standing(xs), seen) == True{} : Bool}) -> {authors_in(List.filter.put(M.Node, x, M.standing(xs), up), seen) == True{} : Bool}:
  match up:
    case True{}:
      and_intro(M.has(seen, M.Node.author(x)), authors_in(M.standing(xs), seen), hx, ih)
    case False{}:
      ih

def standing_authors(ns: List<&2, M.Node>, +seen: List<&2, Nat>, +h: {authors_in(ns, seen) == True{} : Bool}) -> {authors_in(M.standing(ns), seen) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +x <> +xs:
      standing_authors.at(x, xs, seen, M.Node.standing(x), Comp.and_left(M.has(seen, M.Node.author(x)), authors_in(xs, seen), h), standing_authors(xs, seen, Comp.and_right(M.has(seen, M.Node.author(x)), authors_in(xs, seen), h)))

def visible_authors(+t: List<&2, M.Node>, +seen: List<&2, Nat>) -> {authors_in(M.visible(M.restrict(t, seen)), seen) == True{} : Bool}:
  standing_authors(M.order(M.restrict(t, seen)), seen,
    read_authors(1n+List.length(&2, M.Node, M.restrict(t, seen)), M.restrict(t, seen), M.children(M.restrict(t, seen), None{}, True{}), seen, restrict_authors(t, seen),
      children_authors(M.restrict(t, seen), None{}, True{}, seen, restrict_authors(t, seen))))

def ndisc(m: Maybe<&2, M.Node>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some(-x: M.Node, e: {None{} == Some{x} : Maybe<&2, M.Node>}) -> Empty:
  %e : {ndisc(_) : Type}
  Unit{}

def some_node(+y: M.Node, -x: M.Node, e: {Some{y} == Some{x} : Maybe<&2, M.Node>}) -> {y == x : M.Node}:
  Equal.cong(Maybe<&2, M.Node>, M.Node, m => Maybe.default(&2, M.Node, m, y), Some{y}, Some{x}, e)

def get_author(prepare: List<&2, M.Node>, i: Nat, +seen: List<&2, Nat>, +h: {authors_in(prepare, seen) == True{} : Bool}, +x: M.Node, e: {List.get(&2, M.Node, prepare, i) == Some{x} : Maybe<&2, M.Node>}) -> {M.has(seen, M.Node.author(x)) == True{} : Bool}:
  match prepare i:
    case Nil{} _:
      Empty.absurd({M.has(seen, M.Node.author(x)) == True{} : Bool}, none_some(x, e))
    case +y <> ys 0n:
      %some_node(y, x, e) : {M.has(seen, M.Node.author(_)) == True{} : Bool}
      Comp.and_left(M.has(seen, M.Node.author(y)), authors_in(ys, seen), h)
    case y <> ys 1n+p:
      get_author(ys, p, seen, Comp.and_right(M.has(seen, M.Node.author(y)), authors_in(ys, seen), h), x, e)

def ne_of_has.at(+seen: List<&2, Nat>, +f: Nat, +a: Nat, b: Bool, eb: {Nat.is_eq(f, a) == b : Bool}, hf: {M.has(seen, f) == False{} : Bool}, ha: {M.has(seen, a) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, true_false(Equal.trans(Bool, True{}, M.has(seen, f), False{},
        Equal.trans(Bool, True{}, M.has(seen, a), M.has(seen, f), Equal.sym(Bool, M.has(seen, a), True{}, ha), Equal.sym(Bool, M.has(seen, f), M.has(seen, a), Equal.cong(Nat, Bool, n => M.has(seen, n), f, a, nat_eq(f, a, eb)))),
        hf)))

def ne_of_has(+seen: List<&2, Nat>, +f: Nat, +a: Nat, hf: {M.has(seen, f) == False{} : Bool}, ha: {M.has(seen, a) == True{} : Bool}) -> {Nat.is_eq(f, a) == False{} : Bool}:
  ne_of_has.at(seen, f, a, Nat.is_eq(f, a), {==}, hf, ha)

def avoid.m(m: Maybe<&2, List<&2, M.Action>>, f: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{acts}:
      avoid(acts, f)

def not_false(b: Bool, e: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({False{} == True{} : Bool}, true_false(e))

def deletes_avoid.agreed(+a: Nat, +m: Nat, ag: Bool, more: Maybe<&2, List<&2, M.Action>>, +f: Nat, ih: {avoid.m(more, f) == True{} : Bool}, ne: {Nat.is_eq(f, a) == False{} : Bool}) -> {avoid.m(M.deletes.agreed(M.Name{a, m}, more, ag), f) == True{} : Bool}:
  match ag more:
    case False{} _:
      {==}
    case True{} None{}:
      {==}
    case True{} Some{acts}:
      and_intro(Bool.not(Nat.is_eq(f, a)), avoid(acts, f), not_false(Nat.is_eq(f, a), ne), ih)

def deletes_avoid.at(it: Ops.Item, more: Maybe<&2, List<&2, M.Action>>, found: Maybe<&2, M.Node>, +prepare: List<&2, M.Node>, +at: Nat, +seen: List<&2, Nat>, +f: Nat, eq: {List.get(&2, M.Node, prepare, at) == found : Maybe<&2, M.Node>}, hp: {authors_in(prepare, seen) == True{} : Bool}, hf: {M.has(seen, f) == False{} : Bool}, ih: {avoid.m(more, f) == True{} : Bool}) -> {avoid.m(M.deletes.at(it, more, found), f) == True{} : Bool}:
  match found:
    case None{}:
      {==}
    case Some{M.Node{M.Name{+a, +m}, +item, +pl, +d}}:
      deletes_avoid.agreed(a, m, Ops.agrees(it, item), more, f, ih, ne_of_has(seen, f, a, hf, get_author(prepare, at, seen, hp, M.Node{M.Name{a, m}, item, pl, d}, eq)))

def deletes_avoid(items: List<&2, Ops.Item>, +prepare: List<&2, M.Node>, +at: Nat, +seen: List<&2, Nat>, +f: Nat, +hp: {authors_in(prepare, seen) == True{} : Bool}, +hf: {M.has(seen, f) == False{} : Bool}) -> {avoid.m(M.deletes(items, prepare, at), f) == True{} : Bool}:
  match items:
    case Nil{}:
      {==}
    case +it <> +more:
      deletes_avoid.at(it, M.deletes(more, prepare, 1n+at), List.get(&2, M.Node, prepare, at), prepare, at, seen, f, {==}, hp, hf, deletes_avoid(more, prepare, 1n+at, seen, f, hp, hf))

def Inserted.acts(i: M.Inserted) -> List<&2, M.Action>:
  match i:
    case M.Inserted{v, acts, m}:
      acts

def inserts_avoid.of(+minted: Nat, it: Ops.Item, place: M.Place, rest: M.Inserted, +f: Nat, ih: {avoid(Inserted.acts(rest), f) == True{} : Bool}) -> {avoid(Inserted.acts(M.inserts.of(minted, it, place, rest)), f) == True{} : Bool}:
  match rest:
    case M.Inserted{v, acts, m}:
      ih

def inserts_avoid(items: List<&2, Ops.Item>, +v: List<&2, M.Node>, +e: Nat, +left: Maybe<&2, M.Name>, +minted: Nat, +f: Nat) -> {avoid(Inserted.acts(M.inserts(items, v, e, left, minted)), f) == True{} : Bool}:
  match items:
    case Nil{}:
      {==}
    case +it <> +more:
      inserts_avoid.of(minted, it, M.anchor(v, left), M.inserts(more, M.attach(v, M.Node{M.Name{e, minted}, it, M.anchor(v, left), Nil{}}), e, Some{M.Name{e, minted}}, 1n+minted), f,
        inserts_avoid(more, M.attach(v, M.Node{M.Name{e, minted}, it, M.anchor(v, left), Nil{}}), e, Some{M.Name{e, minted}}, 1n+minted, f))

def append_avoid(a: List<&2, M.Action>, +b: List<&2, M.Action>, +f: Nat, +ha: {avoid(a, f) == True{} : Bool}, hb: {avoid(b, f) == True{} : Bool}) -> {avoid(List.append(&2, M.Action, a, b), f) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case +x <> +xs:
      and_intro(avoid.one(x, f), avoid(List.append(&2, M.Action, xs, b), f), Comp.and_left(avoid.one(x, f), avoid(xs, f), ha), append_avoid(xs, b, f, Comp.and_right(avoid.one(x, f), avoid(xs, f), ha), hb))

def avoid.st(st: Maybe<&2, M.Running>, f: Nat) -> Bool:
  match st:
    case None{}:
      True{}
    case Some{M.Running{v, m, acts}}:
      avoid(acts, f)

def step_avoid.deleted(+v: List<&2, M.Node>, m: Nat, +acts: List<&2, M.Action>, new: Maybe<&2, List<&2, M.Action>>, +f: Nat, h0: {avoid(acts, f) == True{} : Bool}, hn: {avoid.m(new, f) == True{} : Bool}) -> {avoid.st(M.run.deleted(v, m, acts, new), f) == True{} : Bool}:
  match new:
    case None{}:
      {==}
    case Some{a}:
      append_avoid(acts, a, f, h0, hn)

def step_avoid.inserted(+acts: List<&2, M.Action>, done: M.Inserted, +f: Nat, h0: {avoid(acts, f) == True{} : Bool}, hn: {avoid(Inserted.acts(done), f) == True{} : Bool}) -> {avoid.st(M.run.inserted(acts, done), f) == True{} : Bool}:
  match done:
    case M.Inserted{v2, new, m2}:
      append_avoid(acts, new, f, h0, hn)

def step_avoid.insert(+items: List<&2, Ops.Item>, +v: List<&2, M.Node>, +e: Nat, +m: Nat, +acts: List<&2, M.Action>, left: Maybe<&2, Maybe<&2, M.Name>>, +f: Nat, h0: {avoid(acts, f) == True{} : Bool}) -> {avoid.st(M.run.insert(items, v, e, m, acts, left), f) == True{} : Bool}:
  match left:
    case None{}:
      {==}
    case Some{+l}:
      step_avoid.inserted(acts, M.inserts(items, v, e, l, m), f, h0, inserts_avoid(items, v, e, l, m, f))

def step_avoid(st: Maybe<&2, M.Running>, op: Ops.Op, +e: Nat, +prepare: List<&2, M.Node>, +seen: List<&2, Nat>, +f: Nat, hp: {authors_in(prepare, seen) == True{} : Bool}, hf: {M.has(seen, f) == False{} : Bool}, h0: {avoid.st(st, f) == True{} : Bool}) -> {avoid.st(M.run.step(st, op, e, prepare), f) == True{} : Bool}:
  match st:
    case None{}:
      {==}
    case Some{M.Running{+v, +m, +acts}}:
      match op:
        case Ops.Op{Ops.Delete{}, +at, +items}:
          step_avoid.deleted(v, m, acts, M.deletes(items, prepare, at), f, h0, deletes_avoid(items, prepare, at, seen, f, hp, hf))
        case Ops.Op{Ops.Insert{}, +at, +items}:
          step_avoid.insert(items, v, e, m, acts, M.left_of(prepare, at), f, h0)

def run_avoid(ops: List<&2, Ops.Op>, +st: Maybe<&2, M.Running>, +e: Nat, +prepare: List<&2, M.Node>, +seen: List<&2, Nat>, +f: Nat, +hp: {authors_in(prepare, seen) == True{} : Bool}, +hf: {M.has(seen, f) == False{} : Bool}, h0: {avoid.st(st, f) == True{} : Bool}) -> {avoid.st(M.run(ops, st, e, prepare), f) == True{} : Bool}:
  match ops:
    case Nil{}:
      h0
    case +op <> rest:
      run_avoid(rest, M.run.step(st, op, e, prepare), e, prepare, seen, f, hp, hf, step_avoid(st, op, e, prepare, seen, f, hp, hf, h0))

def acts_avoid(st: Maybe<&2, M.Running>, +f: Nat, h: {avoid.st(st, f) == True{} : Bool}) -> {avoid.m(M.run.acts(st), f) == True{} : Bool}:
  match st:
    case None{}:
      {==}
    case Some{M.Running{v, m, acts}}:
      h

def actions_avoid(+t: List<&2, M.Node>, +seen: List<&2, Nat>, +e: Nat, +ops: List<&2, Ops.Op>, +f: Nat, hf: {M.has(seen, f) == False{} : Bool}) -> {avoid.m(M.actions(t, seen, e, ops), f) == True{} : Bool}:
  acts_avoid(M.run(ops, Some{M.Running{M.restrict(t, seen), 0n, Nil{}}}, e, M.visible(M.restrict(t, seen))), f,
    run_avoid(ops, Some{M.Running{M.restrict(t, seen), 0n, Nil{}}}, e, M.visible(M.restrict(t, seen)), seen, f, visible_authors(t, seen), hf, {==}))

# Commuting events
# ----------------
#
# Two events that had not seen each other: each decides its actions on a
# view the other's actions leave alone, and the actions commute.
def actions_stable(+t: List<&2, M.Node>, b: List<&2, M.Action>, +x: Nat, +seen: List<&2, Nat>, +f: Nat, +ops: List<&2, Ops.Op>, hx: {M.has(seen, x) == False{} : Bool}) -> {M.actions(M.apply(b, t, x), seen, f, ops) == M.actions(t, seen, f, ops) : Maybe<&2, List<&2, M.Action>>}:
  %Equal.sym(List<&2, M.Node>, M.restrict(M.apply(b, t, x), seen), M.restrict(t, seen), restrict_apply(b, t, x, seen, hx)) : {M.run.acts(M.run(ops, Some{M.Running{_, 0n, Nil{}}}, f, M.visible(_))) == M.actions(t, seen, f, ops) : Maybe<&2, List<&2, M.Action>>}
  {==}

def core(+t: List<&2, M.Node>, +f: Nat, +x: Nat, +sf: List<&2, Nat>, +opsf: List<&2, Ops.Op>, +sx: List<&2, Nat>, +opsx: List<&2, Ops.Op>, ma: Maybe<&2, List<&2, M.Action>>, mb: Maybe<&2, List<&2, M.Action>>, eA: {M.actions(t, sf, f, opsf) == ma : Maybe<&2, List<&2, M.Action>>}, eB: {M.actions(t, sx, x, opsx) == mb : Maybe<&2, List<&2, M.Action>>}, avA: {avoid.m(ma, x) == True{} : Bool}, avB: {avoid.m(mb, f) == True{} : Bool}, +hx: {M.has(sf, x) == False{} : Bool}, +hf: {M.has(sx, f) == False{} : Bool}, ne: {Nat.is_eq(f, x) == False{} : Bool}) -> {M.step.m(M.step.of(t, f, ma), Some{M.Rev{sx, Some{opsx}}}, x) == M.step.m(M.step.of(t, x, mb), Some{M.Rev{sf, Some{opsf}}}, f) : Maybe<&2, List<&2, M.Node>>}:
  match ma mb:
    case None{} None{}:
      {==}
    case None{} Some{b}:
      %Equal.sym(Maybe<&2, List<&2, M.Action>>, M.actions(M.apply(b, t, x), sf, f, opsf), M.actions(t, sf, f, opsf), actions_stable(t, b, x, sf, f, opsf, hx)) : {None{} == M.step.of(M.apply(b, t, x), f, _) : Maybe<&2, List<&2, M.Node>>}
      %Equal.sym(Maybe<&2, List<&2, M.Action>>, M.actions(t, sf, f, opsf), None{}, eA) : {None{} == M.step.of(M.apply(b, t, x), f, _) : Maybe<&2, List<&2, M.Node>>}
      {==}
    case Some{a} None{}:
      %Equal.sym(Maybe<&2, List<&2, M.Action>>, M.actions(M.apply(a, t, f), sx, x, opsx), M.actions(t, sx, x, opsx), actions_stable(t, a, f, sx, x, opsx, hf)) : {M.step.of(M.apply(a, t, f), x, _) == None{} : Maybe<&2, List<&2, M.Node>>}
      %Equal.sym(Maybe<&2, List<&2, M.Action>>, M.actions(t, sx, x, opsx), None{}, eB) : {M.step.of(M.apply(a, t, f), x, _) == None{} : Maybe<&2, List<&2, M.Node>>}
      {==}
    case Some{+a} Some{+b}:
      %Equal.sym(Maybe<&2, List<&2, M.Action>>, M.actions(M.apply(a, t, f), sx, x, opsx), M.actions(t, sx, x, opsx), actions_stable(t, a, f, sx, x, opsx, hf)) : {M.step.of(M.apply(a, t, f), x, _) == M.step.of(M.apply(b, t, x), f, M.actions(M.apply(b, t, x), sf, f, opsf)) : Maybe<&2, List<&2, M.Node>>}
      %Equal.sym(Maybe<&2, List<&2, M.Action>>, M.actions(t, sx, x, opsx), Some{b}, eB) : {M.step.of(M.apply(a, t, f), x, _) == M.step.of(M.apply(b, t, x), f, M.actions(M.apply(b, t, x), sf, f, opsf)) : Maybe<&2, List<&2, M.Node>>}
      %Equal.sym(Maybe<&2, List<&2, M.Action>>, M.actions(M.apply(b, t, x), sf, f, opsf), M.actions(t, sf, f, opsf), actions_stable(t, b, x, sf, f, opsf, hx)) : {Some{M.apply(b, M.apply(a, t, f), x)} == M.step.of(M.apply(b, t, x), f, _) : Maybe<&2, List<&2, M.Node>>}
      %Equal.sym(Maybe<&2, List<&2, M.Action>>, M.actions(t, sf, f, opsf), Some{a}, eA) : {Some{M.apply(b, M.apply(a, t, f), x)} == M.step.of(M.apply(b, t, x), f, _) : Maybe<&2, List<&2, M.Node>>}
      Equal.cong(List<&2, M.Node>, Maybe<&2, List<&2, M.Node>>, l => Some{l}, M.apply(b, M.apply(a, t, f), x), M.apply(a, M.apply(b, t, x), f), apply_comm(b, a, t, f, x, ne, avA, avB))

def step_m_none(m: Maybe<&2, List<&2, M.Node>>, f: Nat) -> {M.step.m(m, None{}, f) == None{} : Maybe<&2, List<&2, M.Node>>}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      {==}

def step_m_nothing(m: Maybe<&2, List<&2, M.Node>>, seen: List<&2, Nat>, f: Nat) -> {M.step.m(m, Some{M.Rev{seen, None{}}}, f) == m : Maybe<&2, List<&2, M.Node>>}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      {==}

def comm(ef: Maybe<&2, M.Rev>, ex: Maybe<&2, M.Rev>, +t: List<&2, M.Node>, +f: Nat, +x: Nat, +hx: {M.has(M.Rev.past(ef), x) == False{} : Bool}, +hf: {M.has(M.Rev.past(ex), f) == False{} : Bool}, ne: {Nat.is_eq(f, x) == False{} : Bool}) -> {M.step.m(M.step(ef, t, f), ex, x) == M.step.m(M.step(ex, t, x), ef, f) : Maybe<&2, List<&2, M.Node>>}:
  match ef ex:
    case None{} _:
      Equal.sym(Maybe<&2, List<&2, M.Node>>, M.step.m(M.step(ex, t, x), None{}, f), None{}, step_m_none(M.step(ex, t, x), f))
    case Some{M.Rev{sf, None{}}} _:
      Equal.sym(Maybe<&2, List<&2, M.Node>>, M.step.m(M.step(ex, t, x), Some{M.Rev{sf, None{}}}, f), M.step(ex, t, x), step_m_nothing(M.step(ex, t, x), sf, f))
    case Some{M.Rev{sf, Some{opsf}}} None{}:
      step_m_none(M.step.of(t, f, M.actions(t, sf, f, opsf)), x)
    case Some{M.Rev{sf, Some{opsf}}} Some{M.Rev{sx, None{}}}:
      step_m_nothing(M.step.of(t, f, M.actions(t, sf, f, opsf)), sx, x)
    case Some{M.Rev{+sf, Some{+opsf}}} Some{M.Rev{+sx, Some{+opsx}}}:
      core(t, f, x, sf, opsf, sx, opsx, M.actions(t, sf, f, opsf), M.actions(t, sx, x, opsx), {==}, {==}, actions_avoid(t, sf, f, opsf, x, hx), actions_avoid(t, sx, x, opsx, f, hf), hx, hf, ne)

def comm.m(mt: Maybe<&2, List<&2, M.Node>>, ef: Maybe<&2, M.Rev>, ex: Maybe<&2, M.Rev>, +f: Nat, +x: Nat, hx: {M.has(M.Rev.past(ef), x) == False{} : Bool}, hf: {M.has(M.Rev.past(ex), f) == False{} : Bool}, ne: {Nat.is_eq(f, x) == False{} : Bool}) -> {M.step.m(M.step.m(mt, ef, f), ex, x) == M.step.m(M.step.m(mt, ex, x), ef, f) : Maybe<&2, List<&2, M.Node>>}:
  match mt:
    case None{}:
      {==}
    case Some{t}:
      comm(ef, ex, t, f, x, hx, hf, ne)

# Orders
# ------
#
# Any causal order is any other with concurrent neighbours swapped: the
# first event of one order is concurrent with everything before it in the
# other, so it bubbles to the front, and the rest is the same graph less
# one event.
def remove.put(x: Nat, xs: List<&2, Nat>, rest: List<&2, Nat>, hit: Bool) -> List<&2, Nat>:
  match hit:
    case True{}:
      xs
    case False{}:
      x <> rest

def remove(o: List<&2, Nat>, +f: Nat) -> List<&2, Nat>:
  match o:
    case Nil{}:
      Nil{}
    case +x <> +xs:
      remove.put(x, xs, remove(xs, f), Nat.is_eq(x, f))

# Everything before `f` in the order is concurrent with it.
def ahead.put(+g: List<&2, M.Rev>, +x: Nat, +f: Nat, rest: Bool, hit: Bool) -> Bool:
  match hit:
    case True{}:
      True{}
    case False{}:
      Bool.and(Bool.not(M.has(M.past(g, f), x)), Bool.and(Bool.not(M.has(M.past(g, x), f)), rest))

def ahead(o: List<&2, Nat>, +g: List<&2, M.Rev>, +f: Nat) -> Bool:
  match o:
    case Nil{}:
      True{}
    case +x <> xs:
      ahead.put(g, x, f, ahead(xs, g, f), Nat.is_eq(x, f))

def or_false_left(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, true_false(e))

def or_false_right(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case False{}:
      e
    case True{}:
      Empty.absurd({b == False{} : Bool}, true_false(e))

def or_left_false(a: Bool, -b: Bool, e: {Bool.or(a, b) == True{} : Bool}, ea: {a == False{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      e
    case True{}:
      Empty.absurd({b == True{} : Bool}, true_false(ea))

def or_right(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def ne_sym(+a: Nat, +b: Nat, e: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  Equal.trans(Bool, Nat.is_eq(b, a), Nat.is_eq(a, b), False{}, is_eq_sym(a, b), e)

def none_known_has.at(+p: List<&2, Nat>, +x: Nat, +xs: List<&2, Nat>, +y: Nat, b: Bool, eb: {Nat.is_eq(x, y) == b : Bool}, nk: {Bool.and(Bool.not(M.has(p, x)), M.none_known(p, xs)) == True{} : Bool}, hy: {Bool.or(b, M.has(xs, y)) == True{} : Bool}, ih: {M.has(xs, y) == True{} : Bool} -> {M.has(p, y) == False{} : Bool}) -> {M.has(p, y) == False{} : Bool}:
  match b:
    case True{}:
      %nat_eq(x, y, eb) : {M.has(p, _) == False{} : Bool}
      not_of_true(M.has(p, x), Comp.and_left(Bool.not(M.has(p, x)), M.none_known(p, xs), nk))
    case False{}:
      ih(hy)

def none_known_has(+p: List<&2, Nat>, l: List<&2, Nat>, +y: Nat, +nk: {M.none_known(p, l) == True{} : Bool}, hy: {M.has(l, y) == True{} : Bool}) -> {M.has(p, y) == False{} : Bool}:
  match l:
    case Nil{}:
      Empty.absurd({M.has(p, y) == False{} : Bool}, Comp.false_true(hy))
    case +x <> +xs:
      none_known_has.at(p, x, xs, y, Nat.is_eq(x, y), {==}, nk, hy, h => none_known_has(p, xs, y, Comp.and_right(Bool.not(M.has(p, x)), M.none_known(p, xs), nk), h))

def subset_nil(o: List<&2, Nat>, e: {M.subset(o, Nil{}) == True{} : Bool}) -> {o == Nil{} : List<&2, Nat>}:
  match o:
    case Nil{}:
      {==}
    case x <> xs:
      Empty.absurd({x <> xs == Nil{} : List<&2, Nat>}, Comp.false_true(e))

def has_remove_other.at(+x: Nat, +xs: List<&2, Nat>, +y: Nat, +f: Nat, hit: Bool, b: Bool, eq: {Nat.is_eq(x, f) == hit : Bool}, eb: {Nat.is_eq(x, y) == b : Bool}, hy: {Bool.or(b, M.has(xs, y)) == True{} : Bool}, ne: {Nat.is_eq(y, f) == False{} : Bool}, ih: {M.has(xs, y) == True{} : Bool} -> {M.has(remove(xs, f), y) == True{} : Bool}) -> {M.has(remove.put(x, xs, remove(xs, f), hit), y) == True{} : Bool}:
  match hit b:
    case True{} True{}:
      Empty.absurd({M.has(xs, y) == True{} : Bool}, true_false(Equal.trans(Bool, True{}, Nat.is_eq(y, f), False{},
        Equal.trans(Bool, True{}, Nat.is_eq(x, f), Nat.is_eq(y, f), Equal.sym(Bool, Nat.is_eq(x, f), True{}, eq), Equal.cong(Nat, Bool, n => Nat.is_eq(n, f), x, y, nat_eq(x, y, eb))),
        ne)))
    case True{} False{}:
      hy
    case False{} True{}:
      %Equal.sym(Bool, Nat.is_eq(x, y), True{}, eb) : {Bool.or(_, M.has(remove(xs, f), y)) == True{} : Bool}
      {==}
    case False{} False{}:
      %Equal.sym(Bool, Nat.is_eq(x, y), False{}, eb) : {Bool.or(_, M.has(remove(xs, f), y)) == True{} : Bool}
      ih(hy)

def has_remove_other(o: List<&2, Nat>, +y: Nat, +f: Nat, hy: {M.has(o, y) == True{} : Bool}, +ne: {Nat.is_eq(y, f) == False{} : Bool}) -> {M.has(remove(o, f), y) == True{} : Bool}:
  match o:
    case Nil{}:
      Empty.absurd({M.has(Nil{}, y) == True{} : Bool}, Comp.false_true(hy))
    case +x <> +xs:
      has_remove_other.at(x, xs, y, f, Nat.is_eq(x, f), Nat.is_eq(x, y), {==}, {==}, hy, ne, h => has_remove_other(xs, y, f, h, ne))

def remove_sub.at(+x: Nat, +xs: List<&2, Nat>, +f: Nat, +y: Nat, hit: Bool, b: Bool, eb: {Nat.is_eq(x, y) == b : Bool}, h: {M.has(remove.put(x, xs, remove(xs, f), hit), y) == True{} : Bool}, ih: {M.has(remove(xs, f), y) == True{} : Bool} -> {M.has(xs, y) == True{} : Bool}) -> {Bool.or(b, M.has(xs, y)) == True{} : Bool}:
  match hit b:
    case True{} True{}:
      {==}
    case True{} False{}:
      h
    case False{} True{}:
      {==}
    case False{} False{}:
      ih(or_left_false(Nat.is_eq(x, y), M.has(remove(xs, f), y), h, eb))

def remove_sub(o: List<&2, Nat>, +f: Nat, +y: Nat, h: {M.has(remove(o, f), y) == True{} : Bool}) -> {M.has(o, y) == True{} : Bool}:
  match o:
    case Nil{}:
      h
    case +x <> +xs:
      remove_sub.at(x, xs, f, y, Nat.is_eq(x, f), Nat.is_eq(x, y), {==}, h, hh => remove_sub(xs, f, y, hh))

def remove_gone.at(+x: Nat, +xs: List<&2, Nat>, +f: Nat, hit: Bool, +eq: {Nat.is_eq(x, f) == hit : Bool}, +d: {Bool.and(Bool.not(M.has(xs, x)), M.distinct(xs)) == True{} : Bool}, ih: {M.distinct(xs) == True{} : Bool} -> {M.has(remove(xs, f), f) == False{} : Bool}) -> {M.has(remove.put(x, xs, remove(xs, f), hit), f) == False{} : Bool}:
  match hit:
    case True{}:
      %nat_eq(x, f, eq) : {M.has(xs, _) == False{} : Bool}
      not_of_true(M.has(xs, x), Comp.and_left(Bool.not(M.has(xs, x)), M.distinct(xs), d))
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(x, f), False{}, eq) : {Bool.or(_, M.has(remove(xs, f), f)) == False{} : Bool}
      ih(Comp.and_right(Bool.not(M.has(xs, x)), M.distinct(xs), d))

def remove_gone(o: List<&2, Nat>, +f: Nat, d: {M.distinct(o) == True{} : Bool}) -> {M.has(remove(o, f), f) == False{} : Bool}:
  match o:
    case Nil{}:
      {==}
    case +x <> +xs:
      remove_gone.at(x, xs, f, Nat.is_eq(x, f), {==}, d, dd => remove_gone(xs, f, dd))

def not_has_remove.at(+xs: List<&2, Nat>, +f: Nat, +x: Nat, b: Bool, eb: {M.has(remove(xs, f), x) == b : Bool}, nx: {M.has(xs, x) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, true_false(Equal.trans(Bool, True{}, M.has(xs, x), False{}, Equal.sym(Bool, M.has(xs, x), True{}, remove_sub(xs, f, x, eb)), nx)))

def not_has_remove(+xs: List<&2, Nat>, +f: Nat, +x: Nat, nx: {M.has(xs, x) == False{} : Bool}) -> {M.has(remove(xs, f), x) == False{} : Bool}:
  not_has_remove.at(xs, f, x, M.has(remove(xs, f), x), {==}, nx)

def distinct_remove.at(+x: Nat, +xs: List<&2, Nat>, +f: Nat, hit: Bool, +d: {Bool.and(Bool.not(M.has(xs, x)), M.distinct(xs)) == True{} : Bool}, ih: {M.distinct(xs) == True{} : Bool} -> {M.distinct(remove(xs, f)) == True{} : Bool}) -> {M.distinct(remove.put(x, xs, remove(xs, f), hit)) == True{} : Bool}:
  match hit:
    case True{}:
      Comp.and_right(Bool.not(M.has(xs, x)), M.distinct(xs), d)
    case False{}:
      and_intro(Bool.not(M.has(remove(xs, f), x)), M.distinct(remove(xs, f)),
        not_false(M.has(remove(xs, f), x), not_has_remove(xs, f, x, not_of_true(M.has(xs, x), Comp.and_left(Bool.not(M.has(xs, x)), M.distinct(xs), d)))),
        ih(Comp.and_right(Bool.not(M.has(xs, x)), M.distinct(xs), d)))

def distinct_remove(o: List<&2, Nat>, +f: Nat, d: {M.distinct(o) == True{} : Bool}) -> {M.distinct(remove(o, f)) == True{} : Bool}:
  match o:
    case Nil{}:
      {==}
    case +x <> +xs:
      distinct_remove.at(x, xs, f, Nat.is_eq(x, f), d, dd => distinct_remove(xs, f, dd))

def subset_remove_other(a: List<&2, Nat>, +o: List<&2, Nat>, +f: Nat, +s: {M.subset(a, o) == True{} : Bool}, +nf: {M.has(a, f) == False{} : Bool}) -> {M.subset(a, remove(o, f)) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case +y <> +ys:
      and_intro(M.has(remove(o, f), y), M.subset(ys, remove(o, f)),
        has_remove_other(o, y, f, Comp.and_left(M.has(o, y), M.subset(ys, o), s), or_false_left(Nat.is_eq(y, f), M.has(ys, f), nf)),
        subset_remove_other(ys, o, f, Comp.and_right(M.has(o, y), M.subset(ys, o), s), or_false_right(Nat.is_eq(y, f), M.has(ys, f), nf)))

def subset_drop(l: List<&2, Nat>, +f: Nat, +a: List<&2, Nat>, +s: {M.subset(l, f <> a) == True{} : Bool}, +nf: {M.has(l, f) == False{} : Bool}) -> {M.subset(l, a) == True{} : Bool}:
  match l:
    case Nil{}:
      {==}
    case +y <> +ys:
      and_intro(M.has(a, y), M.subset(ys, a),
        or_left_false(Nat.is_eq(f, y), M.has(a, y), Comp.and_left(M.has(f <> a, y), M.subset(ys, f <> a), s), ne_sym(y, f, or_false_left(Nat.is_eq(y, f), M.has(ys, f), nf))),
        subset_drop(ys, f, a, Comp.and_right(M.has(f <> a, y), M.subset(ys, f <> a), s), or_false_right(Nat.is_eq(y, f), M.has(ys, f), nf)))

def subset_of_remove.at(+x: Nat, +xs: List<&2, Nat>, +f: Nat, +a: List<&2, Nat>, hit: Bool, +eq: {Nat.is_eq(x, f) == hit : Bool}, +s: {Bool.and(M.has(f <> a, x), M.subset(xs, f <> a)) == True{} : Bool}, +d: {Bool.and(Bool.not(M.has(xs, x)), M.distinct(xs)) == True{} : Bool}, ih: {M.subset(xs, f <> a) == True{} : Bool} -> {M.distinct(xs) == True{} : Bool} -> {M.subset(remove(xs, f), a) == True{} : Bool}) -> {M.subset(remove.put(x, xs, remove(xs, f), hit), a) == True{} : Bool}:
  match hit:
    case True{}:
      subset_drop(xs, f, a, Comp.and_right(M.has(f <> a, x), M.subset(xs, f <> a), s),
        Equal.trans(Bool, M.has(xs, f), M.has(xs, x), False{}, Equal.cong(Nat, Bool, n => M.has(xs, n), f, x, Equal.sym(Nat, x, f, nat_eq(x, f, eq))), not_of_true(M.has(xs, x), Comp.and_left(Bool.not(M.has(xs, x)), M.distinct(xs), d))))
    case False{}:
      and_intro(M.has(a, x), M.subset(remove(xs, f), a),
        or_left_false(Nat.is_eq(f, x), M.has(a, x), Comp.and_left(M.has(f <> a, x), M.subset(xs, f <> a), s), ne_sym(x, f, eq)),
        ih(Comp.and_right(M.has(f <> a, x), M.subset(xs, f <> a), s), Comp.and_right(Bool.not(M.has(xs, x)), M.distinct(xs), d)))

def subset_of_remove(o: List<&2, Nat>, +f: Nat, +a: List<&2, Nat>, s: {M.subset(o, f <> a) == True{} : Bool}, d: {M.distinct(o) == True{} : Bool}) -> {M.subset(remove(o, f), a) == True{} : Bool}:
  match o:
    case Nil{}:
      {==}
    case +x <> +xs:
      subset_of_remove.at(x, xs, f, a, Nat.is_eq(x, f), {==}, s, d, ss => dd => subset_of_remove(xs, f, a, ss, dd))

def none_known_remove.at(+p: List<&2, Nat>, +x: Nat, +xs: List<&2, Nat>, +f: Nat, hit: Bool, +e: {Bool.and(Bool.not(M.has(p, x)), M.none_known(p, xs)) == True{} : Bool}, ih: {M.none_known(p, xs) == True{} : Bool} -> {M.none_known(p, remove(xs, f)) == True{} : Bool}) -> {M.none_known(p, remove.put(x, xs, remove(xs, f), hit)) == True{} : Bool}:
  match hit:
    case True{}:
      Comp.and_right(Bool.not(M.has(p, x)), M.none_known(p, xs), e)
    case False{}:
      and_intro(Bool.not(M.has(p, x)), M.none_known(p, remove(xs, f)), Comp.and_left(Bool.not(M.has(p, x)), M.none_known(p, xs), e), ih(Comp.and_right(Bool.not(M.has(p, x)), M.none_known(p, xs), e)))

def none_known_remove(+p: List<&2, Nat>, l: List<&2, Nat>, +f: Nat, e: {M.none_known(p, l) == True{} : Bool}) -> {M.none_known(p, remove(l, f)) == True{} : Bool}:
  match l:
    case Nil{}:
      {==}
    case +x <> +xs:
      none_known_remove.at(p, x, xs, f, Nat.is_eq(x, f), e, ee => none_known_remove(p, xs, f, ee))

def causal_remove.at(+g: List<&2, M.Rev>, +x: Nat, +xs: List<&2, Nat>, +f: Nat, hit: Bool, +c: {Bool.and(M.none_known(M.past(g, x), xs), M.causal(xs, g)) == True{} : Bool}, ih: {M.causal(xs, g) == True{} : Bool} -> {M.causal(remove(xs, f), g) == True{} : Bool}) -> {M.causal(remove.put(x, xs, remove(xs, f), hit), g) == True{} : Bool}:
  match hit:
    case True{}:
      Comp.and_right(M.none_known(M.past(g, x), xs), M.causal(xs, g), c)
    case False{}:
      and_intro(M.none_known(M.past(g, x), remove(xs, f)), M.causal(remove(xs, f), g),
        none_known_remove(M.past(g, x), xs, f, Comp.and_left(M.none_known(M.past(g, x), xs), M.causal(xs, g), c)),
        ih(Comp.and_right(M.none_known(M.past(g, x), xs), M.causal(xs, g), c)))

def causal_remove(o: List<&2, Nat>, +g: List<&2, M.Rev>, +f: Nat, c: {M.causal(o, g) == True{} : Bool}) -> {M.causal(remove(o, f), g) == True{} : Bool}:
  match o:
    case Nil{}:
      {==}
    case +x <> +xs:
      causal_remove.at(g, x, xs, f, Nat.is_eq(x, f), c, cc => causal_remove(xs, g, f, cc))

def ahead_of.at(+g: List<&2, M.Rev>, +x: Nat, +xs: List<&2, Nat>, +f: Nat, +a: List<&2, Nat>, hit: Bool, +eq: {Nat.is_eq(x, f) == hit : Bool}, +c: {Bool.and(M.none_known(M.past(g, x), xs), M.causal(xs, g)) == True{} : Bool}, +s: {Bool.and(M.has(f <> a, x), M.subset(xs, f <> a)) == True{} : Bool}, +nk: {M.none_known(M.past(g, f), a) == True{} : Bool}, +h: {Bool.or(hit, M.has(xs, f)) == True{} : Bool}, ih: {M.causal(xs, g) == True{} : Bool} -> {M.subset(xs, f <> a) == True{} : Bool} -> {M.has(xs, f) == True{} : Bool} -> {ahead(xs, g, f) == True{} : Bool}) -> {ahead.put(g, x, f, ahead(xs, g, f), hit) == True{} : Bool}:
  match hit:
    case True{}:
      {==}
    case False{}:
      and_intro(Bool.not(M.has(M.past(g, f), x)), Bool.and(Bool.not(M.has(M.past(g, x), f)), ahead(xs, g, f)),
        not_false(M.has(M.past(g, f), x), none_known_has(M.past(g, f), a, x, nk, or_left_false(Nat.is_eq(f, x), M.has(a, x), Comp.and_left(M.has(f <> a, x), M.subset(xs, f <> a), s), ne_sym(x, f, eq)))),
        and_intro(Bool.not(M.has(M.past(g, x), f)), ahead(xs, g, f),
          not_false(M.has(M.past(g, x), f), none_known_has(M.past(g, x), xs, f, Comp.and_left(M.none_known(M.past(g, x), xs), M.causal(xs, g), c), h)),
          ih(Comp.and_right(M.none_known(M.past(g, x), xs), M.causal(xs, g), c), Comp.and_right(M.has(f <> a, x), M.subset(xs, f <> a), s), h)))

def ahead_of(o: List<&2, Nat>, +g: List<&2, M.Rev>, +f: Nat, +a: List<&2, Nat>, c: {M.causal(o, g) == True{} : Bool}, s: {M.subset(o, f <> a) == True{} : Bool}, +nk: {M.none_known(M.past(g, f), a) == True{} : Bool}, h: {M.has(o, f) == True{} : Bool}) -> {ahead(o, g, f) == True{} : Bool}:
  match o:
    case Nil{}:
      {==}
    case +x <> +xs:
      ahead_of.at(g, x, xs, f, a, Nat.is_eq(x, f), {==}, c, s, nk, h, cc => ss => hh => ahead_of(xs, g, f, a, cc, ss, nk, hh))

# The bubble: an order with `f` somewhere ahead of nothing that saw it is
# the order with `f` first.
def bubble.at(+x: Nat, +xs: List<&2, Nat>, +g: List<&2, M.Rev>, +f: Nat, +mt: Maybe<&2, List<&2, M.Node>>, hit: Bool, +eq: {Nat.is_eq(x, f) == hit : Bool}, +a: {ahead.put(g, x, f, ahead(xs, g, f), hit) == True{} : Bool}, +h: {Bool.or(hit, M.has(xs, f)) == True{} : Bool}, ih: @m: Maybe<&2, List<&2, M.Node>> -> {ahead(xs, g, f) == True{} : Bool} -> {M.has(xs, f) == True{} : Bool} -> {M.walk(xs, g, m) == M.walk(f <> remove(xs, f), g, m) : Maybe<&2, List<&2, M.Node>>}) -> {M.walk(x <> xs, g, mt) == M.walk(f <> remove.put(x, xs, remove(xs, f), hit), g, mt) : Maybe<&2, List<&2, M.Node>>}:
  match hit:
    case True{}:
      %nat_eq(x, f, eq) : {M.walk(x <> xs, g, mt) == M.walk(_ <> xs, g, mt) : Maybe<&2, List<&2, M.Node>>}
      {==}
    case False{}:
      Equal.trans(Maybe<&2, List<&2, M.Node>>, M.walk(x <> xs, g, mt), M.walk(f <> remove(xs, f), g, M.step.m(mt, List.get(&2, M.Rev, g, x), x)), M.walk(f <> x <> remove(xs, f), g, mt),
        ih(M.step.m(mt, List.get(&2, M.Rev, g, x), x), Comp.and_right(Bool.not(M.has(M.past(g, x), f)), ahead(xs, g, f), Comp.and_right(Bool.not(M.has(M.past(g, f), x)), Bool.and(Bool.not(M.has(M.past(g, x), f)), ahead(xs, g, f)), a)), h),
        Equal.cong(Maybe<&2, List<&2, M.Node>>, Maybe<&2, List<&2, M.Node>>, m => M.walk(remove(xs, f), g, m), M.step.m(M.step.m(mt, List.get(&2, M.Rev, g, x), x), List.get(&2, M.Rev, g, f), f), M.step.m(M.step.m(mt, List.get(&2, M.Rev, g, f), f), List.get(&2, M.Rev, g, x), x),
          comm.m(mt, List.get(&2, M.Rev, g, x), List.get(&2, M.Rev, g, f), x, f,
            not_of_true(M.has(M.past(g, x), f), Comp.and_left(Bool.not(M.has(M.past(g, x), f)), ahead(xs, g, f), Comp.and_right(Bool.not(M.has(M.past(g, f), x)), Bool.and(Bool.not(M.has(M.past(g, x), f)), ahead(xs, g, f)), a))),
            not_of_true(M.has(M.past(g, f), x), Comp.and_left(Bool.not(M.has(M.past(g, f), x)), Bool.and(Bool.not(M.has(M.past(g, x), f)), ahead(xs, g, f)), a)),
            eq)))

def bubble(o: List<&2, Nat>, +g: List<&2, M.Rev>, +f: Nat, +mt: Maybe<&2, List<&2, M.Node>>, a: {ahead(o, g, f) == True{} : Bool}, h: {M.has(o, f) == True{} : Bool}) -> {M.walk(o, g, mt) == M.walk(f <> remove(o, f), g, mt) : Maybe<&2, List<&2, M.Node>>}:
  match o:
    case Nil{}:
      Empty.absurd({mt == M.walk(f <> Nil{}, g, mt) : Maybe<&2, List<&2, M.Node>>}, Comp.false_true(h))
    case +x <> +xs:
      bubble.at(x, xs, g, f, mt, Nat.is_eq(x, f), {==}, a, h, m => aa => hh => bubble(xs, g, f, m, aa, hh))

# The theorem
# -----------

def converge(o1: List<&2, Nat>, +g: List<&2, M.Rev>, +o2: List<&2, Nat>, +mt: Maybe<&2, List<&2, M.Node>>, +d1: {M.distinct(o1) == True{} : Bool}, +d2: {M.distinct(o2) == True{} : Bool}, +s12: {M.subset(o1, o2) == True{} : Bool}, +s21: {M.subset(o2, o1) == True{} : Bool}, +c1: {M.causal(o1, g) == True{} : Bool}, +c2: {M.causal(o2, g) == True{} : Bool}) -> {M.walk(o1, g, mt) == M.walk(o2, g, mt) : Maybe<&2, List<&2, M.Node>>}:
  match o1:
    case Nil{}:
      %Equal.sym(List<&2, Nat>, o2, Nil{}, subset_nil(o2, s21)) : {mt == M.walk(_, g, mt) : Maybe<&2, List<&2, M.Node>>}
      {==}
    case +f <> +o1:
      Equal.trans(Maybe<&2, List<&2, M.Node>>, M.walk(f <> o1, g, mt), M.walk(f <> remove(o2, f), g, mt), M.walk(o2, g, mt),
        converge(o1, g, remove(o2, f), M.step.m(mt, List.get(&2, M.Rev, g, f), f),
          Comp.and_right(Bool.not(M.has(o1, f)), M.distinct(o1), d1),
          distinct_remove(o2, f, d2),
          subset_remove_other(o1, o2, f, Comp.and_right(M.has(o2, f), M.subset(o1, o2), s12), not_of_true(M.has(o1, f), Comp.and_left(Bool.not(M.has(o1, f)), M.distinct(o1), d1))),
          subset_of_remove(o2, f, o1, s21, d2),
          Comp.and_right(M.none_known(M.past(g, f), o1), M.causal(o1, g), c1),
          causal_remove(o2, g, f, c2)),
        Equal.sym(Maybe<&2, List<&2, M.Node>>, M.walk(o2, g, mt), M.walk(f <> remove(o2, f), g, mt),
          bubble(o2, g, f, mt,
            ahead_of(o2, g, f, o1, c2, s21, Comp.and_left(M.none_known(M.past(g, f), o1), M.causal(o1, g), c1), Comp.and_left(M.has(o2, f), M.subset(o1, o2), s12)),
            Comp.and_left(M.has(o2, f), M.subset(o1, o2), s12))))

# Stated over the graph's validity predicate and the merged file.
def merge_converges(+g: List<&2, M.Rev>, +a: List<&2, Nat>, +b: List<&2, Nat>, +e: {M.orders(g, a, b) == True{} : Bool}) -> {M.merged(g, a) == M.merged(g, b) : Maybe<&2, List<&2, Ops.Item>>}:
  Equal.cong(Maybe<&2, List<&2, M.Node>>, Maybe<&2, List<&2, Ops.Item>>, m => M.merged.of(m), M.walk(a, g, Some{Nil{}}), M.walk(b, g, Some{Nil{}}),
    converge(a, g, b, Some{Nil{}},
      Comp.and_left(M.distinct(a), Bool.and(M.distinct(b), Bool.and(M.subset(a, b), Bool.and(M.subset(b, a), Bool.and(M.causal(a, g), M.causal(b, g))))), e),
      Comp.and_left(M.distinct(b), Bool.and(M.subset(a, b), Bool.and(M.subset(b, a), Bool.and(M.causal(a, g), M.causal(b, g)))), Comp.and_right(M.distinct(a), Bool.and(M.distinct(b), Bool.and(M.subset(a, b), Bool.and(M.subset(b, a), Bool.and(M.causal(a, g), M.causal(b, g))))), e)),
      Comp.and_left(M.subset(a, b), Bool.and(M.subset(b, a), Bool.and(M.causal(a, g), M.causal(b, g))), Comp.and_right(M.distinct(b), Bool.and(M.subset(a, b), Bool.and(M.subset(b, a), Bool.and(M.causal(a, g), M.causal(b, g)))), Comp.and_right(M.distinct(a), Bool.and(M.distinct(b), Bool.and(M.subset(a, b), Bool.and(M.subset(b, a), Bool.and(M.causal(a, g), M.causal(b, g))))), e))),
      Comp.and_left(M.subset(b, a), Bool.and(M.causal(a, g), M.causal(b, g)), Comp.and_right(M.subset(a, b), Bool.and(M.subset(b, a), Bool.and(M.causal(a, g), M.causal(b, g))), Comp.and_right(M.distinct(b), Bool.and(M.subset(a, b), Bool.and(M.subset(b, a), Bool.and(M.causal(a, g), M.causal(b, g)))), Comp.and_right(M.distinct(a), Bool.and(M.distinct(b), Bool.and(M.subset(a, b), Bool.and(M.subset(b, a), Bool.and(M.causal(a, g), M.causal(b, g))))), e)))),
      Comp.and_left(M.causal(a, g), M.causal(b, g), Comp.and_right(M.subset(b, a), Bool.and(M.causal(a, g), M.causal(b, g)), Comp.and_right(M.subset(a, b), Bool.and(M.subset(b, a), Bool.and(M.causal(a, g), M.causal(b, g))), Comp.and_right(M.distinct(b), Bool.and(M.subset(a, b), Bool.and(M.subset(b, a), Bool.and(M.causal(a, g), M.causal(b, g)))), Comp.and_right(M.distinct(a), Bool.and(M.distinct(b), Bool.and(M.subset(a, b), Bool.and(M.subset(b, a), Bool.and(M.causal(a, g), M.causal(b, g))))), e))))),
      Comp.and_right(M.causal(a, g), M.causal(b, g), Comp.and_right(M.subset(b, a), Bool.and(M.causal(a, g), M.causal(b, g)), Comp.and_right(M.subset(a, b), Bool.and(M.subset(b, a), Bool.and(M.causal(a, g), M.causal(b, g))), Comp.and_right(M.distinct(b), Bool.and(M.subset(a, b), Bool.and(M.subset(b, a), Bool.and(M.causal(a, g), M.causal(b, g)))), Comp.and_right(M.distinct(a), Bool.and(M.distinct(b), Bool.and(M.subset(a, b), Bool.and(M.subset(b, a), Bool.and(M.causal(a, g), M.causal(b, g))))), e)))))))

# A merge revision that records nothing changes nothing
# -----------------------------------------------------
#
# An event with no document, walked last, leaves the file the events
# before it made: `historica merge` on one head, or a merge recorded with
# nothing said about this file.

def lt_zero(e: Nat, l: {Nat.is_lt(e, 0n) == True{} : Bool}) -> Empty:
  match e:
    case 0n:
      Comp.false_true(l)
    case 1n+p:
      Comp.false_true(l)

def get_append(g: List<&2, M.Rev>, x: M.Rev, e: Nat, l: {Nat.is_lt(e, List.length(&2, M.Rev, g)) == True{} : Bool}) -> {List.get(&2, M.Rev, List.append(&2, M.Rev, g, [x]), e) == List.get(&2, M.Rev, g, e) : Maybe<&2, M.Rev>}:
  match g:
    case Nil{}:
      Empty.absurd({List.get(&2, M.Rev, [x], e) == List.get(&2, M.Rev, Nil{}, e) : Maybe<&2, M.Rev>}, lt_zero(e, l))
    case h <> t:
      match e:
        case 0n:
          {==}
        case 1n+p:
          get_append(t, x, p, l)

def get_last(g: List<&2, M.Rev>, x: M.Rev) -> {List.get(&2, M.Rev, List.append(&2, M.Rev, g, [x]), List.length(&2, M.Rev, g)) == Some{x} : Maybe<&2, M.Rev>}:
  match g:
    case Nil{}:
      {==}
    case h <> t:
      get_last(t, x)

def walk_append(o: List<&2, Nat>, +e: Nat, +g: List<&2, M.Rev>, mt: Maybe<&2, List<&2, M.Node>>) -> {M.walk(List.append(&2, Nat, o, [e]), g, mt) == M.step.m(M.walk(o, g, mt), List.get(&2, M.Rev, g, e), e) : Maybe<&2, List<&2, M.Node>>}:
  match o:
    case Nil{}:
      {==}
    case +x <> rest:
      walk_append(rest, e, g, M.step.m(mt, List.get(&2, M.Rev, g, x), x))

def walk_below(o: List<&2, Nat>, +g: List<&2, M.Rev>, +x: M.Rev, mt: Maybe<&2, List<&2, M.Node>>, +b: {M.below(o, List.length(&2, M.Rev, g)) == True{} : Bool}) -> {M.walk(o, List.append(&2, M.Rev, g, [x]), mt) == M.walk(o, g, mt) : Maybe<&2, List<&2, M.Node>>}:
  match o:
    case Nil{}:
      {==}
    case +i <> +rest:
      %Equal.sym(Maybe<&2, M.Rev>, List.get(&2, M.Rev, List.append(&2, M.Rev, g, [x]), i), List.get(&2, M.Rev, g, i), get_append(g, x, i, Comp.and_left(Nat.is_lt(i, List.length(&2, M.Rev, g)), M.below(rest, List.length(&2, M.Rev, g)), b))) : {M.walk(rest, List.append(&2, M.Rev, g, [x]), M.step.m(mt, _, i)) == M.walk(rest, g, M.step.m(mt, List.get(&2, M.Rev, g, i), i)) : Maybe<&2, List<&2, M.Node>>}
      walk_below(rest, g, x, M.step.m(mt, List.get(&2, M.Rev, g, i), i), Comp.and_right(Nat.is_lt(i, List.length(&2, M.Rev, g)), M.below(rest, List.length(&2, M.Rev, g)), b))

def step_none(mt: Maybe<&2, List<&2, M.Node>>, past: List<&2, Nat>, e: Nat) -> {M.step.m(mt, Some{M.Rev{past, None{}}}, e) == mt : Maybe<&2, List<&2, M.Node>>}:
  match mt:
    case None{}:
      {==}
    case Some{t}:
      {==}

def merge_records_nothing(+g: List<&2, M.Rev>, +o: List<&2, Nat>, +past: List<&2, Nat>, b: {M.below(o, List.length(&2, M.Rev, g)) == True{} : Bool}) -> {M.merged(List.append(&2, M.Rev, g, [M.Rev{past, None{}}]), List.append(&2, Nat, o, [List.length(&2, M.Rev, g)])) == M.merged(g, o) : Maybe<&2, List<&2, Ops.Item>>}:
  %Equal.sym(Maybe<&2, List<&2, M.Node>>, M.walk(List.append(&2, Nat, o, [List.length(&2, M.Rev, g)]), List.append(&2, M.Rev, g, [M.Rev{past, None{}}]), Some{Nil{}}), M.step.m(M.walk(o, List.append(&2, M.Rev, g, [M.Rev{past, None{}}]), Some{Nil{}}), List.get(&2, M.Rev, List.append(&2, M.Rev, g, [M.Rev{past, None{}}]), List.length(&2, M.Rev, g)), List.length(&2, M.Rev, g)), walk_append(o, List.length(&2, M.Rev, g), List.append(&2, M.Rev, g, [M.Rev{past, None{}}]), Some{Nil{}})) : {M.merged.of(_) == M.merged.of(M.walk(o, g, Some{Nil{}})) : Maybe<&2, List<&2, Ops.Item>>}
  %Equal.sym(Maybe<&2, M.Rev>, List.get(&2, M.Rev, List.append(&2, M.Rev, g, [M.Rev{past, None{}}]), List.length(&2, M.Rev, g)), Some{M.Rev{past, None{}}}, get_last(g, M.Rev{past, None{}})) : {M.merged.of(M.step.m(M.walk(o, List.append(&2, M.Rev, g, [M.Rev{past, None{}}]), Some{Nil{}}), _, List.length(&2, M.Rev, g))) == M.merged.of(M.walk(o, g, Some{Nil{}})) : Maybe<&2, List<&2, Ops.Item>>}
  %Equal.sym(Maybe<&2, List<&2, M.Node>>, M.step.m(M.walk(o, List.append(&2, M.Rev, g, [M.Rev{past, None{}}]), Some{Nil{}}), Some{M.Rev{past, None{}}}, List.length(&2, M.Rev, g)), M.walk(o, List.append(&2, M.Rev, g, [M.Rev{past, None{}}]), Some{Nil{}}), step_none(M.walk(o, List.append(&2, M.Rev, g, [M.Rev{past, None{}}]), Some{Nil{}}), past, List.length(&2, M.Rev, g))) : {M.merged.of(_) == M.merged.of(M.walk(o, g, Some{Nil{}})) : Maybe<&2, List<&2, Ops.Item>>}
  %Equal.sym(Maybe<&2, List<&2, M.Node>>, M.walk(o, List.append(&2, M.Rev, g, [M.Rev{past, None{}}]), Some{Nil{}}), M.walk(o, g, Some{Nil{}}), walk_below(o, g, M.Rev{past, None{}}, Some{Nil{}}, b)) : {M.merged.of(_) == M.merged.of(M.walk(o, g, Some{Nil{}})) : Maybe<&2, List<&2, Ops.Item>>}
  {==}

def main() -> Unit:
  Unit{}
