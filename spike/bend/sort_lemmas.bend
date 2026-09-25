# Sorting by a name. Strings are ordered totally — the comparison of two
# is the other read backwards, and an order no larger than another no larger
# than a third is no larger than that — so a sort by a name puts every item
# where it belongs.
import Base
import ./string_lemmas.bend as S
import ./position_lemmas.bend as Pos
import ./composition_lemmas.bend as Comp

# The order of strings
# --------------------

def cflip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

def bool_flip(a: Bool, b: Bool) -> {Bool.cmp(b, a) == cflip(Bool.cmp(a, b)) : Cmp}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def fin_flip(+a: Bool, +b: Bool, c: Cmp) -> {Word.cmp.fin(b, a, cflip(c)) == cflip(Word.cmp.fin(a, b, c)) : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      bool_flip(a, b)
    case GT{}:
      {==}

def word_flip(n: Nat, a: Word(n), b: Word(n)) -> {Word.cmp(n, b, a) == cflip(Word.cmp(n, a, b)) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          %Equal.sym(Cmp, Word.cmp(p, bt, at), cflip(Word.cmp(p, at, bt)), word_flip(p, at, bt)) : {Word.cmp.fin(bb, ab, _) == cflip(Word.cmp.fin(ab, bb, Word.cmp(p, at, bt))) : Cmp}
          fin_flip(ab, bb, Word.cmp(p, at, bt))

def cmp_flip_eq(-x: Cmp, c: Cmp, +y: Cmp, ex: {x == cflip(c) : Cmp}, ec: {c == y : Cmp}) -> {x == cflip(y) : Cmp}:
  %ec : {x == cflip(_) : Cmp}
  ex

def str_flip.fin(c: Cmp, +w1: Word(32n), +w2: Word(32n), +t1: String, +t2: String, ew: {Word.cmp(32n, w1, w2) == c : Cmp}, ih: {String.order(t2, t1) == cflip(String.order(t1, t2)) : Cmp}) -> {String.order.fin(String.cmp.fin(t2, t1, ((Chr{U32{w2}}, Chr{U32{w1}}), Word.cmp(32n, w2, w1)))) == cflip(String.order.fin(String.cmp.fin(t1, t2, ((Chr{U32{w1}}, Chr{U32{w2}}), c)))) : Cmp}:
  match c:
    case LT{}:
      %Equal.sym(Cmp, Word.cmp(32n, w2, w1), GT{}, cmp_flip_eq(Word.cmp(32n, w2, w1), Word.cmp(32n, w1, w2), LT{}, word_flip(32n, w1, w2), ew)) : {String.order.fin(String.cmp.fin(t2, t1, ((Chr{U32{w2}}, Chr{U32{w1}}), _))) == GT{} : Cmp}
      {==}
    case GT{}:
      %Equal.sym(Cmp, Word.cmp(32n, w2, w1), LT{}, cmp_flip_eq(Word.cmp(32n, w2, w1), Word.cmp(32n, w1, w2), GT{}, word_flip(32n, w1, w2), ew)) : {String.order.fin(String.cmp.fin(t2, t1, ((Chr{U32{w2}}, Chr{U32{w1}}), _))) == LT{} : Cmp}
      {==}
    case EQ{}:
      %Equal.sym(Cmp, Word.cmp(32n, w2, w1), EQ{}, cmp_flip_eq(Word.cmp(32n, w2, w1), Word.cmp(32n, w1, w2), EQ{}, word_flip(32n, w1, w2), ew)) : {String.order.fin(String.cmp.fin(t2, t1, ((Chr{U32{w2}}, Chr{U32{w1}}), _))) == cflip(String.order.fin(String.cmp.rec(Chr{U32{w1}}, Chr{U32{w2}}, String.cmp(t1, t2)))) : Cmp}
      %Equal.sym(Cmp, String.order.fin(String.cmp.rec(Chr{U32{w2}}, Chr{U32{w1}}, String.cmp(t2, t1))), String.order.fin(String.cmp(t2, t1)), S.rec_order(Chr{U32{w2}}, Chr{U32{w1}}, String.cmp(t2, t1))) : {_ == cflip(String.order.fin(String.cmp.rec(Chr{U32{w1}}, Chr{U32{w2}}, String.cmp(t1, t2)))) : Cmp}
      %Equal.sym(Cmp, String.order.fin(String.cmp.rec(Chr{U32{w1}}, Chr{U32{w2}}, String.cmp(t1, t2))), String.order.fin(String.cmp(t1, t2)), S.rec_order(Chr{U32{w1}}, Chr{U32{w2}}, String.cmp(t1, t2))) : {String.order(t2, t1) == cflip(_) : Cmp}
      ih

# The order of two strings is the other's, read backwards.
def str_flip(a: String, b: String) -> {String.order(b, a) == cflip(String.order(a, b)) : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      {==}
    case SCon{h, t} SNil{}:
      {==}
    case SCon{Chr{U32{+w1}}, +t1} SCon{Chr{U32{+w2}}, +t2}:
      str_flip.fin(Word.cmp(32n, w1, w2), w1, w2, t1, t2, {==}, str_flip(t1, t2))

def lt_not(-x: Cmp, e: {x == LT{} : Cmp}, ne: {Cmp.is_lt(x) == False{} : Bool}) -> Empty:
  S.false_true(Equal.trans(Bool, False{}, Cmp.is_lt(x), True{}, Equal.sym(Bool, Cmp.is_lt(x), False{}, ne), Equal.cong(Cmp, Bool, Cmp.is_lt, x, LT{}, e)))

def bits_lt(bb: Bool, ab: Bool, cb: Bool, e1: {Bool.cmp(ab, bb) == LT{} : Cmp}, e2: {Bool.cmp(bb, cb) == LT{} : Cmp}) -> Empty:
  match bb:
    case False{}:
      match ab:
        case False{}:
          lt_not(EQ{}, e1, {==})
        case True{}:
          lt_not(GT{}, e1, {==})
    case True{}:
      match cb:
        case False{}:
          lt_not(GT{}, e2, {==})
        case True{}:
          lt_not(EQ{}, e2, {==})

def wlt.fin(t1: Cmp, t2: Cmp, +ab: Bool, +bb: Bool, +cb: Bool, +p: Nat, +at: Word(p), +bt: Word(p), +ct: Word(p), et1: {Word.cmp(p, at, bt) == t1 : Cmp}, et2: {Word.cmp(p, bt, ct) == t2 : Cmp}, e1: {Word.cmp.fin(ab, bb, t1) == LT{} : Cmp}, e2: {Word.cmp.fin(bb, cb, t2) == LT{} : Cmp}, ih: {Word.cmp(p, at, bt) == LT{} : Cmp} -> {Word.cmp(p, bt, ct) == LT{} : Cmp} -> {Word.cmp(p, at, ct) == LT{} : Cmp}) -> {Word.cmp.fin(ab, cb, Word.cmp(p, at, ct)) == LT{} : Cmp}:
  match t1 t2:
    case LT{} LT{}:
      %Equal.sym(Cmp, Word.cmp(p, at, ct), LT{}, ih(et1, et2)) : {Word.cmp.fin(ab, cb, _) == LT{} : Cmp}
      {==}
    case LT{} EQ{}:
      %S.word_eq(p, bt, ct, et2) : {Word.cmp.fin(ab, cb, Word.cmp(p, at, _)) == LT{} : Cmp}
      %Equal.sym(Cmp, Word.cmp(p, at, bt), LT{}, et1) : {Word.cmp.fin(ab, cb, _) == LT{} : Cmp}
      {==}
    case LT{} GT{}:
      Empty.absurd({Word.cmp.fin(ab, cb, Word.cmp(p, at, ct)) == LT{} : Cmp}, lt_not(GT{}, e2, {==}))
    case EQ{} LT{}:
      %Equal.sym(Word(p), at, bt, S.word_eq(p, at, bt, et1)) : {Word.cmp.fin(ab, cb, Word.cmp(p, _, ct)) == LT{} : Cmp}
      %Equal.sym(Cmp, Word.cmp(p, bt, ct), LT{}, et2) : {Word.cmp.fin(ab, cb, _) == LT{} : Cmp}
      {==}
    case EQ{} EQ{}:
      Empty.absurd({Word.cmp.fin(ab, cb, Word.cmp(p, at, ct)) == LT{} : Cmp}, bits_lt(bb, ab, cb, e1, e2))
    case EQ{} GT{}:
      Empty.absurd({Word.cmp.fin(ab, cb, Word.cmp(p, at, ct)) == LT{} : Cmp}, lt_not(GT{}, e2, {==}))
    case GT{} LT{}:
      Empty.absurd({Word.cmp.fin(ab, cb, Word.cmp(p, at, ct)) == LT{} : Cmp}, lt_not(GT{}, e1, {==}))
    case GT{} EQ{}:
      Empty.absurd({Word.cmp.fin(ab, cb, Word.cmp(p, at, ct)) == LT{} : Cmp}, lt_not(GT{}, e1, {==}))
    case GT{} GT{}:
      Empty.absurd({Word.cmp.fin(ab, cb, Word.cmp(p, at, ct)) == LT{} : Cmp}, lt_not(GT{}, e1, {==}))

def word_lt(n: Nat, a: Word(n), b: Word(n), c: Word(n), e1: {Word.cmp(n, a, b) == LT{} : Cmp}, e2: {Word.cmp(n, b, c) == LT{} : Cmp}) -> {Word.cmp(n, a, c) == LT{} : Cmp}:
  match n:
    case 0n:
      Empty.absurd({EQ{} == LT{} : Cmp}, lt_not(EQ{}, e1, {==}))
    case 1n++p:
      match a b c:
        case WCon{+ab, +at} WCon{+bb, +bt} WCon{+cb, +ct}:
          wlt.fin(Word.cmp(p, at, bt), Word.cmp(p, bt, ct), ab, bb, cb, p, at, bt, ct, {==}, {==}, e1, e2, x => y => word_lt(p, at, bt, ct, x, y))

def le_not(-x: Cmp, e: {Cmp.is_le(x) == True{} : Bool}, ne: {Cmp.is_le(x) == False{} : Bool}) -> Empty:
  S.false_true(Equal.trans(Bool, False{}, Cmp.is_le(x), True{}, Equal.sym(Bool, Cmp.is_le(x), False{}, ne), e))

def str_le.fin(c1: Cmp, c2: Cmp, +wa: Word(32n), +wb: Word(32n), +wc: Word(32n), +ta: String, +tb: String, +tc: String, e1: {Word.cmp(32n, wa, wb) == c1 : Cmp}, e2: {Word.cmp(32n, wb, wc) == c2 : Cmp}, h1: {Cmp.is_le(String.order.fin(String.cmp.fin(ta, tb, ((Chr{U32{wa}}, Chr{U32{wb}}), c1)))) == True{} : Bool}, h2: {Cmp.is_le(String.order.fin(String.cmp.fin(tb, tc, ((Chr{U32{wb}}, Chr{U32{wc}}), c2)))) == True{} : Bool}, ih: {Cmp.is_le(String.order(ta, tb)) == True{} : Bool} -> {Cmp.is_le(String.order(tb, tc)) == True{} : Bool} -> {Cmp.is_le(String.order(ta, tc)) == True{} : Bool}) -> {Cmp.is_le(String.order.fin(String.cmp.fin(ta, tc, ((Chr{U32{wa}}, Chr{U32{wc}}), Word.cmp(32n, wa, wc))))) == True{} : Bool}:
  match c1 c2:
    case LT{} LT{}:
      %Equal.sym(Cmp, Word.cmp(32n, wa, wc), LT{}, word_lt(32n, wa, wb, wc, e1, e2)) : {Cmp.is_le(String.order.fin(String.cmp.fin(ta, tc, ((Chr{U32{wa}}, Chr{U32{wc}}), _)))) == True{} : Bool}
      {==}
    case LT{} EQ{}:
      %S.word_eq(32n, wb, wc, e2) : {Cmp.is_le(String.order.fin(String.cmp.fin(ta, tc, ((Chr{U32{wa}}, Chr{U32{wc}}), Word.cmp(32n, wa, _))))) == True{} : Bool}
      %Equal.sym(Cmp, Word.cmp(32n, wa, wb), LT{}, e1) : {Cmp.is_le(String.order.fin(String.cmp.fin(ta, tc, ((Chr{U32{wa}}, Chr{U32{wc}}), _)))) == True{} : Bool}
      {==}
    case EQ{} LT{}:
      %Equal.sym(Word(32n), wa, wb, S.word_eq(32n, wa, wb, e1)) : {Cmp.is_le(String.order.fin(String.cmp.fin(ta, tc, ((Chr{U32{wa}}, Chr{U32{wc}}), Word.cmp(32n, _, wc))))) == True{} : Bool}
      %Equal.sym(Cmp, Word.cmp(32n, wb, wc), LT{}, e2) : {Cmp.is_le(String.order.fin(String.cmp.fin(ta, tc, ((Chr{U32{wa}}, Chr{U32{wc}}), _)))) == True{} : Bool}
      {==}
    case EQ{} EQ{}:
      %S.word_eq(32n, wb, wc, e2) : {Cmp.is_le(String.order.fin(String.cmp.fin(ta, tc, ((Chr{U32{wa}}, Chr{U32{wc}}), Word.cmp(32n, wa, _))))) == True{} : Bool}
      %Equal.sym(Cmp, Word.cmp(32n, wa, wb), EQ{}, e1) : {Cmp.is_le(String.order.fin(String.cmp.fin(ta, tc, ((Chr{U32{wa}}, Chr{U32{wc}}), _)))) == True{} : Bool}
      %Equal.sym(Cmp, String.order.fin(String.cmp.rec(Chr{U32{wa}}, Chr{U32{wc}}, String.cmp(ta, tc))), String.order(ta, tc), S.rec_order(Chr{U32{wa}}, Chr{U32{wc}}, String.cmp(ta, tc))) : {Cmp.is_le(_) == True{} : Bool}
      ih(Equal.trans(Bool, Cmp.is_le(String.order(ta, tb)), Cmp.is_le(String.order.fin(String.cmp.rec(Chr{U32{wa}}, Chr{U32{wb}}, String.cmp(ta, tb)))), True{}, Equal.cong(Cmp, Bool, Cmp.is_le, String.order(ta, tb), String.order.fin(String.cmp.rec(Chr{U32{wa}}, Chr{U32{wb}}, String.cmp(ta, tb))), Equal.sym(Cmp, String.order.fin(String.cmp.rec(Chr{U32{wa}}, Chr{U32{wb}}, String.cmp(ta, tb))), String.order(ta, tb), S.rec_order(Chr{U32{wa}}, Chr{U32{wb}}, String.cmp(ta, tb)))), h1),
        Equal.trans(Bool, Cmp.is_le(String.order(tb, tc)), Cmp.is_le(String.order.fin(String.cmp.rec(Chr{U32{wb}}, Chr{U32{wc}}, String.cmp(tb, tc)))), True{}, Equal.cong(Cmp, Bool, Cmp.is_le, String.order(tb, tc), String.order.fin(String.cmp.rec(Chr{U32{wb}}, Chr{U32{wc}}, String.cmp(tb, tc))), Equal.sym(Cmp, String.order.fin(String.cmp.rec(Chr{U32{wb}}, Chr{U32{wc}}, String.cmp(tb, tc))), String.order(tb, tc), S.rec_order(Chr{U32{wb}}, Chr{U32{wc}}, String.cmp(tb, tc)))), h2))
    case GT{} LT{}:
      Empty.absurd({Cmp.is_le(String.order.fin(String.cmp.fin(ta, tc, ((Chr{U32{wa}}, Chr{U32{wc}}), Word.cmp(32n, wa, wc))))) == True{} : Bool}, le_not(GT{}, h1, {==}))
    case GT{} EQ{}:
      Empty.absurd({Cmp.is_le(String.order.fin(String.cmp.fin(ta, tc, ((Chr{U32{wa}}, Chr{U32{wc}}), Word.cmp(32n, wa, wc))))) == True{} : Bool}, le_not(GT{}, h1, {==}))
    case GT{} GT{}:
      Empty.absurd({Cmp.is_le(String.order.fin(String.cmp.fin(ta, tc, ((Chr{U32{wa}}, Chr{U32{wc}}), Word.cmp(32n, wa, wc))))) == True{} : Bool}, le_not(GT{}, h1, {==}))
    case LT{} GT{}:
      Empty.absurd({Cmp.is_le(String.order.fin(String.cmp.fin(ta, tc, ((Chr{U32{wa}}, Chr{U32{wc}}), Word.cmp(32n, wa, wc))))) == True{} : Bool}, le_not(GT{}, h2, {==}))
    case EQ{} GT{}:
      Empty.absurd({Cmp.is_le(String.order.fin(String.cmp.fin(ta, tc, ((Chr{U32{wa}}, Chr{U32{wc}}), Word.cmp(32n, wa, wc))))) == True{} : Bool}, le_not(GT{}, h2, {==}))

# An order no larger than another no larger than a third is no larger than
# that.
def str_le(a: String, b: String, c: String, h1: {Cmp.is_le(String.order(a, b)) == True{} : Bool}, h2: {Cmp.is_le(String.order(b, c)) == True{} : Bool}) -> {Cmp.is_le(String.order(a, c)) == True{} : Bool}:
  match a b c:
    case SNil{} SNil{} SNil{}:
      {==}
    case SNil{} SNil{} SCon{hc, tc}:
      {==}
    case SNil{} SCon{hb, tb} SNil{}:
      {==}
    case SNil{} SCon{hb, tb} SCon{hc, tc}:
      {==}
    case SCon{ha, ta} SNil{} SNil{}:
      Empty.absurd({Cmp.is_le(String.order(SCon{ha, ta}, SNil{})) == True{} : Bool}, le_not(GT{}, h1, {==}))
    case SCon{ha, ta} SNil{} SCon{hc, tc}:
      Empty.absurd({Cmp.is_le(String.order(SCon{ha, ta}, SCon{hc, tc})) == True{} : Bool}, le_not(GT{}, h1, {==}))
    case SCon{ha, ta} SCon{hb, tb} SNil{}:
      Empty.absurd({Cmp.is_le(String.order(SCon{ha, ta}, SNil{})) == True{} : Bool}, le_not(GT{}, h2, {==}))
    case SCon{Chr{U32{+wa}}, +ta} SCon{Chr{U32{+wb}}, +tb} SCon{Chr{U32{+wc}}, +tc}:
      str_le.fin(Word.cmp(32n, wa, wb), Word.cmp(32n, wb, wc), wa, wb, wc, ta, tb, tc, {==}, {==}, h1, h2, x => y => str_le(ta, tb, tc, x, y))

def str_total.of(c: Cmp, e: {Cmp.is_le(c) == False{} : Bool}) -> {Cmp.is_le(cflip(c)) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Cmp.is_le(GT{}) == True{} : Bool}, S.true_false(e))
    case EQ{}:
      Empty.absurd({Cmp.is_le(EQ{}) == True{} : Bool}, S.true_false(e))
    case GT{}:
      {==}

# Where one is not no larger than the other, the other is.
def str_total(+a: String, +b: String, e: {Cmp.is_le(String.order(a, b)) == False{} : Bool}) -> {Cmp.is_le(String.order(b, a)) == True{} : Bool}:
  %Equal.sym(Cmp, String.order(b, a), cflip(String.order(a, b)), str_flip(a, b)) : {Cmp.is_le(_) == True{} : Bool}
  str_total.of(String.order(a, b), e)

# Merging two runs
# ----------------

def nat_le_trans(a: Nat, b: Nat, c: Nat, e1: {Nat.is_le(a, b) == True{} : Bool}, e2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      Pos.zero_le(c)
    case 1n+ap 0n _:
      Empty.absurd({Nat.is_le(1n+ap, c) == True{} : Bool}, S.false_true(e1))
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, S.false_true(e2))
    case 1n+ap 1n+bp 1n+cp:
      nat_le_trans(ap, bp, cp, e1, e2)

# Two runs merged, as `List.merge.go` merges them when its fuel lasts.
def mg(~A: Data, ~key: A -> String, xs: List<&2, A>, ys: List<&2, A>) -> List<&2, A>:
  match xs ys:
    case Nil{} Nil{}:
      Nil{}
    case Nil{} y <> yt:
      y <> yt
    case x <> xt Nil{}:
      x <> xt
    case +x <> +xt +y <> +yt:
      Bool.pick(List<&2, A>, String.is_le(key(x), key(y)), x <> mg(~A, ~key, xt, y <> yt), y <> mg(~A, ~key, x <> xt, yt))

def merge_step(~A: Data, ~key: A -> String, b: Bool, +x: A, +xt: List<&2, A>, +y: A, +yt: List<&2, A>, +acc: List<&2, A>, +f: Nat, hf: {Nat.is_le(Nat.add(List.length(&2, A, xt), 1n+List.length(&2, A, yt)), f) == True{} : Bool}, ih: @xs2: List<&2, A> -> @ys2: List<&2, A> -> @acc2: List<&2, A> -> {Nat.is_le(Nat.add(List.length(&2, A, xs2), List.length(&2, A, ys2)), f) == True{} : Bool} -> {List.merge.go(~A, ~(a => b => String.is_le(key(a), key(b))), f, (acc2, xs2, ys2)) == List.reverse.go(&2, A, acc2, mg(~A, ~key, xs2, ys2)) : List<&2, A>}) -> {List.merge.go(~A, ~(a => b => String.is_le(key(a), key(b))), f, List.merge.step(A, acc, x, xt, y, yt, b)) == List.reverse.go(&2, A, acc, Bool.pick(List<&2, A>, b, x <> mg(~A, ~key, xt, y <> yt), y <> mg(~A, ~key, x <> xt, yt))) : List<&2, A>}:
  match b:
    case True{}:
      ih(xt, y <> yt, x <> acc, hf)
    case False{}:
      ih(x <> xt, yt, y <> acc, Equal.trans(Bool, Nat.is_le(1n+Nat.add(List.length(&2, A, xt), List.length(&2, A, yt)), f), Nat.is_le(Nat.add(List.length(&2, A, xt), 1n+List.length(&2, A, yt)), f), True{},
        Equal.cong(Nat, Bool, v => Nat.is_le(v, f), 1n+Nat.add(List.length(&2, A, xt), List.length(&2, A, yt)), Nat.add(List.length(&2, A, xt), 1n+List.length(&2, A, yt)), Equal.sym(Nat, Nat.add(List.length(&2, A, xt), 1n+List.length(&2, A, yt)), 1n+Nat.add(List.length(&2, A, xt), List.length(&2, A, yt)), Pos.add_succ(List.length(&2, A, xt), List.length(&2, A, yt)))), hf))

# With fuel for every step, the merge is `mg`, after what it had.
def merge_go(~A: Data, ~key: A -> String, fuel: Nat, xs: List<&2, A>, ys: List<&2, A>, +acc: List<&2, A>, hf: {Nat.is_le(Nat.add(List.length(&2, A, xs), List.length(&2, A, ys)), fuel) == True{} : Bool}) -> {List.merge.go(~A, ~(a => b => String.is_le(key(a), key(b))), fuel, (acc, xs, ys)) == List.reverse.go(&2, A, acc, mg(~A, ~key, xs, ys)) : List<&2, A>}:
  match fuel xs ys:
    case 0n Nil{} Nil{}:
      {==}
    case 0n Nil{} y <> yt:
      Empty.absurd({List.merge.go(~A, ~(a => b => String.is_le(key(a), key(b))), 0n, (acc, Nil{}, y <> yt)) == List.reverse.go(&2, A, acc, mg(~A, ~key, Nil{}, y <> yt)) : List<&2, A>}, S.false_true(hf))
    case 0n x <> xt Nil{}:
      Empty.absurd({List.merge.go(~A, ~(a => b => String.is_le(key(a), key(b))), 0n, (acc, x <> xt, Nil{})) == List.reverse.go(&2, A, acc, mg(~A, ~key, x <> xt, Nil{})) : List<&2, A>}, S.false_true(hf))
    case 0n x <> xt y <> yt:
      Empty.absurd({List.merge.go(~A, ~(a => b => String.is_le(key(a), key(b))), 0n, (acc, x <> xt, y <> yt)) == List.reverse.go(&2, A, acc, mg(~A, ~key, x <> xt, y <> yt)) : List<&2, A>}, S.false_true(hf))
    case 1n+f Nil{} Nil{}:
      {==}
    case 1n+f Nil{} y <> yt:
      {==}
    case 1n+f x <> xt Nil{}:
      {==}
    case 1n++f +x <> +xt +y <> +yt:
      merge_step(~A, ~key, String.is_le(key(x), key(y)), x, xt, y, yt, acc, f, hf, xs2 => ys2 => acc2 => h => merge_go(~A, ~key, f, xs2, ys2, acc2, h))

# Sorted runs
# -----------

def band_i(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, S.false_true(ea))

def band_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(e))

def band_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, S.false_true(e))

# Every item no smaller, by name, than the one before it, the first no
# smaller than `k`.
def sorted.from(~A: Data, ~key: A -> String, xs: List<&2, A>, +k: String) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +y <> rest:
      Bool.and(String.is_le(k, key(y)), sorted.from(~A, ~key, rest, key(y)))

def sorted(~A: Data, ~key: A -> String, xs: List<&2, A>) -> Bool:
  sorted.from(~A, ~key, xs, SNil{})

# The items under one name, in order.
def keyed(~A: Data, ~key: A -> String, +f: String, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> +rest:
      Bool.pick(List<&2, A>, String.eq(key(x), f), x <> keyed(~A, ~key, f, rest), keyed(~A, ~key, f, rest))

def mg_sorted_step(~A: Data, ~key: A -> String, b: Bool, +k: String, +x: A, +xt: List<&2, A>, +y: A, +yt: List<&2, A>, eb: {String.is_le(key(x), key(y)) == b : Bool}, +hx: {sorted.from(~A, ~key, x <> xt, k) == True{} : Bool}, +hy: {sorted.from(~A, ~key, y <> yt, k) == True{} : Bool}, iht: {sorted.from(~A, ~key, y <> yt, key(x)) == True{} : Bool} -> {sorted.from(~A, ~key, mg(~A, ~key, xt, y <> yt), key(x)) == True{} : Bool}, ihf: {sorted.from(~A, ~key, x <> xt, key(y)) == True{} : Bool} -> {sorted.from(~A, ~key, mg(~A, ~key, x <> xt, yt), key(y)) == True{} : Bool}) -> {sorted.from(~A, ~key, Bool.pick(List<&2, A>, b, x <> mg(~A, ~key, xt, y <> yt), y <> mg(~A, ~key, x <> xt, yt)), k) == True{} : Bool}:
  match b:
    case True{}:
      band_i(String.is_le(k, key(x)), sorted.from(~A, ~key, mg(~A, ~key, xt, y <> yt), key(x)), band_l(String.is_le(k, key(x)), sorted.from(~A, ~key, xt, key(x)), hx), iht(band_i(String.is_le(key(x), key(y)), sorted.from(~A, ~key, yt, key(y)), eb, band_r(String.is_le(k, key(y)), sorted.from(~A, ~key, yt, key(y)), hy))))
    case False{}:
      band_i(String.is_le(k, key(y)), sorted.from(~A, ~key, mg(~A, ~key, x <> xt, yt), key(y)), band_l(String.is_le(k, key(y)), sorted.from(~A, ~key, yt, key(y)), hy), ihf(band_i(String.is_le(key(y), key(x)), sorted.from(~A, ~key, xt, key(x)), str_total(key(x), key(y), eb), band_r(String.is_le(k, key(x)), sorted.from(~A, ~key, xt, key(x)), hx))))

# Two runs sorted above `k` merge into one.
def mg_sorted(~A: Data, ~key: A -> String, xs: List<&2, A>, ys: List<&2, A>, +k: String, +hx: {sorted.from(~A, ~key, xs, k) == True{} : Bool}, +hy: {sorted.from(~A, ~key, ys, k) == True{} : Bool}) -> {sorted.from(~A, ~key, mg(~A, ~key, xs, ys), k) == True{} : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yt:
      hy
    case x <> xt Nil{}:
      hx
    case +x <> +xt +y <> +yt:
      mg_sorted_step(~A, ~key, String.is_le(key(x), key(y)), k, x, xt, y, yt, {==}, hx, hy, h => mg_sorted(~A, ~key, xt, y <> yt, key(x), band_r(String.is_le(k, key(x)), sorted.from(~A, ~key, xt, key(x)), hx), h), h => mg_sorted(~A, ~key, x <> xt, yt, key(y), h, band_r(String.is_le(k, key(y)), sorted.from(~A, ~key, yt, key(y)), hy)))

def lapp_nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, Nil{}) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Equal.cong(List<&2, A>, List<&2, A>, l => x <> l, List.append(&2, A, rest, Nil{}), rest, lapp_nil(A, rest))

def le_empty(s: String) -> {String.is_le(SNil{}, s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

def le_self(+s: String) -> {String.is_le(s, s) == True{} : Bool}:
  %Equal.sym(Cmp, String.order(s, s), EQ{}, S.order_refl(s)) : {Cmp.is_le(_) == True{} : Bool}
  {==}

def cons_pick(-A: Data, e: Bool, +x: A, +p: List<&2, A>, +q: List<&2, A>, +c: List<&2, A>, ep: {p == List.append(&2, A, q, c) : List<&2, A>}) -> {Bool.pick(List<&2, A>, e, x <> p, p) == List.append(&2, A, Bool.pick(List<&2, A>, e, x <> q, q), c) : List<&2, A>}:
  match e:
    case True{}:
      Equal.cong(List<&2, A>, List<&2, A>, l => x <> l, p, List.append(&2, A, q, c), ep)
    case False{}:
      ep

# The items under a name, of two lists one after the other.
def keyed_app(~A: Data, ~key: A -> String, +f: String, xs: List<&2, A>, +ys: List<&2, A>) -> {keyed(~A, ~key, f, List.append(&2, A, xs, ys)) == List.append(&2, A, keyed(~A, ~key, f, xs), keyed(~A, ~key, f, ys)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      cons_pick(A, String.eq(key(x), f), x, keyed(~A, ~key, f, List.append(&2, A, rest, ys)), keyed(~A, ~key, f, rest), keyed(~A, ~key, f, ys), keyed_app(~A, ~key, f, rest, ys))

def kn_step(~A: Data, ~key: A -> String, e: Bool, c: Bool, +f: String, +k: String, +z: A, +r: List<&2, A>, +ee: {String.eq(key(z), f) == e : Bool}, +ec: {String.is_le(key(z), f) == c : Bool}, +hlt: {String.is_le(k, f) == False{} : Bool}, +hkz: {String.is_le(k, key(z)) == True{} : Bool}, ih: {String.is_le(key(z), f) == False{} : Bool} -> {keyed(~A, ~key, f, r) == Nil{} : List<&2, A>}) -> {Bool.pick(List<&2, A>, e, z <> keyed(~A, ~key, f, r), keyed(~A, ~key, f, r)) == Nil{} : List<&2, A>}:
  match e:
    case True{}:
      Empty.absurd({z <> keyed(~A, ~key, f, r) == Nil{} : List<&2, A>}, S.false_true(Equal.trans(Bool, False{}, String.is_le(k, f), True{}, Equal.sym(Bool, String.is_le(k, f), False{}, hlt),
        Equal.trans(Bool, String.is_le(k, f), String.is_le(k, key(z)), True{}, Equal.cong(String, Bool, v => String.is_le(k, v), f, key(z), Equal.sym(String, key(z), f, S.eq_true(key(z), f, ee))), hkz))))
    case False{}:
      match c:
        case True{}:
          Empty.absurd({keyed(~A, ~key, f, r) == Nil{} : List<&2, A>}, S.false_true(Equal.trans(Bool, False{}, String.is_le(k, f), True{}, Equal.sym(Bool, String.is_le(k, f), False{}, hlt), str_le(k, key(z), f, hkz, ec))))
        case False{}:
          ih(ec)

# Nothing sorted above a name larger than `f` is under `f`.
def keyed_none(~A: Data, ~key: A -> String, l: List<&2, A>, +k: String, +f: String, +hlt: {String.is_le(k, f) == False{} : Bool}, +hs: {sorted.from(~A, ~key, l, k) == True{} : Bool}) -> {keyed(~A, ~key, f, l) == Nil{} : List<&2, A>}:
  match l:
    case Nil{}:
      {==}
    case +z <> +r:
      kn_step(~A, ~key, String.eq(key(z), f), String.is_le(key(z), f), f, k, z, r, {==}, {==}, hlt, band_l(String.is_le(k, key(z)), sorted.from(~A, ~key, r, key(z)), hs),
        h => keyed_none(~A, ~key, r, key(z), f, h, band_r(String.is_le(k, key(z)), sorted.from(~A, ~key, r, key(z)), hs)))

def mgk_false(~A: Data, ~key: A -> String, e2: Bool, +f: String, +x: A, +xt: List<&2, A>, +y: A, +yt: List<&2, A>, +ee2: {String.eq(key(y), f) == e2 : Bool}, +eb: {String.is_le(key(x), key(y)) == False{} : Bool}, +hxs: {sorted.from(~A, ~key, xt, key(x)) == True{} : Bool}, +ef: {keyed(~A, ~key, f, mg(~A, ~key, x <> xt, yt)) == List.append(&2, A, keyed(~A, ~key, f, x <> xt), keyed(~A, ~key, f, yt)) : List<&2, A>}) -> {Bool.pick(List<&2, A>, e2, y <> keyed(~A, ~key, f, mg(~A, ~key, x <> xt, yt)), keyed(~A, ~key, f, mg(~A, ~key, x <> xt, yt))) == List.append(&2, A, keyed(~A, ~key, f, x <> xt), Bool.pick(List<&2, A>, e2, y <> keyed(~A, ~key, f, yt), keyed(~A, ~key, f, yt))) : List<&2, A>}:
  match e2:
    case False{}:
      ef
    case True{}:
      %Equal.sym(List<&2, A>, keyed(~A, ~key, f, x <> xt), Nil{}, keyed_none(~A, ~key, x <> xt, key(x), f,
        Equal.trans(Bool, String.is_le(key(x), f), String.is_le(key(x), key(y)), False{}, Equal.cong(String, Bool, v => String.is_le(key(x), v), f, key(y), Equal.sym(String, key(y), f, S.eq_true(key(y), f, ee2))), eb),
        band_i(String.is_le(key(x), key(x)), sorted.from(~A, ~key, xt, key(x)), le_self(key(x)), hxs))) : {y <> keyed(~A, ~key, f, mg(~A, ~key, x <> xt, yt)) == List.append(&2, A, _, y <> keyed(~A, ~key, f, yt)) : List<&2, A>}
      Equal.cong(List<&2, A>, List<&2, A>, l => y <> l, keyed(~A, ~key, f, mg(~A, ~key, x <> xt, yt)), keyed(~A, ~key, f, yt),
        Equal.trans(List<&2, A>, keyed(~A, ~key, f, mg(~A, ~key, x <> xt, yt)), List.append(&2, A, keyed(~A, ~key, f, x <> xt), keyed(~A, ~key, f, yt)), keyed(~A, ~key, f, yt), ef,
          Equal.cong(List<&2, A>, List<&2, A>, l => List.append(&2, A, l, keyed(~A, ~key, f, yt)), keyed(~A, ~key, f, x <> xt), Nil{}, keyed_none(~A, ~key, x <> xt, key(x), f,
            Equal.trans(Bool, String.is_le(key(x), f), String.is_le(key(x), key(y)), False{}, Equal.cong(String, Bool, v => String.is_le(key(x), v), f, key(y), Equal.sym(String, key(y), f, S.eq_true(key(y), f, ee2))), eb),
            band_i(String.is_le(key(x), key(x)), sorted.from(~A, ~key, xt, key(x)), le_self(key(x)), hxs)))))

def mgk_step(~A: Data, ~key: A -> String, b: Bool, +f: String, +k: String, +x: A, +xt: List<&2, A>, +y: A, +yt: List<&2, A>, +eb: {String.is_le(key(x), key(y)) == b : Bool}, +hx: {sorted.from(~A, ~key, x <> xt, k) == True{} : Bool}, +hy: {sorted.from(~A, ~key, y <> yt, k) == True{} : Bool}, iht: {sorted.from(~A, ~key, y <> yt, key(x)) == True{} : Bool} -> {keyed(~A, ~key, f, mg(~A, ~key, xt, y <> yt)) == List.append(&2, A, keyed(~A, ~key, f, xt), keyed(~A, ~key, f, y <> yt)) : List<&2, A>}, ihf: {sorted.from(~A, ~key, x <> xt, key(y)) == True{} : Bool} -> {keyed(~A, ~key, f, mg(~A, ~key, x <> xt, yt)) == List.append(&2, A, keyed(~A, ~key, f, x <> xt), keyed(~A, ~key, f, yt)) : List<&2, A>}) -> {keyed(~A, ~key, f, Bool.pick(List<&2, A>, b, x <> mg(~A, ~key, xt, y <> yt), y <> mg(~A, ~key, x <> xt, yt))) == List.append(&2, A, keyed(~A, ~key, f, x <> xt), keyed(~A, ~key, f, y <> yt)) : List<&2, A>}:
  match b:
    case True{}:
      cons_pick(A, String.eq(key(x), f), x, keyed(~A, ~key, f, mg(~A, ~key, xt, y <> yt)), keyed(~A, ~key, f, xt), keyed(~A, ~key, f, y <> yt), iht(band_i(String.is_le(key(x), key(y)), sorted.from(~A, ~key, yt, key(y)), eb, band_r(String.is_le(k, key(y)), sorted.from(~A, ~key, yt, key(y)), hy))))
    case False{}:
      mgk_false(~A, ~key, String.eq(key(y), f), f, x, xt, y, yt, {==}, eb, band_r(String.is_le(k, key(x)), sorted.from(~A, ~key, xt, key(x)), hx),
        ihf(band_i(String.is_le(key(y), key(x)), sorted.from(~A, ~key, xt, key(x)), str_total(key(x), key(y), eb), band_r(String.is_le(k, key(x)), sorted.from(~A, ~key, xt, key(x)), hx))))

# Merging sorted runs keeps each name's items in order: those of the first,
# then those of the second.
def mg_keyed(~A: Data, ~key: A -> String, xs: List<&2, A>, ys: List<&2, A>, +k: String, +f: String, +hx: {sorted.from(~A, ~key, xs, k) == True{} : Bool}, +hy: {sorted.from(~A, ~key, ys, k) == True{} : Bool}) -> {keyed(~A, ~key, f, mg(~A, ~key, xs, ys)) == List.append(&2, A, keyed(~A, ~key, f, xs), keyed(~A, ~key, f, ys)) : List<&2, A>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yt:
      {==}
    case +x <> +xt Nil{}:
      Equal.sym(List<&2, A>, List.append(&2, A, keyed(~A, ~key, f, x <> xt), Nil{}), keyed(~A, ~key, f, x <> xt), lapp_nil(A, keyed(~A, ~key, f, x <> xt)))
    case +x <> +xt +y <> +yt:
      mgk_step(~A, ~key, String.is_le(key(x), key(y)), f, k, x, xt, y, yt, {==}, hx, hy,
        h => mg_keyed(~A, ~key, xt, y <> yt, key(x), f, band_r(String.is_le(k, key(x)), sorted.from(~A, ~key, xt, key(x)), hx), h),
        h => mg_keyed(~A, ~key, x <> xt, yt, key(y), f, h, band_r(String.is_le(k, key(y)), sorted.from(~A, ~key, yt, key(y)), hy)))

def mgl_step(~A: Data, ~key: A -> String, b: Bool, +x: A, +xt: List<&2, A>, +y: A, +yt: List<&2, A>, et: {List.length(&2, A, mg(~A, ~key, xt, y <> yt)) == Nat.add(List.length(&2, A, xt), 1n+List.length(&2, A, yt)) : Nat}, ef: {List.length(&2, A, mg(~A, ~key, x <> xt, yt)) == 1n+Nat.add(List.length(&2, A, xt), List.length(&2, A, yt)) : Nat}) -> {List.length(&2, A, Bool.pick(List<&2, A>, b, x <> mg(~A, ~key, xt, y <> yt), y <> mg(~A, ~key, x <> xt, yt))) == 1n+Nat.add(List.length(&2, A, xt), 1n+List.length(&2, A, yt)) : Nat}:
  match b:
    case True{}:
      Equal.cong(Nat, Nat, v => 1n+v, List.length(&2, A, mg(~A, ~key, xt, y <> yt)), Nat.add(List.length(&2, A, xt), 1n+List.length(&2, A, yt)), et)
    case False{}:
      %Equal.sym(Nat, Nat.add(List.length(&2, A, xt), 1n+List.length(&2, A, yt)), 1n+Nat.add(List.length(&2, A, xt), List.length(&2, A, yt)), Pos.add_succ(List.length(&2, A, xt), List.length(&2, A, yt))) : {List.length(&2, A, y <> mg(~A, ~key, x <> xt, yt)) == 1n+_ : Nat}
      Equal.cong(Nat, Nat, v => 1n+v, List.length(&2, A, mg(~A, ~key, x <> xt, yt)), 1n+Nat.add(List.length(&2, A, xt), List.length(&2, A, yt)), ef)

def mg_len(~A: Data, ~key: A -> String, xs: List<&2, A>, ys: List<&2, A>) -> {List.length(&2, A, mg(~A, ~key, xs, ys)) == Nat.add(List.length(&2, A, xs), List.length(&2, A, ys)) : Nat}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yt:
      {==}
    case x <> xt Nil{}:
      Equal.sym(Nat, Nat.add(List.length(&2, A, x <> xt), 0n), List.length(&2, A, x <> xt), Comp.add_zero(List.length(&2, A, x <> xt)))
    case +x <> +xt +y <> +yt:
      mgl_step(~A, ~key, String.is_le(key(x), key(y)), x, xt, y, yt, mg_len(~A, ~key, xt, y <> yt), mg_len(~A, ~key, x <> xt, yt))

# Passes of merges
# ----------------

def app_assoc(-A: Data, xs: List<&2, A>, -ys: List<&2, A>, -zs: List<&2, A>) -> {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Equal.cong(List<&2, A>, List<&2, A>, l => x <> l, List.append(&2, A, List.append(&2, A, rest, ys), zs), List.append(&2, A, rest, List.append(&2, A, ys, zs)), app_assoc(A, rest, ys, zs))

def len_app(-A: Data, xs: List<&2, A>, -ys: List<&2, A>) -> {List.length(&2, A, List.append(&2, A, xs, ys)) == Nat.add(List.length(&2, A, xs), List.length(&2, A, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Equal.cong(Nat, Nat, v => 1n+v, List.length(&2, A, List.append(&2, A, rest, ys)), Nat.add(List.length(&2, A, rest), List.length(&2, A, ys)), len_app(A, rest, ys))

def le_plus(b: Nat, +c: Nat) -> {Nat.is_le(b, Nat.add(b, c)) == True{} : Bool}:
  match b:
    case 0n:
      Pos.zero_le(c)
    case 1n+p:
      le_plus(p, c)

def le_add3a(a: Nat, +b: Nat, +c: Nat) -> {Nat.is_le(Nat.add(a, b), Nat.add(a, Nat.add(b, c))) == True{} : Bool}:
  match a:
    case 0n:
      le_plus(b, c)
    case 1n+p:
      le_add3a(p, b, c)

def le_c(b: Nat, +c: Nat) -> {Nat.is_le(c, Nat.add(b, c)) == True{} : Bool}:
  match b:
    case 0n:
      Comp.le_refl(c)
    case 1n++p:
      Comp.le_succ(c, Nat.add(p, c), le_c(p, c))

def le_add3c(a: Nat, +b: Nat, +c: Nat) -> {Nat.is_le(c, Nat.add(a, Nat.add(b, c))) == True{} : Bool}:
  match a:
    case 0n:
      le_c(b, c)
    case 1n++p:
      Comp.le_succ(c, Nat.add(p, Nat.add(b, c)), le_add3c(p, b, c))

# The passes the sort makes, their merges given the fuel they need.
def pspec(~A: Data, ~key: A -> String, runs: List<&2, List<&2, A>>) -> List<&2, List<&2, A>>:
  match runs:
    case Nil{}:
      Nil{}
    case r <> Nil{}:
      [r]
    case r1 <> r2 <> rest:
      mg(~A, ~key, r1, r2) <> pspec(~A, ~key, rest)

def all_sorted(~A: Data, ~key: A -> String, runs: List<&2, List<&2, A>>) -> Bool:
  match runs:
    case Nil{}:
      True{}
    case r <> rest:
      Bool.and(sorted.from(~A, ~key, r, SNil{}), all_sorted(~A, ~key, rest))

def len_runs(-A: Data, +r1: List<&2, A>, +r2: List<&2, A>, rest: List<&2, List<&2, A>>) -> {List.length(&2, A, List.concat(&2, A, r1 <> r2 <> rest)) == Nat.add(List.length(&2, A, r1), Nat.add(List.length(&2, A, r2), List.length(&2, A, List.concat(&2, A, rest)))) : Nat}:
  Equal.trans(Nat, List.length(&2, A, List.concat(&2, A, r1 <> r2 <> rest)), Nat.add(List.length(&2, A, r1), List.length(&2, A, List.append(&2, A, r2, List.concat(&2, A, rest)))), Nat.add(List.length(&2, A, r1), Nat.add(List.length(&2, A, r2), List.length(&2, A, List.concat(&2, A, rest)))), len_app(A, r1, List.append(&2, A, r2, List.concat(&2, A, rest))),
    Equal.cong(Nat, Nat, v => Nat.add(List.length(&2, A, r1), v), List.length(&2, A, List.append(&2, A, r2, List.concat(&2, A, rest))), Nat.add(List.length(&2, A, r2), List.length(&2, A, List.concat(&2, A, rest))), len_app(A, r2, List.concat(&2, A, rest))))

def pass_eq(~A: Data, ~key: A -> String, +n: Nat, runs: List<&2, List<&2, A>>, +hn: {Nat.is_le(List.length(&2, A, List.concat(&2, A, runs)), n) == True{} : Bool}) -> {List.sort.pass(~A, ~(a => b => String.is_le(key(a), key(b))), n, runs) == pspec(~A, ~key, runs) : List<&2, List<&2, A>>}:
  match runs:
    case Nil{}:
      {==}
    case r <> Nil{}:
      {==}
    case +r1 <> +r2 <> +rest:
      %Equal.sym(List<&2, A>, List.merge.go(~A, ~(a => b => String.is_le(key(a), key(b))), n, (Nil{}, r1, r2)), mg(~A, ~key, r1, r2), merge_go(~A, ~key, n, r1, r2, Nil{},
        nat_le_trans(Nat.add(List.length(&2, A, r1), List.length(&2, A, r2)), Nat.add(List.length(&2, A, r1), Nat.add(List.length(&2, A, r2), List.length(&2, A, List.concat(&2, A, rest)))), n, le_add3a(List.length(&2, A, r1), List.length(&2, A, r2), List.length(&2, A, List.concat(&2, A, rest))),
          Equal.trans(Bool, Nat.is_le(Nat.add(List.length(&2, A, r1), Nat.add(List.length(&2, A, r2), List.length(&2, A, List.concat(&2, A, rest)))), n), Nat.is_le(List.length(&2, A, List.concat(&2, A, r1 <> r2 <> rest)), n), True{}, Equal.cong(Nat, Bool, v => Nat.is_le(v, n), Nat.add(List.length(&2, A, r1), Nat.add(List.length(&2, A, r2), List.length(&2, A, List.concat(&2, A, rest)))), List.length(&2, A, List.concat(&2, A, r1 <> r2 <> rest)), Equal.sym(Nat, List.length(&2, A, List.concat(&2, A, r1 <> r2 <> rest)), Nat.add(List.length(&2, A, r1), Nat.add(List.length(&2, A, r2), List.length(&2, A, List.concat(&2, A, rest)))), len_runs(A, r1, r2, rest))), hn)))) : {_ <> List.sort.pass(~A, ~(a => b => String.is_le(key(a), key(b))), n, rest) == mg(~A, ~key, r1, r2) <> pspec(~A, ~key, rest) : List<&2, List<&2, A>>}
      %Equal.sym(List<&2, List<&2, A>>, List.sort.pass(~A, ~(a => b => String.is_le(key(a), key(b))), n, rest), pspec(~A, ~key, rest), pass_eq(~A, ~key, n, rest,
        nat_le_trans(List.length(&2, A, List.concat(&2, A, rest)), Nat.add(List.length(&2, A, r1), Nat.add(List.length(&2, A, r2), List.length(&2, A, List.concat(&2, A, rest)))), n, le_add3c(List.length(&2, A, r1), List.length(&2, A, r2), List.length(&2, A, List.concat(&2, A, rest))),
          Equal.trans(Bool, Nat.is_le(Nat.add(List.length(&2, A, r1), Nat.add(List.length(&2, A, r2), List.length(&2, A, List.concat(&2, A, rest)))), n), Nat.is_le(List.length(&2, A, List.concat(&2, A, r1 <> r2 <> rest)), n), True{}, Equal.cong(Nat, Bool, v => Nat.is_le(v, n), Nat.add(List.length(&2, A, r1), Nat.add(List.length(&2, A, r2), List.length(&2, A, List.concat(&2, A, rest)))), List.length(&2, A, List.concat(&2, A, r1 <> r2 <> rest)), Equal.sym(Nat, List.length(&2, A, List.concat(&2, A, r1 <> r2 <> rest)), Nat.add(List.length(&2, A, r1), Nat.add(List.length(&2, A, r2), List.length(&2, A, List.concat(&2, A, rest)))), len_runs(A, r1, r2, rest))), hn)))) : {mg(~A, ~key, r1, r2) <> _ == mg(~A, ~key, r1, r2) <> pspec(~A, ~key, rest) : List<&2, List<&2, A>>}
      {==}

def pspec_sorted(~A: Data, ~key: A -> String, runs: List<&2, List<&2, A>>, +hs: {all_sorted(~A, ~key, runs) == True{} : Bool}) -> {all_sorted(~A, ~key, pspec(~A, ~key, runs)) == True{} : Bool}:
  match runs:
    case Nil{}:
      {==}
    case r <> Nil{}:
      hs
    case +r1 <> +r2 <> +rest:
      band_i(sorted.from(~A, ~key, mg(~A, ~key, r1, r2), SNil{}), all_sorted(~A, ~key, pspec(~A, ~key, rest)), mg_sorted(~A, ~key, r1, r2, SNil{}, band_l(sorted.from(~A, ~key, r1, SNil{}), all_sorted(~A, ~key, r2 <> rest), hs), band_l(sorted.from(~A, ~key, r2, SNil{}), all_sorted(~A, ~key, rest), band_r(sorted.from(~A, ~key, r1, SNil{}), all_sorted(~A, ~key, r2 <> rest), hs))), pspec_sorted(~A, ~key, rest, band_r(sorted.from(~A, ~key, r2, SNil{}), all_sorted(~A, ~key, rest), band_r(sorted.from(~A, ~key, r1, SNil{}), all_sorted(~A, ~key, r2 <> rest), hs))))

def pspec_keyed(~A: Data, ~key: A -> String, runs: List<&2, List<&2, A>>, +f: String, +hs: {all_sorted(~A, ~key, runs) == True{} : Bool}) -> {keyed(~A, ~key, f, List.concat(&2, A, pspec(~A, ~key, runs))) == keyed(~A, ~key, f, List.concat(&2, A, runs)) : List<&2, A>}:
  match runs:
    case Nil{}:
      {==}
    case r <> Nil{}:
      {==}
    case +r1 <> +r2 <> +rest:
      %Equal.sym(List<&2, A>, keyed(~A, ~key, f, List.append(&2, A, mg(~A, ~key, r1, r2), List.concat(&2, A, pspec(~A, ~key, rest)))), List.append(&2, A, keyed(~A, ~key, f, mg(~A, ~key, r1, r2)), keyed(~A, ~key, f, List.concat(&2, A, pspec(~A, ~key, rest)))), keyed_app(~A, ~key, f, mg(~A, ~key, r1, r2), List.concat(&2, A, pspec(~A, ~key, rest)))) : {_ == keyed(~A, ~key, f, List.concat(&2, A, r1 <> r2 <> rest)) : List<&2, A>}
      %Equal.sym(List<&2, A>, keyed(~A, ~key, f, mg(~A, ~key, r1, r2)), List.append(&2, A, keyed(~A, ~key, f, r1), keyed(~A, ~key, f, r2)), mg_keyed(~A, ~key, r1, r2, SNil{}, f, band_l(sorted.from(~A, ~key, r1, SNil{}), all_sorted(~A, ~key, r2 <> rest), hs), band_l(sorted.from(~A, ~key, r2, SNil{}), all_sorted(~A, ~key, rest), band_r(sorted.from(~A, ~key, r1, SNil{}), all_sorted(~A, ~key, r2 <> rest), hs)))) : {List.append(&2, A, _, keyed(~A, ~key, f, List.concat(&2, A, pspec(~A, ~key, rest)))) == keyed(~A, ~key, f, List.concat(&2, A, r1 <> r2 <> rest)) : List<&2, A>}
      %Equal.sym(List<&2, A>, keyed(~A, ~key, f, List.concat(&2, A, pspec(~A, ~key, rest))), keyed(~A, ~key, f, List.concat(&2, A, rest)), pspec_keyed(~A, ~key, rest, f, band_r(sorted.from(~A, ~key, r2, SNil{}), all_sorted(~A, ~key, rest), band_r(sorted.from(~A, ~key, r1, SNil{}), all_sorted(~A, ~key, r2 <> rest), hs)))) : {List.append(&2, A, List.append(&2, A, keyed(~A, ~key, f, r1), keyed(~A, ~key, f, r2)), _) == keyed(~A, ~key, f, List.concat(&2, A, r1 <> r2 <> rest)) : List<&2, A>}
      %Equal.sym(List<&2, A>, keyed(~A, ~key, f, List.append(&2, A, r1, List.append(&2, A, r2, List.concat(&2, A, rest)))), List.append(&2, A, keyed(~A, ~key, f, r1), keyed(~A, ~key, f, List.append(&2, A, r2, List.concat(&2, A, rest)))), keyed_app(~A, ~key, f, r1, List.append(&2, A, r2, List.concat(&2, A, rest)))) : {List.append(&2, A, List.append(&2, A, keyed(~A, ~key, f, r1), keyed(~A, ~key, f, r2)), keyed(~A, ~key, f, List.concat(&2, A, rest))) == _ : List<&2, A>}
      %Equal.sym(List<&2, A>, keyed(~A, ~key, f, List.append(&2, A, r2, List.concat(&2, A, rest))), List.append(&2, A, keyed(~A, ~key, f, r2), keyed(~A, ~key, f, List.concat(&2, A, rest))), keyed_app(~A, ~key, f, r2, List.concat(&2, A, rest))) : {List.append(&2, A, List.append(&2, A, keyed(~A, ~key, f, r1), keyed(~A, ~key, f, r2)), keyed(~A, ~key, f, List.concat(&2, A, rest))) == List.append(&2, A, keyed(~A, ~key, f, r1), _) : List<&2, A>}
      app_assoc(A, keyed(~A, ~key, f, r1), keyed(~A, ~key, f, r2), keyed(~A, ~key, f, List.concat(&2, A, rest)))

def pspec_len(~A: Data, ~key: A -> String, runs: List<&2, List<&2, A>>) -> {List.length(&2, A, List.concat(&2, A, pspec(~A, ~key, runs))) == List.length(&2, A, List.concat(&2, A, runs)) : Nat}:
  match runs:
    case Nil{}:
      {==}
    case r <> Nil{}:
      {==}
    case +r1 <> +r2 <> +rest:
      %Equal.sym(Nat, List.length(&2, A, List.append(&2, A, mg(~A, ~key, r1, r2), List.concat(&2, A, pspec(~A, ~key, rest)))), Nat.add(List.length(&2, A, mg(~A, ~key, r1, r2)), List.length(&2, A, List.concat(&2, A, pspec(~A, ~key, rest)))), len_app(A, mg(~A, ~key, r1, r2), List.concat(&2, A, pspec(~A, ~key, rest)))) : {_ == List.length(&2, A, List.concat(&2, A, r1 <> r2 <> rest)) : Nat}
      %Equal.sym(Nat, List.length(&2, A, mg(~A, ~key, r1, r2)), Nat.add(List.length(&2, A, r1), List.length(&2, A, r2)), mg_len(~A, ~key, r1, r2)) : {Nat.add(_, List.length(&2, A, List.concat(&2, A, pspec(~A, ~key, rest)))) == List.length(&2, A, List.concat(&2, A, r1 <> r2 <> rest)) : Nat}
      %Equal.sym(Nat, List.length(&2, A, List.concat(&2, A, pspec(~A, ~key, rest))), List.length(&2, A, List.concat(&2, A, rest)), pspec_len(~A, ~key, rest)) : {Nat.add(Nat.add(List.length(&2, A, r1), List.length(&2, A, r2)), _) == List.length(&2, A, List.concat(&2, A, r1 <> r2 <> rest)) : Nat}
      %Equal.sym(Nat, List.length(&2, A, List.concat(&2, A, r1 <> r2 <> rest)), Nat.add(List.length(&2, A, r1), Nat.add(List.length(&2, A, r2), List.length(&2, A, List.concat(&2, A, rest)))), len_runs(A, r1, r2, rest)) : {Nat.add(Nat.add(List.length(&2, A, r1), List.length(&2, A, r2)), List.length(&2, A, List.concat(&2, A, rest))) == _ : Nat}
      Pos.add_assoc(List.length(&2, A, r1), List.length(&2, A, r2), List.length(&2, A, List.concat(&2, A, rest)))

def pspec_count(~A: Data, ~key: A -> String, runs: List<&2, List<&2, A>>) -> {Nat.is_le(List.length(&2, List<&2, A>, pspec(~A, ~key, runs)), List.length(&2, List<&2, A>, runs)) == True{} : Bool}:
  match runs:
    case Nil{}:
      {==}
    case r <> Nil{}:
      {==}
    case r1 <> r2 <> +rest:
      Comp.le_succ(List.length(&2, List<&2, A>, pspec(~A, ~key, rest)), List.length(&2, List<&2, A>, rest), pspec_count(~A, ~key, rest))

# The sort
# --------

# With a pass for every run but one, the passes leave one sorted run.
def go_sorted(~A: Data, ~key: A -> String, fuel: Nat, +n: Nat, runs: List<&2, List<&2, A>>, +hs: {all_sorted(~A, ~key, runs) == True{} : Bool}, +hn: {Nat.is_le(List.length(&2, A, List.concat(&2, A, runs)), n) == True{} : Bool}, hf: {Nat.is_le(List.length(&2, List<&2, A>, runs), 1n+fuel) == True{} : Bool}) -> {sorted.from(~A, ~key, List.sort.go(~A, ~(a => b => String.is_le(key(a), key(b))), fuel, n, runs), SNil{}) == True{} : Bool}:
  match fuel:
    case 0n:
      match runs:
        case Nil{}:
          {==}
        case +r <> rest0:
          match rest0:
            case Nil{}:
              %Equal.sym(List<&2, A>, List.append(&2, A, r, Nil{}), r, lapp_nil(A, r)) : {sorted.from(~A, ~key, _, SNil{}) == True{} : Bool}
              band_l(sorted.from(~A, ~key, r, SNil{}), True{}, hs)
            case r2 <> rest:
              Empty.absurd({sorted.from(~A, ~key, List.concat(&2, A, r <> r2 <> rest), SNil{}) == True{} : Bool}, S.false_true(hf))
    case 1n++f:
      match runs:
        case Nil{}:
          {==}
        case +r1 <> +rest0:
          match rest0:
            case Nil{}:
              band_l(sorted.from(~A, ~key, r1, SNil{}), True{}, hs)
            case +r2 <> +rest:
              %Equal.sym(List<&2, List<&2, A>>, List.sort.pass(~A, ~(a => b => String.is_le(key(a), key(b))), n, r1 <> r2 <> rest), pspec(~A, ~key, r1 <> r2 <> rest), pass_eq(~A, ~key, n, r1 <> r2 <> rest, hn)) : {sorted.from(~A, ~key, List.sort.go(~A, ~(a => b => String.is_le(key(a), key(b))), f, n, _), SNil{}) == True{} : Bool}
              go_sorted(~A, ~key, f, n, pspec(~A, ~key, r1 <> r2 <> rest), pspec_sorted(~A, ~key, r1 <> r2 <> rest, hs), Equal.trans(Bool, Nat.is_le(List.length(&2, A, List.concat(&2, A, pspec(~A, ~key, r1 <> r2 <> rest))), n), Nat.is_le(List.length(&2, A, List.concat(&2, A, r1 <> r2 <> rest)), n), True{}, Equal.cong(Nat, Bool, v => Nat.is_le(v, n), List.length(&2, A, List.concat(&2, A, pspec(~A, ~key, r1 <> r2 <> rest))), List.length(&2, A, List.concat(&2, A, r1 <> r2 <> rest)), pspec_len(~A, ~key, r1 <> r2 <> rest)), hn), nat_le_trans(List.length(&2, List<&2, A>, pspec(~A, ~key, rest)), List.length(&2, List<&2, A>, rest), f, pspec_count(~A, ~key, rest), hf))

def go_keyed(~A: Data, ~key: A -> String, fuel: Nat, +n: Nat, runs: List<&2, List<&2, A>>, +f0: String, +hs: {all_sorted(~A, ~key, runs) == True{} : Bool}, +hn: {Nat.is_le(List.length(&2, A, List.concat(&2, A, runs)), n) == True{} : Bool}, hf: {Nat.is_le(List.length(&2, List<&2, A>, runs), 1n+fuel) == True{} : Bool}) -> {keyed(~A, ~key, f0, List.sort.go(~A, ~(a => b => String.is_le(key(a), key(b))), fuel, n, runs)) == keyed(~A, ~key, f0, List.concat(&2, A, runs)) : List<&2, A>}:
  match fuel:
    case 0n:
      {==}
    case 1n++f:
      match runs:
        case Nil{}:
          {==}
        case +r1 <> +rest0:
          match rest0:
            case Nil{}:
              %lapp_nil(A, r1) : {keyed(~A, ~key, f0, _) == keyed(~A, ~key, f0, List.append(&2, A, r1, Nil{})) : List<&2, A>}
              {==}
            case +r2 <> +rest:
              %Equal.sym(List<&2, List<&2, A>>, List.sort.pass(~A, ~(a => b => String.is_le(key(a), key(b))), n, r1 <> r2 <> rest), pspec(~A, ~key, r1 <> r2 <> rest), pass_eq(~A, ~key, n, r1 <> r2 <> rest, hn)) : {keyed(~A, ~key, f0, List.sort.go(~A, ~(a => b => String.is_le(key(a), key(b))), f, n, _)) == keyed(~A, ~key, f0, List.concat(&2, A, r1 <> r2 <> rest)) : List<&2, A>}
              Equal.trans(List<&2, A>, keyed(~A, ~key, f0, List.sort.go(~A, ~(a => b => String.is_le(key(a), key(b))), f, n, pspec(~A, ~key, r1 <> r2 <> rest))), keyed(~A, ~key, f0, List.concat(&2, A, pspec(~A, ~key, r1 <> r2 <> rest))), keyed(~A, ~key, f0, List.concat(&2, A, r1 <> r2 <> rest)),
                go_keyed(~A, ~key, f, n, pspec(~A, ~key, r1 <> r2 <> rest), f0, pspec_sorted(~A, ~key, r1 <> r2 <> rest, hs), Equal.trans(Bool, Nat.is_le(List.length(&2, A, List.concat(&2, A, pspec(~A, ~key, r1 <> r2 <> rest))), n), Nat.is_le(List.length(&2, A, List.concat(&2, A, r1 <> r2 <> rest)), n), True{}, Equal.cong(Nat, Bool, v => Nat.is_le(v, n), List.length(&2, A, List.concat(&2, A, pspec(~A, ~key, r1 <> r2 <> rest))), List.length(&2, A, List.concat(&2, A, r1 <> r2 <> rest)), pspec_len(~A, ~key, r1 <> r2 <> rest)), hn), nat_le_trans(List.length(&2, List<&2, A>, pspec(~A, ~key, rest)), List.length(&2, List<&2, A>, rest), f, pspec_count(~A, ~key, rest), hf)),
                pspec_keyed(~A, ~key, r1 <> r2 <> rest, f0, hs))

def concat_runs(-A: Data, xs: List<&2, A>) -> {List.concat(&2, A, List.sort.runs(A, xs)) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Equal.cong(List<&2, A>, List<&2, A>, l => x <> l, List.concat(&2, A, List.sort.runs(A, rest)), rest, concat_runs(A, rest))

def runs_len(-A: Data, xs: List<&2, A>) -> {List.length(&2, List<&2, A>, List.sort.runs(A, xs)) == List.length(&2, A, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Equal.cong(Nat, Nat, v => 1n+v, List.length(&2, List<&2, A>, List.sort.runs(A, rest)), List.length(&2, A, rest), runs_len(A, rest))

def runs_sorted(~A: Data, ~key: A -> String, xs: List<&2, A>) -> {all_sorted(~A, ~key, List.sort.runs(A, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      band_i(sorted.from(~A, ~key, [x], SNil{}), all_sorted(~A, ~key, List.sort.runs(A, rest)), band_i(String.is_le(SNil{}, key(x)), True{}, le_empty(key(x)), {==}), runs_sorted(~A, ~key, rest))

def runs_hn(-A: Data, +xs: List<&2, A>) -> {Nat.is_le(List.length(&2, A, List.concat(&2, A, List.sort.runs(A, xs))), List.length(&2, A, xs)) == True{} : Bool}:
  %Equal.sym(List<&2, A>, List.concat(&2, A, List.sort.runs(A, xs)), xs, concat_runs(A, xs)) : {Nat.is_le(List.length(&2, A, _), List.length(&2, A, xs)) == True{} : Bool}
  Comp.le_refl(List.length(&2, A, xs))

def runs_hf(-A: Data, +xs: List<&2, A>) -> {Nat.is_le(List.length(&2, List<&2, A>, List.sort.runs(A, xs)), 1n+List.length(&2, A, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, List<&2, A>, List.sort.runs(A, xs)), List.length(&2, A, xs), runs_len(A, xs)) : {Nat.is_le(_, 1n+List.length(&2, A, xs)) == True{} : Bool}
  Comp.le_succ(List.length(&2, A, xs), List.length(&2, A, xs), Comp.le_refl(List.length(&2, A, xs)))

# `List.sort`, by a name, puts every item no smaller than the one before it.
def sort_sorted(~A: Data, ~key: A -> String, +xs: List<&2, A>) -> {sorted(~A, ~key, List.sort(~A, ~(a => b => String.is_le(key(a), key(b))), xs)) == True{} : Bool}:
  go_sorted(~A, ~key, List.length(&2, A, xs), List.length(&2, A, xs), List.sort.runs(A, xs), runs_sorted(~A, ~key, xs), runs_hn(A, xs), runs_hf(A, xs))

# And keeps every item: the items under each name are the ones it was
# given, in the order it was given them.
def sort_keyed(~A: Data, ~key: A -> String, +xs: List<&2, A>, +f: String) -> {keyed(~A, ~key, f, List.sort(~A, ~(a => b => String.is_le(key(a), key(b))), xs)) == keyed(~A, ~key, f, xs) : List<&2, A>}:
  Equal.trans(List<&2, A>, keyed(~A, ~key, f, List.sort.go(~A, ~(a => b => String.is_le(key(a), key(b))), List.length(&2, A, xs), List.length(&2, A, xs), List.sort.runs(A, xs))), keyed(~A, ~key, f, List.concat(&2, A, List.sort.runs(A, xs))), keyed(~A, ~key, f, xs),
    go_keyed(~A, ~key, List.length(&2, A, xs), List.length(&2, A, xs), List.sort.runs(A, xs), f, runs_sorted(~A, ~key, xs), runs_hn(A, xs), runs_hf(A, xs)),
    Equal.cong(List<&2, A>, List<&2, A>, l => keyed(~A, ~key, f, l), List.concat(&2, A, List.sort.runs(A, xs)), xs, concat_runs(A, xs)))

# What a sort keeps
# -----------------

# A sort only moves what it is given, so whatever holds of every item it
# was given holds of every item it returns, whichever order it sorts by.
def all_ok(~A: Data, ~ok: A -> Bool, xs: List<&2, A>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(ok(x), all_ok(~A, ~ok, rest))

def all_app(~A: Data, ~ok: A -> Bool, xs: List<&2, A>, +ys: List<&2, A>, +hx: {all_ok(~A, ~ok, xs) == True{} : Bool}, hy: {all_ok(~A, ~ok, ys) == True{} : Bool}) -> {all_ok(~A, ~ok, List.append(&2, A, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +x <> +rest:
      band_i(ok(x), all_ok(~A, ~ok, List.append(&2, A, rest, ys)), band_l(ok(x), all_ok(~A, ~ok, rest), hx), all_app(~A, ~ok, rest, ys, band_r(ok(x), all_ok(~A, ~ok, rest), hx), hy))

def all_rev_go(~A: Data, ~ok: A -> Bool, acc: List<&2, A>, +zs: List<&2, A>, +ha: {all_ok(~A, ~ok, acc) == True{} : Bool}, +hz: {all_ok(~A, ~ok, zs) == True{} : Bool}) -> {all_ok(~A, ~ok, List.reverse.go(&2, A, acc, zs)) == True{} : Bool}:
  match acc:
    case Nil{}:
      hz
    case +a <> +rest:
      all_rev_go(~A, ~ok, rest, a <> zs, band_r(ok(a), all_ok(~A, ~ok, rest), ha), band_i(ok(a), all_ok(~A, ~ok, zs), band_l(ok(a), all_ok(~A, ~ok, rest), ha), hz))

def all_step(~A: Data, ~le: A -> A -> Bool, ~ok: A -> Bool, b: Bool, +f: Nat, +acc: List<&2, A>, +x: A, +xt: List<&2, A>, +y: A, +yt: List<&2, A>, ihf: {all_ok(~A, ~ok, List.merge.go(~A, ~le, f, (y <> acc, x <> xt, yt))) == True{} : Bool}, iht: {all_ok(~A, ~ok, List.merge.go(~A, ~le, f, (x <> acc, xt, y <> yt))) == True{} : Bool}) -> {all_ok(~A, ~ok, List.merge.go(~A, ~le, f, List.merge.step(A, acc, x, xt, y, yt, b))) == True{} : Bool}:
  match b:
    case False{}:
      ihf
    case True{}:
      iht

def all_merge(~A: Data, ~le: A -> A -> Bool, ~ok: A -> Bool, fuel: Nat, +acc: List<&2, A>, +xs: List<&2, A>, +ys: List<&2, A>, +ha: {all_ok(~A, ~ok, acc) == True{} : Bool}, +hx: {all_ok(~A, ~ok, xs) == True{} : Bool}, +hy: {all_ok(~A, ~ok, ys) == True{} : Bool}) -> {all_ok(~A, ~ok, List.merge.go(~A, ~le, fuel, (acc, xs, ys))) == True{} : Bool}:
  match fuel:
    case 0n:
      all_rev_go(~A, ~ok, acc, List.append(&2, A, xs, ys), ha, all_app(~A, ~ok, xs, ys, hx, hy))
    case 1n++f:
      match xs ys:
        case Nil{} Nil{}:
          all_rev_go(~A, ~ok, acc, Nil{}, ha, {==})
        case Nil{} +y <> +yt:
          all_rev_go(~A, ~ok, acc, y <> yt, ha, hy)
        case +x <> +xt Nil{}:
          all_rev_go(~A, ~ok, acc, x <> xt, ha, hx)
        case +x <> +xt +y <> +yt:
          all_step(~A, ~le, ~ok, le(x, y), f, acc, x, xt, y, yt,
            all_merge(~A, ~le, ~ok, f, y <> acc, x <> xt, yt, band_i(ok(y), all_ok(~A, ~ok, acc), band_l(ok(y), all_ok(~A, ~ok, yt), hy), ha), hx, band_r(ok(y), all_ok(~A, ~ok, yt), hy)),
            all_merge(~A, ~le, ~ok, f, x <> acc, xt, y <> yt, band_i(ok(x), all_ok(~A, ~ok, acc), band_l(ok(x), all_ok(~A, ~ok, xt), hx), ha), band_r(ok(x), all_ok(~A, ~ok, xt), hx), hy))

def all_runs(~A: Data, ~ok: A -> Bool, rs: List<&2, List<&2, A>>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> rest:
      Bool.and(all_ok(~A, ~ok, r), all_runs(~A, ~ok, rest))

def all_pass(~A: Data, ~le: A -> A -> Bool, ~ok: A -> Bool, +n: Nat, runs: List<&2, List<&2, A>>, +h: {all_runs(~A, ~ok, runs) == True{} : Bool}) -> {all_runs(~A, ~ok, List.sort.pass(~A, ~le, n, runs)) == True{} : Bool}:
  match runs:
    case Nil{}:
      {==}
    case +r <> Nil{}:
      h
    case +r1 <> +r2 <> +rest:
      band_i(all_ok(~A, ~ok, List.merge.go(~A, ~le, n, (Nil{}, r1, r2))), all_runs(~A, ~ok, List.sort.pass(~A, ~le, n, rest)),
        all_merge(~A, ~le, ~ok, n, Nil{}, r1, r2, {==}, band_l(all_ok(~A, ~ok, r1), all_runs(~A, ~ok, r2 <> rest), h), band_l(all_ok(~A, ~ok, r2), all_runs(~A, ~ok, rest), band_r(all_ok(~A, ~ok, r1), all_runs(~A, ~ok, r2 <> rest), h))),
        all_pass(~A, ~le, ~ok, n, rest, band_r(all_ok(~A, ~ok, r2), all_runs(~A, ~ok, rest), band_r(all_ok(~A, ~ok, r1), all_runs(~A, ~ok, r2 <> rest), h))))

def all_concat(~A: Data, ~ok: A -> Bool, runs: List<&2, List<&2, A>>, +h: {all_runs(~A, ~ok, runs) == True{} : Bool}) -> {all_ok(~A, ~ok, List.concat(&2, A, runs)) == True{} : Bool}:
  match runs:
    case Nil{}:
      {==}
    case +r <> +rest:
      all_app(~A, ~ok, r, List.concat(&2, A, rest), band_l(all_ok(~A, ~ok, r), all_runs(~A, ~ok, rest), h), all_concat(~A, ~ok, rest, band_r(all_ok(~A, ~ok, r), all_runs(~A, ~ok, rest), h)))

def all_go(~A: Data, ~le: A -> A -> Bool, ~ok: A -> Bool, fuel: Nat, +n: Nat, runs: List<&2, List<&2, A>>, +h: {all_runs(~A, ~ok, runs) == True{} : Bool}) -> {all_ok(~A, ~ok, List.sort.go(~A, ~le, fuel, n, runs)) == True{} : Bool}:
  match fuel:
    case 0n:
      all_concat(~A, ~ok, runs, h)
    case 1n++f:
      match runs:
        case Nil{}:
          {==}
        case +r <> Nil{}:
          band_l(all_ok(~A, ~ok, r), True{}, h)
        case +r1 <> +r2 <> +rest:
          all_go(~A, ~le, ~ok, f, n, List.sort.pass(~A, ~le, n, r1 <> r2 <> rest), all_pass(~A, ~le, ~ok, n, r1 <> r2 <> rest, h))

def all_runs_of(~A: Data, ~ok: A -> Bool, xs: List<&2, A>, +h: {all_ok(~A, ~ok, xs) == True{} : Bool}) -> {all_runs(~A, ~ok, List.sort.runs(A, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      band_i(Bool.and(ok(x), True{}), all_runs(~A, ~ok, List.sort.runs(A, rest)), band_i(ok(x), True{}, band_l(ok(x), all_ok(~A, ~ok, rest), h), {==}), all_runs_of(~A, ~ok, rest, band_r(ok(x), all_ok(~A, ~ok, rest), h)))

def all_sort(~A: Data, ~le: A -> A -> Bool, ~ok: A -> Bool, +xs: List<&2, A>, +h: {all_ok(~A, ~ok, xs) == True{} : Bool}) -> {all_ok(~A, ~ok, List.sort(~A, ~le, xs)) == True{} : Bool}:
  all_go(~A, ~le, ~ok, List.length(&2, A, xs), List.length(&2, A, xs), List.sort.runs(A, xs), all_runs_of(~A, ~ok, xs, h))

# The same, for a test that reads one more value, which a template cannot
# capture: whatever holds of every item with it holds after the sort.
def all_at(~A: Data, ~C: Data, ~ok: C -> A -> Bool, +c: C, xs: List<&2, A>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(ok(c, x), all_at(~A, ~C, ~ok, c, rest))

def all_app_at(~A: Data, ~C: Data, ~ok: C -> A -> Bool, +c: C, xs: List<&2, A>, +ys: List<&2, A>, +hx: {all_at(~A, ~C, ~ok, c, xs) == True{} : Bool}, hy: {all_at(~A, ~C, ~ok, c, ys) == True{} : Bool}) -> {all_at(~A, ~C, ~ok, c, List.append(&2, A, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +x <> +rest:
      band_i(ok(c, x), all_at(~A, ~C, ~ok, c, List.append(&2, A, rest, ys)), band_l(ok(c, x), all_at(~A, ~C, ~ok, c, rest), hx), all_app_at(~A, ~C, ~ok, c, rest, ys, band_r(ok(c, x), all_at(~A, ~C, ~ok, c, rest), hx), hy))

def all_rev_go_at(~A: Data, ~C: Data, ~ok: C -> A -> Bool, +c: C, acc: List<&2, A>, +zs: List<&2, A>, +ha: {all_at(~A, ~C, ~ok, c, acc) == True{} : Bool}, +hz: {all_at(~A, ~C, ~ok, c, zs) == True{} : Bool}) -> {all_at(~A, ~C, ~ok, c, List.reverse.go(&2, A, acc, zs)) == True{} : Bool}:
  match acc:
    case Nil{}:
      hz
    case +a <> +rest:
      all_rev_go_at(~A, ~C, ~ok, c, rest, a <> zs, band_r(ok(c, a), all_at(~A, ~C, ~ok, c, rest), ha), band_i(ok(c, a), all_at(~A, ~C, ~ok, c, zs), band_l(ok(c, a), all_at(~A, ~C, ~ok, c, rest), ha), hz))

def all_step_at(~A: Data, ~le: A -> A -> Bool, ~C: Data, ~ok: C -> A -> Bool, +c: C, b: Bool, +f: Nat, +acc: List<&2, A>, +x: A, +xt: List<&2, A>, +y: A, +yt: List<&2, A>, ihf: {all_at(~A, ~C, ~ok, c, List.merge.go(~A, ~le, f, (y <> acc, x <> xt, yt))) == True{} : Bool}, iht: {all_at(~A, ~C, ~ok, c, List.merge.go(~A, ~le, f, (x <> acc, xt, y <> yt))) == True{} : Bool}) -> {all_at(~A, ~C, ~ok, c, List.merge.go(~A, ~le, f, List.merge.step(A, acc, x, xt, y, yt, b))) == True{} : Bool}:
  match b:
    case False{}:
      ihf
    case True{}:
      iht

def all_merge_at(~A: Data, ~le: A -> A -> Bool, ~C: Data, ~ok: C -> A -> Bool, +c: C, fuel: Nat, +acc: List<&2, A>, +xs: List<&2, A>, +ys: List<&2, A>, +ha: {all_at(~A, ~C, ~ok, c, acc) == True{} : Bool}, +hx: {all_at(~A, ~C, ~ok, c, xs) == True{} : Bool}, +hy: {all_at(~A, ~C, ~ok, c, ys) == True{} : Bool}) -> {all_at(~A, ~C, ~ok, c, List.merge.go(~A, ~le, fuel, (acc, xs, ys))) == True{} : Bool}:
  match fuel:
    case 0n:
      all_rev_go_at(~A, ~C, ~ok, c, acc, List.append(&2, A, xs, ys), ha, all_app_at(~A, ~C, ~ok, c, xs, ys, hx, hy))
    case 1n++f:
      match xs ys:
        case Nil{} Nil{}:
          all_rev_go_at(~A, ~C, ~ok, c, acc, Nil{}, ha, {==})
        case Nil{} +y <> +yt:
          all_rev_go_at(~A, ~C, ~ok, c, acc, y <> yt, ha, hy)
        case +x <> +xt Nil{}:
          all_rev_go_at(~A, ~C, ~ok, c, acc, x <> xt, ha, hx)
        case +x <> +xt +y <> +yt:
          all_step_at(~A, ~le, ~C, ~ok, c, le(x, y), f, acc, x, xt, y, yt,
            all_merge_at(~A, ~le, ~C, ~ok, c, f, y <> acc, x <> xt, yt, band_i(ok(c, y), all_at(~A, ~C, ~ok, c, acc), band_l(ok(c, y), all_at(~A, ~C, ~ok, c, yt), hy), ha), hx, band_r(ok(c, y), all_at(~A, ~C, ~ok, c, yt), hy)),
            all_merge_at(~A, ~le, ~C, ~ok, c, f, x <> acc, xt, y <> yt, band_i(ok(c, x), all_at(~A, ~C, ~ok, c, acc), band_l(ok(c, x), all_at(~A, ~C, ~ok, c, xt), hx), ha), band_r(ok(c, x), all_at(~A, ~C, ~ok, c, xt), hx), hy))

def all_runs_at(~A: Data, ~C: Data, ~ok: C -> A -> Bool, +c: C, rs: List<&2, List<&2, A>>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> rest:
      Bool.and(all_at(~A, ~C, ~ok, c, r), all_runs_at(~A, ~C, ~ok, c, rest))

def all_pass_at(~A: Data, ~le: A -> A -> Bool, ~C: Data, ~ok: C -> A -> Bool, +c: C, +n: Nat, runs: List<&2, List<&2, A>>, +h: {all_runs_at(~A, ~C, ~ok, c, runs) == True{} : Bool}) -> {all_runs_at(~A, ~C, ~ok, c, List.sort.pass(~A, ~le, n, runs)) == True{} : Bool}:
  match runs:
    case Nil{}:
      {==}
    case +r <> Nil{}:
      h
    case +r1 <> +r2 <> +rest:
      band_i(all_at(~A, ~C, ~ok, c, List.merge.go(~A, ~le, n, (Nil{}, r1, r2))), all_runs_at(~A, ~C, ~ok, c, List.sort.pass(~A, ~le, n, rest)),
        all_merge_at(~A, ~le, ~C, ~ok, c, n, Nil{}, r1, r2, {==}, band_l(all_at(~A, ~C, ~ok, c, r1), all_runs_at(~A, ~C, ~ok, c, r2 <> rest), h), band_l(all_at(~A, ~C, ~ok, c, r2), all_runs_at(~A, ~C, ~ok, c, rest), band_r(all_at(~A, ~C, ~ok, c, r1), all_runs_at(~A, ~C, ~ok, c, r2 <> rest), h))),
        all_pass_at(~A, ~le, ~C, ~ok, c, n, rest, band_r(all_at(~A, ~C, ~ok, c, r2), all_runs_at(~A, ~C, ~ok, c, rest), band_r(all_at(~A, ~C, ~ok, c, r1), all_runs_at(~A, ~C, ~ok, c, r2 <> rest), h))))

def all_concat_at(~A: Data, ~C: Data, ~ok: C -> A -> Bool, +c: C, runs: List<&2, List<&2, A>>, +h: {all_runs_at(~A, ~C, ~ok, c, runs) == True{} : Bool}) -> {all_at(~A, ~C, ~ok, c, List.concat(&2, A, runs)) == True{} : Bool}:
  match runs:
    case Nil{}:
      {==}
    case +r <> +rest:
      all_app_at(~A, ~C, ~ok, c, r, List.concat(&2, A, rest), band_l(all_at(~A, ~C, ~ok, c, r), all_runs_at(~A, ~C, ~ok, c, rest), h), all_concat_at(~A, ~C, ~ok, c, rest, band_r(all_at(~A, ~C, ~ok, c, r), all_runs_at(~A, ~C, ~ok, c, rest), h)))

def all_go_at(~A: Data, ~le: A -> A -> Bool, ~C: Data, ~ok: C -> A -> Bool, +c: C, fuel: Nat, +n: Nat, runs: List<&2, List<&2, A>>, +h: {all_runs_at(~A, ~C, ~ok, c, runs) == True{} : Bool}) -> {all_at(~A, ~C, ~ok, c, List.sort.go(~A, ~le, fuel, n, runs)) == True{} : Bool}:
  match fuel:
    case 0n:
      all_concat_at(~A, ~C, ~ok, c, runs, h)
    case 1n++f:
      match runs:
        case Nil{}:
          {==}
        case +r <> Nil{}:
          band_l(all_at(~A, ~C, ~ok, c, r), True{}, h)
        case +r1 <> +r2 <> +rest:
          all_go_at(~A, ~le, ~C, ~ok, c, f, n, List.sort.pass(~A, ~le, n, r1 <> r2 <> rest), all_pass_at(~A, ~le, ~C, ~ok, c, n, r1 <> r2 <> rest, h))

def all_runs_of_at(~A: Data, ~C: Data, ~ok: C -> A -> Bool, +c: C, xs: List<&2, A>, +h: {all_at(~A, ~C, ~ok, c, xs) == True{} : Bool}) -> {all_runs_at(~A, ~C, ~ok, c, List.sort.runs(A, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      band_i(Bool.and(ok(c, x), True{}), all_runs_at(~A, ~C, ~ok, c, List.sort.runs(A, rest)), band_i(ok(c, x), True{}, band_l(ok(c, x), all_at(~A, ~C, ~ok, c, rest), h), {==}), all_runs_of_at(~A, ~C, ~ok, c, rest, band_r(ok(c, x), all_at(~A, ~C, ~ok, c, rest), h)))

def all_sort_at(~A: Data, ~le: A -> A -> Bool, ~C: Data, ~ok: C -> A -> Bool, +c: C, +xs: List<&2, A>, +h: {all_at(~A, ~C, ~ok, c, xs) == True{} : Bool}) -> {all_at(~A, ~C, ~ok, c, List.sort(~A, ~le, xs)) == True{} : Bool}:
  all_go_at(~A, ~le, ~C, ~ok, c, List.length(&2, A, xs), List.length(&2, A, xs), List.sort.runs(A, xs), all_runs_of_at(~A, ~C, ~ok, c, xs, h))

# What a sort returns is empty only where what it was given is
# ------------------------------------------------------------

def ne_rev(-A: Data, acc: List<&2, A>, +zs: List<&2, A>, h: {List.is_empty(&2, A, zs) == False{} : Bool}) -> {List.is_empty(&2, A, List.reverse.go(&2, A, acc, zs)) == False{} : Bool}:
  match acc:
    case Nil{}:
      h
    case +a <> +rest:
      ne_rev(A, rest, a <> zs, {==})

def ne_step(~A: Data, ~le: A -> A -> Bool, b: Bool, +f: Nat, +acc: List<&2, A>, +x: A, +xt: List<&2, A>, +y: A, +yt: List<&2, A>, ihf: {List.is_empty(&2, A, List.merge.go(~A, ~le, f, (y <> acc, x <> xt, yt))) == False{} : Bool}, iht: {List.is_empty(&2, A, List.merge.go(~A, ~le, f, (x <> acc, xt, y <> yt))) == False{} : Bool}) -> {List.is_empty(&2, A, List.merge.go(~A, ~le, f, List.merge.step(A, acc, x, xt, y, yt, b))) == False{} : Bool}:
  match b:
    case False{}:
      ihf
    case True{}:
      iht

# A merge with something already taken returns something.
def ne_merge_acc(~A: Data, ~le: A -> A -> Bool, fuel: Nat, +a: A, +at: List<&2, A>, +xs: List<&2, A>, +ys: List<&2, A>) -> {List.is_empty(&2, A, List.merge.go(~A, ~le, fuel, (a <> at, xs, ys))) == False{} : Bool}:
  match fuel:
    case 0n:
      ne_rev(A, at, a <> List.append(&2, A, xs, ys), {==})
    case 1n++f:
      match xs ys:
        case Nil{} Nil{}:
          ne_rev(A, at, [a], {==})
        case Nil{} +y <> +yt:
          ne_rev(A, at, a <> y <> yt, {==})
        case +x <> +xt Nil{}:
          ne_rev(A, at, a <> x <> xt, {==})
        case +x <> +xt +y <> +yt:
          ne_step(~A, ~le, le(x, y), f, a <> at, x, xt, y, yt,
            ne_merge_acc(~A, ~le, f, y, a <> at, x <> xt, yt),
            ne_merge_acc(~A, ~le, f, x, a <> at, xt, y <> yt))

# A merge of a run with something in it returns something.
def ne_merge_x(~A: Data, ~le: A -> A -> Bool, fuel: Nat, +acc: List<&2, A>, +x: A, +xt: List<&2, A>, +ys: List<&2, A>) -> {List.is_empty(&2, A, List.merge.go(~A, ~le, fuel, (acc, x <> xt, ys))) == False{} : Bool}:
  match fuel:
    case 0n:
      ne_rev(A, acc, x <> List.append(&2, A, xt, ys), {==})
    case 1n++f:
      match ys:
        case Nil{}:
          ne_rev(A, acc, x <> xt, {==})
        case +y <> +yt:
          ne_step(~A, ~le, le(x, y), f, acc, x, xt, y, yt,
            ne_merge_acc(~A, ~le, f, y, acc, x <> xt, yt),
            ne_merge_acc(~A, ~le, f, x, acc, xt, y <> yt))

# Every run holds something.
def runs_ne(-A: Data, rs: List<&2, List<&2, A>>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> rest:
      Bool.and(Bool.not(List.is_empty(&2, A, r)), runs_ne(A, rest))

def ne_merge_run(~A: Data, ~le: A -> A -> Bool, +n: Nat, r1: List<&2, A>, +r2: List<&2, A>, h: {Bool.not(List.is_empty(&2, A, r1)) == True{} : Bool}) -> {Bool.not(List.is_empty(&2, A, List.merge.go(~A, ~le, n, (Nil{}, r1, r2)))) == True{} : Bool}:
  match r1:
    case Nil{}:
      Empty.absurd({Bool.not(List.is_empty(&2, A, List.merge.go(~A, ~le, n, (Nil{}, Nil{}, r2)))) == True{} : Bool}, S.false_true(h))
    case +x <> +xt:
      %Equal.sym(Bool, List.is_empty(&2, A, List.merge.go(~A, ~le, n, (Nil{}, x <> xt, r2))), False{}, ne_merge_x(~A, ~le, n, Nil{}, x, xt, r2)) : {Bool.not(_) == True{} : Bool}
      {==}

def ne_pass(~A: Data, ~le: A -> A -> Bool, +n: Nat, runs: List<&2, List<&2, A>>, +h: {runs_ne(A, runs) == True{} : Bool}) -> {runs_ne(A, List.sort.pass(~A, ~le, n, runs)) == True{} : Bool}:
  match runs:
    case Nil{}:
      {==}
    case +r <> Nil{}:
      h
    case +r1 <> +r2 <> +rest:
      band_i(Bool.not(List.is_empty(&2, A, List.merge.go(~A, ~le, n, (Nil{}, r1, r2)))), runs_ne(A, List.sort.pass(~A, ~le, n, rest)),
        ne_merge_run(~A, ~le, n, r1, r2, band_l(Bool.not(List.is_empty(&2, A, r1)), runs_ne(A, r2 <> rest), h)),
        ne_pass(~A, ~le, n, rest, band_r(Bool.not(List.is_empty(&2, A, r2)), runs_ne(A, rest), band_r(Bool.not(List.is_empty(&2, A, r1)), runs_ne(A, r2 <> rest), h))))

def ne_not(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, S.false_true(h))

def ne_app(-A: Data, r: List<&2, A>, -ys: List<&2, A>, h: {Bool.not(List.is_empty(&2, A, r)) == True{} : Bool}) -> {List.is_empty(&2, A, List.append(&2, A, r, ys)) == False{} : Bool}:
  match r:
    case Nil{}:
      Empty.absurd({List.is_empty(&2, A, ys) == False{} : Bool}, S.false_true(h))
    case x <> xt:
      {==}

def ne_go(~A: Data, ~le: A -> A -> Bool, fuel: Nat, +n: Nat, runs: List<&2, List<&2, A>>, +hr: {runs_ne(A, runs) == True{} : Bool}, hl: {List.is_empty(&2, List<&2, A>, runs) == False{} : Bool}) -> {List.is_empty(&2, A, List.sort.go(~A, ~le, fuel, n, runs)) == False{} : Bool}:
  match fuel:
    case 0n:
      match runs:
        case Nil{}:
          Empty.absurd({List.is_empty(&2, A, Nil{}) == False{} : Bool}, S.true_false(hl))
        case +r <> +rest:
          ne_app(A, r, List.concat(&2, A, rest), band_l(Bool.not(List.is_empty(&2, A, r)), runs_ne(A, rest), hr))
    case 1n++f:
      match runs:
        case Nil{}:
          Empty.absurd({List.is_empty(&2, A, Nil{}) == False{} : Bool}, S.true_false(hl))
        case +r <> Nil{}:
          ne_not(List.is_empty(&2, A, r), band_l(Bool.not(List.is_empty(&2, A, r)), True{}, hr))
        case +r1 <> +r2 <> +rest:
          ne_go(~A, ~le, f, n, List.sort.pass(~A, ~le, n, r1 <> r2 <> rest), ne_pass(~A, ~le, n, r1 <> r2 <> rest, hr), {==})

def ne_runs(-A: Data, xs: List<&2, A>) -> {runs_ne(A, List.sort.runs(A, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      ne_runs(A, rest)

# A sort by any order of something returns something.
def ne_sort(~A: Data, ~le: A -> A -> Bool, xs: List<&2, A>, h: {List.is_empty(&2, A, xs) == False{} : Bool}) -> {List.is_empty(&2, A, List.sort(~A, ~le, xs)) == False{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({List.is_empty(&2, A, List.sort(~A, ~le, Nil{})) == False{} : Bool}, S.true_false(h))
    case +x <> +rest:
      ne_go(~A, ~le, List.length(&2, A, x <> rest), List.length(&2, A, x <> rest), List.sort.runs(A, x <> rest), ne_runs(A, x <> rest), {==})
