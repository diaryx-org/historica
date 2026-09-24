# What a merge shows and what it states. A resolution `record --merge`
# writes, assembled as `cat` assembles one, is the folder's file: the
# alignment it is written from reads as what the folder holds, the pieces
# are that alignment spelled maximally, and each `keep` of a name brings
# back the item the walk minted under it.
import Base
import ./ops.bend as Ops
import ./similar.bend as Sim
import ./resolution.bend as Res
import ./merge.bend as Merge
import ./store.bend as Store
import ./conflict.bend as C
import ./commands.bend as Main
import ./string_lemmas.bend as SL
import ./hunk_lemmas.bend as HL
import ./anchor_lemmas.bend as AL
import ./composition_lemmas.bend as Comp
import ./similar_lemmas.bend as SimL
import ./diff_lemmas.bend as Diff
import ./blame_lemmas.bend as BlameL

# What an alignment stands for
# ----------------------------

# The items a list of names stands under, and the items an alignment reads
# as: each kept name's item and each line written.
def items.of(ns: List<&2, C.Named>) -> List<&2, Ops.Item>:
  match ns:
    case Nil{}:
      Nil{}
    case C.Named{r, it} <> rest:
      it <> items.of(rest)

def said.items(ss: List<&2, C.Said>) -> List<&2, Ops.Item>:
  match ss:
    case Nil{}:
      Nil{}
    case C.Said.Kept{C.Named{r, it}} <> rest:
      it <> said.items(rest)
    case C.Said.Wrote{y} <> rest:
      y <> said.items(rest)

# Whether the documents here mint every name an alignment keeps.
def said.mint(+ds: List<&2, Store.Doc>, ss: List<&2, C.Said>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case C.Said.Kept{n} <> rest:
      Bool.and(Main.mints(ds, n), said.mint(ds, rest))
    case C.Said.Wrote{y} <> rest:
      said.mint(ds, rest)

# Small facts
# -----------

def mdisc(m: Maybe<&2, Res.Doc>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{d}:
      Empty

def none_some(-d: Res.Doc, e: {None{} == Some{d} : Maybe<&2, Res.Doc>}) -> Empty:
  %e : {mdisc(_) : Type}
  Unit{}

def some_eq(-a: Res.Doc, -b: Res.Doc, e: {Some{a} == Some{b} : Maybe<&2, Res.Doc>}) -> {a == b : Res.Doc}:
  Equal.cong(Maybe<&2, Res.Doc>, Res.Doc, m => Maybe.default(&2, Res.Doc, m, a), Some{a}, Some{b}, e)

def rdisc(r: Result<&2, &2, String, List<&2, Ops.Item>>) -> Type:
  match r:
    case Done{x}:
      Empty
    case Fail{e}:
      Unit

def fail_done(-e: String, -x: List<&2, Ops.Item>, h: {Fail{e} == Done{x} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> Empty:
  %h : {rdisc(_) : Type}
  Unit{}

def done_eq(-a: List<&2, Ops.Item>, -b: List<&2, Ops.Item>, h: {Done{a} == Done{b} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {a == b : List<&2, Ops.Item>}:
  Equal.cong(Result<&2, &2, String, List<&2, Ops.Item>>, List<&2, Ops.Item>, r => Result.default(&2, &2, String, List<&2, Ops.Item>, r, a), Done{a}, Done{b}, h)

def nat_gt_false(n: Nat) -> {Cmp.is_gt(Nat.cmp(0n, n)) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      {==}

def take_zero(xs: List<&2, Ops.Item>) -> {List.take(&2, Ops.Item, xs, 0n) == Nil{} : List<&2, Ops.Item>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      {==}

def drop_zero(xs: List<&2, Ops.Item>) -> {xs == List.drop(&2, Ops.Item, xs, 0n) : List<&2, Ops.Item>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      {==}

def idisc(m: Maybe<&2, Ops.Item>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{d}:
      Empty

def none_some_item(-d: Ops.Item, e: {None{} == Some{d} : Maybe<&2, Ops.Item>}) -> Empty:
  %e : {idisc(_) : Type}
  Unit{}

# An item at a position is the head of what is left from there, and there
# is room for it.
def get_drop(xs: List<&2, Ops.Item>, m: Nat, -x: Ops.Item, e: {List.get(&2, Ops.Item, xs, m) == Some{x} : Maybe<&2, Ops.Item>}) -> {List.drop(&2, Ops.Item, xs, m) == x <> List.drop(&2, Ops.Item, xs, 1n+m) : List<&2, Ops.Item>}:
  match xs m:
    case Nil{} _:
      Empty.absurd({List.drop(&2, Ops.Item, Nil{}, m) == x <> List.drop(&2, Ops.Item, Nil{}, 1n+m) : List<&2, Ops.Item>}, none_some_item(x, e))
    case +h <> +t 0n:
      %Equal.cong(Maybe<&2, Ops.Item>, Ops.Item, v => Maybe.default(&2, Ops.Item, v, h), Some{h}, Some{x}, e) : {h <> t == _ <> List.drop(&2, Ops.Item, t, 0n) : List<&2, Ops.Item>}
      %drop_zero(t) : {h <> t == h <> _ : List<&2, Ops.Item>}
      {==}
    case h <> +t 1n+p:
      get_drop(t, p, x, e)

def room(items: List<&2, Ops.Item>, m: Nat, -x: Ops.Item, e: {List.get(&2, Ops.Item, items, m) == Some{x} : Maybe<&2, Ops.Item>}) -> {Nat.is_gt(Nat.add(m, 1n), List.length(&2, Ops.Item, items)) == False{} : Bool}:
  match items m:
    case Nil{} _:
      Empty.absurd({Nat.is_gt(Nat.add(m, 1n), List.length(&2, Ops.Item, Nil{})) == False{} : Bool}, none_some_item(x, e))
    case h <> +t 0n:
      nat_gt_false(List.length(&2, Ops.Item, t))
    case h <> +t 1n+p:
      room(t, p, x, e)

# A `keep` of one name brings back the item the document mints under it.
def keep_one.got(+d: String, +m: Nat, +it: Ops.Item, +items: List<&2, Ops.Item>, g: Maybe<&2, Ops.Item>, +eg: {List.get(&2, Ops.Item, items, m) == g : Maybe<&2, Ops.Item>}, hm: {Main.mints.item(it, g) == True{} : Bool}) -> {Main.kept.run(d, m, 1n, items) == Done{[it]} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match g:
    case None{}:
      Empty.absurd({Main.kept.run(d, m, 1n, items) == Done{[it]} : Result<&2, &2, String, List<&2, Ops.Item>>}, Comp.false_true(hm))
    case Some{+x}:
      %Equal.sym(Bool, Nat.is_gt(Nat.add(m, 1n), List.length(&2, Ops.Item, items)), False{}, room(items, m, x, eg)) : {Main.kept.cut(d, m, 1n, items, _) == Done{[it]} : Result<&2, &2, String, List<&2, Ops.Item>>}
      %Equal.sym(List<&2, Ops.Item>, List.drop(&2, Ops.Item, items, m), x <> List.drop(&2, Ops.Item, items, 1n+m), get_drop(items, m, x, eg)) : {Done{List.take(&2, Ops.Item, _, 1n)} == Done{[it]} : Result<&2, &2, String, List<&2, Ops.Item>>}
      %Equal.sym(List<&2, Ops.Item>, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, items, 1n+m), 0n), Nil{}, take_zero(List.drop(&2, Ops.Item, items, 1n+m))) : {Done{x <> _} == Done{[it]} : Result<&2, &2, String, List<&2, Ops.Item>>}
      %SimL.item_is_equal(x, it, hm) : {Done{[x]} == Done{[_]} : Result<&2, &2, String, List<&2, Ops.Item>>}
      {==}

def keep_one.doc(+d: String, +m: Nat, +it: Ops.Item, doc: Maybe<&2, String>, hm: {Main.mints.doc(m, it, doc) == True{} : Bool}) -> {Main.kept.found(d, m, 1n, doc) == Done{[it]} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match doc:
    case None{}:
      Empty.absurd({Main.kept.found(d, m, 1n, None{}) == Done{[it]} : Result<&2, &2, String, List<&2, Ops.Item>>}, Comp.false_true(hm))
    case Some{+text}:
      keep_one.got(d, m, it, Main.minted(text), List.get(&2, Ops.Item, Main.minted(text), m), {==}, hm)

# A `keep` that runs on from a name brings back the item under it, then
# the rest of the run.
def keep_more.cut(+d: String, +m: Nat, +c: Nat, +items: List<&2, Ops.Item>, +h: List<&2, Ops.Item>, b: Bool, +eb: {Nat.is_gt(1n+Nat.add(m, c), List.length(&2, Ops.Item, items)) == b : Bool}, e: {Main.kept.cut(d, 1n+m, c, items, b) == Done{h} : Result<&2, &2, String, List<&2, Ops.Item>>}, -it: Ops.Item, +x: Ops.Item, +ex: {x == it : Ops.Item}, +eg: {List.get(&2, Ops.Item, items, m) == Some{x} : Maybe<&2, Ops.Item>}) -> {Main.kept.run(d, m, 1n+c, items) == Done{it <> h} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match b:
    case True{}:
      Empty.absurd({Main.kept.run(d, m, 1n+c, items) == Done{it <> h} : Result<&2, &2, String, List<&2, Ops.Item>>}, fail_done("this resolution keeps up to item " ++ Nat.show(Nat.add(1n+m, c)) ++ " of " ++ d ++ ", which mints " ++ Nat.show(List.length(&2, Ops.Item, items)) ++ "; count the `+` lines of that document to see what the run should say", h, e))
    case False{}:
      %Equal.sym(Nat, Nat.add(m, 1n+c), 1n+Nat.add(m, c), Diff.add_succ(m, c)) : {Main.kept.cut(d, m, 1n+c, items, Nat.is_gt(_, List.length(&2, Ops.Item, items))) == Done{it <> h} : Result<&2, &2, String, List<&2, Ops.Item>>}
      %Equal.sym(Bool, Nat.is_gt(1n+Nat.add(m, c), List.length(&2, Ops.Item, items)), False{}, eb) : {Main.kept.cut(d, m, 1n+c, items, _) == Done{it <> h} : Result<&2, &2, String, List<&2, Ops.Item>>}
      %Equal.sym(List<&2, Ops.Item>, List.drop(&2, Ops.Item, items, m), x <> List.drop(&2, Ops.Item, items, 1n+m), get_drop(items, m, x, eg)) : {Done{List.take(&2, Ops.Item, _, 1n+c)} == Done{it <> h} : Result<&2, &2, String, List<&2, Ops.Item>>}
      %Equal.sym(List<&2, Ops.Item>, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, items, 1n+m), c), h, done_eq(List.take(&2, Ops.Item, List.drop(&2, Ops.Item, items, 1n+m), c), h, e)) : {Done{x <> _} == Done{it <> h} : Result<&2, &2, String, List<&2, Ops.Item>>}
      %Equal.sym(Ops.Item, x, it, ex) : {Done{_ <> h} == Done{it <> h} : Result<&2, &2, String, List<&2, Ops.Item>>}
      {==}

def keep_more.got(+d: String, +m: Nat, +c: Nat, +it: Ops.Item, +items: List<&2, Ops.Item>, +h: List<&2, Ops.Item>, g: Maybe<&2, Ops.Item>, +eg: {List.get(&2, Ops.Item, items, m) == g : Maybe<&2, Ops.Item>}, hm: {Main.mints.item(it, g) == True{} : Bool}, +e: {Main.kept.run(d, 1n+m, c, items) == Done{h} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Main.kept.run(d, m, 1n+c, items) == Done{it <> h} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match g:
    case None{}:
      Empty.absurd({Main.kept.run(d, m, 1n+c, items) == Done{it <> h} : Result<&2, &2, String, List<&2, Ops.Item>>}, Comp.false_true(hm))
    case Some{+x}:
      keep_more.cut(d, m, c, items, h, Nat.is_gt(1n+Nat.add(m, c), List.length(&2, Ops.Item, items)), {==}, e, it, x, SimL.item_is_equal(x, it, hm), eg)

def keep_more.doc(+d: String, +m: Nat, +c: Nat, +it: Ops.Item, +h: List<&2, Ops.Item>, doc: Maybe<&2, String>, hm: {Main.mints.doc(m, it, doc) == True{} : Bool}, e: {Main.kept.found(d, 1n+m, c, doc) == Done{h} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Main.kept.found(d, m, 1n+c, doc) == Done{it <> h} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match doc:
    case None{}:
      Empty.absurd({Main.kept.found(d, m, 1n+c, None{}) == Done{it <> h} : Result<&2, &2, String, List<&2, Ops.Item>>}, Comp.false_true(hm))
    case Some{+text}:
      keep_more.got(d, m, c, it, Main.minted(text), h, List.get(&2, Ops.Item, Main.minted(text), m), {==}, hm, e)

# The pieces
# ----------

def piece_one(+ds: List<&2, Store.Doc>, +d: String, +m: Nat, +it: Ops.Item, hm: {Main.mints(ds, C.Named{C.Ref{d, m}, it}) == True{} : Bool}) -> {Main.assemble.piece(ds, Res.Piece.Keep{d, m, 1n}) == Done{[it]} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  keep_one.doc(d, m, it, Main.doc_by_id(ds, d), hm)

def piece_more(+ds: List<&2, Store.Doc>, +d: String, +m: Nat, +c: Nat, +it: Ops.Item, +h: List<&2, Ops.Item>, hm: {Main.mints(ds, C.Named{C.Ref{d, m}, it}) == True{} : Bool}, e: {Main.assemble.piece(ds, Res.Piece.Keep{d, 1n+m, c}) == Done{h} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Main.assemble.piece(ds, Res.Piece.Keep{d, m, 1n+c}) == Done{it <> h} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  keep_more.doc(d, m, c, it, h, Main.doc_by_id(ds, d), hm, e)

# A line written before an insert joins it; before anything else, it is an
# insert of its own.
def wrote_ins(+y: Ops.Item, +its: List<&2, Ops.Item>, r: Result<&2, &2, String, List<&2, Ops.Item>>, +L: List<&2, Ops.Item>, ih: {Main.assemble.cons(Done{its}, r) == Done{L} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Main.assemble.cons(Done{y <> its}, r) == Done{y <> L} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match r:
    case Fail{e}:
      Empty.absurd({Main.assemble.cons(Done{y <> its}, Fail{e}) == Done{y <> L} : Result<&2, &2, String, List<&2, Ops.Item>>}, fail_done(e, L, ih))
    case Done{+l}:
      %done_eq(List.append(&2, Ops.Item, its, l), L, ih) : {Done{y <> List.append(&2, Ops.Item, its, l)} == Done{y <> _} : Result<&2, &2, String, List<&2, Ops.Item>>}
      {==}

def put_wrote(+ds: List<&2, Store.Doc>, +y: Ops.Item, ps: List<&2, Res.Piece>, +L: List<&2, Ops.Item>, ih: {Main.assemble.pieces(ds, ps) == Done{L} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Main.assemble.pieces(ds, C.pieces.put(C.Said.Wrote{y}, ps)) == Done{y <> L} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match ps:
    case Nil{}:
      %done_eq(Nil{}, L, ih) : {Done{[y]} == Done{y <> _} : Result<&2, &2, String, List<&2, Ops.Item>>}
      {==}
    case Res.Piece.Insert{+its} <> +more:
      wrote_ins(y, its, Main.assemble.pieces(ds, more), L, ih)
    case Res.Piece.Keep{+e, +first, +count} <> +more:
      %Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Main.assemble.pieces(ds, Res.Piece.Keep{e, first, count} <> more), Done{L}, ih) : {Main.assemble.cons(Done{[y]}, _) == Done{y <> L} : Result<&2, &2, String, List<&2, Ops.Item>>}
      {==}

# A name kept before the run it continues joins it.
def merged.split(+ds: List<&2, Store.Doc>, +d: String, +m: Nat, +c: Nat, +it: Ops.Item, +L: List<&2, Ops.Item>, hm: {Main.mints(ds, C.Named{C.Ref{d, m}, it}) == True{} : Bool}, a: Result<&2, &2, String, List<&2, Ops.Item>>, +ea: {Main.assemble.piece(ds, Res.Piece.Keep{d, 1n+m, c}) == a : Result<&2, &2, String, List<&2, Ops.Item>>}, r: Result<&2, &2, String, List<&2, Ops.Item>>, e: {Main.assemble.cons(a, r) == Done{L} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Main.assemble.cons(Main.assemble.piece(ds, Res.Piece.Keep{d, m, 1n+c}), r) == Done{it <> L} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match a r:
    case Fail{x} _:
      Empty.absurd({Main.assemble.cons(Main.assemble.piece(ds, Res.Piece.Keep{d, m, 1n+c}), r) == Done{it <> L} : Result<&2, &2, String, List<&2, Ops.Item>>}, fail_done(x, L, e))
    case Done{h} Fail{x}:
      Empty.absurd({Main.assemble.cons(Main.assemble.piece(ds, Res.Piece.Keep{d, m, 1n+c}), Fail{x}) == Done{it <> L} : Result<&2, &2, String, List<&2, Ops.Item>>}, fail_done(x, L, e))
    case Done{+h} Done{+l}:
      %Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Main.assemble.piece(ds, Res.Piece.Keep{d, m, 1n+c}), Done{it <> h}, piece_more(ds, d, m, c, it, h, hm, ea)) : {Main.assemble.cons(_, Done{l}) == Done{it <> L} : Result<&2, &2, String, List<&2, Ops.Item>>}
      %done_eq(List.append(&2, Ops.Item, h, l), L, e) : {Done{it <> List.append(&2, Ops.Item, h, l)} == Done{it <> _} : Result<&2, &2, String, List<&2, Ops.Item>>}
      {==}

# Where the names meet, the run the next piece holds is the one this name
# continues.
def same_run(+ds: List<&2, Store.Doc>, +d: String, +e: String, +m: Nat, +first: Nat, +count: Nat, +more: List<&2, Res.Piece>, +L: List<&2, Ops.Item>, ed: {d == e : String}, ef: {1n+m == first : Nat}, ih: {Main.assemble.pieces(ds, Res.Piece.Keep{e, first, count} <> more) == Done{L} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Main.assemble.cons(Main.assemble.piece(ds, Res.Piece.Keep{d, 1n+m, count}), Main.assemble.pieces(ds, more)) == Done{L} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  %Equal.sym(String, d, e, ed) : {Main.assemble.cons(Main.assemble.piece(ds, Res.Piece.Keep{_, 1n+m, count}), Main.assemble.pieces(ds, more)) == Done{L} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %Equal.sym(Nat, 1n+m, first, ef) : {Main.assemble.cons(Main.assemble.piece(ds, Res.Piece.Keep{e, _, count}), Main.assemble.pieces(ds, more)) == Done{L} : Result<&2, &2, String, List<&2, Ops.Item>>}
  ih

def kept_keep(+ds: List<&2, Store.Doc>, +d: String, +m: Nat, +it: Ops.Item, +e: String, +first: Nat, +count: Nat, +more: List<&2, Res.Piece>, +L: List<&2, Ops.Item>, +hm: {Main.mints(ds, C.Named{C.Ref{d, m}, it}) == True{} : Bool}, +ih: {Main.assemble.pieces(ds, Res.Piece.Keep{e, first, count} <> more) == Done{L} : Result<&2, &2, String, List<&2, Ops.Item>>}, b: Bool, +eb: {Bool.and(String.eq(d, e), Nat.is_eq(1n+m, first)) == b : Bool}) -> {Main.assemble.pieces(ds, Bool.pick(List<&2, Res.Piece>, b, Res.Piece.Keep{d, m, 1n+count} <> more, Res.Piece.Keep{d, m, 1n} <> Res.Piece.Keep{e, first, count} <> more)) == Done{it <> L} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match b:
    case False{}:
      %Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Main.assemble.piece(ds, Res.Piece.Keep{d, m, 1n}), Done{[it]}, piece_one(ds, d, m, it, hm)) : {Main.assemble.cons(_, Main.assemble.pieces(ds, Res.Piece.Keep{e, first, count} <> more)) == Done{it <> L} : Result<&2, &2, String, List<&2, Ops.Item>>}
      %Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Main.assemble.pieces(ds, Res.Piece.Keep{e, first, count} <> more), Done{L}, ih) : {Main.assemble.cons(Done{[it]}, _) == Done{it <> L} : Result<&2, &2, String, List<&2, Ops.Item>>}
      {==}
    case True{}:
      +ed = SL.eq_true(d, e, Comp.and_left(String.eq(d, e), Nat.is_eq(1n+m, first), eb))
      +ef = Comp.eq_of_is_eq(1n+m, first, Comp.and_right(String.eq(d, e), Nat.is_eq(1n+m, first), eb))
      merged.split(ds, d, m, count, it, L, hm, Main.assemble.piece(ds, Res.Piece.Keep{d, 1n+m, count}), {==}, Main.assemble.pieces(ds, more), same_run(ds, d, e, m, first, count, more, L, ed, ef, ih))

def put_kept(+ds: List<&2, Store.Doc>, +d: String, +m: Nat, +it: Ops.Item, ps: List<&2, Res.Piece>, +L: List<&2, Ops.Item>, +hm: {Main.mints(ds, C.Named{C.Ref{d, m}, it}) == True{} : Bool}, +ih: {Main.assemble.pieces(ds, ps) == Done{L} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Main.assemble.pieces(ds, C.pieces.put(C.Said.Kept{C.Named{C.Ref{d, m}, it}}, ps)) == Done{it <> L} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match ps:
    case Nil{}:
      %Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Main.assemble.piece(ds, Res.Piece.Keep{d, m, 1n}), Done{[it]}, piece_one(ds, d, m, it, hm)) : {Main.assemble.cons(_, Done{Nil{}}) == Done{it <> L} : Result<&2, &2, String, List<&2, Ops.Item>>}
      %done_eq(Nil{}, L, ih) : {Done{[it]} == Done{it <> _} : Result<&2, &2, String, List<&2, Ops.Item>>}
      {==}
    case Res.Piece.Insert{+its} <> +more:
      %Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Main.assemble.piece(ds, Res.Piece.Keep{d, m, 1n}), Done{[it]}, piece_one(ds, d, m, it, hm)) : {Main.assemble.cons(_, Main.assemble.pieces(ds, Res.Piece.Insert{its} <> more)) == Done{it <> L} : Result<&2, &2, String, List<&2, Ops.Item>>}
      %Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Main.assemble.pieces(ds, Res.Piece.Insert{its} <> more), Done{L}, ih) : {Main.assemble.cons(Done{[it]}, _) == Done{it <> L} : Result<&2, &2, String, List<&2, Ops.Item>>}
      {==}
    case Res.Piece.Keep{+e, +first, +count} <> +more:
      kept_keep(ds, d, m, it, e, first, count, more, L, hm, ih, Bool.and(String.eq(d, e), Nat.is_eq(1n+m, first)), {==})

# The pieces an alignment is spelled as, assembled, read as the alignment
# does, wherever the documents mint every name it keeps.
def pieces_assemble(+ds: List<&2, Store.Doc>, ss: List<&2, C.Said>, +h: {said.mint(ds, ss) == True{} : Bool}) -> {Main.assemble.pieces(ds, C.pieces(ss)) == Done{said.items(ss)} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match ss:
    case Nil{}:
      {==}
    case C.Said.Kept{C.Named{C.Ref{+d, +m}, +it}} <> +rest:
      put_kept(ds, d, m, it, C.pieces(rest), said.items(rest), Comp.and_left(Main.mints(ds, C.Named{C.Ref{d, m}, it}), said.mint(ds, rest), h), pieces_assemble(ds, rest, Comp.and_right(Main.mints(ds, C.Named{C.Ref{d, m}, it}), said.mint(ds, rest), h)))
    case C.Said.Wrote{+y} <> +rest:
      put_wrote(ds, y, C.pieces(rest), said.items(rest), pieces_assemble(ds, rest, h))

# What the alignment reads as
# ---------------------------

# The items the names stand under are the file the walk reads.
def named_file(ns: List<&2, Merge.Node>, +dg: List<&2, String>) -> {items.of(C.named.of(ns, dg)) == Merge.file.of(ns) : List<&2, Ops.Item>}:
  match ns:
    case Nil{}:
      {==}
    case +n <> +rest:
      %Equal.sym(List<&2, Ops.Item>, items.of(C.named.of(rest, dg)), Merge.file.of(rest), named_file(rest, dg)) : {Merge.Node.item(n) <> _ == Merge.Node.item(n) <> Merge.file.of(rest) : List<&2, Ops.Item>}
      {==}

# An alignment that takes the proposal to the folder, read by name, is the
# folder: each name kept stands over the line the folder holds there, and
# each line written is one.
def said_fit(ms: List<&2, Ops.Move>, named: List<&2, C.Named>, +new: List<&2, Ops.Item>, +h: {Sim.fit(ms, items.of(named), new) == True{} : Bool}) -> {said.items(C.said.of(ms, named)) == new : List<&2, Ops.Item>}:
  match ms named new:
    case Nil{} Nil{} Nil{}:
      {==}
    case Nil{} Nil{} +z <> +zs:
      Empty.absurd({said.items(C.said.of(Nil{}, Nil{})) == z <> zs : List<&2, Ops.Item>}, Comp.false_true(h))
    case Nil{} C.Named{+r, +x} <> +more Nil{}:
      Empty.absurd({said.items(C.said.of(Nil{}, C.Named{r, x} <> more)) == Nil{} : List<&2, Ops.Item>}, Comp.false_true(h))
    case Nil{} C.Named{+r, +x} <> +more +z <> +zs:
      Empty.absurd({said.items(C.said.of(Nil{}, C.Named{r, x} <> more)) == z <> zs : List<&2, Ops.Item>}, Comp.false_true(h))
    case Ops.Keep{} <> +rs Nil{} +new:
      Empty.absurd({said.items(C.said.of(Ops.Keep{} <> rs, Nil{})) == new : List<&2, Ops.Item>}, Comp.false_true(h))
    case Ops.Keep{} <> +rs C.Named{+r, +x} <> +more Nil{}:
      Empty.absurd({said.items(C.said.of(Ops.Keep{} <> rs, C.Named{r, x} <> more)) == Nil{} : List<&2, Ops.Item>}, Comp.false_true(h))
    case Ops.Keep{} <> +rs C.Named{+r, +x} <> +more +z <> +zs:
      %Equal.sym(List<&2, Ops.Item>, said.items(C.said.of(rs, more)), zs, said_fit(rs, more, zs, Comp.and_right(Sim.fit.item(x, z), Sim.fit(rs, items.of(more), zs), h))) : {x <> _ == z <> zs : List<&2, Ops.Item>}
      %SimL.item_is_equal(x, z, Comp.and_left(Sim.fit.item(x, z), Sim.fit(rs, items.of(more), zs), h)) : {x <> zs == _ <> zs : List<&2, Ops.Item>}
      {==}
    case Ops.Del{+d} <> +rs Nil{} +new:
      Empty.absurd({said.items(C.said.of(Ops.Del{d} <> rs, Nil{})) == new : List<&2, Ops.Item>}, Comp.false_true(h))
    case Ops.Del{+d} <> +rs C.Named{+r, +x} <> +more +new:
      said_fit(rs, more, new, Comp.and_right(Ops.agrees(d, x), Sim.fit(rs, items.of(more), new), h))
    case Ops.Ins{+y} <> +rs +named Nil{}:
      Empty.absurd({said.items(C.said.of(Ops.Ins{y} <> rs, named)) == Nil{} : List<&2, Ops.Item>}, Comp.false_true(h))
    case Ops.Ins{+y} <> +rs Nil{} +z <> +zs:
      %Equal.sym(List<&2, Ops.Item>, said.items(C.said.of(rs, Nil{})), zs, said_fit(rs, Nil{}, zs, Comp.and_right(Sim.fit.item(y, z), Sim.fit(rs, Nil{}, zs), h))) : {y <> _ == z <> zs : List<&2, Ops.Item>}
      %SimL.item_is_equal(y, z, Comp.and_left(Sim.fit.item(y, z), Sim.fit(rs, Nil{}, zs), h)) : {y <> zs == _ <> zs : List<&2, Ops.Item>}
      {==}
    case Ops.Ins{+y} <> +rs C.Named{+r, +x} <> +more +z <> +zs:
      %Equal.sym(List<&2, Ops.Item>, said.items(C.said.of(rs, C.Named{r, x} <> more)), zs, said_fit(rs, C.Named{r, x} <> more, zs, Comp.and_right(Sim.fit.item(y, z), Sim.fit(rs, x <> items.of(more), zs), h))) : {y <> _ == z <> zs : List<&2, Ops.Item>}
      %SimL.item_is_equal(y, z, Comp.and_left(Sim.fit.item(y, z), Sim.fit(rs, x <> items.of(more), zs), h)) : {y <> zs == _ <> zs : List<&2, Ops.Item>}
      {==}

# Every line stated afresh reads as the lines, and names nothing.
def wrote_items(its: List<&2, Ops.Item>) -> {said.items(C.wrote.all(its)) == its : List<&2, Ops.Item>}:
  match its:
    case Nil{}:
      {==}
    case +it <> +rest:
      %Equal.sym(List<&2, Ops.Item>, said.items(C.wrote.all(rest)), rest, wrote_items(rest)) : {it <> _ == it <> rest : List<&2, Ops.Item>}
      {==}

def wrote_mint(+ds: List<&2, Store.Doc>, its: List<&2, Ops.Item>) -> {said.mint(ds, C.wrote.all(its)) == True{} : Bool}:
  match its:
    case Nil{}:
      {==}
    case it <> rest:
      wrote_mint(ds, rest)

# An alignment names only what the walk stood under, so where those names
# are minted, so are the ones it keeps.
def said_mint(+ds: List<&2, Store.Doc>, ms: List<&2, Ops.Move>, named: List<&2, C.Named>, +h: {Main.all_mint(ds, named) == True{} : Bool}) -> {said.mint(ds, C.said.of(ms, named)) == True{} : Bool}:
  match ms named:
    case Nil{} Nil{}:
      {==}
    case Nil{} n <> more:
      {==}
    case Ops.Keep{} <> +rs Nil{}:
      said_mint(ds, rs, Nil{}, {==})
    case Ops.Keep{} <> +rs +n <> +more:
      %Equal.sym(Bool, Main.mints(ds, n), True{}, Comp.and_left(Main.mints(ds, n), Main.all_mint(ds, more), h)) : {Bool.and(_, said.mint(ds, C.said.of(rs, more))) == True{} : Bool}
      said_mint(ds, rs, more, Comp.and_right(Main.mints(ds, n), Main.all_mint(ds, more), h))
    case Ops.Del{d} <> +rs Nil{}:
      said_mint(ds, rs, Nil{}, {==})
    case Ops.Del{d} <> +rs +n <> +more:
      said_mint(ds, rs, more, Comp.and_right(Main.mints(ds, n), Main.all_mint(ds, more), h))
    case Ops.Ins{y} <> +rs Nil{}:
      said_mint(ds, rs, Nil{}, h)
    case Ops.Ins{y} <> +rs +n <> +more:
      said_mint(ds, rs, n <> more, h)

def checked_items(+ms: List<&2, Ops.Move>, named: List<&2, C.Named>, +after: List<&2, Ops.Item>, ok: Bool, +e: {Sim.fit(ms, items.of(named), after) == ok : Bool}) -> {said.items(C.said.checked(ms, named, after, ok)) == after : List<&2, Ops.Item>}:
  match ok:
    case True{}:
      said_fit(ms, named, after, e)
    case False{}:
      wrote_items(after)

def checked_mint(+ds: List<&2, Store.Doc>, +ms: List<&2, Ops.Move>, named: List<&2, C.Named>, +after: List<&2, Ops.Item>, ok: Bool, +h: {Main.all_mint(ds, named) == True{} : Bool}) -> {said.mint(ds, C.said.checked(ms, named, after, ok)) == True{} : Bool}:
  match ok:
    case True{}:
      said_mint(ds, ms, named, h)
    case False{}:
      wrote_mint(ds, after)

def fit_named(+ms: List<&2, Ops.Move>, +vt: List<&2, Merge.Node>, +dg: List<&2, String>, +after: List<&2, Ops.Item>) -> {Sim.fit(ms, items.of(C.named.of(vt, dg)), after) == Sim.fit(ms, Merge.file.of(vt), after) : Bool}:
  %named_file(vt, dg) : {Sim.fit(ms, items.of(C.named.of(vt, dg)), after) == Sim.fit(ms, _, after) : Bool}
  {==}

# What `said` reads as is the folder, whatever the alignment did.
def said_items(j: C.Joined, +after: List<&2, Ops.Item>) -> {said.items(C.said(j, after)) == after : List<&2, Ops.Item>}:
  match j:
    case C.Joined{ns, +dg, g, +t}:
      checked_items(Sim.walked.moves(Sim.walked.go(Sim.ops(Merge.file(t), after), Sim.Walked{Merge.file(t), after, Nil{}})), C.named.of(Merge.visible(t), dg), after, Sim.fit(Sim.walked.moves(Sim.walked.go(Sim.ops(Merge.file(t), after), Sim.Walked{Merge.file(t), after, Nil{}})), Merge.file(t), after), fit_named(Sim.walked.moves(Sim.walked.go(Sim.ops(Merge.file(t), after), Sim.Walked{Merge.file(t), after, Nil{}})), Merge.visible(t), dg, after))

def said_minted(+ds: List<&2, Store.Doc>, j: C.Joined, +after: List<&2, Ops.Item>, +h: {Main.all_mint(ds, C.named(j)) == True{} : Bool}) -> {said.mint(ds, C.said(j, after)) == True{} : Bool}:
  match j:
    case C.Joined{ns, +dg, g, +t}:
      checked_mint(ds, Sim.walked.moves(Sim.walked.go(Sim.ops(Merge.file(t), after), Sim.Walked{Merge.file(t), after, Nil{}})), C.named.of(Merge.visible(t), dg), after, Sim.fit(Sim.walked.moves(Sim.walked.go(Sim.ops(Merge.file(t), after), Sim.Walked{Merge.file(t), after, Nil{}})), Merge.file(t), after), h)

# The resolution
# --------------

# A file whose lines but the last all end is one a resolution may state.
def unterminated_none(xs: List<&2, Ops.Item>, +i: Nat, +h: {Ops.terminated_but_last(xs) == True{} : Bool}) -> {Main.unterminated_at(xs, i) == None{} : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Ops.Item{t, True{}, f} <> Nil{}:
      {==}
    case Ops.Item{t, False{}, f} <> Nil{}:
      {==}
    case Ops.Item{+t, True{}, +f} <> +y <> +rest:
      unterminated_none(y <> rest, 1n+i, h)
    case Ops.Item{+t, False{}, +f} <> +y <> +rest:
      Empty.absurd({Main.unterminated_at(Ops.Item{t, False{}, f} <> y <> rest, i) == None{} : Maybe<&2, Nat>}, Comp.false_true(h))

# Pieces that assemble to a well-shaped file make a document that
# assembles to it: the digest it states is the one `cat` checks.
def resolution_assembles(+ds: List<&2, Store.Doc>, +after: List<&2, Ops.Item>, ps: List<&2, Res.Piece>, +pa: {Main.assemble.pieces(ds, ps) == Done{after} : Result<&2, &2, String, List<&2, Ops.Item>>}, +sh: {Main.unterminated_at(after, 0n) == None{} : Maybe<&2, Nat>}, -doc: Res.Doc, e: {C.resolution.of(after, ps) == Some{doc} : Maybe<&2, Res.Doc>}) -> {Main.assemble(ds, doc) == Done{after} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match ps:
    case Nil{}:
      Empty.absurd({Main.assemble(ds, doc) == Done{after} : Result<&2, &2, String, List<&2, Ops.Item>>}, none_some(doc, e))
    case +p <> +rest:
      %some_eq(Res.Doc{None{}, Some{Ops.state_digest(after)}, p <> rest}, doc, e) : {Main.assemble(ds, _) == Done{after} : Result<&2, &2, String, List<&2, Ops.Item>>}
      %Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Main.assemble.pieces(ds, p <> rest), Done{after}, pa) : {Main.assemble.of(Some{Ops.state_digest(after)}, _) == Done{after} : Result<&2, &2, String, List<&2, Ops.Item>>}
      %Equal.sym(Maybe<&2, Nat>, Main.unterminated_at(after, 0n), None{}, sh) : {Main.assemble.shaped(Some{Ops.state_digest(after)}, after, Main.assembled.shape(_)) == Done{after} : Result<&2, &2, String, List<&2, Ops.Item>>}
      %Equal.sym(Bool, String.eq(Ops.state_digest(after), Ops.state_digest(after)), True{}, SL.eq_refl(Ops.state_digest(after))) : {Main.assemble.checked(after, Main.assembled.verdict(Bool.or(Ops.any_forgotten(after), _), Ops.state_digest(after), Ops.state_digest(after))) == Done{after} : Result<&2, &2, String, List<&2, Ops.Item>>}
      %Equal.sym(Bool, Bool.or(Ops.any_forgotten(after), True{}), True{}, HL.or_true_r(Ops.any_forgotten(after))) : {Main.assemble.checked(after, Main.assembled.verdict(_, Ops.state_digest(after), Ops.state_digest(after))) == Done{after} : Result<&2, &2, String, List<&2, Ops.Item>>}
      {==}

# What a merge states for a file, spelled as pieces and assembled, is the
# file.
def pieces_after(+ds: List<&2, Store.Doc>, +j: C.Joined, +after: List<&2, Ops.Item>, +hm: {Main.all_mint(ds, C.named(j)) == True{} : Bool}) -> {Main.assemble.pieces(ds, C.pieces(C.said(j, after))) == Done{after} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  %said_items(j, after) : {Main.assemble.pieces(ds, C.pieces(C.said(j, after))) == Done{_} : Result<&2, &2, String, List<&2, Ops.Item>>}
  pieces_assemble(ds, C.said(j, after), said_minted(ds, j, after, hm))

# The resolution `record --merge` writes for a file of lines, assembled as
# `cat` assembles one, is the file the folder holds — wherever the store's
# documents mint every element the walk stands under, as the walk that
# named them read them.
def resolved(+ds: List<&2, Store.Doc>, +j: C.Joined, +s: String, +hm: {Main.all_mint(ds, C.named(j)) == True{} : Bool}, -doc: Res.Doc, e: {C.resolve(j, Ops.from_text(s)) == Some{doc} : Maybe<&2, Res.Doc>}) -> {Main.assemble(ds, doc) == Done{Ops.from_text(s)} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  resolution_assembles(ds, Ops.from_text(s), C.pieces(C.said(j, Ops.from_text(s))), pieces_after(ds, j, Ops.from_text(s), hm), unterminated_none(Ops.from_text(s), 0n, BlameL.tbl_text(s)), doc, e)
