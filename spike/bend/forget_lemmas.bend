# What `forget` writes and what it destroys. A forgetting document states
# what it stands in for with only text destroyed, so a reader folds it in
# rather than setting it aside; and `forget` destroys a file only where its
# bytes are one of the digests it forgets.
import Base
import ./ops.bend as Ops
import ./text.bend as T
import ./revision.bend as Rev
import ./resolution.bend as Res
import ./commands.bend as Main
import ./standin.bend as Stand
import ./forget.bend as Fg
import ./string_lemmas.bend as S
import ./graph_lemmas.bend as GL
import ./status_lemmas.bend as StatusL
import ./composition_lemmas.bend as Comp
import ./anchor_lemmas.bend as AL
import ./blamed_lemmas.bend as B
import ./equality_lemmas.bend as Eq
import ./diff_lemmas.bend as Diff
import ./refusal_lemmas.bend as Refuse
import ./store.bend as Store
import ./merge.bend as Merge
import ./spelling_lemmas.bend as Sp

# Which items `forget` destroys
# -------------------------------

# Item `j` of operation `k` of a document, as an operation of that one
# item: its verb, its position and the item.
def item.in(kind: Ops.Verb, +at: Nat, m: Maybe<&2, Ops.Item>) -> Maybe<&2, Ops.Op>:
  match m:
    case None{}:
      None{}
    case Some{it}:
      Some{Ops.Op{kind, at, [it]}}

def item.of(ops: List<&2, Ops.Op>, k: Nat, +j: Nat) -> Maybe<&2, Ops.Op>:
  match ops k:
    case Nil{} _:
      None{}
    case Ops.Op{kind, +at, items} <> rest 0n:
      item.in(kind, at, List.get(&2, Ops.Item, items, j))
    case o <> rest 1n+q:
      item.of(rest, q, j)

# What that item is to be: with its text gone and marked forgotten where
# `hit`, its terminator kept; as it was otherwise.
def forgot.at(m: Maybe<&2, Ops.Op>, hit: Bool) -> Maybe<&2, Ops.Op>:
  match m:
    case Some{Ops.Op{kind, +at, [Ops.Item{x, +n, f}]}}:
      Some{Ops.Op{kind, at, [Bool.pick(Ops.Item, hit, Ops.Item{SNil{}, n, True{}}, Ops.Item{x, n, f})]}}
    case _:
      None{}

def item_pick(hit: Bool, kind: Ops.Verb, +at: Nat, x: String, +n: Bool, f: Bool) -> {Some{Ops.Op{kind, at, [Fg.forget.item(hit, Ops.Item{x, n, f})]}} == forgot.at(Some{Ops.Op{kind, at, [Ops.Item{x, n, f}]}}, hit) : Maybe<&2, Ops.Op>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def items_at(kind: Ops.Verb, +at: Nat, items: List<&2, Ops.Item>, +ps: List<&2, Fg.FgPick>, +t: String, +i: Nat, +j0: Nat, j: Nat) -> {item.in(kind, at, List.get(&2, Ops.Item, Fg.forget.items(items, ps, t, i, j0), j)) == forgot.at(item.in(kind, at, List.get(&2, Ops.Item, items, j)), Fg.picked.has(ps, t, i, Nat.add(j0, j))) : Maybe<&2, Ops.Op>}:
  match items j:
    case Nil{} _:
      {==}
    case Ops.Item{x, +n, f} <> rest 0n:
      %Equal.sym(Nat, Nat.add(j0, 0n), j0, Comp.add_zero(j0)) : {Some{Ops.Op{kind, at, [Fg.forget.item(Fg.picked.has(ps, t, i, j0), Ops.Item{x, n, f})]}} == forgot.at(Some{Ops.Op{kind, at, [Ops.Item{x, n, f}]}}, Fg.picked.has(ps, t, i, _)) : Maybe<&2, Ops.Op>}
      item_pick(Fg.picked.has(ps, t, i, j0), kind, at, x, n, f)
    case it <> +rest 1n+q:
      %Equal.sym(Nat, Nat.add(j0, 1n+q), 1n+Nat.add(j0, q), Diff.add_succ(j0, q)) : {item.in(kind, at, List.get(&2, Ops.Item, Fg.forget.items(rest, ps, t, i, 1n+j0), q)) == forgot.at(item.in(kind, at, List.get(&2, Ops.Item, rest, q)), Fg.picked.has(ps, t, i, _)) : Maybe<&2, Ops.Op>}
      items_at(kind, at, rest, ps, t, i, 1n+j0, q)

# Every item of a forgetting document is the original's, with its text
# gone and marked forgotten exactly where it is picked.
def ops_at(ops: List<&2, Ops.Op>, +ps: List<&2, Fg.FgPick>, +t: String, +i: Nat, k: Nat, +j: Nat) -> {item.of(Fg.forget.ops(ops, ps, t, i), k, j) == forgot.at(item.of(ops, k, j), Fg.picked.has(ps, t, Nat.add(i, k), j)) : Maybe<&2, Ops.Op>}:
  match ops k:
    case Nil{} _:
      {==}
    case Ops.Op{kind, +at, +items} <> rest 0n:
      %Equal.sym(Nat, Nat.add(i, 0n), i, Comp.add_zero(i)) : {item.in(kind, at, List.get(&2, Ops.Item, Fg.forget.items(items, ps, t, i, 0n), j)) == forgot.at(item.in(kind, at, List.get(&2, Ops.Item, items, j)), Fg.picked.has(ps, t, _, j)) : Maybe<&2, Ops.Op>}
      items_at(kind, at, items, ps, t, i, 0n, j)
    case Ops.Op{kind, at, items} <> +rest 1n+q:
      %Equal.sym(Nat, Nat.add(i, 1n+q), 1n+Nat.add(i, q), Diff.add_succ(i, q)) : {item.of(Fg.forget.ops(rest, ps, t, 1n+i), q, j) == forgot.at(item.of(rest, q, j), Fg.picked.has(ps, t, _, j)) : Maybe<&2, Ops.Op>}
      ops_at(rest, ps, t, 1n+i, q, j)

# So at every place the original has an item, the forgetting document has
# it forgotten where it is picked and as it was where it is not.
def ops_forgot_at(ops: List<&2, Ops.Op>, +ps: List<&2, Fg.FgPick>, +t: String, +i: Nat, +k: Nat, +j: Nat, kind: Ops.Verb, +at: Nat, x: String, +n: Bool, f: Bool, h: {item.of(ops, k, j) == Some{Ops.Op{kind, at, [Ops.Item{x, n, f}]}} : Maybe<&2, Ops.Op>}) -> {item.of(Fg.forget.ops(ops, ps, t, i), k, j) == Some{Ops.Op{kind, at, [Bool.pick(Ops.Item, Fg.picked.has(ps, t, Nat.add(i, k), j), Ops.Item{SNil{}, n, True{}}, Ops.Item{x, n, f})]}} : Maybe<&2, Ops.Op>}:
  +b = Fg.picked.has(ps, t, Nat.add(i, k), j)
  %Equal.sym(Maybe<&2, Ops.Op>, item.of(Fg.forget.ops(ops, ps, t, i), k, j), forgot.at(item.of(ops, k, j), b), ops_at(ops, ps, t, i, k, j)) : {_ == Some{Ops.Op{kind, at, [Bool.pick(Ops.Item, b, Ops.Item{SNil{}, n, True{}}, Ops.Item{x, n, f})]}} : Maybe<&2, Ops.Op>}
  %Equal.sym(Maybe<&2, Ops.Op>, item.of(ops, k, j), Some{Ops.Op{kind, at, [Ops.Item{x, n, f}]}}, h) : {forgot.at(_, b) == Some{Ops.Op{kind, at, [Bool.pick(Ops.Item, b, Ops.Item{SNil{}, n, True{}}, Ops.Item{x, n, f})]}} : Maybe<&2, Ops.Op>}
  {==}

# Shape
# -----

def verb_refl(k: Ops.Verb) -> {Ops.verb_is(k, k) == True{} : Bool}:
  match k:
    case Ops.Delete{}:
      {==}
    case Ops.Insert{}:
      {==}

def term_refl(n: Bool) -> {Bool.not(Bool.xor(n, n)) == True{} : Bool}:
  match n:
    case True{}:
      {==}
    case False{}:
      {==}

# An item forgotten or not keeps its terminator.
def item_shape(hit: Bool, it: Ops.Item, -rest: List<&2, Ops.Item>, -fr: List<&2, Ops.Item>, ih: {Stand.items.shape(rest, fr) == True{} : Bool}) -> {Stand.items.shape(it <> rest, Fg.forget.item(hit, it) <> fr) == True{} : Bool}:
  match hit it:
    case True{} Ops.Item{t, n, f}:
      %Equal.sym(Bool, Bool.not(Bool.xor(n, n)), True{}, term_refl(n)) : {Bool.and(_, Stand.items.shape(rest, fr)) == True{} : Bool}
      ih
    case False{} Ops.Item{t, n, f}:
      %Equal.sym(Bool, Bool.not(Bool.xor(n, n)), True{}, term_refl(n)) : {Bool.and(_, Stand.items.shape(rest, fr)) == True{} : Bool}
      ih

def items_shape(items: List<&2, Ops.Item>, +ps: List<&2, Fg.FgPick>, +t: String, +i: Nat, +j: Nat) -> {Stand.items.shape(items, Fg.forget.items(items, ps, t, i, j)) == True{} : Bool}:
  match items:
    case Nil{}:
      {==}
    case it <> +rest:
      item_shape(Fg.picked.has(ps, t, i, j), it, rest, Fg.forget.items(rest, ps, t, i, 1n+j), items_shape(rest, ps, t, i, 1n+j))

def ops_shape(ops: List<&2, Ops.Op>, +ps: List<&2, Fg.FgPick>, +t: String, +i: Nat) -> {Stand.ops.shape(ops, Fg.forget.ops(ops, ps, t, i)) == True{} : Bool}:
  match ops:
    case Nil{}:
      {==}
    case Ops.Op{k, +at, +items} <> +rest:
      %Equal.sym(Bool, Ops.verb_is(k, k), True{}, verb_refl(k)) : {Bool.and(_, Bool.and(Nat.is_eq(at, at), Bool.and(Stand.items.shape(items, Fg.forget.items(items, ps, t, i, 0n)), Stand.ops.shape(rest, Fg.forget.ops(rest, ps, t, 1n+i))))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(at, at), True{}, Comp.eq_refl(at)) : {Bool.and(True{}, Bool.and(_, Bool.and(Stand.items.shape(items, Fg.forget.items(items, ps, t, i, 0n)), Stand.ops.shape(rest, Fg.forget.ops(rest, ps, t, 1n+i))))) == True{} : Bool}
      %Equal.sym(Bool, Stand.items.shape(items, Fg.forget.items(items, ps, t, i, 0n)), True{}, items_shape(items, ps, t, i, 0n)) : {Bool.and(True{}, Bool.and(True{}, Bool.and(_, Stand.ops.shape(rest, Fg.forget.ops(rest, ps, t, 1n+i))))) == True{} : Bool}
      ops_shape(rest, ps, t, 1n+i)

def pieces_shape(pieces: List<&2, Res.Piece>, +ps: List<&2, Fg.FgPick>, +t: String, +i: Nat) -> {Stand.pieces.shape(pieces, Fg.forget.pieces(pieces, ps, t, i)) == True{} : Bool}:
  match pieces:
    case Nil{}:
      {==}
    case Res.Piece.Insert{+items} <> +rest:
      %Equal.sym(Bool, Stand.items.shape(items, Fg.forget.items(items, ps, t, i, 0n)), True{}, items_shape(items, ps, t, i, 0n)) : {Bool.and(_, Stand.pieces.shape(rest, Fg.forget.pieces(rest, ps, t, 1n+i))) == True{} : Bool}
      pieces_shape(rest, ps, t, 1n+i)
    case Res.Piece.Keep{+d, +f, +c} <> +rest:
      %Equal.sym(Bool, String.eq(d, d), True{}, S.eq_refl(d)) : {Bool.and(Bool.and(_, Bool.and(Nat.is_eq(f, f), Nat.is_eq(c, c))), Stand.pieces.shape(rest, Fg.forget.pieces(rest, ps, t, 1n+i))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(f, f), True{}, Comp.eq_refl(f)) : {Bool.and(Bool.and(True{}, Bool.and(_, Nat.is_eq(c, c))), Stand.pieces.shape(rest, Fg.forget.pieces(rest, ps, t, 1n+i))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(c, c), True{}, Comp.eq_refl(c)) : {Bool.and(Bool.and(True{}, Bool.and(True{}, _)), Stand.pieces.shape(rest, Fg.forget.pieces(rest, ps, t, 1n+i))) == True{} : Bool}
      pieces_shape(rest, ps, t, 1n+i)

# What is destroyed
# -----------------

def held_cons(+ids: List<&2, String>, +y: String, xs: List<&2, String>, +h: {Main.all_held(ids, xs) == True{} : Bool}) -> {Main.all_held(y <> ids, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      AL.and_intro(Rev.member(y <> ids, x), Main.all_held(y <> ids, rest),
        GL.member_tail(y, ids, x, Comp.and_left(Rev.member(ids, x), Main.all_held(ids, rest), h)),
        held_cons(ids, y, rest, Comp.and_right(Rev.member(ids, x), Main.all_held(ids, rest), h)))

def held_member(+ids: List<&2, String>, xs: List<&2, String>, +p: String, +h: {Main.all_held(ids, xs) == True{} : Bool}, m: {Rev.member(xs, p) == True{} : Bool}) -> {Rev.member(ids, p) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Rev.member(ids, p) == True{} : Bool}, S.false_true(m))
    case +x <> +rest:
      GL.member_cons({Rev.member(ids, p) == True{} : Bool}, x, rest, p, m,
        e => GL.member_at(ids, x, p, e, Comp.and_left(Rev.member(ids, x), Main.all_held(ids, rest), h)),
        t => held_member(ids, rest, p, Comp.and_right(Rev.member(ids, x), Main.all_held(ids, rest), h), t))

def of_step(held: Bool, kind: Bool, +p: String, +h: List<&2, String>, +x: List<&2, String>, ih: {Main.all_held(h, x) == True{} : Bool}) -> {Main.all_held(Rev.keep(held, p, h), Rev.keep(Bool.and(held, kind), p, x)) == True{} : Bool}:
  match held kind:
    case True{} True{}:
      AL.and_intro(Rev.member(p <> h, p), Main.all_held(p <> h, x), GL.member_head(p, h), held_cons(h, p, x, ih))
    case True{} False{}:
      held_cons(h, p, x, ih)
    case False{} _:
      ih

def of_held(fs: List<&2, Fg.FgFiled>, +ts: List<&2, String>, +b: Bool) -> {Main.all_held(Fg.holding(fs, ts), Fg.destroyed.of(fs, ts, b)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Fg.Fg.Filed{+p, +d, n} <> +rest:
      of_step(Rev.member(ts, d), Bool.not(Bool.xor(Fg.filed.document(p), b)), p, Fg.holding(rest, ts), Fg.destroyed.of(rest, ts, b), of_held(rest, ts, b))

# Whatever `forget` destroys is a file whose bytes are a digest it forgets.
def destroys(+fs: List<&2, Fg.FgFiled>, +ts: List<&2, String>, +p: String, e: {Rev.member(Fg.destroyed(fs, ts), p) == True{} : Bool}) -> {Rev.member(Fg.holding(fs, ts), p) == True{} : Bool}:
  held_member(Fg.holding(fs, ts), Fg.destroyed(fs, ts), p,
    StatusL.ah_app(Fg.holding(fs, ts), List.sort(~String, ~(a => b => Fg.path.le(a, b)), Fg.destroyed.of(fs, ts, True{})), List.sort(~String, ~(a => b => Fg.path.le(a, b)), Fg.destroyed.of(fs, ts, False{})),
      StatusL.ah_sort(~(a => b => Fg.path.le(a, b)), Fg.holding(fs, ts), Fg.destroyed.of(fs, ts, True{}), of_held(fs, ts, True{})),
      StatusL.ah_sort(~(a => b => Fg.path.le(a, b)), Fg.holding(fs, ts), Fg.destroyed.of(fs, ts, False{}), of_held(fs, ts, False{}))),
    e)

# What is rewritten
# -----------------

# Whether a document found, if any, is one of these.
def found.in(+docs: List<&2, String>, m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{d}:
      Rev.member(docs, d)

def found_tail(+y: String, +docs: List<&2, String>, m: Maybe<&2, String>, h: {found.in(docs, m) == True{} : Bool}) -> {found.in(y <> docs, m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+d}:
      GL.member_tail(y, docs, d, h)

def find_step(c: Bool, +x: String, +rest: List<&2, Fg.FgNamed>, +by: String, ih: {found.in(Fg.named.docs(rest), Fg.named.find(rest, by)) == True{} : Bool}) -> {found.in(x <> Fg.named.docs(rest), Bool.pick(Maybe<&2, String>, c, Some{x}, Fg.named.find(rest, by))) == True{} : Bool}:
  match c:
    case True{}:
      GL.member_head(x, Fg.named.docs(rest))
    case False{}:
      found_tail(x, Fg.named.docs(rest), Fg.named.find(rest, by), ih)

# What `named.find` finds is a document the revisions name for the file.
def find_named(ns: List<&2, Fg.FgNamed>, +by: String) -> {found.in(Fg.named.docs(ns), Fg.named.find(ns, by)) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Fg.Fg.Named{+b, +x} <> +rest:
      find_step(String.eq(b, by), x, rest, by, find_named(rest, by))

def pick_if(found: Maybe<&2, String>, +op: Nat, +item: Nat, +rest: List<&2, Fg.FgPick>, +docs: List<&2, String>, hf: {found.in(docs, found) == True{} : Bool}, hr: {Main.all_held(docs, Fg.targets.of(rest)) == True{} : Bool}) -> {Main.all_held(docs, Fg.targets.of(Fg.pick.if(found, op, item, rest))) == True{} : Bool}:
  match found:
    case None{}:
      hr
    case Some{+d}:
      AL.and_intro(Rev.member(docs, d), Main.all_held(docs, Fg.targets.of(rest)), hf, hr)

def picks_deletes(qs: List<&2, Fg.FgQuote>, +ns: List<&2, Fg.FgNamed>) -> {Main.all_held(Fg.named.docs(ns), Fg.targets.of(Fg.picks.deletes(qs, ns))) == True{} : Bool}:
  match qs:
    case Nil{}:
      {==}
    case Fg.Fg.Quote{+by, +op, +item} <> +rest:
      pick_if(Fg.named.find(ns, by), op, item, Fg.picks.deletes(rest, ns), Fg.named.docs(ns), find_named(ns, by), picks_deletes(rest, ns))

def picks_of(+ns: List<&2, Fg.FgNamed>, taken: Bool, q: Fg.FgQuoted) -> {Main.all_held(Fg.named.docs(ns), Fg.targets.of(Fg.picks.of(ns, taken, q))) == True{} : Bool}:
  match taken q:
    case True{} Fg.Fg.Quoted{+by, +op, +item, t, +dl, dr, f, v}:
      pick_if(Fg.named.find(ns, by), op, item, Fg.picks.deletes(dl, ns), Fg.named.docs(ns), find_named(ns, by), picks_deletes(dl, ns))
    case False{} q2:
      {==}

def targets_app(xs: List<&2, Fg.FgPick>, +ys: List<&2, Fg.FgPick>) -> {Fg.targets.of(List.append(&2, Fg.FgPick, xs, ys)) == List.append(&2, String, Fg.targets.of(xs), Fg.targets.of(ys)) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case Fg.Fg.Pick{d, op, item} <> +rest:
      %Equal.sym(List<&2, String>, Fg.targets.of(List.append(&2, Fg.FgPick, rest, ys)), List.append(&2, String, Fg.targets.of(rest), Fg.targets.of(ys)), targets_app(rest, ys)) : {d <> _ == d <> List.append(&2, String, Fg.targets.of(rest), Fg.targets.of(ys)) : List<&2, String>}
      {==}

def picks.of.picked(p: Fg.FgPicked) -> List<&2, Fg.FgPick>:
  match p:
    case Fg.Fg.Picked{ps, n}:
      ps

def join_picks(+taken: Bool, +forgot: Bool, +here: List<&2, Fg.FgPick>, r: Fg.FgPicked, +docs: List<&2, String>, hh: {Main.all_held(docs, Fg.targets.of(here)) == True{} : Bool}, hr: {Main.all_held(docs, Fg.targets.of(picks.of.picked(r))) == True{} : Bool}) -> {Main.all_held(docs, Fg.targets.of(picks.of.picked(Fg.picked.join(taken, forgot, here, r)))) == True{} : Bool}:
  match r:
    case Fg.Fg.Picked{+ps, n}:
      %Equal.sym(List<&2, String>, Fg.targets.of(List.append(&2, Fg.FgPick, here, ps)), List.append(&2, String, Fg.targets.of(here), Fg.targets.of(ps)), targets_app(here, ps)) : {Main.all_held(docs, _) == True{} : Bool}
      StatusL.ah_app(docs, Fg.targets.of(here), Fg.targets.of(ps), hh, hr)

# Every item `picked` takes is in a document the revisions name for the
# file: where it was written, or where a delete quotes it.
def picked_named(qs: List<&2, Fg.FgQuoted>, +span: List<&2, String>, +ns: List<&2, Fg.FgNamed>) -> {Main.all_held(Fg.named.docs(ns), Fg.targets.of(picks.of.picked(Fg.picked(qs, span, ns)))) == True{} : Bool}:
  match qs:
    case Nil{}:
      {==}
    case +q <> +rest:
      join_picks(Rev.member(span, Fg.quoted.key(q)), Fg.quoted.forgot(q), Fg.picks.of(ns, Rev.member(span, Fg.quoted.key(q)), q), Fg.picked(rest, span, ns), Fg.named.docs(ns),
        picks_of(ns, Rev.member(span, Fg.quoted.key(q)), q), picked_named(rest, span, ns))

def plan.targets(p: Fg.FgPlan) -> List<&2, String>:
  match p:
    case Fg.Fg.Plan{ts, ws, a, n}:
      ts

def plan_eq(-a: Fg.FgPlan, -b: Fg.FgPlan, h: {Done{a} == Done{b} : Result<&2, &2, Main.Refused, Fg.FgPlan>}) -> {plan.targets(a) == plan.targets(b) : List<&2, String>}:
  Equal.cong(Fg.FgPlan, List<&2, String>, p => plan.targets(p), a, b, B.done_eq(Fg.FgPlan, a, b, h))

def picked_ws(+ts: List<&2, String>, +already: Nat, r: Result<&2, &2, Main.Refused, List<&2, Fg.FgWrite>>, +p: Fg.FgPlan, e: {Result.map(&2, &2, Main.Refused, List<&2, Fg.FgWrite>, Fg.FgPlan, ws => Fg.Fg.Plan{ts, ws, already, 0n}, r) == Done{p} : Result<&2, &2, Main.Refused, Fg.FgPlan>}) -> {ts == plan.targets(p) : List<&2, String>}:
  match r:
    case Fail{x}:
      Empty.absurd({ts == plan.targets(p) : List<&2, String>}, B.fail_done(Fg.FgPlan, x, p, e))
    case Done{ws}:
      plan_eq(Fg.Fg.Plan{ts, ws, already, 0n}, p, e)

# A plan's targets are the documents its picks name, sorted, each once.
def lines_of(+ds: List<&2, Store.Doc>, q: Fg.FgPicked, +p: Fg.FgPlan, e: {Fg.lines.of(ds, q) == Done{p} : Result<&2, &2, Main.Refused, Fg.FgPlan>}) -> {Fg.targets(picks.of.picked(q)) == plan.targets(p) : List<&2, String>}:
  match q:
    case Fg.Fg.Picked{+ps, +already}:
      picked_ws(Fg.targets(ps), already, Fg.standins(Fg.targets(ps), ps, ds), p, e)

def targets_named(+docs: List<&2, String>, +ps: List<&2, Fg.FgPick>, h: {Main.all_held(docs, Fg.targets.of(ps)) == True{} : Bool}) -> {Main.all_held(docs, Fg.targets(ps)) == True{} : Bool}:
  StatusL.ah_distinct(docs, List.sort(~String, ~(a => b => String.is_le(a, b)), Fg.targets.of(ps)),
    StatusL.ah_sort(~(a => b => String.is_le(a, b)), docs, Fg.targets.of(ps), h))

def every_ok(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +file: String, +span: List<&2, String>, r: Result<&2, &2, Main.Refused, List<&2, Fg.FgQuoted>>, +p: Fg.FgPlan, e: {Fg.lines.every(fs, ds, file, span, r) == Done{p} : Result<&2, &2, Main.Refused, Fg.FgPlan>}) -> {Main.all_held(Fg.named.docs(Fg.named(fs, file)), plan.targets(p)) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.all_held(Fg.named.docs(Fg.named(fs, file)), plan.targets(p)) == True{} : Bool}, B.fail_done(Fg.FgPlan, x, p, e))
    case Done{+every}:
      +q = Fg.picked(every, Fg.copies(every, span), Fg.named(fs, file))
      +eq = lines_of(ds, q, p, e)
      %eq : {Main.all_held(Fg.named.docs(Fg.named(fs, file)), _) == True{} : Bool}
      targets_named(Fg.named.docs(Fg.named(fs, file)), picks.of.picked(q), picked_named(every, Fg.copies(every, span), Fg.named(fs, file)))

def within_ok(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String, +first: String, +last: String, +visible: List<&2, Fg.FgQuoted>, ok: Result<&2, &2, Main.Refused, Unit>, +p: Fg.FgPlan, e: {Fg.lines.within(fs, ds, id, file, first, last, visible, ok) == Done{p} : Result<&2, &2, Main.Refused, Fg.FgPlan>}) -> {Main.all_held(Fg.named.docs(Fg.named(fs, file)), plan.targets(p)) == True{} : Bool}:
  match ok:
    case Fail{x}:
      Empty.absurd({Main.all_held(Fg.named.docs(Fg.named(fs, file)), plan.targets(p)) == True{} : Bool}, B.fail_done(Fg.FgPlan, x, p, e))
    case Done{u}:
      every_ok(fs, ds, file, Fg.span.keys(visible, first, last), Fg.refused.of(List<&2, Fg.FgQuoted>, Fg.quotes(Fg.by_digest(fs), ds, id, file)), p, e)

def at_ok(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String, +first: String, +last: String, r: Result<&2, &2, Main.Refused, List<&2, Fg.FgQuoted>>, +p: Fg.FgPlan, e: {Fg.lines.at(fs, ds, id, file, first, last, r) == Done{p} : Result<&2, &2, Main.Refused, Fg.FgPlan>}) -> {Main.all_held(Fg.named.docs(Fg.named(fs, file)), plan.targets(p)) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.all_held(Fg.named.docs(Fg.named(fs, file)), plan.targets(p)) == True{} : Bool}, B.fail_done(Fg.FgPlan, x, p, e))
    case Done{at}:
      +visible = Fg.quoted.visible(at)
      within_ok(fs, ds, id, file, first, last, visible, Fg.span.within.r(last, List.length(&2, Fg.FgQuoted, visible)), p, e)

def checked_ok(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String, +first: String, +last: String, ok: Result<&2, &2, Main.Refused, Unit>, +p: Fg.FgPlan, e: {Fg.lines.checked(fs, ds, id, file, first, last, ok) == Done{p} : Result<&2, &2, Main.Refused, Fg.FgPlan>}) -> {Main.all_held(Fg.named.docs(Fg.named(fs, file)), plan.targets(p)) == True{} : Bool}:
  match ok:
    case Fail{x}:
      Empty.absurd({Main.all_held(Fg.named.docs(Fg.named(fs, file)), plan.targets(p)) == True{} : Bool}, B.fail_done(Fg.FgPlan, x, p, e))
    case Done{u}:
      at_ok(fs, ds, id, file, first, last, Fg.refused.of(List<&2, Fg.FgQuoted>, Fg.quotes(Main.walked.ancestry(fs, id), ds, id, file)), p, e)

# Every document `forget --lines` plans a stand-in for is one a revision
# states for the file.
def rewrites(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String, +first: String, +last: String, +ts: List<&2, String>, +ws: List<&2, Fg.FgWrite>, +a: Nat, +n: Nat, e: {Fg.lines.plan.r(fs, ds, id, file, first, last) == Done{Fg.Fg.Plan{ts, ws, a, n}} : Result<&2, &2, Main.Refused, Fg.FgPlan>}) -> {Main.all_held(Fg.named.docs(Fg.named(fs, file)), ts) == True{} : Bool}:
  checked_ok(fs, ds, id, file, first, last, Fg.span.checked.r(first, last), Fg.Fg.Plan{ts, ws, a, n}, e)

# What a revision states for a file, read off its headers with no reader
# of `forget`'s: a header `edit`, `text` or `bytes` whose value is the
# file's path, a space, and the digest.
def stated.in(hs: List<&2, Rev.Header>, +file: String, +d: String) -> Bool:
  match hs:
    case Nil{}:
      False{}
    case Rev.Header{+k, +v} <> rest:
      Bool.or(Bool.and(Bool.or(String.eq(k, "edit"), Bool.or(String.eq(k, "text"), String.eq(k, "bytes"))), String.eq(v, file ++ " " ++ d)), stated.in(rest, file, d))

def stated(fs: List<&2, Main.Full>, +file: String, +d: String) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case +f <> rest:
      Bool.or(stated.in(Main.facts_of(f), file, d), stated(rest, file, d))

def all_stated(+fs: List<&2, Main.Full>, +file: String, ts: List<&2, String>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case +t <> rest:
      Bool.and(stated(fs, file, t), all_stated(fs, file, rest))

def said.doc(s: Main.Said) -> Maybe<&2, String>:
  match s:
    case Main.Whole{d}:
      Some{d}
    case Main.Edited{d}:
      Some{d}
    case Main.Nothing{}:
      None{}

def sdisc(m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some(-d: String, h: {None{} == Some{d} : Maybe<&2, String>}) -> Empty:
  %h : {sdisc(_) : Type}
  Unit{}

def some_eq(-a: String, -b: String, h: {Some{a} == Some{b} : Maybe<&2, String>}) -> {a == b : String}:
  Equal.cong(Maybe<&2, String>, String, m => Maybe.default(&2, String, m, a), Some{a}, Some{b}, h)

# A header of the kinds that name a document, its value the file, a space
# and `d'`, states `d'` for the file.
def head_stated(+k: String, +v: String, +file: String, +f2: String, +d2: String, +d: String, +rest: List<&2, Rev.Header>, kind: {Bool.or(String.eq(k, "edit"), Bool.or(String.eq(k, "text"), String.eq(k, "bytes"))) == True{} : Bool}, ev: {T.split_once(v) == Some{T.Split{f2, d2}} : Maybe<&2, T.Split>}, ef: {String.eq(f2, file) == True{} : Bool}, ed: {d2 == d : String}) -> {stated.in(Rev.Header{k, v} <> rest, file, d) == True{} : Bool}:
  %Equal.sym(String, v, f2 ++ (" " ++ d2), Sp.split_top(v, f2, d2, ev)) : {Bool.or(Bool.and(Bool.or(String.eq(k, "edit"), Bool.or(String.eq(k, "text"), String.eq(k, "bytes"))), String.eq(_, file ++ " " ++ d)), stated.in(rest, file, d)) == True{} : Bool}
  %Equal.sym(String, f2, file, S.eq_true(f2, file, ef)) : {Bool.or(Bool.and(Bool.or(String.eq(k, "edit"), Bool.or(String.eq(k, "text"), String.eq(k, "bytes"))), String.eq(_ ++ (" " ++ d2), file ++ " " ++ d)), stated.in(rest, file, d)) == True{} : Bool}
  %Equal.sym(String, d2, d, ed) : {Bool.or(Bool.and(Bool.or(String.eq(k, "edit"), Bool.or(String.eq(k, "text"), String.eq(k, "bytes"))), String.eq(file ++ (" " ++ _), file ++ " " ++ d)), stated.in(rest, file, d)) == True{} : Bool}
  AL.or_left(Bool.and(Bool.or(String.eq(k, "edit"), Bool.or(String.eq(k, "text"), String.eq(k, "bytes"))), String.eq(file ++ " " ++ d, file ++ " " ++ d)), stated.in(rest, file, d),
    AL.and_intro(Bool.or(String.eq(k, "edit"), Bool.or(String.eq(k, "text"), String.eq(k, "bytes"))), String.eq(file ++ " " ++ d, file ++ " " ++ d), kind, S.eq_refl(file ++ " " ++ d)))

def kind_step(o: Bool, ed: Bool, wh: Bool, +k: String, +v: String, +file: String, +f2: String, +d2: String, +d: String, +rest: List<&2, Rev.Header>, eo: {String.eq(f2, file) == o : Bool}, eed: {String.eq(k, "edit") == ed : Bool}, ewh: {Bool.or(String.eq(k, "text"), String.eq(k, "bytes")) == wh : Bool}, ev: {T.split_once(v) == Some{T.Split{f2, d2}} : Maybe<&2, T.Split>}, h: {said.doc(Main.said.or(Main.said.kind(d2, o, ed, wh), Main.said(rest, file))) == Some{d} : Maybe<&2, String>}, ih: {said.doc(Main.said(rest, file)) == Some{d} : Maybe<&2, String>} -> {stated.in(rest, file, d) == True{} : Bool}) -> {stated.in(Rev.Header{k, v} <> rest, file, d) == True{} : Bool}:
  match o ed wh:
    case False{} ed2 wh2:
      AL.or_right(Bool.and(Bool.or(String.eq(k, "edit"), Bool.or(String.eq(k, "text"), String.eq(k, "bytes"))), String.eq(v, file ++ " " ++ d)), stated.in(rest, file, d), ih(h))
    case True{} True{} wh2:
      head_stated(k, v, file, f2, d2, d, rest, AL.or_left(String.eq(k, "edit"), Bool.or(String.eq(k, "text"), String.eq(k, "bytes")), eed), ev, eo, some_eq(d2, d, h))
    case True{} False{} True{}:
      head_stated(k, v, file, f2, d2, d, rest, AL.or_right(String.eq(k, "edit"), Bool.or(String.eq(k, "text"), String.eq(k, "bytes")), ewh), ev, eo, some_eq(d2, d, h))
    case True{} False{} False{}:
      AL.or_right(Bool.and(Bool.or(String.eq(k, "edit"), Bool.or(String.eq(k, "text"), String.eq(k, "bytes"))), String.eq(v, file ++ " " ++ d)), stated.in(rest, file, d), ih(h))

def cut_step(c: Maybe<&2, T.Split>, +k: String, +v: String, +file: String, +d: String, +rest: List<&2, Rev.Header>, ec: {T.split_once(v) == c : Maybe<&2, T.Split>}, h: {said.doc(Main.said.or(Main.said.cut(k, file, c), Main.said(rest, file))) == Some{d} : Maybe<&2, String>}, ih: {said.doc(Main.said(rest, file)) == Some{d} : Maybe<&2, String>} -> {stated.in(rest, file, d) == True{} : Bool}) -> {stated.in(Rev.Header{k, v} <> rest, file, d) == True{} : Bool}:
  match c:
    case None{}:
      AL.or_right(Bool.and(Bool.or(String.eq(k, "edit"), Bool.or(String.eq(k, "text"), String.eq(k, "bytes"))), String.eq(v, file ++ " " ++ d)), stated.in(rest, file, d), ih(h))
    case Some{T.Split{+f2, +d2}}:
      kind_step(String.eq(f2, file), String.eq(k, "edit"), Bool.or(String.eq(k, "text"), String.eq(k, "bytes")), k, v, file, f2, d2, d, rest, {==}, {==}, {==}, ec, h, ih)

# What `said` finds for a file is a document a header states for it.
def said_stated(hs: List<&2, Rev.Header>, +file: String, +d: String, h: {said.doc(Main.said(hs, file)) == Some{d} : Maybe<&2, String>}) -> {stated.in(hs, file, d) == True{} : Bool}:
  match hs:
    case Nil{}:
      Empty.absurd({stated.in(Nil{}, file, d) == True{} : Bool}, none_some(d, h))
    case Rev.Header{+k, +v} <> +rest:
      cut_step(T.split_once(v), k, v, file, d, rest, {==}, h, t => said_stated(rest, file, d, t))

def said_found(+facts: List<&2, Rev.Header>, +file: String, -s: Main.Said, +d2: String, +d: String, es: {Main.said(facts, file) == s : Main.Said}, ed: {said.doc(s) == Some{d2} : Maybe<&2, String>}, e: {d2 == d : String}) -> {stated.in(facts, file, d) == True{} : Bool}:
  said_stated(facts, file, d,
    Equal.trans(Maybe<&2, String>, said.doc(Main.said(facts, file)), Some{d2}, Some{d},
      Equal.trans(Maybe<&2, String>, said.doc(Main.said(facts, file)), said.doc(s), Some{d2}, Equal.cong(Main.Said, Maybe<&2, String>, x => said.doc(x), Main.said(facts, file), s, es), ed),
      Equal.cong(String, Maybe<&2, String>, x => Some{x}, d2, d, e)))

def named_of_step(+facts: List<&2, Rev.Header>, +id: String, s: Main.Said, tx: Bool, +ns: List<&2, Fg.FgNamed>, +file: String, +d: String, es: {Main.said(facts, file) == s : Main.Said}, h: {Rev.member(Fg.named.docs(Fg.named.of(id, s, tx, ns)), d) == True{} : Bool}) -> {Bool.or(stated.in(facts, file, d), Rev.member(Fg.named.docs(ns), d)) == True{} : Bool}:
  match s tx:
    case Main.Edited{+d2} x:
      GL.member_cons({Bool.or(stated.in(facts, file, d), Rev.member(Fg.named.docs(ns), d)) == True{} : Bool}, d2, Fg.named.docs(ns), d, h,
        e => AL.or_left(stated.in(facts, file, d), Rev.member(Fg.named.docs(ns), d), said_found(facts, file, Main.Edited{d2}, d2, d, es, {==}, e)),
        t => AL.or_right(stated.in(facts, file, d), Rev.member(Fg.named.docs(ns), d), t))
    case Main.Whole{+d2} True{}:
      GL.member_cons({Bool.or(stated.in(facts, file, d), Rev.member(Fg.named.docs(ns), d)) == True{} : Bool}, d2, Fg.named.docs(ns), d, h,
        e => AL.or_left(stated.in(facts, file, d), Rev.member(Fg.named.docs(ns), d), said_found(facts, file, Main.Whole{d2}, d2, d, es, {==}, e)),
        t => AL.or_right(stated.in(facts, file, d), Rev.member(Fg.named.docs(ns), d), t))
    case Main.Whole{d2} False{}:
      AL.or_right(stated.in(facts, file, d), Rev.member(Fg.named.docs(ns), d), h)
    case Main.Nothing{} x:
      AL.or_right(stated.in(facts, file, d), Rev.member(Fg.named.docs(ns), d), h)

# Every document the revisions name for a file is one a header of theirs
# states for it.
def named_stated(fs: List<&2, Main.Full>, +file: String, +d: String, h: {Rev.member(Fg.named.docs(Fg.named(fs, file)), d) == True{} : Bool}) -> {stated(fs, file, d) == True{} : Bool}:
  match fs:
    case Nil{}:
      Empty.absurd({stated(Nil{}, file, d) == True{} : Bool}, S.false_true(h))
    case +f <> +rest:
      AL.or_cases({stated(f <> rest, file, d) == True{} : Bool}, stated.in(Main.facts_of(f), file, d), Rev.member(Fg.named.docs(Fg.named(rest, file)), d),
        named_of_step(Main.facts_of(f), Main.id_of(f), Main.said(Main.facts_of(f), file), Main.is_text(Main.facts_of(f), file), Fg.named(rest, file), file, d, {==}, h),
        l => AL.or_left(stated.in(Main.facts_of(f), file, d), stated(rest, file, d), l),
        r => AL.or_right(stated.in(Main.facts_of(f), file, d), stated(rest, file, d), named_stated(rest, file, d, r)))

def held_stated(+fs: List<&2, Main.Full>, +file: String, ts: List<&2, String>, +h: {Main.all_held(Fg.named.docs(Fg.named(fs, file)), ts) == True{} : Bool}) -> {all_stated(fs, file, ts) == True{} : Bool}:
  match ts:
    case Nil{}:
      {==}
    case +t <> +rest:
      AL.and_intro(stated(fs, file, t), all_stated(fs, file, rest),
        named_stated(fs, file, t, Comp.and_left(Rev.member(Fg.named.docs(Fg.named(fs, file)), t), Main.all_held(Fg.named.docs(Fg.named(fs, file)), rest), h)),
        held_stated(fs, file, rest, Comp.and_right(Rev.member(Fg.named.docs(Fg.named(fs, file)), t), Main.all_held(Fg.named.docs(Fg.named(fs, file)), rest), h)))

# Every document `forget --lines` plans a stand-in for is one a header of
# some revision states for the file.
def rewrites_stated(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String, +first: String, +last: String, +ts: List<&2, String>, +ws: List<&2, Fg.FgWrite>, +a: Nat, +n: Nat, e: {Fg.lines.plan.r(fs, ds, id, file, first, last) == Done{Fg.Fg.Plan{ts, ws, a, n}} : Result<&2, &2, Main.Refused, Fg.FgPlan>}) -> {all_stated(fs, file, ts) == True{} : Bool}:
  held_stated(fs, file, ts, rewrites(fs, ds, id, file, first, last, ts, ws, a, n, e))

# What a payload's forgetting takes
# ---------------------------------

def whole_of(+target: String, held: Maybe<&2, String>, +stood: Maybe<&2, Stand.Stood>, +n: Nat, +p: Fg.FgPlan, e: {Fg.whole.of(target, held, stood, n) == Done{p} : Result<&2, &2, Main.Refused, Fg.FgPlan>}) -> {Main.all_held([target], plan.targets(p)) == True{} : Bool}:
  match held stood:
    case None{} None{}:
      Empty.absurd({Main.all_held([target], plan.targets(p)) == True{} : Bool}, B.fail_done(Fg.FgPlan, Main.Refused{1, "this store does not hold the content " ++ target ++ ", and has no record of destroying it; there is nothing here to forget"}, p, e))
    case None{} Some{s}:
      +eq = plan_eq(Fg.Fg.Plan{Nil{}, Nil{}, 1n, n}, p, e)
      %eq : {Main.all_held([target], _) == True{} : Bool}
      {==}
    case Some{+k} s:
      +eq = plan_eq(Fg.Fg.Plan{[target], Bool.pick(List<&2, Fg.FgWrite>, String.eq(Fg.stood.text(s), Stand.payload.write(Stand.Payload{target, k})), Nil{}, [Fg.Fg.Write{target, Stand.payload.write(Stand.Payload{target, k}), True{}}]), 0n, n}, p, e)
      %eq : {Main.all_held([target], _) == True{} : Bool}
      AL.and_intro(Rev.member([target], target), True{}, GL.member_head(target, Nil{}), {==})

# Forgetting a file of bytes takes the payload its tree holds, or nothing.
def takes_one(+file: String, payload: Maybe<&2, String>, +files: List<&2, Fg.FgFiled>, +stood: List<&2, Store.Doc>, +n: Nat, +p: Fg.FgPlan, e: {Fg.whole.plan.r(file, payload, files, stood, n) == Done{p} : Result<&2, &2, Main.Refused, Fg.FgPlan>}) -> {Main.all_held(Fg.payload.list(payload), plan.targets(p)) == True{} : Bool}:
  match payload:
    case None{}:
      Empty.absurd({Main.all_held(Nil{}, plan.targets(p)) == True{} : Bool}, B.fail_done(Fg.FgPlan, Main.Refused{1, "concurrent revisions each state the whole content of the file " ++ file ++ ", and bytes do not merge; record the version you mean, which is the only thing that can decide it"}, p, e))
    case Some{+target}:
      whole_of(target, Fg.held.size(files, target), Stand.payload.standing(stood, target), n, p, e)

# What the command line says
# --------------------------

def go_fail(ws: List<&2, String>, -e: Main.Refused) -> {Fg.reading.go(ws, Fail{e}) == Fail{e} : Result<&2, &2, Main.Refused, Fg.FgReading>}:
  match ws:
    case Nil{}:
      {==}
    case w <> rest:
      go_fail(rest, e)

def app_nil(+xs: List<&2, String>) -> {List.append(&2, String, xs, Nil{}) == xs : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case x <> +rest:
      %Equal.sym(List<&2, String>, List.append(&2, String, rest, Nil{}), rest, app_nil(rest)) : {x <> _ == x <> rest : List<&2, String>}
      {==}

def app_one(xs: List<&2, String>, +w: String, +rest: List<&2, String>) -> {List.append(&2, String, List.append(&2, String, xs, [w]), rest) == List.append(&2, String, xs, w <> rest) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case x <> +more:
      %Equal.sym(List<&2, String>, List.append(&2, String, List.append(&2, String, more, [w]), rest), List.append(&2, String, more, w <> rest), app_one(more, w, rest)) : {x <> _ == x <> List.append(&2, String, more, w <> rest) : List<&2, String>}
      {==}

# What a command line says, read plainly. `skip` is whether the word
# before was a `--lines`, whose word this one is.
def plain.said(ws: List<&2, String>, skip: Bool) -> List<&2, String>:
  match ws skip:
    case Nil{} _:
      Nil{}
    case w <> rest True{}:
      plain.said(rest, False{})
    case +w <> +rest False{}:
      Bool.pick(List<&2, String>, String.eq(w, "--lines"), plain.said(rest, True{}), Rev.keep(Bool.not(String.starts_with(w, "-")), w, plain.said(rest, False{})))

def dry.said(ws: List<&2, String>, skip: Bool) -> Bool:
  match ws skip:
    case Nil{} _:
      False{}
    case w <> rest True{}:
      dry.said(rest, False{})
    case +w <> +rest False{}:
      Bool.pick(Bool, String.eq(w, "--lines"), dry.said(rest, True{}), Bool.or(Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), dry.said(rest, False{})))

def fields.said(ws: List<&2, String>, skip: Bool) -> Bool:
  match ws skip:
    case Nil{} _:
      False{}
    case w <> rest True{}:
      fields.said(rest, False{})
    case +w <> +rest False{}:
      Bool.pick(Bool, String.eq(w, "--lines"), fields.said(rest, True{}), Bool.or(String.eq(w, "--fields"), fields.said(rest, False{})))

# The first of two that is something.
def later(a: Maybe<&2, String>, b: Maybe<&2, String>) -> Maybe<&2, String>:
  match a:
    case Some{x}:
      Some{x}
    case None{}:
      b

# The word after the last `--lines`.
def lines.said(ws: List<&2, String>, skip: Bool) -> Maybe<&2, String>:
  match ws skip:
    case Nil{} _:
      None{}
    case +w <> rest True{}:
      later(lines.said(rest, False{}), Some{w})
    case +w <> +rest False{}:
      Bool.pick(Maybe<&2, String>, String.eq(w, "--lines"), lines.said(rest, True{}), lines.said(rest, False{}))

# A reading, whatever it was waiting for.
def seen(r: Fg.FgReading) -> Fg.FgReading:
  match r:
    case Fg.Fg.Reading{l, d, f, ws, x}:
      Fg.Fg.Reading{l, d, f, ws, False{}}

def or_f(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def or_t(b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def later_some(a: Maybe<&2, String>, +w: String, b: Maybe<&2, String>) -> {later(later(a, Some{w}), b) == later(a, Some{w}) : Maybe<&2, String>}:
  match a:
    case Some{x}:
      {==}
    case None{}:
      {==}

def later_none(a: Maybe<&2, String>) -> {later(a, None{}) == a : Maybe<&2, String>}:
  match a:
    case Some{x}:
      {==}
    case None{}:
      {==}

def retag(k1: Fg.FgWord, k2: Fg.FgWord, +rest: List<&2, String>, +st: Fg.FgReading, +w: String, +r: Fg.FgReading, hk: {k1 == k2 : Fg.FgWord}, e: {Fg.reading.go(rest, Fg.reading.word(st, w, k1)) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>}) -> {Fg.reading.go(rest, Fg.reading.word(st, w, k2)) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>}:
  Equal.trans(Result<&2, &2, Main.Refused, Fg.FgReading>, Fg.reading.go(rest, Fg.reading.word(st, w, k2)), Fg.reading.go(rest, Fg.reading.word(st, w, k1)), Done{r},
    Equal.sym(Result<&2, &2, Main.Refused, Fg.FgReading>, Fg.reading.go(rest, Fg.reading.word(st, w, k1)), Fg.reading.go(rest, Fg.reading.word(st, w, k2)), Equal.cong(Fg.FgWord, Result<&2, &2, Main.Refused, Fg.FgReading>, k => Fg.reading.go(rest, Fg.reading.word(st, w, k)), k1, k2, hk)), e)

def rd_lines(+w: String, +rest: List<&2, String>, +l: Maybe<&2, String>, +d0: Bool, +f0: Bool, +acc: List<&2, String>, +r: Fg.FgReading, +hw: {w == "--lines" : String}, e: {Fg.reading.go(rest, Fg.reading.word(Fg.Fg.Reading{l, d0, f0, acc, False{}}, w, Fg.word(w))) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>}, ih: @l2: Maybe<&2, String> -> @d2: Bool -> @f2: Bool -> @acc2: List<&2, String> -> @w2: Bool -> {Fg.reading.go(rest, Done{Fg.Fg.Reading{l2, d2, f2, acc2, w2}}) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>} -> {seen(r) == Fg.Fg.Reading{later(lines.said(rest, w2), l2), Bool.or(d2, dry.said(rest, w2)), Bool.or(f2, fields.said(rest, w2)), List.append(&2, String, acc2, plain.said(rest, w2)), False{}} : Fg.FgReading}) -> {seen(r) == Fg.Fg.Reading{later(Bool.pick(Maybe<&2, String>, String.eq(w, "--lines"), lines.said(rest, True{}), lines.said(rest, False{})), l), Bool.or(d0, Bool.pick(Bool, String.eq(w, "--lines"), dry.said(rest, True{}), Bool.or(Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), dry.said(rest, False{})))), Bool.or(f0, Bool.pick(Bool, String.eq(w, "--lines"), fields.said(rest, True{}), Bool.or(String.eq(w, "--fields"), fields.said(rest, False{})))), List.append(&2, String, acc, Bool.pick(List<&2, String>, String.eq(w, "--lines"), plain.said(rest, True{}), Rev.keep(Bool.not(String.starts_with(w, "-")), w, plain.said(rest, False{})))), False{}} : Fg.FgReading}:
  +e2 = retag(Fg.word(w), Fg.Fg.Lines{}, rest, Fg.Fg.Reading{l, d0, f0, acc, False{}}, w, r, (%Equal.sym(String, w, "--lines", hw) : {Fg.word(_) == Fg.Fg.Lines{} : Fg.FgWord}; {==}), e)
  %Equal.sym(String, w, "--lines", hw) : {seen(r) == Fg.Fg.Reading{later(Bool.pick(Maybe<&2, String>, String.eq(_, "--lines"), lines.said(rest, True{}), lines.said(rest, False{})), l), Bool.or(d0, Bool.pick(Bool, String.eq(_, "--lines"), dry.said(rest, True{}), Bool.or(Bool.or(String.eq(_, "-n"), String.eq(_, "--dry-run")), dry.said(rest, False{})))), Bool.or(f0, Bool.pick(Bool, String.eq(_, "--lines"), fields.said(rest, True{}), Bool.or(String.eq(_, "--fields"), fields.said(rest, False{})))), List.append(&2, String, acc, Bool.pick(List<&2, String>, String.eq(_, "--lines"), plain.said(rest, True{}), Rev.keep(Bool.not(String.starts_with(_, "-")), _, plain.said(rest, False{})))), False{}} : Fg.FgReading}
  ih(l, d0, f0, acc, True{}, e2)

def rd_n(+w: String, +rest: List<&2, String>, +l: Maybe<&2, String>, +d0: Bool, +f0: Bool, +acc: List<&2, String>, +r: Fg.FgReading, +hw: {w == "-n" : String}, e: {Fg.reading.go(rest, Fg.reading.word(Fg.Fg.Reading{l, d0, f0, acc, False{}}, w, Fg.word(w))) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>}, ih: @l2: Maybe<&2, String> -> @d2: Bool -> @f2: Bool -> @acc2: List<&2, String> -> @w2: Bool -> {Fg.reading.go(rest, Done{Fg.Fg.Reading{l2, d2, f2, acc2, w2}}) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>} -> {seen(r) == Fg.Fg.Reading{later(lines.said(rest, w2), l2), Bool.or(d2, dry.said(rest, w2)), Bool.or(f2, fields.said(rest, w2)), List.append(&2, String, acc2, plain.said(rest, w2)), False{}} : Fg.FgReading}) -> {seen(r) == Fg.Fg.Reading{later(Bool.pick(Maybe<&2, String>, String.eq(w, "--lines"), lines.said(rest, True{}), lines.said(rest, False{})), l), Bool.or(d0, Bool.pick(Bool, String.eq(w, "--lines"), dry.said(rest, True{}), Bool.or(Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), dry.said(rest, False{})))), Bool.or(f0, Bool.pick(Bool, String.eq(w, "--lines"), fields.said(rest, True{}), Bool.or(String.eq(w, "--fields"), fields.said(rest, False{})))), List.append(&2, String, acc, Bool.pick(List<&2, String>, String.eq(w, "--lines"), plain.said(rest, True{}), Rev.keep(Bool.not(String.starts_with(w, "-")), w, plain.said(rest, False{})))), False{}} : Fg.FgReading}:
  +e2 = retag(Fg.word(w), Fg.Fg.Dry{}, rest, Fg.Fg.Reading{l, d0, f0, acc, False{}}, w, r, (%Equal.sym(String, w, "-n", hw) : {Fg.word(_) == Fg.Fg.Dry{} : Fg.FgWord}; {==}), e)
  %Equal.sym(String, w, "-n", hw) : {seen(r) == Fg.Fg.Reading{later(Bool.pick(Maybe<&2, String>, String.eq(_, "--lines"), lines.said(rest, True{}), lines.said(rest, False{})), l), Bool.or(d0, Bool.pick(Bool, String.eq(_, "--lines"), dry.said(rest, True{}), Bool.or(Bool.or(String.eq(_, "-n"), String.eq(_, "--dry-run")), dry.said(rest, False{})))), Bool.or(f0, Bool.pick(Bool, String.eq(_, "--lines"), fields.said(rest, True{}), Bool.or(String.eq(_, "--fields"), fields.said(rest, False{})))), List.append(&2, String, acc, Bool.pick(List<&2, String>, String.eq(_, "--lines"), plain.said(rest, True{}), Rev.keep(Bool.not(String.starts_with(_, "-")), _, plain.said(rest, False{})))), False{}} : Fg.FgReading}
  %Equal.sym(Bool, Bool.or(d0, True{}), True{}, or_t(d0)) : {seen(r) == Fg.Fg.Reading{later(lines.said(rest, False{}), l), _, Bool.or(f0, fields.said(rest, False{})), List.append(&2, String, acc, plain.said(rest, False{})), False{}} : Fg.FgReading}
  ih(l, True{}, f0, acc, False{}, e2)

def rd_dry(+w: String, +rest: List<&2, String>, +l: Maybe<&2, String>, +d0: Bool, +f0: Bool, +acc: List<&2, String>, +r: Fg.FgReading, +hw: {w == "--dry-run" : String}, e: {Fg.reading.go(rest, Fg.reading.word(Fg.Fg.Reading{l, d0, f0, acc, False{}}, w, Fg.word(w))) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>}, ih: @l2: Maybe<&2, String> -> @d2: Bool -> @f2: Bool -> @acc2: List<&2, String> -> @w2: Bool -> {Fg.reading.go(rest, Done{Fg.Fg.Reading{l2, d2, f2, acc2, w2}}) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>} -> {seen(r) == Fg.Fg.Reading{later(lines.said(rest, w2), l2), Bool.or(d2, dry.said(rest, w2)), Bool.or(f2, fields.said(rest, w2)), List.append(&2, String, acc2, plain.said(rest, w2)), False{}} : Fg.FgReading}) -> {seen(r) == Fg.Fg.Reading{later(Bool.pick(Maybe<&2, String>, String.eq(w, "--lines"), lines.said(rest, True{}), lines.said(rest, False{})), l), Bool.or(d0, Bool.pick(Bool, String.eq(w, "--lines"), dry.said(rest, True{}), Bool.or(Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), dry.said(rest, False{})))), Bool.or(f0, Bool.pick(Bool, String.eq(w, "--lines"), fields.said(rest, True{}), Bool.or(String.eq(w, "--fields"), fields.said(rest, False{})))), List.append(&2, String, acc, Bool.pick(List<&2, String>, String.eq(w, "--lines"), plain.said(rest, True{}), Rev.keep(Bool.not(String.starts_with(w, "-")), w, plain.said(rest, False{})))), False{}} : Fg.FgReading}:
  +e2 = retag(Fg.word(w), Fg.Fg.Dry{}, rest, Fg.Fg.Reading{l, d0, f0, acc, False{}}, w, r, (%Equal.sym(String, w, "--dry-run", hw) : {Fg.word(_) == Fg.Fg.Dry{} : Fg.FgWord}; {==}), e)
  %Equal.sym(String, w, "--dry-run", hw) : {seen(r) == Fg.Fg.Reading{later(Bool.pick(Maybe<&2, String>, String.eq(_, "--lines"), lines.said(rest, True{}), lines.said(rest, False{})), l), Bool.or(d0, Bool.pick(Bool, String.eq(_, "--lines"), dry.said(rest, True{}), Bool.or(Bool.or(String.eq(_, "-n"), String.eq(_, "--dry-run")), dry.said(rest, False{})))), Bool.or(f0, Bool.pick(Bool, String.eq(_, "--lines"), fields.said(rest, True{}), Bool.or(String.eq(_, "--fields"), fields.said(rest, False{})))), List.append(&2, String, acc, Bool.pick(List<&2, String>, String.eq(_, "--lines"), plain.said(rest, True{}), Rev.keep(Bool.not(String.starts_with(_, "-")), _, plain.said(rest, False{})))), False{}} : Fg.FgReading}
  %Equal.sym(Bool, Bool.or(d0, True{}), True{}, or_t(d0)) : {seen(r) == Fg.Fg.Reading{later(lines.said(rest, False{}), l), _, Bool.or(f0, fields.said(rest, False{})), List.append(&2, String, acc, plain.said(rest, False{})), False{}} : Fg.FgReading}
  ih(l, True{}, f0, acc, False{}, e2)

def rd_fields(+w: String, +rest: List<&2, String>, +l: Maybe<&2, String>, +d0: Bool, +f0: Bool, +acc: List<&2, String>, +r: Fg.FgReading, +hw: {w == "--fields" : String}, e: {Fg.reading.go(rest, Fg.reading.word(Fg.Fg.Reading{l, d0, f0, acc, False{}}, w, Fg.word(w))) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>}, ih: @l2: Maybe<&2, String> -> @d2: Bool -> @f2: Bool -> @acc2: List<&2, String> -> @w2: Bool -> {Fg.reading.go(rest, Done{Fg.Fg.Reading{l2, d2, f2, acc2, w2}}) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>} -> {seen(r) == Fg.Fg.Reading{later(lines.said(rest, w2), l2), Bool.or(d2, dry.said(rest, w2)), Bool.or(f2, fields.said(rest, w2)), List.append(&2, String, acc2, plain.said(rest, w2)), False{}} : Fg.FgReading}) -> {seen(r) == Fg.Fg.Reading{later(Bool.pick(Maybe<&2, String>, String.eq(w, "--lines"), lines.said(rest, True{}), lines.said(rest, False{})), l), Bool.or(d0, Bool.pick(Bool, String.eq(w, "--lines"), dry.said(rest, True{}), Bool.or(Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), dry.said(rest, False{})))), Bool.or(f0, Bool.pick(Bool, String.eq(w, "--lines"), fields.said(rest, True{}), Bool.or(String.eq(w, "--fields"), fields.said(rest, False{})))), List.append(&2, String, acc, Bool.pick(List<&2, String>, String.eq(w, "--lines"), plain.said(rest, True{}), Rev.keep(Bool.not(String.starts_with(w, "-")), w, plain.said(rest, False{})))), False{}} : Fg.FgReading}:
  +e2 = retag(Fg.word(w), Fg.Fg.Fields{}, rest, Fg.Fg.Reading{l, d0, f0, acc, False{}}, w, r, (%Equal.sym(String, w, "--fields", hw) : {Fg.word(_) == Fg.Fg.Fields{} : Fg.FgWord}; {==}), e)
  %Equal.sym(String, w, "--fields", hw) : {seen(r) == Fg.Fg.Reading{later(Bool.pick(Maybe<&2, String>, String.eq(_, "--lines"), lines.said(rest, True{}), lines.said(rest, False{})), l), Bool.or(d0, Bool.pick(Bool, String.eq(_, "--lines"), dry.said(rest, True{}), Bool.or(Bool.or(String.eq(_, "-n"), String.eq(_, "--dry-run")), dry.said(rest, False{})))), Bool.or(f0, Bool.pick(Bool, String.eq(_, "--lines"), fields.said(rest, True{}), Bool.or(String.eq(_, "--fields"), fields.said(rest, False{})))), List.append(&2, String, acc, Bool.pick(List<&2, String>, String.eq(_, "--lines"), plain.said(rest, True{}), Rev.keep(Bool.not(String.starts_with(_, "-")), _, plain.said(rest, False{})))), False{}} : Fg.FgReading}
  %Equal.sym(Bool, Bool.or(f0, True{}), True{}, or_t(f0)) : {seen(r) == Fg.Fg.Reading{later(lines.said(rest, False{}), l), Bool.or(d0, dry.said(rest, False{})), _, List.append(&2, String, acc, plain.said(rest, False{})), False{}} : Fg.FgReading}
  ih(l, d0, True{}, acc, False{}, e2)

def word_plain(+w: String, +ea: {String.eq(w, "--lines") == False{} : Bool}, +eb: {Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")) == False{} : Bool}, +ec: {String.eq(w, "--fields") == False{} : Bool}) -> {Fg.word(w) == Bool.pick(Fg.FgWord, String.starts_with(w, "-"), Fg.Fg.Flag{}, Fg.Fg.Plain{}) : Fg.FgWord}:
  %Equal.sym(Bool, String.eq(w, "--lines"), False{}, ea) : {Bool.pick(Fg.FgWord, _, Fg.Fg.Lines{}, Bool.pick(Fg.FgWord, Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), Fg.Fg.Dry{}, Bool.pick(Fg.FgWord, String.eq(w, "--fields"), Fg.Fg.Fields{}, Bool.pick(Fg.FgWord, String.starts_with(w, "-"), Fg.Fg.Flag{}, Fg.Fg.Plain{})))) == Bool.pick(Fg.FgWord, String.starts_with(w, "-"), Fg.Fg.Flag{}, Fg.Fg.Plain{}) : Fg.FgWord}
  %Equal.sym(Bool, Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), False{}, eb) : {Bool.pick(Fg.FgWord, _, Fg.Fg.Dry{}, Bool.pick(Fg.FgWord, String.eq(w, "--fields"), Fg.Fg.Fields{}, Bool.pick(Fg.FgWord, String.starts_with(w, "-"), Fg.Fg.Flag{}, Fg.Fg.Plain{}))) == Bool.pick(Fg.FgWord, String.starts_with(w, "-"), Fg.Fg.Flag{}, Fg.Fg.Plain{}) : Fg.FgWord}
  %Equal.sym(Bool, String.eq(w, "--fields"), False{}, ec) : {Bool.pick(Fg.FgWord, _, Fg.Fg.Fields{}, Bool.pick(Fg.FgWord, String.starts_with(w, "-"), Fg.Fg.Flag{}, Fg.Fg.Plain{})) == Bool.pick(Fg.FgWord, String.starts_with(w, "-"), Fg.Fg.Flag{}, Fg.Fg.Plain{}) : Fg.FgWord}
  {==}

def rd_plain(sw: Bool, +w: String, +rest: List<&2, String>, +l: Maybe<&2, String>, +d0: Bool, +f0: Bool, +acc: List<&2, String>, +r: Fg.FgReading, e2: {Fg.reading.go(rest, Fg.reading.word(Fg.Fg.Reading{l, d0, f0, acc, False{}}, w, Bool.pick(Fg.FgWord, sw, Fg.Fg.Flag{}, Fg.Fg.Plain{}))) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>}, ih: @l2: Maybe<&2, String> -> @d2: Bool -> @f2: Bool -> @acc2: List<&2, String> -> @w2: Bool -> {Fg.reading.go(rest, Done{Fg.Fg.Reading{l2, d2, f2, acc2, w2}}) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>} -> {seen(r) == Fg.Fg.Reading{later(lines.said(rest, w2), l2), Bool.or(d2, dry.said(rest, w2)), Bool.or(f2, fields.said(rest, w2)), List.append(&2, String, acc2, plain.said(rest, w2)), False{}} : Fg.FgReading}) -> {seen(r) == Fg.Fg.Reading{later(lines.said(rest, False{}), l), Bool.or(d0, dry.said(rest, False{})), Bool.or(f0, fields.said(rest, False{})), List.append(&2, String, acc, Rev.keep(Bool.not(sw), w, plain.said(rest, False{}))), False{}} : Fg.FgReading}:
  match sw:
    case True{}:
      +bad = {Main.Refused{2, "`" ++ w ++ "` is not an argument `forget` takes"} : Main.Refused}
      Empty.absurd({seen(r) == Fg.Fg.Reading{later(lines.said(rest, False{}), l), Bool.or(d0, dry.said(rest, False{})), Bool.or(f0, fields.said(rest, False{})), List.append(&2, String, acc, Rev.keep(Bool.not(True{}), w, plain.said(rest, False{}))), False{}} : Fg.FgReading},
        B.fail_done(Fg.FgReading, bad, r, Equal.trans(Result<&2, &2, Main.Refused, Fg.FgReading>, Fail{bad}, Fg.reading.go(rest, Fail{bad}), Done{r}, Equal.sym(Result<&2, &2, Main.Refused, Fg.FgReading>, Fg.reading.go(rest, Fail{bad}), Fail{bad}, go_fail(rest, bad)), e2)))
    case False{}:
      +h = ih(l, d0, f0, List.append(&2, String, acc, [w]), False{}, e2)
      %app_one(acc, w, plain.said(rest, False{})) : {seen(r) == Fg.Fg.Reading{later(lines.said(rest, False{}), l), Bool.or(d0, dry.said(rest, False{})), Bool.or(f0, fields.said(rest, False{})), _, False{}} : Fg.FgReading}
      h

def rd_nd(n: Bool, +w: String, +rest: List<&2, String>, +l: Maybe<&2, String>, +d0: Bool, +f0: Bool, +acc: List<&2, String>, +r: Fg.FgReading, +en: {String.eq(w, "-n") == n : Bool}, eb: {Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")) == True{} : Bool}, e: {Fg.reading.go(rest, Fg.reading.word(Fg.Fg.Reading{l, d0, f0, acc, False{}}, w, Fg.word(w))) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>}, ih: @l2: Maybe<&2, String> -> @d2: Bool -> @f2: Bool -> @acc2: List<&2, String> -> @w2: Bool -> {Fg.reading.go(rest, Done{Fg.Fg.Reading{l2, d2, f2, acc2, w2}}) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>} -> {seen(r) == Fg.Fg.Reading{later(lines.said(rest, w2), l2), Bool.or(d2, dry.said(rest, w2)), Bool.or(f2, fields.said(rest, w2)), List.append(&2, String, acc2, plain.said(rest, w2)), False{}} : Fg.FgReading}) -> {seen(r) == Fg.Fg.Reading{later(Bool.pick(Maybe<&2, String>, String.eq(w, "--lines"), lines.said(rest, True{}), lines.said(rest, False{})), l), Bool.or(d0, Bool.pick(Bool, String.eq(w, "--lines"), dry.said(rest, True{}), Bool.or(Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), dry.said(rest, False{})))), Bool.or(f0, Bool.pick(Bool, String.eq(w, "--lines"), fields.said(rest, True{}), Bool.or(String.eq(w, "--fields"), fields.said(rest, False{})))), List.append(&2, String, acc, Bool.pick(List<&2, String>, String.eq(w, "--lines"), plain.said(rest, True{}), Rev.keep(Bool.not(String.starts_with(w, "-")), w, plain.said(rest, False{})))), False{}} : Fg.FgReading}:
  match n:
    case True{}:
      rd_n(w, rest, l, d0, f0, acc, r, S.eq_true(w, "-n", en), e, ih)
    case False{}:
      rd_dry(w, rest, l, d0, f0, acc, r, S.eq_true(w, "--dry-run", Equal.trans(Bool, String.eq(w, "--dry-run"), Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), True{}, Equal.sym(Bool, Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), String.eq(w, "--dry-run"), Equal.cong(Bool, Bool, x => Bool.or(x, String.eq(w, "--dry-run")), String.eq(w, "-n"), False{}, en)), eb)), e, ih)

def rd_c(c: Bool, +w: String, +rest: List<&2, String>, +l: Maybe<&2, String>, +d0: Bool, +f0: Bool, +acc: List<&2, String>, +r: Fg.FgReading, +ea: {String.eq(w, "--lines") == False{} : Bool}, +eb: {Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")) == False{} : Bool}, +ec: {String.eq(w, "--fields") == c : Bool}, e: {Fg.reading.go(rest, Fg.reading.word(Fg.Fg.Reading{l, d0, f0, acc, False{}}, w, Fg.word(w))) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>}, ih: @l2: Maybe<&2, String> -> @d2: Bool -> @f2: Bool -> @acc2: List<&2, String> -> @w2: Bool -> {Fg.reading.go(rest, Done{Fg.Fg.Reading{l2, d2, f2, acc2, w2}}) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>} -> {seen(r) == Fg.Fg.Reading{later(lines.said(rest, w2), l2), Bool.or(d2, dry.said(rest, w2)), Bool.or(f2, fields.said(rest, w2)), List.append(&2, String, acc2, plain.said(rest, w2)), False{}} : Fg.FgReading}) -> {seen(r) == Fg.Fg.Reading{later(lines.said(rest, False{}), l), Bool.or(d0, dry.said(rest, False{})), Bool.or(f0, Bool.or(c, fields.said(rest, False{}))), List.append(&2, String, acc, Rev.keep(Bool.not(String.starts_with(w, "-")), w, plain.said(rest, False{}))), False{}} : Fg.FgReading}:
  match c:
    case True{}:
      %ec : {seen(r) == Fg.Fg.Reading{later(Bool.pick(Maybe<&2, String>, False{}, lines.said(rest, True{}), lines.said(rest, False{})), l), Bool.or(d0, Bool.pick(Bool, False{}, dry.said(rest, True{}), Bool.or(False{}, dry.said(rest, False{})))), Bool.or(f0, Bool.pick(Bool, False{}, fields.said(rest, True{}), Bool.or(_, fields.said(rest, False{})))), List.append(&2, String, acc, Bool.pick(List<&2, String>, False{}, plain.said(rest, True{}), Rev.keep(Bool.not(String.starts_with(w, "-")), w, plain.said(rest, False{})))), False{}} : Fg.FgReading}
      %eb : {seen(r) == Fg.Fg.Reading{later(Bool.pick(Maybe<&2, String>, False{}, lines.said(rest, True{}), lines.said(rest, False{})), l), Bool.or(d0, Bool.pick(Bool, False{}, dry.said(rest, True{}), Bool.or(_, dry.said(rest, False{})))), Bool.or(f0, Bool.pick(Bool, False{}, fields.said(rest, True{}), Bool.or(String.eq(w, "--fields"), fields.said(rest, False{})))), List.append(&2, String, acc, Bool.pick(List<&2, String>, False{}, plain.said(rest, True{}), Rev.keep(Bool.not(String.starts_with(w, "-")), w, plain.said(rest, False{})))), False{}} : Fg.FgReading}
      %ea : {seen(r) == Fg.Fg.Reading{later(Bool.pick(Maybe<&2, String>, _, lines.said(rest, True{}), lines.said(rest, False{})), l), Bool.or(d0, Bool.pick(Bool, _, dry.said(rest, True{}), Bool.or(Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), dry.said(rest, False{})))), Bool.or(f0, Bool.pick(Bool, _, fields.said(rest, True{}), Bool.or(String.eq(w, "--fields"), fields.said(rest, False{})))), List.append(&2, String, acc, Bool.pick(List<&2, String>, _, plain.said(rest, True{}), Rev.keep(Bool.not(String.starts_with(w, "-")), w, plain.said(rest, False{})))), False{}} : Fg.FgReading}
      rd_fields(w, rest, l, d0, f0, acc, r, S.eq_true(w, "--fields", ec), e, ih)
    case False{}:
      rd_plain(String.starts_with(w, "-"), w, rest, l, d0, f0, acc, r, retag(Fg.word(w), Bool.pick(Fg.FgWord, String.starts_with(w, "-"), Fg.Fg.Flag{}, Fg.Fg.Plain{}), rest, Fg.Fg.Reading{l, d0, f0, acc, False{}}, w, r, word_plain(w, ea, eb, ec), e), ih)

def rd_b(b: Bool, +w: String, +rest: List<&2, String>, +l: Maybe<&2, String>, +d0: Bool, +f0: Bool, +acc: List<&2, String>, +r: Fg.FgReading, +ea: {String.eq(w, "--lines") == False{} : Bool}, +eb: {Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")) == b : Bool}, e: {Fg.reading.go(rest, Fg.reading.word(Fg.Fg.Reading{l, d0, f0, acc, False{}}, w, Fg.word(w))) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>}, ih: @l2: Maybe<&2, String> -> @d2: Bool -> @f2: Bool -> @acc2: List<&2, String> -> @w2: Bool -> {Fg.reading.go(rest, Done{Fg.Fg.Reading{l2, d2, f2, acc2, w2}}) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>} -> {seen(r) == Fg.Fg.Reading{later(lines.said(rest, w2), l2), Bool.or(d2, dry.said(rest, w2)), Bool.or(f2, fields.said(rest, w2)), List.append(&2, String, acc2, plain.said(rest, w2)), False{}} : Fg.FgReading}) -> {seen(r) == Fg.Fg.Reading{later(lines.said(rest, False{}), l), Bool.or(d0, Bool.or(b, dry.said(rest, False{}))), Bool.or(f0, Bool.or(String.eq(w, "--fields"), fields.said(rest, False{}))), List.append(&2, String, acc, Rev.keep(Bool.not(String.starts_with(w, "-")), w, plain.said(rest, False{}))), False{}} : Fg.FgReading}:
  match b:
    case True{}:
      %eb : {seen(r) == Fg.Fg.Reading{later(Bool.pick(Maybe<&2, String>, False{}, lines.said(rest, True{}), lines.said(rest, False{})), l), Bool.or(d0, Bool.pick(Bool, False{}, dry.said(rest, True{}), Bool.or(_, dry.said(rest, False{})))), Bool.or(f0, Bool.pick(Bool, False{}, fields.said(rest, True{}), Bool.or(String.eq(w, "--fields"), fields.said(rest, False{})))), List.append(&2, String, acc, Bool.pick(List<&2, String>, False{}, plain.said(rest, True{}), Rev.keep(Bool.not(String.starts_with(w, "-")), w, plain.said(rest, False{})))), False{}} : Fg.FgReading}
      %ea : {seen(r) == Fg.Fg.Reading{later(Bool.pick(Maybe<&2, String>, _, lines.said(rest, True{}), lines.said(rest, False{})), l), Bool.or(d0, Bool.pick(Bool, _, dry.said(rest, True{}), Bool.or(Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), dry.said(rest, False{})))), Bool.or(f0, Bool.pick(Bool, _, fields.said(rest, True{}), Bool.or(String.eq(w, "--fields"), fields.said(rest, False{})))), List.append(&2, String, acc, Bool.pick(List<&2, String>, _, plain.said(rest, True{}), Rev.keep(Bool.not(String.starts_with(w, "-")), w, plain.said(rest, False{})))), False{}} : Fg.FgReading}
      rd_nd(String.eq(w, "-n"), w, rest, l, d0, f0, acc, r, {==}, eb, e, ih)
    case False{}:
      rd_c(String.eq(w, "--fields"), w, rest, l, d0, f0, acc, r, ea, eb, {==}, e, ih)

def rd_a(a: Bool, +w: String, +rest: List<&2, String>, +l: Maybe<&2, String>, +d0: Bool, +f0: Bool, +acc: List<&2, String>, +r: Fg.FgReading, +ea: {String.eq(w, "--lines") == a : Bool}, e: {Fg.reading.go(rest, Fg.reading.word(Fg.Fg.Reading{l, d0, f0, acc, False{}}, w, Fg.word(w))) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>}, ih: @l2: Maybe<&2, String> -> @d2: Bool -> @f2: Bool -> @acc2: List<&2, String> -> @w2: Bool -> {Fg.reading.go(rest, Done{Fg.Fg.Reading{l2, d2, f2, acc2, w2}}) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>} -> {seen(r) == Fg.Fg.Reading{later(lines.said(rest, w2), l2), Bool.or(d2, dry.said(rest, w2)), Bool.or(f2, fields.said(rest, w2)), List.append(&2, String, acc2, plain.said(rest, w2)), False{}} : Fg.FgReading}) -> {seen(r) == Fg.Fg.Reading{later(Bool.pick(Maybe<&2, String>, a, lines.said(rest, True{}), lines.said(rest, False{})), l), Bool.or(d0, Bool.pick(Bool, a, dry.said(rest, True{}), Bool.or(Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), dry.said(rest, False{})))), Bool.or(f0, Bool.pick(Bool, a, fields.said(rest, True{}), Bool.or(String.eq(w, "--fields"), fields.said(rest, False{})))), List.append(&2, String, acc, Bool.pick(List<&2, String>, a, plain.said(rest, True{}), Rev.keep(Bool.not(String.starts_with(w, "-")), w, plain.said(rest, False{})))), False{}} : Fg.FgReading}:
  match a:
    case True{}:
      %ea : {seen(r) == Fg.Fg.Reading{later(Bool.pick(Maybe<&2, String>, _, lines.said(rest, True{}), lines.said(rest, False{})), l), Bool.or(d0, Bool.pick(Bool, _, dry.said(rest, True{}), Bool.or(Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), dry.said(rest, False{})))), Bool.or(f0, Bool.pick(Bool, _, fields.said(rest, True{}), Bool.or(String.eq(w, "--fields"), fields.said(rest, False{})))), List.append(&2, String, acc, Bool.pick(List<&2, String>, _, plain.said(rest, True{}), Rev.keep(Bool.not(String.starts_with(w, "-")), w, plain.said(rest, False{})))), False{}} : Fg.FgReading}
      rd_lines(w, rest, l, d0, f0, acc, r, S.eq_true(w, "--lines", ea), e, ih)
    case False{}:
      rd_b(Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), w, rest, l, d0, f0, acc, r, ea, {==}, e, ih)

def rd_step(wants: Bool, +w: String, +rest: List<&2, String>, +l: Maybe<&2, String>, +d0: Bool, +f0: Bool, +acc: List<&2, String>, +r: Fg.FgReading, e: {Fg.reading.go(rest, Fg.reading.step(Fg.Fg.Reading{l, d0, f0, acc, wants}, w)) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>}, ih: @l2: Maybe<&2, String> -> @d2: Bool -> @f2: Bool -> @acc2: List<&2, String> -> @w2: Bool -> {Fg.reading.go(rest, Done{Fg.Fg.Reading{l2, d2, f2, acc2, w2}}) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>} -> {seen(r) == Fg.Fg.Reading{later(lines.said(rest, w2), l2), Bool.or(d2, dry.said(rest, w2)), Bool.or(f2, fields.said(rest, w2)), List.append(&2, String, acc2, plain.said(rest, w2)), False{}} : Fg.FgReading}) -> {seen(r) == Fg.Fg.Reading{later(lines.said((w <> rest), wants), l), Bool.or(d0, dry.said((w <> rest), wants)), Bool.or(f0, fields.said((w <> rest), wants)), List.append(&2, String, acc, plain.said((w <> rest), wants)), False{}} : Fg.FgReading}:
  match wants:
    case True{}:
      %Equal.sym(Maybe<&2, String>, later(later(lines.said(rest, False{}), Some{w}), l), later(lines.said(rest, False{}), Some{w}), later_some(lines.said(rest, False{}), w, l)) : {seen(r) == Fg.Fg.Reading{_, Bool.or(d0, dry.said(rest, False{})), Bool.or(f0, fields.said(rest, False{})), List.append(&2, String, acc, plain.said(rest, False{})), False{}} : Fg.FgReading}
      ih(Some{w}, d0, f0, acc, False{}, e)
    case False{}:
      rd_a(String.eq(w, "--lines"), w, rest, l, d0, f0, acc, r, {==}, e, ih)

# Whatever `reading.go` reads, it reads as the plain readings say, after
# what it had read already.
def rd_go(ws: List<&2, String>, +l: Maybe<&2, String>, +d0: Bool, +f0: Bool, +acc: List<&2, String>, +wants: Bool, +r: Fg.FgReading, e: {Fg.reading.go(ws, Done{Fg.Fg.Reading{l, d0, f0, acc, wants}}) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>}) -> {seen(r) == Fg.Fg.Reading{later(lines.said(ws, wants), l), Bool.or(d0, dry.said(ws, wants)), Bool.or(f0, fields.said(ws, wants)), List.append(&2, String, acc, plain.said(ws, wants)), False{}} : Fg.FgReading}:
  match ws:
    case Nil{}:
      +eq = B.done_eq(Fg.FgReading, Fg.Fg.Reading{l, d0, f0, acc, wants}, r, e)
      %eq : {seen(_) == Fg.Fg.Reading{later(lines.said(Nil{}, wants), l), Bool.or(d0, dry.said(Nil{}, wants)), Bool.or(f0, fields.said(Nil{}, wants)), List.append(&2, String, acc, plain.said(Nil{}, wants)), False{}} : Fg.FgReading}
      %Equal.sym(Bool, Bool.or(d0, False{}), d0, or_f(d0)) : {Fg.Fg.Reading{l, d0, f0, acc, False{}} == Fg.Fg.Reading{l, _, Bool.or(f0, False{}), List.append(&2, String, acc, Nil{}), False{}} : Fg.FgReading}
      %Equal.sym(Bool, Bool.or(f0, False{}), f0, or_f(f0)) : {Fg.Fg.Reading{l, d0, f0, acc, False{}} == Fg.Fg.Reading{l, d0, _, List.append(&2, String, acc, Nil{}), False{}} : Fg.FgReading}
      %Equal.sym(List<&2, String>, List.append(&2, String, acc, Nil{}), acc, app_nil(acc)) : {Fg.Fg.Reading{l, d0, f0, acc, False{}} == Fg.Fg.Reading{l, d0, f0, _, False{}} : Fg.FgReading}
      {==}
    case +w <> +rest:
      rd_step(wants, w, rest, l, d0, f0, acc, r, e, l2 => d2 => f2 => acc2 => w2 => h2 => rd_go(rest, l2, d2, f2, acc2, w2, r, h2))

def read.words(r: Fg.FgReading) -> Result<&2, &2, Main.Refused, Fg.FgAsked>:
  match r:
    case Fg.Fg.Reading{l, +d, +f, ws, x}:
      Fg.asked.words(l, d, f, ws)

# A reading `asked.read` accepts is one whatever it says is taken from.
def read_words(+l: Maybe<&2, String>, d: Bool, f: Bool, +ws: List<&2, String>, wants: Bool, +a: Fg.FgAsked, e: {Fg.asked.read(Fg.Fg.Reading{l, d, f, ws, wants}) == Done{a} : Result<&2, &2, Main.Refused, Fg.FgAsked>}) -> {read.words(Fg.Fg.Reading{l, d, f, ws, wants}) == Done{a} : Result<&2, &2, Main.Refused, Fg.FgAsked>}:
  match d f wants:
    case True{} True{} True{}:
      Empty.absurd({Fg.asked.words(l, True{}, True{}, ws) == Done{a} : Result<&2, &2, Main.Refused, Fg.FgAsked>}, B.fail_done(Fg.FgAsked, Main.Refused{2, "`--lines` wants a span, as `<first>..<last>`"}, a, e))
    case True{} False{} True{}:
      Empty.absurd({Fg.asked.words(l, True{}, False{}, ws) == Done{a} : Result<&2, &2, Main.Refused, Fg.FgAsked>}, B.fail_done(Fg.FgAsked, Main.Refused{2, "`--lines` wants a span, as `<first>..<last>`"}, a, e))
    case False{} True{} True{}:
      Empty.absurd({Fg.asked.words(l, False{}, True{}, ws) == Done{a} : Result<&2, &2, Main.Refused, Fg.FgAsked>}, B.fail_done(Fg.FgAsked, Main.Refused{2, "`--lines` wants a span, as `<first>..<last>`"}, a, e))
    case False{} False{} True{}:
      Empty.absurd({Fg.asked.words(l, False{}, False{}, ws) == Done{a} : Result<&2, &2, Main.Refused, Fg.FgAsked>}, B.fail_done(Fg.FgAsked, Main.Refused{2, "`--lines` wants a span, as `<first>..<last>`"}, a, e))
    case True{} True{} False{}:
      Empty.absurd({Fg.asked.words(l, True{}, True{}, ws) == Done{a} : Result<&2, &2, Main.Refused, Fg.FgAsked>}, B.fail_done(Fg.FgAsked, Main.Refused{2, "`forget --dry-run --fields` is refused: `--fields` states what is on disk, and a plan is not on disk. ask for one or the other"}, a, e))
    case True{} False{} False{}:
      e
    case False{} True{} False{}:
      e
    case False{} False{} False{}:
      e

# What `asked.words` accepts, as the plain readings of it.
def said.of(a: Fg.FgAsked) -> List<&2, String> & (Bool & (Bool & Result<&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>>)):
  match a:
    case Fg.Fg.Asked{t, p, sp, d, f}:
      ([t, p], (d, (f, Done{sp})))

def span_said(+t: String, +p: String, +d: Bool, +f: Bool, +l: Maybe<&2, String>, m: Result<&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>>, em: {Fg.asked.span(l) == m : Result<&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>>}, +a: Fg.FgAsked, e: {Result.map(&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>, Fg.FgAsked, sp => Fg.Fg.Asked{t, p, sp, d, f}, m) == Done{a} : Result<&2, &2, Main.Refused, Fg.FgAsked>}) -> {([t, p], (d, (f, Fg.asked.span(l)))) == said.of(a) : List<&2, String> & (Bool & (Bool & Result<&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>>))}:
  match m:
    case Fail{x}:
      Empty.absurd({([t, p], (d, (f, Fg.asked.span(l)))) == said.of(a) : List<&2, String> & (Bool & (Bool & Result<&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>>))}, B.fail_done(Fg.FgAsked, x, a, e))
    case Done{sp}:
      %Equal.sym(Result<&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>>, Fg.asked.span(l), Done{sp}, em) : {([t, p], (d, (f, _))) == said.of(a) : List<&2, String> & (Bool & (Bool & Result<&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>>))}
      Equal.cong(Fg.FgAsked, List<&2, String> & (Bool & (Bool & Result<&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>>)), x => said.of(x), Fg.Fg.Asked{t, p, sp, d, f}, a, B.done_eq(Fg.FgAsked, Fg.Fg.Asked{t, p, sp, d, f}, a, e))

def words_said(+l: Maybe<&2, String>, +d: Bool, +f: Bool, ws: List<&2, String>, +a: Fg.FgAsked, e: {Fg.asked.words(l, d, f, ws) == Done{a} : Result<&2, &2, Main.Refused, Fg.FgAsked>}) -> {(ws, (d, (f, Fg.asked.span(l)))) == said.of(a) : List<&2, String> & (Bool & (Bool & Result<&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>>))}:
  match ws:
    case Nil{}:
      Empty.absurd({(Nil{}, (d, (f, Fg.asked.span(l)))) == said.of(a) : List<&2, String> & (Bool & (Bool & Result<&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>>))}, B.fail_done(Fg.FgAsked, Main.Refused{2, "`forget` wants a revision to read the span at"}, a, e))
    case t <> Nil{}:
      Empty.absurd({([t], (d, (f, Fg.asked.span(l)))) == said.of(a) : List<&2, String> & (Bool & (Bool & Result<&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>>))}, B.fail_done(Fg.FgAsked, Main.Refused{2, "`forget` wants a path"}, a, e))
    case +t <> +p <> Nil{}:
      span_said(t, p, d, f, l, Fg.asked.span(l), {==}, a, e)
    case t <> p <> +x <> more:
      Empty.absurd({(t <> p <> x <> more, (d, (f, Fg.asked.span(l)))) == said.of(a) : List<&2, String> & (Bool & (Bool & Result<&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>>))}, B.fail_done(Fg.FgAsked, Main.Refused{2, "`forget` takes a target and one path, and `" ++ x ++ "` is a third argument"}, a, e))

def read.said(r: Fg.FgReading) -> List<&2, String> & (Bool & (Bool & Result<&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>>)):
  match r:
    case Fg.Fg.Reading{+l, d, f, ws, x}:
      (ws, (d, (f, Fg.asked.span(l))))

def reading_said(r: Fg.FgReading, +a: Fg.FgAsked, e: {Fg.asked.read(r) == Done{a} : Result<&2, &2, Main.Refused, Fg.FgAsked>}) -> {read.said(seen(r)) == said.of(a) : List<&2, String> & (Bool & (Bool & Result<&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>>))}:
  match r:
    case Fg.Fg.Reading{+l, +d, +f, +ws, wants}:
      words_said(l, d, f, ws, a, read_words(l, d, f, ws, wants, a, e))

def asked_said(+ws: List<&2, String>, g: Result<&2, &2, Main.Refused, Fg.FgReading>, +eg: {Fg.reading.go(ws, Done{Fg.Fg.Reading{None{}, False{}, False{}, Nil{}, False{}}}) == g : Result<&2, &2, Main.Refused, Fg.FgReading>}, +a: Fg.FgAsked, e: {Result.bind(&2, &2, Main.Refused, Fg.FgReading, Fg.FgAsked, g, r => Fg.asked.read(r)) == Done{a} : Result<&2, &2, Main.Refused, Fg.FgAsked>}) -> {(plain.said(ws, False{}), (dry.said(ws, False{}), (fields.said(ws, False{}), Fg.asked.span(lines.said(ws, False{}))))) == said.of(a) : List<&2, String> & (Bool & (Bool & Result<&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>>))}:
  match g:
    case Fail{x}:
      Empty.absurd({(plain.said(ws, False{}), (dry.said(ws, False{}), (fields.said(ws, False{}), Fg.asked.span(lines.said(ws, False{}))))) == said.of(a) : List<&2, String> & (Bool & (Bool & Result<&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>>))}, B.fail_done(Fg.FgAsked, x, a, e))
    case Done{+r}:
      +h = rd_go(ws, None{}, False{}, False{}, Nil{}, False{}, r, eg)
      +hr = reading_said(r, a, e)
      %later_none(lines.said(ws, False{})) : {(plain.said(ws, False{}), (dry.said(ws, False{}), (fields.said(ws, False{}), Fg.asked.span(_)))) == said.of(a) : List<&2, String> & (Bool & (Bool & Result<&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>>))}
      Equal.trans(List<&2, String> & (Bool & (Bool & Result<&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>>)), read.said(Fg.Fg.Reading{later(lines.said(ws, False{}), None{}), Bool.or(False{}, dry.said(ws, False{})), Bool.or(False{}, fields.said(ws, False{})), List.append(&2, String, Nil{}, plain.said(ws, False{})), False{}}), read.said(seen(r)), said.of(a),
        Equal.sym(List<&2, String> & (Bool & (Bool & Result<&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>>)), read.said(seen(r)), read.said(Fg.Fg.Reading{later(lines.said(ws, False{}), None{}), Bool.or(False{}, dry.said(ws, False{})), Bool.or(False{}, fields.said(ws, False{})), List.append(&2, String, Nil{}, plain.said(ws, False{})), False{}}), Equal.cong(Fg.FgReading, List<&2, String> & (Bool & (Bool & Result<&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>>)), x => read.said(x), seen(r), Fg.Fg.Reading{later(lines.said(ws, False{}), None{}), Bool.or(False{}, dry.said(ws, False{})), Bool.or(False{}, fields.said(ws, False{})), List.append(&2, String, Nil{}, plain.said(ws, False{})), False{}}, h)),
        hr)

# `forget` reads its command line as its plain reading says.
def reads_words(+ws: List<&2, String>, +t: String, +p: String, +sp: Maybe<&2, Fg.FgSpan>, +d: Bool, +f: Bool, e: {Fg.asked.r(ws) == Done{Fg.Fg.Asked{t, p, sp, d, f}} : Result<&2, &2, Main.Refused, Fg.FgAsked>}) -> {(plain.said(ws, False{}), (dry.said(ws, False{}), (fields.said(ws, False{}), Fg.asked.span(lines.said(ws, False{}))))) == ([t, p], (d, (f, Done{sp}))) : List<&2, String> & (Bool & (Bool & Result<&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>>))}:
  asked_said(ws, Fg.reading.go(ws, Done{Fg.Fg.Reading{None{}, False{}, False{}, Nil{}, False{}}}), {==}, Fg.Fg.Asked{t, p, sp, d, f}, e)

# What `cache/` loses
# -------------------

def cached_step(b: Bool, +q: String, +rest: List<&2, String>, +p: String, hb: {T.is_digest(String.drop(q, 6n)) == b : Bool}, m: {Rev.member(Rev.keep(b, q, Fg.cached(rest)), p) == True{} : Bool}, ih: {Rev.member(Fg.cached(rest), p) == True{} : Bool} -> {T.is_digest(String.drop(p, 6n)) == True{} : Bool}) -> {T.is_digest(String.drop(p, 6n)) == True{} : Bool}:
  match b:
    case True{}:
      GL.member_cons({T.is_digest(String.drop(p, 6n)) == True{} : Bool}, q, Fg.cached(rest), p, m,
        h => (%h : {T.is_digest(String.drop(_, 6n)) == True{} : Bool}; hb),
        t => ih(t))
    case False{}:
      ih(m)

# What `cache/`'s listing names past `cache/` and is no digest, `forget`
# does not remove.
def clears(ps: List<&2, String>, +p: String, m: {Rev.member(Fg.cached(ps), p) == True{} : Bool}) -> {T.is_digest(String.drop(p, 6n)) == True{} : Bool}:
  match ps:
    case Nil{}:
      Empty.absurd({T.is_digest(String.drop(p, 6n)) == True{} : Bool}, S.false_true(m))
    case +q <> +rest:
      cached_step(T.is_digest(String.drop(q, 6n)), q, rest, p, {==}, m, t => clears(rest, p, t))

def kept_case(b: Bool, +ps: List<&2, String>, +p: String, hn: {T.is_digest(String.drop(p, 6n)) == False{} : Bool}, eb: {Rev.member(Fg.cached(ps), p) == b : Bool}) -> {Rev.member(Fg.cached(ps), p) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      Empty.absurd({Rev.member(Fg.cached(ps), p) == False{} : Bool}, S.false_true(Equal.trans(Bool, False{}, T.is_digest(String.drop(p, 6n)), True{}, Equal.sym(Bool, T.is_digest(String.drop(p, 6n)), False{}, hn), clears(ps, p, eb))))

# A name in `cache/` that is no digest stays, whatever else is listed.
def kept_note(+ps: List<&2, String>, +p: String, hn: {T.is_digest(String.drop(p, 6n)) == False{} : Bool}) -> {Rev.member(Fg.cached(ps), p) == False{} : Bool}:
  kept_case(Rev.member(Fg.cached(ps), p), ps, p, hn, {==})

# The note `init` writes and the catalogues the Rust store keeps in
# `cache/` all stay.
def notes_kept(+ps: List<&2, String>) -> {Bool.or(Rev.member(Fg.cached(ps), "cache/README.txt"), Bool.or(Rev.member(Fg.cached(ps), "cache/operations.txt"), Bool.or(Rev.member(Fg.cached(ps), "cache/working.txt"), Rev.member(Fg.cached(ps), "cache/revisions.txt")))) == False{} : Bool}:
  %Equal.sym(Bool, Rev.member(Fg.cached(ps), "cache/README.txt"), False{}, kept_note(ps, "cache/README.txt", {==})) : {Bool.or(_, Bool.or(Rev.member(Fg.cached(ps), "cache/operations.txt"), Bool.or(Rev.member(Fg.cached(ps), "cache/working.txt"), Rev.member(Fg.cached(ps), "cache/revisions.txt")))) == False{} : Bool}
  %Equal.sym(Bool, Rev.member(Fg.cached(ps), "cache/operations.txt"), False{}, kept_note(ps, "cache/operations.txt", {==})) : {Bool.or(False{}, Bool.or(_, Bool.or(Rev.member(Fg.cached(ps), "cache/working.txt"), Rev.member(Fg.cached(ps), "cache/revisions.txt")))) == False{} : Bool}
  %Equal.sym(Bool, Rev.member(Fg.cached(ps), "cache/working.txt"), False{}, kept_note(ps, "cache/working.txt", {==})) : {Bool.or(False{}, Bool.or(False{}, Bool.or(_, Rev.member(Fg.cached(ps), "cache/revisions.txt")))) == False{} : Bool}
  %Equal.sym(Bool, Rev.member(Fg.cached(ps), "cache/revisions.txt"), False{}, kept_note(ps, "cache/revisions.txt", {==})) : {Bool.or(False{}, Bool.or(False{}, Bool.or(False{}, _))) == False{} : Bool}
  {==}

def drop0(str: String) -> {String.drop(str, 0n) == str : String}:
  match str:
    case SNil{}:
      {==}
    case SCon{x, u}:
      {==}

def keep_mem(b: Bool, +y: String, +xs: List<&2, String>, +x: String, h: {Rev.member(xs, x) == True{} : Bool}) -> {Rev.member(Rev.keep(b, y, xs), x) == True{} : Bool}:
  match b:
    case True{}:
      GL.member_tail(y, xs, x, h)
    case False{}:
      h

# Every entry listed in `cache/` as a digest is removed.
def clears_copy(ps: List<&2, String>, +d: String, +hd: {T.is_digest(d) == True{} : Bool}, hm: {Rev.member(ps, "cache/" ++ d) == True{} : Bool}) -> {Rev.member(Fg.cached(ps), "cache/" ++ d) == True{} : Bool}:
  match ps:
    case Nil{}:
      Empty.absurd({Rev.member(Fg.cached(Nil{}), "cache/" ++ d) == True{} : Bool}, S.false_true(hm))
    case +q <> +rest:
      GL.member_cons({Rev.member(Fg.cached(q <> rest), "cache/" ++ d) == True{} : Bool}, q, rest, "cache/" ++ d, hm,
        e => (%Equal.sym(String, q, "cache/" ++ d, e) : {Rev.member(Rev.keep(T.is_digest(String.drop(_, 6n)), _, Fg.cached(rest)), "cache/" ++ d) == True{} : Bool};
          %Equal.sym(String, String.drop(d, 0n), d, drop0(d)) : {Rev.member(Rev.keep(T.is_digest(_), "cache/" ++ d, Fg.cached(rest)), "cache/" ++ d) == True{} : Bool};
          %Equal.sym(Bool, T.is_digest(d), True{}, hd) : {Rev.member(Rev.keep(_, "cache/" ++ d, Fg.cached(rest)), "cache/" ++ d) == True{} : Bool};
          GL.member_head("cache/" ++ d, Fg.cached(rest))),
        t => keep_mem(T.is_digest(String.drop(q, 6n)), q, Fg.cached(rest), "cache/" ++ d, clears_copy(rest, d, hd, t)))

# Replaying through a stand-in
# ----------------------------
#
# Decision 0014: replay does not consult payload. A document whose items
# are each the original's or that item forgotten, applied to a parent whose
# items are each the original parent's or forgotten, makes a file wherever
# the original makes one, and each of its lines is the original's line or
# that line forgotten: the cursor walk is run beside itself, a stage at a
# time, with a forgotten item agreeing with whatever its terminator allows.

def imp(a: Bool, b: Bool) -> Bool:
  Bool.or(Bool.not(a), b)

def xnor_eq(a: Bool, b: Bool, h: {Bool.not(Bool.xor(a, b)) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, S.false_true(h))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(h))

# The terminator a like item keeps.
def like_term(t1: String, n1: Bool, f1: Bool, t2: String, n2: Bool, f2: Bool, h: {Stand.item.like(Ops.Item{t1, n1, f1}, Ops.Item{t2, n2, f2}) == True{} : Bool}) -> {n1 == n2 : Bool}:
  match f2:
    case True{}:
      xnor_eq(n1, n2, h)
    case False{}:
      xnor_eq(n1, n2, Comp.and_right(T.same(t1, t2), Bool.not(Bool.xor(n1, n2)), Comp.and_right(Bool.not(f1), Bool.and(T.same(t1, t2), Bool.not(Bool.xor(n1, n2))), h)))

# Where either side is forgotten, agreement is the terminators', which a
# like item keeps.
def agrees_term(+nr1: Bool, +ns1: Bool, +nr2: Bool, +ns2: Bool, er: {nr1 == nr2 : Bool}, es: {ns1 == ns2 : Bool}, ha: {Bool.not(Bool.xor(nr1, ns1)) == True{} : Bool}) -> {Bool.and(Bool.not(Bool.xor(nr2, ns2)), True{}) == True{} : Bool}:
  %er : {Bool.and(Bool.not(Bool.xor(_, ns2)), True{}) == True{} : Bool}
  %es : {Bool.and(Bool.not(Bool.xor(nr1, _)), True{}) == True{} : Bool}
  %Equal.sym(Bool, Bool.not(Bool.xor(nr1, ns1)), True{}, ha) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

def agrees_plain(+tr1: String, +nr1: Bool, +ts1: String, +ns1: Bool, +tr2: String, +nr2: Bool, +ts2: String, +ns2: Bool, er: {nr1 == nr2 : Bool}, es: {ns1 == ns2 : Bool}, et: {tr1 == tr2 : String}, eu: {ts1 == ts2 : String}, ha: {Bool.and(Bool.not(Bool.xor(nr1, ns1)), T.same(tr1, ts1)) == True{} : Bool}) -> {Bool.and(Bool.not(Bool.xor(nr2, ns2)), T.same(tr2, ts2)) == True{} : Bool}:
  %er : {Bool.and(Bool.not(Bool.xor(_, ns2)), T.same(tr2, ts2)) == True{} : Bool}
  %es : {Bool.and(Bool.not(Bool.xor(nr1, _)), T.same(tr2, ts2)) == True{} : Bool}
  %et : {Bool.and(Bool.not(Bool.xor(nr1, ns1)), T.same(_, ts2)) == True{} : Bool}
  %eu : {Bool.and(Bool.not(Bool.xor(nr1, ns1)), T.same(tr1, _)) == True{} : Bool}
  ha

def agrees_fields(fr2: Bool, fs2: Bool, fr1: Bool, fs1: Bool, +tr1: String, +nr1: Bool, +tr2: String, +nr2: Bool, +ts1: String, +ns1: Bool, +ts2: String, +ns2: Bool, +hr: {Stand.item.like(Ops.Item{tr1, nr1, fr1}, Ops.Item{tr2, nr2, fr2}) == True{} : Bool}, +hs: {Stand.item.like(Ops.Item{ts1, ns1, fs1}, Ops.Item{ts2, ns2, fs2}) == True{} : Bool}, +ha: {Ops.agrees(Ops.Item{tr1, nr1, fr1}, Ops.Item{ts1, ns1, fs1}) == True{} : Bool}) -> {Ops.agrees(Ops.Item{tr2, nr2, fr2}, Ops.Item{ts2, ns2, fs2}) == True{} : Bool}:
  match fr2 fs2 fr1 fs1:
    case True{} _ _ _:
      agrees_term(nr1, ns1, nr2, ns2, like_term(tr1, nr1, fr1, tr2, nr2, True{}, hr), like_term(ts1, ns1, fs1, ts2, ns2, fs2, hs), Comp.and_left(Bool.not(Bool.xor(nr1, ns1)), Bool.or(Bool.or(fr1, fs1), T.same(tr1, ts1)), ha))
    case False{} True{} _ _:
      agrees_term(nr1, ns1, nr2, ns2, like_term(tr1, nr1, fr1, tr2, nr2, False{}, hr), like_term(ts1, ns1, fs1, ts2, ns2, True{}, hs), Comp.and_left(Bool.not(Bool.xor(nr1, ns1)), Bool.or(Bool.or(fr1, fs1), T.same(tr1, ts1)), ha))
    case False{} False{} True{} _:
      Empty.absurd({Ops.agrees(Ops.Item{tr2, nr2, False{}}, Ops.Item{ts2, ns2, False{}}) == True{} : Bool}, S.false_true(hr))
    case False{} False{} False{} True{}:
      Empty.absurd({Ops.agrees(Ops.Item{tr2, nr2, False{}}, Ops.Item{ts2, ns2, False{}}) == True{} : Bool}, S.false_true(hs))
    case False{} False{} False{} False{}:
      agrees_plain(tr1, nr1, ts1, ns1, tr2, nr2, ts2, ns2,
        like_term(tr1, nr1, False{}, tr2, nr2, False{}, hr), like_term(ts1, ns1, False{}, ts2, ns2, False{}, hs),
        Eq.same_eq(tr1, tr2, Comp.and_left(T.same(tr1, tr2), Bool.not(Bool.xor(nr1, nr2)), hr)),
        Eq.same_eq(ts1, ts2, Comp.and_left(T.same(ts1, ts2), Bool.not(Bool.xor(ns1, ns2)), hs)),
        ha)

def agrees_imp(a: Bool, -b: Bool, -ea: {a == a : Bool}, f: {a == True{} : Bool} -> {b == True{} : Bool}) -> {imp(a, b) == True{} : Bool}:
  match a:
    case True{}:
      f({==})
    case False{}:
      {==}

# A quote a delete makes agrees, through stand-ins, wherever it agreed.
def agrees_like(r1: Ops.Item, r2: Ops.Item, s1: Ops.Item, s2: Ops.Item, +hr: {Stand.item.like(r1, r2) == True{} : Bool}, +hs: {Stand.item.like(s1, s2) == True{} : Bool}) -> {imp(Ops.agrees(r1, s1), Ops.agrees(r2, s2)) == True{} : Bool}:
  match r1 r2 s1 s2:
    case Ops.Item{+tr1, +nr1, +fr1} Ops.Item{+tr2, +nr2, +fr2} Ops.Item{+ts1, +ns1, +fs1} Ops.Item{+ts2, +ns2, +fs2}:
      agrees_imp(Ops.agrees(Ops.Item{tr1, nr1, fr1}, Ops.Item{ts1, ns1, fs1}), Ops.agrees(Ops.Item{tr2, nr2, fr2}, Ops.Item{ts2, ns2, fs2}), {==}, h => agrees_fields(fr2, fs2, fr1, fs1, tr1, nr1, tr2, nr2, ts1, ns1, ts2, ns2, hr, hs, h))

def imp_and(a1: Bool, b1: Bool, a2: Bool, b2: Bool, ha: {imp(a1, a2) == True{} : Bool}, hb: {imp(b1, b2) == True{} : Bool}) -> {imp(Bool.and(a1, b1), Bool.and(a2, b2)) == True{} : Bool}:
  match a1 b1:
    case False{} _:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      match a2 b2:
        case True{} True{}:
          {==}
        case False{} _:
          Empty.absurd({imp(True{}, Bool.and(False{}, b2)) == True{} : Bool}, S.false_true(ha))
        case True{} False{}:
          Empty.absurd({imp(True{}, False{}) == True{} : Bool}, S.false_true(hb))

def dropped.like(a: Ops.Dropped, b: Ops.Dropped) -> Bool:
  match a b:
    case Ops.Dropped{r1, g1} Ops.Dropped{r2, g2}:
      Bool.and(Stand.items.like(r1, r2), imp(g1, g2))

# A deleted run is dropped alike, and agrees through stand-ins wherever it
# agreed.
def drop_like(rec1: List<&2, Ops.Item>, rec2: List<&2, Ops.Item>, st1: List<&2, Ops.Item>, st2: List<&2, Ops.Item>, +ok1: Bool, +ok2: Bool, +hrec: {Stand.items.like(rec1, rec2) == True{} : Bool}, +hst: {Stand.items.like(st1, st2) == True{} : Bool}, +hok: {imp(ok1, ok2) == True{} : Bool}) -> {dropped.like(Ops.drop_checked(rec1, st1, ok1), Ops.drop_checked(rec2, st2, ok2)) == True{} : Bool}:
  match rec1 rec2 st1 st2:
    case Nil{} Nil{} +s1 +s2:
      AL.and_intro(Stand.items.like(s1, s2), imp(ok1, ok2), hst, hok)
    case Nil{} y <> ys s1 s2:
      Empty.absurd({dropped.like(Ops.drop_checked(Nil{}, s1, ok1), Ops.drop_checked(y <> ys, s2, ok2)) == True{} : Bool}, S.false_true(hrec))
    case x <> xs Nil{} s1 s2:
      Empty.absurd({dropped.like(Ops.drop_checked(x <> xs, s1, ok1), Ops.drop_checked(Nil{}, s2, ok2)) == True{} : Bool}, S.false_true(hrec))
    case x <> xs y <> ys Nil{} Nil{}:
      {==}
    case x <> xs y <> ys Nil{} s <> ss:
      Empty.absurd({dropped.like(Ops.drop_checked(x <> xs, Nil{}, ok1), Ops.drop_checked(y <> ys, s <> ss, ok2)) == True{} : Bool}, S.false_true(hst))
    case x <> xs y <> ys s <> ss Nil{}:
      Empty.absurd({dropped.like(Ops.drop_checked(x <> xs, s <> ss, ok1), Ops.drop_checked(y <> ys, Nil{}, ok2)) == True{} : Bool}, S.false_true(hst))
    case +x <> +xs +y <> +ys +s <> +ss +t <> +ts:
      drop_like(xs, ys, ss, ts, Bool.and(ok1, Ops.agrees(x, s)), Bool.and(ok2, Ops.agrees(y, t)),
        Comp.and_right(Stand.item.like(x, y), Stand.items.like(xs, ys), hrec),
        Comp.and_right(Stand.item.like(s, t), Stand.items.like(ss, ts), hst),
        imp_and(ok1, Ops.agrees(x, s), ok2, Ops.agrees(y, t), hok, agrees_like(x, y, s, t, Comp.and_left(Stand.item.like(x, y), Stand.items.like(xs, ys), hrec), Comp.and_left(Stand.item.like(s, t), Stand.items.like(ss, ts), hst))))

def advanced.like(a: Ops.Advanced, b: Ops.Advanced) -> Bool:
  match a b:
    case Ops.Advanced{a1, r1} Ops.Advanced{a2, r2}:
      Bool.and(Stand.items.like(a1, a2), Stand.items.like(r1, r2))

# The walk moves alike over alike states.
def advance_like(n: Nat, st1: List<&2, Ops.Item>, st2: List<&2, Ops.Item>, +acc1: List<&2, Ops.Item>, +acc2: List<&2, Ops.Item>, +hst: {Stand.items.like(st1, st2) == True{} : Bool}, +hacc: {Stand.items.like(acc1, acc2) == True{} : Bool}) -> {advanced.like(Ops.advance(n, st1, acc1), Ops.advance(n, st2, acc2)) == True{} : Bool}:
  match n st1 st2:
    case 0n +s1 +s2:
      AL.and_intro(Stand.items.like(acc1, acc2), Stand.items.like(s1, s2), hacc, hst)
    case 1n+p Nil{} Nil{}:
      AL.and_intro(Stand.items.like(acc1, acc2), True{}, hacc, {==})
    case 1n+p Nil{} y <> ys:
      Empty.absurd({advanced.like(Ops.advance(1n+p, Nil{}, acc1), Ops.advance(1n+p, y <> ys, acc2)) == True{} : Bool}, S.false_true(hst))
    case 1n+p x <> xs Nil{}:
      Empty.absurd({advanced.like(Ops.advance(1n+p, x <> xs, acc1), Ops.advance(1n+p, Nil{}, acc2)) == True{} : Bool}, S.false_true(hst))
    case 1n+p +x <> +xs +y <> +ys:
      advance_like(p, xs, ys, x <> acc1, y <> acc2,
        Comp.and_right(Stand.item.like(x, y), Stand.items.like(xs, ys), hst),
        AL.and_intro(Stand.item.like(x, y), Stand.items.like(acc1, acc2), Comp.and_left(Stand.item.like(x, y), Stand.items.like(xs, ys), hst), hacc))

def landed.like(a: Ops.Landed, b: Ops.Landed) -> Bool:
  match a b:
    case Ops.Landed{a1, s1, g1} Ops.Landed{a2, s2, g2}:
      Bool.and(Stand.items.like(a1, a2), Bool.and(Stand.items.like(s1, s2), imp(g1, g2)))

def ins_like(v1: Ops.Advanced, v2: Ops.Advanced, +h: {advanced.like(v1, v2) == True{} : Bool}) -> {landed.like(Ops.land.insert(v1), Ops.land.insert(v2)) == True{} : Bool}:
  match v1 v2:
    case Ops.Advanced{+a1, +s1} Ops.Advanced{+a2, +s2}:
      AL.and_intro(Stand.items.like(a1, a2), Bool.and(Stand.items.like(s1, s2), True{}),
        Comp.and_left(Stand.items.like(a1, a2), Stand.items.like(s1, s2), h),
        AL.and_intro(Stand.items.like(s1, s2), True{}, Comp.and_right(Stand.items.like(a1, a2), Stand.items.like(s1, s2), h), {==}))

def dropped_landed(+a1: List<&2, Ops.Item>, +a2: List<&2, Ops.Item>, d1: Ops.Dropped, d2: Ops.Dropped, +ha: {Stand.items.like(a1, a2) == True{} : Bool}, h: {dropped.like(d1, d2) == True{} : Bool}) -> {landed.like(Ops.land.dropped(a1, d1), Ops.land.dropped(a2, d2)) == True{} : Bool}:
  match d1 d2:
    case Ops.Dropped{+r1, +g1} Ops.Dropped{+r2, +g2}:
      AL.and_intro(Stand.items.like(a1, a2), Bool.and(Stand.items.like(r1, r2), imp(g1, g2)), ha, h)

def del_like(+i1: List<&2, Ops.Item>, +i2: List<&2, Ops.Item>, v1: Ops.Advanced, v2: Ops.Advanced, +hi: {Stand.items.like(i1, i2) == True{} : Bool}, +h: {advanced.like(v1, v2) == True{} : Bool}) -> {landed.like(Ops.land.delete(i1, v1), Ops.land.delete(i2, v2)) == True{} : Bool}:
  match v1 v2:
    case Ops.Advanced{+a1, +s1} Ops.Advanced{+a2, +s2}:
      dropped_landed(a1, a2, Ops.drop_checked(i1, s1, True{}), Ops.drop_checked(i2, s2, True{}),
        Comp.and_left(Stand.items.like(a1, a2), Stand.items.like(s1, s2), h),
        drop_like(i1, i2, s1, s2, True{}, True{}, hi, Comp.and_right(Stand.items.like(a1, a2), Stand.items.like(s1, s2), h), {==}))

# The walk lands alike on the next operation of two alike documents.
def land_like(ops1: List<&2, Ops.Op>, ops2: List<&2, Ops.Op>, +pos: Nat, +st1: List<&2, Ops.Item>, +st2: List<&2, Ops.Item>, +acc1: List<&2, Ops.Item>, +acc2: List<&2, Ops.Item>, +hops: {Stand.ops.like(ops1, ops2) == True{} : Bool}, +hst: {Stand.items.like(st1, st2) == True{} : Bool}, +hacc: {Stand.items.like(acc1, acc2) == True{} : Bool}) -> {landed.like(Ops.land(ops1, pos, st1, acc1), Ops.land(ops2, pos, st2, acc2)) == True{} : Bool}:
  match ops1 ops2:
    case Nil{} Nil{}:
      AL.and_intro(Stand.items.like(acc1, acc2), Bool.and(Stand.items.like(st1, st2), True{}), hacc, AL.and_intro(Stand.items.like(st1, st2), True{}, hst, {==}))
    case Nil{} Ops.Op{k, a, i} <> os:
      Empty.absurd({landed.like(Ops.land(Nil{}, pos, st1, acc1), Ops.land(Ops.Op{k, a, i} <> os, pos, st2, acc2)) == True{} : Bool}, S.false_true(hops))
    case Ops.Op{k, a, i} <> os Nil{}:
      Empty.absurd({landed.like(Ops.land(Ops.Op{k, a, i} <> os, pos, st1, acc1), Ops.land(Nil{}, pos, st2, acc2)) == True{} : Bool}, S.false_true(hops))
    case Ops.Op{Ops.Insert{}, +at1, +i1} <> +ra Ops.Op{Ops.Insert{}, +at2, +i2} <> +rb:
      +eq = Comp.eq_of_is_eq(at1, at2, Comp.and_left(Nat.is_eq(at1, at2), Bool.and(Stand.items.like(i1, i2), Stand.ops.like(ra, rb)), hops))
      %eq : {landed.like(Ops.land.insert(Ops.advance(Nat.sub(at1, pos), st1, acc1)), Ops.land.insert(Ops.advance(Nat.sub(_, pos), st2, acc2))) == True{} : Bool}
      ins_like(Ops.advance(Nat.sub(at1, pos), st1, acc1), Ops.advance(Nat.sub(at1, pos), st2, acc2), advance_like(Nat.sub(at1, pos), st1, st2, acc1, acc2, hst, hacc))
    case Ops.Op{Ops.Delete{}, +at1, +i1} <> +ra Ops.Op{Ops.Delete{}, +at2, +i2} <> +rb:
      +eq = Comp.eq_of_is_eq(at1, at2, Comp.and_left(Nat.is_eq(at1, at2), Bool.and(Stand.items.like(i1, i2), Stand.ops.like(ra, rb)), hops))
      %eq : {landed.like(Ops.land.delete(i1, Ops.advance(Nat.sub(at1, pos), st1, acc1)), Ops.land.delete(i2, Ops.advance(Nat.sub(_, pos), st2, acc2))) == True{} : Bool}
      del_like(i1, i2, Ops.advance(Nat.sub(at1, pos), st1, acc1), Ops.advance(Nat.sub(at1, pos), st2, acc2),
        Comp.and_left(Stand.items.like(i1, i2), Stand.ops.like(ra, rb), Comp.and_right(Nat.is_eq(at1, at2), Bool.and(Stand.items.like(i1, i2), Stand.ops.like(ra, rb)), hops)),
        advance_like(Nat.sub(at1, pos), st1, st2, acc1, acc2, hst, hacc))
    case Ops.Op{Ops.Insert{}, at1, i1} <> ra Ops.Op{Ops.Delete{}, at2, i2} <> rb:
      Empty.absurd({landed.like(Ops.land(Ops.Op{Ops.Insert{}, at1, i1} <> ra, pos, st1, acc1), Ops.land(Ops.Op{Ops.Delete{}, at2, i2} <> rb, pos, st2, acc2)) == True{} : Bool}, S.false_true(hops))
    case Ops.Op{Ops.Delete{}, at1, i1} <> ra Ops.Op{Ops.Insert{}, at2, i2} <> rb:
      Empty.absurd({landed.like(Ops.land(Ops.Op{Ops.Delete{}, at1, i1} <> ra, pos, st1, acc1), Ops.land(Ops.Op{Ops.Insert{}, at2, i2} <> rb, pos, st2, acc2)) == True{} : Bool}, S.false_true(hops))

def rev_like(xs: List<&2, Ops.Item>, ys: List<&2, Ops.Item>, +acc1: List<&2, Ops.Item>, +acc2: List<&2, Ops.Item>, +hx: {Stand.items.like(xs, ys) == True{} : Bool}, +ha: {Stand.items.like(acc1, acc2) == True{} : Bool}) -> {Stand.items.like(List.reverse.go(&2, Ops.Item, xs, acc1), List.reverse.go(&2, Ops.Item, ys, acc2)) == True{} : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      ha
    case Nil{} y <> yr:
      Empty.absurd({Stand.items.like(acc1, List.reverse.go(&2, Ops.Item, y <> yr, acc2)) == True{} : Bool}, S.false_true(hx))
    case x <> xr Nil{}:
      Empty.absurd({Stand.items.like(List.reverse.go(&2, Ops.Item, x <> xr, acc1), acc2) == True{} : Bool}, S.false_true(hx))
    case +x <> +xr +y <> +yr:
      rev_like(xr, yr, x <> acc1, y <> acc2, Comp.and_right(Stand.item.like(x, y), Stand.items.like(xr, yr), hx),
        AL.and_intro(Stand.item.like(x, y), Stand.items.like(acc1, acc2), Comp.and_left(Stand.item.like(x, y), Stand.items.like(xr, yr), hx), ha))

def app_like(xs: List<&2, Ops.Item>, ys: List<&2, Ops.Item>, +zs: List<&2, Ops.Item>, +ws: List<&2, Ops.Item>, +hx: {Stand.items.like(xs, ys) == True{} : Bool}, +hz: {Stand.items.like(zs, ws) == True{} : Bool}) -> {Stand.items.like(List.append(&2, Ops.Item, xs, zs), List.append(&2, Ops.Item, ys, ws)) == True{} : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      hz
    case Nil{} y <> yr:
      Empty.absurd({Stand.items.like(zs, List.append(&2, Ops.Item, y <> yr, ws)) == True{} : Bool}, S.false_true(hx))
    case x <> xr Nil{}:
      Empty.absurd({Stand.items.like(List.append(&2, Ops.Item, x <> xr, zs), ws) == True{} : Bool}, S.false_true(hx))
    case +x <> +xr +y <> +yr:
      AL.and_intro(Stand.item.like(x, y), Stand.items.like(List.append(&2, Ops.Item, xr, zs), List.append(&2, Ops.Item, yr, ws)),
        Comp.and_left(Stand.item.like(x, y), Stand.items.like(xr, yr), hx),
        app_like(xr, yr, zs, ws, Comp.and_right(Stand.item.like(x, y), Stand.items.like(xr, yr), hx), hz))

def like_len(xs: List<&2, Ops.Item>, ys: List<&2, Ops.Item>, +h: {Stand.items.like(xs, ys) == True{} : Bool}) -> {List.length(&2, Ops.Item, xs) == List.length(&2, Ops.Item, ys) : Nat}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yr:
      Empty.absurd({0n == List.length(&2, Ops.Item, y <> yr) : Nat}, S.false_true(h))
    case x <> xr Nil{}:
      Empty.absurd({List.length(&2, Ops.Item, x <> xr) == 0n : Nat}, S.false_true(h))
    case +x <> +xr +y <> +yr:
      +e = like_len(xr, yr, Comp.and_right(Stand.item.like(x, y), Stand.items.like(xr, yr), h))
      %e : {1n+List.length(&2, Ops.Item, xr) == 1n+_ : Nat}
      {==}

def none_of(m: Maybe<&2, String>) -> Bool:
  Maybe.is_none(&2, String, m)

# A delete that agreed adds no error the original did not have.
def err_step(err1: Maybe<&2, String>, err2: Maybe<&2, String>, g1: Bool, g2: Bool, -m1: String, -m2: String, he: {imp(none_of(err1), none_of(err2)) == True{} : Bool}, hg: {imp(g1, g2) == True{} : Bool}) -> {imp(none_of(Maybe.or(&2, String, err1, Bool.pick(Maybe<&2, String>, g1, None{}, Some{m1}))), none_of(Maybe.or(&2, String, err2, Bool.pick(Maybe<&2, String>, g2, None{}, Some{m2})))) == True{} : Bool}:
  match err1 err2 g1 g2:
    case Some{x} _ _ _:
      {==}
    case None{} Some{y} _ _:
      Empty.absurd({imp(none_of(Bool.pick(Maybe<&2, String>, g1, None{}, Some{m1})), none_of(Maybe.or(&2, String, Some{y}, Bool.pick(Maybe<&2, String>, g2, None{}, Some{m2})))) == True{} : Bool}, S.false_true(he))
    case None{} None{} False{} _:
      {==}
    case None{} None{} True{} True{}:
      {==}
    case None{} None{} True{} False{}:
      Empty.absurd({imp(True{}, False{}) == True{} : Bool}, S.false_true(hg))

def go_end(+a1: List<&2, Ops.Item>, +s1: List<&2, Ops.Item>, -g1: Bool, +a2: List<&2, Ops.Item>, +s2: List<&2, Ops.Item>, -g2: Bool, -pos: Nat, err1: Maybe<&2, String>, err2: Maybe<&2, String>, ha: {Stand.items.like(a1, a2) == True{} : Bool}, hs: {Stand.items.like(s1, s2) == True{} : Bool}, he: {imp(none_of(err1), none_of(err2)) == True{} : Bool}) -> {Stand.result.like(Ops.apply.go(Nil{}, Ops.Landed{a1, s1, g1}, pos, err1), Ops.apply.go(Nil{}, Ops.Landed{a2, s2, g2}, pos, err2)) == True{} : Bool}:
  match err1 err2:
    case Some{x} _:
      {==}
    case None{} Some{y}:
      Empty.absurd({Stand.result.like(Ops.apply.go(Nil{}, Ops.Landed{a1, s1, g1}, pos, None{}), Ops.apply.go(Nil{}, Ops.Landed{a2, s2, g2}, pos, Some{y})) == True{} : Bool}, S.false_true(he))
    case None{} None{}:
      app_like(List.reverse(&2, Ops.Item, a1), List.reverse(&2, Ops.Item, a2), s1, s2, rev_like(a1, a2, Nil{}, Nil{}, ha, {==}), hs)

def landed.acc(l: Ops.Landed) -> List<&2, Ops.Item>:
  match l:
    case Ops.Landed{a, s, g}:
      a

# Two alike documents walked from alike landings, the second's errors no
# more than the first's, make alike files wherever the first makes one.
def go_like(ops1: List<&2, Ops.Op>, ops2: List<&2, Ops.Op>, l1: Ops.Landed, l2: Ops.Landed, +pos: Nat, +err1: Maybe<&2, String>, +err2: Maybe<&2, String>, +hops: {Stand.ops.like(ops1, ops2) == True{} : Bool}, +hl: {landed.like(l1, l2) == True{} : Bool}, +he: {imp(none_of(err1), none_of(err2)) == True{} : Bool}) -> {Stand.result.like(Ops.apply.go(ops1, l1, pos, err1), Ops.apply.go(ops2, l2, pos, err2)) == True{} : Bool}:
  match ops1 ops2 l1 l2:
    case Nil{} Nil{} Ops.Landed{+a1, +s1, g1} Ops.Landed{+a2, +s2, g2}:
      go_end(a1, s1, g1, a2, s2, g2, pos, err1, err2,
        Comp.and_left(Stand.items.like(a1, a2), Bool.and(Stand.items.like(s1, s2), imp(g1, g2)), hl),
        Comp.and_left(Stand.items.like(s1, s2), imp(g1, g2), Comp.and_right(Stand.items.like(a1, a2), Bool.and(Stand.items.like(s1, s2), imp(g1, g2)), hl)),
        he)
    case Nil{} Ops.Op{k, a, i} <> os x y:
      Empty.absurd({Stand.result.like(Ops.apply.go(Nil{}, x, pos, err1), Ops.apply.go(Ops.Op{k, a, i} <> os, y, pos, err2)) == True{} : Bool}, S.false_true(hops))
    case Ops.Op{k, a, i} <> os Nil{} x y:
      Empty.absurd({Stand.result.like(Ops.apply.go(Ops.Op{k, a, i} <> os, x, pos, err1), Ops.apply.go(Nil{}, y, pos, err2)) == True{} : Bool}, S.false_true(hops))
    case Ops.Op{Ops.Insert{}, +at1, +i1} <> +ra Ops.Op{Ops.Insert{}, +at2, +i2} <> +rb Ops.Landed{+a1, +s1, +g1} Ops.Landed{+a2, +s2, +g2}:
      +eq = Comp.eq_of_is_eq(at1, at2, Comp.and_left(Nat.is_eq(at1, at2), Bool.and(Stand.items.like(i1, i2), Stand.ops.like(ra, rb)), hops))
      +hi = Comp.and_left(Stand.items.like(i1, i2), Stand.ops.like(ra, rb), Comp.and_right(Nat.is_eq(at1, at2), Bool.and(Stand.items.like(i1, i2), Stand.ops.like(ra, rb)), hops))
      +hr = Comp.and_right(Stand.items.like(i1, i2), Stand.ops.like(ra, rb), Comp.and_right(Nat.is_eq(at1, at2), Bool.and(Stand.items.like(i1, i2), Stand.ops.like(ra, rb)), hops))
      +ha = Comp.and_left(Stand.items.like(a1, a2), Bool.and(Stand.items.like(s1, s2), imp(g1, g2)), hl)
      +hs = Comp.and_left(Stand.items.like(s1, s2), imp(g1, g2), Comp.and_right(Stand.items.like(a1, a2), Bool.and(Stand.items.like(s1, s2), imp(g1, g2)), hl))
      %eq : {Stand.result.like(Ops.apply.go(ra, Ops.land(ra, Nat.max(pos, at1), s1, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, i1), a1)), Nat.max(pos, at1), err1), Ops.apply.go(rb, Ops.land(rb, Nat.max(pos, _), s2, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, i2), a2)), Nat.max(pos, _), err2)) == True{} : Bool}
      go_like(ra, rb, Ops.land(ra, Nat.max(pos, at1), s1, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, i1), a1)), Ops.land(rb, Nat.max(pos, at1), s2, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, i2), a2)), Nat.max(pos, at1), err1, err2, hr,
        land_like(ra, rb, Nat.max(pos, at1), s1, s2, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, i1), a1), List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, i2), a2), hr, hs,
          app_like(List.reverse(&2, Ops.Item, i1), List.reverse(&2, Ops.Item, i2), a1, a2, rev_like(i1, i2, Nil{}, Nil{}, hi, {==}), ha)),
        he)
    case Ops.Op{Ops.Delete{}, +at1, +i1} <> +ra Ops.Op{Ops.Delete{}, +at2, +i2} <> +rb Ops.Landed{+a1, +s1, +g1} Ops.Landed{+a2, +s2, +g2}:
      +eq = Comp.eq_of_is_eq(at1, at2, Comp.and_left(Nat.is_eq(at1, at2), Bool.and(Stand.items.like(i1, i2), Stand.ops.like(ra, rb)), hops))
      +hi = Comp.and_left(Stand.items.like(i1, i2), Stand.ops.like(ra, rb), Comp.and_right(Nat.is_eq(at1, at2), Bool.and(Stand.items.like(i1, i2), Stand.ops.like(ra, rb)), hops))
      +hr = Comp.and_right(Stand.items.like(i1, i2), Stand.ops.like(ra, rb), Comp.and_right(Nat.is_eq(at1, at2), Bool.and(Stand.items.like(i1, i2), Stand.ops.like(ra, rb)), hops))
      +ha = Comp.and_left(Stand.items.like(a1, a2), Bool.and(Stand.items.like(s1, s2), imp(g1, g2)), hl)
      +hs = Comp.and_left(Stand.items.like(s1, s2), imp(g1, g2), Comp.and_right(Stand.items.like(a1, a2), Bool.and(Stand.items.like(s1, s2), imp(g1, g2)), hl))
      +hg = Comp.and_right(Stand.items.like(s1, s2), imp(g1, g2), Comp.and_right(Stand.items.like(a1, a2), Bool.and(Stand.items.like(s1, s2), imp(g1, g2)), hl))
      +en = like_len(i1, i2, hi)
      +p2 = Nat.add(at1, List.length(&2, Ops.Item, i1))
      %eq : {Stand.result.like(Ops.apply.go(ra, Ops.land(ra, p2, s1, a1), p2, Maybe.or(&2, String, err1, Bool.pick(Maybe<&2, String>, g1, None{}, Some{"a delete at " ++ Nat.show(at1) ++ " quotes lines the parent does not hold"}))), Ops.apply.go(rb, Ops.land(rb, Nat.add(_, List.length(&2, Ops.Item, i2)), s2, a2), Nat.add(_, List.length(&2, Ops.Item, i2)), Maybe.or(&2, String, err2, Bool.pick(Maybe<&2, String>, g2, None{}, Some{"a delete at " ++ Nat.show(_) ++ " quotes lines the parent does not hold"})))) == True{} : Bool}
      %en : {Stand.result.like(Ops.apply.go(ra, Ops.land(ra, p2, s1, a1), p2, Maybe.or(&2, String, err1, Bool.pick(Maybe<&2, String>, g1, None{}, Some{"a delete at " ++ Nat.show(at1) ++ " quotes lines the parent does not hold"}))), Ops.apply.go(rb, Ops.land(rb, Nat.add(at1, _), s2, a2), Nat.add(at1, _), Maybe.or(&2, String, err2, Bool.pick(Maybe<&2, String>, g2, None{}, Some{"a delete at " ++ Nat.show(at1) ++ " quotes lines the parent does not hold"})))) == True{} : Bool}
      go_like(ra, rb, Ops.land(ra, p2, s1, a1), Ops.land(rb, p2, s2, a2), p2,
        Maybe.or(&2, String, err1, Bool.pick(Maybe<&2, String>, g1, None{}, Some{"a delete at " ++ Nat.show(at1) ++ " quotes lines the parent does not hold"})),
        Maybe.or(&2, String, err2, Bool.pick(Maybe<&2, String>, g2, None{}, Some{"a delete at " ++ Nat.show(at1) ++ " quotes lines the parent does not hold"})),
        hr, land_like(ra, rb, p2, s1, s2, a1, a2, hr, hs, ha),
        err_step(err1, err2, g1, g2, "a delete at " ++ Nat.show(at1) ++ " quotes lines the parent does not hold", "a delete at " ++ Nat.show(at1) ++ " quotes lines the parent does not hold", he, hg))
    case Ops.Op{Ops.Insert{}, at1, i1} <> ra Ops.Op{Ops.Delete{}, at2, i2} <> rb x y:
      Empty.absurd({Stand.result.like(Ops.apply.go(Ops.Op{Ops.Insert{}, at1, i1} <> ra, x, pos, err1), Ops.apply.go(Ops.Op{Ops.Delete{}, at2, i2} <> rb, y, pos, err2)) == True{} : Bool}, S.false_true(hops))
    case Ops.Op{Ops.Delete{}, at1, i1} <> ra Ops.Op{Ops.Insert{}, at2, i2} <> rb x y:
      Empty.absurd({Stand.result.like(Ops.apply.go(Ops.Op{Ops.Delete{}, at1, i1} <> ra, x, pos, err1), Ops.apply.go(Ops.Op{Ops.Insert{}, at2, i2} <> rb, y, pos, err2)) == True{} : Bool}, S.false_true(hops))

def tbl_like(xs: List<&2, Ops.Item>, ys: List<&2, Ops.Item>, +h: {Stand.items.like(xs, ys) == True{} : Bool}) -> {Ops.terminated_but_last(xs) == Ops.terminated_but_last(ys) : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yr:
      Empty.absurd({True{} == Ops.terminated_but_last(y <> yr) : Bool}, S.false_true(h))
    case x <> xr Nil{}:
      Empty.absurd({Ops.terminated_but_last(x <> xr) == True{} : Bool}, S.false_true(h))
    case Ops.Item{t1, n1, f1} <> Nil{} Ops.Item{t2, n2, f2} <> Nil{}:
      {==}
    case Ops.Item{+t1, +n1, +f1} <> Nil{} Ops.Item{+t2, +n2, +f2} <> +y2 <> +yr:
      Empty.absurd({True{} == Ops.terminated_but_last(Ops.Item{t2, n2, f2} <> y2 <> yr) : Bool}, S.false_true(Comp.and_right(Stand.item.like(Ops.Item{t1, n1, f1}, Ops.Item{t2, n2, f2}), Stand.items.like(Nil{}, y2 <> yr), h)))
    case Ops.Item{+t1, +n1, +f1} <> +x2 <> +xr Ops.Item{+t2, +n2, +f2} <> Nil{}:
      Empty.absurd({Ops.terminated_but_last(Ops.Item{t1, n1, f1} <> x2 <> xr) == True{} : Bool}, S.false_true(Comp.and_right(Stand.item.like(Ops.Item{t1, n1, f1}, Ops.Item{t2, n2, f2}), Stand.items.like(x2 <> xr, Nil{}), h)))
    case Ops.Item{+t1, +n1, +f1} <> +x2 <> +xr Ops.Item{+t2, +n2, +f2} <> +y2 <> +yr:
      +en = like_term(t1, n1, f1, t2, n2, f2, Comp.and_left(Stand.item.like(Ops.Item{t1, n1, f1}, Ops.Item{t2, n2, f2}), Stand.items.like(x2 <> xr, y2 <> yr), h))
      +er = tbl_like(x2 <> xr, y2 <> yr, Comp.and_right(Stand.item.like(Ops.Item{t1, n1, f1}, Ops.Item{t2, n2, f2}), Stand.items.like(x2 <> xr, y2 <> yr), h))
      %en : {Bool.and(n1, Ops.terminated_but_last(x2 <> xr)) == Bool.and(_, Ops.terminated_but_last(y2 <> yr)) : Bool}
      %er : {Bool.and(n1, Ops.terminated_but_last(x2 <> xr)) == Bool.and(n1, _) : Bool}
      {==}

def after_like(+xs: List<&2, Ops.Item>, +ys: List<&2, Ops.Item>, tb1: Bool, tb2: Bool, dig: Result<&2, &2, String, Unit>, +h: {Stand.items.like(xs, ys) == True{} : Bool}, etb: {tb1 == tb2 : Bool}) -> {Stand.result.like(Diff.after_checks(xs, tb1, dig), Diff.after_checks(ys, tb2, Done{Unit{}})) == True{} : Bool}:
  match tb1 dig:
    case False{} d:
      {==}
    case True{} Fail{e}:
      {==}
    case True{} Done{u}:
      %etb : {Stand.result.like(Done{xs}, Diff.after_checks(ys, _, Done{Unit{}})) == True{} : Bool}
      h

# What the replay checks of the file it makes: a stand-in states no result,
# and its file ends where the original's does.
def checked_like(+r: Maybe<&2, String>, +xs: List<&2, Ops.Item>, +ys: List<&2, Ops.Item>, +h: {Stand.items.like(xs, ys) == True{} : Bool}) -> {Stand.result.like(Ops.apply.checked(r, xs), Ops.apply.checked(None{}, ys)) == True{} : Bool}:
  %Refuse.checked_is(xs, r) : {Stand.result.like(_, Ops.apply.checked(None{}, ys)) == True{} : Bool}
  %Refuse.checked_is(ys, None{}) : {Stand.result.like(Diff.after_checks(xs, Ops.terminated_but_last(xs), Ops.check_result(r, xs)), _) == True{} : Bool}
  after_like(xs, ys, Ops.terminated_but_last(xs), Ops.terminated_but_last(ys), Ops.check_result(r, xs), h, tbl_like(xs, ys, h))

# The range check reads positions and counts, which a stand-in keeps.
def range_like(ops1: List<&2, Ops.Op>, ops2: List<&2, Ops.Op>, +n: Nat, +h: {Stand.ops.like(ops1, ops2) == True{} : Bool}) -> {Ops.in_range(ops1, n) == Ops.in_range(ops2, n) : Bool}:
  match ops1 ops2:
    case Nil{} Nil{}:
      {==}
    case Nil{} Ops.Op{k, a, i} <> os:
      Empty.absurd({True{} == Ops.in_range(Ops.Op{k, a, i} <> os, n) : Bool}, S.false_true(h))
    case Ops.Op{k, a, i} <> os Nil{}:
      Empty.absurd({Ops.in_range(Ops.Op{k, a, i} <> os, n) == True{} : Bool}, S.false_true(h))
    case Ops.Op{Ops.Insert{}, +at1, +i1} <> +ra Ops.Op{Ops.Insert{}, +at2, +i2} <> +rb:
      +eq = Comp.eq_of_is_eq(at1, at2, Comp.and_left(Nat.is_eq(at1, at2), Bool.and(Stand.items.like(i1, i2), Stand.ops.like(ra, rb)), h))
      +er = range_like(ra, rb, n, Comp.and_right(Stand.items.like(i1, i2), Stand.ops.like(ra, rb), Comp.and_right(Nat.is_eq(at1, at2), Bool.and(Stand.items.like(i1, i2), Stand.ops.like(ra, rb)), h)))
      %eq : {Bool.and(Nat.is_le(at1, n), Ops.in_range(ra, n)) == Bool.and(Nat.is_le(_, n), Ops.in_range(rb, n)) : Bool}
      %er : {Bool.and(Nat.is_le(at1, n), Ops.in_range(ra, n)) == Bool.and(Nat.is_le(at1, n), _) : Bool}
      {==}
    case Ops.Op{Ops.Delete{}, +at1, +i1} <> +ra Ops.Op{Ops.Delete{}, +at2, +i2} <> +rb:
      +eq = Comp.eq_of_is_eq(at1, at2, Comp.and_left(Nat.is_eq(at1, at2), Bool.and(Stand.items.like(i1, i2), Stand.ops.like(ra, rb)), h))
      +el = like_len(i1, i2, Comp.and_left(Stand.items.like(i1, i2), Stand.ops.like(ra, rb), Comp.and_right(Nat.is_eq(at1, at2), Bool.and(Stand.items.like(i1, i2), Stand.ops.like(ra, rb)), h)))
      +er = range_like(ra, rb, n, Comp.and_right(Stand.items.like(i1, i2), Stand.ops.like(ra, rb), Comp.and_right(Nat.is_eq(at1, at2), Bool.and(Stand.items.like(i1, i2), Stand.ops.like(ra, rb)), h)))
      %eq : {Bool.and(Nat.is_le(Nat.add(at1, List.length(&2, Ops.Item, i1)), n), Ops.in_range(ra, n)) == Bool.and(Nat.is_le(Nat.add(_, List.length(&2, Ops.Item, i2)), n), Ops.in_range(rb, n)) : Bool}
      %el : {Bool.and(Nat.is_le(Nat.add(at1, List.length(&2, Ops.Item, i1)), n), Ops.in_range(ra, n)) == Bool.and(Nat.is_le(Nat.add(at1, _), n), Ops.in_range(rb, n)) : Bool}
      %er : {Bool.and(Nat.is_le(Nat.add(at1, List.length(&2, Ops.Item, i1)), n), Ops.in_range(ra, n)) == Bool.and(Nat.is_le(Nat.add(at1, List.length(&2, Ops.Item, i1)), n), _) : Bool}
      {==}
    case Ops.Op{Ops.Insert{}, at1, i1} <> ra Ops.Op{Ops.Delete{}, at2, i2} <> rb:
      Empty.absurd({Ops.in_range(Ops.Op{Ops.Insert{}, at1, i1} <> ra, n) == Ops.in_range(Ops.Op{Ops.Delete{}, at2, i2} <> rb, n) : Bool}, S.false_true(h))
    case Ops.Op{Ops.Delete{}, at1, i1} <> ra Ops.Op{Ops.Insert{}, at2, i2} <> rb:
      Empty.absurd({Ops.in_range(Ops.Op{Ops.Delete{}, at1, i1} <> ra, n) == Ops.in_range(Ops.Op{Ops.Insert{}, at2, i2} <> rb, n) : Bool}, S.false_true(h))

# `Ops.apply`, its range check named.
def after_range(+state: List<&2, Ops.Item>, result: Maybe<&2, String>, +ops: List<&2, Ops.Op>, ok: Bool) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  do Result<&2, &2, String, List<&2, Ops.Item>>:
    Bool.pick(Result<&2, &2, String, Unit>, ok, Done{Unit{}}, Fail{"an operation counts past the end of the parent"})
    items : List<&2, Ops.Item> <- Ops.apply.go(ops, Ops.land(ops, 0n, state, Nil{}), 0n, None{})
    Ops.apply.checked(result, items)

def apply_is(+state: List<&2, Ops.Item>, -f: Maybe<&2, String>, result: Maybe<&2, String>, +ops: List<&2, Ops.Op>) -> {Ops.apply(state, Ops.Doc{f, result, ops}) == after_range(state, result, ops, Ops.in_range(ops, List.length(&2, Ops.Item, state))) : Result<&2, &2, String, List<&2, Ops.Item>>}:
  {==}

def bind_like(g1: Result<&2, &2, String, List<&2, Ops.Item>>, g2: Result<&2, &2, String, List<&2, Ops.Item>>, +r: Maybe<&2, String>, h: {Stand.result.like(g1, g2) == True{} : Bool}) -> {Stand.result.like(Result.bind(&2, &2, String, List<&2, Ops.Item>, List<&2, Ops.Item>, g1, items => Ops.apply.checked(r, items)), Result.bind(&2, &2, String, List<&2, Ops.Item>, List<&2, Ops.Item>, g2, items => Ops.apply.checked(None{}, items))) == True{} : Bool}:
  match g1 g2:
    case Fail{e} y:
      {==}
    case Done{+x} Done{+y}:
      checked_like(r, x, y, h)
    case Done{x} Fail{e}:
      Empty.absurd({Stand.result.like(Ops.apply.checked(r, x), Fail{e}) == True{} : Bool}, S.false_true(h))

def range_case(ok1: Bool, ok2: Bool, +st1: List<&2, Ops.Item>, +st2: List<&2, Ops.Item>, +r: Maybe<&2, String>, +ops1: List<&2, Ops.Op>, +ops2: List<&2, Ops.Op>, eok: {ok1 == ok2 : Bool}, +hs: {Stand.items.like(st1, st2) == True{} : Bool}, +hops: {Stand.ops.like(ops1, ops2) == True{} : Bool}) -> {Stand.result.like(after_range(st1, r, ops1, ok1), after_range(st2, None{}, ops2, ok2)) == True{} : Bool}:
  match ok1:
    case False{}:
      {==}
    case True{}:
      %eok : {Stand.result.like(after_range(st1, r, ops1, True{}), after_range(st2, None{}, ops2, _)) == True{} : Bool}
      bind_like(Ops.apply.go(ops1, Ops.land(ops1, 0n, st1, Nil{}), 0n, None{}), Ops.apply.go(ops2, Ops.land(ops2, 0n, st2, Nil{}), 0n, None{}), r,
        go_like(ops1, ops2, Ops.land(ops1, 0n, st1, Nil{}), Ops.land(ops2, 0n, st2, Nil{}), 0n, None{}, None{}, hops,
          land_like(ops1, ops2, 0n, st1, st2, Nil{}, Nil{}, hops, hs, {==}), {==}))

# A stand-in replays wherever what it stands in for replays, over a parent
# read through stand-ins too, to a file whose every line is the original's
# line or that line forgotten.
def replays_like(+st1: List<&2, Ops.Item>, +st2: List<&2, Ops.Item>, -f: Maybe<&2, String>, +r: Maybe<&2, String>, +ops1: List<&2, Ops.Op>, -f2: Maybe<&2, String>, +ops2: List<&2, Ops.Op>, +hs: {Stand.items.like(st1, st2) == True{} : Bool}, +hops: {Stand.ops.like(ops1, ops2) == True{} : Bool}) -> {Stand.result.like(Ops.apply(st1, Ops.Doc{f, r, ops1}), Ops.apply(st2, Ops.Doc{f2, None{}, ops2})) == True{} : Bool}:
  %apply_is(st1, f, r, ops1) : {Stand.result.like(_, Ops.apply(st2, Ops.Doc{f2, None{}, ops2})) == True{} : Bool}
  %apply_is(st2, f2, None{}, ops2) : {Stand.result.like(after_range(st1, r, ops1, Ops.in_range(ops1, List.length(&2, Ops.Item, st1))), _) == True{} : Bool}
  +el = like_len(st1, st2, hs)
  %el : {Stand.result.like(after_range(st1, r, ops1, Ops.in_range(ops1, List.length(&2, Ops.Item, st1))), after_range(st2, None{}, ops2, Ops.in_range(ops2, _))) == True{} : Bool}
  range_case(Ops.in_range(ops1, List.length(&2, Ops.Item, st1)), Ops.in_range(ops2, List.length(&2, Ops.Item, st1)), st1, st2, r, ops1, ops2, range_like(ops1, ops2, List.length(&2, Ops.Item, st1), hops), hs, hops)

# What `forget` writes is alike
# -----------------------------

def item_self(it: Ops.Item) -> {Stand.item.like(it, it) == True{} : Bool}:
  match it:
    case Ops.Item{+t, +n, True{}}:
      term_refl(n)
    case Ops.Item{+t, +n, False{}}:
      %Equal.sym(Bool, T.same(t, t), True{}, Diff.same_refl(t)) : {Bool.and(True{}, Bool.and(_, Bool.not(Bool.xor(n, n)))) == True{} : Bool}
      term_refl(n)

def item_forgot(hit: Bool, it: Ops.Item) -> {Stand.item.like(it, Fg.forget.item(hit, it)) == True{} : Bool}:
  match hit it:
    case True{} Ops.Item{t, +n, f}:
      term_refl(n)
    case False{} +it2:
      item_self(it2)

def items_forgot(items: List<&2, Ops.Item>, +ps: List<&2, Fg.FgPick>, +t: String, +i: Nat, +j: Nat) -> {Stand.items.like(items, Fg.forget.items(items, ps, t, i, j)) == True{} : Bool}:
  match items:
    case Nil{}:
      {==}
    case +it <> +rest:
      AL.and_intro(Stand.item.like(it, Fg.forget.item(Fg.picked.has(ps, t, i, j), it)), Stand.items.like(rest, Fg.forget.items(rest, ps, t, i, 1n+j)),
        item_forgot(Fg.picked.has(ps, t, i, j), it), items_forgot(rest, ps, t, i, 1n+j))

# A forgetting document is its original with text destroyed and nothing else.
def ops_forgot(ops: List<&2, Ops.Op>, +ps: List<&2, Fg.FgPick>, +t: String, +i: Nat) -> {Stand.ops.like(ops, Fg.forget.ops(ops, ps, t, i)) == True{} : Bool}:
  match ops:
    case Nil{}:
      {==}
    case Ops.Op{k, +at, +items} <> +rest:
      %Equal.sym(Bool, Ops.verb_is(k, k), True{}, verb_refl(k)) : {Bool.and(_, Bool.and(Nat.is_eq(at, at), Bool.and(Stand.items.like(items, Fg.forget.items(items, ps, t, i, 0n)), Stand.ops.like(rest, Fg.forget.ops(rest, ps, t, 1n+i))))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(at, at), True{}, Comp.eq_refl(at)) : {Bool.and(True{}, Bool.and(_, Bool.and(Stand.items.like(items, Fg.forget.items(items, ps, t, i, 0n)), Stand.ops.like(rest, Fg.forget.ops(rest, ps, t, 1n+i))))) == True{} : Bool}
      %Equal.sym(Bool, Stand.items.like(items, Fg.forget.items(items, ps, t, i, 0n)), True{}, items_forgot(items, ps, t, i, 0n)) : {Bool.and(True{}, Bool.and(True{}, Bool.and(_, Stand.ops.like(rest, Fg.forget.ops(rest, ps, t, 1n+i))))) == True{} : Bool}
      ops_forgot(rest, ps, t, 1n+i)

# The other versions
# ------------------

def held_self(xs: List<&2, String>) -> {Main.all_held(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Rev.member(x <> rest, x), Main.all_held(x <> rest, rest), GL.member_head(x, rest), held_cons(rest, x, rest, held_self(rest)))

def excl_step(e: Bool, +d: String, +x: List<&2, String>, +t: String, he: {String.eq(d, t) == e : Bool}, ih: {Rev.member(x, t) == False{} : Bool}) -> {Rev.member(Rev.keep(Bool.not(e), d, x), t) == False{} : Bool}:
  match e:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, String.eq(d, t), False{}, he) : {Bool.or(_, Rev.member(x, t)) == False{} : Bool}
      ih

def excl(ds: List<&2, String>, +t: String) -> {Rev.member(Fg.others.of(ds, t), t) == False{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case +d <> +rest:
      excl_step(String.eq(d, t), d, Fg.others.of(rest, t), t, {==}, excl(rest, t))

def not_true(b: Bool, e: {b == False{} : Bool}, h: {b == True{} : Bool}) -> Empty:
  S.false_true(Equal.trans(Bool, False{}, b, True{}, Equal.sym(Bool, b, False{}, e), h))

def others_case(m: Bool, +fs: List<&2, Main.Full>, +file: String, +t: String, em: {Rev.member(Fg.others(fs, file, t), t) == m : Bool}) -> {m == False{} : Bool}:
  match m:
    case False{}:
      {==}
    case True{}:
      +xs = Fg.others.of(Fg.bytes.of(fs, file), t)
      +sorted = List.sort(~String, ~(a => b => String.is_le(a, b)), xs)
      Empty.absurd({True{} == False{} : Bool},
        not_true(Rev.member(xs, t), excl(Fg.bytes.of(fs, file), t),
          held_member(xs, sorted, t, StatusL.ah_sort(~(a => b => String.is_le(a, b)), xs, xs, held_self(xs)),
            held_member(sorted, Main.distinct(sorted), t, StatusL.ah_distinct(sorted, sorted, held_self(sorted)), em))))

# The other versions `forget` counts of a file of bytes never include the
# one it forgets.
def others_exclude(+fs: List<&2, Main.Full>, +file: String, +t: String) -> {Rev.member(Fg.others(fs, file, t), t) == False{} : Bool}:
  others_case(Rev.member(Fg.others(fs, file, t), t), fs, file, t, {==})

# Stand-ins beside a held original
# --------------------------------

# A stand-in of the held shape, folded in, leaves forgotten every item it
# forgets; and folding more in never brings one back.
def item_cover_union(s: Ops.Item, h: Ops.Item) -> {Stand.item.covers(s, Stand.item.union(h, s)) == True{} : Bool}:
  match s h:
    case Ops.Item{ts, ns, True{}} Ops.Item{t, n, f}:
      {==}
    case Ops.Item{ts, ns, False{}} Ops.Item{t, n, f}:
      {==}

def items_cover_union(ss: List<&2, Ops.Item>, hs: List<&2, Ops.Item>, +e: {Stand.items.shape(hs, ss) == True{} : Bool}) -> {Stand.items.covers(ss, Stand.items.union(hs, ss)) == True{} : Bool}:
  match ss hs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Ops.Item{+t, +n, +f} <> +hr:
      Empty.absurd({Stand.items.covers(Nil{}, Stand.items.union(Ops.Item{t, n, f} <> hr, Nil{})) == True{} : Bool}, S.false_true(e))
    case +s <> +sr Nil{}:
      Empty.absurd({Stand.items.covers(s <> sr, Stand.items.union(Nil{}, s <> sr)) == True{} : Bool}, S.false_true(e))
    case Ops.Item{+ts, +ns, +fs} <> +sr Ops.Item{+t, +n, +f} <> +hr:
      AL.and_intro(Stand.item.covers(Ops.Item{ts, ns, fs}, Stand.item.union(Ops.Item{t, n, f}, Ops.Item{ts, ns, fs})), Stand.items.covers(sr, Stand.items.union(hr, sr)),
        item_cover_union(Ops.Item{ts, ns, fs}, Ops.Item{t, n, f}),
        items_cover_union(sr, hr, Comp.and_right(Bool.not(Bool.xor(n, ns)), Stand.items.shape(hr, sr), e)))

def ops_cover_union(ss: List<&2, Ops.Op>, hs: List<&2, Ops.Op>, +e: {Stand.ops.shape(hs, ss) == True{} : Bool}) -> {Stand.ops.covers(ss, Stand.ops.union(hs, ss)) == True{} : Bool}:
  match ss hs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Ops.Op{+k, +at, +hi} <> +hr:
      Empty.absurd({Stand.ops.covers(Nil{}, Stand.ops.union(Ops.Op{k, at, hi} <> hr, Nil{})) == True{} : Bool}, S.false_true(e))
    case Ops.Op{+ks, +ats, +si} <> +sr Nil{}:
      Empty.absurd({Stand.ops.covers(Ops.Op{ks, ats, si} <> sr, Stand.ops.union(Nil{}, Ops.Op{ks, ats, si} <> sr)) == True{} : Bool}, S.false_true(e))
    case Ops.Op{+ks, +ats, +si} <> +sr Ops.Op{+k, +at, +hi} <> +hr:
      +e2 = Comp.and_right(Nat.is_eq(at, ats), Bool.and(Stand.items.shape(hi, si), Stand.ops.shape(hr, sr)), Comp.and_right(Ops.verb_is(k, ks), Bool.and(Nat.is_eq(at, ats), Bool.and(Stand.items.shape(hi, si), Stand.ops.shape(hr, sr))), e))
      AL.and_intro(Stand.items.covers(si, Stand.items.union(hi, si)), Stand.ops.covers(sr, Stand.ops.union(hr, sr)),
        items_cover_union(si, hi, Comp.and_left(Stand.items.shape(hi, si), Stand.ops.shape(hr, sr), e2)),
        ops_cover_union(sr, hr, Comp.and_right(Stand.items.shape(hi, si), Stand.ops.shape(hr, sr), e2)))

def item_cover_mono(s: Ops.Item, r: Ops.Item, x: Ops.Item, +h: {Stand.item.covers(s, r) == True{} : Bool}) -> {Stand.item.covers(s, Stand.item.union(r, x)) == True{} : Bool}:
  match s r x:
    case Ops.Item{ts, ns, True{}} Ops.Item{tr, nr, True{}} Ops.Item{tx, nx, True{}}:
      {==}
    case Ops.Item{ts, ns, True{}} Ops.Item{tr, nr, True{}} Ops.Item{tx, nx, False{}}:
      {==}
    case Ops.Item{+ts, +ns, True{}} Ops.Item{+tr, +nr, False{}} +x2:
      Empty.absurd({Stand.item.covers(Ops.Item{ts, ns, True{}}, Stand.item.union(Ops.Item{tr, nr, False{}}, x2)) == True{} : Bool}, S.false_true(h))
    case Ops.Item{ts, ns, False{}} r2 x2:
      {==}

def items_cover_mono(ss: List<&2, Ops.Item>, rs: List<&2, Ops.Item>, xs: List<&2, Ops.Item>, +h: {Stand.items.covers(ss, rs) == True{} : Bool}) -> {Stand.items.covers(ss, Stand.items.union(rs, xs)) == True{} : Bool}:
  match ss rs xs:
    case Nil{} Nil{} x:
      {==}
    case Nil{} +r <> +rr +x:
      Empty.absurd({Stand.items.covers(Nil{}, Stand.items.union(r <> rr, x)) == True{} : Bool}, S.false_true(h))
    case +s <> +sr Nil{} +x:
      Empty.absurd({Stand.items.covers(s <> sr, Stand.items.union(Nil{}, x)) == True{} : Bool}, S.false_true(h))
    case +s <> +sr +r <> +rr Nil{}:
      h
    case +s <> +sr +r <> +rr +x <> +xr:
      AL.and_intro(Stand.item.covers(s, Stand.item.union(r, x)), Stand.items.covers(sr, Stand.items.union(rr, xr)),
        item_cover_mono(s, r, x, Comp.and_left(Stand.item.covers(s, r), Stand.items.covers(sr, rr), h)),
        items_cover_mono(sr, rr, xr, Comp.and_right(Stand.item.covers(s, r), Stand.items.covers(sr, rr), h)))

def ops_cover_mono(ss: List<&2, Ops.Op>, rs: List<&2, Ops.Op>, xs: List<&2, Ops.Op>, +h: {Stand.ops.covers(ss, rs) == True{} : Bool}) -> {Stand.ops.covers(ss, Stand.ops.union(rs, xs)) == True{} : Bool}:
  match ss rs xs:
    case Nil{} Nil{} x:
      {==}
    case Nil{} Ops.Op{+kr, +atr, +ri} <> +rr +x:
      Empty.absurd({Stand.ops.covers(Nil{}, Stand.ops.union(Ops.Op{kr, atr, ri} <> rr, x)) == True{} : Bool}, S.false_true(h))
    case Ops.Op{+ks, +ats, +si} <> +sr Nil{} +x:
      Empty.absurd({Stand.ops.covers(Ops.Op{ks, ats, si} <> sr, Stand.ops.union(Nil{}, x)) == True{} : Bool}, S.false_true(h))
    case Ops.Op{+ks, +ats, +si} <> +sr Ops.Op{+kr, +atr, +ri} <> +rr Nil{}:
      h
    case Ops.Op{ks, ats, +si} <> +sr Ops.Op{kr, atr, +ri} <> +rr Ops.Op{kx, atx, +xi} <> +xr:
      AL.and_intro(Stand.items.covers(si, Stand.items.union(ri, xi)), Stand.ops.covers(sr, Stand.ops.union(rr, xr)),
        items_cover_mono(si, ri, xi, Comp.and_left(Stand.items.covers(si, ri), Stand.ops.covers(sr, rr), h)),
        ops_cover_mono(sr, rr, xr, Comp.and_right(Stand.items.covers(si, ri), Stand.ops.covers(sr, rr), h)))

def pick_cover(ss: List<&2, Ops.Op>, rs: List<&2, Ops.Op>, xs: List<&2, Ops.Op>, same: Bool, +h: {Stand.ops.covers(ss, rs) == True{} : Bool}) -> {Stand.ops.covers(ss, Stand.ops.fold.pick(rs, xs, same)) == True{} : Bool}:
  match same:
    case True{}:
      ops_cover_mono(ss, rs, xs, h)
    case False{}:
      h

def folded_cover(ds: List<&2, Ops.Doc>, +ss: List<&2, Ops.Op>, +held: List<&2, Ops.Op>, +h: {Stand.ops.covers(ss, held) == True{} : Bool}) -> {Stand.ops.covers(ss, Stand.ops.folded(ds, held)) == True{} : Bool}:
  match ds:
    case Nil{}:
      h
    case Ops.Doc{f, r, +stated} <> +rest:
      folded_cover(rest, ss, Stand.ops.fold.pick(held, stated, Stand.ops.shape(held, stated)), pick_cover(ss, held, stated, Stand.ops.shape(held, stated), h))

# What a stand-in of the held shape forgets is forgotten in what is read,
# whatever other stand-ins are folded in after it.
def forgets_all(f: Maybe<&2, String>, r: Maybe<&2, String>, +stated: List<&2, Ops.Op>, rest: List<&2, Ops.Doc>, +held: List<&2, Ops.Op>, +e: {Stand.ops.shape(held, stated) == True{} : Bool}) -> {Stand.ops.covers(stated, Stand.ops.folded(Ops.Doc{f, r, stated} <> rest, held)) == True{} : Bool}:
  %Equal.sym(Bool, Stand.ops.shape(held, stated), True{}, e) : {Stand.ops.covers(stated, Stand.ops.folded(rest, Stand.ops.fold.pick(held, stated, _))) == True{} : Bool}
  folded_cover(rest, stated, Stand.ops.union(held, stated), ops_cover_union(stated, held, e))

def items_self(xs: List<&2, Ops.Item>) -> {Stand.items.like(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Stand.item.like(x, x), Stand.items.like(rest, rest), item_self(x), items_self(rest))

def ops_self(xs: List<&2, Ops.Op>) -> {Stand.ops.like(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Ops.Op{k, +at, +items} <> +rest:
      %Equal.sym(Bool, Ops.verb_is(k, k), True{}, verb_refl(k)) : {Bool.and(_, Bool.and(Nat.is_eq(at, at), Bool.and(Stand.items.like(items, items), Stand.ops.like(rest, rest)))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(at, at), True{}, Comp.eq_refl(at)) : {Bool.and(True{}, Bool.and(_, Bool.and(Stand.items.like(items, items), Stand.ops.like(rest, rest)))) == True{} : Bool}
      %Equal.sym(Bool, Stand.items.like(items, items), True{}, items_self(items)) : {Bool.and(True{}, Bool.and(True{}, Bool.and(_, Stand.ops.like(rest, rest)))) == True{} : Bool}
      ops_self(rest)

# A stand-in's item folded into one read like the original stays like it:
# forgotten, it takes the text and keeps the terminator; kept, it changes
# nothing.
def item_union_like(x: Ops.Item, c: Ops.Item, s: Ops.Item, +h: {Stand.item.like(x, c) == True{} : Bool}) -> {Stand.item.like(x, Stand.item.union(c, s)) == True{} : Bool}:
  match x c s:
    case Ops.Item{+tx, +nx, +fx} Ops.Item{+tc, +nc, True{}} Ops.Item{ts, ns, True{}}:
      h
    case Ops.Item{+tx, +nx, +fx} Ops.Item{+tc, +nc, False{}} Ops.Item{ts, ns, True{}}:
      Comp.and_right(T.same(tx, tc), Bool.not(Bool.xor(nx, nc)), Comp.and_right(Bool.not(fx), Bool.and(T.same(tx, tc), Bool.not(Bool.xor(nx, nc))), h))
    case Ops.Item{+tx, +nx, +fx} Ops.Item{+tc, +nc, +fc} Ops.Item{ts, ns, False{}}:
      h

def items_union_like(xs: List<&2, Ops.Item>, cs: List<&2, Ops.Item>, ss: List<&2, Ops.Item>, +h: {Stand.items.like(xs, cs) == True{} : Bool}) -> {Stand.items.like(xs, Stand.items.union(cs, ss)) == True{} : Bool}:
  match xs cs ss:
    case Nil{} Nil{} s:
      {==}
    case Nil{} +c <> +cr +s:
      Empty.absurd({Stand.items.like(Nil{}, Stand.items.union(c <> cr, s)) == True{} : Bool}, S.false_true(h))
    case +x <> +xr Nil{} +s:
      Empty.absurd({Stand.items.like(x <> xr, Stand.items.union(Nil{}, s)) == True{} : Bool}, S.false_true(h))
    case +x <> +xr +c <> +cr Nil{}:
      h
    case +x <> +xr +c <> +cr +s <> +sr:
      AL.and_intro(Stand.item.like(x, Stand.item.union(c, s)), Stand.items.like(xr, Stand.items.union(cr, sr)),
        item_union_like(x, c, s, Comp.and_left(Stand.item.like(x, c), Stand.items.like(xr, cr), h)),
        items_union_like(xr, cr, sr, Comp.and_right(Stand.item.like(x, c), Stand.items.like(xr, cr), h)))

def ops_union_like(xs: List<&2, Ops.Op>, cs: List<&2, Ops.Op>, ss: List<&2, Ops.Op>, +h: {Stand.ops.like(xs, cs) == True{} : Bool}) -> {Stand.ops.like(xs, Stand.ops.union(cs, ss)) == True{} : Bool}:
  match xs cs ss:
    case Nil{} Nil{} s:
      {==}
    case Nil{} Ops.Op{+kc, +atc, +ic} <> +cr +s:
      Empty.absurd({Stand.ops.like(Nil{}, Stand.ops.union(Ops.Op{kc, atc, ic} <> cr, s)) == True{} : Bool}, S.false_true(h))
    case Ops.Op{+kx, +atx, +ix} <> +xr Nil{} +s:
      Empty.absurd({Stand.ops.like(Ops.Op{kx, atx, ix} <> xr, Stand.ops.union(Nil{}, s)) == True{} : Bool}, S.false_true(h))
    case Ops.Op{+kx, +atx, +ix} <> +xr Ops.Op{+kc, +atc, +ic} <> +cr Nil{}:
      h
    case Ops.Op{+kx, +atx, +ix} <> +xr Ops.Op{+kc, +atc, +ic} <> +cr Ops.Op{ks, ats, +si} <> +sr:
      +hr = Comp.and_right(Ops.verb_is(kx, kc), Bool.and(Nat.is_eq(atx, atc), Bool.and(Stand.items.like(ix, ic), Stand.ops.like(xr, cr))), h)
      +hr2 = Comp.and_right(Nat.is_eq(atx, atc), Bool.and(Stand.items.like(ix, ic), Stand.ops.like(xr, cr)), hr)
      AL.and_intro(Ops.verb_is(kx, kc), Bool.and(Nat.is_eq(atx, atc), Bool.and(Stand.items.like(ix, Stand.items.union(ic, si)), Stand.ops.like(xr, Stand.ops.union(cr, sr)))),
        Comp.and_left(Ops.verb_is(kx, kc), Bool.and(Nat.is_eq(atx, atc), Bool.and(Stand.items.like(ix, ic), Stand.ops.like(xr, cr))), h),
        AL.and_intro(Nat.is_eq(atx, atc), Bool.and(Stand.items.like(ix, Stand.items.union(ic, si)), Stand.ops.like(xr, Stand.ops.union(cr, sr))),
          Comp.and_left(Nat.is_eq(atx, atc), Bool.and(Stand.items.like(ix, ic), Stand.ops.like(xr, cr)), hr),
          AL.and_intro(Stand.items.like(ix, Stand.items.union(ic, si)), Stand.ops.like(xr, Stand.ops.union(cr, sr)),
            items_union_like(ix, ic, si, Comp.and_left(Stand.items.like(ix, ic), Stand.ops.like(xr, cr), hr2)),
            ops_union_like(xr, cr, sr, Comp.and_right(Stand.items.like(ix, ic), Stand.ops.like(xr, cr), hr2)))))

def pick_like(xs: List<&2, Ops.Op>, held: List<&2, Ops.Op>, stated: List<&2, Ops.Op>, same: Bool, +h: {Stand.ops.like(xs, held) == True{} : Bool}) -> {Stand.ops.like(xs, Stand.ops.fold.pick(held, stated, same)) == True{} : Bool}:
  match same:
    case True{}:
      ops_union_like(xs, held, stated, h)
    case False{}:
      h

def folded_like(ds: List<&2, Ops.Doc>, +xs: List<&2, Ops.Op>, +held: List<&2, Ops.Op>, +h: {Stand.ops.like(xs, held) == True{} : Bool}) -> {Stand.ops.like(xs, Stand.ops.folded(ds, held)) == True{} : Bool}:
  match ds:
    case Nil{}:
      h
    case Ops.Doc{f, r, +stated} <> +rest:
      folded_like(rest, xs, Stand.ops.fold.pick(held, stated, Stand.ops.shape(held, stated)), pick_like(xs, held, stated, Stand.ops.shape(held, stated), h))

# Whatever documents say they forget one the store holds, what is read is
# that document with each item as it was or forgotten.
def only_forget(ds: List<&2, Ops.Doc>, +ops: List<&2, Ops.Op>) -> {Stand.ops.like(ops, Stand.ops.folded(ds, ops)) == True{} : Bool}:
  folded_like(ds, ops, ops, ops_self(ops))

# The union is indifferent to the order stand-ins come in: item by item,
# forgetting is forgetting whichever came first.
def item_union_comm(h: Ops.Item, a: Ops.Item, b: Ops.Item) -> {Stand.item.union(Stand.item.union(h, a), b) == Stand.item.union(Stand.item.union(h, b), a) : Ops.Item}:
  match h a b:
    case Ops.Item{t, n, f} Ops.Item{ta, na, True{}} Ops.Item{tb, nb, True{}}:
      {==}
    case Ops.Item{t, n, f} Ops.Item{ta, na, True{}} Ops.Item{tb, nb, False{}}:
      {==}
    case Ops.Item{t, n, f} Ops.Item{ta, na, False{}} Ops.Item{tb, nb, True{}}:
      {==}
    case Ops.Item{t, n, f} Ops.Item{ta, na, False{}} Ops.Item{tb, nb, False{}}:
      {==}

def items_union_comm(hs: List<&2, Ops.Item>, ys: List<&2, Ops.Item>, zs: List<&2, Ops.Item>) -> {Stand.items.union(Stand.items.union(hs, ys), zs) == Stand.items.union(Stand.items.union(hs, zs), ys) : List<&2, Ops.Item>}:
  match hs ys zs:
    case Nil{} y z:
      {==}
    case h <> hr Nil{} Nil{}:
      {==}
    case h <> hr Nil{} z <> zr:
      {==}
    case h <> hr y <> yr Nil{}:
      {==}
    case +h <> +hr +y <> +yr +z <> +zr:
      %item_union_comm(h, y, z) : {Stand.item.union(Stand.item.union(h, y), z) <> Stand.items.union(Stand.items.union(hr, yr), zr) == _ <> Stand.items.union(Stand.items.union(hr, zr), yr) : List<&2, Ops.Item>}
      %items_union_comm(hr, yr, zr) : {Stand.item.union(Stand.item.union(h, y), z) <> Stand.items.union(Stand.items.union(hr, yr), zr) == Stand.item.union(Stand.item.union(h, y), z) <> _ : List<&2, Ops.Item>}
      {==}

def ops_union_comm(hs: List<&2, Ops.Op>, ys: List<&2, Ops.Op>, zs: List<&2, Ops.Op>) -> {Stand.ops.union(Stand.ops.union(hs, ys), zs) == Stand.ops.union(Stand.ops.union(hs, zs), ys) : List<&2, Ops.Op>}:
  match hs ys zs:
    case Nil{} y z:
      {==}
    case Ops.Op{k, at, hi} <> hr Nil{} Nil{}:
      {==}
    case Ops.Op{k, at, hi} <> hr Nil{} Ops.Op{kz, atz, zi} <> zr:
      {==}
    case Ops.Op{k, at, hi} <> hr Ops.Op{ky, aty, yi} <> yr Nil{}:
      {==}
    case Ops.Op{+k, +at, +hi} <> +hr Ops.Op{ky, aty, +yi} <> +yr Ops.Op{kz, atz, +zi} <> +zr:
      %items_union_comm(hi, yi, zi) : {Ops.Op{k, at, Stand.items.union(Stand.items.union(hi, yi), zi)} <> Stand.ops.union(Stand.ops.union(hr, yr), zr) == Ops.Op{k, at, _} <> Stand.ops.union(Stand.ops.union(hr, zr), yr) : List<&2, Ops.Op>}
      %ops_union_comm(hr, yr, zr) : {Ops.Op{k, at, Stand.items.union(Stand.items.union(hi, yi), zi)} <> Stand.ops.union(Stand.ops.union(hr, yr), zr) == Ops.Op{k, at, Stand.items.union(Stand.items.union(hi, yi), zi)} <> _ : List<&2, Ops.Op>}
      {==}

# Folding a stand-in in changes no shape, so whether a later one is of the
# held shape does not depend on what came before it.
def items_shape_union(hs: List<&2, Ops.Item>, ys: List<&2, Ops.Item>, zs: List<&2, Ops.Item>) -> {Stand.items.shape(Stand.items.union(hs, ys), zs) == Stand.items.shape(hs, zs) : Bool}:
  match hs ys zs:
    case Nil{} y z:
      {==}
    case h <> hr Nil{} z:
      {==}
    case Ops.Item{t, n, f} <> hr Ops.Item{ty, ny, True{}} <> yr Nil{}:
      {==}
    case Ops.Item{t, n, f} <> hr Ops.Item{ty, ny, False{}} <> yr Nil{}:
      {==}
    case Ops.Item{t, +n, f} <> +hr Ops.Item{ty, ny, True{}} <> +yr Ops.Item{tz, +nz, fz} <> +zr:
      %items_shape_union(hr, yr, zr) : {Bool.and(Bool.not(Bool.xor(n, nz)), Stand.items.shape(Stand.items.union(hr, yr), zr)) == Bool.and(Bool.not(Bool.xor(n, nz)), _) : Bool}
      {==}
    case Ops.Item{t, +n, f} <> +hr Ops.Item{ty, ny, False{}} <> +yr Ops.Item{tz, +nz, fz} <> +zr:
      %items_shape_union(hr, yr, zr) : {Bool.and(Bool.not(Bool.xor(n, nz)), Stand.items.shape(Stand.items.union(hr, yr), zr)) == Bool.and(Bool.not(Bool.xor(n, nz)), _) : Bool}
      {==}

def ops_shape_union(hs: List<&2, Ops.Op>, ys: List<&2, Ops.Op>, zs: List<&2, Ops.Op>) -> {Stand.ops.shape(Stand.ops.union(hs, ys), zs) == Stand.ops.shape(hs, zs) : Bool}:
  match hs ys zs:
    case Nil{} y z:
      {==}
    case Ops.Op{k, at, hi} <> hr Nil{} z:
      {==}
    case Ops.Op{k, at, hi} <> hr Ops.Op{ky, aty, yi} <> yr Nil{}:
      {==}
    case Ops.Op{+k, +at, +hi} <> +hr Ops.Op{ky, aty, +yi} <> +yr Ops.Op{+kz, +atz, +zi} <> +zr:
      %items_shape_union(hi, yi, zi) : {Bool.and(Ops.verb_is(k, kz), Bool.and(Nat.is_eq(at, atz), Bool.and(Stand.items.shape(Stand.items.union(hi, yi), zi), Stand.ops.shape(Stand.ops.union(hr, yr), zr)))) == Bool.and(Ops.verb_is(k, kz), Bool.and(Nat.is_eq(at, atz), Bool.and(_, Stand.ops.shape(hr, zr)))) : Bool}
      %ops_shape_union(hr, yr, zr) : {Bool.and(Ops.verb_is(k, kz), Bool.and(Nat.is_eq(at, atz), Bool.and(Stand.items.shape(Stand.items.union(hi, yi), zi), Stand.ops.shape(Stand.ops.union(hr, yr), zr)))) == Bool.and(Ops.verb_is(k, kz), Bool.and(Nat.is_eq(at, atz), Bool.and(Stand.items.shape(Stand.items.union(hi, yi), zi), _))) : Bool}
      {==}

def pick_shape(hs: List<&2, Ops.Op>, ys: List<&2, Ops.Op>, s: Bool, zs: List<&2, Ops.Op>) -> {Stand.ops.shape(Stand.ops.fold.pick(hs, ys, s), zs) == Stand.ops.shape(hs, zs) : Bool}:
  match s:
    case True{}:
      ops_shape_union(hs, ys, zs)
    case False{}:
      {==}

def swap4(hs: List<&2, Ops.Op>, ys: List<&2, Ops.Op>, zs: List<&2, Ops.Op>, sy: Bool, sz: Bool) -> {Stand.ops.fold.pick(Stand.ops.fold.pick(hs, ys, sy), zs, sz) == Stand.ops.fold.pick(Stand.ops.fold.pick(hs, zs, sz), ys, sy) : List<&2, Ops.Op>}:
  match sy sz:
    case True{} True{}:
      ops_union_comm(hs, ys, zs)
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def swap_pick(+hs: List<&2, Ops.Op>, +ys: List<&2, Ops.Op>, +zs: List<&2, Ops.Op>) -> {Stand.ops.fold.pick(Stand.ops.fold.pick(hs, ys, Stand.ops.shape(hs, ys)), zs, Stand.ops.shape(Stand.ops.fold.pick(hs, ys, Stand.ops.shape(hs, ys)), zs)) == Stand.ops.fold.pick(Stand.ops.fold.pick(hs, zs, Stand.ops.shape(hs, zs)), ys, Stand.ops.shape(Stand.ops.fold.pick(hs, zs, Stand.ops.shape(hs, zs)), ys)) : List<&2, Ops.Op>}:
  %Equal.sym(Bool, Stand.ops.shape(Stand.ops.fold.pick(hs, ys, Stand.ops.shape(hs, ys)), zs), Stand.ops.shape(hs, zs), pick_shape(hs, ys, Stand.ops.shape(hs, ys), zs)) : {Stand.ops.fold.pick(Stand.ops.fold.pick(hs, ys, Stand.ops.shape(hs, ys)), zs, _) == Stand.ops.fold.pick(Stand.ops.fold.pick(hs, zs, Stand.ops.shape(hs, zs)), ys, Stand.ops.shape(Stand.ops.fold.pick(hs, zs, Stand.ops.shape(hs, zs)), ys)) : List<&2, Ops.Op>}
  %Equal.sym(Bool, Stand.ops.shape(Stand.ops.fold.pick(hs, zs, Stand.ops.shape(hs, zs)), ys), Stand.ops.shape(hs, ys), pick_shape(hs, zs, Stand.ops.shape(hs, zs), ys)) : {Stand.ops.fold.pick(Stand.ops.fold.pick(hs, ys, Stand.ops.shape(hs, ys)), zs, Stand.ops.shape(hs, zs)) == Stand.ops.fold.pick(Stand.ops.fold.pick(hs, zs, Stand.ops.shape(hs, zs)), ys, _) : List<&2, Ops.Op>}
  swap4(hs, ys, zs, Stand.ops.shape(hs, ys), Stand.ops.shape(hs, zs))

# Two stand-ins next to each other fold alike in either order, so any
# order of them does.
def folded_swap(a: Ops.Doc, b: Ops.Doc, rest: List<&2, Ops.Doc>, +held: List<&2, Ops.Op>) -> {Stand.ops.folded(a <> b <> rest, held) == Stand.ops.folded(b <> a <> rest, held) : List<&2, Ops.Op>}:
  match a b:
    case Ops.Doc{fa, ra, +ys} Ops.Doc{fb, rb, +zs}:
      %swap_pick(held, ys, zs) : {Stand.ops.folded(rest, Stand.ops.fold.pick(Stand.ops.fold.pick(held, ys, Stand.ops.shape(held, ys)), zs, Stand.ops.shape(Stand.ops.fold.pick(held, ys, Stand.ops.shape(held, ys)), zs))) == Stand.ops.folded(rest, _) : List<&2, Ops.Op>}
      {==}

# Replaying the store through stand-ins
# ------------------------------------

# Stored documents, one by one, each the original or one that stands in
# for it: both operation documents, the second parsing to one that states
# no result and whose operations are alike to the first's wherever the
# first parses; or both payloads, the same bytes.
def stored.parsed(a: Result<&2, &2, String, Ops.Doc>, b: Result<&2, &2, String, Ops.Doc>) -> Bool:
  match a b:
    case Fail{e} _:
      True{}
    case Done{Ops.Doc{f1, r1, o1}} Done{Ops.Doc{f2, None{}, o2}}:
      Stand.ops.like(o1, o2)
    case _ _:
      False{}

def stored.doc(b1: Bool, b2: Bool, +t1: String, +t2: String) -> Bool:
  match b1 b2:
    case True{} True{}:
      stored.parsed(Ops.parse(t1), Ops.parse(t2))
    case False{} False{}:
      String.eq(t1, t2)
    case _ _:
      False{}

def stored.like(a: List<&2, Store.Doc>, b: List<&2, Store.Doc>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Store.Doc{+p1, i1, s1, +t1} <> r1 Store.Doc{+p2, i2, s2, +t2} <> r2:
      Bool.and(stored.doc(String.ends_with(p1, ".ops.txt"), String.ends_with(p2, ".ops.txt"), t1, t2), stored.like(r1, r2))
    case _ _:
      False{}

def replay_doc_fail(-e: String, text: String, is_ops: Bool) -> {Main.replay.doc(Fail{e}, text, is_ops) == Fail{e} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match is_ops:
    case True{}:
      {==}
    case False{}:
      {==}

def replay_fail(ds: List<&2, Store.Doc>, -e: String) -> {Main.replay.go(ds, Fail{e}) == Fail{e} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match ds:
    case Nil{}:
      {==}
    case Store.Doc{+path, id, size, text} <> rest:
      %Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Main.replay.doc(Fail{e}, text, String.ends_with(path, ".ops.txt")), Fail{e}, replay_doc_fail(e, text, String.ends_with(path, ".ops.txt"))) : {Main.replay.go(rest, _) == Fail{e} : Result<&2, &2, String, List<&2, Ops.Item>>}
      replay_fail(rest, e)

def step_like(r1: Result<&2, &2, String, List<&2, Ops.Item>>, r2: Result<&2, &2, String, List<&2, Ops.Item>>, p1: Result<&2, &2, String, Ops.Doc>, p2: Result<&2, &2, String, Ops.Doc>, +hr: {Stand.result.like(r1, r2) == True{} : Bool}, +hp: {stored.parsed(p1, p2) == True{} : Bool}) -> {Stand.result.like(Main.replay.step(r1, p1), Main.replay.step(r2, p2)) == True{} : Bool}:
  match r1 r2 p1 p2:
    case Fail{e} b c d:
      {==}
    case Done{x} Fail{e} c d:
      Empty.absurd({Stand.result.like(Main.replay.step(Done{x}, c), Main.replay.step(Fail{e}, d)) == True{} : Bool}, S.false_true(hr))
    case Done{x} Done{y} Fail{e} d:
      {==}
    case Done{+x} Done{+y} Done{Ops.Doc{f1, +r, +o1}} Done{Ops.Doc{f2, None{}, +o2}}:
      replays_like(x, y, f1, r, o1, f2, o2, hr, hp)
    case Done{x} Done{y} Done{Ops.Doc{f1, r, o1}} Done{Ops.Doc{f2, Some{z}, o2}}:
      Empty.absurd({Stand.result.like(Main.replay.step(Done{x}, Done{Ops.Doc{f1, r, o1}}), Main.replay.step(Done{y}, Done{Ops.Doc{f2, Some{z}, o2}})) == True{} : Bool}, S.false_true(hp))
    case Done{x} Done{y} Done{Ops.Doc{f1, r, o1}} Fail{e}:
      Empty.absurd({Stand.result.like(Main.replay.step(Done{x}, Done{Ops.Doc{f1, r, o1}}), Main.replay.step(Done{y}, Fail{e})) == True{} : Bool}, S.false_true(hp))

def payload_like(r1: Result<&2, &2, String, List<&2, Ops.Item>>, r2: Result<&2, &2, String, List<&2, Ops.Item>>, +t1: String, +t2: String, +hr: {Stand.result.like(r1, r2) == True{} : Bool}, +ht: {String.eq(t1, t2) == True{} : Bool}) -> {Stand.result.like(Main.replay.payload(r1, t1), Main.replay.payload(r2, t2)) == True{} : Bool}:
  match r1 r2:
    case Fail{e} b:
      {==}
    case Done{x} Fail{e}:
      Empty.absurd({Stand.result.like(Main.replay.payload(Done{x}, t1), Main.replay.payload(Fail{e}, t2)) == True{} : Bool}, S.false_true(hr))
    case Done{x} Done{y}:
      %S.eq_true(t1, t2, ht) : {Stand.items.like(Ops.from_text(t1), Ops.from_text(_)) == True{} : Bool}
      items_self(Ops.from_text(t1))

def doc_like(b1: Bool, b2: Bool, +t1: String, +t2: String, r1: Result<&2, &2, String, List<&2, Ops.Item>>, r2: Result<&2, &2, String, List<&2, Ops.Item>>, +hr: {Stand.result.like(r1, r2) == True{} : Bool}, +hd: {stored.doc(b1, b2, t1, t2) == True{} : Bool}) -> {Stand.result.like(Main.replay.doc(r1, t1, b1), Main.replay.doc(r2, t2, b2)) == True{} : Bool}:
  match b1 b2:
    case True{} True{}:
      step_like(r1, r2, Ops.parse(t1), Ops.parse(t2), hr, hd)
    case False{} False{}:
      payload_like(r1, r2, t1, t2, hr, hd)
    case True{} False{}:
      Empty.absurd({Stand.result.like(Main.replay.doc(r1, t1, True{}), Main.replay.doc(r2, t2, False{})) == True{} : Bool}, S.false_true(hd))
    case False{} True{}:
      Empty.absurd({Stand.result.like(Main.replay.doc(r1, t1, False{}), Main.replay.doc(r2, t2, True{})) == True{} : Bool}, S.false_true(hd))

# The replay of stored documents reads alike through stand-ins, from alike
# files.
def stored_like(ds1: List<&2, Store.Doc>, ds2: List<&2, Store.Doc>, +r1: Result<&2, &2, String, List<&2, Ops.Item>>, +r2: Result<&2, &2, String, List<&2, Ops.Item>>, +hd: {stored.like(ds1, ds2) == True{} : Bool}, +hr: {Stand.result.like(r1, r2) == True{} : Bool}) -> {Stand.result.like(Main.replay.go(ds1, r1), Main.replay.go(ds2, r2)) == True{} : Bool}:
  match ds1 ds2:
    case Nil{} Nil{}:
      hr
    case Store.Doc{+p1, i1, s1, +t1} <> +xs Store.Doc{+p2, i2, s2, +t2} <> +ys:
      +b1 = String.ends_with(p1, ".ops.txt")
      +b2 = String.ends_with(p2, ".ops.txt")
      stored_like(xs, ys, Main.replay.doc(r1, t1, b1), Main.replay.doc(r2, t2, b2),
        Comp.and_right(stored.doc(b1, b2, t1, t2), stored.like(xs, ys), hd),
        doc_like(b1, b2, t1, t2, r1, r2, hr, Comp.and_left(stored.doc(b1, b2, t1, t2), stored.like(xs, ys), hd)))
    case Nil{} Store.Doc{p2, i2, s2, t2} <> ys:
      Empty.absurd({Stand.result.like(Main.replay.go(Nil{}, r1), Main.replay.go(Store.Doc{p2, i2, s2, t2} <> ys, r2)) == True{} : Bool}, S.false_true(hd))
    case Store.Doc{p1, i1, s1, t1} <> xs Nil{}:
      Empty.absurd({Stand.result.like(Main.replay.go(Store.Doc{p1, i1, s1, t1} <> xs, r1), Main.replay.go(Nil{}, r2)) == True{} : Bool}, S.false_true(hd))
