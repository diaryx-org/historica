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

def words.of(r: Fg.FgReading) -> List<&2, String>:
  match r:
    case Fg.Fg.Reading{l, d, f, ws, x}:
      ws

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

def words_eq(-a: Fg.FgReading, -b: Fg.FgReading, h: {Done{a} == Done{b} : Result<&2, &2, Main.Refused, Fg.FgReading>}) -> {words.of(a) == words.of(b) : List<&2, String>}:
  Equal.cong(Fg.FgReading, List<&2, String>, r => words.of(r), a, b, B.done_eq(Fg.FgReading, a, b, h))

def go_done(-r: Fg.FgReading, -x: Fg.FgReading, h: {Done{x} == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>}) -> {words.of(r) == words.of(x) : List<&2, String>}:
  Equal.sym(List<&2, String>, words.of(x), words.of(r), words_eq(x, r, h))

def word_ok(k: Fg.FgWord, +w: String, +rest: List<&2, String>, +l: Maybe<&2, String>, +d: Bool, +f: Bool, +acc: List<&2, String>, +r: Fg.FgReading, e: {Fg.reading.go(rest, Fg.reading.word(Fg.Fg.Reading{l, d, f, acc, False{}}, w, k)) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>}, ih: @l2: Maybe<&2, String> -> @d2: Bool -> @f2: Bool -> @acc2: List<&2, String> -> @w2: Bool -> {Fg.reading.go(rest, Done{Fg.Fg.Reading{l2, d2, f2, acc2, w2}}) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>} -> {words.of(r) == List.append(&2, String, acc2, Fg.plain(rest, w2)) : List<&2, String>}) -> {words.of(r) == List.append(&2, String, acc, Fg.plain.pick(False{}, k, w, Fg.plain(rest, True{}), Fg.plain(rest, False{}))) : List<&2, String>}:
  match k:
    case Fg.Fg.Lines{}:
      ih(l, d, f, acc, True{}, e)
    case Fg.Fg.Dry{}:
      ih(l, True{}, f, acc, False{}, e)
    case Fg.Fg.Fields{}:
      ih(l, d, True{}, acc, False{}, e)
    case Fg.Fg.Flag{}:
      +bad = {Main.Refused{2, "`" ++ w ++ "` is not an argument `forget` takes"} : Main.Refused}
      Empty.absurd({words.of(r) == List.append(&2, String, acc, Fg.plain(rest, False{})) : List<&2, String>},
        B.fail_done(Fg.FgReading, bad, r, Equal.trans(Result<&2, &2, Main.Refused, Fg.FgReading>, Fail{bad}, Fg.reading.go(rest, Fail{bad}), Done{r}, Equal.sym(Result<&2, &2, Main.Refused, Fg.FgReading>, Fg.reading.go(rest, Fail{bad}), Fail{bad}, go_fail(rest, bad)), e)))
    case Fg.Fg.Plain{}:
      +h = ih(l, d, f, List.append(&2, String, acc, [w]), False{}, e)
      %app_one(acc, w, Fg.plain(rest, False{})) : {words.of(r) == _ : List<&2, String>}
      h

def step_ok(wants: Bool, +w: String, +rest: List<&2, String>, +l: Maybe<&2, String>, +d: Bool, +f: Bool, +acc: List<&2, String>, +r: Fg.FgReading, e: {Fg.reading.go(rest, Fg.reading.step(Fg.Fg.Reading{l, d, f, acc, wants}, w)) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>}, ih: @l2: Maybe<&2, String> -> @d2: Bool -> @f2: Bool -> @acc2: List<&2, String> -> @w2: Bool -> {Fg.reading.go(rest, Done{Fg.Fg.Reading{l2, d2, f2, acc2, w2}}) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>} -> {words.of(r) == List.append(&2, String, acc2, Fg.plain(rest, w2)) : List<&2, String>}) -> {words.of(r) == List.append(&2, String, acc, Fg.plain.pick(wants, Fg.word(w), w, Fg.plain(rest, True{}), Fg.plain(rest, False{}))) : List<&2, String>}:
  match wants:
    case True{}:
      ih(Some{w}, d, f, acc, False{}, e)
    case False{}:
      word_ok(Fg.word(w), w, rest, l, d, f, acc, r, e, ih)

# The words `reading.go` keeps are the command line's plain words, after
# those it had kept already.
def go_ok(ws: List<&2, String>, +l: Maybe<&2, String>, +d: Bool, +f: Bool, +acc: List<&2, String>, +wants: Bool, +r: Fg.FgReading, e: {Fg.reading.go(ws, Done{Fg.Fg.Reading{l, d, f, acc, wants}}) == Done{r} : Result<&2, &2, Main.Refused, Fg.FgReading>}) -> {words.of(r) == List.append(&2, String, acc, Fg.plain(ws, wants)) : List<&2, String>}:
  match ws:
    case Nil{}:
      +h = go_done(r, Fg.Fg.Reading{l, d, f, acc, wants}, e)
      %Equal.sym(List<&2, String>, List.append(&2, String, acc, Nil{}), acc, app_nil(acc)) : {words.of(r) == _ : List<&2, String>}
      h
    case +w <> +rest:
      step_ok(wants, w, rest, l, d, f, acc, r, e, l2 => d2 => f2 => acc2 => w2 => h2 => go_ok(rest, l2, d2, f2, acc2, w2, r, h2))

def asked.words.of(a: Fg.FgAsked) -> List<&2, String>:
  match a:
    case Fg.Fg.Asked{t, p, sp, d, f}:
      [t, p]

def asked_eq(-a: Fg.FgAsked, -b: Fg.FgAsked, h: {Done{a} == Done{b} : Result<&2, &2, Main.Refused, Fg.FgAsked>}) -> {asked.words.of(a) == asked.words.of(b) : List<&2, String>}:
  Equal.cong(Fg.FgAsked, List<&2, String>, x => asked.words.of(x), a, b, B.done_eq(Fg.FgAsked, a, b, h))

def span_ok(+t: String, +p: String, +d: Bool, +f: Bool, r: Result<&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>>, +a: Fg.FgAsked, e: {Result.map(&2, &2, Main.Refused, Maybe<&2, Fg.FgSpan>, Fg.FgAsked, sp => Fg.Fg.Asked{t, p, sp, d, f}, r) == Done{a} : Result<&2, &2, Main.Refused, Fg.FgAsked>}) -> {[t, p] == asked.words.of(a) : List<&2, String>}:
  match r:
    case Fail{x}:
      Empty.absurd({[t, p] == asked.words.of(a) : List<&2, String>}, B.fail_done(Fg.FgAsked, x, a, e))
    case Done{sp}:
      asked_eq(Fg.Fg.Asked{t, p, sp, d, f}, a, e)

def words_ok(+l: Maybe<&2, String>, +d: Bool, +f: Bool, ws: List<&2, String>, +a: Fg.FgAsked, e: {Fg.asked.words(l, d, f, ws) == Done{a} : Result<&2, &2, Main.Refused, Fg.FgAsked>}) -> {ws == asked.words.of(a) : List<&2, String>}:
  match ws:
    case Nil{}:
      Empty.absurd({Nil{} == asked.words.of(a) : List<&2, String>}, B.fail_done(Fg.FgAsked, Main.Refused{2, "`forget` wants a revision to read the span at"}, a, e))
    case t <> Nil{}:
      Empty.absurd({[t] == asked.words.of(a) : List<&2, String>}, B.fail_done(Fg.FgAsked, Main.Refused{2, "`forget` wants a path"}, a, e))
    case +t <> +p <> Nil{}:
      span_ok(t, p, d, f, Fg.asked.span(l), a, e)
    case t <> p <> +x <> more:
      Empty.absurd({t <> p <> x <> more == asked.words.of(a) : List<&2, String>}, B.fail_done(Fg.FgAsked, Main.Refused{2, "`forget` takes a target and one path, and `" ++ x ++ "` is a third argument"}, a, e))

def read_ok(+l: Maybe<&2, String>, d: Bool, f: Bool, +ws: List<&2, String>, wants: Bool, +a: Fg.FgAsked, e: {Fg.asked.read(Fg.Fg.Reading{l, d, f, ws, wants}) == Done{a} : Result<&2, &2, Main.Refused, Fg.FgAsked>}) -> {ws == asked.words.of(a) : List<&2, String>}:
  match d f wants:
    case True{} True{} True{}:
      Empty.absurd({ws == asked.words.of(a) : List<&2, String>}, B.fail_done(Fg.FgAsked, Main.Refused{2, "`--lines` wants a span, as `<first>..<last>`"}, a, e))
    case True{} False{} True{}:
      Empty.absurd({ws == asked.words.of(a) : List<&2, String>}, B.fail_done(Fg.FgAsked, Main.Refused{2, "`--lines` wants a span, as `<first>..<last>`"}, a, e))
    case False{} True{} True{}:
      Empty.absurd({ws == asked.words.of(a) : List<&2, String>}, B.fail_done(Fg.FgAsked, Main.Refused{2, "`--lines` wants a span, as `<first>..<last>`"}, a, e))
    case False{} False{} True{}:
      Empty.absurd({ws == asked.words.of(a) : List<&2, String>}, B.fail_done(Fg.FgAsked, Main.Refused{2, "`--lines` wants a span, as `<first>..<last>`"}, a, e))
    case True{} True{} False{}:
      Empty.absurd({ws == asked.words.of(a) : List<&2, String>}, B.fail_done(Fg.FgAsked, Main.Refused{2, "`forget --dry-run --fields` is refused: `--fields` states what is on disk, and a plan is not on disk. ask for one or the other"}, a, e))
    case True{} False{} False{}:
      words_ok(l, True{}, False{}, ws, a, e)
    case False{} True{} False{}:
      words_ok(l, False{}, True{}, ws, a, e)
    case False{} False{} False{}:
      words_ok(l, False{}, False{}, ws, a, e)

def reading.of(r: Fg.FgReading, +a: Fg.FgAsked, e: {Fg.asked.read(r) == Done{a} : Result<&2, &2, Main.Refused, Fg.FgAsked>}) -> {words.of(r) == asked.words.of(a) : List<&2, String>}:
  match r:
    case Fg.Fg.Reading{+l, d, f, +ws, wants}:
      read_ok(l, d, f, ws, wants, a, e)

def asked_go(+ws: List<&2, String>, g: Result<&2, &2, Main.Refused, Fg.FgReading>, +eg: {Fg.reading.go(ws, Done{Fg.Fg.Reading{None{}, False{}, False{}, Nil{}, False{}}}) == g : Result<&2, &2, Main.Refused, Fg.FgReading>}, +a: Fg.FgAsked, e: {Result.bind(&2, &2, Main.Refused, Fg.FgReading, Fg.FgAsked, g, r => Fg.asked.read(r)) == Done{a} : Result<&2, &2, Main.Refused, Fg.FgAsked>}) -> {Fg.plain(ws, False{}) == asked.words.of(a) : List<&2, String>}:
  match g:
    case Fail{x}:
      Empty.absurd({Fg.plain(ws, False{}) == asked.words.of(a) : List<&2, String>}, B.fail_done(Fg.FgAsked, x, a, e))
    case Done{+r}:
      +h = go_ok(ws, None{}, False{}, False{}, Nil{}, False{}, r, eg)
      %h : {_ == asked.words.of(a) : List<&2, String>}
      reading.of(r, a, e)

# `forget` reads its target and its path as the plain words of its command
# line, in order.
def reads_words(+ws: List<&2, String>, +t: String, +p: String, +sp: Maybe<&2, Fg.FgSpan>, +d: Bool, +f: Bool, e: {Fg.asked.r(ws) == Done{Fg.Fg.Asked{t, p, sp, d, f}} : Result<&2, &2, Main.Refused, Fg.FgAsked>}) -> {Fg.plain(ws, False{}) == [t, p] : List<&2, String>}:
  asked_go(ws, Fg.reading.go(ws, Done{Fg.Fg.Reading{None{}, False{}, False{}, Nil{}, False{}}}), {==}, Fg.Fg.Asked{t, p, sp, d, f}, e)

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

# `forget` removes from `cache/` only what is named by a digest.
def clears(ps: List<&2, String>, +p: String, m: {Rev.member(Fg.cached(ps), p) == True{} : Bool}) -> {T.is_digest(String.drop(p, 6n)) == True{} : Bool}:
  match ps:
    case Nil{}:
      Empty.absurd({T.is_digest(String.drop(p, 6n)) == True{} : Bool}, S.false_true(m))
    case +q <> +rest:
      cached_step(T.is_digest(String.drop(q, 6n)), q, rest, p, {==}, m, t => clears(rest, p, t))

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

def chain_fail(a: List<&2, List<&2, Ops.Op>>, b: List<&2, List<&2, Ops.Op>>, -e: String, c: Result<&2, &2, String, List<&2, Ops.Item>>) -> {Stand.result.like(Merge.replay(a, Fail{e}), Merge.replay(b, c)) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case x <> xs:
      {==}

# A chain of documents, each the original or a stand-in for it, replays
# alike from alike files.
def chain_like(ds1: List<&2, List<&2, Ops.Op>>, ds2: List<&2, List<&2, Ops.Op>>, r1: Result<&2, &2, String, List<&2, Ops.Item>>, r2: Result<&2, &2, String, List<&2, Ops.Item>>, +hd: {Stand.docs.like(ds1, ds2) == True{} : Bool}, +hr: {Stand.result.like(r1, r2) == True{} : Bool}) -> {Stand.result.like(Merge.replay(ds1, r1), Merge.replay(ds2, r2)) == True{} : Bool}:
  match ds1 ds2 r1 r2:
    case a b Fail{e} c:
      chain_fail(a, b, e, c)
    case Nil{} Nil{} Done{f1} Done{f2}:
      hr
    case a b Done{f1} Fail{e}:
      Empty.absurd({Stand.result.like(Merge.replay(a, Done{f1}), Merge.replay(b, Fail{e})) == True{} : Bool}, S.false_true(hr))
    case Nil{} y <> ys Done{f1} Done{f2}:
      Empty.absurd({Stand.result.like(Merge.replay(Nil{}, Done{f1}), Merge.replay(y <> ys, Done{f2})) == True{} : Bool}, S.false_true(hd))
    case x <> xs Nil{} Done{f1} Done{f2}:
      Empty.absurd({Stand.result.like(Merge.replay(x <> xs, Done{f1}), Merge.replay(Nil{}, Done{f2})) == True{} : Bool}, S.false_true(hd))
    case +x <> +xs +y <> +ys Done{+f1} Done{+f2}:
      chain_like(xs, ys, Ops.apply(f1, Ops.Doc{None{}, None{}, x}), Ops.apply(f2, Ops.Doc{None{}, None{}, y}),
        Comp.and_right(Stand.ops.like(x, y), Stand.docs.like(xs, ys), hd),
        replays_like(f1, f2, None{}, None{}, x, None{}, y, hr, Comp.and_left(Stand.ops.like(x, y), Stand.docs.like(xs, ys), hd)))
