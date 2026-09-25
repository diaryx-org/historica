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
import ./store.bend as Store

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
