# What `amend`, `abandon` and `carry` decide before they write.
#
# A carry restates work without changing whose it is or when it was done:
# each revision a plan writes keeps the change, author, moment and message
# of the one it supersedes, supersedes that one alone, and is named by the
# digest of its own text.
import Base
import ./commands.bend as Main
import ./text.bend as T
import ./revision.bend as Rev
import ./store.bend as Store
import ./sha256.bend as Sha
import ./utf8.bend as Utf8
import ./string_lemmas.bend as S
import ./blamed_lemmas.bend as B
import ./bookmark.bend as Bm

def rdisc_s(-A: Data, r: Result<&2, &2, String, A>) -> Type:
  match r:
    case Done{x}:
      Empty
    case Fail{e}:
      Unit

def done_eq_str(-A: Data, -a: A, -b: A, h: {Done{a} == Done{b} : Result<&2, &2, String, A>}) -> {a == b : A}:
  Equal.cong(Result<&2, &2, String, A>, A, r => Result.default(&2, &2, String, A, r, a), Done{a}, Done{b}, h)

# Carrying keeps what it restates
# -------------------------------

def made_kept(+fs: List<&2, Main.Full>, +id: String, +i: String, +change: String, +ps: List<&2, String>, +ss: List<&2, String>, +author: String, +when: String, +rb: Maybe<&2, String>, +rv: Maybe<&2, String>, +facts: List<&2, Rev.Header>, +message: String, w: Main.Worked, hf: {Main.find(fs, id) == Some{Main.Full{i, change, ps, ss, author, when, rb, rv, facts, message}} : Maybe<&2, Main.Full>}) -> {Main.step.kept(fs, Main.step.made(id, change, author, when, message, w)) == True{} : Bool}:
  match w:
    case Main.Worked{+parents, +nf, +stamp, onto, restated, writes, moving}:
      +doc = {Rev.Rev{change, parents, [id], author, when, Main.revised_by(Main.split.rest(stamp), author), Some{Main.split.head(stamp)}, nf, message} : Rev.Rev}
      %Equal.sym(Maybe<&2, Main.Full>, Main.find(fs, id), Some{Main.Full{i, change, ps, ss, author, when, rb, rv, facts, message}}, hf) : {Bool.and(String.eq(Sha.digest(Utf8.encode(Rev.write(doc))), Sha.digest(Utf8.encode(Rev.write(doc)))), Main.rev.kept(id, _, doc)) == True{} : Bool}
      B.and_tt(String.eq(Sha.digest(Utf8.encode(Rev.write(doc))), Sha.digest(Utf8.encode(Rev.write(doc)))), Main.rev.kept(id, Some{Main.Full{i, change, ps, ss, author, when, rb, rv, facts, message}}, doc), S.eq_refl(Sha.digest(Utf8.encode(Rev.write(doc)))),
        B.and_tt(String.eq(change, change), Bool.and(String.eq(author, author), Bool.and(String.eq(when, when), Bool.and(String.eq(message, message), String.eq(id, id)))), S.eq_refl(change),
        B.and_tt(String.eq(author, author), Bool.and(String.eq(when, when), Bool.and(String.eq(message, message), String.eq(id, id))), S.eq_refl(author),
        B.and_tt(String.eq(when, when), Bool.and(String.eq(message, message), String.eq(id, id)), S.eq_refl(when),
        B.and_tt(String.eq(message, message), String.eq(id, id), S.eq_refl(message), S.eq_refl(id))))))

def mapped_kept(+fs: List<&2, Main.Full>, +id: String, +i: String, +change: String, +ps: List<&2, String>, +ss: List<&2, String>, +author: String, +when: String, +rb: Maybe<&2, String>, +rv: Maybe<&2, String>, +facts: List<&2, Rev.Header>, +message: String, r: Result<&2, &2, String, Main.Worked>, +s: Main.Step, hf: {Main.find(fs, id) == Some{Main.Full{i, change, ps, ss, author, when, rb, rv, facts, message}} : Maybe<&2, Main.Full>}, e: {Result.map(&2, &2, String, Main.Worked, Main.Step, w => Main.step.made(id, change, author, when, message, w), r) == Done{s} : Result<&2, &2, String, Main.Step>}) -> {Main.step.kept(fs, s) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.step.kept(fs, s) == True{} : Bool}, B.fail_done_s(Main.Step, x, s, e))
    case Done{+w}:
      %done_eq_str(Main.Step, Main.step.made(id, change, author, when, message, w), s, e) : {Main.step.kept(fs, _) == True{} : Bool}
      made_kept(fs, id, i, change, ps, ss, author, when, rb, rv, facts, message, w, hf)

# The step `step.of` works out for a revision the store holds keeps it.
def step_kept(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +docs: List<&2, Main.Full>, +id: String, prev: Main.Full, +mapped: List<&2, Main.Mapped>, +authored: Maybe<&2, T.Split>, +s: Main.Step, hf: {Main.find(fs, id) == Some{prev} : Maybe<&2, Main.Full>}, e: {Main.step.of(fs, ds, docs, id, prev, mapped, authored) == Done{s} : Result<&2, &2, String, Main.Step>}) -> {Main.step.kept(fs, s) == True{} : Bool}:
  match prev:
    case Main.Full{+i, +change, +ps, +ss, +author, +when, +rb, +rv, +facts, +message}:
      mapped_kept(fs, id, i, change, ps, ss, author, when, rb, rv, facts, message, Main.step.worked(fs, ds, docs, id, ps, facts, mapped, authored), s, hf, e)

def kept_cons(+fs: List<&2, Main.Full>, +s: Main.Step, +more: List<&2, Main.Step>, -steps: List<&2, Main.Step>, e: {Done{s <> more} == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}, hs: {Main.step.kept(fs, s) == True{} : Bool}, hm: {Main.steps.kept(fs, more) == True{} : Bool}) -> {Main.steps.kept(fs, steps) == True{} : Bool}:
  %done_eq_str(List<&2, Main.Step>, s <> more, steps, e) : {Main.steps.kept(fs, _) == True{} : Bool}
  B.and_tt(Main.step.kept(fs, s), Main.steps.kept(fs, more), hs, hm)

def go4(+fs: List<&2, Main.Full>, +s: Main.Step, r: Result<&2, &2, String, List<&2, Main.Step>>, -steps: List<&2, Main.Step>, e: {Result.bind(&2, &2, String, List<&2, Main.Step>, List<&2, Main.Step>, r, more => Done{s <> more}) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}, hs: {Main.step.kept(fs, s) == True{} : Bool}, ih: @more: List<&2, Main.Step> -> {r == Done{more} : Result<&2, &2, String, List<&2, Main.Step>>} -> {Main.steps.kept(fs, more) == True{} : Bool}) -> {Main.steps.kept(fs, steps) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.steps.kept(fs, steps) == True{} : Bool}, B.fail_done_s(List<&2, Main.Step>, x, steps, e))
    case Done{+more}:
      kept_cons(fs, s, more, steps, e, hs, ih(more, {==}))

def go3(+rest: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +mv: Maybe<&2, Main.Moved>, +stamp: Maybe<&2, T.Split>, +docs: List<&2, Main.Full>, +planned: List<&2, T.Split>, +handed: List<&2, Main.Handed>, +id: String, prev: Main.Full, +mapped: List<&2, Main.Mapped>, r: Result<&2, &2, String, Main.Step>, -steps: List<&2, Main.Step>, er: {Main.step.of(fs, ds, docs, id, prev, mapped, Main.authored.of(id, mv, stamp)) == r : Result<&2, &2, String, Main.Step>}, hf: {Main.find(fs, id) == Some{prev} : Maybe<&2, Main.Full>}, e: {Result.bind(&2, &2, String, Main.Step, List<&2, Main.Step>, r, step => Result.bind(&2, &2, String, List<&2, Main.Step>, List<&2, Main.Step>, Main.steps.go(rest, fs, ds, mv, stamp, Main.step.full(step) <> docs, T.Split{id, Main.step.id(step)} <> planned, Main.step.handed(step) <> handed), more => Done{step <> more})) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}, ih: @docs2: List<&2, Main.Full> -> @planned2: List<&2, T.Split> -> @handed2: List<&2, Main.Handed> -> @more: List<&2, Main.Step> -> {Main.steps.go(rest, fs, ds, mv, stamp, docs2, planned2, handed2) == Done{more} : Result<&2, &2, String, List<&2, Main.Step>>} -> {Main.steps.kept(fs, more) == True{} : Bool}) -> {Main.steps.kept(fs, steps) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.steps.kept(fs, steps) == True{} : Bool}, B.fail_done_s(List<&2, Main.Step>, x, steps, e))
    case Done{+s}:
      go4(fs, s, Main.steps.go(rest, fs, ds, mv, stamp, Main.step.full(s) <> docs, T.Split{id, Main.step.id(s)} <> planned, Main.step.handed(s) <> handed), steps, e,
        step_kept(fs, ds, docs, id, prev, mapped, Main.authored.of(id, mv, stamp), s, hf, er),
        more => h => ih(Main.step.full(s) <> docs, T.Split{id, Main.step.id(s)} <> planned, Main.step.handed(s) <> handed, more, h))

def go2(+rest: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +mv: Maybe<&2, Main.Moved>, +stamp: Maybe<&2, T.Split>, +docs: List<&2, Main.Full>, +planned: List<&2, T.Split>, +handed: List<&2, Main.Handed>, +id: String, +prev: Main.Full, r: Result<&2, &2, String, List<&2, Main.Mapped>>, -steps: List<&2, Main.Step>, hf: {Main.find(fs, id) == Some{prev} : Maybe<&2, Main.Full>}, e: {Result.bind(&2, &2, String, List<&2, Main.Mapped>, List<&2, Main.Step>, r, mapped => Result.bind(&2, &2, String, Main.Step, List<&2, Main.Step>, Main.step.of(fs, ds, docs, id, prev, mapped, Main.authored.of(id, mv, stamp)), step => Result.bind(&2, &2, String, List<&2, Main.Step>, List<&2, Main.Step>, Main.steps.go(rest, fs, ds, mv, stamp, Main.step.full(step) <> docs, T.Split{id, Main.step.id(step)} <> planned, Main.step.handed(step) <> handed), more => Done{step <> more}))) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}, ih: @docs2: List<&2, Main.Full> -> @planned2: List<&2, T.Split> -> @handed2: List<&2, Main.Handed> -> @more: List<&2, Main.Step> -> {Main.steps.go(rest, fs, ds, mv, stamp, docs2, planned2, handed2) == Done{more} : Result<&2, &2, String, List<&2, Main.Step>>} -> {Main.steps.kept(fs, more) == True{} : Bool}) -> {Main.steps.kept(fs, steps) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.steps.kept(fs, steps) == True{} : Bool}, B.fail_done_s(List<&2, Main.Step>, x, steps, e))
    case Done{+mapped}:
      go3(rest, fs, ds, mv, stamp, docs, planned, handed, id, prev, mapped, Main.step.of(fs, ds, docs, id, prev, mapped, Main.authored.of(id, mv, stamp)), steps, {==}, hf, e, ih)

def go1(+rest: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +mv: Maybe<&2, Main.Moved>, +stamp: Maybe<&2, T.Split>, +docs: List<&2, Main.Full>, +planned: List<&2, T.Split>, +handed: List<&2, Main.Handed>, +id: String, f: Maybe<&2, Main.Full>, -steps: List<&2, Main.Step>, hf: {Main.find(fs, id) == f : Maybe<&2, Main.Full>}, e: {Result.bind(&2, &2, String, Main.Full, List<&2, Main.Step>, Main.held.r(f), prev => Result.bind(&2, &2, String, List<&2, Main.Mapped>, List<&2, Main.Step>, Main.mapped.all(fs, ds, planned, handed, id, mv, Main.sorted(Main.parents_of(prev))), mapped => Result.bind(&2, &2, String, Main.Step, List<&2, Main.Step>, Main.step.of(fs, ds, docs, id, prev, mapped, Main.authored.of(id, mv, stamp)), step => Result.bind(&2, &2, String, List<&2, Main.Step>, List<&2, Main.Step>, Main.steps.go(rest, fs, ds, mv, stamp, Main.step.full(step) <> docs, T.Split{id, Main.step.id(step)} <> planned, Main.step.handed(step) <> handed), more => Done{step <> more})))) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}, ih: @docs2: List<&2, Main.Full> -> @planned2: List<&2, T.Split> -> @handed2: List<&2, Main.Handed> -> @more: List<&2, Main.Step> -> {Main.steps.go(rest, fs, ds, mv, stamp, docs2, planned2, handed2) == Done{more} : Result<&2, &2, String, List<&2, Main.Step>>} -> {Main.steps.kept(fs, more) == True{} : Bool}) -> {Main.steps.kept(fs, steps) == True{} : Bool}:
  match f:
    case None{}:
      Empty.absurd({Main.steps.kept(fs, steps) == True{} : Bool}, B.fail_done_s(List<&2, Main.Step>, "a member of the plan is not held", steps, e))
    case Some{+prev}:
      go2(rest, fs, ds, mv, stamp, docs, planned, handed, id, prev, Main.mapped.all(fs, ds, planned, handed, id, mv, Main.sorted(Main.parents_of(prev))), steps, hf, e, ih)

# Every step a plan works out keeps what it restates, whatever order it
# is handed and whatever the steps before it wrote.
def steps_kept(order: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +mv: Maybe<&2, Main.Moved>, +stamp: Maybe<&2, T.Split>, +docs: List<&2, Main.Full>, +planned: List<&2, T.Split>, +handed: List<&2, Main.Handed>, -steps: List<&2, Main.Step>, e: {Main.steps.go(order, fs, ds, mv, stamp, docs, planned, handed) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}) -> {Main.steps.kept(fs, steps) == True{} : Bool}:
  match order:
    case Nil{}:
      %done_eq_str(List<&2, Main.Step>, Nil{}, steps, e) : {Main.steps.kept(fs, _) == True{} : Bool}
      {==}
    case +id <> +rest:
      go1(rest, fs, ds, mv, stamp, docs, planned, handed, id, Main.find(fs, id), steps, {==}, e,
        docs2 => planned2 => handed2 => more => h => steps_kept(rest, fs, ds, mv, stamp, docs2, planned2, handed2, more, h))

def plan4(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +c: Main.Carrying, +fuel: Nat, +mv: Maybe<&2, Main.Moved>, r: Result<&2, &2, String, List<&2, Main.Dep>>, -steps: List<&2, Main.Step>, e: {Result.bind(&2, &2, String, List<&2, Main.Dep>, List<&2, Main.Step>, r, ds2 => Main.steps.go(Main.order.go(fuel, ds2, Nil{}), fs, ds, mv, Main.carrying.stamp(c), Nil{}, Nil{}, Nil{})) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}) -> {Main.steps.kept(fs, steps) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.steps.kept(fs, steps) == True{} : Bool}, B.fail_done_s(List<&2, Main.Step>, x, steps, e))
    case Done{+ds2}:
      steps_kept(Main.order.go(fuel, ds2, Nil{}), fs, ds, mv, Main.carrying.stamp(c), Nil{}, Nil{}, Nil{}, steps, e)

def plan3(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +c: Main.Carrying, +fuel: Nat, +mv: Maybe<&2, Main.Moved>, +set: List<&2, String>, r: Result<&2, &2, String, Unit>, -steps: List<&2, Main.Step>, e: {Result.bind(&2, &2, String, Unit, List<&2, Main.Step>, r, i => Result.bind(&2, &2, String, List<&2, Main.Dep>, List<&2, Main.Step>, Main.deps.r(fs, set, set), ds2 => Main.steps.go(Main.order.go(fuel, ds2, Nil{}), fs, ds, mv, Main.carrying.stamp(c), Nil{}, Nil{}, Nil{}))) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}) -> {Main.steps.kept(fs, steps) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.steps.kept(fs, steps) == True{} : Bool}, B.fail_done_s(List<&2, Main.Step>, x, steps, e))
    case Done{i}:
      plan4(fs, ds, c, fuel, mv, Main.deps.r(fs, set, set), steps, e)

def plan2(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +c: Main.Carrying, +fuel: Nat, +mv: Maybe<&2, Main.Moved>, r: Result<&2, &2, String, List<&2, String>>, -steps: List<&2, Main.Step>, e: {Result.bind(&2, &2, String, List<&2, String>, List<&2, Main.Step>, r, start => Result.bind(&2, &2, String, Unit, List<&2, Main.Step>, Main.onto.inside(Main.sorted(Main.closure(fuel, fs, Main.sorted(start))), mv), i => Result.bind(&2, &2, String, List<&2, Main.Dep>, List<&2, Main.Step>, Main.deps.r(fs, Main.sorted(Main.closure(fuel, fs, Main.sorted(start))), Main.sorted(Main.closure(fuel, fs, Main.sorted(start)))), ds2 => Main.steps.go(Main.order.go(fuel, ds2, Nil{}), fs, ds, mv, Main.carrying.stamp(c), Nil{}, Nil{}, Nil{})))) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}) -> {Main.steps.kept(fs, steps) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.steps.kept(fs, steps) == True{} : Bool}, B.fail_done_s(List<&2, Main.Step>, x, steps, e))
    case Done{+start}:
      plan3(fs, ds, c, fuel, mv, Main.sorted(Main.closure(fuel, fs, Main.sorted(start))), Main.onto.inside(Main.sorted(Main.closure(fuel, fs, Main.sorted(start))), mv), steps, e)

def plan1(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +c: Main.Carrying, +fuel: Nat, r: Result<&2, &2, String, Maybe<&2, Main.Moved>>, -steps: List<&2, Main.Step>, e: {Result.bind(&2, &2, String, Maybe<&2, Main.Moved>, List<&2, Main.Step>, r, mv => Result.bind(&2, &2, String, List<&2, String>, List<&2, Main.Step>, Main.carrying.start(fs, c), start => Result.bind(&2, &2, String, Unit, List<&2, Main.Step>, Main.onto.inside(Main.sorted(Main.closure(fuel, fs, Main.sorted(start))), mv), i => Result.bind(&2, &2, String, List<&2, Main.Dep>, List<&2, Main.Step>, Main.deps.r(fs, Main.sorted(Main.closure(fuel, fs, Main.sorted(start))), Main.sorted(Main.closure(fuel, fs, Main.sorted(start)))), ds2 => Main.steps.go(Main.order.go(fuel, ds2, Nil{}), fs, ds, mv, Main.carrying.stamp(c), Nil{}, Nil{}, Nil{}))))) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}) -> {Main.steps.kept(fs, steps) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.steps.kept(fs, steps) == True{} : Bool}, B.fail_done_s(List<&2, Main.Step>, x, steps, e))
    case Done{+mv}:
      plan2(fs, ds, c, fuel, mv, Main.carrying.start(fs, c), steps, e)

# Every revision a carry plans keeps what it restates.
def plan_kept(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +c: Main.Carrying, -steps: List<&2, Main.Step>, e: {Main.carry.plan(fs, ds, c) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}) -> {Main.steps.kept(fs, steps) == True{} : Bool}:
  plan1(fs, ds, c, Nat.add(List.length(&2, Main.Full, fs), 1n), Main.carrying.move(fs, c), steps, e)

# Abandoning takes a line
# -----------------------

def pick_true(-A: Data, b: Bool, -x: A, -y: Main.Refused, -z: A, h: {Bool.pick(Result<&2, &2, Main.Refused, A>, b, Done{x}, Fail{y}) == Done{z} : Result<&2, &2, Main.Refused, A>}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, B.fail_done(A, y, z, h))

def pick_false(-A: Data, b: Bool, -x: Main.Refused, -y: A, -z: A, h: {Bool.pick(Result<&2, &2, Main.Refused, A>, b, Fail{x}, Done{y}) == Done{z} : Result<&2, &2, Main.Refused, A>}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, B.fail_done(A, x, z, h))

def already_ok(+fs: List<&2, Main.Full>, +id: String, -u: Unit, h: {Main.already.r(fs, id) == Done{u} : Result<&2, &2, Main.Refused, Unit>}) -> {Main.unrewritten(fs, id) == True{} : Bool}:
  pick_true(Unit, List.is_empty(&2, String, Main.successors(fs, id)), Unit{}, Main.Refused{1, Main.ab12(id) ++ " has already been rewritten, and superseding it again would leave one change with two current revisions; amend what replaced it:" ++ Main.listed12(Main.successors(fs, id))}, u, h)

def or_false(a: Bool, h: {Bool.or(a, False{}) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def one_of(ps: List<&2, String>, +p: String, h: {Bool.and(Nat.is_eq(List.length(&2, String, ps), 1n), Rev.member(ps, p)) == True{} : Bool}) -> {Main.only.one(ps, p) == True{} : Bool}:
  match ps:
    case Nil{}:
      Empty.absurd({Main.only.one(Nil{}, p) == True{} : Bool}, S.false_true(h))
    case +x <> Nil{}:
      or_false(String.eq(x, p), h)
    case x <> y <> rest:
      Empty.absurd({Main.only.one(x <> y <> rest, p) == True{} : Bool}, S.false_true(h))

def joins_ok(+n: String, +ps: List<&2, String>, +p: String, -u: Unit, h: {Main.joins.r(n, ps, Some{p}) == Done{u} : Result<&2, &2, Main.Refused, Unit>}) -> {Main.only.one(ps, p) == True{} : Bool}:
  one_of(ps, p, pick_true(Unit, Bool.and(Nat.is_eq(List.length(&2, String, ps), 1n), Rev.member(ps, p)), Unit{}, Main.Refused{1, Main.joins.msg(n)}, u, h))

def after_cons(+fs: List<&2, Main.Full>, +prev: String, +n: String, +more: List<&2, String>, -tail: List<&2, String>, e: {Done{n <> more} == Done{tail} : Result<&2, &2, Main.Refused, List<&2, String>>}, hu: {Main.unrewritten(fs, n) == True{} : Bool}, hj: {Main.only.one(Main.full.parents(Main.find(fs, n)), prev) == True{} : Bool}, hm: {Main.abandon.after(more, fs, n) == True{} : Bool}) -> {Main.abandon.after(tail, fs, prev) == True{} : Bool}:
  %B.done_eq(List<&2, String>, n <> more, tail, e) : {Main.abandon.after(_, fs, prev) == True{} : Bool}
  B.and_tt(Main.unrewritten(fs, n), Bool.and(Main.only.one(Main.full.parents(Main.find(fs, n)), prev), Main.abandon.after(more, fs, n)), hu,
    B.and_tt(Main.only.one(Main.full.parents(Main.find(fs, n)), prev), Main.abandon.after(more, fs, n), hj, hm))

def run3(+fs: List<&2, Main.Full>, +prev: String, +n: String, r: Result<&2, &2, Main.Refused, List<&2, String>>, -tail: List<&2, String>, e: {Result.bind(&2, &2, Main.Refused, List<&2, String>, List<&2, String>, r, more => Done{n <> more}) == Done{tail} : Result<&2, &2, Main.Refused, List<&2, String>>}, hu: {Main.unrewritten(fs, n) == True{} : Bool}, hj: {Main.only.one(Main.full.parents(Main.find(fs, n)), prev) == True{} : Bool}, ih: @more: List<&2, String> -> {r == Done{more} : Result<&2, &2, Main.Refused, List<&2, String>>} -> {Main.abandon.after(more, fs, n) == True{} : Bool}) -> {Main.abandon.after(tail, fs, prev) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.abandon.after(tail, fs, prev) == True{} : Bool}, B.fail_done(List<&2, String>, x, tail, e))
    case Done{+more}:
      after_cons(fs, prev, n, more, tail, e, hu, hj, ih(more, {==}))

def run2(+k: Nat, +fs: List<&2, Main.Full>, +prev: String, +n: String, r: Result<&2, &2, Main.Refused, Unit>, -tail: List<&2, String>, er: {Main.joins.r(n, Main.full.parents(Main.find(fs, n)), Some{prev}) == r : Result<&2, &2, Main.Refused, Unit>}, e: {Result.bind(&2, &2, Main.Refused, Unit, List<&2, String>, r, j => Result.bind(&2, &2, Main.Refused, List<&2, String>, List<&2, String>, Main.run.go(k, fs, n, Main.standing_on(fs, n)), more => Done{n <> more})) == Done{tail} : Result<&2, &2, Main.Refused, List<&2, String>>}, hu: {Main.unrewritten(fs, n) == True{} : Bool}, ih: @more: List<&2, String> -> {Main.run.go(k, fs, n, Main.standing_on(fs, n)) == Done{more} : Result<&2, &2, Main.Refused, List<&2, String>>} -> {Main.abandon.after(more, fs, n) == True{} : Bool}) -> {Main.abandon.after(tail, fs, prev) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.abandon.after(tail, fs, prev) == True{} : Bool}, B.fail_done(List<&2, String>, x, tail, e))
    case Done{u}:
      run3(fs, prev, n, Main.run.go(k, fs, n, Main.standing_on(fs, n)), tail, e, hu, joins_ok(n, Main.full.parents(Main.find(fs, n)), prev, u, er), ih)

def run1(+k: Nat, +fs: List<&2, Main.Full>, +prev: String, +n: String, r: Result<&2, &2, Main.Refused, Unit>, -tail: List<&2, String>, er: {Main.already.r(fs, n) == r : Result<&2, &2, Main.Refused, Unit>}, e: {Result.bind(&2, &2, Main.Refused, Unit, List<&2, String>, r, a => Result.bind(&2, &2, Main.Refused, Unit, List<&2, String>, Main.joins.r(n, Main.full.parents(Main.find(fs, n)), Some{prev}), j => Result.bind(&2, &2, Main.Refused, List<&2, String>, List<&2, String>, Main.run.go(k, fs, n, Main.standing_on(fs, n)), more => Done{n <> more}))) == Done{tail} : Result<&2, &2, Main.Refused, List<&2, String>>}, ih: @more: List<&2, String> -> {Main.run.go(k, fs, n, Main.standing_on(fs, n)) == Done{more} : Result<&2, &2, Main.Refused, List<&2, String>>} -> {Main.abandon.after(more, fs, n) == True{} : Bool}) -> {Main.abandon.after(tail, fs, prev) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.abandon.after(tail, fs, prev) == True{} : Bool}, B.fail_done(List<&2, String>, x, tail, e))
    case Done{u}:
      run2(k, fs, prev, n, Main.joins.r(n, Main.full.parents(Main.find(fs, n)), Some{prev}), tail, {==}, e, already_ok(fs, n, u, er), ih)

# The rest of a run is a line nothing has rewritten, each revision standing
# on the one before it alone.
def run_after(+fuel: Nat, +fs: List<&2, Main.Full>, +prev: String, standing: List<&2, String>, -tail: List<&2, String>, e: {Main.run.go(fuel, fs, prev, standing) == Done{tail} : Result<&2, &2, Main.Refused, List<&2, String>>}) -> {Main.abandon.after(tail, fs, prev) == True{} : Bool}:
  match fuel standing:
    case 0n Nil{}:
      %B.done_eq(List<&2, String>, Nil{}, tail, e) : {Main.abandon.after(_, fs, prev) == True{} : Bool}
      {==}
    case 0n n <> Nil{}:
      %B.done_eq(List<&2, String>, Nil{}, tail, e) : {Main.abandon.after(_, fs, prev) == True{} : Bool}
      {==}
    case 0n n <> m <> rest:
      %B.done_eq(List<&2, String>, Nil{}, tail, e) : {Main.abandon.after(_, fs, prev) == True{} : Bool}
      {==}
    case 1n+k Nil{}:
      %B.done_eq(List<&2, String>, Nil{}, tail, e) : {Main.abandon.after(_, fs, prev) == True{} : Bool}
      {==}
    case 1n+k +n <> Nil{}:
      run1(k, fs, prev, n, Main.already.r(fs, n), tail, {==}, e, more => h => run_after(k, fs, n, Main.standing_on(fs, n), more, h))
    case 1n+k +n <> +m <> +rest:
      Empty.absurd({Main.abandon.after(tail, fs, prev) == True{} : Bool}, B.fail_done(List<&2, String>, Main.Refused{1, Nat.show(List.length(&2, String, n <> m <> rest)) ++ " lines of work stand on " ++ Main.ab12(prev) ++ ", and abandoning it would abandon all of them; name the one you mean, or abandon each in turn:" ++ Main.listed12(n <> m <> rest)}, tail, e))

def pick_done_r(-A: Data, b: Bool, -x: Main.Refused, -y: A, -z: A, h: {Bool.pick(Result<&2, &2, Main.Refused, A>, b, Fail{x}, Done{y}) == Done{z} : Result<&2, &2, Main.Refused, A>}) -> {y == z : A}:
  match b:
    case True{}:
      Empty.absurd({y == z : A}, B.fail_done(A, x, z, h))
    case False{}:
      B.done_eq(A, y, z, h)

def not_false(b: Bool, h: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  %Equal.sym(Bool, b, False{}, h) : {Bool.not(_) == True{} : Bool}
  {==}

def only_line(+fs: List<&2, Main.Full>, +id: String, -run: List<&2, String>, hu: {Main.unrewritten(fs, id) == True{} : Bool}, +e: {Bool.pick(Result<&2, &2, Main.Refused, List<&2, String>>, Nat.is_lt(1n, List.length(&2, String, Main.full.parents(Main.find(fs, id)))), Fail{Main.Refused{1, Main.joins.msg(id)}}, Done{[id]}) == Done{run} : Result<&2, &2, Main.Refused, List<&2, String>>}) -> {Main.abandon.line(fs, id, True{}, run) == True{} : Bool}:
  +b = Nat.is_lt(1n, List.length(&2, String, Main.full.parents(Main.find(fs, id))))
  %pick_done_r(List<&2, String>, b, Main.Refused{1, Main.joins.msg(id)}, [id], run, e) : {Main.abandon.line(fs, id, True{}, _) == True{} : Bool}
  B.and_tt(String.eq(id, id), Bool.and(Main.unrewritten(fs, id), Bool.not(b)), S.eq_refl(id),
    B.and_tt(Main.unrewritten(fs, id), Bool.not(b), hu, not_false(b, pick_false(List<&2, String>, b, Main.Refused{1, Main.joins.msg(id)}, [id], run, e))))

def only1(+fs: List<&2, Main.Full>, +id: String, r: Result<&2, &2, Main.Refused, Unit>, -run: List<&2, String>, er: {Main.already.r(fs, id) == r : Result<&2, &2, Main.Refused, Unit>}, e: {Result.bind(&2, &2, Main.Refused, Unit, List<&2, String>, r, a => Bool.pick(Result<&2, &2, Main.Refused, List<&2, String>>, Nat.is_lt(1n, List.length(&2, String, Main.full.parents(Main.find(fs, id)))), Fail{Main.Refused{1, Main.joins.msg(id)}}, Done{[id]})) == Done{run} : Result<&2, &2, Main.Refused, List<&2, String>>}) -> {Main.abandon.line(fs, id, True{}, run) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.abandon.line(fs, id, True{}, run) == True{} : Bool}, B.fail_done(List<&2, String>, x, run, e))
    case Done{u}:
      only_line(fs, id, run, already_ok(fs, id, u, er), e)

def whole2(+fs: List<&2, Main.Full>, +id: String, r: Result<&2, &2, Main.Refused, List<&2, String>>, -run: List<&2, String>, er: {Main.run.go(Nat.add(List.length(&2, Main.Full, fs), 1n), fs, id, Main.standing_on(fs, id)) == r : Result<&2, &2, Main.Refused, List<&2, String>>}, e: {Result.bind(&2, &2, Main.Refused, List<&2, String>, List<&2, String>, r, more => Done{id <> more}) == Done{run} : Result<&2, &2, Main.Refused, List<&2, String>>}, hu: {Main.unrewritten(fs, id) == True{} : Bool}) -> {Main.abandon.line(fs, id, False{}, run) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.abandon.line(fs, id, False{}, run) == True{} : Bool}, B.fail_done(List<&2, String>, x, run, e))
    case Done{+more}:
      %B.done_eq(List<&2, String>, id <> more, run, e) : {Main.abandon.line(fs, id, False{}, _) == True{} : Bool}
      B.and_tt(String.eq(id, id), Bool.and(Main.unrewritten(fs, id), Main.abandon.after(more, fs, id)), S.eq_refl(id),
        B.and_tt(Main.unrewritten(fs, id), Main.abandon.after(more, fs, id), hu, run_after(Nat.add(List.length(&2, Main.Full, fs), 1n), fs, id, Main.standing_on(fs, id), more, er)))

def whole1(+fs: List<&2, Main.Full>, +id: String, r: Result<&2, &2, Main.Refused, Unit>, -run: List<&2, String>, er: {Main.already.r(fs, id) == r : Result<&2, &2, Main.Refused, Unit>}, e: {Result.bind(&2, &2, Main.Refused, Unit, List<&2, String>, r, a => Result.bind(&2, &2, Main.Refused, List<&2, String>, List<&2, String>, Main.run.go(Nat.add(List.length(&2, Main.Full, fs), 1n), fs, id, Main.standing_on(fs, id)), more => Done{id <> more})) == Done{run} : Result<&2, &2, Main.Refused, List<&2, String>>}) -> {Main.abandon.line(fs, id, False{}, run) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.abandon.line(fs, id, False{}, run) == True{} : Bool}, B.fail_done(List<&2, String>, x, run, e))
    case Done{u}:
      whole2(fs, id, Main.run.go(Nat.add(List.length(&2, Main.Full, fs), 1n), fs, id, Main.standing_on(fs, id)), run, {==}, e, already_ok(fs, id, u, er))

# What `abandon` plans to abandon is a line nothing has rewritten.
def plan_line(+fs: List<&2, Main.Full>, +id: String, only: Bool, -run: List<&2, String>, e: {Main.abandon.plan.r(fs, id, only) == Done{run} : Result<&2, &2, Main.Refused, List<&2, String>>}) -> {Main.abandon.line(fs, id, only, run) == True{} : Bool}:
  match only:
    case True{}:
      only1(fs, id, Main.already.r(fs, id), run, {==}, e)
    case False{}:
      whole1(fs, id, Main.already.r(fs, id), run, {==}, e)

# A reword changes the message alone
# ----------------------------------

def differs(b: Bool, +x: String, +message: String, +change: String, +parents: List<&2, String>, +author: String, +when: String, +facts: List<&2, Rev.Header>, eb: {String.eq(x, message) == b : Bool}, hne: {String.eq(Rev.write(Rev.Rev{change, Main.sorted(parents), Nil{}, author, when, None{}, None{}, facts, message}), Rev.write(Rev.Rev{change, Main.sorted(parents), Nil{}, author, when, None{}, None{}, facts, x})) == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      +hx = S.eq_true(x, message, eb)
      +hmm = Equal.trans(Bool, String.eq(Rev.write(Rev.Rev{change, Main.sorted(parents), Nil{}, author, when, None{}, None{}, facts, message}), Rev.write(Rev.Rev{change, Main.sorted(parents), Nil{}, author, when, None{}, None{}, facts, message})), String.eq(Rev.write(Rev.Rev{change, Main.sorted(parents), Nil{}, author, when, None{}, None{}, facts, message}), Rev.write(Rev.Rev{change, Main.sorted(parents), Nil{}, author, when, None{}, None{}, facts, x})), False{},
        Equal.cong(String, Bool, s => String.eq(Rev.write(Rev.Rev{change, Main.sorted(parents), Nil{}, author, when, None{}, None{}, facts, message}), Rev.write(Rev.Rev{change, Main.sorted(parents), Nil{}, author, when, None{}, None{}, facts, s})), message, x, Equal.sym(String, x, message, hx)), hne)
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, S.true_false(Equal.trans(Bool, True{}, String.eq(Rev.write(Rev.Rev{change, Main.sorted(parents), Nil{}, author, when, None{}, None{}, facts, message}), Rev.write(Rev.Rev{change, Main.sorted(parents), Nil{}, author, when, None{}, None{}, facts, message})), False{}, Equal.sym(Bool, String.eq(Rev.write(Rev.Rev{change, Main.sorted(parents), Nil{}, author, when, None{}, None{}, facts, message}), Rev.write(Rev.Rev{change, Main.sorted(parents), Nil{}, author, when, None{}, None{}, facts, message})), True{}, S.eq_refl(Rev.write(Rev.Rev{change, Main.sorted(parents), Nil{}, author, when, None{}, None{}, facts, message}))), hmm)))

def reworded(+x: String, +id: String, +change: String, +parents: List<&2, String>, +ss: List<&2, String>, +author: String, +when: String, +rb: Maybe<&2, String>, +rv: Maybe<&2, String>, +facts: List<&2, Rev.Header>, +message: String, +reviser: String, +revised: String, hne: {String.eq(Main.bare(Rev.Rev{change, parents, ss, author, when, rb, rv, facts, message}), Main.bare(Rev.Rev{change, parents, [id], author, when, Main.revised_by(reviser, author), Some{revised}, facts, x})) == False{} : Bool}) -> {Main.reword.ok(Main.Full{id, change, parents, ss, author, when, rb, rv, facts, message}, Some{x}, Rev.Rev{change, parents, [id], author, when, Main.revised_by(reviser, author), Some{revised}, facts, x}) == True{} : Bool}:
  B.and_tt(String.eq(x, x), Bool.and(Bool.not(String.eq(x, message)), Bool.and(String.eq(id, id), String.eq(Rev.write(Rev.Rev{change, Main.sorted(parents), Nil{}, author, when, None{}, None{}, facts, message}), Rev.write(Rev.Rev{change, Main.sorted(parents), Nil{}, author, when, None{}, None{}, facts, message})))), S.eq_refl(x),
    B.and_tt(Bool.not(String.eq(x, message)), Bool.and(String.eq(id, id), String.eq(Rev.write(Rev.Rev{change, Main.sorted(parents), Nil{}, author, when, None{}, None{}, facts, message}), Rev.write(Rev.Rev{change, Main.sorted(parents), Nil{}, author, when, None{}, None{}, facts, message}))), differs(String.eq(x, message), x, message, change, parents, author, when, facts, {==}, hne),
    B.and_tt(String.eq(id, id), String.eq(Rev.write(Rev.Rev{change, Main.sorted(parents), Nil{}, author, when, None{}, None{}, facts, message}), Rev.write(Rev.Rev{change, Main.sorted(parents), Nil{}, author, when, None{}, None{}, facts, message})), S.eq_refl(id), S.eq_refl(Rev.write(Rev.Rev{change, Main.sorted(parents), Nil{}, author, when, None{}, None{}, facts, message})))))

def reword3(+x: String, +id: String, +change: String, +parents: List<&2, String>, +ss: List<&2, String>, +author: String, +when: String, +rb: Maybe<&2, String>, +rv: Maybe<&2, String>, +facts: List<&2, Rev.Header>, +message: String, +reviser: String, +revised: String, r: Result<&2, &2, Main.Refused, Unit>, -doc: Rev.Rev, er: {Main.same.r(id, Rev.Rev{change, parents, ss, author, when, rb, rv, facts, message}, Rev.Rev{change, parents, [id], author, when, Main.revised_by(reviser, author), Some{revised}, facts, x}) == r : Result<&2, &2, Main.Refused, Unit>}, e: {Result.bind(&2, &2, Main.Refused, Unit, Rev.Rev, r, s => Done{Rev.Rev{change, parents, [id], author, when, Main.revised_by(reviser, author), Some{revised}, facts, x}}) == Done{doc} : Result<&2, &2, Main.Refused, Rev.Rev>}) -> {Main.reword.ok(Main.Full{id, change, parents, ss, author, when, rb, rv, facts, message}, Some{x}, doc) == True{} : Bool}:
  match r:
    case Fail{y}:
      Empty.absurd({Main.reword.ok(Main.Full{id, change, parents, ss, author, when, rb, rv, facts, message}, Some{x}, doc) == True{} : Bool}, B.fail_done(Rev.Rev, y, doc, e))
    case Done{u}:
      %B.done_eq(Rev.Rev, Rev.Rev{change, parents, [id], author, when, Main.revised_by(reviser, author), Some{revised}, facts, x}, doc, e) : {Main.reword.ok(Main.Full{id, change, parents, ss, author, when, rb, rv, facts, message}, Some{x}, _) == True{} : Bool}
      reworded(x, id, change, parents, ss, author, when, rb, rv, facts, message, reviser, revised, pick_false(Unit, String.eq(Main.bare(Rev.Rev{change, parents, ss, author, when, rb, rv, facts, message}), Main.bare(Rev.Rev{change, parents, [id], author, when, Main.revised_by(reviser, author), Some{revised}, facts, x})), Main.Refused{1, Main.ab12(id) ++ " already says exactly this, and a revision superseding one identical to itself would mean nothing"}, Unit{}, u, er))

def reword2(m: Maybe<&2, String>, +standing: List<&2, String>, +id: String, +change: String, +parents: List<&2, String>, +ss: List<&2, String>, +author: String, +when: String, +rb: Maybe<&2, String>, +rv: Maybe<&2, String>, +facts: List<&2, Rev.Header>, +message: String, +reviser: String, +revised: String, -doc: Rev.Rev, e: {Result.bind(&2, &2, Main.Refused, String, Rev.Rev, Main.reword.message.r(id, standing, m), msg => Result.bind(&2, &2, Main.Refused, Unit, Rev.Rev, Main.same.r(id, Rev.Rev{change, parents, ss, author, when, rb, rv, facts, message}, Rev.Rev{change, parents, [id], author, when, Main.revised_by(reviser, author), Some{revised}, facts, msg}), s => Done{Rev.Rev{change, parents, [id], author, when, Main.revised_by(reviser, author), Some{revised}, facts, msg}})) == Done{doc} : Result<&2, &2, Main.Refused, Rev.Rev>}) -> {Main.reword.ok(Main.Full{id, change, parents, ss, author, when, rb, rv, facts, message}, m, doc) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Main.reword.ok(Main.Full{id, change, parents, ss, author, when, rb, rv, facts, message}, None{}, doc) == True{} : Bool}, B.fail_done(Rev.Rev, Main.Refused{1, Main.some_lines(standing) ++ " work stands on " ++ Main.ab12(id) ++ ", so the folder cannot say what it holds and the act available is a reword: give -m to fix its message alone, which keeps every other fact it states:" ++ Main.listed12(standing)}, doc, e))
    case Some{+x}:
      reword3(x, id, change, parents, ss, author, when, rb, rv, facts, message, reviser, revised, Main.same.r(id, Rev.Rev{change, parents, ss, author, when, rb, rv, facts, message}, Rev.Rev{change, parents, [id], author, when, Main.revised_by(reviser, author), Some{revised}, facts, x}), doc, {==}, e)

def reword1(+fs: List<&2, Main.Full>, +standing: List<&2, String>, +m: Maybe<&2, String>, +id: String, +change: String, +parents: List<&2, String>, +ss: List<&2, String>, +author: String, +when: String, +rb: Maybe<&2, String>, +rv: Maybe<&2, String>, +facts: List<&2, Rev.Header>, +message: String, +reviser: String, +revised: String, r: Result<&2, &2, Main.Refused, Unit>, -doc: Rev.Rev, e: {Result.bind(&2, &2, Main.Refused, Unit, Rev.Rev, r, a => Result.bind(&2, &2, Main.Refused, String, Rev.Rev, Main.reword.message.r(id, standing, m), msg => Result.bind(&2, &2, Main.Refused, Unit, Rev.Rev, Main.same.r(id, Rev.Rev{change, parents, ss, author, when, rb, rv, facts, message}, Rev.Rev{change, parents, [id], author, when, Main.revised_by(reviser, author), Some{revised}, facts, msg}), s => Done{Rev.Rev{change, parents, [id], author, when, Main.revised_by(reviser, author), Some{revised}, facts, msg}}))) == Done{doc} : Result<&2, &2, Main.Refused, Rev.Rev>}) -> {Main.reword.ok(Main.Full{id, change, parents, ss, author, when, rb, rv, facts, message}, m, doc) == True{} : Bool}:
  match r:
    case Fail{y}:
      Empty.absurd({Main.reword.ok(Main.Full{id, change, parents, ss, author, when, rb, rv, facts, message}, m, doc) == True{} : Bool}, B.fail_done(Rev.Rev, y, doc, e))
    case Done{u}:
      reword2(m, standing, id, change, parents, ss, author, when, rb, rv, facts, message, reviser, revised, doc, e)

# What a reword writes changes the message alone.
def reword_ok(+fs: List<&2, Main.Full>, prev: Main.Full, +standing: List<&2, String>, +m: Maybe<&2, String>, +reviser: String, +revised: String, -doc: Rev.Rev, e: {Main.reword.r(fs, prev, standing, m, reviser, revised) == Done{doc} : Result<&2, &2, Main.Refused, Rev.Rev>}) -> {Main.reword.ok(prev, m, doc) == True{} : Bool}:
  match prev:
    case Main.Full{+id, +change, +parents, +ss, +author, +when, +rb, +rv, +facts, +message}:
      reword1(fs, standing, m, id, change, parents, ss, author, when, rb, rv, facts, message, reviser, revised, Main.already.r(fs, id), doc, e)

# What is rewritten is held
# -------------------------

def head_held(+fs: List<&2, Main.Full>, h: Maybe<&2, String>, +f: Main.Full, e: {Main.amend.head.r(fs, h) == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}) -> {Rev.member(Main.ids(fs), Main.id_of(f)) == True{} : Bool}:
  match h:
    case None{}:
      Empty.absurd({Rev.member(Main.ids(fs), Main.id_of(f)) == True{} : Bool}, B.fail_done(Main.Full, Main.Refused{1, "this store holds no revisions yet, so there is nothing to rewrite"}, f, e))
    case Some{+id}:
      B.found_mem(fs, id, Main.find(fs, id), {==}, f, e)

def the_head_held(+fs: List<&2, Main.Full>, r: Result<&2, &2, Main.Refused, Maybe<&2, String>>, +f: Main.Full, e: {Result.bind(&2, &2, Main.Refused, Maybe<&2, String>, Main.Full, r, h => Main.amend.head.r(fs, h)) == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}) -> {Rev.member(Main.ids(fs), Main.id_of(f)) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Rev.member(Main.ids(fs), Main.id_of(f)) == True{} : Bool}, B.fail_done(Main.Full, x, f, e))
    case Done{h}:
      head_held(fs, h, f, e)

# What `amend` rewrites is a revision the store holds.
def amend_held(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, named: Maybe<&2, String>, +f: Main.Full, e: {Main.amend.target.r(fs, bs, named) == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}) -> {Rev.member(Main.ids(fs), Main.id_of(f)) == True{} : Bool}:
  match named:
    case Some{+s}:
      B.resolved_mem(fs, bs, s, f, e)
    case None{}:
      the_head_held(fs, Main.the_head.r(fs, bs, Main.current_heads(Main.history(fs))), f, e)

def nonedisc(r: Result<&2, &2, Main.Refused, Maybe<&2, String>>) -> Type:
  match r:
    case Done{None{}}:
      Unit
    case _:
      Empty

def none_some(-id: String, h: {Done{None{}} == Done{Some{id}} : Result<&2, &2, Main.Refused, Maybe<&2, String>>}) -> Empty:
  %h : {nonedisc(_) : Type}
  Unit{}

def some_eq(-a: String, -b: String, h: {Done{Some{a}} == Done{Some{b}} : Result<&2, &2, Main.Refused, Maybe<&2, String>>}) -> {a == b : String}:
  Equal.cong(Result<&2, &2, Main.Refused, Maybe<&2, String>>, String, r => Maybe.default(&2, String, Result.default(&2, &2, Main.Refused, Maybe<&2, String>, r, None{}), a), Done{Some{a}}, Done{Some{b}}, h)

def carried_held(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +s: String, r: Result<&2, &2, Main.Refused, Main.Full>, +id: String, er: {Main.resolved.r(fs, bs, s) == r : Result<&2, &2, Main.Refused, Main.Full>}, e: {Result.map(&2, &2, Main.Refused, Main.Full, Maybe<&2, String>, f => Some{Main.id_of(f)}, r) == Done{Some{id}} : Result<&2, &2, Main.Refused, Maybe<&2, String>>}) -> {Rev.member(Main.ids(fs), id) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Rev.member(Main.ids(fs), id) == True{} : Bool}, B.fail_done(Maybe<&2, String>, x, Some{id}, e))
    case Done{+f}:
      %some_eq(Main.id_of(f), id, e) : {Rev.member(Main.ids(fs), _) == True{} : Bool}
      B.resolved_mem(fs, bs, s, f, er)

# What `carry` is asked to carry is a revision the store holds.
def carry_held(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, named: Maybe<&2, String>, +id: String, e: {Main.carry.target.r(fs, bs, named) == Done{Some{id}} : Result<&2, &2, Main.Refused, Maybe<&2, String>>}) -> {Rev.member(Main.ids(fs), id) == True{} : Bool}:
  match named:
    case None{}:
      Empty.absurd({Rev.member(Main.ids(fs), id) == True{} : Bool}, none_some(id, e))
    case Some{+s}:
      carried_held(fs, bs, s, Main.resolved.r(fs, bs, s), id, {==}, e)
