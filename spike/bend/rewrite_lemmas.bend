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
