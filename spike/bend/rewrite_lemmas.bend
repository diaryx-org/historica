# What `amend`, `abandon` and `carry` decide before they write, and what
# they say of it.
#
# A carry reports each revision it writes by the name the store will read
# it back under: the digest of the bytes it files, which `step.made` names
# it by and `carry.write` files.
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
import ./sort_lemmas.bend as SortL
import ./status_lemmas.bend as StatusL
import ./survey.bend as Sv
import ./fetch_lemmas.bend as FetchL
import ./chain_lemmas.bend as ChainL
import ./diff_lemmas.bend as Diff

def rdisc_s(-A: Data, r: Result<&2, &2, String, A>) -> Type:
  match r:
    case Done{x}:
      Empty
    case Fail{e}:
      Unit

def done_eq_str(-A: Data, -a: A, -b: A, h: {Done{a} == Done{b} : Result<&2, &2, String, A>}) -> {a == b : A}:
  Equal.cong(Result<&2, &2, String, A>, A, r => Result.default(&2, &2, String, A, r, a), Done{a}, Done{b}, h)

# What carrying says it files
# ---------------------------

# The store's name for a document is the digest of its bytes, wherever it
# is filed.
def named_by_digest(+path: String, bs: List<&2, U32>) -> {Store.id_of(Store.doc_of(path, bs)) == Sha.digest(bs) : String}:
  {==}

# A step reports as its identifier what the store will call its text.
def made_filed(+path: String, +id: String, +change: String, +author: String, +when: String, +message: String, w: Main.Worked) -> {Main.step.id(Main.step.made(id, change, author, when, message, w)) == Main.step.filed(path, Main.step.made(id, change, author, when, message, w)) : String}:
  match w:
    case Main.Worked{+parents, +nf, +stamp, onto, restated, writes, moving}:
      +text = Rev.write(Rev.Rev{change, parents, [id], author, when, Main.revised_by(Main.split.rest(stamp), author), Some{Main.split.head(stamp)}, nf, message})
      Equal.sym(String, Store.id_of(Store.doc_of(path, Utf8.encode(text))), Sha.digest(Utf8.encode(text)), named_by_digest(path, Utf8.encode(text)))

def mapped_filed(+path: String, +id: String, +change: String, +author: String, +when: String, +message: String, r: Result<&2, &2, String, Main.Worked>, +s: Main.Step, e: {Result.map(&2, &2, String, Main.Worked, Main.Step, w => Main.step.made(id, change, author, when, message, w), r) == Done{s} : Result<&2, &2, String, Main.Step>}) -> {Main.step.id(s) == Main.step.filed(path, s) : String}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.step.id(s) == Main.step.filed(path, s) : String}, B.fail_done_s(Main.Step, x, s, e))
    case Done{+w}:
      %done_eq_str(Main.Step, Main.step.made(id, change, author, when, message, w), s, e) : {Main.step.id(_) == Main.step.filed(path, _) : String}
      made_filed(path, id, change, author, when, message, w)

# The step `step.of` works out reports what the store will call its text.
def step_filed(+path: String, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +docs: List<&2, Main.Full>, +id: String, prev: Main.Full, +mapped: List<&2, Main.Mapped>, +authored: Maybe<&2, T.Split>, +s: Main.Step, e: {Main.step.of(fs, ds, docs, id, prev, mapped, authored) == Done{s} : Result<&2, &2, String, Main.Step>}) -> {Main.step.id(s) == Main.step.filed(path, s) : String}:
  match prev:
    case Main.Full{+i, +change, +ps, +ss, +author, +when, +rb, +rv, +facts, +message}:
      mapped_filed(path, id, change, author, when, message, Main.step.worked(fs, ds, docs, id, ps, facts, mapped, authored), s, e)

def filed_one(+path: String, s: Main.Step, +more: List<&2, Main.Step>, hs: {Main.step.id(s) == Main.step.filed(path, s) : String}, hm: {Main.carried.ids(more) == Main.steps.filed(path, more) : List<&2, String>}) -> {Main.carried.ids(s <> more) == Main.steps.filed(path, s <> more) : List<&2, String>}:
  match s:
    case Main.Step{+p, +id, +o, +d, +r, +w, +m}:
      Equal.trans(List<&2, String>, id <> Main.carried.ids(more), Main.step.filed(path, Main.Step{p, id, o, d, r, w, m}) <> Main.carried.ids(more), Main.step.filed(path, Main.Step{p, id, o, d, r, w, m}) <> Main.steps.filed(path, more),
        Equal.cong(String, List<&2, String>, x => x <> Main.carried.ids(more), id, Main.step.filed(path, Main.Step{p, id, o, d, r, w, m}), hs),
        Equal.cong(List<&2, String>, List<&2, String>, l => Main.step.filed(path, Main.Step{p, id, o, d, r, w, m}) <> l, Main.carried.ids(more), Main.steps.filed(path, more), hm))

def filed_cons(+path: String, +s: Main.Step, +more: List<&2, Main.Step>, -steps: List<&2, Main.Step>, e: {Done{s <> more} == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}, hs: {Main.step.id(s) == Main.step.filed(path, s) : String}, hm: {Main.carried.ids(more) == Main.steps.filed(path, more) : List<&2, String>}) -> {Main.carried.ids(steps) == Main.steps.filed(path, steps) : List<&2, String>}:
  %done_eq_str(List<&2, Main.Step>, s <> more, steps, e) : {Main.carried.ids(_) == Main.steps.filed(path, _) : List<&2, String>}
  filed_one(path, s, more, hs, hm)

def fgo4(+path: String, +s: Main.Step, r: Result<&2, &2, String, List<&2, Main.Step>>, -steps: List<&2, Main.Step>, e: {Result.bind(&2, &2, String, List<&2, Main.Step>, List<&2, Main.Step>, r, more => Done{s <> more}) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}, hs: {Main.step.id(s) == Main.step.filed(path, s) : String}, ih: @more: List<&2, Main.Step> -> {r == Done{more} : Result<&2, &2, String, List<&2, Main.Step>>} -> {Main.carried.ids(more) == Main.steps.filed(path, more) : List<&2, String>}) -> {Main.carried.ids(steps) == Main.steps.filed(path, steps) : List<&2, String>}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.carried.ids(steps) == Main.steps.filed(path, steps) : List<&2, String>}, B.fail_done_s(List<&2, Main.Step>, x, steps, e))
    case Done{+more}:
      filed_cons(path, s, more, steps, e, hs, ih(more, {==}))

def fgo3(+path: String, +rest: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +mv: Maybe<&2, Main.Moved>, +stamp: Maybe<&2, T.Split>, +docs: List<&2, Main.Full>, +planned: List<&2, T.Split>, +handed: List<&2, Main.Handed>, +id: String, prev: Main.Full, +mapped: List<&2, Main.Mapped>, r: Result<&2, &2, String, Main.Step>, -steps: List<&2, Main.Step>, er: {Main.step.of(fs, ds, docs, id, prev, mapped, Main.authored.of(id, mv, stamp)) == r : Result<&2, &2, String, Main.Step>}, e: {Result.bind(&2, &2, String, Main.Step, List<&2, Main.Step>, r, step => Result.bind(&2, &2, String, List<&2, Main.Step>, List<&2, Main.Step>, Main.steps.go(rest, fs, ds, mv, stamp, Main.step.full(step) <> docs, T.Split{id, Main.step.id(step)} <> planned, Main.step.handed(step) <> handed), more => Done{step <> more})) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}, ih: @docs2: List<&2, Main.Full> -> @planned2: List<&2, T.Split> -> @handed2: List<&2, Main.Handed> -> @more: List<&2, Main.Step> -> {Main.steps.go(rest, fs, ds, mv, stamp, docs2, planned2, handed2) == Done{more} : Result<&2, &2, String, List<&2, Main.Step>>} -> {Main.carried.ids(more) == Main.steps.filed(path, more) : List<&2, String>}) -> {Main.carried.ids(steps) == Main.steps.filed(path, steps) : List<&2, String>}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.carried.ids(steps) == Main.steps.filed(path, steps) : List<&2, String>}, B.fail_done_s(List<&2, Main.Step>, x, steps, e))
    case Done{+s}:
      fgo4(path, s, Main.steps.go(rest, fs, ds, mv, stamp, Main.step.full(s) <> docs, T.Split{id, Main.step.id(s)} <> planned, Main.step.handed(s) <> handed), steps, e,
        step_filed(path, fs, ds, docs, id, prev, mapped, Main.authored.of(id, mv, stamp), s, er),
        more => h => ih(Main.step.full(s) <> docs, T.Split{id, Main.step.id(s)} <> planned, Main.step.handed(s) <> handed, more, h))

def fgo2(+path: String, +rest: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +mv: Maybe<&2, Main.Moved>, +stamp: Maybe<&2, T.Split>, +docs: List<&2, Main.Full>, +planned: List<&2, T.Split>, +handed: List<&2, Main.Handed>, +id: String, +prev: Main.Full, r: Result<&2, &2, String, List<&2, Main.Mapped>>, -steps: List<&2, Main.Step>, e: {Result.bind(&2, &2, String, List<&2, Main.Mapped>, List<&2, Main.Step>, r, mapped => Result.bind(&2, &2, String, Main.Step, List<&2, Main.Step>, Main.step.of(fs, ds, docs, id, prev, mapped, Main.authored.of(id, mv, stamp)), step => Result.bind(&2, &2, String, List<&2, Main.Step>, List<&2, Main.Step>, Main.steps.go(rest, fs, ds, mv, stamp, Main.step.full(step) <> docs, T.Split{id, Main.step.id(step)} <> planned, Main.step.handed(step) <> handed), more => Done{step <> more}))) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}, ih: @docs2: List<&2, Main.Full> -> @planned2: List<&2, T.Split> -> @handed2: List<&2, Main.Handed> -> @more: List<&2, Main.Step> -> {Main.steps.go(rest, fs, ds, mv, stamp, docs2, planned2, handed2) == Done{more} : Result<&2, &2, String, List<&2, Main.Step>>} -> {Main.carried.ids(more) == Main.steps.filed(path, more) : List<&2, String>}) -> {Main.carried.ids(steps) == Main.steps.filed(path, steps) : List<&2, String>}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.carried.ids(steps) == Main.steps.filed(path, steps) : List<&2, String>}, B.fail_done_s(List<&2, Main.Step>, x, steps, e))
    case Done{+mapped}:
      fgo3(path, rest, fs, ds, mv, stamp, docs, planned, handed, id, prev, mapped, Main.step.of(fs, ds, docs, id, prev, mapped, Main.authored.of(id, mv, stamp)), steps, {==}, e, ih)

def fgo1(+path: String, +rest: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +mv: Maybe<&2, Main.Moved>, +stamp: Maybe<&2, T.Split>, +docs: List<&2, Main.Full>, +planned: List<&2, T.Split>, +handed: List<&2, Main.Handed>, +id: String, f: Maybe<&2, Main.Full>, -steps: List<&2, Main.Step>, e: {Result.bind(&2, &2, String, Main.Full, List<&2, Main.Step>, Main.held.r(f), prev => Result.bind(&2, &2, String, List<&2, Main.Mapped>, List<&2, Main.Step>, Main.mapped.all(fs, ds, planned, handed, id, mv, Main.sorted(Main.parents_of(prev))), mapped => Result.bind(&2, &2, String, Main.Step, List<&2, Main.Step>, Main.step.of(fs, ds, docs, id, prev, mapped, Main.authored.of(id, mv, stamp)), step => Result.bind(&2, &2, String, List<&2, Main.Step>, List<&2, Main.Step>, Main.steps.go(rest, fs, ds, mv, stamp, Main.step.full(step) <> docs, T.Split{id, Main.step.id(step)} <> planned, Main.step.handed(step) <> handed), more => Done{step <> more})))) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}, ih: @docs2: List<&2, Main.Full> -> @planned2: List<&2, T.Split> -> @handed2: List<&2, Main.Handed> -> @more: List<&2, Main.Step> -> {Main.steps.go(rest, fs, ds, mv, stamp, docs2, planned2, handed2) == Done{more} : Result<&2, &2, String, List<&2, Main.Step>>} -> {Main.carried.ids(more) == Main.steps.filed(path, more) : List<&2, String>}) -> {Main.carried.ids(steps) == Main.steps.filed(path, steps) : List<&2, String>}:
  match f:
    case None{}:
      Empty.absurd({Main.carried.ids(steps) == Main.steps.filed(path, steps) : List<&2, String>}, B.fail_done_s(List<&2, Main.Step>, "a member of the plan is not held", steps, e))
    case Some{+prev}:
      fgo2(path, rest, fs, ds, mv, stamp, docs, planned, handed, id, prev, Main.mapped.all(fs, ds, planned, handed, id, mv, Main.sorted(Main.parents_of(prev))), steps, e, ih)

# Every step a plan works out reports what the store will call its text,
# whatever order it is handed and whatever the steps before it wrote.
def steps_filed(+path: String, order: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +mv: Maybe<&2, Main.Moved>, +stamp: Maybe<&2, T.Split>, +docs: List<&2, Main.Full>, +planned: List<&2, T.Split>, +handed: List<&2, Main.Handed>, -steps: List<&2, Main.Step>, e: {Main.steps.go(order, fs, ds, mv, stamp, docs, planned, handed) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}) -> {Main.carried.ids(steps) == Main.steps.filed(path, steps) : List<&2, String>}:
  match order:
    case Nil{}:
      %done_eq_str(List<&2, Main.Step>, Nil{}, steps, e) : {Main.carried.ids(_) == Main.steps.filed(path, _) : List<&2, String>}
      {==}
    case +id <> +rest:
      fgo1(path, rest, fs, ds, mv, stamp, docs, planned, handed, id, Main.find(fs, id), steps, e,
        docs2 => planned2 => handed2 => more => h => steps_filed(path, rest, fs, ds, mv, stamp, docs2, planned2, handed2, more, h))

def fplan4(+path: String, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +c: Main.Carrying, +fuel: Nat, +mv: Maybe<&2, Main.Moved>, r: Result<&2, &2, String, List<&2, Main.Dep>>, -steps: List<&2, Main.Step>, e: {Result.bind(&2, &2, String, List<&2, Main.Dep>, List<&2, Main.Step>, r, ds2 => Main.steps.go(Main.order.go(fuel, ds2, Nil{}), fs, ds, mv, Main.carrying.stamp(c), Nil{}, Nil{}, Nil{})) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}) -> {Main.carried.ids(steps) == Main.steps.filed(path, steps) : List<&2, String>}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.carried.ids(steps) == Main.steps.filed(path, steps) : List<&2, String>}, B.fail_done_s(List<&2, Main.Step>, x, steps, e))
    case Done{+ds2}:
      steps_filed(path, Main.order.go(fuel, ds2, Nil{}), fs, ds, mv, Main.carrying.stamp(c), Nil{}, Nil{}, Nil{}, steps, e)

def fplan3(+path: String, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +c: Main.Carrying, +fuel: Nat, +mv: Maybe<&2, Main.Moved>, +set: List<&2, String>, r: Result<&2, &2, String, Unit>, -steps: List<&2, Main.Step>, e: {Result.bind(&2, &2, String, Unit, List<&2, Main.Step>, r, i => Result.bind(&2, &2, String, List<&2, Main.Dep>, List<&2, Main.Step>, Main.deps.r(fs, set, set), ds2 => Main.steps.go(Main.order.go(fuel, ds2, Nil{}), fs, ds, mv, Main.carrying.stamp(c), Nil{}, Nil{}, Nil{}))) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}) -> {Main.carried.ids(steps) == Main.steps.filed(path, steps) : List<&2, String>}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.carried.ids(steps) == Main.steps.filed(path, steps) : List<&2, String>}, B.fail_done_s(List<&2, Main.Step>, x, steps, e))
    case Done{i}:
      fplan4(path, fs, ds, c, fuel, mv, Main.deps.r(fs, set, set), steps, e)

def fplan2(+path: String, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +c: Main.Carrying, +fuel: Nat, +mv: Maybe<&2, Main.Moved>, r: Result<&2, &2, String, List<&2, String>>, -steps: List<&2, Main.Step>, e: {Result.bind(&2, &2, String, List<&2, String>, List<&2, Main.Step>, r, start => Result.bind(&2, &2, String, Unit, List<&2, Main.Step>, Main.onto.inside(Main.sorted(Main.closure(fuel, fs, Main.sorted(start))), mv), i => Result.bind(&2, &2, String, List<&2, Main.Dep>, List<&2, Main.Step>, Main.deps.r(fs, Main.sorted(Main.closure(fuel, fs, Main.sorted(start))), Main.sorted(Main.closure(fuel, fs, Main.sorted(start)))), ds2 => Main.steps.go(Main.order.go(fuel, ds2, Nil{}), fs, ds, mv, Main.carrying.stamp(c), Nil{}, Nil{}, Nil{})))) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}) -> {Main.carried.ids(steps) == Main.steps.filed(path, steps) : List<&2, String>}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.carried.ids(steps) == Main.steps.filed(path, steps) : List<&2, String>}, B.fail_done_s(List<&2, Main.Step>, x, steps, e))
    case Done{+start}:
      fplan3(path, fs, ds, c, fuel, mv, Main.sorted(Main.closure(fuel, fs, Main.sorted(start))), Main.onto.inside(Main.sorted(Main.closure(fuel, fs, Main.sorted(start))), mv), steps, e)

def fplan1(+path: String, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +c: Main.Carrying, +fuel: Nat, r: Result<&2, &2, String, Maybe<&2, Main.Moved>>, -steps: List<&2, Main.Step>, e: {Result.bind(&2, &2, String, Maybe<&2, Main.Moved>, List<&2, Main.Step>, r, mv => Result.bind(&2, &2, String, List<&2, String>, List<&2, Main.Step>, Main.carrying.start(fs, c), start => Result.bind(&2, &2, String, Unit, List<&2, Main.Step>, Main.onto.inside(Main.sorted(Main.closure(fuel, fs, Main.sorted(start))), mv), i => Result.bind(&2, &2, String, List<&2, Main.Dep>, List<&2, Main.Step>, Main.deps.r(fs, Main.sorted(Main.closure(fuel, fs, Main.sorted(start))), Main.sorted(Main.closure(fuel, fs, Main.sorted(start)))), ds2 => Main.steps.go(Main.order.go(fuel, ds2, Nil{}), fs, ds, mv, Main.carrying.stamp(c), Nil{}, Nil{}, Nil{}))))) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}) -> {Main.carried.ids(steps) == Main.steps.filed(path, steps) : List<&2, String>}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.carried.ids(steps) == Main.steps.filed(path, steps) : List<&2, String>}, B.fail_done_s(List<&2, Main.Step>, x, steps, e))
    case Done{+mv}:
      fplan2(path, fs, ds, c, fuel, mv, Main.carrying.start(fs, c), steps, e)

# Every revision a carry plans reports what the store will call its text.
def plan_filed(+path: String, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +c: Main.Carrying, -steps: List<&2, Main.Step>, e: {Main.carry.plan(fs, ds, c) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}) -> {Main.carried.ids(steps) == Main.steps.filed(path, steps) : List<&2, String>}:
  fplan1(path, fs, ds, c, Nat.add(List.length(&2, Main.Full, fs), 1n), Main.carrying.move(fs, c), steps, e)

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

# What is rewritten is what was asked for
# ----------------------------------------

# A result that is not `Done` is not the one a command went on with.
def not_done(-A: Data, -r: Result<&2, &2, Main.Refused, A>, -x: A, e: {r == Done{x} : Result<&2, &2, Main.Refused, A>}, u: B.rdisc(A, r)) -> Empty:
  %e : {B.rdisc(A, _) : Type}
  u

# What `find` finds under an identifier is filed under it.
def found_is(+fs: List<&2, Main.Full>, +id: String, m: Maybe<&2, Main.Full>, em: {Main.find(fs, id) == m : Maybe<&2, Main.Full>}, -f: Main.Full, e: {Main.resolved.found.r(id, m) == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}) -> {id == Main.id_of(f) : String}:
  match m:
    case None{}:
      Empty.absurd({id == Main.id_of(f) : String}, not_done(Main.Full, Main.resolved.found.r(id, None{}), f, e, Unit{}))
    case Some{+g}:
      %B.done_eq(Main.Full, g, f, e) : {id == Main.id_of(_) : String}
      S.eq_true(id, Main.id_of(g), ChainL.find_id(fs, id, g, em))

def named_is(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +s: String, r: Result<&2, &2, String, String>, er: {Main.resolve(fs, bs, s) == r : Result<&2, &2, String, String>}, -f: Main.Full, e: {Main.resolved.of.r(fs, r) == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}) -> {Main.resolve(fs, bs, s) == Done{Main.id_of(f)} : Result<&2, &2, String, String>}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.resolve(fs, bs, s) == Done{Main.id_of(f)} : Result<&2, &2, String, String>}, not_done(Main.Full, Main.resolved.of.r(fs, Fail{x}), f, e, Unit{}))
    case Done{+id}:
      Equal.trans(Result<&2, &2, String, String>, Main.resolve(fs, bs, s), Done{id}, Done{Main.id_of(f)}, er,
        Equal.cong(String, Result<&2, &2, String, String>, y => Done{y}, id, Main.id_of(f), found_is(fs, id, Main.find(fs, id), {==}, f, e)))

# What `amend` rewrites, where a target is named, is the revision that
# target resolves to.
def amend_named(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +s: String, -f: Main.Full, e: {Main.amend.target.r(fs, bs, Some{s}) == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}) -> {Main.resolve(fs, bs, s) == Done{Main.id_of(f)} : Result<&2, &2, String, String>}:
  named_is(fs, bs, s, Main.resolve(fs, bs, s), {==}, f, e)

def one_head(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, heads: List<&2, String>, -f: Main.Full, e: {Result.bind(&2, &2, Main.Refused, Maybe<&2, String>, Main.Full, Main.the_head.r(fs, bs, heads), h => Main.amend.head.r(fs, h)) == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}) -> {heads == [Main.id_of(f)] : List<&2, String>}:
  match heads:
    case Nil{}:
      Empty.absurd({Nil{} == [Main.id_of(f)] : List<&2, String>}, not_done(Main.Full, Main.amend.head.r(fs, None{}), f, e, Unit{}))
    case +x <> Nil{}:
      Equal.cong(String, List<&2, String>, y => [y], x, Main.id_of(f), found_is(fs, x, Main.find(fs, x), {==}, f, e))
    case +x <> +y <> +rest:
      Empty.absurd({x <> y <> rest == [Main.id_of(f)] : List<&2, String>}, not_done(Main.Full, Result.bind(&2, &2, Main.Refused, Maybe<&2, String>, Main.Full, Main.the_head.r(fs, bs, x <> y <> rest), h => Main.amend.head.r(fs, h)), f, e, Unit{}))

# With no target named, what `amend` rewrites is the one current head.
def amend_head(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, -f: Main.Full, e: {Main.amend.target.r(fs, bs, None{}) == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}) -> {Main.current_heads(Main.history(fs)) == [Main.id_of(f)] : List<&2, String>}:
  one_head(fs, bs, Main.current_heads(Main.history(fs)), f, e)

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

# What `--fields` says they wrote
# -------------------------------

def strip_nil(x: String) -> {T.strip_prefix(x, SNil{}) == Some{x} : Maybe<&2, String>}:
  match x:
    case SNil{}:
      {==}
    case SCon{c, t}:
      {==}

def str_app_nil(x: String) -> {String.append(x, SNil{}) == x : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      Equal.cong(String, String, y => SCon{c, y}, String.append(t, SNil{}), t, str_app_nil(t))

# A `revision` line says the revision it names.
def revs_said(xs: List<&2, String>) -> {Main.fields.revisions(Main.said.lines("revision ", SNil{}, xs)) == xs : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Maybe<&2, String>, T.strip_prefix(String.append(x, SNil{}), SNil{}), Some{String.append(x, SNil{})}, strip_nil(String.append(x, SNil{}))) : {Main.fields.revision(_, Main.fields.revisions(Main.said.lines("revision ", SNil{}, rest))) == x <> rest : List<&2, String>}
      %Equal.sym(String, String.append(x, SNil{}), x, str_app_nil(x)) : {_ <> Main.fields.revisions(Main.said.lines("revision ", SNil{}, rest)) == x <> rest : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, l => x <> l, Main.fields.revisions(Main.said.lines("revision ", SNil{}, rest)), rest, revs_said(rest))

# A `name` line names no revision.
def names_said(ys: List<&2, String>) -> {Main.fields.revisions(Main.said.lines("name ", SNil{}, ys)) == Nil{} : List<&2, String>}:
  match ys:
    case Nil{}:
      {==}
    case y <> rest:
      names_said(rest)

def revision_app(r: Maybe<&2, String>, +a: List<&2, String>, +b: List<&2, String>) -> {Main.fields.revision(r, List.append(&2, String, a, b)) == List.append(&2, String, Main.fields.revision(r, a), b) : List<&2, String>}:
  match r:
    case Some{x}:
      {==}
    case None{}:
      {==}

def revs_app(xs: List<&2, String>, +ys: List<&2, String>) -> {Main.fields.revisions(List.append(&2, String, xs, ys)) == List.append(&2, String, Main.fields.revisions(xs), Main.fields.revisions(ys)) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case +l <> +rest:
      %Equal.sym(List<&2, String>, Main.fields.revisions(List.append(&2, String, rest, ys)), List.append(&2, String, Main.fields.revisions(rest), Main.fields.revisions(ys)), revs_app(rest, ys)) : {Main.fields.revision(T.strip_prefix(l, "revision "), _) == List.append(&2, String, Main.fields.revision(T.strip_prefix(l, "revision "), Main.fields.revisions(rest)), Main.fields.revisions(ys)) : List<&2, String>}
      revision_app(T.strip_prefix(l, "revision "), Main.fields.revisions(rest), Main.fields.revisions(ys))

def mem_head(+f: String, +rest: List<&2, String>) -> {Rev.member(f <> rest, f) == True{} : Bool}:
  %Equal.sym(Bool, String.eq(f, f), True{}, S.eq_refl(f)) : {Bool.or(_, Rev.member(rest, f)) == True{} : Bool}
  {==}

# Every list names each of its own members.
def held_refl(xs: List<&2, String>) -> {Main.all_held(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      B.and_tt(Rev.member(x <> rest, x), Main.all_held(x <> rest, rest), mem_head(x, rest), StatusL.ah_weak(x, rest, rest, held_refl(rest)))

def dist_held(+xs: List<&2, String>) -> {Main.all_held(xs, Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs))) == True{} : Bool}:
  StatusL.ah_distinct(xs, List.sort(~String, ~(a => b => String.is_le(a, b)), xs), StatusL.ah_sort(~(a => b => String.is_le(a, b)), xs, xs, held_refl(xs)))

def dh_keep(e: Bool, +a: String, +b: String, +rest: List<&2, String>, ee: {String.eq(a, b) == e : Bool}, ih: {List.head(&2, String, Main.distinct(b <> rest)) == Some{b} : Maybe<&2, String>}) -> {List.head(&2, String, Main.distinct.keep(a, Main.distinct(b <> rest), e)) == Some{a} : Maybe<&2, String>}:
  match e:
    case True{}:
      Equal.trans(Maybe<&2, String>, List.head(&2, String, Main.distinct(b <> rest)), Some{b}, Some{a}, ih,
        Equal.cong(String, Maybe<&2, String>, x => Some{x}, b, a, Equal.sym(String, a, b, S.eq_true(a, b, ee))))
    case False{}:
      {==}

# What `distinct` keeps first is what it was given first.
def dist_head(ys: List<&2, String>) -> {List.head(&2, String, Main.distinct(ys)) == List.head(&2, String, ys) : Maybe<&2, String>}:
  match ys:
    case Nil{}:
      {==}
    case a <> Nil{}:
      {==}
    case +a <> +b <> +rest:
      dh_keep(String.eq(a, b), a, b, rest, {==}, dist_head(b <> rest))

def msome_eq(-a: String, -b: String, h: {Some{a} == Some{b} : Maybe<&2, String>}) -> {a == b : String}:
  Equal.cong(Maybe<&2, String>, String, m => Maybe.default(&2, String, m, a), Some{a}, Some{b}, h)

def mnone(m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some_m(-b: String, h: {None{} == Some{b} : Maybe<&2, String>}) -> Empty:
  %h : {mnone(_) : Type}
  Unit{}

def from_head(ds: List<&2, String>, +a: String, +b: String, hab: {String.is_le(a, b) == True{} : Bool}, ee: {String.eq(a, b) == False{} : Bool}, hh: {List.head(&2, String, ds) == Some{b} : Maybe<&2, String>}, ih: {Main.rising(ds) == True{} : Bool}) -> {Main.rising.from(ds, a) == True{} : Bool}:
  match ds:
    case Nil{}:
      Empty.absurd({Main.rising.from(Nil{}, a) == True{} : Bool}, none_some_m(b, hh))
    case +d <> rest:
      %Equal.sym(String, d, b, msome_eq(d, b, hh)) : {Bool.and(Bool.and(String.is_le(a, _), Bool.not(String.eq(a, _))), Main.rising.from(rest, d)) == True{} : Bool}
      B.and_tt(Bool.and(String.is_le(a, b), Bool.not(String.eq(a, b))), Main.rising.from(rest, d), B.and_tt(String.is_le(a, b), Bool.not(String.eq(a, b)), hab, not_false(String.eq(a, b), ee)), ih)

def dr_keep(e: Bool, +a: String, +b: String, +rest: List<&2, String>, ee: {String.eq(a, b) == e : Bool}, hab: {String.is_le(a, b) == True{} : Bool}, ih: {Main.rising(Main.distinct(b <> rest)) == True{} : Bool}) -> {Main.rising(Main.distinct.keep(a, Main.distinct(b <> rest), e)) == True{} : Bool}:
  match e:
    case True{}:
      ih
    case False{}:
      from_head(Main.distinct(b <> rest), a, b, hab, ee, dist_head(b <> rest), ih)

# What `distinct` keeps of a sorted list rises: each string once, in order.
def dist_rising(ys: List<&2, String>, +k: String, h: {SortL.sorted.from(~String, ~(x => x), ys, k) == True{} : Bool}) -> {Main.rising(Main.distinct(ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case a <> Nil{}:
      {==}
    case +a <> +b <> +rest:
      +hr = SortL.band_r(String.is_le(k, a), SortL.sorted.from(~String, ~(x => x), b <> rest, a), h)
      dr_keep(String.eq(a, b), a, b, rest, {==}, SortL.band_l(String.is_le(a, b), SortL.sorted.from(~String, ~(x => x), rest, b), hr), dist_rising(b <> rest, a, hr))


def sd_rising(+xs: List<&2, String>) -> {Main.rising(Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs))) == True{} : Bool}:
  dist_rising(List.sort(~String, ~(a => b => String.is_le(a, b)), xs), SNil{}, SortL.sort_sorted(~String, ~(x => x), xs))

# Every string of a list is among what `distinct` keeps of it sorted.
def sd_all(+xs: List<&2, String>) -> {Main.all_held(Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs)), xs) == True{} : Bool}:
  FetchL.ah_ds(xs, xs, FetchL.ah_refl(xs))

# What `--fields` says opens with the header, and names the revisions it
# is handed: each once, in order, every one of them and nothing else.
def ok_of(+written: List<&2, String>, +revs: List<&2, String>, +rest: List<&2, String>, hr: {Main.fields.revisions(rest) == revs : List<&2, String>}, hrise: {Main.rising(revs) == True{} : Bool}, hheld: {Main.all_held(written, revs) == True{} : Bool}, hall: {Main.all_held(revs, written) == True{} : Bool}) -> {Main.fields.ok(written, Main.WROTE() <> rest) == True{} : Bool}:
  %Equal.sym(List<&2, String>, Main.fields.revisions(rest), revs, hr) : {Bool.and(String.eq(Main.WROTE(), Main.WROTE()), Bool.and(Main.rising(_), Bool.and(Main.all_held(written, _), Main.all_held(_, written)))) == True{} : Bool}
  B.and_tt(String.eq(Main.WROTE(), Main.WROTE()), Bool.and(Main.rising(revs), Bool.and(Main.all_held(written, revs), Main.all_held(revs, written))), S.eq_refl(Main.WROTE()),
    B.and_tt(Main.rising(revs), Bool.and(Main.all_held(written, revs), Main.all_held(revs, written)), hrise,
      B.and_tt(Main.all_held(written, revs), Main.all_held(revs, written), hheld, hall)))

def record_fields(+id: String, +names: List<&2, String>) -> {Main.fields.ok([id], Main.WROTE() <> ("revision " ++ id) <> Main.said.lines("name ", SNil{}, names)) == True{} : Bool}:
  ok_of([id], [id], ("revision " ++ id) <> Main.said.lines("name ", SNil{}, names),
    Equal.trans(List<&2, String>, Main.fields.revisions(("revision " ++ id) <> Main.said.lines("name ", SNil{}, names)), Main.fields.revision(Some{id}, Main.fields.revisions(Main.said.lines("name ", SNil{}, names))), [id],
      Equal.cong(Maybe<&2, String>, List<&2, String>, r => Main.fields.revision(r, Main.fields.revisions(Main.said.lines("name ", SNil{}, names))), T.strip_prefix(id, SNil{}), Some{id}, strip_nil(id)),
      Equal.cong(List<&2, String>, List<&2, String>, l => id <> l, Main.fields.revisions(Main.said.lines("name ", SNil{}, names)), Nil{}, names_said(names))),
    {==}, B.and_tt(Rev.member([id], id), True{}, mem_head(id, Nil{}), {==}), B.and_tt(Rev.member([id], id), True{}, mem_head(id, Nil{}), {==}))

def revs_fields(+xs: List<&2, String>) -> {Main.fields.ok(xs, Main.WROTE() <> Main.said.lines("revision ", SNil{}, Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs)))) == True{} : Bool}:
  ok_of(xs, Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs)), Main.said.lines("revision ", SNil{}, Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs))), revs_said(Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs))), sd_rising(xs), dist_held(xs), sd_all(xs))

def abandon_fields(+xs: List<&2, String>, +names: List<&2, String>) -> {Main.fields.ok(xs, Main.WROTE() <> List.append(&2, String, Main.said.lines("revision ", SNil{}, Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs))), Main.said.lines("name ", SNil{}, Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), names))))) == True{} : Bool}:
  +R = Main.said.lines("revision ", SNil{}, Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs)))
  +N = Main.said.lines("name ", SNil{}, Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), names)))
  ok_of(xs, Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs)), List.append(&2, String, R, N),
    Equal.trans(List<&2, String>, Main.fields.revisions(List.append(&2, String, R, N)), List.append(&2, String, Main.fields.revisions(R), Main.fields.revisions(N)), Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs)), revs_app(R, N),
      Equal.trans(List<&2, String>, List.append(&2, String, Main.fields.revisions(R), Main.fields.revisions(N)), List.append(&2, String, Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs)), Nil{}), Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs)),
        Equal.trans(List<&2, String>, List.append(&2, String, Main.fields.revisions(R), Main.fields.revisions(N)), List.append(&2, String, Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs)), Main.fields.revisions(N)), List.append(&2, String, Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs)), Nil{}),
          Equal.cong(List<&2, String>, List<&2, String>, l => List.append(&2, String, l, Main.fields.revisions(N)), Main.fields.revisions(R), Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs)), revs_said(Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs)))),
          Equal.cong(List<&2, String>, List<&2, String>, l => List.append(&2, String, Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs)), l), Main.fields.revisions(N), Nil{}, names_said(Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), names))))),
        SortL.lapp_nil(String, Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs))))),
    sd_rising(xs), dist_held(xs), sd_all(xs))

# Asked for `--fields`, what the writing commands say of what they wrote
# is decision 0074's.
def writes_fields(+a: String, +when: String, +m: String, +facts: List<&2, T.Split>, +change: String, +id: String, +names: List<&2, String>, +ps: List<&2, String>, +prev: String, +carrying: List<&2, String>, +steps: List<&2, Main.Step>, +run: List<&2, String>, +dry: Bool) -> {Bool.and(Main.fields.ok([id], Main.record.said.lines(Main.Writing{a, when, m, True{}}, facts, change, id, names, ps)), Bool.and(Main.fields.ok(id <> Main.carried.ids(steps), Main.amend.said.lines(True{}, False{}, facts, prev, change, id, carrying, steps)), Bool.and(Main.fields.ok(id <> Main.carried.ids(steps), Main.abandon.said.lines(True{}, id, change, run, names, steps)), Main.fields.ok(Main.carried.ids(steps), Main.carry.said.lines(True{}, dry, steps))))) == True{} : Bool}:
  B.and_tt(Main.fields.ok([id], Main.record.said.lines(Main.Writing{a, when, m, True{}}, facts, change, id, names, ps)), Bool.and(Main.fields.ok(id <> Main.carried.ids(steps), Main.amend.said.lines(True{}, False{}, facts, prev, change, id, carrying, steps)), Bool.and(Main.fields.ok(id <> Main.carried.ids(steps), Main.abandon.said.lines(True{}, id, change, run, names, steps)), Main.fields.ok(Main.carried.ids(steps), Main.carry.said.lines(True{}, dry, steps)))),
    record_fields(id, names),
    B.and_tt(Main.fields.ok(id <> Main.carried.ids(steps), Main.amend.said.lines(True{}, False{}, facts, prev, change, id, carrying, steps)), Bool.and(Main.fields.ok(id <> Main.carried.ids(steps), Main.abandon.said.lines(True{}, id, change, run, names, steps)), Main.fields.ok(Main.carried.ids(steps), Main.carry.said.lines(True{}, dry, steps))),
      revs_fields(id <> Main.carried.ids(steps)),
      B.and_tt(Main.fields.ok(id <> Main.carried.ids(steps), Main.abandon.said.lines(True{}, id, change, run, names, steps)), Main.fields.ok(Main.carried.ids(steps), Main.carry.said.lines(True{}, dry, steps)),
        abandon_fields(id <> Main.carried.ids(steps), names),
        revs_fields(Main.carried.ids(steps)))))


# With `--fields`, a carry names exactly what it files, as the store will
# name it.
def carry_fields(+path: String, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +c: Main.Carrying, +steps: List<&2, Main.Step>, e: {Main.carry.plan(fs, ds, c) == Done{steps} : Result<&2, &2, String, List<&2, Main.Step>>}) -> {Main.fields.ok(Main.steps.filed(path, steps), Main.carry.said.lines(True{}, False{}, steps)) == True{} : Bool}:
  %plan_filed(path, fs, ds, c, steps, e) : {Main.fields.ok(_, Main.carry.said.lines(True{}, False{}, steps)) == True{} : Bool}
  revs_fields(Main.carried.ids(steps))

# An amendment keeps what it added
# --------------------------------

def lk_pick(b: Bool, +v: String, -l: Maybe<&2, String>, -m: Bool, h: {Maybe.is_some(&2, String, l) == m : Bool}) -> {Maybe.is_some(&2, String, Bool.pick(Maybe<&2, String>, b, Some{v}, l)) == Bool.or(b, m) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      h

# `lookup` finds a path exactly where it is among the heads.
def lk_member(kept: List<&2, T.Split>, +p: String) -> {Maybe.is_some(&2, String, Main.lookup(kept, p)) == Rev.member(T.map(~T.Split, ~String, ~(s => Main.split.head(s)), kept), p) : Bool}:
  match kept:
    case Nil{}:
      {==}
    case T.Split{+k, +v} <> +rest:
      lk_pick(String.eq(k, p), v, Main.lookup(rest, p), Rev.member(T.map(~T.Split, ~String, ~(s => Main.split.head(s)), rest), p), lk_member(rest, p))

def bool_disc(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def tf(h: {True{} == False{} : Bool}) -> Empty:
  S.true_false(h)

def am_case(l: Maybe<&2, String>, b: Bool, +kept: List<&2, T.Split>, +p: String, +rest: List<&2, String>, +hex: String, rel: {Maybe.is_some(&2, String, l) == b : Bool}, ih: @hex2: String -> {Main.strings.same(T.map(~T.Split, ~String, ~(s => Main.split.head(s)), Main.amend.mint(rest, Main.lookups(rest, kept), Main.ids.minted(List.length(&2, String, Main.minus(rest, T.map(~T.Split, ~String, ~(s => Main.split.head(s)), kept))), hex2))), rest) == True{} : Bool}) -> {Main.strings.same(T.map(~T.Split, ~String, ~(s => Main.split.head(s)), Main.amend.mint(p <> rest, l <> Main.lookups(rest, kept), Main.ids.minted(List.length(&2, String, Rev.keep(Bool.not(b), p, Main.minus(rest, T.map(~T.Split, ~String, ~(s => Main.split.head(s)), kept)))), hex))), p <> rest) == True{} : Bool}:
  match l b:
    case Some{g} True{}:
      B.and_tt(String.eq(p, p), Main.strings.same(T.map(~T.Split, ~String, ~(s => Main.split.head(s)), Main.amend.mint(rest, Main.lookups(rest, kept), Main.ids.minted(List.length(&2, String, Main.minus(rest, T.map(~T.Split, ~String, ~(s => Main.split.head(s)), kept))), hex))), rest), S.eq_refl(p), ih(hex))
    case Some{g} False{}:
      Empty.absurd({Main.strings.same(T.map(~T.Split, ~String, ~(s => Main.split.head(s)), Main.amend.mint(p <> rest, Some{g} <> Main.lookups(rest, kept), Main.ids.minted(List.length(&2, String, Rev.keep(Bool.not(False{}), p, Main.minus(rest, T.map(~T.Split, ~String, ~(s => Main.split.head(s)), kept)))), hex))), p <> rest) == True{} : Bool}, tf(rel))
    case None{} True{}:
      Empty.absurd({Main.strings.same(T.map(~T.Split, ~String, ~(s => Main.split.head(s)), Main.amend.mint(p <> rest, None{} <> Main.lookups(rest, kept), Main.ids.minted(List.length(&2, String, Rev.keep(Bool.not(True{}), p, Main.minus(rest, T.map(~T.Split, ~String, ~(s => Main.split.head(s)), kept)))), hex))), p <> rest) == True{} : Bool}, S.false_true(rel))
    case None{} False{}:
      B.and_tt(String.eq(p, p), Main.strings.same(T.map(~T.Split, ~String, ~(s => Main.split.head(s)), Main.amend.mint(rest, Main.lookups(rest, kept), Main.ids.minted(List.length(&2, String, Main.minus(rest, T.map(~T.Split, ~String, ~(s => Main.split.head(s)), kept))), String.drop(hex, 24n)))), rest), S.eq_refl(p), ih(String.drop(hex, 24n)))

# Every file arriving is given an identifier, in path order.
def am_heads(arr: List<&2, String>, +kept: List<&2, T.Split>, +hex: String) -> {Main.strings.same(T.map(~T.Split, ~String, ~(s => Main.split.head(s)), Main.amend.mint(arr, Main.lookups(arr, kept), Main.ids.minted(List.length(&2, String, Main.minus(arr, T.map(~T.Split, ~String, ~(s => Main.split.head(s)), kept))), hex))), arr) == True{} : Bool}:
  match arr:
    case Nil{}:
      {==}
    case +p <> +rest:
      am_case(Main.lookup(kept, p), Rev.member(T.map(~T.Split, ~String, ~(s => Main.split.head(s)), kept), p), kept, p, rest, hex, lk_member(kept, p), hex2 => am_heads(rest, kept, hex2))

def kp_case(l: Maybe<&2, String>, ids: List<&2, String>, +kept: List<&2, T.Split>, +p: String, +rest: List<&2, String>, el: {Main.lookup(kept, p) == l : Maybe<&2, String>}, ih: @ids2: List<&2, String> -> {Main.minted.keeps(kept, Main.amend.mint(rest, Main.lookups(rest, kept), ids2)) == True{} : Bool}) -> {Main.minted.keeps(kept, Main.amend.mint(p <> rest, l <> Main.lookups(rest, kept), ids)) == True{} : Bool}:
  match l ids:
    case Some{+g} _:
      %Equal.sym(Maybe<&2, String>, Main.lookup(kept, p), Some{g}, el) : {Bool.and(Main.keeps.one(_, g), Main.minted.keeps(kept, Main.amend.mint(rest, Main.lookups(rest, kept), ids))) == True{} : Bool}
      B.and_tt(String.eq(g, g), Main.minted.keeps(kept, Main.amend.mint(rest, Main.lookups(rest, kept), ids)), S.eq_refl(g), ih(ids))
    case None{} Nil{}:
      {==}
    case None{} +i <> others:
      %Equal.sym(Maybe<&2, String>, Main.lookup(kept, p), None{}, el) : {Bool.and(Main.keeps.one(_, i), Main.minted.keeps(kept, Main.amend.mint(rest, Main.lookups(rest, kept), others))) == True{} : Bool}
      ih(others)

# Each file the amended revision added keeps the identifier it was added
# under.
def am_keeps(arr: List<&2, String>, +kept: List<&2, T.Split>, ids: List<&2, String>) -> {Main.minted.keeps(kept, Main.amend.mint(arr, Main.lookups(arr, kept), ids)) == True{} : Bool}:
  match arr:
    case Nil{}:
      {==}
    case +p <> +rest:
      kp_case(Main.lookup(kept, p), ids, kept, p, rest, {==}, ids2 => am_keeps(rest, kept, ids2))

# What an amendment mints keeps what it added, and names every arrival.
def amend_minted_ok(+arriving: List<&2, String>, +kept: List<&2, T.Split>, +hex: String) -> {Main.amend.minted.ok(arriving, kept, Main.amend.minted(arriving, kept, hex)) == True{} : Bool}:
  +ids = Main.ids.minted(List.length(&2, String, Main.minus(arriving, T.map(~T.Split, ~String, ~(s => Main.split.head(s)), kept))), hex)
  +m = Main.amend.mint(arriving, Main.lookups(arriving, kept), ids)
  B.and_tt(Main.strings.same(T.map(~T.Split, ~String, ~(s => Main.split.head(s)), m), arriving), Main.minted.keeps(kept, m), am_heads(arriving, kept, hex), am_keeps(arriving, kept, ids))

# Abandoning asks for a revision
# ------------------------------

# A word read as anything but a target is not read as one.
def wdisc(k: Main.WWord) -> Type:
  match k:
    case Main.WWord.Word{}:
      Empty
    case _:
      Unit

def not_word(-x: Main.WWord, h: {x == Main.WWord.Word{} : Main.WWord}, u: wdisc(x)) -> Empty:
  %h : {wdisc(_) : Type}
  u

def ww_skip(b: Bool, -x: Main.WWord, -y: Main.WWord, hx: {x == Main.WWord.Word{} : Main.WWord} -> Empty, e: {Bool.pick(Main.WWord, b, x, y) == Main.WWord.Word{} : Main.WWord}) -> {y == Main.WWord.Word{} : Main.WWord}:
  match b:
    case True{}:
      Empty.absurd({y == Main.WWord.Word{} : Main.WWord}, hx(e))
    case False{}:
      e

def ww_last(b: Bool, e: {Bool.pick(Main.WWord, b, Main.WWord.Flag{}, Main.WWord.Word{}) == Main.WWord.Word{} : Main.WWord}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, not_word(Main.WWord.Flag{}, e, Unit{}))
    case False{}:
      {==}

# A word read as the target does not begin with `-`.
def word_plain(+cmd: String, +w: String, ek: {Main.wword.of(cmd, w) == Main.WWord.Word{} : Main.WWord}) -> {String.starts_with(w, "-") == False{} : Bool}:
  ww_last(String.starts_with(w, "-"), ww_skip(String.eq(w, "--fields"), Main.WWord.Fields{}, Bool.pick(Main.WWord, String.starts_with(w, "-"), Main.WWord.Flag{}, Main.WWord.Word{}), h => not_word(Main.WWord.Fields{}, h, Unit{}), ww_skip(Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), Main.WWord.Dry{}, Bool.pick(Main.WWord, String.eq(w, "--fields"), Main.WWord.Fields{}, Bool.pick(Main.WWord, String.starts_with(w, "-"), Main.WWord.Flag{}, Main.WWord.Word{})), h => not_word(Main.WWord.Dry{}, h, Unit{}), ww_skip(Bool.and(String.eq(cmd, "abandon"), String.eq(w, "--only")), Main.WWord.Only{}, Bool.pick(Main.WWord, Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), Main.WWord.Dry{}, Bool.pick(Main.WWord, String.eq(w, "--fields"), Main.WWord.Fields{}, Bool.pick(Main.WWord, String.starts_with(w, "-"), Main.WWord.Flag{}, Main.WWord.Word{}))), h => not_word(Main.WWord.Only{}, h, Unit{}), ww_skip(Bool.and(String.eq(cmd, "carry"), String.eq(w, "--onto")), Main.WWord.Onto{}, Bool.pick(Main.WWord, Bool.and(String.eq(cmd, "abandon"), String.eq(w, "--only")), Main.WWord.Only{}, Bool.pick(Main.WWord, Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), Main.WWord.Dry{}, Bool.pick(Main.WWord, String.eq(w, "--fields"), Main.WWord.Fields{}, Bool.pick(Main.WWord, String.starts_with(w, "-"), Main.WWord.Flag{}, Main.WWord.Word{})))), h => not_word(Main.WWord.Onto{}, h, Unit{}), ww_skip(Bool.and(String.eq(cmd, "amend"), String.eq(w, "--move")), Main.WWord.Move{}, Bool.pick(Main.WWord, Bool.and(String.eq(cmd, "carry"), String.eq(w, "--onto")), Main.WWord.Onto{}, Bool.pick(Main.WWord, Bool.and(String.eq(cmd, "abandon"), String.eq(w, "--only")), Main.WWord.Only{}, Bool.pick(Main.WWord, Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), Main.WWord.Dry{}, Bool.pick(Main.WWord, String.eq(w, "--fields"), Main.WWord.Fields{}, Bool.pick(Main.WWord, String.starts_with(w, "-"), Main.WWord.Flag{}, Main.WWord.Word{}))))), h => not_word(Main.WWord.Move{}, h, Unit{}), ww_skip(Bool.and(Bool.not(String.eq(cmd, "carry")), Bool.or(String.eq(w, "-m"), String.eq(w, "--message"))), Main.WWord.Message{}, Bool.pick(Main.WWord, Bool.and(String.eq(cmd, "amend"), String.eq(w, "--move")), Main.WWord.Move{}, Bool.pick(Main.WWord, Bool.and(String.eq(cmd, "carry"), String.eq(w, "--onto")), Main.WWord.Onto{}, Bool.pick(Main.WWord, Bool.and(String.eq(cmd, "abandon"), String.eq(w, "--only")), Main.WWord.Only{}, Bool.pick(Main.WWord, Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), Main.WWord.Dry{}, Bool.pick(Main.WWord, String.eq(w, "--fields"), Main.WWord.Fields{}, Bool.pick(Main.WWord, String.starts_with(w, "-"), Main.WWord.Flag{}, Main.WWord.Word{})))))), h => not_word(Main.WWord.Message{}, h, Unit{}), ek)))))))

def move_app(+cmd: String, +rest: List<&2, String>, +ys: List<&2, String>, +c: Main.RwCmd, -c2: Main.RwCmd, r: Result<&2, &2, Main.Refused, T.Split>, e: {Result.bind(&2, &2, Main.Refused, T.Split, Main.RwCmd, r, s => Main.rw.args.go(cmd, rest, Main.rw.move(c, s), Main.wword(cmd, rest))) == Done{c2} : Result<&2, &2, Main.Refused, Main.RwCmd>}, ih: @s: T.Split -> {Main.rw.args.go(cmd, rest, Main.rw.move(c, s), Main.wword(cmd, rest)) == Done{c2} : Result<&2, &2, Main.Refused, Main.RwCmd>} -> {Main.rw.args.go(cmd, List.append(&2, String, rest, ys), Main.rw.move(c, s), Main.wword(cmd, List.append(&2, String, rest, ys))) == Main.rw.args.go(cmd, ys, c2, Main.wword(cmd, ys)) : Result<&2, &2, Main.Refused, Main.RwCmd>}) -> {Result.bind(&2, &2, Main.Refused, T.Split, Main.RwCmd, r, s => Main.rw.args.go(cmd, List.append(&2, String, rest, ys), Main.rw.move(c, s), Main.wword(cmd, List.append(&2, String, rest, ys)))) == Main.rw.args.go(cmd, ys, c2, Main.wword(cmd, ys)) : Result<&2, &2, Main.Refused, Main.RwCmd>}:
  match r:
    case Fail{x}:
      Empty.absurd({Result.bind(&2, &2, Main.Refused, T.Split, Main.RwCmd, Fail{x}, s => Main.rw.args.go(cmd, List.append(&2, String, rest, ys), Main.rw.move(c, s), Main.wword(cmd, List.append(&2, String, rest, ys)))) == Main.rw.args.go(cmd, ys, c2, Main.wword(cmd, ys)) : Result<&2, &2, Main.Refused, Main.RwCmd>}, not_done(Main.RwCmd, Fail{x}, c2, e, Unit{}))
    case Done{+s}:
      ih(s, e)

def word_app(+cmd: String, +rest: List<&2, String>, +ys: List<&2, String>, -c2: Main.RwCmd, r: Result<&2, &2, Main.Refused, Main.RwCmd>, e: {Result.bind(&2, &2, Main.Refused, Main.RwCmd, Main.RwCmd, r, more => Main.rw.args.go(cmd, rest, more, Main.wword(cmd, rest))) == Done{c2} : Result<&2, &2, Main.Refused, Main.RwCmd>}, ih: @more: Main.RwCmd -> {Main.rw.args.go(cmd, rest, more, Main.wword(cmd, rest)) == Done{c2} : Result<&2, &2, Main.Refused, Main.RwCmd>} -> {Main.rw.args.go(cmd, List.append(&2, String, rest, ys), more, Main.wword(cmd, List.append(&2, String, rest, ys))) == Main.rw.args.go(cmd, ys, c2, Main.wword(cmd, ys)) : Result<&2, &2, Main.Refused, Main.RwCmd>}) -> {Result.bind(&2, &2, Main.Refused, Main.RwCmd, Main.RwCmd, r, more => Main.rw.args.go(cmd, List.append(&2, String, rest, ys), more, Main.wword(cmd, List.append(&2, String, rest, ys)))) == Main.rw.args.go(cmd, ys, c2, Main.wword(cmd, ys)) : Result<&2, &2, Main.Refused, Main.RwCmd>}:
  match r:
    case Fail{x}:
      Empty.absurd({Result.bind(&2, &2, Main.Refused, Main.RwCmd, Main.RwCmd, Fail{x}, more => Main.rw.args.go(cmd, List.append(&2, String, rest, ys), more, Main.wword(cmd, List.append(&2, String, rest, ys)))) == Main.rw.args.go(cmd, ys, c2, Main.wword(cmd, ys)) : Result<&2, &2, Main.Refused, Main.RwCmd>}, not_done(Main.RwCmd, Fail{x}, c2, e, Unit{}))
    case Done{+more}:
      ih(more, e)

# A flag that takes no value is read the same whatever follows it.
def step_only(+cmd: String, +w: String, zs: List<&2, String>, +c: Main.RwCmd) -> {Main.rw.args.go(cmd, w <> zs, c, Main.WWord.Only{}) == Main.rw.args.go(cmd, zs, Main.rw.only(c), Main.wword(cmd, zs)) : Result<&2, &2, Main.Refused, Main.RwCmd>}:
  match zs:
    case Nil{}:
      {==}
    case z <> more:
      {==}

def step_dry(+cmd: String, +w: String, zs: List<&2, String>, +c: Main.RwCmd) -> {Main.rw.args.go(cmd, w <> zs, c, Main.WWord.Dry{}) == Main.rw.args.go(cmd, zs, Main.rw.dry(c), Main.wword(cmd, zs)) : Result<&2, &2, Main.Refused, Main.RwCmd>}:
  match zs:
    case Nil{}:
      {==}
    case z <> more:
      {==}

def step_fields(+cmd: String, +w: String, zs: List<&2, String>, +c: Main.RwCmd) -> {Main.rw.args.go(cmd, w <> zs, c, Main.WWord.Fields{}) == Main.rw.args.go(cmd, zs, Main.rw.fields(c), Main.wword(cmd, zs)) : Result<&2, &2, Main.Refused, Main.RwCmd>}:
  match zs:
    case Nil{}:
      {==}
    case z <> more:
      {==}

def step_word(+cmd: String, +w: String, zs: List<&2, String>, +c: Main.RwCmd) -> {Main.rw.args.go(cmd, w <> zs, c, Main.WWord.Word{}) == Result.bind(&2, &2, Main.Refused, Main.RwCmd, Main.RwCmd, Main.rw.word(cmd, c, w), more => Main.rw.args.go(cmd, zs, more, Main.wword(cmd, zs))) : Result<&2, &2, Main.Refused, Main.RwCmd>}:
  match zs:
    case Nil{}:
      {==}
    case z <> more:
      {==}

def flag_fail(+cmd: String, +w: String, zs: List<&2, String>, +c: Main.RwCmd, -c2: Main.RwCmd, e: {Main.rw.args.go(cmd, w <> zs, c, Main.WWord.Flag{}) == Done{c2} : Result<&2, &2, Main.Refused, Main.RwCmd>}) -> Empty:
  match zs:
    case Nil{}:
      not_done(Main.RwCmd, Main.rw.args.go(cmd, [w], c, Main.WWord.Flag{}), c2, e, Unit{})
    case +z <> +more:
      not_done(Main.RwCmd, Main.rw.args.go(cmd, w <> z <> more, c, Main.WWord.Flag{}), c2, e, Unit{})

# Words read, and more after them, are read on from where the first left
# off.
def go_app(+cmd: String, args: List<&2, String>, +c: Main.RwCmd, k: Main.WWord, +ys: List<&2, String>, -c2: Main.RwCmd, ek: {Main.wword(cmd, args) == k : Main.WWord}, e: {Main.rw.args.go(cmd, args, c, k) == Done{c2} : Result<&2, &2, Main.Refused, Main.RwCmd>}) -> {Main.rw.args.go(cmd, List.append(&2, String, args, ys), c, Main.wword(cmd, List.append(&2, String, args, ys))) == Main.rw.args.go(cmd, ys, c2, Main.wword(cmd, ys)) : Result<&2, &2, Main.Refused, Main.RwCmd>}:
  match args k:
    case Nil{} _:
      Equal.cong(Main.RwCmd, Result<&2, &2, Main.Refused, Main.RwCmd>, x => Main.rw.args.go(cmd, ys, x, Main.wword(cmd, ys)), c, c2, B.done_eq(Main.RwCmd, c, c2, e))
    case +w <> Nil{} Main.WWord.Message{}:
      Empty.absurd({Main.rw.args.go(cmd, List.append(&2, String, w <> Nil{}, ys), c, Main.wword(cmd, List.append(&2, String, w <> Nil{}, ys))) == Main.rw.args.go(cmd, ys, c2, Main.wword(cmd, ys)) : Result<&2, &2, Main.Refused, Main.RwCmd>}, not_done(Main.RwCmd, Main.rw.args.go(cmd, w <> Nil{}, c, Main.WWord.Message{}), c2, e, Unit{}))
    case +w <> +v <> +rest Main.WWord.Message{}:
      %Equal.sym(Main.WWord, Main.wword(cmd, w <> v <> rest), Main.WWord.Message{}, ek) : {Main.rw.args.go(cmd, List.append(&2, String, w <> v <> rest, ys), c, _) == Main.rw.args.go(cmd, ys, c2, Main.wword(cmd, ys)) : Result<&2, &2, Main.Refused, Main.RwCmd>}
      go_app(cmd, rest, Main.rw.message(c, v), Main.wword(cmd, rest), ys, c2, {==}, e)
    case +w <> Nil{} Main.WWord.Onto{}:
      Empty.absurd({Main.rw.args.go(cmd, List.append(&2, String, w <> Nil{}, ys), c, Main.wword(cmd, List.append(&2, String, w <> Nil{}, ys))) == Main.rw.args.go(cmd, ys, c2, Main.wword(cmd, ys)) : Result<&2, &2, Main.Refused, Main.RwCmd>}, not_done(Main.RwCmd, Main.rw.args.go(cmd, w <> Nil{}, c, Main.WWord.Onto{}), c2, e, Unit{}))
    case +w <> +v <> +rest Main.WWord.Onto{}:
      %Equal.sym(Main.WWord, Main.wword(cmd, w <> v <> rest), Main.WWord.Onto{}, ek) : {Main.rw.args.go(cmd, List.append(&2, String, w <> v <> rest, ys), c, _) == Main.rw.args.go(cmd, ys, c2, Main.wword(cmd, ys)) : Result<&2, &2, Main.Refused, Main.RwCmd>}
      go_app(cmd, rest, Main.rw.onto(c, v), Main.wword(cmd, rest), ys, c2, {==}, e)
    case +w <> Nil{} Main.WWord.Move{}:
      Empty.absurd({Main.rw.args.go(cmd, List.append(&2, String, w <> Nil{}, ys), c, Main.wword(cmd, List.append(&2, String, w <> Nil{}, ys))) == Main.rw.args.go(cmd, ys, c2, Main.wword(cmd, ys)) : Result<&2, &2, Main.Refused, Main.RwCmd>}, not_done(Main.RwCmd, Main.rw.args.go(cmd, w <> Nil{}, c, Main.WWord.Move{}), c2, e, Unit{}))
    case +w <> +v <> +rest Main.WWord.Move{}:
      %Equal.sym(Main.WWord, Main.wword(cmd, w <> v <> rest), Main.WWord.Move{}, ek) : {Main.rw.args.go(cmd, List.append(&2, String, w <> v <> rest, ys), c, _) == Main.rw.args.go(cmd, ys, c2, Main.wword(cmd, ys)) : Result<&2, &2, Main.Refused, Main.RwCmd>}
      move_app(cmd, rest, ys, c, c2, Main.record.split(v, "`--move` is spelled `--move <old>=<new>`"), e, s => h => go_app(cmd, rest, Main.rw.move(c, s), Main.wword(cmd, rest), ys, c2, {==}, h))
    case +w <> +rest Main.WWord.Only{}:
      %Equal.sym(Main.WWord, Main.wword(cmd, w <> rest), Main.WWord.Only{}, ek) : {Main.rw.args.go(cmd, List.append(&2, String, w <> rest, ys), c, _) == Main.rw.args.go(cmd, ys, c2, Main.wword(cmd, ys)) : Result<&2, &2, Main.Refused, Main.RwCmd>}
      Equal.trans(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, w <> List.append(&2, String, rest, ys), c, Main.WWord.Only{}), Main.rw.args.go(cmd, List.append(&2, String, rest, ys), Main.rw.only(c), Main.wword(cmd, List.append(&2, String, rest, ys))), Main.rw.args.go(cmd, ys, c2, Main.wword(cmd, ys)),
        step_only(cmd, w, List.append(&2, String, rest, ys), c),
        go_app(cmd, rest, Main.rw.only(c), Main.wword(cmd, rest), ys, c2, {==}, Equal.trans(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, rest, Main.rw.only(c), Main.wword(cmd, rest)), Main.rw.args.go(cmd, w <> rest, c, Main.WWord.Only{}), Done{c2}, Equal.sym(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, w <> rest, c, Main.WWord.Only{}), Main.rw.args.go(cmd, rest, Main.rw.only(c), Main.wword(cmd, rest)), step_only(cmd, w, rest, c)), e)))
    case +w <> +rest Main.WWord.Dry{}:
      %Equal.sym(Main.WWord, Main.wword(cmd, w <> rest), Main.WWord.Dry{}, ek) : {Main.rw.args.go(cmd, List.append(&2, String, w <> rest, ys), c, _) == Main.rw.args.go(cmd, ys, c2, Main.wword(cmd, ys)) : Result<&2, &2, Main.Refused, Main.RwCmd>}
      Equal.trans(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, w <> List.append(&2, String, rest, ys), c, Main.WWord.Dry{}), Main.rw.args.go(cmd, List.append(&2, String, rest, ys), Main.rw.dry(c), Main.wword(cmd, List.append(&2, String, rest, ys))), Main.rw.args.go(cmd, ys, c2, Main.wword(cmd, ys)),
        step_dry(cmd, w, List.append(&2, String, rest, ys), c),
        go_app(cmd, rest, Main.rw.dry(c), Main.wword(cmd, rest), ys, c2, {==}, Equal.trans(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, rest, Main.rw.dry(c), Main.wword(cmd, rest)), Main.rw.args.go(cmd, w <> rest, c, Main.WWord.Dry{}), Done{c2}, Equal.sym(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, w <> rest, c, Main.WWord.Dry{}), Main.rw.args.go(cmd, rest, Main.rw.dry(c), Main.wword(cmd, rest)), step_dry(cmd, w, rest, c)), e)))
    case +w <> +rest Main.WWord.Fields{}:
      %Equal.sym(Main.WWord, Main.wword(cmd, w <> rest), Main.WWord.Fields{}, ek) : {Main.rw.args.go(cmd, List.append(&2, String, w <> rest, ys), c, _) == Main.rw.args.go(cmd, ys, c2, Main.wword(cmd, ys)) : Result<&2, &2, Main.Refused, Main.RwCmd>}
      Equal.trans(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, w <> List.append(&2, String, rest, ys), c, Main.WWord.Fields{}), Main.rw.args.go(cmd, List.append(&2, String, rest, ys), Main.rw.fields(c), Main.wword(cmd, List.append(&2, String, rest, ys))), Main.rw.args.go(cmd, ys, c2, Main.wword(cmd, ys)),
        step_fields(cmd, w, List.append(&2, String, rest, ys), c),
        go_app(cmd, rest, Main.rw.fields(c), Main.wword(cmd, rest), ys, c2, {==}, Equal.trans(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, rest, Main.rw.fields(c), Main.wword(cmd, rest)), Main.rw.args.go(cmd, w <> rest, c, Main.WWord.Fields{}), Done{c2}, Equal.sym(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, w <> rest, c, Main.WWord.Fields{}), Main.rw.args.go(cmd, rest, Main.rw.fields(c), Main.wword(cmd, rest)), step_fields(cmd, w, rest, c)), e)))
    case +w <> +rest Main.WWord.Flag{}:
      Empty.absurd({Main.rw.args.go(cmd, List.append(&2, String, w <> rest, ys), c, Main.wword(cmd, List.append(&2, String, w <> rest, ys))) == Main.rw.args.go(cmd, ys, c2, Main.wword(cmd, ys)) : Result<&2, &2, Main.Refused, Main.RwCmd>}, flag_fail(cmd, w, rest, c, c2, e))
    case +w <> +rest Main.WWord.Word{}:
      %Equal.sym(Main.WWord, Main.wword(cmd, w <> rest), Main.WWord.Word{}, ek) : {Main.rw.args.go(cmd, List.append(&2, String, w <> rest, ys), c, _) == Main.rw.args.go(cmd, ys, c2, Main.wword(cmd, ys)) : Result<&2, &2, Main.Refused, Main.RwCmd>}
      Equal.trans(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, w <> List.append(&2, String, rest, ys), c, Main.WWord.Word{}), Result.bind(&2, &2, Main.Refused, Main.RwCmd, Main.RwCmd, Main.rw.word(cmd, c, w), more => Main.rw.args.go(cmd, List.append(&2, String, rest, ys), more, Main.wword(cmd, List.append(&2, String, rest, ys)))), Main.rw.args.go(cmd, ys, c2, Main.wword(cmd, ys)),
        step_word(cmd, w, List.append(&2, String, rest, ys), c),
        word_app(cmd, rest, ys, c2, Main.rw.word(cmd, c, w), Equal.trans(Result<&2, &2, Main.Refused, Main.RwCmd>, Result.bind(&2, &2, Main.Refused, Main.RwCmd, Main.RwCmd, Main.rw.word(cmd, c, w), more => Main.rw.args.go(cmd, rest, more, Main.wword(cmd, rest))), Main.rw.args.go(cmd, w <> rest, c, Main.WWord.Word{}), Done{c2}, Equal.sym(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, w <> rest, c, Main.WWord.Word{}), Result.bind(&2, &2, Main.Refused, Main.RwCmd, Main.RwCmd, Main.rw.word(cmd, c, w), more => Main.rw.args.go(cmd, rest, more, Main.wword(cmd, rest))), step_word(cmd, w, rest, c)), e), more => h => go_app(cmd, rest, more, Main.wword(cmd, rest), ys, c2, {==}, h)))

# The target, where one is read, is one of the words and not a flag.
def target.in(+orig: List<&2, String>, n: Maybe<&2, String>) -> Bool:
  match n:
    case Some{+t}:
      Bool.and(Rev.member(orig, t), Bool.not(String.starts_with(t, "-")))
    case None{}:
      True{}

def keep_in(+orig: List<&2, String>, -c: Main.RwCmd, -c3: Main.RwCmd, eq: {Main.rw.named(c3) == Main.rw.named(c) : Maybe<&2, String>}, hc: {target.in(orig, Main.rw.named(c)) == True{} : Bool}) -> {target.in(orig, Main.rw.named(c3)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, String>, Main.rw.named(c3), Main.rw.named(c), eq) : {target.in(orig, _) == True{} : Bool}
  hc

def nm_message(c: Main.RwCmd, -v: String) -> {Main.rw.named(Main.rw.message(c, v)) == Main.rw.named(c) : Maybe<&2, String>}:
  match c:
    case Main.RwCmd{m, mv, o, n, d, f, y}:
      {==}

def nm_move(c: Main.RwCmd, -v: T.Split) -> {Main.rw.named(Main.rw.move(c, v)) == Main.rw.named(c) : Maybe<&2, String>}:
  match c:
    case Main.RwCmd{m, mv, o, n, d, f, y}:
      {==}

def nm_onto(c: Main.RwCmd, -v: String) -> {Main.rw.named(Main.rw.onto(c, v)) == Main.rw.named(c) : Maybe<&2, String>}:
  match c:
    case Main.RwCmd{m, mv, o, n, d, f, y}:
      {==}

def nm_only(c: Main.RwCmd) -> {Main.rw.named(Main.rw.only(c)) == Main.rw.named(c) : Maybe<&2, String>}:
  match c:
    case Main.RwCmd{m, mv, o, n, d, f, y}:
      {==}

def nm_dry(c: Main.RwCmd) -> {Main.rw.named(Main.rw.dry(c)) == Main.rw.named(c) : Maybe<&2, String>}:
  match c:
    case Main.RwCmd{m, mv, o, n, d, f, y}:
      {==}

def nm_fields(c: Main.RwCmd) -> {Main.rw.named(Main.rw.fields(c)) == Main.rw.named(c) : Maybe<&2, String>}:
  match c:
    case Main.RwCmd{m, mv, o, n, d, f, y}:
      {==}

def drop1(+orig: List<&2, String>, +w: String, +rest: List<&2, String>, hs: {Main.all_held(orig, w <> rest) == True{} : Bool}) -> {Main.all_held(orig, rest) == True{} : Bool}:
  SortL.band_r(Rev.member(orig, w), Main.all_held(orig, rest), hs)

def move_target(+cmd: String, +orig: List<&2, String>, +rest: List<&2, String>, +c: Main.RwCmd, -c2: Main.RwCmd, hc: {target.in(orig, Main.rw.named(c)) == True{} : Bool}, r: Result<&2, &2, Main.Refused, T.Split>, e: {Result.bind(&2, &2, Main.Refused, T.Split, Main.RwCmd, r, s => Main.rw.args.go(cmd, rest, Main.rw.move(c, s), Main.wword(cmd, rest))) == Done{c2} : Result<&2, &2, Main.Refused, Main.RwCmd>}, ih: @s: T.Split -> {target.in(orig, Main.rw.named(Main.rw.move(c, s))) == True{} : Bool} -> {Main.rw.args.go(cmd, rest, Main.rw.move(c, s), Main.wword(cmd, rest)) == Done{c2} : Result<&2, &2, Main.Refused, Main.RwCmd>} -> {target.in(orig, Main.rw.named(c2)) == True{} : Bool}) -> {target.in(orig, Main.rw.named(c2)) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({target.in(orig, Main.rw.named(c2)) == True{} : Bool}, not_done(Main.RwCmd, Fail{x}, c2, e, Unit{}))
    case Done{+s}:
      ih(s, keep_in(orig, c, Main.rw.move(c, s), nm_move(c, s), hc), e)

def word_target(+cmd: String, +orig: List<&2, String>, +w: String, +rest: List<&2, String>, c: Main.RwCmd, -c2: Main.RwCmd, hw: {target.in(orig, Some{w}) == True{} : Bool}, e: {Result.bind(&2, &2, Main.Refused, Main.RwCmd, Main.RwCmd, Main.rw.word(cmd, c, w), more => Main.rw.args.go(cmd, rest, more, Main.wword(cmd, rest))) == Done{c2} : Result<&2, &2, Main.Refused, Main.RwCmd>}, ih: @more: Main.RwCmd -> {target.in(orig, Main.rw.named(more)) == True{} : Bool} -> {Main.rw.args.go(cmd, rest, more, Main.wword(cmd, rest)) == Done{c2} : Result<&2, &2, Main.Refused, Main.RwCmd>} -> {target.in(orig, Main.rw.named(c2)) == True{} : Bool}) -> {target.in(orig, Main.rw.named(c2)) == True{} : Bool}:
  match c:
    case Main.RwCmd{+m, +mv, +o, None{}, +d, +f, +y}:
      ih(Main.RwCmd{m, mv, o, Some{w}, d, f, y}, hw, e)
    case Main.RwCmd{m, mv, o, Some{n}, d, f, y}:
      Empty.absurd({target.in(orig, Main.rw.named(c2)) == True{} : Bool}, not_done(Main.RwCmd, Result.bind(&2, &2, Main.Refused, Main.RwCmd, Main.RwCmd, Main.rw.word(cmd, Main.RwCmd{m, mv, o, Some{n}, d, f, y}, w), more => Main.rw.args.go(cmd, rest, more, Main.wword(cmd, rest))), c2, e, Unit{}))

# Whatever the words, the target read is one of them and not a flag.
def go_target(+cmd: String, +orig: List<&2, String>, args: List<&2, String>, +c: Main.RwCmd, k: Main.WWord, -c2: Main.RwCmd, ek: {Main.wword(cmd, args) == k : Main.WWord}, +hs: {Main.all_held(orig, args) == True{} : Bool}, hc: {target.in(orig, Main.rw.named(c)) == True{} : Bool}, e: {Main.rw.args.go(cmd, args, c, k) == Done{c2} : Result<&2, &2, Main.Refused, Main.RwCmd>}) -> {target.in(orig, Main.rw.named(c2)) == True{} : Bool}:
  match args k:
    case Nil{} _:
      %B.done_eq(Main.RwCmd, c, c2, e) : {target.in(orig, Main.rw.named(_)) == True{} : Bool}
      hc
    case +w <> Nil{} Main.WWord.Message{}:
      Empty.absurd({target.in(orig, Main.rw.named(c2)) == True{} : Bool}, not_done(Main.RwCmd, Main.rw.args.go(cmd, w <> Nil{}, c, Main.WWord.Message{}), c2, e, Unit{}))
    case +w <> +v <> +rest Main.WWord.Message{}:
      go_target(cmd, orig, rest, Main.rw.message(c, v), Main.wword(cmd, rest), c2, {==}, drop1(orig, v, rest, drop1(orig, w, v <> rest, hs)), keep_in(orig, c, Main.rw.message(c, v), nm_message(c, v), hc), e)
    case +w <> Nil{} Main.WWord.Onto{}:
      Empty.absurd({target.in(orig, Main.rw.named(c2)) == True{} : Bool}, not_done(Main.RwCmd, Main.rw.args.go(cmd, w <> Nil{}, c, Main.WWord.Onto{}), c2, e, Unit{}))
    case +w <> +v <> +rest Main.WWord.Onto{}:
      go_target(cmd, orig, rest, Main.rw.onto(c, v), Main.wword(cmd, rest), c2, {==}, drop1(orig, v, rest, drop1(orig, w, v <> rest, hs)), keep_in(orig, c, Main.rw.onto(c, v), nm_onto(c, v), hc), e)
    case +w <> Nil{} Main.WWord.Move{}:
      Empty.absurd({target.in(orig, Main.rw.named(c2)) == True{} : Bool}, not_done(Main.RwCmd, Main.rw.args.go(cmd, w <> Nil{}, c, Main.WWord.Move{}), c2, e, Unit{}))
    case +w <> +v <> +rest Main.WWord.Move{}:
      move_target(cmd, orig, rest, c, c2, hc, Main.record.split(v, "`--move` is spelled `--move <old>=<new>`"), e, s => hm => h => go_target(cmd, orig, rest, Main.rw.move(c, s), Main.wword(cmd, rest), c2, {==}, drop1(orig, v, rest, drop1(orig, w, v <> rest, hs)), hm, h))
    case +w <> +rest Main.WWord.Only{}:
      go_target(cmd, orig, rest, Main.rw.only(c), Main.wword(cmd, rest), c2, {==}, drop1(orig, w, rest, hs), keep_in(orig, c, Main.rw.only(c), nm_only(c), hc), Equal.trans(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, rest, Main.rw.only(c), Main.wword(cmd, rest)), Main.rw.args.go(cmd, w <> rest, c, Main.WWord.Only{}), Done{c2}, Equal.sym(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, w <> rest, c, Main.WWord.Only{}), Main.rw.args.go(cmd, rest, Main.rw.only(c), Main.wword(cmd, rest)), step_only(cmd, w, rest, c)), e))
    case +w <> +rest Main.WWord.Dry{}:
      go_target(cmd, orig, rest, Main.rw.dry(c), Main.wword(cmd, rest), c2, {==}, drop1(orig, w, rest, hs), keep_in(orig, c, Main.rw.dry(c), nm_dry(c), hc), Equal.trans(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, rest, Main.rw.dry(c), Main.wword(cmd, rest)), Main.rw.args.go(cmd, w <> rest, c, Main.WWord.Dry{}), Done{c2}, Equal.sym(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, w <> rest, c, Main.WWord.Dry{}), Main.rw.args.go(cmd, rest, Main.rw.dry(c), Main.wword(cmd, rest)), step_dry(cmd, w, rest, c)), e))
    case +w <> +rest Main.WWord.Fields{}:
      go_target(cmd, orig, rest, Main.rw.fields(c), Main.wword(cmd, rest), c2, {==}, drop1(orig, w, rest, hs), keep_in(orig, c, Main.rw.fields(c), nm_fields(c), hc), Equal.trans(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, rest, Main.rw.fields(c), Main.wword(cmd, rest)), Main.rw.args.go(cmd, w <> rest, c, Main.WWord.Fields{}), Done{c2}, Equal.sym(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, w <> rest, c, Main.WWord.Fields{}), Main.rw.args.go(cmd, rest, Main.rw.fields(c), Main.wword(cmd, rest)), step_fields(cmd, w, rest, c)), e))
    case +w <> +rest Main.WWord.Flag{}:
      Empty.absurd({target.in(orig, Main.rw.named(c2)) == True{} : Bool}, flag_fail(cmd, w, rest, c, c2, e))
    case +w <> +rest Main.WWord.Word{}:
      word_target(cmd, orig, w, rest, c, c2, B.and_tt(Rev.member(orig, w), Bool.not(String.starts_with(w, "-")), SortL.band_l(Rev.member(orig, w), Main.all_held(orig, rest), hs), not_false(String.starts_with(w, "-"), word_plain(cmd, w, ek))), Equal.trans(Result<&2, &2, Main.Refused, Main.RwCmd>, Result.bind(&2, &2, Main.Refused, Main.RwCmd, Main.RwCmd, Main.rw.word(cmd, c, w), more => Main.rw.args.go(cmd, rest, more, Main.wword(cmd, rest))), Main.rw.args.go(cmd, w <> rest, c, Main.WWord.Word{}), Done{c2}, Equal.sym(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, w <> rest, c, Main.WWord.Word{}), Result.bind(&2, &2, Main.Refused, Main.RwCmd, Main.RwCmd, Main.rw.word(cmd, c, w), more => Main.rw.args.go(cmd, rest, more, Main.wword(cmd, rest))), step_word(cmd, w, rest, c)), e), more => hm => h => go_target(cmd, orig, rest, more, Main.wword(cmd, rest), c2, {==}, drop1(orig, w, rest, hs), hm, h))

def asks_df(+args: List<&2, String>, +m: Maybe<&2, String>, +mv: List<&2, T.Split>, +o: Maybe<&2, String>, +t: String, d: Bool, f: Bool, +y: Bool, -c: Main.RwCmd, hin: {target.in(args, Some{t}) == True{} : Bool}, e: {Main.abandon.asks.r(Main.RwCmd{m, mv, o, Some{t}, d, f, y}) == Done{c} : Result<&2, &2, Main.Refused, Main.RwCmd>}) -> {Main.abandon.target.ok(args, Main.rw.named(c)) == True{} : Bool}:
  match d f:
    case True{} True{}:
      Empty.absurd({Main.abandon.target.ok(args, Main.rw.named(c)) == True{} : Bool}, not_done(Main.RwCmd, Main.abandon.asks.r(Main.RwCmd{m, mv, o, Some{t}, True{}, True{}, y}), c, e, Unit{}))
    case True{} False{}:
      %B.done_eq(Main.RwCmd, Main.RwCmd{m, mv, o, Some{t}, True{}, False{}, y}, c, e) : {Main.abandon.target.ok(args, Main.rw.named(_)) == True{} : Bool}
      hin
    case False{} True{}:
      %B.done_eq(Main.RwCmd, Main.RwCmd{m, mv, o, Some{t}, False{}, True{}, y}, c, e) : {Main.abandon.target.ok(args, Main.rw.named(_)) == True{} : Bool}
      hin
    case False{} False{}:
      %B.done_eq(Main.RwCmd, Main.RwCmd{m, mv, o, Some{t}, False{}, False{}, y}, c, e) : {Main.abandon.target.ok(args, Main.rw.named(_)) == True{} : Bool}
      hin

def asks_n(+args: List<&2, String>, +m: Maybe<&2, String>, +mv: List<&2, T.Split>, +o: Maybe<&2, String>, n: Maybe<&2, String>, +d: Bool, +f: Bool, +y: Bool, -c: Main.RwCmd, hin: {target.in(args, n) == True{} : Bool}, e: {Main.abandon.asks.r(Main.RwCmd{m, mv, o, n, d, f, y}) == Done{c} : Result<&2, &2, Main.Refused, Main.RwCmd>}) -> {Main.abandon.target.ok(args, Main.rw.named(c)) == True{} : Bool}:
  match n:
    case None{}:
      Empty.absurd({Main.abandon.target.ok(args, Main.rw.named(c)) == True{} : Bool}, not_done(Main.RwCmd, Main.abandon.asks.r(Main.RwCmd{m, mv, o, None{}, d, f, y}), c, e, Unit{}))
    case Some{+t}:
      asks_df(args, m, mv, o, t, d, f, y, c, hin, e)

def asks_c(+args: List<&2, String>, c1: Main.RwCmd, -c: Main.RwCmd, hin: {target.in(args, Main.rw.named(c1)) == True{} : Bool}, e: {Main.abandon.asks.r(c1) == Done{c} : Result<&2, &2, Main.Refused, Main.RwCmd>}) -> {Main.abandon.target.ok(args, Main.rw.named(c)) == True{} : Bool}:
  match c1:
    case Main.RwCmd{+m, +mv, +o, n, +d, +f, +y}:
      asks_n(args, m, mv, o, n, d, f, y, c, hin, e)

def words1(+args: List<&2, String>, r: Result<&2, &2, Main.Refused, Main.RwCmd>, er: {Main.rw.args.r("abandon", args) == r : Result<&2, &2, Main.Refused, Main.RwCmd>}, -c: Main.RwCmd, e: {Result.bind(&2, &2, Main.Refused, Main.RwCmd, Main.RwCmd, r, x => Main.abandon.asks.r(x)) == Done{c} : Result<&2, &2, Main.Refused, Main.RwCmd>}) -> {Main.abandon.target.ok(args, Main.rw.named(c)) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.abandon.target.ok(args, Main.rw.named(c)) == True{} : Bool}, not_done(Main.RwCmd, Fail{x}, c, e, Unit{}))
    case Done{+c1}:
      asks_c(args, c1, c, go_target("abandon", args, args, Main.RwCmd{None{}, Nil{}, None{}, None{}, False{}, False{}, False{}}, Main.wword("abandon", args), c1, {==}, held_refl(args), {==}, er), e)

# What `abandon` goes on with is a target it was given among its words.
def target_words(+args: List<&2, String>, -c: Main.RwCmd, e: {Main.abandon.words.r(args) == Done{c} : Result<&2, &2, Main.Refused, Main.RwCmd>}) -> {Main.abandon.target.ok(args, Main.rw.named(c)) == True{} : Bool}:
  words1(args, Main.rw.args.r("abandon", args), {==}, c, e)

def named_code(n: Maybe<&2, String>, -m: Maybe<&2, String>, -mv: List<&2, T.Split>, -o: Maybe<&2, String>, -y: Bool) -> {Main.refused.code(Main.RwCmd, Main.abandon.asks.r(Main.RwCmd{m, mv, o, n, True{}, True{}, y})) == 2 : U32}:
  match n:
    case None{}:
      {==}
    case Some{t}:
      {==}

def dry_fields_code(c: Main.RwCmd) -> {Main.refused.code(Main.RwCmd, Main.abandon.asks.r(Main.rw.fields(Main.rw.dry(c)))) == 2 : U32}:
  match c:
    case Main.RwCmd{m, mv, o, n, d, f, y}:
      named_code(n, m, mv, o, y)

# Whatever words `abandon` reads, `--dry-run --fields` after them is
# refused as a usage error.
def dry_fields(+args: List<&2, String>, c: Main.RwCmd, e: {Main.rw.args.r("abandon", args) == Done{c} : Result<&2, &2, Main.Refused, Main.RwCmd>}) -> {Main.refused.code(Main.RwCmd, Main.abandon.words.r(List.append(&2, String, args, ["--dry-run", "--fields"]))) == 2 : U32}:
  %Equal.sym(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go("abandon", List.append(&2, String, args, ["--dry-run", "--fields"]), Main.RwCmd{None{}, Nil{}, None{}, None{}, False{}, False{}, False{}}, Main.wword("abandon", List.append(&2, String, args, ["--dry-run", "--fields"]))), Main.rw.args.go("abandon", ["--dry-run", "--fields"], c, Main.wword("abandon", ["--dry-run", "--fields"])), go_app("abandon", args, Main.RwCmd{None{}, Nil{}, None{}, None{}, False{}, False{}, False{}}, Main.wword("abandon", args), ["--dry-run", "--fields"], c, {==}, e)) : {Main.refused.code(Main.RwCmd, Result.bind(&2, &2, Main.Refused, Main.RwCmd, Main.RwCmd, _, x => Main.abandon.asks.r(x))) == 2 : U32}
  dry_fields_code(c)

# A dry run of abandoning says the run
# ------------------------------------

# Stripping a prefix from what begins with it leaves the rest.
def strip_app(p: String, +r: String) -> {T.strip_prefix(String.append(p, r), p) == Some{r} : Maybe<&2, String>}:
  match p:
    case SNil{}:
      strip_nil(r)
    case SCon{+c, t}:
      %Equal.sym(Bool, Char.is_eq(c, c), True{}, Diff.char_eq_refl(c)) : {Bool.pick(Maybe<&2, String>, _, T.strip_prefix(String.append(t, r), t), None{}) == Some{r} : Maybe<&2, String>}
      strip_app(t, r)

def names_pick(b: Bool, +n: String, +rest: String, ih: {Main.dry.rest(Some{rest}) == True{} : Bool}) -> {Main.dry.rest(Some{Bool.pick(String, b, "  " ++ n, SNil{}) ++ rest}) == True{} : Bool}:
  match b:
    case True{}:
      B.sw_ext("  " ++ n, "  ", rest, B.sw_ext("  ", "  ", n, B.sw_refl("  ")))
    case False{}:
      ih

# What follows a revision on its line, if anything, begins with two spaces:
# the bookmarks there.
def names_two(bs: List<&2, Bm.Bookmark>, +h: Rev.History(), +x: String) -> {Main.dry.rest(Some{Main.names_at(bs, h, x)}) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Bm.Bookmark{+n, +t, p} <> +rest:
      names_pick(Main.names_at.one(h, x, t), n, Main.names_at(rest, h, x), names_two(rest, h, x))

# A revision's line names it by its first twelve letters.
def names_line(+bs: List<&2, Bm.Bookmark>, +h: Rev.History(), +x: String) -> {Main.dry.names(x, "would abandon " ++ (Main.ab12(x) ++ Main.names_at(bs, h, x))) == True{} : Bool}:
  Equal.trans(Bool, Main.dry.rest(T.strip_prefix(String.append("would abandon " ++ String.take(x, 12n), Main.names_at(bs, h, x)), "would abandon " ++ String.take(x, 12n))), Main.dry.rest(Some{Main.names_at(bs, h, x)}), True{},
    Equal.cong(Maybe<&2, String>, Bool, m => Main.dry.rest(m), T.strip_prefix(String.append("would abandon " ++ String.take(x, 12n), Main.names_at(bs, h, x)), "would abandon " ++ String.take(x, 12n)), Some{Main.names_at(bs, h, x)}, strip_app("would abandon " ++ String.take(x, 12n), Main.names_at(bs, h, x))),
    names_two(bs, h, x))

def carry_start(ys: List<&2, String>, +rest: List<&2, String>, hr: {Main.lines.start(rest, "would carry ") == True{} : Bool}) -> {Main.lines.start(List.append(&2, String, Main.each.lines("would carry ", ys), rest), "would carry ") == True{} : Bool}:
  match ys:
    case Nil{}:
      hr
    case +y <> more:
      B.and_tt(String.starts_with("would carry " ++ y, "would carry "), Main.lines.start(List.append(&2, String, Main.each.lines("would carry ", more), rest), "would carry "),
        B.sw_ext("would carry ", "would carry ", y, B.sw_refl("would carry ")),
        carry_start(more, rest, hr))

# Each revision of the run gets its line, in order.
def said_run(xs: List<&2, String>, +bs: List<&2, Bm.Bookmark>, +h: Rev.History(), +rest: List<&2, String>, hr: {Main.dry.said(Nil{}, rest) == True{} : Bool}) -> {Main.dry.said(xs, List.append(&2, String, Main.each.lines("would abandon ", Main.spelled_all(bs, h, xs)), rest)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hr
    case +x <> +more:
      B.and_tt(Main.dry.names(x, "would abandon " ++ (Main.ab12(x) ++ Main.names_at(bs, h, x))), Main.dry.said(more, List.append(&2, String, Main.each.lines("would abandon ", Main.spelled_all(bs, h, more)), rest)),
        names_line(bs, h, x),
        said_run(more, bs, h, rest, hr))

# What `abandon --dry-run` says: each revision of the run, the tombstone,
# and what it would carry.
def dry_names(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +only: Bool, +run: List<&2, String>) -> {Main.dry.said(run, Main.abandon.dry.lines(fs, bs, id, only, run)) == True{} : Bool}:
  +n = List.length(&2, String, run)
  +said = Bool.pick(String, Nat.is_eq(n, 1n), "this revision", "these " ++ Nat.show(n) ++ " revisions") ++ ", and its message is required"
  +carried = Main.each.lines("would carry ", Main.map12(Bool.pick(List<&2, String>, only, Main.would_carry(fs, id, Main.standing_on(fs, id)), Nil{})))
  said_run(run, bs, Main.history(fs), List.concat(&2, String, [["a tombstone would supersede " ++ said], carried]),
    B.and_tt(String.starts_with("a tombstone would supersede " ++ said, "a tombstone would supersede "), Main.lines.start(List.append(&2, String, carried, Nil{}), "would carry "),
      B.sw_ext("a tombstone would supersede ", "a tombstone would supersede ", said, B.sw_refl("a tombstone would supersede ")),
      carry_start(Main.map12(Bool.pick(List<&2, String>, only, Main.would_carry(fs, id, Main.standing_on(fs, id)), Nil{})), Nil{}, {==})))
