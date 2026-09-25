# What `arrange` plans. Every rename it plans goes to a path nothing in the
# store was at, from a different one; without `--refile`, a revision
# document is renamed only within the directory it sits in; and it opens no
# store holding a revision document whose text does not parse. What it
# reads its words as is `words_lemmas.bend`'s.
import Base
import ./arrange.bend as Arrange
import ./commands.bend as Main
import ./text.bend as T
import ./naming.bend as Naming
import ./blamed_lemmas.bend as B
import ./name_lemmas.bend as NameL
import ./string_lemmas.bend as S
import ./position_lemmas.bend as Pos
import ./revision_lemmas.bend as RevL
import ./store.bend as Store
import ./revision.bend as Rev
import ./tree.bend as Tree
import ./map_lemmas.bend as ML

# Placing one file
# ----------------

def done_placing(-a: Arrange.Placing, -b: Arrange.Placing, h: {Done{a} == Done{b} : Result<&2, &2, Main.Refused, Arrange.Placing>}) -> {a == b : Arrange.Placing}:
  B.done_eq(Arrange.Placing, a, b, h)

def done_list(-a: List<&2, Arrange.Placing>, -b: List<&2, Arrange.Placing>, h: {Done{a} == Done{b} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>}) -> {a == b : List<&2, Arrange.Placing>}:
  B.done_eq(List<&2, Arrange.Placing>, a, b, h)

def done_plan(-a: Arrange.Arrangement, -b: Arrange.Arrangement, h: {Done{a} == Done{b} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}) -> {a == b : Arrange.Arrangement}:
  B.done_eq(Arrange.Arrangement, a, b, h)

def place_free(+held: Set(), +path: String, +target: String, c: Bool, e2: {Arrange.has(held, target) == c : Bool}, e1: {String.eq(path, target) == False{} : Bool}) -> {Arrange.rename_safe(held, Bool.pick(Arrange.Placing, c, Arrange.Placing.Occupied{path, target}, Arrange.Placing.Rename{path, target})) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, String.eq(path, target), False{}, e1) : {Bool.and(Bool.not(_), Bool.not(Arrange.has(held, target))) == True{} : Bool}
      %Equal.sym(Bool, Arrange.has(held, target), False{}, e2) : {Bool.and(True{}, Bool.not(_)) == True{} : Bool}
      {==}

def place_moved(+held: Set(), +path: String, +target: String, c: Bool, e1: {String.eq(path, target) == c : Bool}) -> {Arrange.rename_safe(held, Bool.pick(Arrange.Placing, c, Arrange.Placing.Already{path}, Bool.pick(Arrange.Placing, Arrange.has(held, target), Arrange.Placing.Occupied{path, target}, Arrange.Placing.Rename{path, target}))) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      place_free(held, path, target, Arrange.has(held, target), {==}, e1)

# A file is placed where it is, left where its name is taken, or renamed
# to a name nothing holds, from a path that is not that name.
def place_safe(+held: Set(), +path: String, +target: String) -> {Arrange.rename_safe(held, Arrange.place(held, path, target)) == True{} : Bool}:
  place_moved(held, path, target, String.eq(path, target), {==})

def op_safe(+held: Set(), +path: String, name: Maybe<&2, String>) -> {Arrange.rename_safe(held, Arrange.op.placed(held, path, name)) == True{} : Bool}:
  match name:
    case None{}:
      {==}
    case Some{+n}:
      place_safe(held, path, "operations/" ++ n)

def ops_safe(ds: List<&2, T.Split>, +held: Set(), +names: List<&2, T.Split>) -> {Arrange.renames_safe(Arrange.ops.placed(ds, held, names), held) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case T.Split{+path, +id} <> +rest:
      B.and_tt(Arrange.rename_safe(held, Arrange.op.placed(held, path, Arrange.lookup(names, id))), Arrange.renames_safe(Arrange.ops.placed(rest, held, names), held),
        op_safe(held, path, Arrange.lookup(names, id)), ops_safe(rest, held, names))

def rev_safe(+refile: Bool, +held: Set(), +path: String, stem: Maybe<&2, String>, +x: Arrange.Placing, e: {Arrange.rev.placed(refile, held, path, stem) == Done{x} : Result<&2, &2, Main.Refused, Arrange.Placing>}) -> {Arrange.rename_safe(held, x) == True{} : Bool}:
  match stem:
    case None{}:
      Empty.absurd({Arrange.rename_safe(held, x) == True{} : Bool}, B.fail_done(Arrange.Placing, Main.Refused{1, path ++ " changed while it was being arranged"}, x, e))
    case Some{+s}:
      %done_placing(Arrange.place(held, path, Arrange.rev.target(refile, path, s)), x, e) : {Arrange.rename_safe(held, _) == True{} : Bool}
      place_safe(held, path, Arrange.rev.target(refile, path, s))

# A plan's renames, each safe, joined, are safe; a refusal is no plan.
def cons_safe(+held: Set(), p: Result<&2, &2, Main.Refused, Arrange.Placing>, r: Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>, +ps: List<&2, Arrange.Placing>, e: {Arrange.placed.cons(p, r) == Done{ps} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>}, hp: @x: Arrange.Placing -> {p == Done{x} : Result<&2, &2, Main.Refused, Arrange.Placing>} -> {Arrange.rename_safe(held, x) == True{} : Bool}, hr: @xs: List<&2, Arrange.Placing> -> {r == Done{xs} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>} -> {Arrange.renames_safe(xs, held) == True{} : Bool}) -> {Arrange.renames_safe(ps, held) == True{} : Bool}:
  match p r:
    case Fail{x} _:
      Empty.absurd({Arrange.renames_safe(ps, held) == True{} : Bool}, B.fail_done(List<&2, Arrange.Placing>, x, ps, e))
    case Done{x} Fail{y}:
      Empty.absurd({Arrange.renames_safe(ps, held) == True{} : Bool}, B.fail_done(List<&2, Arrange.Placing>, y, ps, e))
    case Done{+x} Done{+xs}:
      %done_list(x <> xs, ps, e) : {Arrange.renames_safe(_, held) == True{} : Bool}
      B.and_tt(Arrange.rename_safe(held, x), Arrange.renames_safe(xs, held), hp(x, {==}), hr(xs, {==}))

def revs_safe(ds: List<&2, T.Split>, +refile: Bool, +held: Set(), +ss: List<&2, T.Split>, +ps: List<&2, Arrange.Placing>, e: {Arrange.revs.placed(ds, refile, held, ss) == Done{ps} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>}) -> {Arrange.renames_safe(ps, held) == True{} : Bool}:
  match ds:
    case Nil{}:
      %done_list(Nil{}, ps, e) : {Arrange.renames_safe(_, held) == True{} : Bool}
      {==}
    case T.Split{+path, +id} <> +rest:
      cons_safe(held, Arrange.rev.placed(refile, held, path, Arrange.lookup(ss, id)), Arrange.revs.placed(rest, refile, held, ss), ps, e,
        x => h => rev_safe(refile, held, path, Arrange.lookup(ss, id), x, h),
        xs => h => revs_safe(rest, refile, held, ss, xs, h))

# The plan
# --------

def placed_safe(+held: Set(), +ops: List<&2, T.Split>, +names: List<&2, T.Split>, rp: Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>, +a: Arrange.Arrangement, e: {Arrange.arrangement.placed(held, ops, names, rp) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}, hr: @xs: List<&2, Arrange.Placing> -> {rp == Done{xs} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>} -> {Arrange.renames_safe(xs, held) == True{} : Bool}) -> {Arrange.plan_safe(held, a) == True{} : Bool}:
  match rp:
    case Fail{x}:
      Empty.absurd({Arrange.plan_safe(held, a) == True{} : Bool}, B.fail_done(Arrange.Arrangement, x, a, e))
    case Done{+ps}:
      %done_plan(Arrange.Arrangement{ps, Arrange.ops.placed(ops, held, names)}, a, e) : {Arrange.plan_safe(held, _) == True{} : Bool}
      B.and_tt(Arrange.renames_safe(ps, held), Arrange.renames_safe(Arrange.ops.placed(ops, held, names), held), hr(ps, {==}), ops_safe(ops, held, names))

def named_safe(+refile: Bool, +held: Set(), +ss: List<&2, T.Split>, +revs: List<&2, T.Split>, +ops: List<&2, T.Split>, names: Result<&2, &2, Main.Refused, List<&2, T.Split>>, +a: Arrange.Arrangement, e: {Arrange.arrangement.named(refile, held, ss, revs, ops, names) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}) -> {Arrange.plan_safe(held, a) == True{} : Bool}:
  match names:
    case Fail{x}:
      Empty.absurd({Arrange.plan_safe(held, a) == True{} : Bool}, B.fail_done(Arrange.Arrangement, x, a, e))
    case Done{+ns}:
      placed_safe(held, ops, ns, Arrange.revs.placed(revs, refile, held, ss), a, e, xs => h => revs_safe(revs, refile, held, ss, xs, h))

# `arrange` never plans to write over a file.
def plan_safe(+refile: Bool, +fs: List<&2, Main.Full>, +revs: List<&2, T.Split>, +ops: List<&2, T.Split>, +ls: List<&2, String>, +a: Arrange.Arrangement, e: {Arrange.arrangement.r(refile, fs, revs, ops, ls) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}) -> {Arrange.plan_safe(Arrange.taken(ls), a) == True{} : Bool}:
  named_safe(refile, Arrange.taken(ls), Arrange.stems(Arrange.distinct(fs)), revs, ops, Arrange.operation_names(fs, Arrange.stems(Arrange.distinct(fs))), a, e)

# Opening
# -------

def mdisc_r(m: Maybe<&2, Main.Refused>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{x}:
      Unit

def some_none_r(-x: Main.Refused, e: {Some{x} == None{} : Maybe<&2, Main.Refused>}) -> Empty:
  %e : {mdisc_r(_) : Type}
  Unit{}

def or_left(a: Maybe<&2, Main.Refused>, -b: Maybe<&2, Main.Refused>, e: {Maybe.or(&2, Main.Refused, a, b) == None{} : Maybe<&2, Main.Refused>}) -> {a == None{} : Maybe<&2, Main.Refused>}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, Main.Refused>}, some_none_r(x, e))

def or_right(a: Maybe<&2, Main.Refused>, -b: Maybe<&2, Main.Refused>, e: {Maybe.or(&2, Main.Refused, a, b) == None{} : Maybe<&2, Main.Refused>}) -> {b == None{} : Maybe<&2, Main.Refused>}:
  match a:
    case None{}:
      e
    case Some{x}:
      Empty.absurd({b == None{} : Maybe<&2, Main.Refused>}, some_none_r(x, e))

def fault_parses(+path: String, r: Result<&2, &2, String, Rev.Rev>, e: {Arrange.parse_fault(path, r) == None{} : Maybe<&2, Main.Refused>}) -> {Bool.not(Arrange.rev.fails(r)) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Bool.not(Arrange.rev.fails(Fail{x})) == True{} : Bool}, some_none_r(Main.Refused{1, path ++ ": " ++ x}, e))
    case Done{x}:
      {==}

def faults_none(ds: List<&2, Store.Doc>, +e: {Arrange.first_fault(ds) == None{} : Maybe<&2, Main.Refused>}) -> {Arrange.all_parse(ds) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Store.Doc{+path, +id, +size, +text} <> +rest:
      B.and_tt(Bool.not(Arrange.rev.fails(Rev.parse(text))), Arrange.all_parse(rest),
        fault_parses(path, Rev.parse(text), or_left(Arrange.parse_fault(path, Rev.parse(text)), Arrange.first_fault(rest), e)),
        faults_none(rest, or_right(Arrange.parse_fault(path, Rev.parse(text)), Arrange.first_fault(rest), e)))

def of_found(found: Maybe<&2, Main.Refused>, -u: Unit, e: {Arrange.opened.of(found) == Done{u} : Result<&2, &2, Main.Refused, Unit>}) -> {found == None{} : Maybe<&2, Main.Refused>}:
  match found:
    case Some{r}:
      Empty.absurd({Some{r} == None{} : Maybe<&2, Main.Refused>}, B.fail_done(Unit, r, u, e))
    case None{}:
      {==}

# A store is opened only where every revision document in it parses.
def opened(+ds: List<&2, Store.Doc>, -u: Unit, e: {Arrange.opened.r(ds) == Done{u} : Result<&2, &2, Main.Refused, Unit>}) -> {Arrange.all_parse(Arrange.revision_docs(ds)) == True{} : Bool}:
  faults_none(Arrange.revision_docs(ds), of_found(Arrange.first_fault(Arrange.revision_docs(ds)), u, e))

def and_false_r(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def bad_step(c: Bool, +q: Store.Doc, -r: List<&2, Store.Doc>, ih: {Arrange.all_parse(r) == False{} : Bool}) -> {Arrange.all_parse(Tree.keep(~Store.Doc, c, q, r)) == False{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, Arrange.all_parse(r), False{}, ih) : {Bool.and(Arrange.parses(q), _) == False{} : Bool}
      and_false_r(Arrange.parses(q))
    case False{}:
      ih

# Whatever else a store holds, a revision document among its files whose
# text does not parse is one the check that every revision parses finds.
def bad_parse(pre: List<&2, Store.Doc>, +path: String, +id: String, +size: Nat, +text: String, +post: List<&2, Store.Doc>, +msg: String, +hp: {String.ends_with(path, ".rev.txt") == True{} : Bool}, +hf: {Rev.parse(text) == Fail{msg} : Result<&2, &2, String, Rev.Rev>}) -> {Arrange.all_parse(Arrange.revision_docs(List.append(&2, Store.Doc, pre, Store.Doc{path, id, size, text} <> post))) == False{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, String.ends_with(path, ".rev.txt"), True{}, hp) : {Arrange.all_parse(Tree.keep(~Store.Doc, _, Store.Doc{path, id, size, text}, Arrange.revision_docs(post))) == False{} : Bool}
      %Equal.sym(Result<&2, &2, String, Rev.Rev>, Rev.parse(text), Fail{msg}, hf) : {Bool.and(Bool.not(Arrange.rev.fails(_)), Arrange.all_parse(Arrange.revision_docs(post))) == False{} : Bool}
      {==}
    case +q <> +rest:
      bad_step(Arrange.claims_revision(Store.path_of(q)), q, Arrange.revision_docs(List.append(&2, Store.Doc, rest, Store.Doc{path, id, size, text} <> post)), bad_parse(rest, path, id, size, text, post, msg, hp, hf))

def opens_r(r: Result<&2, &2, Main.Refused, Unit>, +ds: List<&2, Store.Doc>, e: {Arrange.opened.r(ds) == r : Result<&2, &2, Main.Refused, Unit>}, hb: {Arrange.all_parse(Arrange.revision_docs(ds)) == False{} : Bool}) -> {Result.is_done(&2, &2, Main.Refused, Unit, r) == False{} : Bool}:
  match r:
    case Fail{x}:
      {==}
    case Done{u}:
      Empty.absurd({Result.is_done(&2, &2, Main.Refused, Unit, Done{u}) == False{} : Bool}, S.false_true(Equal.trans(Bool, False{}, Arrange.all_parse(Arrange.revision_docs(ds)), True{}, Equal.sym(Bool, Arrange.all_parse(Arrange.revision_docs(ds)), False{}, hb), opened(ds, u, e))))

# `arrange` opens no store holding a revision document whose text does not
# parse, whatever else the store holds.
def opens(+pre: List<&2, Store.Doc>, +path: String, +id: String, +size: Nat, +text: String, +post: List<&2, Store.Doc>, +msg: String, hp: {String.ends_with(path, ".rev.txt") == True{} : Bool}, hf: {Rev.parse(text) == Fail{msg} : Result<&2, &2, String, Rev.Rev>}) -> {Result.is_done(&2, &2, Main.Refused, Unit, Arrange.opened.r(List.append(&2, Store.Doc, pre, Store.Doc{path, id, size, text} <> post))) == False{} : Bool}:
  opens_r(Arrange.opened.r(List.append(&2, Store.Doc, pre, Store.Doc{path, id, size, text} <> post)), List.append(&2, Store.Doc, pre, Store.Doc{path, id, size, text} <> post), {==}, bad_parse(pre, path, id, size, text, post, msg, hp, hf))

# Counting
# --------

def succ_eq(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  Equal.cong(Nat, Nat, n => 1n+n, a, b, e)

def succ_out(x: Nat, -y: Nat) -> {1n+Nat.add(x, y) == Nat.add(x, 1n+y) : Nat}:
  Equal.sym(Nat, Nat.add(x, 1n+y), 1n+Nat.add(x, y), Pos.add_succ(x, y))

# The four counts a directory's report ends with, added up: renamed,
# already arranged, left as duplicates, and named by no revision.
def tally(c: Arrange.Came) -> Nat:
  match c:
    case Arrange.Came{rs, a, os, u}:
      Nat.add(List.length(&2, T.Split, rs), Nat.add(a, Nat.add(List.length(&2, T.Split, os), u)))

# The four counts a report prints for a plan add up to its files.
def tally_planned(ps: List<&2, Arrange.Placing>) -> {tally(Arrange.planned(ps)) == List.length(&2, Arrange.Placing, ps) : Nat}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +rest:
      match p:
        case Arrange.Placing.Rename{+f, +t}:
          succ_eq(tally(Arrange.planned(rest)), List.length(&2, Arrange.Placing, rest), tally_planned(rest))
        case Arrange.Placing.Already{+f}:
          %succ_out(List.length(&2, T.Split, Arrange.done.renamed(rest)), Nat.add(Arrange.done.already(rest), Nat.add(List.length(&2, T.Split, Arrange.done.occupied(rest)), Arrange.done.unnamed(rest)))) : {_ == 1n+List.length(&2, Arrange.Placing, rest) : Nat}
          succ_eq(tally(Arrange.planned(rest)), List.length(&2, Arrange.Placing, rest), tally_planned(rest))
        case Arrange.Placing.Occupied{+f, +h}:
          %succ_out(Arrange.done.already(rest), Nat.add(List.length(&2, T.Split, Arrange.done.occupied(rest)), Arrange.done.unnamed(rest))) : {Nat.add(List.length(&2, T.Split, Arrange.done.renamed(rest)), _) == 1n+List.length(&2, Arrange.Placing, rest) : Nat}
          %succ_out(List.length(&2, T.Split, Arrange.done.renamed(rest)), Nat.add(Arrange.done.already(rest), Nat.add(List.length(&2, T.Split, Arrange.done.occupied(rest)), Arrange.done.unnamed(rest)))) : {_ == 1n+List.length(&2, Arrange.Placing, rest) : Nat}
          succ_eq(tally(Arrange.planned(rest)), List.length(&2, Arrange.Placing, rest), tally_planned(rest))
        case Arrange.Placing.Unnamed{+f}:
          %succ_out(List.length(&2, T.Split, Arrange.done.occupied(rest)), Arrange.done.unnamed(rest)) : {Nat.add(List.length(&2, T.Split, Arrange.done.renamed(rest)), Nat.add(Arrange.done.already(rest), _)) == 1n+List.length(&2, Arrange.Placing, rest) : Nat}
          %succ_out(Arrange.done.already(rest), Nat.add(List.length(&2, T.Split, Arrange.done.occupied(rest)), Arrange.done.unnamed(rest))) : {Nat.add(List.length(&2, T.Split, Arrange.done.renamed(rest)), _) == 1n+List.length(&2, Arrange.Placing, rest) : Nat}
          %succ_out(List.length(&2, T.Split, Arrange.done.renamed(rest)), Nat.add(Arrange.done.already(rest), Nat.add(List.length(&2, T.Split, Arrange.done.occupied(rest)), Arrange.done.unnamed(rest)))) : {_ == 1n+List.length(&2, Arrange.Placing, rest) : Nat}
          succ_eq(tally(Arrange.planned(rest)), List.length(&2, Arrange.Placing, rest), tally_planned(rest))

def ops_length(ds: List<&2, T.Split>, +held: Set(), +names: List<&2, T.Split>) -> {List.length(&2, Arrange.Placing, Arrange.ops.placed(ds, held, names)) == List.length(&2, T.Split, ds) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case T.Split{+path, +id} <> +rest:
      succ_eq(List.length(&2, Arrange.Placing, Arrange.ops.placed(rest, held, names)), List.length(&2, T.Split, rest), ops_length(rest, held, names))

def cons_length(p: Result<&2, &2, Main.Refused, Arrange.Placing>, r: Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>, +ps: List<&2, Arrange.Placing>, -n: Nat, e: {Arrange.placed.cons(p, r) == Done{ps} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>}, hr: @xs: List<&2, Arrange.Placing> -> {r == Done{xs} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>} -> {List.length(&2, Arrange.Placing, xs) == n : Nat}) -> {List.length(&2, Arrange.Placing, ps) == 1n+n : Nat}:
  match p r:
    case Fail{x} _:
      Empty.absurd({List.length(&2, Arrange.Placing, ps) == 1n+n : Nat}, B.fail_done(List<&2, Arrange.Placing>, x, ps, e))
    case Done{x} Fail{y}:
      Empty.absurd({List.length(&2, Arrange.Placing, ps) == 1n+n : Nat}, B.fail_done(List<&2, Arrange.Placing>, y, ps, e))
    case Done{+x} Done{+xs}:
      %done_list(x <> xs, ps, e) : {List.length(&2, Arrange.Placing, _) == 1n+n : Nat}
      succ_eq(List.length(&2, Arrange.Placing, xs), n, hr(xs, {==}))

def revs_length(ds: List<&2, T.Split>, +refile: Bool, +held: Set(), +ss: List<&2, T.Split>, +ps: List<&2, Arrange.Placing>, e: {Arrange.revs.placed(ds, refile, held, ss) == Done{ps} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>}) -> {List.length(&2, Arrange.Placing, ps) == List.length(&2, T.Split, ds) : Nat}:
  match ds:
    case Nil{}:
      %done_list(Nil{}, ps, e) : {List.length(&2, Arrange.Placing, _) == 0n : Nat}
      {==}
    case T.Split{+path, +id} <> +rest:
      cons_length(Arrange.rev.placed(refile, held, path, Arrange.lookup(ss, id)), Arrange.revs.placed(rest, refile, held, ss), ps, List.length(&2, T.Split, rest), e,
        xs => h => revs_length(rest, refile, held, ss, xs, h))

# Sets, read as lists
# -------------------

def found_hv(r: Set() & Bool) -> {Arrange.found(r) == ML.hv(Unit, r) : Bool}:
  match r:
    case (m, b):
      {==}

# A set built from a list has exactly the list's strings, so a law may say
# what the code asks of a set as a plain fact about the list it was built
# from.
def has_list(+xs: List<&2, String>, +k: String) -> {Arrange.has(Set.from_list(xs), k) == Rev.member(xs, k) : Bool}:
  Equal.trans(Bool, Arrange.has(Set.from_list(xs), k), ML.hv(Unit, Set.has(Set.from_list(xs), k)), Rev.member(xs, k), found_hv(Set.has(Set.from_list(xs), k)), ML.set_from_list(xs, k))

def or_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# A string is in two lists one after the other where it is in either.
def member_app(xs: List<&2, String>, +ys: List<&2, String>, +d: String) -> {Rev.member(List.append(&2, String, xs, ys), d) == Bool.or(Rev.member(xs, d), Rev.member(ys, d)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, Rev.member(List.append(&2, String, rest, ys), d), Bool.or(Rev.member(rest, d), Rev.member(ys, d)), member_app(rest, ys, d)) : {Bool.or(String.eq(x, d), _) == Bool.or(Rev.member(x <> rest, d), Rev.member(ys, d)) : Bool}
      or_assoc(String.eq(x, d), Rev.member(rest, d), Rev.member(ys, d))

# Booleans
# --------

def or_ff_l(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, S.true_false(e))
    case False{}:
      {==}

def or_ff_r(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, S.true_false(e))
    case False{}:
      e

def or_ff(a: Bool, -b: Bool, ea: {a == False{} : Bool}, eb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({Bool.or(True{}, b) == False{} : Bool}, S.true_false(ea))
    case False{}:
      eb

def and_tl(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(e))

def and_tr(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, S.false_true(e))

def not_tt(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, S.false_true(e))
    case False{}:
      {==}

def not_ff(b: Bool, e: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, S.true_false(e))
    case False{}:
      {==}

# Of an `or` that holds, the right side holds where the left does not.
def or_tt_r(a: Bool, -b: Bool, e: {Bool.or(a, b) == True{} : Bool}, ea: {a == False{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == True{} : Bool}, S.true_false(ea))
    case False{}:
      e

def and_ff_l(a: Bool, -b: Bool, e: {a == False{} : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({Bool.and(True{}, b) == False{} : Bool}, S.true_false(e))
    case False{}:
      {==}

def and_ff_r(a: Bool, -b: Bool, e: {b == False{} : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      {==}

# What arranging moves
# --------------------

# Whether a list of renames holds one from `from` to `to`.
def moves(rs: List<&2, T.Split>, +from: String, +to: String) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case T.Split{+f, +t} <> rest:
      Bool.or(Bool.and(String.eq(f, from), String.eq(t, to)), moves(rest, from, to))

def moves_app(xs: List<&2, T.Split>, +ys: List<&2, T.Split>, +from: String, +to: String) -> {moves(List.append(&2, T.Split, xs, ys), from, to) == Bool.or(moves(xs, from, to), moves(ys, from, to)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case T.Split{+f, +t} <> +rest:
      %Equal.sym(Bool, moves(List.append(&2, T.Split, rest, ys), from, to), Bool.or(moves(rest, from, to), moves(ys, from, to)), moves_app(rest, ys, from, to)) : {Bool.or(Bool.and(String.eq(f, from), String.eq(t, to)), _) == Bool.or(moves(T.Split{f, t} <> rest, from, to), moves(ys, from, to)) : Bool}
      or_assoc(Bool.and(String.eq(f, from), String.eq(t, to)), moves(rest, from, to), moves(ys, from, to))

# A rename that is the one asked about goes where its plan found nothing,
# from a different path; any other leaves the question to the rest.
def rename_hit(c: Bool, +held: Set(), +f: String, +t: String, +from: String, +to: String, +ec: {Bool.and(String.eq(f, from), String.eq(t, to)) == c : Bool}, +hs: {Bool.and(Bool.not(String.eq(f, t)), Bool.not(Arrange.has(held, t))) == True{} : Bool}, -rest: List<&2, T.Split>, hm: {Bool.or(c, moves(rest, from, to)) == True{} : Bool}, ih: {moves(rest, from, to) == True{} : Bool} -> {Bool.or(String.eq(from, to), Arrange.has(held, to)) == False{} : Bool}) -> {Bool.or(String.eq(from, to), Arrange.has(held, to)) == False{} : Bool}:
  match c:
    case True{}:
      +ef = S.eq_true(f, from, and_tl(String.eq(f, from), String.eq(t, to), ec))
      +et = S.eq_true(t, to, and_tr(String.eq(f, from), String.eq(t, to), ec))
      %ef : {Bool.or(String.eq(_, to), Arrange.has(held, to)) == False{} : Bool}
      %et : {Bool.or(String.eq(f, _), Arrange.has(held, _)) == False{} : Bool}
      or_ff(String.eq(f, t), Arrange.has(held, t),
        not_tt(String.eq(f, t), and_tl(Bool.not(String.eq(f, t)), Bool.not(Arrange.has(held, t)), hs)),
        not_tt(Arrange.has(held, t), and_tr(Bool.not(String.eq(f, t)), Bool.not(Arrange.has(held, t)), hs)))
    case False{}:
      ih(hm)

# Every rename a directory's plan carries out goes where its plan found
# nothing, from a different path.
def renamed_safe(ps: List<&2, Arrange.Placing>, +held: Set(), +from: String, +to: String, +hs: {Arrange.renames_safe(ps, held) == True{} : Bool}, hm: {moves(Arrange.done.renamed(ps), from, to) == True{} : Bool}) -> {Bool.or(String.eq(from, to), Arrange.has(held, to)) == False{} : Bool}:
  match ps:
    case Nil{}:
      Empty.absurd({Bool.or(String.eq(from, to), Arrange.has(held, to)) == False{} : Bool}, S.false_true(hm))
    case +p <> +rest:
      match p:
        case Arrange.Placing.Rename{+f, +t}:
          rename_hit(Bool.and(String.eq(f, from), String.eq(t, to)), held, f, t, from, to, {==},
            and_tl(Arrange.rename_safe(held, Arrange.Placing.Rename{f, t}), Arrange.renames_safe(rest, held), hs), Arrange.done.renamed(rest), hm,
            h => renamed_safe(rest, held, from, to, and_tr(Arrange.rename_safe(held, Arrange.Placing.Rename{f, t}), Arrange.renames_safe(rest, held), hs), h))
        case Arrange.Placing.Already{+f}:
          renamed_safe(rest, held, from, to, and_tr(True{}, Arrange.renames_safe(rest, held), hs), hm)
        case Arrange.Placing.Occupied{+f, +h}:
          renamed_safe(rest, held, from, to, and_tr(True{}, Arrange.renames_safe(rest, held), hs), hm)
        case Arrange.Placing.Unnamed{+f}:
          renamed_safe(rest, held, from, to, and_tr(True{}, Arrange.renames_safe(rest, held), hs), hm)

# A set built from a list lacks a string where the list does.
def has_false(+xs: List<&2, String>, +k: String, h: {Arrange.has(Set.from_list(xs), k) == False{} : Bool}) -> {Rev.member(xs, k) == False{} : Bool}:
  Equal.trans(Bool, Rev.member(xs, k), Arrange.has(Set.from_list(xs), k), False{}, Equal.sym(Bool, Arrange.has(Set.from_list(xs), k), Rev.member(xs, k), has_list(xs, k)), h)

def app_false(+xs: List<&2, String>, +ys: List<&2, String>, +k: String, h: {Rev.member(List.append(&2, String, xs, ys), k) == False{} : Bool}) -> {Bool.or(Rev.member(xs, k), Rev.member(ys, k)) == False{} : Bool}:
  Equal.trans(Bool, Bool.or(Rev.member(xs, k), Rev.member(ys, k)), Rev.member(List.append(&2, String, xs, ys), k), False{}, Equal.sym(Bool, Rev.member(List.append(&2, String, xs, ys), k), Bool.or(Rev.member(xs, k), Rev.member(ys, k)), member_app(xs, ys, k)), h)

def taken_list(+ls: List<&2, String>, +to: String, h: {Arrange.has(Arrange.taken(ls), to) == False{} : Bool}) -> {Rev.member(ls, to) == False{} : Bool}:
  or_ff_l(Rev.member(ls, to), Rev.member(List.concat(&2, String, T.map(~String, ~List<&2, String>, ~(n => Naming.prefixes(n)), ls)), to),
    app_false(ls, List.concat(&2, String, T.map(~String, ~List<&2, String>, ~(n => Naming.prefixes(n)), ls)), to,
      has_false(List.append(&2, String, ls, List.concat(&2, String, T.map(~String, ~List<&2, String>, ~(n => Naming.prefixes(n)), ls))), to, h)))

def either_safe(c: Bool, +held: Set(), +rs: List<&2, Arrange.Placing>, +os: List<&2, Arrange.Placing>, +from: String, +to: String, +ec: {moves(Arrange.done.renamed(rs), from, to) == c : Bool}, +hr: {Arrange.renames_safe(rs, held) == True{} : Bool}, +ho: {Arrange.renames_safe(os, held) == True{} : Bool}, h: {Bool.or(c, moves(Arrange.done.renamed(os), from, to)) == True{} : Bool}) -> {Bool.or(String.eq(from, to), Arrange.has(held, to)) == False{} : Bool}:
  match c:
    case True{}:
      renamed_safe(rs, held, from, to, hr, ec)
    case False{}:
      renamed_safe(os, held, from, to, ho, h)

def plan_moves(+held: Set(), a: Arrange.Arrangement, +from: String, +to: String, +hs: {Arrange.plan_safe(held, a) == True{} : Bool}, h: {moves(List.append(&2, T.Split, Arrange.done.renamed(Arrange.arrangement.revs(a)), Arrange.done.renamed(Arrange.arrangement.ops(a))), from, to) == True{} : Bool}) -> {Bool.or(String.eq(from, to), Arrange.has(held, to)) == False{} : Bool}:
  match a:
    case Arrange.Arrangement{+rs, +os}:
      either_safe(moves(Arrange.done.renamed(rs), from, to), held, rs, os, from, to, {==},
        and_tl(Arrange.renames_safe(rs, held), Arrange.renames_safe(os, held), hs), and_tr(Arrange.renames_safe(rs, held), Arrange.renames_safe(os, held), hs),
        Equal.trans(Bool, Bool.or(moves(Arrange.done.renamed(rs), from, to), moves(Arrange.done.renamed(os), from, to)), moves(List.append(&2, T.Split, Arrange.done.renamed(rs), Arrange.done.renamed(os)), from, to), True{},
          Equal.sym(Bool, moves(List.append(&2, T.Split, Arrange.done.renamed(rs), Arrange.done.renamed(os)), from, to), Bool.or(moves(Arrange.done.renamed(rs), from, to), moves(Arrange.done.renamed(os), from, to)), moves_app(Arrange.done.renamed(rs), Arrange.done.renamed(os), from, to)), h))

# `arrange` never plans to write over a file: every rename it carries out,
# in either directory, goes from one path to a different one the store's
# listing does not hold.
def no_overwrite(+refile: Bool, +fs: List<&2, Main.Full>, +revs: List<&2, T.Split>, +ops: List<&2, T.Split>, +ls: List<&2, String>, +a: Arrange.Arrangement, +e: {Arrange.arrangement.r(refile, fs, revs, ops, ls) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}, +from: String, +to: String, +h: {moves(List.append(&2, T.Split, Arrange.done.renamed(Arrange.arrangement.revs(a)), Arrange.done.renamed(Arrange.arrangement.ops(a))), from, to) == True{} : Bool}) -> {Bool.or(String.eq(from, to), Rev.member(ls, to)) == False{} : Bool}:
  +hp = plan_moves(Arrange.taken(ls), a, from, to, plan_safe(refile, fs, revs, ops, ls, a, e), h)
  or_ff(String.eq(from, to), Rev.member(ls, to), or_ff_l(String.eq(from, to), Arrange.has(Arrange.taken(ls), to), hp),
    taken_list(ls, to, or_ff_r(String.eq(from, to), Arrange.has(Arrange.taken(ls), to), hp)))

# Moving each file once
# ---------------------

# The first half of a pair: a file's path in a walk, or where a rename
# moves a file from.
def first(s: T.Split) -> String:
  match s:
    case T.Split{a, b}:
      a

# How many times a list holds a string.
def times(xs: List<&2, String>, +x: String) -> Nat:
  match xs:
    case Nil{}:
      0n
    case +y <> rest:
      +later = times(rest, x)
      Bool.pick(Nat, String.eq(y, x), 1n+later, later)

def placing.path(p: Arrange.Placing) -> String:
  match p:
    case Arrange.Placing.Rename{f, t}:
      f
    case Arrange.Placing.Already{f}:
      f
    case Arrange.Placing.Occupied{f, h}:
      f
    case Arrange.Placing.Unnamed{f}:
      f

def place_in(c: Bool, +path: String, +target: String) -> {placing.path(Bool.pick(Arrange.Placing, c, Arrange.Placing.Occupied{path, target}, Arrange.Placing.Rename{path, target})) == path : String}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def place_at(c: Bool, +held: Set(), +path: String, +target: String) -> {placing.path(Bool.pick(Arrange.Placing, c, Arrange.Placing.Already{path}, Bool.pick(Arrange.Placing, Arrange.has(held, target), Arrange.Placing.Occupied{path, target}, Arrange.Placing.Rename{path, target}))) == path : String}:
  match c:
    case True{}:
      {==}
    case False{}:
      place_in(Arrange.has(held, target), path, target)

# A file is placed from where it is.
def place_path(+held: Set(), +path: String, +target: String) -> {placing.path(Arrange.place(held, path, target)) == path : String}:
  place_at(String.eq(path, target), held, path, target)

def op_path(+held: Set(), +path: String, name: Maybe<&2, String>) -> {placing.path(Arrange.op.placed(held, path, name)) == path : String}:
  match name:
    case None{}:
      {==}
    case Some{+n}:
      place_path(held, path, "operations/" ++ n)

def cons_eq(+x: String, -y: String, -xs: List<&2, String>, -ys: List<&2, String>, ex: {x == y : String}, ers: {xs == ys : List<&2, String>}) -> {x <> xs == y <> ys : List<&2, String>}:
  %ex : {x <> xs == _ <> ys : List<&2, String>}
  Equal.cong(List<&2, String>, List<&2, String>, l => x <> l, xs, ys, ers)

# The files of `operations/` are placed one each, in the walk's order,
# each from where the walk found it.
def ops_paths(ds: List<&2, T.Split>, +held: Set(), +names: List<&2, T.Split>) -> {T.map(~Arrange.Placing, ~String, ~(p => placing.path(p)), Arrange.ops.placed(ds, held, names)) == T.map(~T.Split, ~String, ~(s => first(s)), ds) : List<&2, String>}:
  match ds:
    case Nil{}:
      {==}
    case T.Split{+path, +id} <> +rest:
      cons_eq(placing.path(Arrange.op.placed(held, path, Arrange.lookup(names, id))), path, T.map(~Arrange.Placing, ~String, ~(p => placing.path(p)), Arrange.ops.placed(rest, held, names)), T.map(~T.Split, ~String, ~(s => first(s)), rest),
        op_path(held, path, Arrange.lookup(names, id)), ops_paths(rest, held, names))

def rev_path(+refile: Bool, +held: Set(), +path: String, stem: Maybe<&2, String>, +x: Arrange.Placing, e: {Arrange.rev.placed(refile, held, path, stem) == Done{x} : Result<&2, &2, Main.Refused, Arrange.Placing>}) -> {placing.path(x) == path : String}:
  match stem:
    case None{}:
      Empty.absurd({placing.path(x) == path : String}, B.fail_done(Arrange.Placing, Main.Refused{1, path ++ " changed while it was being arranged"}, x, e))
    case Some{+s}:
      %done_placing(Arrange.place(held, path, Arrange.rev.target(refile, path, s)), x, e) : {placing.path(_) == path : String}
      place_path(held, path, Arrange.rev.target(refile, path, s))

def cons_paths(p: Result<&2, &2, Main.Refused, Arrange.Placing>, r: Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>, +ps: List<&2, Arrange.Placing>, +path: String, -more: List<&2, String>, e: {Arrange.placed.cons(p, r) == Done{ps} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>}, hp: @x: Arrange.Placing -> {p == Done{x} : Result<&2, &2, Main.Refused, Arrange.Placing>} -> {placing.path(x) == path : String}, hr: @xs: List<&2, Arrange.Placing> -> {r == Done{xs} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>} -> {T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), xs) == more : List<&2, String>}) -> {T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), ps) == path <> more : List<&2, String>}:
  match p r:
    case Fail{x} _:
      Empty.absurd({T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), ps) == path <> more : List<&2, String>}, B.fail_done(List<&2, Arrange.Placing>, x, ps, e))
    case Done{x} Fail{y}:
      Empty.absurd({T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), ps) == path <> more : List<&2, String>}, B.fail_done(List<&2, Arrange.Placing>, y, ps, e))
    case Done{+x} Done{+xs}:
      %done_list(x <> xs, ps, e) : {T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), _) == path <> more : List<&2, String>}
      cons_eq(placing.path(x), path, T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), xs), more, hp(x, {==}), hr(xs, {==}))

# The revision documents are placed one each, in the walk's order, each
# from where the walk found it.
def revs_paths(ds: List<&2, T.Split>, +refile: Bool, +held: Set(), +ss: List<&2, T.Split>, +ps: List<&2, Arrange.Placing>, e: {Arrange.revs.placed(ds, refile, held, ss) == Done{ps} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>}) -> {T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), ps) == T.map(~T.Split, ~String, ~(s => first(s)), ds) : List<&2, String>}:
  match ds:
    case Nil{}:
      %done_list(Nil{}, ps, e) : {T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), _) == Nil{} : List<&2, String>}
      {==}
    case T.Split{+path, +id} <> +rest:
      cons_paths(Arrange.rev.placed(refile, held, path, Arrange.lookup(ss, id)), Arrange.revs.placed(rest, refile, held, ss), ps, path, T.map(~T.Split, ~String, ~(s => first(s)), rest), e,
        x => h => rev_path(refile, held, path, Arrange.lookup(ss, id), x, h),
        xs => h => revs_paths(rest, refile, held, ss, xs, h))

def le_both(c: Bool, +a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Bool.pick(Nat, c, 1n+a, a), Bool.pick(Nat, c, 1n+b, b)) == True{} : Bool}:
  match c:
    case True{}:
      h
    case False{}:
      h

def le_right(c: Bool, +a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, Bool.pick(Nat, c, 1n+b, b)) == True{} : Bool}:
  match c:
    case True{}:
      ML.le_weak(a, b, h)
    case False{}:
      h

# A plan renames a path no more often than it places a file from there.
def renamed_le(ps: List<&2, Arrange.Placing>, +x: String) -> {Nat.is_le(times(T.map(~T.Split, ~String, ~(s => first(s)), Arrange.done.renamed(ps)), x), times(T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), ps), x)) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +rest:
      match p:
        case Arrange.Placing.Rename{+f, +t}:
          le_both(String.eq(f, x), times(T.map(~T.Split, ~String, ~(s => first(s)), Arrange.done.renamed(rest)), x), times(T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), rest), x), renamed_le(rest, x))
        case Arrange.Placing.Already{+f}:
          le_right(String.eq(f, x), times(T.map(~T.Split, ~String, ~(s => first(s)), Arrange.done.renamed(rest)), x), times(T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), rest), x), renamed_le(rest, x))
        case Arrange.Placing.Occupied{+f, +h}:
          le_right(String.eq(f, x), times(T.map(~T.Split, ~String, ~(s => first(s)), Arrange.done.renamed(rest)), x), times(T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), rest), x), renamed_le(rest, x))
        case Arrange.Placing.Unnamed{+f}:
          le_right(String.eq(f, x), times(T.map(~T.Split, ~String, ~(s => first(s)), Arrange.done.renamed(rest)), x), times(T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), rest), x), renamed_le(rest, x))

# Of one directory placed from where its walk found each file: a path is
# renamed from no more often than the walk found a file there.
def moved_once(+ps: List<&2, Arrange.Placing>, +ds: List<&2, T.Split>, +x: String, +e: {T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), ps) == T.map(~T.Split, ~String, ~(s => first(s)), ds) : List<&2, String>}) -> {Nat.is_le(times(T.map(~T.Split, ~String, ~(s => first(s)), Arrange.done.renamed(ps)), x), times(T.map(~T.Split, ~String, ~(s => first(s)), ds), x)) == True{} : Bool}:
  %e : {Nat.is_le(times(T.map(~T.Split, ~String, ~(s => first(s)), Arrange.done.renamed(ps)), x), times(_, x)) == True{} : Bool}
  renamed_le(ps, x)

def placed_once(+held: Set(), +revs: List<&2, T.Split>, +ops: List<&2, T.Split>, +names: List<&2, T.Split>, rp: Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>, +a: Arrange.Arrangement, +x: String, e: {Arrange.arrangement.placed(held, ops, names, rp) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}, hr: @xs: List<&2, Arrange.Placing> -> {rp == Done{xs} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>} -> {T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), xs) == T.map(~T.Split, ~String, ~(s => first(s)), revs) : List<&2, String>}) -> {Bool.and(Nat.is_le(times(T.map(~T.Split, ~String, ~(s => first(s)), Arrange.done.renamed(Arrange.arrangement.revs(a))), x), times(T.map(~T.Split, ~String, ~(s => first(s)), revs), x)), Nat.is_le(times(T.map(~T.Split, ~String, ~(s => first(s)), Arrange.done.renamed(Arrange.arrangement.ops(a))), x), times(T.map(~T.Split, ~String, ~(s => first(s)), ops), x))) == True{} : Bool}:
  match rp:
    case Fail{y}:
      Empty.absurd({Bool.and(Nat.is_le(times(T.map(~T.Split, ~String, ~(s => first(s)), Arrange.done.renamed(Arrange.arrangement.revs(a))), x), times(T.map(~T.Split, ~String, ~(s => first(s)), revs), x)), Nat.is_le(times(T.map(~T.Split, ~String, ~(s => first(s)), Arrange.done.renamed(Arrange.arrangement.ops(a))), x), times(T.map(~T.Split, ~String, ~(s => first(s)), ops), x))) == True{} : Bool}, B.fail_done(Arrange.Arrangement, y, a, e))
    case Done{+ps}:
      %done_plan(Arrange.Arrangement{ps, Arrange.ops.placed(ops, held, names)}, a, e) : {Bool.and(Nat.is_le(times(T.map(~T.Split, ~String, ~(s => first(s)), Arrange.done.renamed(Arrange.arrangement.revs(_))), x), times(T.map(~T.Split, ~String, ~(s => first(s)), revs), x)), Nat.is_le(times(T.map(~T.Split, ~String, ~(s => first(s)), Arrange.done.renamed(Arrange.arrangement.ops(_))), x), times(T.map(~T.Split, ~String, ~(s => first(s)), ops), x))) == True{} : Bool}
      B.and_tt(Nat.is_le(times(T.map(~T.Split, ~String, ~(s => first(s)), Arrange.done.renamed(ps)), x), times(T.map(~T.Split, ~String, ~(s => first(s)), revs), x)), Nat.is_le(times(T.map(~T.Split, ~String, ~(s => first(s)), Arrange.done.renamed(Arrange.ops.placed(ops, held, names))), x), times(T.map(~T.Split, ~String, ~(s => first(s)), ops), x)),
        moved_once(ps, revs, x, hr(ps, {==})), moved_once(Arrange.ops.placed(ops, held, names), ops, x, ops_paths(ops, held, names)))

def named_once(+refile: Bool, +held: Set(), +ss: List<&2, T.Split>, +revs: List<&2, T.Split>, +ops: List<&2, T.Split>, names: Result<&2, &2, Main.Refused, List<&2, T.Split>>, +a: Arrange.Arrangement, +x: String, e: {Arrange.arrangement.named(refile, held, ss, revs, ops, names) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}) -> {Bool.and(Nat.is_le(times(T.map(~T.Split, ~String, ~(s => first(s)), Arrange.done.renamed(Arrange.arrangement.revs(a))), x), times(T.map(~T.Split, ~String, ~(s => first(s)), revs), x)), Nat.is_le(times(T.map(~T.Split, ~String, ~(s => first(s)), Arrange.done.renamed(Arrange.arrangement.ops(a))), x), times(T.map(~T.Split, ~String, ~(s => first(s)), ops), x))) == True{} : Bool}:
  match names:
    case Fail{y}:
      Empty.absurd({Bool.and(Nat.is_le(times(T.map(~T.Split, ~String, ~(s => first(s)), Arrange.done.renamed(Arrange.arrangement.revs(a))), x), times(T.map(~T.Split, ~String, ~(s => first(s)), revs), x)), Nat.is_le(times(T.map(~T.Split, ~String, ~(s => first(s)), Arrange.done.renamed(Arrange.arrangement.ops(a))), x), times(T.map(~T.Split, ~String, ~(s => first(s)), ops), x))) == True{} : Bool}, B.fail_done(Arrange.Arrangement, y, a, e))
    case Done{+ns}:
      placed_once(held, revs, ops, ns, Arrange.revs.placed(revs, refile, held, ss), a, x, e, xs => h => revs_paths(revs, refile, held, ss, xs, h))

# `arrange` moves each file once: of each directory, a path is renamed from
# no more often than the walk found a file there.
def once(+refile: Bool, +fs: List<&2, Main.Full>, +revs: List<&2, T.Split>, +ops: List<&2, T.Split>, +ls: List<&2, String>, +a: Arrange.Arrangement, e: {Arrange.arrangement.r(refile, fs, revs, ops, ls) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}, +x: String) -> {Bool.and(Nat.is_le(times(T.map(~T.Split, ~String, ~(s => first(s)), Arrange.done.renamed(Arrange.arrangement.revs(a))), x), times(T.map(~T.Split, ~String, ~(s => first(s)), revs), x)), Nat.is_le(times(T.map(~T.Split, ~String, ~(s => first(s)), Arrange.done.renamed(Arrange.arrangement.ops(a))), x), times(T.map(~T.Split, ~String, ~(s => first(s)), ops), x))) == True{} : Bool}:
  named_once(refile, Arrange.taken(ls), Arrange.stems(Arrange.distinct(fs)), revs, ops, Arrange.operation_names(fs, Arrange.stems(Arrange.distinct(fs))), a, x, e)

# In the directory it sits in
# ---------------------------

# Whether a string holds a `/`.
def slashed(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, rest}:
      Bool.or(Char.is_eq(c, '/'), slashed(rest))

# The directory a path spells: everything up to and including its last
# `/`, and nothing where it has none.
def dir(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      Bool.pick(String, slashed(rest), SCon{c, dir(rest)}, Bool.pick(String, Char.is_eq(c, '/'), "/", SNil{}))

# Whether every rename of a list leaves its file in the directory it was in.
def stays(rs: List<&2, T.Split>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case T.Split{+f, +t} <> rest:
      Bool.and(String.eq(dir(t), dir(f)), stays(rest))

def has_slash_is(s: String) -> {Arrange.has_slash(s) == slashed(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      Equal.cong(Bool, Bool, z => Bool.or(Char.is_eq(c, '/'), z), Arrange.has_slash(rest), slashed(rest), has_slash_is(rest))

def flat_of(+s: String, -k: Bool, ek: {Arrange.has_slash(s) == k : Bool}) -> {slashed(s) == k : Bool}:
  Equal.trans(Bool, slashed(s), Arrange.has_slash(s), k, Equal.sym(Bool, Arrange.has_slash(s), slashed(s), has_slash_is(s)), ek)

# A path with no `/` is in no directory.
def dir_flat(s: String, +h: {slashed(s) == False{} : Bool}) -> {dir(s) == SNil{} : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      %Equal.sym(Bool, slashed(rest), False{}, or_ff_r(Char.is_eq(c, '/'), slashed(rest), h)) : {Bool.pick(String, _, SCon{c, dir(rest)}, Bool.pick(String, Char.is_eq(c, '/'), "/", SNil{})) == SNil{} : String}
      %Equal.sym(Bool, Char.is_eq(c, '/'), False{}, or_ff_l(Char.is_eq(c, '/'), slashed(rest), h)) : {Bool.pick(String, False{}, SCon{c, dir(rest)}, Bool.pick(String, _, "/", SNil{})) == SNil{} : String}
      {==}

def slashed_app(a: String, +b: String) -> {slashed(String.append(a, b)) == Bool.or(slashed(a), slashed(b)) : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      %Equal.sym(Bool, slashed(String.append(rest, b)), Bool.or(slashed(rest), slashed(b)), slashed_app(rest, b)) : {Bool.or(Char.is_eq(c, '/'), _) == Bool.or(slashed(SCon{c, rest}), slashed(b)) : Bool}
      or_assoc(Char.is_eq(c, '/'), slashed(rest), slashed(b))

def leaf_flat.of(k: Bool, q: Bool, +c: Char, +rest: String, ek: {Arrange.has_slash(rest) == k : Bool}, eq: {Char.is_eq(c, '/') == q : Bool}, ih: {slashed(Arrange.leaf(rest)) == False{} : Bool}) -> {slashed(Bool.pick(String, k, Arrange.leaf(rest), Bool.pick(String, q, rest, SCon{c, rest}))) == False{} : Bool}:
  match k:
    case True{}:
      ih
    case False{}:
      match q:
        case True{}:
          flat_of(rest, False{}, ek)
        case False{}:
          %Equal.sym(Bool, Char.is_eq(c, '/'), False{}, eq) : {Bool.or(_, slashed(rest)) == False{} : Bool}
          flat_of(rest, False{}, ek)

# The filename half of a stem has no `/` in it.
def leaf_flat(s: String) -> {slashed(Arrange.leaf(s)) == False{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      leaf_flat.of(Arrange.has_slash(rest), Char.is_eq(c, '/'), c, rest, {==}, {==}, leaf_flat(rest))

# Nor has the name a revision document is given where it sits.
def name_flat(+s: String) -> {slashed(String.append(Arrange.leaf(s), ".rev.txt")) == False{} : Bool}:
  %Equal.sym(Bool, slashed(String.append(Arrange.leaf(s), ".rev.txt")), Bool.or(slashed(Arrange.leaf(s)), slashed(".rev.txt")), slashed_app(Arrange.leaf(s), ".rev.txt")) : {_ == False{} : Bool}
  %Equal.sym(Bool, slashed(Arrange.leaf(s)), False{}, leaf_flat(s)) : {Bool.or(_, slashed(".rev.txt")) == False{} : Bool}
  {==}

def beside_slashed.of(k: Bool, +c: Char, +rest: String, +n: String, ek: {Arrange.has_slash(SCon{c, rest}) == k : Bool}, hn: {slashed(n) == False{} : Bool}, ih: {slashed(Arrange.beside(rest, n)) == slashed(rest) : Bool}) -> {slashed(Bool.pick(String, k, SCon{c, Arrange.beside(rest, n)}, n)) == slashed(SCon{c, rest}) : Bool}:
  match k:
    case True{}:
      Equal.cong(Bool, Bool, z => Bool.or(Char.is_eq(c, '/'), z), slashed(Arrange.beside(rest, n)), slashed(rest), ih)
    case False{}:
      Equal.trans(Bool, slashed(n), False{}, slashed(SCon{c, rest}), hn, Equal.sym(Bool, slashed(SCon{c, rest}), False{}, flat_of(SCon{c, rest}, False{}, ek)))

# A name with no `/` put in place of a path's last one leaves the path with
# a `/` exactly where it had one.
def beside_slashed(p: String, +n: String, +hn: {slashed(n) == False{} : Bool}) -> {slashed(Arrange.beside(p, n)) == slashed(p) : Bool}:
  match p:
    case SNil{}:
      hn
    case SCon{+c, +rest}:
      beside_slashed.of(Arrange.has_slash(SCon{c, rest}), c, rest, n, {==}, hn, beside_slashed(rest, n, hn))

def dir_beside.of(k: Bool, +c: Char, +rest: String, +n: String, ek: {Arrange.has_slash(SCon{c, rest}) == k : Bool}, +hn: {slashed(n) == False{} : Bool}, ih: {dir(Arrange.beside(rest, n)) == dir(rest) : String}) -> {dir(Bool.pick(String, k, SCon{c, Arrange.beside(rest, n)}, n)) == dir(SCon{c, rest}) : String}:
  match k:
    case True{}:
      %Equal.sym(Bool, slashed(Arrange.beside(rest, n)), slashed(rest), beside_slashed(rest, n, hn)) : {Bool.pick(String, _, SCon{c, dir(Arrange.beside(rest, n))}, Bool.pick(String, Char.is_eq(c, '/'), "/", SNil{})) == dir(SCon{c, rest}) : String}
      %Equal.sym(String, dir(Arrange.beside(rest, n)), dir(rest), ih) : {Bool.pick(String, slashed(rest), SCon{c, _}, Bool.pick(String, Char.is_eq(c, '/'), "/", SNil{})) == dir(SCon{c, rest}) : String}
      {==}
    case False{}:
      Equal.trans(String, dir(n), SNil{}, dir(SCon{c, rest}), dir_flat(n, hn), Equal.sym(String, dir(SCon{c, rest}), SNil{}, dir_flat(SCon{c, rest}, flat_of(SCon{c, rest}, False{}, ek))))

# A path renamed where it sits, to a name with no `/`, is in the directory
# it was in.
def dir_beside(p: String, +n: String, +hn: {slashed(n) == False{} : Bool}) -> {dir(Arrange.beside(p, n)) == dir(p) : String}:
  match p:
    case SNil{}:
      dir_flat(n, hn)
    case SCon{+c, +rest}:
      dir_beside.of(Arrange.has_slash(SCon{c, rest}), c, rest, n, {==}, hn, dir_beside(rest, n, hn))

# Whether a placing, where it is a rename, keeps its file's directory.
def kept_in(p: Arrange.Placing) -> Bool:
  match p:
    case Arrange.Placing.Rename{+f, +t}:
      String.eq(dir(t), dir(f))
    case _:
      True{}

def all_kept(ps: List<&2, Arrange.Placing>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case +p <> rest:
      Bool.and(kept_in(p), all_kept(rest))

def place_kept(+held: Set(), +path: String, +target: String, c: Bool, h: {String.eq(dir(target), dir(path)) == True{} : Bool}) -> {kept_in(Bool.pick(Arrange.Placing, c, Arrange.Placing.Occupied{path, target}, Arrange.Placing.Rename{path, target})) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      h

def place_here(+held: Set(), +path: String, +target: String, c: Bool, h: {String.eq(dir(target), dir(path)) == True{} : Bool}) -> {kept_in(Bool.pick(Arrange.Placing, c, Arrange.Placing.Already{path}, Bool.pick(Arrange.Placing, Arrange.has(held, target), Arrange.Placing.Occupied{path, target}, Arrange.Placing.Rename{path, target}))) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      place_kept(held, path, target, Arrange.has(held, target), h)

# A revision kept where it sits is renamed, if at all, to a path in the
# directory it is in.
def kept_here(+held: Set(), +path: String, +stem: String) -> {kept_in(Arrange.place(held, path, Arrange.rev.target(False{}, path, stem))) == True{} : Bool}:
  place_here(held, path, Arrange.rev.target(False{}, path, stem), String.eq(path, Arrange.rev.target(False{}, path, stem)),
    %Equal.sym(String, dir(Arrange.beside(path, String.append(Arrange.leaf(stem), ".rev.txt"))), dir(path), dir_beside(path, String.append(Arrange.leaf(stem), ".rev.txt"), name_flat(stem))) : {String.eq(_, dir(path)) == True{} : Bool}
    S.eq_refl(dir(path)))

def rev_kept(+held: Set(), +path: String, stem: Maybe<&2, String>, +x: Arrange.Placing, e: {Arrange.rev.placed(False{}, held, path, stem) == Done{x} : Result<&2, &2, Main.Refused, Arrange.Placing>}) -> {kept_in(x) == True{} : Bool}:
  match stem:
    case None{}:
      Empty.absurd({kept_in(x) == True{} : Bool}, B.fail_done(Arrange.Placing, Main.Refused{1, path ++ " changed while it was being arranged"}, x, e))
    case Some{+s}:
      %done_placing(Arrange.place(held, path, Arrange.rev.target(False{}, path, s)), x, e) : {kept_in(_) == True{} : Bool}
      kept_here(held, path, s)

def cons_kept(p: Result<&2, &2, Main.Refused, Arrange.Placing>, r: Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>, +ps: List<&2, Arrange.Placing>, e: {Arrange.placed.cons(p, r) == Done{ps} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>}, hp: @x: Arrange.Placing -> {p == Done{x} : Result<&2, &2, Main.Refused, Arrange.Placing>} -> {kept_in(x) == True{} : Bool}, hr: @xs: List<&2, Arrange.Placing> -> {r == Done{xs} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>} -> {all_kept(xs) == True{} : Bool}) -> {all_kept(ps) == True{} : Bool}:
  match p r:
    case Fail{x} _:
      Empty.absurd({all_kept(ps) == True{} : Bool}, B.fail_done(List<&2, Arrange.Placing>, x, ps, e))
    case Done{x} Fail{y}:
      Empty.absurd({all_kept(ps) == True{} : Bool}, B.fail_done(List<&2, Arrange.Placing>, y, ps, e))
    case Done{+x} Done{+xs}:
      %done_list(x <> xs, ps, e) : {all_kept(_) == True{} : Bool}
      B.and_tt(kept_in(x), all_kept(xs), hp(x, {==}), hr(xs, {==}))

def revs_kept(ds: List<&2, T.Split>, +held: Set(), +ss: List<&2, T.Split>, +ps: List<&2, Arrange.Placing>, e: {Arrange.revs.placed(ds, False{}, held, ss) == Done{ps} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>}) -> {all_kept(ps) == True{} : Bool}:
  match ds:
    case Nil{}:
      %done_list(Nil{}, ps, e) : {all_kept(_) == True{} : Bool}
      {==}
    case T.Split{+path, +id} <> +rest:
      cons_kept(Arrange.rev.placed(False{}, held, path, Arrange.lookup(ss, id)), Arrange.revs.placed(rest, False{}, held, ss), ps, e,
        x => h => rev_kept(held, path, Arrange.lookup(ss, id), x, h),
        xs => h => revs_kept(rest, held, ss, xs, h))

# What a plan's renames are, of placings that each keep their directory.
def stays_kept(ps: List<&2, Arrange.Placing>, +h: {all_kept(ps) == True{} : Bool}) -> {stays(Arrange.done.renamed(ps)) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +rest:
      match p:
        case Arrange.Placing.Rename{+f, +t}:
          B.and_tt(String.eq(dir(t), dir(f)), stays(Arrange.done.renamed(rest)), and_tl(String.eq(dir(t), dir(f)), all_kept(rest), h), stays_kept(rest, and_tr(String.eq(dir(t), dir(f)), all_kept(rest), h)))
        case Arrange.Placing.Already{+f}:
          stays_kept(rest, h)
        case Arrange.Placing.Occupied{+f, +o}:
          stays_kept(rest, h)
        case Arrange.Placing.Unnamed{+f}:
          stays_kept(rest, h)

def placed_kept(+held: Set(), +ops: List<&2, T.Split>, +names: List<&2, T.Split>, rp: Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>, +a: Arrange.Arrangement, e: {Arrange.arrangement.placed(held, ops, names, rp) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}, hr: @xs: List<&2, Arrange.Placing> -> {rp == Done{xs} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>} -> {all_kept(xs) == True{} : Bool}) -> {stays(Arrange.done.renamed(Arrange.arrangement.revs(a))) == True{} : Bool}:
  match rp:
    case Fail{x}:
      Empty.absurd({stays(Arrange.done.renamed(Arrange.arrangement.revs(a))) == True{} : Bool}, B.fail_done(Arrange.Arrangement, x, a, e))
    case Done{+ps}:
      %done_plan(Arrange.Arrangement{ps, Arrange.ops.placed(ops, held, names)}, a, e) : {stays(Arrange.done.renamed(Arrange.arrangement.revs(_))) == True{} : Bool}
      stays_kept(ps, hr(ps, {==}))

def named_kept(+held: Set(), +ss: List<&2, T.Split>, +revs: List<&2, T.Split>, +ops: List<&2, T.Split>, names: Result<&2, &2, Main.Refused, List<&2, T.Split>>, +a: Arrange.Arrangement, e: {Arrange.arrangement.named(False{}, held, ss, revs, ops, names) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}) -> {stays(Arrange.done.renamed(Arrange.arrangement.revs(a))) == True{} : Bool}:
  match names:
    case Fail{x}:
      Empty.absurd({stays(Arrange.done.renamed(Arrange.arrangement.revs(a))) == True{} : Bool}, B.fail_done(Arrange.Arrangement, x, a, e))
    case Done{+ns}:
      placed_kept(held, ops, ns, Arrange.revs.placed(revs, False{}, held, ss), a, e, xs => h => revs_kept(revs, held, ss, xs, h))

# Without `--refile`, every revision `arrange` renames is renamed into the
# directory it was in: the path up to its last `/` is the same after.
def kept(+fs: List<&2, Main.Full>, +revs: List<&2, T.Split>, +ops: List<&2, T.Split>, +ls: List<&2, String>, +a: Arrange.Arrangement, e: {Arrange.arrangement.r(False{}, fs, revs, ops, ls) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}) -> {stays(Arrange.done.renamed(Arrange.arrangement.revs(a))) == True{} : Bool}:
  named_kept(Arrange.taken(ls), Arrange.stems(Arrange.distinct(fs)), revs, ops, Arrange.operation_names(fs, Arrange.stems(Arrange.distinct(fs))), a, e)

# Counting what the report says
# -----------------------------

def ndisc(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

def zero_succ(-n: Nat, e: {0n == 1n+n : Nat}) -> Empty:
  %e : {ndisc(_) : Type}
  Unit{}

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def succ_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, n => pred(n), 1n+a, 1n+b, e)

def app_one(xs: List<&2, T.Split>, +x: T.Split) -> {List.length(&2, T.Split, List.append(&2, T.Split, xs, [x])) == 1n+List.length(&2, T.Split, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +rest:
      succ_eq(List.length(&2, T.Split, List.append(&2, T.Split, rest, [x])), 1n+List.length(&2, T.Split, rest), app_one(rest, x))

# A rename, done or left, is counted once in its directory's report.
def push_tally(o: Bool, +f: String, +t: String, d: Arrange.Came) -> {tally(Arrange.act.push(o, f, t, d)) == 1n+tally(d) : Nat}:
  match o d:
    case True{} Arrange.Came{+rs, +a, +os, +u}:
      %Equal.sym(Nat, List.length(&2, T.Split, List.append(&2, T.Split, rs, [T.Split{f, t}])), 1n+List.length(&2, T.Split, rs), app_one(rs, T.Split{f, t})) : {Nat.add(_, Nat.add(a, Nat.add(List.length(&2, T.Split, os), u))) == 1n+tally(Arrange.Came{rs, a, os, u}) : Nat}
      {==}
    case False{} Arrange.Came{+rs, +a, +os, +u}:
      %Equal.sym(Nat, List.length(&2, T.Split, List.append(&2, T.Split, os, [T.Split{f, t}])), 1n+List.length(&2, T.Split, os), app_one(os, T.Split{f, t})) : {Nat.add(List.length(&2, T.Split, rs), Nat.add(a, Nat.add(_, u))) == 1n+tally(Arrange.Came{rs, a, os, u}) : Nat}
      %succ_out(a, Nat.add(List.length(&2, T.Split, os), u)) : {Nat.add(List.length(&2, T.Split, rs), _) == 1n+tally(Arrange.Came{rs, a, os, u}) : Nat}
      %succ_out(List.length(&2, T.Split, rs), Nat.add(a, Nat.add(List.length(&2, T.Split, os), u))) : {_ == 1n+tally(Arrange.Came{rs, a, os, u}) : Nat}
      {==}

# Renames carried out, each with what it came to, add one each to the count.
def came_tally(rs: List<&2, T.Split>, outs: List<&2, Bool>, +d: Arrange.Came, h: {List.length(&2, Bool, outs) == List.length(&2, T.Split, rs) : Nat}) -> {tally(Arrange.came(rs, outs, d)) == Nat.add(List.length(&2, T.Split, rs), tally(d)) : Nat}:
  match rs outs:
    case Nil{} Nil{}:
      {==}
    case Nil{} +o <> +more:
      {==}
    case T.Split{+f, +t} <> +rest Nil{}:
      Empty.absurd({tally(d) == 1n+Nat.add(List.length(&2, T.Split, rest), tally(d)) : Nat}, zero_succ(List.length(&2, T.Split, rest), h))
    case T.Split{+f, +t} <> +rest +o <> +more:
      Equal.trans(Nat, tally(Arrange.came(rest, more, Arrange.act.push(o, f, t, d))), Nat.add(List.length(&2, T.Split, rest), tally(Arrange.act.push(o, f, t, d))), 1n+Nat.add(List.length(&2, T.Split, rest), tally(d)),
        came_tally(rest, more, Arrange.act.push(o, f, t, d), succ_inj(List.length(&2, Bool, more), List.length(&2, T.Split, rest), h)),
        Equal.trans(Nat, Nat.add(List.length(&2, T.Split, rest), tally(Arrange.act.push(o, f, t, d))), Nat.add(List.length(&2, T.Split, rest), 1n+tally(d)), 1n+Nat.add(List.length(&2, T.Split, rest), tally(d)),
          Equal.cong(Nat, Nat, z => Nat.add(List.length(&2, T.Split, rest), z), tally(Arrange.act.push(o, f, t, d)), 1n+tally(d), push_tally(o, f, t, d)),
          Pos.add_succ(List.length(&2, T.Split, rest), tally(d))))

# The real run's report counts what the dry run's does, whatever each
# rename comes to.
def came_planned(+ps: List<&2, Arrange.Placing>, outs: List<&2, Bool>, h: {List.length(&2, Bool, outs) == List.length(&2, T.Split, Arrange.done.renamed(ps)) : Nat}) -> {tally(Arrange.act.came(ps, outs)) == tally(Arrange.planned(ps)) : Nat}:
  came_tally(Arrange.done.renamed(ps), outs, Arrange.act.start(ps), h)

# Of one directory placed file by file from its walk: each file is placed
# from where the walk found it, and both reports count the walk's files.
def dir_counts(+ps: List<&2, Arrange.Placing>, +ds: List<&2, T.Split>, +outs: List<&2, Bool>, ep: {T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), ps) == T.map(~T.Split, ~String, ~(s => first(s)), ds) : List<&2, String>}, +el: {List.length(&2, Arrange.Placing, ps) == List.length(&2, T.Split, ds) : Nat}, ho: {List.length(&2, Bool, outs) == List.length(&2, T.Split, Arrange.done.renamed(ps)) : Nat}) -> {(T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), ps), (tally(Arrange.planned(ps)), tally(Arrange.act.came(ps, outs)))) == (T.map(~T.Split, ~String, ~(s => first(s)), ds), (List.length(&2, T.Split, ds), List.length(&2, T.Split, ds))) : (List<&2, String> & (Nat & Nat))}:
  %Equal.sym(List<&2, String>, T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), ps), T.map(~T.Split, ~String, ~(s => first(s)), ds), ep) : {(_, (tally(Arrange.planned(ps)), tally(Arrange.act.came(ps, outs)))) == (T.map(~T.Split, ~String, ~(s => first(s)), ds), (List.length(&2, T.Split, ds), List.length(&2, T.Split, ds))) : (List<&2, String> & (Nat & Nat))}
  %Equal.sym(Nat, tally(Arrange.planned(ps)), List.length(&2, T.Split, ds), Equal.trans(Nat, tally(Arrange.planned(ps)), List.length(&2, Arrange.Placing, ps), List.length(&2, T.Split, ds), tally_planned(ps), el)) : {(T.map(~T.Split, ~String, ~(s => first(s)), ds), (_, tally(Arrange.act.came(ps, outs)))) == (T.map(~T.Split, ~String, ~(s => first(s)), ds), (List.length(&2, T.Split, ds), List.length(&2, T.Split, ds))) : (List<&2, String> & (Nat & Nat))}
  %Equal.sym(Nat, tally(Arrange.act.came(ps, outs)), List.length(&2, T.Split, ds), Equal.trans(Nat, tally(Arrange.act.came(ps, outs)), tally(Arrange.planned(ps)), List.length(&2, T.Split, ds), came_planned(ps, outs, ho), Equal.trans(Nat, tally(Arrange.planned(ps)), List.length(&2, Arrange.Placing, ps), List.length(&2, T.Split, ds), tally_planned(ps), el))) : {(T.map(~T.Split, ~String, ~(s => first(s)), ds), (List.length(&2, T.Split, ds), _)) == (T.map(~T.Split, ~String, ~(s => first(s)), ds), (List.length(&2, T.Split, ds), List.length(&2, T.Split, ds))) : (List<&2, String> & (Nat & Nat))}
  {==}

def pair_eq(-x: List<&2, String> & (Nat & Nat), -y: List<&2, String> & (Nat & Nat), -u: List<&2, String> & (Nat & Nat), -v: List<&2, String> & (Nat & Nat), ex: {x == u : List<&2, String> & (Nat & Nat)}, ey: {y == v : List<&2, String> & (Nat & Nat)}) -> {(x, y) == (u, v) : (List<&2, String> & (Nat & Nat)) & (List<&2, String> & (Nat & Nat))}:
  %Equal.sym(List<&2, String> & (Nat & Nat), x, u, ex) : {(_, y) == (u, v) : (List<&2, String> & (Nat & Nat)) & (List<&2, String> & (Nat & Nat))}
  %Equal.sym(List<&2, String> & (Nat & Nat), y, v, ey) : {(u, _) == (u, v) : (List<&2, String> & (Nat & Nat)) & (List<&2, String> & (Nat & Nat))}
  {==}

# What `arrange` says it did with each directory, as the law states it.
def Counted(a: Arrange.Arrangement, revs: List<&2, T.Split>, ops: List<&2, T.Split>) -> Type:
  @ro: List<&2, Bool> -> @oo: List<&2, Bool> -> {List.length(&2, Bool, ro) == List.length(&2, T.Split, Arrange.done.renamed(Arrange.arrangement.revs(a))) : Nat} -> {List.length(&2, Bool, oo) == List.length(&2, T.Split, Arrange.done.renamed(Arrange.arrangement.ops(a))) : Nat} -> {((T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), Arrange.arrangement.revs(a)), (tally(Arrange.planned(Arrange.arrangement.revs(a))), tally(Arrange.act.came(Arrange.arrangement.revs(a), ro)))), (T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), Arrange.arrangement.ops(a)), (tally(Arrange.planned(Arrange.arrangement.ops(a))), tally(Arrange.act.came(Arrange.arrangement.ops(a), oo))))) == ((T.map(~T.Split, ~String, ~(s => first(s)), revs), (List.length(&2, T.Split, revs), List.length(&2, T.Split, revs))), (T.map(~T.Split, ~String, ~(s => first(s)), ops), (List.length(&2, T.Split, ops), List.length(&2, T.Split, ops)))) : (List<&2, String> & (Nat & Nat)) & (List<&2, String> & (Nat & Nat))}

def placed_counts(+held: Set(), +revs: List<&2, T.Split>, +ops: List<&2, T.Split>, +names: List<&2, T.Split>, rp: Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>, +a: Arrange.Arrangement, e: {Arrange.arrangement.placed(held, ops, names, rp) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}, hp: @xs: List<&2, Arrange.Placing> -> {rp == Done{xs} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>} -> {T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), xs) == T.map(~T.Split, ~String, ~(s => first(s)), revs) : List<&2, String>}, hl: @xs: List<&2, Arrange.Placing> -> {rp == Done{xs} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>} -> {List.length(&2, Arrange.Placing, xs) == List.length(&2, T.Split, revs) : Nat}) -> Counted(a, revs, ops):
  match rp:
    case Fail{x}:
      Empty.absurd(Counted(a, revs, ops), B.fail_done(Arrange.Arrangement, x, a, e))
    case Done{+ps}:
      %done_plan(Arrange.Arrangement{ps, Arrange.ops.placed(ops, held, names)}, a, e) : Counted(_, revs, ops)
      +ro => +oo => h1 => h2 => pair_eq((T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), ps), (tally(Arrange.planned(ps)), tally(Arrange.act.came(ps, ro)))), (T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), Arrange.ops.placed(ops, held, names)), (tally(Arrange.planned(Arrange.ops.placed(ops, held, names))), tally(Arrange.act.came(Arrange.ops.placed(ops, held, names), oo)))), (T.map(~T.Split, ~String, ~(s => first(s)), revs), (List.length(&2, T.Split, revs), List.length(&2, T.Split, revs))), (T.map(~T.Split, ~String, ~(s => first(s)), ops), (List.length(&2, T.Split, ops), List.length(&2, T.Split, ops))),
        dir_counts(ps, revs, ro, hp(ps, {==}), hl(ps, {==}), h1),
        dir_counts(Arrange.ops.placed(ops, held, names), ops, oo, ops_paths(ops, held, names), ops_length(ops, held, names), h2))

def named_counts(+refile: Bool, +held: Set(), +ss: List<&2, T.Split>, +revs: List<&2, T.Split>, +ops: List<&2, T.Split>, names: Result<&2, &2, Main.Refused, List<&2, T.Split>>, +a: Arrange.Arrangement, e: {Arrange.arrangement.named(refile, held, ss, revs, ops, names) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}) -> Counted(a, revs, ops):
  match names:
    case Fail{x}:
      Empty.absurd(Counted(a, revs, ops), B.fail_done(Arrange.Arrangement, x, a, e))
    case Done{+ns}:
      placed_counts(held, revs, ops, ns, Arrange.revs.placed(revs, refile, held, ss), a, e, xs => h => revs_paths(revs, refile, held, ss, xs, h), xs => h => revs_length(revs, refile, held, ss, xs, h))

# Every file `arrange` walks is placed once, from where the walk found it,
# and each directory's report, in a dry run and in the real run whatever
# each rename comes to, counts as many files as the walk found there.
def counts(+refile: Bool, +fs: List<&2, Main.Full>, +revs: List<&2, T.Split>, +ops: List<&2, T.Split>, +ls: List<&2, String>, +a: Arrange.Arrangement, e: {Arrange.arrangement.r(refile, fs, revs, ops, ls) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}, +ro: List<&2, Bool>, +oo: List<&2, Bool>, h1: {List.length(&2, Bool, ro) == List.length(&2, T.Split, Arrange.done.renamed(Arrange.arrangement.revs(a))) : Nat}, h2: {List.length(&2, Bool, oo) == List.length(&2, T.Split, Arrange.done.renamed(Arrange.arrangement.ops(a))) : Nat}) -> {((T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), Arrange.arrangement.revs(a)), (tally(Arrange.planned(Arrange.arrangement.revs(a))), tally(Arrange.act.came(Arrange.arrangement.revs(a), ro)))), (T.map(~Arrange.Placing, ~String, ~(q => placing.path(q)), Arrange.arrangement.ops(a)), (tally(Arrange.planned(Arrange.arrangement.ops(a))), tally(Arrange.act.came(Arrange.arrangement.ops(a), oo))))) == ((T.map(~T.Split, ~String, ~(s => first(s)), revs), (List.length(&2, T.Split, revs), List.length(&2, T.Split, revs))), (T.map(~T.Split, ~String, ~(s => first(s)), ops), (List.length(&2, T.Split, ops), List.length(&2, T.Split, ops)))) : (List<&2, String> & (Nat & Nat)) & (List<&2, String> & (Nat & Nat))}:
  named_counts(refile, Arrange.taken(ls), Arrange.stems(Arrange.distinct(fs)), revs, ops, Arrange.operation_names(fs, Arrange.stems(Arrange.distinct(fs))), a, e)(ro, oo, h1, h2)
