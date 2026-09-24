# What `arrange` plans. It takes nothing but its flags; every rename it
# plans goes to a path nothing in the store was at, from a different one;
# and without `--refile`, a revision document is renamed only within the
# directory it sits in.
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

# The words
# ---------

# A command line with no word but a flag is one whose every word is a flag.
def other_step(c: Bool, +w: String, +rest: List<&2, String>, e: {Bool.pick(Maybe<&2, String>, c, Arrange.first_other(rest), Some{w}) == None{} : Maybe<&2, String>}, ih: {Arrange.first_other(rest) == None{} : Maybe<&2, String>} -> {Arrange.all_flags(rest) == True{} : Bool}) -> {Bool.and(c, Arrange.all_flags(rest)) == True{} : Bool}:
  match c:
    case True{}:
      ih(e)
    case False{}:
      Empty.absurd({Bool.and(False{}, Arrange.all_flags(rest)) == True{} : Bool}, NameL.some_none(w, e))

def no_other(ws: List<&2, String>, e: {Arrange.first_other(ws) == None{} : Maybe<&2, String>}) -> {Arrange.all_flags(ws) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case +w <> +rest:
      other_step(Arrange.is_flag(w), w, rest, e, h => no_other(rest, h))

def of_none(+dry: Bool, +refile: Bool, extra: Maybe<&2, String>, -c: Arrange.ArrangeCmd, e: {Arrange.args.of(dry, refile, extra) == Done{c} : Result<&2, &2, Main.Refused, Arrange.ArrangeCmd>}) -> {extra == None{} : Maybe<&2, String>}:
  match extra:
    case Some{x}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, String>}, B.fail_done(Arrange.ArrangeCmd, Main.Refused{2, "`arrange` takes no arguments, and `" ++ x ++ "` is one"}, c, e))
    case None{}:
      {==}

# `arrange` accepts a command line only where every word is one of its flags.
def args_flags(+ws: List<&2, String>, -c: Arrange.ArrangeCmd, e: {Arrange.args.r(ws) == Done{c} : Result<&2, &2, Main.Refused, Arrange.ArrangeCmd>}) -> {Arrange.all_flags(ws) == True{} : Bool}:
  no_other(ws, of_none(Arrange.any_dry(ws), Arrange.any_refile(ws), Arrange.first_other(ws), c, e))

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

# In place
# --------

def place_kept(+held: Set(), +path: String, +target: String, c: Bool, h: {String.starts_with(target, Naming.head(path)) == True{} : Bool}) -> {Arrange.in_place(Bool.pick(Arrange.Placing, c, Arrange.Placing.Occupied{path, target}, Arrange.Placing.Rename{path, target})) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      h

def place_here(+held: Set(), +path: String, +target: String, c: Bool, h: {String.starts_with(target, Naming.head(path)) == True{} : Bool}) -> {Arrange.in_place(Bool.pick(Arrange.Placing, c, Arrange.Placing.Already{path}, Bool.pick(Arrange.Placing, Arrange.has(held, target), Arrange.Placing.Occupied{path, target}, Arrange.Placing.Rename{path, target}))) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      place_kept(held, path, target, Arrange.has(held, target), h)

# A revision kept where it sits is renamed, if at all, to its stem's
# filename in the directory it is in.
def kept_here(+held: Set(), +path: String, +stem: String) -> {Arrange.in_place(Arrange.place(held, path, Arrange.rev.target(False{}, path, stem))) == True{} : Bool}:
  place_here(held, path, Arrange.rev.target(False{}, path, stem), String.eq(path, Arrange.rev.target(False{}, path, stem)),
    B.sw_ext(Naming.head(path), Naming.head(path), Arrange.leaf(stem) ++ ".rev.txt", B.sw_refl(Naming.head(path))))

def rev_kept(+held: Set(), +path: String, stem: Maybe<&2, String>, +x: Arrange.Placing, e: {Arrange.rev.placed(False{}, held, path, stem) == Done{x} : Result<&2, &2, Main.Refused, Arrange.Placing>}) -> {Arrange.in_place(x) == True{} : Bool}:
  match stem:
    case None{}:
      Empty.absurd({Arrange.in_place(x) == True{} : Bool}, B.fail_done(Arrange.Placing, Main.Refused{1, path ++ " changed while it was being arranged"}, x, e))
    case Some{+s}:
      %done_placing(Arrange.place(held, path, Arrange.rev.target(False{}, path, s)), x, e) : {Arrange.in_place(_) == True{} : Bool}
      kept_here(held, path, s)

def cons_kept(p: Result<&2, &2, Main.Refused, Arrange.Placing>, r: Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>, +ps: List<&2, Arrange.Placing>, e: {Arrange.placed.cons(p, r) == Done{ps} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>}, hp: @x: Arrange.Placing -> {p == Done{x} : Result<&2, &2, Main.Refused, Arrange.Placing>} -> {Arrange.in_place(x) == True{} : Bool}, hr: @xs: List<&2, Arrange.Placing> -> {r == Done{xs} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>} -> {Arrange.all_in_place(xs) == True{} : Bool}) -> {Arrange.all_in_place(ps) == True{} : Bool}:
  match p r:
    case Fail{x} _:
      Empty.absurd({Arrange.all_in_place(ps) == True{} : Bool}, B.fail_done(List<&2, Arrange.Placing>, x, ps, e))
    case Done{x} Fail{y}:
      Empty.absurd({Arrange.all_in_place(ps) == True{} : Bool}, B.fail_done(List<&2, Arrange.Placing>, y, ps, e))
    case Done{+x} Done{+xs}:
      %done_list(x <> xs, ps, e) : {Arrange.all_in_place(_) == True{} : Bool}
      B.and_tt(Arrange.in_place(x), Arrange.all_in_place(xs), hp(x, {==}), hr(xs, {==}))

def revs_kept(ds: List<&2, T.Split>, +held: Set(), +ss: List<&2, T.Split>, +ps: List<&2, Arrange.Placing>, e: {Arrange.revs.placed(ds, False{}, held, ss) == Done{ps} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>}) -> {Arrange.all_in_place(ps) == True{} : Bool}:
  match ds:
    case Nil{}:
      %done_list(Nil{}, ps, e) : {Arrange.all_in_place(_) == True{} : Bool}
      {==}
    case T.Split{+path, +id} <> +rest:
      cons_kept(Arrange.rev.placed(False{}, held, path, Arrange.lookup(ss, id)), Arrange.revs.placed(rest, False{}, held, ss), ps, e,
        x => h => rev_kept(held, path, Arrange.lookup(ss, id), x, h),
        xs => h => revs_kept(rest, held, ss, xs, h))

def placed_kept(+held: Set(), +ops: List<&2, T.Split>, +names: List<&2, T.Split>, rp: Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>, +a: Arrange.Arrangement, e: {Arrange.arrangement.placed(held, ops, names, rp) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}, hr: @xs: List<&2, Arrange.Placing> -> {rp == Done{xs} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>} -> {Arrange.all_in_place(xs) == True{} : Bool}) -> {Arrange.all_in_place(Arrange.arrangement.revs(a)) == True{} : Bool}:
  match rp:
    case Fail{x}:
      Empty.absurd({Arrange.all_in_place(Arrange.arrangement.revs(a)) == True{} : Bool}, B.fail_done(Arrange.Arrangement, x, a, e))
    case Done{+ps}:
      %done_plan(Arrange.Arrangement{ps, Arrange.ops.placed(ops, held, names)}, a, e) : {Arrange.all_in_place(Arrange.arrangement.revs(_)) == True{} : Bool}
      hr(ps, {==})

def named_kept(+held: Set(), +ss: List<&2, T.Split>, +revs: List<&2, T.Split>, +ops: List<&2, T.Split>, names: Result<&2, &2, Main.Refused, List<&2, T.Split>>, +a: Arrange.Arrangement, e: {Arrange.arrangement.named(False{}, held, ss, revs, ops, names) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}) -> {Arrange.all_in_place(Arrange.arrangement.revs(a)) == True{} : Bool}:
  match names:
    case Fail{x}:
      Empty.absurd({Arrange.all_in_place(Arrange.arrangement.revs(a)) == True{} : Bool}, B.fail_done(Arrange.Arrangement, x, a, e))
    case Done{+ns}:
      placed_kept(held, ops, ns, Arrange.revs.placed(revs, False{}, held, ss), a, e, xs => h => revs_kept(revs, held, ss, xs, h))

# Without `--refile`, every revision `arrange` renames stays in its folder.
def kept(+fs: List<&2, Main.Full>, +revs: List<&2, T.Split>, +ops: List<&2, T.Split>, +ls: List<&2, String>, +a: Arrange.Arrangement, e: {Arrange.arrangement.r(False{}, fs, revs, ops, ls) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}) -> {Arrange.all_in_place(Arrange.arrangement.revs(a)) == True{} : Bool}:
  named_kept(Arrange.taken(ls), Arrange.stems(Arrange.distinct(fs)), revs, ops, Arrange.operation_names(fs, Arrange.stems(Arrange.distinct(fs))), a, e)

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

def fault_parses(+path: String, r: Result<&2, &2, String, Rev.Rev>, e: {Arrange.parse_fault(path, r) == None{} : Maybe<&2, Main.Refused>}) -> {Bool.not(Main.rev.fails(r)) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Bool.not(Main.rev.fails(Fail{x})) == True{} : Bool}, some_none_r(Main.Refused{1, path ++ ": " ++ x}, e))
    case Done{x}:
      {==}

def faults_none(ds: List<&2, Store.Doc>, +e: {Arrange.first_fault(ds) == None{} : Maybe<&2, Main.Refused>}) -> {Arrange.all_parse(ds) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Store.Doc{+path, +id, +size, +text} <> +rest:
      B.and_tt(Bool.not(Main.rev.fails(Rev.parse(text))), Arrange.all_parse(rest),
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

# Counting
# --------

def succ_eq(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  Equal.cong(Nat, Nat, n => 1n+n, a, b, e)

def succ_out(x: Nat, -y: Nat) -> {1n+Nat.add(x, y) == Nat.add(x, 1n+y) : Nat}:
  Equal.sym(Nat, Nat.add(x, 1n+y), 1n+Nat.add(x, y), Pos.add_succ(x, y))

# The four counts a report prints for a plan add up to its files.
def tally_planned(ps: List<&2, Arrange.Placing>) -> {Arrange.tally(Arrange.planned(ps)) == List.length(&2, Arrange.Placing, ps) : Nat}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +rest:
      match p:
        case Arrange.Placing.Rename{+f, +t}:
          succ_eq(Arrange.tally(Arrange.planned(rest)), List.length(&2, Arrange.Placing, rest), tally_planned(rest))
        case Arrange.Placing.Already{+f}:
          %succ_out(List.length(&2, T.Split, Arrange.done.renamed(rest)), Nat.add(Arrange.done.already(rest), Nat.add(List.length(&2, T.Split, Arrange.done.occupied(rest)), Arrange.done.unnamed(rest)))) : {_ == 1n+List.length(&2, Arrange.Placing, rest) : Nat}
          succ_eq(Arrange.tally(Arrange.planned(rest)), List.length(&2, Arrange.Placing, rest), tally_planned(rest))
        case Arrange.Placing.Occupied{+f, +h}:
          %succ_out(Arrange.done.already(rest), Nat.add(List.length(&2, T.Split, Arrange.done.occupied(rest)), Arrange.done.unnamed(rest))) : {Nat.add(List.length(&2, T.Split, Arrange.done.renamed(rest)), _) == 1n+List.length(&2, Arrange.Placing, rest) : Nat}
          %succ_out(List.length(&2, T.Split, Arrange.done.renamed(rest)), Nat.add(Arrange.done.already(rest), Nat.add(List.length(&2, T.Split, Arrange.done.occupied(rest)), Arrange.done.unnamed(rest)))) : {_ == 1n+List.length(&2, Arrange.Placing, rest) : Nat}
          succ_eq(Arrange.tally(Arrange.planned(rest)), List.length(&2, Arrange.Placing, rest), tally_planned(rest))
        case Arrange.Placing.Unnamed{+f}:
          %succ_out(List.length(&2, T.Split, Arrange.done.occupied(rest)), Arrange.done.unnamed(rest)) : {Nat.add(List.length(&2, T.Split, Arrange.done.renamed(rest)), Nat.add(Arrange.done.already(rest), _)) == 1n+List.length(&2, Arrange.Placing, rest) : Nat}
          %succ_out(Arrange.done.already(rest), Nat.add(List.length(&2, T.Split, Arrange.done.occupied(rest)), Arrange.done.unnamed(rest))) : {Nat.add(List.length(&2, T.Split, Arrange.done.renamed(rest)), _) == 1n+List.length(&2, Arrange.Placing, rest) : Nat}
          %succ_out(List.length(&2, T.Split, Arrange.done.renamed(rest)), Nat.add(Arrange.done.already(rest), Nat.add(List.length(&2, T.Split, Arrange.done.occupied(rest)), Arrange.done.unnamed(rest)))) : {_ == 1n+List.length(&2, Arrange.Placing, rest) : Nat}
          succ_eq(Arrange.tally(Arrange.planned(rest)), List.length(&2, Arrange.Placing, rest), tally_planned(rest))

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

def counted(+ps: List<&2, Arrange.Placing>, +ds: List<&2, T.Split>, h: {List.length(&2, Arrange.Placing, ps) == List.length(&2, T.Split, ds) : Nat}) -> {Nat.is_eq(Arrange.tally(Arrange.planned(ps)), List.length(&2, T.Split, ds)) == True{} : Bool}:
  RevL.is_eq_refl(Arrange.tally(Arrange.planned(ps)), List.length(&2, T.Split, ds), Equal.trans(Nat, Arrange.tally(Arrange.planned(ps)), List.length(&2, Arrange.Placing, ps), List.length(&2, T.Split, ds), tally_planned(ps), h))

def placed_counts(+held: Set(), +revs: List<&2, T.Split>, +ops: List<&2, T.Split>, +names: List<&2, T.Split>, rp: Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>, +a: Arrange.Arrangement, e: {Arrange.arrangement.placed(held, ops, names, rp) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}, hr: @xs: List<&2, Arrange.Placing> -> {rp == Done{xs} : Result<&2, &2, Main.Refused, List<&2, Arrange.Placing>>} -> {List.length(&2, Arrange.Placing, xs) == List.length(&2, T.Split, revs) : Nat}) -> {Arrange.accounted(a, revs, ops) == True{} : Bool}:
  match rp:
    case Fail{x}:
      Empty.absurd({Arrange.accounted(a, revs, ops) == True{} : Bool}, B.fail_done(Arrange.Arrangement, x, a, e))
    case Done{+ps}:
      %done_plan(Arrange.Arrangement{ps, Arrange.ops.placed(ops, held, names)}, a, e) : {Arrange.accounted(_, revs, ops) == True{} : Bool}
      B.and_tt(Nat.is_eq(Arrange.tally(Arrange.planned(ps)), List.length(&2, T.Split, revs)), Nat.is_eq(Arrange.tally(Arrange.planned(Arrange.ops.placed(ops, held, names))), List.length(&2, T.Split, ops)),
        counted(ps, revs, hr(ps, {==})), counted(Arrange.ops.placed(ops, held, names), ops, ops_length(ops, held, names)))

def named_counts(+refile: Bool, +held: Set(), +ss: List<&2, T.Split>, +revs: List<&2, T.Split>, +ops: List<&2, T.Split>, names: Result<&2, &2, Main.Refused, List<&2, T.Split>>, +a: Arrange.Arrangement, e: {Arrange.arrangement.named(refile, held, ss, revs, ops, names) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}) -> {Arrange.accounted(a, revs, ops) == True{} : Bool}:
  match names:
    case Fail{x}:
      Empty.absurd({Arrange.accounted(a, revs, ops) == True{} : Bool}, B.fail_done(Arrange.Arrangement, x, a, e))
    case Done{+ns}:
      placed_counts(held, revs, ops, ns, Arrange.revs.placed(revs, refile, held, ss), a, e, xs => h => revs_length(revs, refile, held, ss, xs, h))

# Every file arranging walks is counted once in what a dry run prints.
def counts(+refile: Bool, +fs: List<&2, Main.Full>, +revs: List<&2, T.Split>, +ops: List<&2, T.Split>, +ls: List<&2, String>, +a: Arrange.Arrangement, e: {Arrange.arrangement.r(refile, fs, revs, ops, ls) == Done{a} : Result<&2, &2, Main.Refused, Arrange.Arrangement>}) -> {Arrange.accounted(a, revs, ops) == True{} : Bool}:
  named_counts(refile, Arrange.taken(ls), Arrange.stems(Arrange.distinct(fs)), revs, ops, Arrange.operation_names(fs, Arrange.stems(Arrange.distinct(fs))), a, e)
