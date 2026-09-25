# Decision 0072's dispatch runs `historica-` and the word, and only a word
# spelled in its alphabet — so never one with a `/` in it, which would run
# a file by where it is rather than look a program up on `PATH`.
import Base
import ./shell.bend as Shell
import ./text.bend as T
import ./bookmark_lemmas.bend as BmL
import ./composition_lemmas.bend as Comp

def program.of(p: Shell.Plan) -> String:
  match p:
    case Shell.Plan.Run{d, pr, a}:
      pr
    case Shell.Plan.Missing{m}:
      SNil{}

def ran(p: Shell.Plan) -> Bool:
  match p:
    case Shell.Plan.Run{d, pr, a}:
      True{}
    case Shell.Plan.Missing{m}:
      False{}

# A word the alphabet refuses is not looked for.
def planned(+base: String, +w: String, args: List<&2, String>, b: Bool, eb: {Shell.dispatchable(w) == b : Bool}, +d: String, +p: String, as: List<&2, String>, e: {Shell.plan(base, w, args) == Shell.Plan.Run{d, p, as} : Shell.Plan}) -> {Shell.dispatchable(w) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Shell.dispatchable(w) == True{} : Bool}, Comp.false_true(Equal.trans(Bool, False{}, ran(Shell.plan(base, w, args)), True{},
        Equal.cong(Bool, Bool, x => ran(Bool.pick(Shell.Plan, x, Shell.Plan.Run{base, "historica-" ++ w, args}, Shell.Plan.Missing{Shell.missing(w)})), False{}, Shell.dispatchable(w), Equal.sym(Bool, Shell.dispatchable(w), False{}, eb)),
        Equal.cong(Shell.Plan, Bool, x => ran(x), Shell.plan(base, w, args), Shell.Plan.Run{d, p, as}, e))))

# `/` is not in the alphabet.
def slash.at(+c: Char, b: Bool, eb: {Char.is_eq(c, '/') == b : Bool}, h: {Shell.spelling(c) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Comp.false_true(Equal.trans(Bool, False{}, Shell.spelling(c), True{},
        Equal.cong(Char, Bool, x => Shell.spelling(x), '/', c, Equal.sym(Char, c, '/', BmL.chr_eq(c, '/', eb))), h)))

def unslashed(s: String, +h: {Shell.spelled(s) == True{} : Bool}) -> {T.has_char(s, '/') == False{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Char.is_eq(c, '/'), False{}, slash.at(c, Char.is_eq(c, '/'), {==}, Comp.and_left(Shell.spelling(c), Shell.spelled(t), h))) : {Bool.or(_, T.has_char(t, '/')) == False{} : Bool}
      %Equal.sym(Bool, T.has_char(t, '/'), False{}, unslashed(t, Comp.and_right(Shell.spelling(c), Shell.spelled(t), h))) : {Bool.or(False{}, _) == False{} : Bool}
      {==}

# The program a dispatch runs holds no `/`.
def runs(+base: String, +w: String, args: List<&2, String>, +d: String, +p: String, as: List<&2, String>, +e: {Shell.plan(base, w, args) == Shell.Plan.Run{d, p, as} : Shell.Plan}) -> {T.has_char(p, '/') == False{} : Bool}:
  +ok = planned(base, w, args, Shell.dispatchable(w), {==}, d, p, as, e)
  +named = Equal.trans(String, p, program.of(Shell.plan(base, w, args)), "historica-" ++ w,
    Equal.cong(Shell.Plan, String, x => program.of(x), Shell.Plan.Run{d, p, as}, Shell.plan(base, w, args), Equal.sym(Shell.Plan, Shell.plan(base, w, args), Shell.Plan.Run{d, p, as}, e)),
    Equal.cong(Bool, String, x => program.of(Bool.pick(Shell.Plan, x, Shell.Plan.Run{base, "historica-" ++ w, args}, Shell.Plan.Missing{Shell.missing(w)})), Shell.dispatchable(w), True{}, ok))
  +spelled = Comp.and_right(Bool.not(String.ends_with(w, "-")), Shell.spelled(w), Comp.and_right(Bool.not(String.starts_with(w, "-")), Bool.and(Bool.not(String.ends_with(w, "-")), Shell.spelled(w)), Comp.and_right(Bool.not(String.is_empty(w)), Bool.and(Bool.not(String.starts_with(w, "-")), Bool.and(Bool.not(String.ends_with(w, "-")), Shell.spelled(w))), ok)))
  %Equal.sym(String, p, "historica-" ++ w, named) : {T.has_char(_, '/') == False{} : Bool}
  unslashed(w, spelled)
