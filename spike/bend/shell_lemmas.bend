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

# Decision 0072's positive rule, in Base's classes of character
# -------------------------------------------------------------

# An ASCII letter or digit, as Base classes a character.
def alnum(+c: Char) -> Bool:
  Bool.or(Char.is_alpha(c), Char.is_digit(c))

# `c` and the characters after it: each a letter, a digit or a hyphen, and
# the last a letter or a digit.
def tail(s: String, +c: Char) -> Bool:
  match s:
    case SNil{}:
      alnum(c)
    case SCon{+d, t}:
      Bool.and(Bool.or(alnum(c), Char.is_eq(c, '-')), tail(t, d))

# A word decision 0072 looks for: not empty, a letter or a digit at each
# end, and letters, digits and hyphens between.
def word(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, t}:
      Bool.and(alnum(c), tail(t, c))

# The last character of `c` and the characters after it.
def last(s: String, +c: Char) -> Char:
  match s:
    case SNil{}:
      c
    case SCon{+d, t}:
      last(t, d)

def or4(l: Bool, u: Bool, -d: Bool, -h: Bool) -> {Bool.or(Bool.or(l, u), Bool.or(d, h)) == Bool.or(Bool.or(Bool.or(u, l), d), h) : Bool}:
  match l u:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# The alphabet `shell.bend` spells by code point is Base's letters and
# digits, and the hyphen.
def spelling_is(c: Char) -> {Shell.spelling(c) == Bool.or(alnum(c), Char.is_eq(c, '-')) : Bool}:
  match c:
    case Chr{+x}:
      or4(Bool.and(U32.is_ge(x, 97), U32.is_le(x, 122)), Bool.and(U32.is_ge(x, 65), U32.is_le(x, 90)), Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)), U32.is_eq(x, 45))

def sw_nil(str: String) -> {String.starts_with(str, SNil{}) == True{} : Bool}:
  match str:
    case SNil{}:
      {==}
    case SCon{x, u}:
      {==}

def sw_if(str: String, flag: Bool) -> {String.starts_with.if(str, SNil{}, flag) == flag : Bool}:
  match flag:
    case False{}:
      {==}
    case True{}:
      sw_nil(str)

# A string reversed onto `c` and more opens with a hyphen where its last
# character, or `c` for the empty string, is one.
def ends_rev(t: String, +c: Char, acc: String) -> {String.starts_with(String.reverse.go(t, SCon{c, acc}), "-") == Char.is_eq(last(t, c), '-') : Bool}:
  match t:
    case SNil{}:
      sw_if(acc, Char.is_eq(c, '-'))
    case SCon{+d, u}:
      ends_rev(u, d, SCon{c, acc})

def k_false(a: Bool) -> {Bool.and(Bool.not(False{}), Bool.and(Bool.or(a, False{}), True{})) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def k_end(+c: Char, e: Bool, ee: {Char.is_eq(c, '-') == e : Bool}) -> {Bool.and(Bool.not(e), Bool.and(Bool.or(alnum(c), e), True{})) == alnum(c) : Bool}:
  match e:
    case True{}:
      %Equal.sym(Char, c, '-', BmL.chr_eq(c, '-', ee)) : {False{} == alnum(_) : Bool}
      {==}
    case False{}:
      k_false(alnum(c))


def swap(x: Bool, h: Bool, -y: Bool) -> {Bool.and(x, Bool.and(h, y)) == Bool.and(h, Bool.and(x, y)) : Bool}:
  match x h:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# What `shell.bend` asks of every character but the first — the alphabet,
# and no hyphen last — is what `tail` asks.
def tail_is(t: String, +c: Char) -> {Bool.and(Bool.not(Char.is_eq(last(t, c), '-')), Bool.and(Shell.spelling(c), Shell.spelled(t))) == tail(t, c) : Bool}:
  match t:
    case SNil{}:
      %Equal.sym(Bool, Shell.spelling(c), Bool.or(alnum(c), Char.is_eq(c, '-')), spelling_is(c)) : {Bool.and(Bool.not(Char.is_eq(c, '-')), Bool.and(_, True{})) == alnum(c) : Bool}
      k_end(c, Char.is_eq(c, '-'), {==})
    case SCon{+d, +u}:
      %tail_is(u, d) : {Bool.and(Bool.not(Char.is_eq(last(u, d), '-')), Bool.and(Shell.spelling(c), Bool.and(Shell.spelling(d), Shell.spelled(u)))) == Bool.and(Bool.or(alnum(c), Char.is_eq(c, '-')), _) : Bool}
      %Equal.sym(Bool, Shell.spelling(c), Bool.or(alnum(c), Char.is_eq(c, '-')), spelling_is(c)) : {Bool.and(Bool.not(Char.is_eq(last(u, d), '-')), Bool.and(_, Bool.and(Shell.spelling(d), Shell.spelled(u)))) == Bool.and(Bool.or(alnum(c), Char.is_eq(c, '-')), Bool.and(Bool.not(Char.is_eq(last(u, d), '-')), Bool.and(Shell.spelling(d), Shell.spelled(u)))) : Bool}
      swap(Bool.not(Char.is_eq(last(u, d), '-')), Bool.or(alnum(c), Char.is_eq(c, '-')), Bool.and(Shell.spelling(d), Shell.spelled(u)))

def head_false(a: Bool, el: Bool, -s: Bool) -> {Bool.and(el, Bool.and(Bool.or(a, False{}), s)) == Bool.and(a, Bool.and(el, Bool.and(Bool.or(a, False{}), s))) : Bool}:
  match a el:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# A word opening with a hyphen is none; any other opens with a letter or a
# digit where it opens with a character of the alphabet.
def head_ok(+c: Char, e: Bool, ee: {Char.is_eq(c, '-') == e : Bool}, +el: Bool, -s: Bool) -> {Bool.and(Bool.not(e), Bool.and(el, Bool.and(Bool.or(alnum(c), e), s))) == Bool.and(alnum(c), Bool.and(el, Bool.and(Bool.or(alnum(c), e), s))) : Bool}:
  match e:
    case True{}:
      %Equal.sym(Char, c, '-', BmL.chr_eq(c, '-', ee)) : {False{} == Bool.and(alnum(_), Bool.and(el, Bool.and(Bool.or(alnum(c), True{}), s))) : Bool}
      {==}
    case False{}:
      head_false(alnum(c), el, s)

# Decision 0072's rule as `shell.bend` spells it is the rule as `word`
# states it.
def dispatchable_is(w: String) -> {Shell.dispatchable(w) == word(w) : Bool}:
  match w:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, String.starts_with.if(t, SNil{}, Char.is_eq(c, '-')), Char.is_eq(c, '-'), sw_if(t, Char.is_eq(c, '-'))) : {Bool.and(Bool.not(_), Bool.and(Bool.not(String.starts_with(String.reverse.go(t, SCon{c, SNil{}}), "-")), Bool.and(Shell.spelling(c), Shell.spelled(t)))) == Bool.and(alnum(c), tail(t, c)) : Bool}
      %Equal.sym(Bool, String.starts_with(String.reverse.go(t, SCon{c, SNil{}}), "-"), Char.is_eq(last(t, c), '-'), ends_rev(t, c, SNil{})) : {Bool.and(Bool.not(Char.is_eq(c, '-')), Bool.and(Bool.not(_), Bool.and(Shell.spelling(c), Shell.spelled(t)))) == Bool.and(alnum(c), tail(t, c)) : Bool}
      %tail_is(t, c) : {Bool.and(Bool.not(Char.is_eq(c, '-')), Bool.and(Bool.not(Char.is_eq(last(t, c), '-')), Bool.and(Shell.spelling(c), Shell.spelled(t)))) == Bool.and(alnum(c), _) : Bool}
      %Equal.sym(Bool, Shell.spelling(c), Bool.or(alnum(c), Char.is_eq(c, '-')), spelling_is(c)) : {Bool.and(Bool.not(Char.is_eq(c, '-')), Bool.and(Bool.not(Char.is_eq(last(t, c), '-')), Bool.and(_, Shell.spelled(t)))) == Bool.and(alnum(c), Bool.and(Bool.not(Char.is_eq(last(t, c), '-')), Bool.and(_, Shell.spelled(t)))) : Bool}
      head_ok(c, Char.is_eq(c, '-'), {==}, Bool.not(Char.is_eq(last(t, c), '-')), Shell.spelled(t))

# A word of the alphabet runs `historica-` and the word, in the directory
# given, with the words after it as they were typed.
def runs_word(+base: String, +w: String, +args: List<&2, String>, +h: {word(w) == True{} : Bool}) -> {Shell.plan(base, w, args) == Shell.Plan.Run{base, "historica-" ++ w, args} : Shell.Plan}:
  %Equal.sym(Bool, Shell.dispatchable(w), True{}, Equal.trans(Bool, Shell.dispatchable(w), word(w), True{}, dispatchable_is(w), h)) : {Bool.pick(Shell.Plan, _, Shell.Plan.Run{base, "historica-" ++ w, args}, Shell.Plan.Missing{Shell.missing(w)}) == Shell.Plan.Run{base, "historica-" ++ w, args} : Shell.Plan}
  {==}

# Any other word is the refusal a command this tool does not have gets.
def refuses_word(+base: String, +w: String, +args: List<&2, String>, +h: {word(w) == False{} : Bool}) -> {Shell.plan(base, w, args) == Shell.Plan.Missing{"there is no `" ++ w ++ "` command"} : Shell.Plan}:
  %Equal.sym(Bool, Shell.dispatchable(w), False{}, Equal.trans(Bool, Shell.dispatchable(w), word(w), False{}, dispatchable_is(w), h)) : {Bool.pick(Shell.Plan, _, Shell.Plan.Run{base, "historica-" ++ w, args}, Shell.Plan.Missing{Shell.missing(w)}) == Shell.Plan.Missing{"there is no `" ++ w ++ "` command"} : Shell.Plan}
  {==}
