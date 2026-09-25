# A name rule's pattern, as decision 0011 reads it: runs of characters with
# `*` between them, where `*` is any run of characters and nothing else is
# special. `Folder.matches` finds each run after the first at its leftmost
# place and asks the last to end the name; this holds it to the plain
# reading — a pattern matches exactly the names it spells with each `*`
# standing for some run of characters, whatever run each stands for.
import Base
import ./folder.bend as F
import ./string_lemmas.bend as S
import ./bookmark_lemmas.bend as BmL
import ./skip_lemmas.bend as SkipL
import ./composition_lemmas.bend as Comp
import ./anchor_lemmas.bend as AL
import ./host_lemmas.bend as HostL

# What a pattern spells
# ---------------------

# The runs after the first, each after what its `*` stands for; where `xs`
# runs out, a `*` stands for nothing.
def filled(more: List<&2, String>, xs: List<&2, String>) -> String:
  match more xs:
    case Nil{} _:
      SNil{}
    case r <> rest x <> xr:
      x ++ r ++ filled(rest, xr)
    case r <> rest Nil{}:
      r ++ filled(rest, Nil{})

# The name the pattern `r0*r1*…` spells with each `*` standing for the run
# of `xs` in its place.
def fill(+r0: String, more: List<&2, String>, xs: List<&2, String>) -> String:
  r0 ++ filled(more, xs)

# Strings
# -------

# A string opens with itself.
def sw_app(a: String, +b: String) -> {String.starts_with(a ++ b, a) == True{} : Bool}:
  match a:
    case SNil{}:
      match b:
        case SNil{}:
          {==}
        case SCon{c, t}:
          {==}
    case SCon{+x, t}:
      %Equal.sym(Bool, Char.is_eq(x, x), True{}, HostL.char_refl(x)) : {String.starts_with.if(t ++ b, t, _) == True{} : Bool}
      sw_app(t, b)

def drop_app(a: String, +b: String) -> {String.drop(a ++ b, String.length(a)) == b : String}:
  match a:
    case SNil{}:
      HostL.drop_zero(b)
    case SCon{x, t}:
      drop_app(t, b)

def app_assoc(a: String, +b: String, +c: String) -> {(a ++ b) ++ c == a ++ (b ++ c) : String}:
  SkipL.app_assoc(a, b, c)

# Dropping from a string and what follows it no more than the string holds
# leaves the rest of the string, then what follows.
def drop_le(a: String, +b: String, n: Nat, +h: {Nat.is_le(n, String.length(a)) == True{} : Bool}) -> {String.drop(a ++ b, n) == String.drop(a, n) ++ b : String}:
  match a n:
    case SNil{} 0n:
      HostL.drop_zero(b)
    case SNil{} 1n+m:
      Empty.absurd({String.drop(b, 1n+m) == SNil{} ++ b : String}, S.false_true(h))
    case SCon{x, t} 0n:
      {==}
    case SCon{x, t} 1n+m:
      drop_le(t, b, m, h)

def le_len(a: String, +b: String) -> {Nat.is_le(String.length(b), String.length(a ++ b)) == True{} : Bool}:
  match a:
    case SNil{}:
      Comp.le_refl(String.length(b))
    case SCon{x, +t}:
      Comp.le_succ(String.length(b), String.length(t ++ b), le_len(t, b))

def ge_refl(n: Nat) -> {Nat.is_ge(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ge_refl(p)

def ge_succ(a: Nat, b: Nat, h: {Nat.is_ge(a, b) == True{} : Bool}) -> {Nat.is_ge(1n+a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.is_ge(1n, 1n+q) == True{} : Bool}, S.false_true(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ge_succ(p, q, h)

def ge_len(a: String, +b: String) -> {Nat.is_ge(String.length(a ++ b), String.length(b)) == True{} : Bool}:
  match a:
    case SNil{}:
      ge_refl(String.length(b))
    case SCon{x, +t}:
      ge_succ(String.length(t ++ b), String.length(b), ge_len(t, b))

# A string ends with what ends it.
def ew_app(+a: String, +b: String) -> {String.ends_with(a ++ b, b) == True{} : Bool}:
  %Equal.sym(String, String.reverse(a ++ b), String.reverse(b) ++ String.reverse(a), SkipL.rev_app(a, b)) : {String.starts_with(_, String.reverse(b)) == True{} : Bool}
  sw_app(String.reverse(b), String.reverse(a))

# The last run, after anything, ends the name and is no longer than it.
def last_ok(+v: String, +m: String) -> {Bool.and(Nat.is_ge(String.length(v ++ m), String.length(m)), String.ends_with(v ++ m, m)) == True{} : Bool}:
  AL.and_intro(Nat.is_ge(String.length(v ++ m), String.length(m)), String.ends_with(v ++ m, m), ge_len(v, m), ew_app(v, m))

# `split` at `*` of runs joined by it: the runs.
def split_join.go(xs: List<&2, String>, +h: String, +c: Char, +hh: {HostL.nosep(h, c) == True{} : Bool}, +hx: {HostL.all_nosep(xs, c) == True{} : Bool}) -> {String.split(String.join.go(xs, h, SCon{c, SNil{}}), c) == h <> xs : List<&2, String>}:
  match xs:
    case Nil{}:
      HostL.split_whole(h, c, hh)
    case +x <> +rest:
      Equal.trans(List<&2, String>, String.split(h ++ SCon{c, String.join.go(rest, x, SCon{c, SNil{}})}, c), h <> String.split(String.join.go(rest, x, SCon{c, SNil{}}), c), h <> x <> rest,
        HostL.split_sep(h, String.join.go(rest, x, SCon{c, SNil{}}), c, hh),
        Equal.cong(List<&2, String>, List<&2, String>, l => h <> l, String.split(String.join.go(rest, x, SCon{c, SNil{}}), c), x <> rest,
          split_join.go(rest, x, c, Comp.and_left(HostL.nosep(x, c), HostL.all_nosep(rest, c), hx), Comp.and_right(HostL.nosep(x, c), HostL.all_nosep(rest, c), hx))))

def runs_of(+r0: String, +more: List<&2, String>, +h: {HostL.all_nosep(r0 <> more, '*') == True{} : Bool}) -> {String.split(String.join(r0 <> more, "*"), '*') == r0 <> more : List<&2, String>}:
  split_join.go(more, r0, '*', Comp.and_left(HostL.nosep(r0, '*'), HostL.all_nosep(more, '*'), h), Comp.and_right(HostL.nosep(r0, '*'), HostL.all_nosep(more, '*'), h))

# Every name it spells
# --------------------

def after_true(s: String, +run: String, +n: Nat) -> {F.after(s, run, n, True{}) == Some{String.drop(s, n)} : Maybe<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      {==}

# Wherever a run stands in a name, the first place it stands is no later:
# what follows that place is what follows the other, with something before
# it; and a tail that takes anything before it takes that.
def found_later(w: String, b: Bool, +run: String, +t: String, +ms: List<&2, String>, +eb: {String.starts_with(w ++ (run ++ t), run) == b : Bool}, ih: @u: String -> {F.runs.match(ms, Some{u ++ t}) == True{} : Bool}) -> {F.runs.match(ms, F.after(w ++ (run ++ t), run, String.length(run), b)) == True{} : Bool}:
  match w b:
    case SNil{} True{}:
      %Equal.sym(Maybe<&2, String>, F.after(run ++ t, run, String.length(run), True{}), Some{String.drop(run ++ t, String.length(run))}, after_true(run ++ t, run, String.length(run))) : {F.runs.match(ms, _) == True{} : Bool}
      %Equal.sym(String, String.drop(run ++ t, String.length(run)), t, drop_app(run, t)) : {F.runs.match(ms, Some{_}) == True{} : Bool}
      ih(SNil{})
    case SNil{} False{}:
      Empty.absurd({F.runs.match(ms, F.after(run ++ t, run, String.length(run), False{})) == True{} : Bool}, S.false_true(Equal.trans(Bool, False{}, String.starts_with(run ++ t, run), True{}, Equal.sym(Bool, String.starts_with(run ++ t, run), False{}, eb), sw_app(run, t))))
    case SCon{+c, +w2} True{}:
      %app_assoc(SCon{c, w2}, run, t) : {F.runs.match(ms, Some{String.drop(_, String.length(run))}) == True{} : Bool}
      %Equal.sym(String, String.drop((SCon{c, w2} ++ run) ++ t, String.length(run)), String.drop(SCon{c, w2} ++ run, String.length(run)) ++ t, drop_le(SCon{c, w2} ++ run, t, String.length(run), le_len(SCon{c, w2}, run))) : {F.runs.match(ms, Some{_}) == True{} : Bool}
      ih(String.drop(SCon{c, w2} ++ run, String.length(run)))
    case SCon{+c, +w2} False{}:
      found_later(w2, String.starts_with(w2 ++ (run ++ t), run), run, t, ms, {==}, ih)

# The last run, after what its `*` stands for, ends the name.
def fits_last(+m: String, xs: List<&2, String>, +u: String) -> {F.runs.match([m], Some{u ++ filled([m], xs)}) == True{} : Bool}:
  match xs:
    case Nil{}:
      %Equal.sym(String, m ++ SNil{}, m, HostL.app_nil(m)) : {F.runs.match([m], Some{u ++ _}) == True{} : Bool}
      last_ok(u, m)
    case +x <> xr:
      %Equal.sym(String, m ++ SNil{}, m, HostL.app_nil(m)) : {F.runs.match([m], Some{u ++ (x ++ _)}) == True{} : Bool}
      %app_assoc(u, x, m) : {F.runs.match([m], Some{_}) == True{} : Bool}
      last_ok(u ++ x, m)

# The runs after the first, each after what its `*` stands for, after
# anything at all: the tail of the matcher takes them.
def fits(ms: List<&2, String>, +m: String, xs: List<&2, String>, +u: String) -> {F.runs.match(m <> ms, Some{u ++ filled(m <> ms, xs)}) == True{} : Bool}:
  match ms xs:
    case Nil{} _:
      fits_last(m, xs, u)
    case +m2 <> +ms2 Nil{}:
      found_later(u, String.starts_with(u ++ (m ++ filled(m2 <> ms2, Nil{})), m), m, filled(m2 <> ms2, Nil{}), m2 <> ms2, {==}, v => fits(ms2, m2, Nil{}, v))
    case +m2 <> +ms2 +x <> +xr:
      %app_assoc(u, x, m ++ filled(m2 <> ms2, xr)) : {F.runs.match(m <> m2 <> ms2, Some{_}) == True{} : Bool}
      found_later(u ++ x, String.starts_with((u ++ x) ++ (m ++ filled(m2 <> ms2, xr)), m), m, filled(m2 <> ms2, xr), m2 <> ms2, {==}, v => fits(ms2, m2, xr, v))

def fits_all(more: List<&2, String>, xs: List<&2, String>) -> {F.runs.match(more, Some{filled(more, xs)}) == True{} : Bool}:
  match more:
    case Nil{}:
      {==}
    case +m <> +ms:
      fits(ms, m, xs, SNil{})

# `a_pattern_matches_each_name_it_spells`.
def spells(+r0: String, +more: List<&2, String>, +xs: List<&2, String>, +h: {HostL.all_nosep(r0 <> more, '*') == True{} : Bool}) -> {F.matches(String.join(r0 <> more, "*"), fill(r0, more, xs)) == True{} : Bool}:
  %Equal.sym(List<&2, String>, String.split(String.join(r0 <> more, "*"), '*'), r0 <> more, runs_of(r0, more, h)) : {F.matches.of(fill(r0, more, xs), _) == True{} : Bool}
  %Equal.sym(Bool, String.starts_with(r0 ++ filled(more, xs), r0), True{}, sw_app(r0, filled(more, xs))) : {Bool.and(_, F.runs.match(more, Some{String.drop(r0 ++ filled(more, xs), String.length(r0))})) == True{} : Bool}
  %Equal.sym(String, String.drop(r0 ++ filled(more, xs), String.length(r0)), filled(more, xs), drop_app(r0, filled(more, xs))) : {Bool.and(True{}, F.runs.match(more, Some{_})) == True{} : Bool}
  fits_all(more, xs)

# Only names it spells
# --------------------

def mdisc(m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some(-x: String, e: {None{} == Some{x} : Maybe<&2, String>}) -> Empty:
  %e : {mdisc(_) : Type}
  Unit{}

def some_inj(-a: String, -b: String, e: {Some{a} == Some{b} : Maybe<&2, String>}) -> {a == b : String}:
  Equal.cong(Maybe<&2, String>, String, m => Maybe.default(&2, String, m, a), Some{a}, Some{b}, e)

# Nothing opens with more than it holds.
def sw_nil(p: String, e: {String.starts_with(SNil{}, p) == True{} : Bool}) -> {p == SNil{} : String}:
  match p:
    case SNil{}:
      {==}
    case SCon{c, t}:
      Empty.absurd({SCon{c, t} == SNil{} : String}, S.false_true(e))

def sw_split.at(b: Bool, +x: Char, +y: Char, +st: String, +pt: String, eb: {Char.is_eq(x, y) == b : Bool}, e: {String.starts_with.if(st, pt, b) == True{} : Bool}, ih: {String.starts_with(st, pt) == True{} : Bool} -> {pt ++ String.drop(st, String.length(pt)) == st : String}) -> {SCon{y, pt ++ String.drop(st, String.length(pt))} == SCon{x, st} : String}:
  match b:
    case True{}:
      %BmL.chr_eq(x, y, eb) : {SCon{_, pt ++ String.drop(st, String.length(pt))} == SCon{x, st} : String}
      Equal.cong(String, String, v => SCon{x, v}, pt ++ String.drop(st, String.length(pt)), st, ih(e))
    case False{}:
      Empty.absurd({SCon{y, pt ++ String.drop(st, String.length(pt))} == SCon{x, st} : String}, S.false_true(e))

# A name that opens with a run is the run and what follows it.
def sw_split(s: String, p: String, e: {String.starts_with(s, p) == True{} : Bool}) -> {p ++ String.drop(s, String.length(p)) == s : String}:
  match s p:
    case s2 SNil{}:
      HostL.drop_zero(s2)
    case SNil{} SCon{y, pt}:
      Empty.absurd({SCon{y, pt} ++ String.drop(SNil{}, String.length(SCon{y, pt})) == SNil{} : String}, S.false_true(e))
    case SCon{+x, +st} SCon{+y, +pt}:
      sw_split.at(Char.is_eq(x, y), x, y, st, pt, {==}, e, h => sw_split(st, pt, h))

def passed(+c: Char, +t: String, +run: String, -r: String, p: &w: String -> {w ++ (run ++ r) == t : String}) -> &w: String -> {w ++ (run ++ r) == SCon{c, t} : String}:
  match p:
    case (+w2, p2):
      (SCon{c, w2}, Equal.cong(String, String, v => SCon{c, v}, w2 ++ (run ++ r), t, p2))

# Where the matcher finds a run, the name is what it passed, the run, and
# what follows.
def after_split(s: String, hit: Bool, +run: String, +eh: {String.starts_with(s, run) == hit : Bool}, -r: String, e: {F.after(s, run, String.length(run), hit) == Some{r} : Maybe<&2, String>}) -> &w: String -> {w ++ (run ++ r) == s : String}:
  match s hit:
    case SNil{} True{}:
      +er = some_inj(SNil{}, r, e)
      (SNil{}, (%Equal.sym(String, run, SNil{}, sw_nil(run, eh)) : {_ ++ r == SNil{} : String}
        Equal.sym(String, SNil{}, r, er)))
    case SNil{} False{}:
      Empty.absurd(&w: String -> {w ++ (run ++ r) == SNil{} : String}, none_some(r, e))
    case SCon{+c, +t} True{}:
      +er = some_inj(String.drop(SCon{c, t}, String.length(run)), r, e)
      (SNil{}, (%er : {run ++ _ == SCon{c, t} : String}
        sw_split(SCon{c, t}, run, eh)))
    case SCon{+c, +t} False{}:
      passed(c, t, run, r, after_split(t, String.starts_with(t, run), run, {==}, r, e))

# A name that ends with the last run is something, then that run.
def split_last(+s: String, +m: String, e: {String.ends_with(s, m) == True{} : Bool}) -> {String.reverse(String.drop(String.reverse(s), String.length(String.reverse(m)))) ++ m == s : String}:
  +d = String.drop(String.reverse(s), String.length(String.reverse(m)))
  Equal.trans(String, String.reverse(d) ++ m, String.reverse(String.reverse(m) ++ d), s,
    (%Equal.sym(String, String.reverse(String.reverse(m) ++ d), String.reverse(d) ++ String.reverse(String.reverse(m)), SkipL.rev_app(String.reverse(m), d)) : {String.reverse(d) ++ m == _ : String}
      (%Equal.sym(String, String.reverse(String.reverse(m)), m, SkipL.rev_rev(m)) : {String.reverse(d) ++ m == String.reverse(d) ++ _ : String}
        {==})),
    (%Equal.sym(String, String.reverse(m) ++ d, String.reverse(s), sw_split(String.reverse(s), String.reverse(m), e)) : {String.reverse(_) == s : String}
      SkipL.rev_rev(s)))

def empty_nil(s: String, e: {String.is_empty(s) == True{} : Bool}) -> {s == SNil{} : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      Empty.absurd({SCon{c, t} == SNil{} : String}, S.false_true(e))

# What the matcher passed before a run, and what the rest spells after it.
def glue(+m: String, +rest: List<&2, String>, -r: String, -s: String, pw: &w: String -> {w ++ (m ++ r) == s : String}, px: &xs: List<&2, String> -> {filled(rest, xs) == r : String}) -> &xs: List<&2, String> -> {filled(m <> rest, xs) == s : String}:
  match pw:
    case (+w, ew):
      match px:
        case (+xs2, ex):
          (w <> xs2, Equal.trans(String, w ++ (m ++ filled(rest, xs2)), w ++ (m ++ r), s, Equal.cong(String, String, v => w ++ (m ++ v), filled(rest, xs2), r, ex), ew))

def none_false(+m2: String, ms2: List<&2, String>) -> {F.runs.match(m2 <> ms2, None{}) == False{} : Bool}:
  match ms2:
    case Nil{}:
      {==}
    case x <> xs:
      {==}

def spelled_mid(mb: Maybe<&2, String>, +s: String, +m: String, +m2: String, +ms2: List<&2, String>, em: {F.after(s, m, String.length(m), String.starts_with(s, m)) == mb : Maybe<&2, String>}, e: {F.runs.match(m2 <> ms2, mb) == True{} : Bool}, ih: @r: String -> {F.runs.match(m2 <> ms2, Some{r}) == True{} : Bool} -> &xs: List<&2, String> -> {filled(m2 <> ms2, xs) == r : String}) -> &xs: List<&2, String> -> {filled(m <> m2 <> ms2, xs) == s : String}:
  match mb:
    case None{}:
      Empty.absurd(&xs: List<&2, String> -> {filled(m <> m2 <> ms2, xs) == s : String}, S.false_true(Equal.trans(Bool, False{}, F.runs.match(m2 <> ms2, None{}), True{}, Equal.sym(Bool, F.runs.match(m2 <> ms2, None{}), False{}, none_false(m2, ms2)), e)))
    case Some{+r}:
      glue(m, m2 <> ms2, r, s, after_split(s, String.starts_with(s, m), m, {==}, r, em), ih(r, e))

# What the matcher takes after the first run is the rest of the pattern
# spelled with some run for each `*`.
def spelled_by(more: List<&2, String>, +s: String, e: {F.runs.match(more, Some{s}) == True{} : Bool}) -> &xs: List<&2, String> -> {filled(more, xs) == s : String}:
  match more:
    case Nil{}:
      (Nil{}, Equal.sym(String, s, SNil{}, empty_nil(s, e)))
    case +m <> +rest:
      match rest:
        case Nil{}:
          ([String.reverse(String.drop(String.reverse(s), String.length(String.reverse(m))))], (%Equal.sym(String, m ++ SNil{}, m, HostL.app_nil(m)) : {String.reverse(String.drop(String.reverse(s), String.length(String.reverse(m)))) ++ _ == s : String}
            split_last(s, m, Comp.and_right(Nat.is_ge(String.length(s), String.length(m)), String.ends_with(s, m), e))))
        case +m2 <> +ms2:
          spelled_mid(F.after(s, m, String.length(m), String.starts_with(s, m)), s, m, m2, ms2, {==}, e, r => h => spelled_by(m2 <> ms2, r, h))

def matched(+r0: String, +more: List<&2, String>, +c: String, +h: {HostL.all_nosep(r0 <> more, '*') == True{} : Bool}, e: {F.matches(String.join(r0 <> more, "*"), c) == True{} : Bool}) -> {F.matches.of(c, r0 <> more) == True{} : Bool}:
  %runs_of(r0, more, h) : {F.matches.of(c, _) == True{} : Bool}
  e

def front(+r0: String, +more: List<&2, String>, -c: String, ec: {r0 ++ String.drop(c, String.length(r0)) == c : String}, p: &xs: List<&2, String> -> {filled(more, xs) == String.drop(c, String.length(r0)) : String}) -> &xs: List<&2, String> -> {fill(r0, more, xs) == c : String}:
  match p:
    case (+xs, ex):
      (xs, Equal.trans(String, r0 ++ filled(more, xs), r0 ++ String.drop(c, String.length(r0)), c, Equal.cong(String, String, v => r0 ++ v, filled(more, xs), String.drop(c, String.length(r0)), ex), ec))

# `a_pattern_matches_only_names_it_spells`.
def spelled(+r0: String, +more: List<&2, String>, +c: String, +h: {HostL.all_nosep(r0 <> more, '*') == True{} : Bool}, e: {F.matches(String.join(r0 <> more, "*"), c) == True{} : Bool}) -> &xs: List<&2, String> -> {fill(r0, more, xs) == c : String}:
  +e2 = matched(r0, more, c, h, e)
  front(r0, more, c,
    sw_split(c, r0, Comp.and_left(String.starts_with(c, r0), F.runs.match(more, Some{String.drop(c, String.length(r0))}), e2)),
    spelled_by(more, String.drop(c, String.length(r0)), Comp.and_right(String.starts_with(c, r0), F.runs.match(more, Some{String.drop(c, String.length(r0))}), e2)))
