# What `name` writes to. A bookmark's file is its name under `names/`, so a
# name it takes that began `/` or climbed out with `..` would be a name
# choosing where in the store — or out of it — its file goes. Every name
# `name` takes is refused neither by `check_name` nor by the path rules it
# reads, so it is never absolute and never climbs.
#
# And what `name` does: it reads its words as they say, a field at a time;
# a plan is what the words said, a deletion only of the one word beside
# `--delete`; the bookmark it sets points at what was asked — a revision,
# a change or a file the store holds — as private as asked or as it was;
# `--delete` is refused exactly where no bookmark has the name; and
# `--fields` says its header once.
import Base
import ./commands.bend as Main
import ./survey.bend as Sv
import ./folder.bend as Folder
import ./blamed_lemmas.bend as B
import ./anchor_lemmas.bend as AL
import ./string_lemmas.bend as S
import ./ident.bend as Id
import ./sort_lemmas.bend as SortL
import ./graph_lemmas.bend as GL
import ./show_lemmas.bend as ShowL
import ./bookmark.bend as Bm
import ./revision.bend as Rev
import ./composition_lemmas.bend as Comp

def mnone(m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{x}:
      Unit

def some_none(-x: String, e: {Some{x} == None{} : Maybe<&2, String>}) -> Empty:
  %e : {mnone(_) : Type}
  Unit{}

# A refusal chosen by a test that came out `None`: the test was false, and
# what it would otherwise have said is `None` too.
def pick_rest(c: Bool, -x: String, -m: Maybe<&2, String>, e: {Bool.pick(Maybe<&2, String>, c, Some{x}, m) == None{} : Maybe<&2, String>}) -> {m == None{} : Maybe<&2, String>}:
  match c:
    case True{}:
      Empty.absurd({m == None{} : Maybe<&2, String>}, some_none(x, e))
    case False{}:
      e

def pick_cond(c: Bool, -x: String, -m: Maybe<&2, String>, e: {Bool.pick(Maybe<&2, String>, c, Some{x}, m) == None{} : Maybe<&2, String>}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, some_none(x, e))
    case False{}:
      {==}

def or_false(a: Bool, -b: Bool, ea: {a == False{} : Bool}, eb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({Bool.or(True{}, b) == False{} : Bool}, S.true_false(ea))
    case False{}:
      eb

# No component `check_path` passes is `..`.
def dots(+x: String) -> Bool:
  Bool.or(String.eq(x, "."), String.eq(x, ".."))

def after_empty(+x: String, rest: List<&2, String>) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, dots(x), Some{"`.` and `..` are not components"}, Sv.component_fault(rest))

def components(cs: List<&2, String>, +e: {Sv.component_fault(cs) == None{} : Maybe<&2, String>}) -> {List.any(~&2, ~String, ~(c => String.eq(c, "..")), cs) == False{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case +x <> +rest:
      or_false(String.eq(x, ".."), List.any(~&2, ~String, ~(c => String.eq(c, "..")), rest),
        AL.or_false_r(String.eq(x, "."), String.eq(x, ".."),
          pick_cond(dots(x), "`.` and `..` are not components", Sv.component_fault(rest),
            pick_rest(String.is_empty(x), "it has an empty component", after_empty(x, rest), e))),
        components(rest,
          pick_rest(dots(x), "`.` and `..` are not components", Sv.component_fault(rest),
            pick_rest(String.is_empty(x), "it has an empty component", after_empty(x, rest), e))))

# The path rules, past the two a climbing name would meet.
def after_trailing(+p: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, List.any(~&2, ~Char, ~Folder.is_control, String.to_list(p)), Some{"it holds a control character"},
    Sv.normal_fault(Sv.component_fault(String.split(p, '/')), p))

# The last rule, normal form C, is asked only of a path the others passed.
def normal_none(f: Maybe<&2, String>, +p: String, e: {Sv.normal_fault(f, p) == None{} : Maybe<&2, String>}) -> {f == None{} : Maybe<&2, String>}:
  match f:
    case Some{b}:
      Empty.absurd({Some{b} == None{} : Maybe<&2, String>}, some_none(b, e))
    case None{}:
      {==}

def after_ends(+p: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, Bool.or(String.starts_with(p, " "), String.ends_with(p, " ")), Some{"it has leading or trailing space"}, after_trailing(p))

def after_root(+p: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.ends_with(p, "/"), Some{"it ends with `/`, and a path names a file rather than a directory"}, after_ends(p))

def after_first(+p: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.starts_with(p, "/"), Some{"it begins with `/`, and a path is relative to the repository root"}, after_root(p))

def path_parts(+p: String, +e: {Sv.path_check(p) == None{} : Maybe<&2, String>}) -> {Sv.component_fault(String.split(p, '/')) == None{} : Maybe<&2, String>}:
  normal_none(Sv.component_fault(String.split(p, '/')), p,
    pick_rest(List.any(~&2, ~Char, ~Folder.is_control, String.to_list(p)), "it holds a control character", Sv.normal_fault(Sv.component_fault(String.split(p, '/')), p),
      pick_rest(Bool.or(String.starts_with(p, " "), String.ends_with(p, " ")), "it has leading or trailing space", after_trailing(p),
        pick_rest(String.ends_with(p, "/"), "it ends with `/`, and a path names a file rather than a directory", after_ends(p),
          pick_rest(String.starts_with(p, "/"), "it begins with `/`, and a path is relative to the repository root", after_root(p),
            pick_rest(String.is_empty(p), "it is empty", after_first(p), e))))))

def path_rooted(+p: String, +e: {Sv.path_check(p) == None{} : Maybe<&2, String>}) -> {String.starts_with(p, "/") == False{} : Bool}:
  pick_cond(String.starts_with(p, "/"), "it begins with `/`, and a path is relative to the repository root", after_root(p),
    pick_rest(String.is_empty(p), "it is empty", after_first(p), e))

def path_stays(+p: String, +e: {Sv.path_check(p) == None{} : Maybe<&2, String>}) -> {Main.escapes(p) == False{} : Bool}:
  or_false(String.starts_with(p, "/"), List.any(~&2, ~String, ~(c => String.eq(c, "..")), String.split(p, '/')),
    path_rooted(p, e), components(String.split(p, '/'), path_parts(p, e)))

# A name `name` takes passes the path rules.
def usable_none(+n: String, fault: Maybe<&2, String>, e: {Main.name.usable.r(n, fault) == Done{Unit{}} : Result<&2, &2, Main.Refused, Unit>}) -> {fault == None{} : Maybe<&2, String>}:
  match fault:
    case Some{because}:
      Empty.absurd({Some{because} == None{} : Maybe<&2, String>}, B.fail_done(Unit, Main.Refused{1, "`" ++ n ++ "` cannot be a bookmark: " ++ because}, Unit{}, e))
    case None{}:
      {==}

def checked_pick(+n: String, c: Bool, -m: String, e: {Bool.pick(Result<&2, &2, Main.Refused, Unit>, c, Fail{Main.Refused{1, m}}, Main.name.usable.r(n, Main.name_fault(n))) == Done{Unit{}} : Result<&2, &2, Main.Refused, Unit>}) -> {Main.name_fault(n) == None{} : Maybe<&2, String>}:
  match c:
    case True{}:
      Empty.absurd({Main.name_fault(n) == None{} : Maybe<&2, String>}, B.fail_done(Unit, Main.Refused{1, m}, Unit{}, e))
    case False{}:
      usable_none(n, Main.name_fault(n), e)

def backslash(+n: String) -> Bool:
  List.any(~&2, ~Char, ~(c => Char.is_eq(c, '\\')), String.to_list(n))

def after_named(+n: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, backslash(n), Some{"it holds a backslash, which is a separator on some machines and a character on others; a bookmark that changed shape when its store was copied would be worse than one refused everywhere"}, Sv.path_check(n))

def stays(+n: String, e: {Main.name.checked.r(n) == Done{Unit{}} : Result<&2, &2, Main.Refused, Unit>}) -> {Main.escapes(n) == False{} : Bool}:
  path_stays(n,
    pick_rest(backslash(n), "it holds a backslash, which is a separator on some machines and a character on others; a bookmark that changed shape when its store was copied would be worse than one refused everywhere", Sv.path_check(n),
      pick_rest(String.is_empty(n), "it is empty, and a bookmark with no name is not a bookmark", after_named(n),
        checked_pick(n, Id.is_assigned(n), "`" ++ n ++ "` is spelled as an identifier, and a bookmark that is one would stop that identifier naming its own file; give it a name a person would say", e))))

# Its words
# ---------

# One word read: whatever it is, the fields read from the rest take it in.
def args_step(k: Main.NWord, +w: String, rest: List<&2, String>, +p: Bool, +a: Maybe<&2, Bool>, +d: Bool, +f: Bool, +sh: List<&2, String>, +r: List<&2, String>, ih: @p2: Bool -> @a2: Maybe<&2, Bool> -> @d2: Bool -> @f2: Bool -> @sh2: List<&2, String> -> @r2: List<&2, String> -> {Main.name.args(rest, Main.NameCmd{p2, a2, d2, f2, sh2, r2}) == Main.NameCmd{Main.nargs.pin(rest, p2), Main.nargs.axis(rest, a2), Main.nargs.delete(rest, d2), Main.nargs.fields(rest, f2), List.append(&2, String, sh2, Main.nargs.shaping(rest)), List.append(&2, String, r2, Main.nargs.words(rest))} : Main.NameCmd}) -> {Main.name.args(rest, Main.name.word(Main.NameCmd{p, a, d, f, sh, r}, k, w)) == Main.NameCmd{Main.nargs.pin(rest, Main.nargs.pin.of(k, p)), Main.nargs.axis(rest, Main.nargs.axis.of(k, a)), Main.nargs.delete(rest, Main.nargs.delete.of(k, d)), Main.nargs.fields(rest, Main.nargs.fields.of(k, f)), List.append(&2, String, sh, Main.nargs.shaping.of(k, w, Main.nargs.shaping(rest))), List.append(&2, String, r, Main.nargs.words.of(k, w, Main.nargs.words(rest)))} : Main.NameCmd}:
  match k:
    case Main.NWord.Revision{}:
      %SortL.app_assoc(String, sh, [w], Main.nargs.shaping(rest)) : {Main.name.args(rest, Main.NameCmd{True{}, a, d, f, List.append(&2, String, sh, [w]), r}) == Main.NameCmd{Main.nargs.pin(rest, True{}), Main.nargs.axis(rest, a), Main.nargs.delete(rest, d), Main.nargs.fields(rest, f), _, List.append(&2, String, r, Main.nargs.words(rest))} : Main.NameCmd}
      ih(True{}, a, d, f, List.append(&2, String, sh, [w]), r)
    case Main.NWord.Change{}:
      %SortL.app_assoc(String, sh, [w], Main.nargs.shaping(rest)) : {Main.name.args(rest, Main.NameCmd{False{}, a, d, f, List.append(&2, String, sh, [w]), r}) == Main.NameCmd{Main.nargs.pin(rest, False{}), Main.nargs.axis(rest, a), Main.nargs.delete(rest, d), Main.nargs.fields(rest, f), _, List.append(&2, String, r, Main.nargs.words(rest))} : Main.NameCmd}
      ih(False{}, a, d, f, List.append(&2, String, sh, [w]), r)
    case Main.NWord.Private{}:
      %SortL.app_assoc(String, sh, [w], Main.nargs.shaping(rest)) : {Main.name.args(rest, Main.NameCmd{p, Some{True{}}, d, f, List.append(&2, String, sh, [w]), r}) == Main.NameCmd{Main.nargs.pin(rest, p), Main.nargs.axis(rest, Some{True{}}), Main.nargs.delete(rest, d), Main.nargs.fields(rest, f), _, List.append(&2, String, r, Main.nargs.words(rest))} : Main.NameCmd}
      ih(p, Some{True{}}, d, f, List.append(&2, String, sh, [w]), r)
    case Main.NWord.Shared{}:
      %SortL.app_assoc(String, sh, [w], Main.nargs.shaping(rest)) : {Main.name.args(rest, Main.NameCmd{p, Some{False{}}, d, f, List.append(&2, String, sh, [w]), r}) == Main.NameCmd{Main.nargs.pin(rest, p), Main.nargs.axis(rest, Some{False{}}), Main.nargs.delete(rest, d), Main.nargs.fields(rest, f), _, List.append(&2, String, r, Main.nargs.words(rest))} : Main.NameCmd}
      ih(p, Some{False{}}, d, f, List.append(&2, String, sh, [w]), r)
    case Main.NWord.Delete{}:
      ih(p, a, True{}, f, sh, r)
    case Main.NWord.Fields{}:
      ih(p, a, d, True{}, sh, r)
    case Main.NWord.Other{}:
      %SortL.app_assoc(String, r, [w], Main.nargs.words(rest)) : {Main.name.args(rest, Main.NameCmd{p, a, d, f, sh, List.append(&2, String, r, [w])}) == Main.NameCmd{Main.nargs.pin(rest, p), Main.nargs.axis(rest, a), Main.nargs.delete(rest, d), Main.nargs.fields(rest, f), List.append(&2, String, sh, Main.nargs.shaping(rest)), _} : Main.NameCmd}
      ih(p, a, d, f, sh, List.append(&2, String, r, [w]))

def args_go(ws: List<&2, String>, +p: Bool, +a: Maybe<&2, Bool>, +d: Bool, +f: Bool, +sh: List<&2, String>, +r: List<&2, String>) -> {Main.name.args(ws, Main.NameCmd{p, a, d, f, sh, r}) == Main.NameCmd{Main.nargs.pin(ws, p), Main.nargs.axis(ws, a), Main.nargs.delete(ws, d), Main.nargs.fields(ws, f), List.append(&2, String, sh, Main.nargs.shaping(ws)), List.append(&2, String, r, Main.nargs.words(ws))} : Main.NameCmd}:
  match ws:
    case Nil{}:
      %Equal.sym(List<&2, String>, List.append(&2, String, sh, Nil{}), sh, SortL.lapp_nil(String, sh)) : {Main.NameCmd{p, a, d, f, sh, r} == Main.NameCmd{p, a, d, f, _, List.append(&2, String, r, Nil{})} : Main.NameCmd}
      %Equal.sym(List<&2, String>, List.append(&2, String, r, Nil{}), r, SortL.lapp_nil(String, r)) : {Main.NameCmd{p, a, d, f, sh, r} == Main.NameCmd{p, a, d, f, sh, _} : Main.NameCmd}
      {==}
    case +w <> +rest:
      args_step(Main.nword(w), w, rest, p, a, d, f, sh, r, p2 => a2 => d2 => f2 => sh2 => r2 => args_go(rest, p2, a2, d2, f2, sh2, r2))

# `name` reads its words as they say.
def args_said(+ws: List<&2, String>) -> {Main.name.args(ws, Main.NameCmd{False{}, None{}, False{}, False{}, Nil{}, Nil{}}) == Main.nargs.said(ws) : Main.NameCmd}:
  args_go(ws, False{}, None{}, False{}, False{}, Nil{}, Nil{})

# What it plans
# -------------

def same_refl(b: Bool) -> {Main.nplan.same(b, b) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def axis_refl(a: Maybe<&2, Bool>) -> {Main.nplan.axis(a, a) == True{} : Bool}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      same_refl(x)

def words_refl(xs: List<&2, String>) -> {Main.nplan.words(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      %Equal.sym(Bool, String.eq(x, x), True{}, S.eq_refl(x)) : {Bool.and(_, Main.nplan.words(rest, rest)) == True{} : Bool}
      words_refl(rest)

def early_ok(f: Bool, x: Bool) -> {Bool.or(Bool.not(Bool.and(f, x)), f) == True{} : Bool}:
  match f x:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} _:
      {==}

def unpinned(pin: Bool) -> {Bool.not(Bool.and(pin, False{})) == True{} : Bool}:
  match pin:
    case True{}:
      {==}
    case False{}:
      {==}

def set_meant(-sh: List<&2, String>, +n: String, +t: String, +path: Maybe<&2, String>, +pin: Bool, +axis: Maybe<&2, Bool>, +f: Bool, +x: Bool, hp: {Bool.not(Bool.and(pin, Maybe.is_some(&2, String, path))) == True{} : Bool}) -> {Main.name.plan.meant(Main.NameCmd{pin, axis, False{}, f, sh, n <> t <> Main.nplan.path(path)}, Main.NamePlan.Set{n, t, path, pin, axis, f, Bool.and(f, x)}) == True{} : Bool}:
  AL.and_intro(Main.nplan.words(n <> t <> Main.nplan.path(path), n <> t <> Main.nplan.path(path)), Bool.and(Main.nplan.same(pin, pin), Bool.and(Main.nplan.axis(axis, axis), Bool.and(Main.nplan.same(f, f), Bool.and(Bool.not(Bool.and(pin, Maybe.is_some(&2, String, path))), Bool.or(Bool.not(Bool.and(f, x)), f))))), words_refl(n <> t <> Main.nplan.path(path)),
    AL.and_intro(Main.nplan.same(pin, pin), Bool.and(Main.nplan.axis(axis, axis), Bool.and(Main.nplan.same(f, f), Bool.and(Bool.not(Bool.and(pin, Maybe.is_some(&2, String, path))), Bool.or(Bool.not(Bool.and(f, x)), f)))), same_refl(pin),
      AL.and_intro(Main.nplan.axis(axis, axis), Bool.and(Main.nplan.same(f, f), Bool.and(Bool.not(Bool.and(pin, Maybe.is_some(&2, String, path))), Bool.or(Bool.not(Bool.and(f, x)), f))), axis_refl(axis),
        AL.and_intro(Main.nplan.same(f, f), Bool.and(Bool.not(Bool.and(pin, Maybe.is_some(&2, String, path))), Bool.or(Bool.not(Bool.and(f, x)), f)), same_refl(f),
          AL.and_intro(Bool.not(Bool.and(pin, Maybe.is_some(&2, String, path))), Bool.or(Bool.not(Bool.and(f, x)), f), hp, early_ok(f, x))))))

def done_plan(-a: Main.NamePlan, -b: Main.NamePlan, h: {Done{a} == Done{b} : Result<&2, &2, Main.Refused, Main.NamePlan>}) -> {a == b : Main.NamePlan}:
  B.done_eq(Main.NamePlan, a, b, h)

# A plan is what its words said.
def plan_meant(c: Main.NameCmd, +p: Main.NamePlan, e: {Main.name.plan.r(c) == Done{p} : Result<&2, &2, Main.Refused, Main.NamePlan>}) -> {Main.name.plan.meant(c, p) == True{} : Bool}:
  match c:
    case Main.NameCmd{True{}, +axis, True{}, +f, s1 <> more, rest}:
      Empty.absurd({Main.name.plan.meant(Main.NameCmd{True{}, axis, True{}, f, s1 <> more, rest}, p) == True{} : Bool}, B.refuse(Main.NamePlan, Main.name.plan.r(Main.NameCmd{True{}, axis, True{}, f, s1 <> more, rest}), p, {==}, e))
    case Main.NameCmd{False{}, +axis, True{}, +f, s1 <> more, rest}:
      Empty.absurd({Main.name.plan.meant(Main.NameCmd{False{}, axis, True{}, f, s1 <> more, rest}, p) == True{} : Bool}, B.refuse(Main.NamePlan, Main.name.plan.r(Main.NameCmd{False{}, axis, True{}, f, s1 <> more, rest}), p, {==}, e))
    case Main.NameCmd{True{}, +axis, True{}, +f, Nil{}, Nil{}}:
      Empty.absurd({Main.name.plan.meant(Main.NameCmd{True{}, axis, True{}, f, Nil{}, Nil{}}, p) == True{} : Bool}, B.refuse(Main.NamePlan, Main.name.plan.r(Main.NameCmd{True{}, axis, True{}, f, Nil{}, Nil{}}), p, {==}, e))
    case Main.NameCmd{False{}, +axis, True{}, +f, Nil{}, Nil{}}:
      Empty.absurd({Main.name.plan.meant(Main.NameCmd{False{}, axis, True{}, f, Nil{}, Nil{}}, p) == True{} : Bool}, B.refuse(Main.NamePlan, Main.name.plan.r(Main.NameCmd{False{}, axis, True{}, f, Nil{}, Nil{}}), p, {==}, e))
    case Main.NameCmd{True{}, +axis, True{}, +f, Nil{}, +n <> x <> more}:
      Empty.absurd({Main.name.plan.meant(Main.NameCmd{True{}, axis, True{}, f, Nil{}, n <> x <> more}, p) == True{} : Bool}, B.refuse(Main.NamePlan, Main.name.plan.r(Main.NameCmd{True{}, axis, True{}, f, Nil{}, n <> x <> more}), p, {==}, e))
    case Main.NameCmd{False{}, +axis, True{}, +f, Nil{}, +n <> x <> more}:
      Empty.absurd({Main.name.plan.meant(Main.NameCmd{False{}, axis, True{}, f, Nil{}, n <> x <> more}, p) == True{} : Bool}, B.refuse(Main.NamePlan, Main.name.plan.r(Main.NameCmd{False{}, axis, True{}, f, Nil{}, n <> x <> more}), p, {==}, e))
    case Main.NameCmd{True{}, +axis, True{}, +f, Nil{}, +n <> Nil{}}:
      %done_plan(Main.NamePlan.Delete{n, f}, p, e) : {Main.name.plan.meant(Main.NameCmd{True{}, axis, True{}, f, Nil{}, n <> Nil{}}, _) == True{} : Bool}
      AL.and_intro(Main.nplan.words([n], [n]), Main.nplan.same(f, f), words_refl([n]), same_refl(f))
    case Main.NameCmd{False{}, +axis, True{}, +f, Nil{}, +n <> Nil{}}:
      %done_plan(Main.NamePlan.Delete{n, f}, p, e) : {Main.name.plan.meant(Main.NameCmd{False{}, axis, True{}, f, Nil{}, n <> Nil{}}, _) == True{} : Bool}
      AL.and_intro(Main.nplan.words([n], [n]), Main.nplan.same(f, f), words_refl([n]), same_refl(f))
    case Main.NameCmd{True{}, +axis, False{}, +f, sh, Nil{}}:
      Empty.absurd({Main.name.plan.meant(Main.NameCmd{True{}, axis, False{}, f, sh, Nil{}}, p) == True{} : Bool}, B.refuse(Main.NamePlan, Main.name.plan.r(Main.NameCmd{True{}, axis, False{}, f, sh, Nil{}}), p, {==}, e))
    case Main.NameCmd{False{}, +axis, False{}, +f, sh, Nil{}}:
      Empty.absurd({Main.name.plan.meant(Main.NameCmd{False{}, axis, False{}, f, sh, Nil{}}, p) == True{} : Bool}, B.refuse(Main.NamePlan, Main.name.plan.r(Main.NameCmd{False{}, axis, False{}, f, sh, Nil{}}), p, {==}, e))
    case Main.NameCmd{True{}, +axis, False{}, +f, sh, +n <> Nil{}}:
      Empty.absurd({Main.name.plan.meant(Main.NameCmd{True{}, axis, False{}, f, sh, n <> Nil{}}, p) == True{} : Bool}, B.refuse(Main.NamePlan, Main.name.plan.r(Main.NameCmd{True{}, axis, False{}, f, sh, n <> Nil{}}), p, {==}, e))
    case Main.NameCmd{False{}, +axis, False{}, +f, sh, +n <> Nil{}}:
      Empty.absurd({Main.name.plan.meant(Main.NameCmd{False{}, axis, False{}, f, sh, n <> Nil{}}, p) == True{} : Bool}, B.refuse(Main.NamePlan, Main.name.plan.r(Main.NameCmd{False{}, axis, False{}, f, sh, n <> Nil{}}), p, {==}, e))
    case Main.NameCmd{True{}, +axis, False{}, +f, sh, +n <> +t <> +q <> x <> more}:
      Empty.absurd({Main.name.plan.meant(Main.NameCmd{True{}, axis, False{}, f, sh, n <> t <> q <> x <> more}, p) == True{} : Bool}, B.refuse(Main.NamePlan, Main.name.plan.r(Main.NameCmd{True{}, axis, False{}, f, sh, n <> t <> q <> x <> more}), p, {==}, e))
    case Main.NameCmd{False{}, +axis, False{}, +f, sh, +n <> +t <> +q <> x <> more}:
      Empty.absurd({Main.name.plan.meant(Main.NameCmd{False{}, axis, False{}, f, sh, n <> t <> q <> x <> more}, p) == True{} : Bool}, B.refuse(Main.NamePlan, Main.name.plan.r(Main.NameCmd{False{}, axis, False{}, f, sh, n <> t <> q <> x <> more}), p, {==}, e))
    case Main.NameCmd{True{}, +axis, False{}, +f, sh, +n <> +t <> +q <> Nil{}}:
      Empty.absurd({Main.name.plan.meant(Main.NameCmd{True{}, axis, False{}, f, sh, n <> t <> q <> Nil{}}, p) == True{} : Bool}, B.refuse(Main.NamePlan, Main.name.plan.r(Main.NameCmd{True{}, axis, False{}, f, sh, n <> t <> q <> Nil{}}), p, {==}, e))
    case Main.NameCmd{False{}, +axis, False{}, +f, sh, +n <> +t <> +q <> Nil{}}:
      %done_plan(Main.NamePlan.Set{n, t, Some{q}, False{}, axis, f, Bool.and(f, Bool.and(Bool.not(String.is_empty(t)), Bool.not(String.eq(q, "file:"))))}, p, e) : {Main.name.plan.meant(Main.NameCmd{False{}, axis, False{}, f, sh, n <> t <> q <> Nil{}}, _) == True{} : Bool}
      set_meant(sh, n, t, Some{q}, False{}, axis, f, Bool.and(Bool.not(String.is_empty(t)), Bool.not(String.eq(q, "file:"))), {==})
    case Main.NameCmd{True{}, +axis, False{}, +f, sh, +n <> +t <> Nil{}}:
      %done_plan(Main.NamePlan.Set{n, t, None{}, True{}, axis, f, Bool.and(f, Bool.not(String.is_empty(t)))}, p, e) : {Main.name.plan.meant(Main.NameCmd{True{}, axis, False{}, f, sh, n <> t <> Nil{}}, _) == True{} : Bool}
      set_meant(sh, n, t, None{}, True{}, axis, f, Bool.not(String.is_empty(t)), unpinned(True{}))
    case Main.NameCmd{False{}, +axis, False{}, +f, sh, +n <> +t <> Nil{}}:
      %done_plan(Main.NamePlan.Set{n, t, None{}, False{}, axis, f, Bool.and(f, Bool.not(String.is_empty(t)))}, p, e) : {Main.name.plan.meant(Main.NameCmd{False{}, axis, False{}, f, sh, n <> t <> Nil{}}, _) == True{} : Bool}
      set_meant(sh, n, t, None{}, False{}, axis, f, Bool.not(String.is_empty(t)), unpinned(False{}))

# Where it points
# ---------------

# A bookmark moved keeps the privacy of the one it replaces: the first of
# that name, which is the one `--delete` would find.
def kept_at(b: Bool, +m: String, +t: Bm.Target, +p: Bool, +rest: List<&2, Bm.Bookmark>, +n: String, ih: {Main.name.kept.of(Main.found_of(rest, n), Main.private_of(rest, n)) == True{} : Bool}) -> {Main.name.kept.of(Bool.pick(Maybe<&2, Bm.Bookmark>, b, Some{Bm.Bookmark{m, t, p}}, Main.found_of(rest, n)), Bool.pick(Bool, b, p, Main.private_of(rest, n))) == True{} : Bool}:
  match b:
    case True{}:
      same_refl(p)
    case False{}:
      ih

def kept_found(bs: List<&2, Bm.Bookmark>, +n: String) -> {Main.name.kept.of(Main.found_of(bs, n), Main.private_of(bs, n)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Bm.Bookmark{+m, +t, +p} <> +rest:
      kept_at(String.eq(m, n), m, t, p, rest, n, kept_found(rest, n))

def kept_ok(+bs: List<&2, Bm.Bookmark>, +n: String, axis: Maybe<&2, Bool>) -> {Main.name.kept(bs, n, axis, Maybe.default(&2, Bool, axis, Main.private_of(bs, n))) == True{} : Bool}:
  match axis:
    case Some{x}:
      same_refl(x)
    case None{}:
      kept_found(bs, n)

# A change the store's revisions carry is among its changes.
def push_has.of(b: Bool, +c: String, +rest: List<&2, String>, eb: {Rev.member(rest, c) == b : Bool}) -> {Rev.member(Rev.keep(Bool.not(b), c, rest), c) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      GL.member_head(c, rest)

def push_keeps(b: Bool, +c: String, +rest: List<&2, String>, +x: String, m: {Rev.member(rest, x) == True{} : Bool}) -> {Rev.member(Rev.keep(b, c, rest), x) == True{} : Bool}:
  match b:
    case True{}:
      GL.member_tail(c, rest, x, m)
    case False{}:
      m

def find_change_at(b: Bool, +i: String, +change: String, +parents: List<&2, String>, +supersedes: List<&2, String>, +author: String, +when: String, +revised_by: Maybe<&2, String>, +revised: Maybe<&2, String>, +facts: List<&2, Rev.Header>, +message: String, +rest: List<&2, Main.Full>, +x: String, +g: Main.Full, e: {Bool.pick(Maybe<&2, Main.Full>, b, Some{Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}}, Main.find(rest, x)) == Some{g} : Maybe<&2, Main.Full>}, ih: {Main.find(rest, x) == Some{g} : Maybe<&2, Main.Full>} -> {Rev.member(Main.changes(rest), Main.change_of(g)) == True{} : Bool}) -> {Rev.member(Main.changes.push(change, Main.changes(rest)), Main.change_of(g)) == True{} : Bool}:
  match b:
    case True{}:
      +d = B.some_eq_f(Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}, g, e)
      %d : {Rev.member(Main.changes.push(change, Main.changes(rest)), Main.change_of(_)) == True{} : Bool}
      push_has.of(Rev.member(Main.changes(rest), change), change, Main.changes(rest), {==})
    case False{}:
      push_keeps(Bool.not(Rev.member(Main.changes(rest), change)), change, Main.changes(rest), Main.change_of(g), ih(e))

def find_change(fs: List<&2, Main.Full>, +x: String, +g: Main.Full, e: {Main.find(fs, x) == Some{g} : Maybe<&2, Main.Full>}) -> {Rev.member(Main.changes(fs), Main.change_of(g)) == True{} : Bool}:
  match fs:
    case Nil{}:
      Empty.absurd({Rev.member(Main.changes(Nil{}), Main.change_of(g)) == True{} : Bool}, (%e : {B.mdisc_f(_) : Type} Unit{}))
    case Main.Full{+i, +change, +parents, +supersedes, +author, +when, +revised_by, +revised, +facts, +message} <> +rest:
      find_change_at(String.eq(i, x), i, change, parents, supersedes, author, when, revised_by, revised, facts, message, rest, x, g, e, h => find_change(rest, x, g, h))

def found_change(+fs: List<&2, Main.Full>, +id: String, m: Maybe<&2, Main.Full>, +em: {Main.find(fs, id) == m : Maybe<&2, Main.Full>}, +f: Main.Full, e: {Main.resolved.found.r(id, m) == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}) -> {Rev.member(Main.changes(fs), Main.change_of(f)) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Rev.member(Main.changes(fs), Main.change_of(f)) == True{} : Bool}, B.refuse(Main.Full, Main.resolved.found.r(id, None{}), f, {==}, e))
    case Some{+g}:
      +d = B.done_eq(Main.Full, g, f, e)
      %d : {Rev.member(Main.changes(fs), Main.change_of(_)) == True{} : Bool}
      find_change(fs, id, g, em)

def resolved_of_change(+fs: List<&2, Main.Full>, r: Result<&2, &2, String, String>, +f: Main.Full, e: {Main.resolved.of.r(fs, r) == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}) -> {Rev.member(Main.changes(fs), Main.change_of(f)) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Rev.member(Main.changes(fs), Main.change_of(f)) == True{} : Bool}, B.fail_done(Main.Full, Main.Refused{1, x}, f, e))
    case Done{+id}:
      found_change(fs, id, Main.find(fs, id), {==}, f, e)

# A target resolves to a revision carrying one of the store's changes.
def resolved_change(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +target: String, +f: Main.Full, e: {Main.resolved.r(fs, bs, target) == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}) -> {Rev.member(Main.changes(fs), Main.change_of(f)) == True{} : Bool}:
  resolved_of_change(fs, Main.resolve(fs, bs, target), f, e)

# `name` refuses an empty target before resolving it, and otherwise
# resolves it as every command does.
def name_resolved(b: Bool, -r: Result<&2, &2, Main.Refused, Main.Full>, -f: Main.Full, e: {Bool.pick(Result<&2, &2, Main.Refused, Main.Full>, b, Fail{Main.Refused{2, "a target cannot be empty"}}, r) == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}) -> {r == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}:
  match b:
    case True{}:
      Empty.absurd({r == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}, B.fail_done(Main.Full, Main.Refused{2, "a target cannot be empty"}, f, e))
    case False{}:
      e

# A file some revision the store holds has in its tree.
def somewhere_at(held: List<&2, String>, +fs: List<&2, Main.Full>, +x: String, +i: String, m: {Rev.member(held, i) == True{} : Bool}, +h: {Main.tree.holds.r(Main.tree.r(fs, i), x) == True{} : Bool}) -> {Main.name.somewhere(held, fs, x) == True{} : Bool}:
  match held:
    case Nil{}:
      Empty.absurd({Main.name.somewhere(Nil{}, fs, x) == True{} : Bool}, S.false_true(m))
    case +y <> +rest:
      GL.member_cons({Main.name.somewhere(y <> rest, fs, x) == True{} : Bool}, y, rest, i, m,
        yi => (%Equal.sym(String, y, i, yi) : {Bool.or(Main.tree.holds.r(Main.tree.r(fs, _), x), Main.name.somewhere(rest, fs, x)) == True{} : Bool}
          AL.or_left(Main.tree.holds.r(Main.tree.r(fs, i), x), Main.name.somewhere(rest, fs, x), h)),
        mr => AL.or_right(Main.tree.holds.r(Main.tree.r(fs, y), x), Main.name.somewhere(rest, fs, x), somewhere_at(rest, fs, x, i, mr, h)))

def target_eq(-a: Bm.Target, -b: Bm.Target, h: {Done{a} == Done{b} : Result<&2, &2, Main.Refused, Bm.Target>}) -> {a == b : Bm.Target}:
  B.done_eq(Bm.Target, a, b, h)

def file_aimed(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +hf: {Rev.member(Main.ids(fs), id) == True{} : Bool}, +p: String, +pin: Bool, r: Result<&2, &2, Main.Refused, String>, +er: {Main.show.file.r(fs, bs, id, p) == r : Result<&2, &2, Main.Refused, String>}, +t: Bm.Target, e: {Result.map(&2, &2, Main.Refused, String, Bm.Target, file => Bm.Target.File{file}, r) == Done{t} : Result<&2, &2, Main.Refused, Bm.Target>}) -> {Main.name.aimed(fs, Some{p}, pin, t) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.name.aimed(fs, Some{p}, pin, t) == True{} : Bool}, B.fail_done(Bm.Target, x, t, e))
    case Done{+x}:
      %target_eq(Bm.Target.File{x}, t, e) : {Main.name.aimed(fs, Some{p}, pin, _) == True{} : Bool}
      somewhere_at(Main.ids(fs), fs, x, id, hf, ShowL.file_ok(fs, bs, id, p, x, er))

# The target is what was asked for, at the revision named.
def aimed_ok(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +f: Main.Full, path: Maybe<&2, String>, pin: Bool, +hf: {Rev.member(Main.ids(fs), Main.id_of(f)) == True{} : Bool}, +hc: {Rev.member(Main.changes(fs), Main.change_of(f)) == True{} : Bool}, +t: Bm.Target, e: {Main.name.target.r(fs, bs, f, path, pin) == Done{t} : Result<&2, &2, Main.Refused, Bm.Target>}) -> {Main.name.aimed(fs, path, pin, t) == True{} : Bool}:
  match path pin:
    case Some{+p} True{}:
      file_aimed(fs, bs, Main.id_of(f), hf, p, True{}, Main.show.file.r(fs, bs, Main.id_of(f), p), {==}, t, e)
    case Some{+p} False{}:
      file_aimed(fs, bs, Main.id_of(f), hf, p, False{}, Main.show.file.r(fs, bs, Main.id_of(f), p), {==}, t, e)
    case None{} True{}:
      %target_eq(Bm.Target.Revision{Main.id_of(f)}, t, e) : {Main.name.aimed(fs, None{}, True{}, _) == True{} : Bool}
      hf
    case None{} False{}:
      %target_eq(Bm.Target.Change{Main.change_of(f)}, t, e) : {Main.name.aimed(fs, None{}, False{}, _) == True{} : Bool}
      hc

def bm_eq(-a: Bm.Bookmark, -b: Bm.Bookmark, h: {Done{a} == Done{b} : Result<&2, &2, Main.Refused, Bm.Bookmark>}) -> {a == b : Bm.Bookmark}:
  B.done_eq(Bm.Bookmark, a, b, h)

def checked_unit(u: Unit, -n: String, e: {Main.name.checked.r(n) == Done{u} : Result<&2, &2, Main.Refused, Unit>}) -> {Main.name.checked.r(n) == Done{Unit{}} : Result<&2, &2, Main.Refused, Unit>}:
  match u:
    case Unit{}:
      e

def points3(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +n: String, path: Maybe<&2, String>, pin: Bool, +axis: Maybe<&2, Bool>, +t: Bm.Target, +ht: {Main.name.aimed(fs, path, pin, t) == True{} : Bool}, r: Result<&2, &2, Main.Refused, Unit>, +er: {Main.name.checked.r(n) == r : Result<&2, &2, Main.Refused, Unit>}, +b: Bm.Bookmark, e: {Result.bind(&2, &2, Main.Refused, Unit, Bm.Bookmark, r, u => Done{Bm.Bookmark{n, t, Maybe.default(&2, Bool, axis, Main.private_of(bs, n))}}) == Done{b} : Result<&2, &2, Main.Refused, Bm.Bookmark>}) -> {Main.name.points(fs, bs, n, path, pin, axis, b) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.name.points(fs, bs, n, path, pin, axis, b) == True{} : Bool}, B.fail_done(Bm.Bookmark, x, b, e))
    case Done{u}:
      %bm_eq(Bm.Bookmark{n, t, Maybe.default(&2, Bool, axis, Main.private_of(bs, n))}, b, e) : {Main.name.points(fs, bs, n, path, pin, axis, _) == True{} : Bool}
      %Equal.sym(Bool, String.eq(n, n), True{}, S.eq_refl(n)) : {Bool.and(_, Bool.and(Bool.not(Main.escapes(n)), Bool.and(Main.name.aimed(fs, path, pin, t), Main.name.kept(bs, n, axis, Maybe.default(&2, Bool, axis, Main.private_of(bs, n)))))) == True{} : Bool}
      AL.and_intro(Bool.not(Main.escapes(n)), Bool.and(Main.name.aimed(fs, path, pin, t), Main.name.kept(bs, n, axis, Maybe.default(&2, Bool, axis, Main.private_of(bs, n)))),
        AL.not_true(Main.escapes(n), stays(n, checked_unit(u, n, er))),
        AL.and_intro(Main.name.aimed(fs, path, pin, t), Main.name.kept(bs, n, axis, Maybe.default(&2, Bool, axis, Main.private_of(bs, n))), ht, kept_ok(bs, n, axis)))

def points2(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +n: String, +f: Main.Full, +path: Maybe<&2, String>, +pin: Bool, +axis: Maybe<&2, Bool>, +hf: {Rev.member(Main.ids(fs), Main.id_of(f)) == True{} : Bool}, +hc: {Rev.member(Main.changes(fs), Main.change_of(f)) == True{} : Bool}, r: Result<&2, &2, Main.Refused, Bm.Target>, +er: {Main.name.target.r(fs, bs, f, path, pin) == r : Result<&2, &2, Main.Refused, Bm.Target>}, +b: Bm.Bookmark, e: {Result.bind(&2, &2, Main.Refused, Bm.Target, Bm.Bookmark, r, t => Result.bind(&2, &2, Main.Refused, Unit, Bm.Bookmark, Main.name.checked.r(n), u => Done{Bm.Bookmark{n, t, Maybe.default(&2, Bool, axis, Main.private_of(bs, n))}})) == Done{b} : Result<&2, &2, Main.Refused, Bm.Bookmark>}) -> {Main.name.points(fs, bs, n, path, pin, axis, b) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.name.points(fs, bs, n, path, pin, axis, b) == True{} : Bool}, B.fail_done(Bm.Bookmark, x, b, e))
    case Done{+t}:
      points3(fs, bs, n, path, pin, axis, t, aimed_ok(fs, bs, f, path, pin, hf, hc, t, er), Main.name.checked.r(n), {==}, b, e)

def points1(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +n: String, +sp: String, +path: Maybe<&2, String>, +pin: Bool, +axis: Maybe<&2, Bool>, r: Result<&2, &2, Main.Refused, Main.Full>, +er: {Main.name.resolved.r(fs, bs, sp) == r : Result<&2, &2, Main.Refused, Main.Full>}, +b: Bm.Bookmark, e: {Result.bind(&2, &2, Main.Refused, Main.Full, Bm.Bookmark, r, f => Result.bind(&2, &2, Main.Refused, Bm.Target, Bm.Bookmark, Main.name.target.r(fs, bs, f, path, pin), t => Result.bind(&2, &2, Main.Refused, Unit, Bm.Bookmark, Main.name.checked.r(n), u => Done{Bm.Bookmark{n, t, Maybe.default(&2, Bool, axis, Main.private_of(bs, n))}}))) == Done{b} : Result<&2, &2, Main.Refused, Bm.Bookmark>}) -> {Main.name.points(fs, bs, n, path, pin, axis, b) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.name.points(fs, bs, n, path, pin, axis, b) == True{} : Bool}, B.fail_done(Bm.Bookmark, x, b, e))
    case Done{+f}:
      +held = name_resolved(String.is_empty(sp), Main.resolved.r(fs, bs, sp), f, er)
      points2(fs, bs, n, f, path, pin, axis, B.resolved_mem(fs, bs, sp, f, held), resolved_change(fs, bs, sp, f, held), Main.name.target.r(fs, bs, f, path, pin), {==}, b, e)

# The bookmark `name` sets is named as asked, stays under `names/`, points
# where it was asked to, and is as private as asked or as it was.
def points_ok(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +n: String, +sp: String, +path: Maybe<&2, String>, +pin: Bool, +axis: Maybe<&2, Bool>, +b: Bm.Bookmark, e: {Main.name.stated.r(fs, bs, n, sp, path, pin, axis) == Done{b} : Result<&2, &2, Main.Refused, Bm.Bookmark>}) -> {Main.name.points(fs, bs, n, path, pin, axis, b) == True{} : Bool}:
  points1(fs, bs, n, sp, path, pin, axis, Main.name.resolved.r(fs, bs, sp), {==}, b, e)

# What it deletes
# ---------------

def same_self(+b: Bm.Bookmark) -> {Main.name.same(b, b) == True{} : Bool}:
  match b:
    case Bm.Bookmark{+m, +s, +p}:
      AL.and_intro(String.eq(m, m), Bool.and(String.eq(Bm.show_target(s), Bm.show_target(s)), Main.nplan.same(p, p)), S.eq_refl(m),
        AL.and_intro(String.eq(Bm.show_target(s), Bm.show_target(s)), Main.nplan.same(p, p), S.eq_refl(Bm.show_target(s)), same_refl(p)))

def gone_skip(+b: Bm.Bookmark, +rest: List<&2, Bm.Bookmark>, +n: String, r: Result<&2, &2, Main.Refused, Bm.Bookmark>, eb: {String.eq(Bm.name_of(b), n) == False{} : Bool}, +h: {Main.name.gone(rest, n, r) == True{} : Bool}) -> {Main.name.gone(b <> rest, n, r) == True{} : Bool}:
  match r:
    case Fail{x}:
      %Equal.sym(Bool, String.eq(Bm.name_of(b), n), False{}, eb) : {Bool.not(Bool.or(_, Main.name.any(rest, n))) == True{} : Bool}
      h
    case Done{+c}:
      AL.and_intro(String.eq(Bm.name_of(c), n), Bool.or(Main.name.same(b, c), Main.name.holds(rest, c)), Comp.and_left(String.eq(Bm.name_of(c), n), Main.name.holds(rest, c), h),
        AL.or_right(Main.name.same(b, c), Main.name.holds(rest, c), Comp.and_right(String.eq(Bm.name_of(c), n), Main.name.holds(rest, c), h)))

def gone_at(c: Bool, +b: Bm.Bookmark, +rest: List<&2, Bm.Bookmark>, +n: String, ec: {String.eq(Bm.name_of(b), n) == c : Bool}, ih: {Main.name.gone(rest, n, Main.name.present.r(n, Main.found_of(rest, n))) == True{} : Bool}) -> {Main.name.gone(b <> rest, n, Main.name.present.r(n, Bool.pick(Maybe<&2, Bm.Bookmark>, c, Some{b}, Main.found_of(rest, n)))) == True{} : Bool}:
  match c:
    case True{}:
      AL.and_intro(String.eq(Bm.name_of(b), n), Bool.or(Main.name.same(b, b), Main.name.holds(rest, b)), ec, AL.or_left(Main.name.same(b, b), Main.name.holds(rest, b), same_self(b)))
    case False{}:
      gone_skip(b, rest, n, Main.name.present.r(n, Main.found_of(rest, n)), ec, ih)

# `--delete` is refused exactly where there is no bookmark of that name,
# and otherwise finds one the store holds under it.
def found_gone(bs: List<&2, Bm.Bookmark>, +n: String) -> {Main.name.gone(bs, n, Main.name.present.r(n, Main.found_of(bs, n))) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      gone_at(String.eq(Bm.name_of(b), n), b, rest, n, {==}, found_gone(rest, n))

# What it says
# ------------

# Asked for `--fields`, a bookmark set says so once: the header before the
# store was opened or after it was written, never both, and `name` with it.
def said_fields(+n: String, b: Bm.Bookmark, early: Bool, s: Bool) -> {List.append(&2, String, Main.name.head(early), Main.name.said.lines(n, b, True{}, early, s)) == [Main.WROTE(), "name " ++ n] : List<&2, String>}:
  match early:
    case True{}:
      {==}
    case False{}:
      {==}
