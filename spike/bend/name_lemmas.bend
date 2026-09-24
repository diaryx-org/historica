# What `name` writes to. A bookmark's file is its name under `names/`, so a
# name it takes that began `/` or climbed out with `..` would be a name
# choosing where in the store — or out of it — its file goes. Every name
# `name` takes is refused neither by `check_name` nor by the path rules it
# reads, so it is never absolute and never climbs.
import Base
import ./commands.bend as Main
import ./survey.bend as Sv
import ./folder.bend as Folder
import ./blamed_lemmas.bend as B
import ./anchor_lemmas.bend as AL
import ./string_lemmas.bend as S
import ./ident.bend as Id
import ./sort_lemmas.bend as SortL

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
    Sv.component_fault(String.split(p, '/')))

def after_ends(+p: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, Bool.or(String.starts_with(p, " "), String.ends_with(p, " ")), Some{"it has leading or trailing space"}, after_trailing(p))

def after_root(+p: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.ends_with(p, "/"), Some{"it ends with `/`, and a path names a file rather than a directory"}, after_ends(p))

def after_first(+p: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.starts_with(p, "/"), Some{"it begins with `/`, and a path is relative to the repository root"}, after_root(p))

def path_parts(+p: String, +e: {Sv.path_check(p) == None{} : Maybe<&2, String>}) -> {Sv.component_fault(String.split(p, '/')) == None{} : Maybe<&2, String>}:
  pick_rest(List.any(~&2, ~Char, ~Folder.is_control, String.to_list(p)), "it holds a control character", Sv.component_fault(String.split(p, '/')),
    pick_rest(Bool.or(String.starts_with(p, " "), String.ends_with(p, " ")), "it has leading or trailing space", after_trailing(p),
      pick_rest(String.ends_with(p, "/"), "it ends with `/`, and a path names a file rather than a directory", after_ends(p),
        pick_rest(String.starts_with(p, "/"), "it begins with `/`, and a path is relative to the repository root", after_root(p),
          pick_rest(String.is_empty(p), "it is empty", after_first(p), e)))))

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
