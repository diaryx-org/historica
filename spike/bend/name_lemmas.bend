# What `name` writes to. A bookmark's file is its name under `names/`, so a
# name it takes that began `/` or climbed out with `..` would be a name
# choosing where in the store — or out of it — its file goes. Every name
# `name` takes is refused neither by `check_name` nor by the path rules it
# reads, so it is never absolute and never climbs.
import Base
import ./main.bend as Main
import ./survey.bend as Sv
import ./folder.bend as Folder
import ./blamed_lemmas.bend as B
import ./anchor_lemmas.bend as AL
import ./string_lemmas.bend as S
import ./ident.bend as Id

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
