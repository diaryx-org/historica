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
import ./chain_lemmas.bend as ChainL

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

# What `LAWS.name_reads_its_words` says of the words, a list fact at a
# time: the `--revision` and `--change` among them, the `--private` and
# `--shared`, the four that shape a target, and those that are none of the
# six flags.
def nw.rc(ws: List<&2, String>) -> List<&2, String>:
  List.filter(~String, ~(w => Rev.member(["--revision", "--change"], w)), ws)

def nw.ps(ws: List<&2, String>) -> List<&2, String>:
  List.filter(~String, ~(w => Rev.member(["--private", "--shared"], w)), ws)

def nw.shaping(ws: List<&2, String>) -> List<&2, String>:
  List.filter(~String, ~(w => Rev.member(["--revision", "--change", "--private", "--shared"], w)), ws)

def nw.others(ws: List<&2, String>) -> List<&2, String>:
  List.filter(~String, ~(w => Bool.not(Rev.member(["--revision", "--change", "--private", "--shared", "--delete", "--fields"], w))), ws)

# After words whose last `--revision` or `--change` is `m`, from a pin `p`;
# and likewise for `--private` and `--shared`.
def nw.pin(m: Maybe<&2, String>, p: Bool) -> Bool:
  match m:
    case None{}:
      p
    case Some{x}:
      String.eq(x, "--revision")

def nw.axis(m: Maybe<&2, String>, a: Maybe<&2, Bool>) -> Maybe<&2, Bool>:
  match m:
    case None{}:
      a
    case Some{x}:
      Some{String.eq(x, "--private")}

# What the words say, read on from a command already part read.
def nw.from(+ws: List<&2, String>, +p: Bool, +a: Maybe<&2, Bool>, +d: Bool, +f: Bool, +sh: List<&2, String>, +r: List<&2, String>) -> Main.NameCmd:
  Main.NameCmd{nw.pin(List.last(&2, String, nw.rc(ws)), p), nw.axis(List.last(&2, String, nw.ps(ws)), a), Bool.or(d, Rev.member(ws, "--delete")), Bool.or(f, Rev.member(ws, "--fields")), List.append(&2, String, sh, nw.shaping(ws)), List.append(&2, String, r, nw.others(ws))}

# `nw.from` of a word and more, with the word's answer to each question
# handed in.
def nw.cons(+w: String, +rest: List<&2, String>, +p: Bool, +a: Maybe<&2, Bool>, +d: Bool, +f: Bool, +sh: List<&2, String>, +r: List<&2, String>, brc: Bool, bps: Bool, bdel: Bool, bfld: Bool, bsh: Bool, bot: Bool) -> Main.NameCmd:
  Main.NameCmd{nw.pin(List.last(&2, String, List.filter.put(String, w, nw.rc(rest), brc)), p), nw.axis(List.last(&2, String, List.filter.put(String, w, nw.ps(rest), bps)), a), Bool.or(d, Bool.or(bdel, Rev.member(rest, "--delete"))), Bool.or(f, Bool.or(bfld, Rev.member(rest, "--fields"))), List.append(&2, String, sh, List.filter.put(String, w, nw.shaping(rest), bsh)), List.append(&2, String, r, List.filter.put(String, w, nw.others(rest), bot))}

def nw.pin_last(xs: List<&2, String>, +h: String) -> {nw.pin(List.last(&2, String, xs), String.eq(h, "--revision")) == String.eq(List.last.go(&2, String, xs, h), "--revision") : Bool}:
  match xs:
    case Nil{}:
      {==}
    case y <> ys:
      {==}

def nw.axis_last(xs: List<&2, String>, +h: String) -> {nw.axis(List.last(&2, String, xs), Some{String.eq(h, "--private")}) == Some{String.eq(List.last.go(&2, String, xs, h), "--private")} : Maybe<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case y <> ys:
      {==}

def nw.pin_top(m: Maybe<&2, String>) -> {nw.pin(m, False{}) == String.eq(Maybe.default(&2, String, m, ""), "--revision") : Bool}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def nw.axis_top(m: Maybe<&2, String>) -> {nw.axis(m, None{}) == Maybe.map(&2, String, Bool, x => String.eq(x, "--private"), m) : Maybe<&2, Bool>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def nw.or_true(b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def nw.or_false(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# A word that is not a flag's spelling is not it either way round.
def nw.flip_false(c: Bool, +x: String, +y: String, e: {String.eq(x, y) == False{} : Bool}, ec: {String.eq(y, x) == c : Bool}) -> {String.eq(y, x) == False{} : Bool}:
  match c:
    case False{}:
      ec
    case True{}:
      Empty.absurd({String.eq(y, x) == False{} : Bool}, S.true_false(Equal.trans(Bool, True{}, String.eq(x, x), False{}, Equal.sym(Bool, String.eq(x, x), True{}, S.eq_refl(x)),
        Equal.trans(Bool, String.eq(x, x), String.eq(x, y), False{}, Equal.cong(String, Bool, z => String.eq(x, z), x, y, Equal.sym(String, y, x, S.eq_true(y, x, ec))), e))))

def nw.flip(+x: String, +y: String, e: {String.eq(x, y) == False{} : Bool}) -> {String.eq(y, x) == False{} : Bool}:
  nw.flip_false(String.eq(y, x), x, y, e, {==})

# A word none of the six flags is read as none of them.
def nw.word_other(+w: String, e1: {String.eq(w, "--revision") == False{} : Bool}, e2: {String.eq(w, "--change") == False{} : Bool}, e3: {String.eq(w, "--private") == False{} : Bool}, e4: {String.eq(w, "--shared") == False{} : Bool}, e5: {String.eq(w, "--delete") == False{} : Bool}, e6: {String.eq(w, "--fields") == False{} : Bool}) -> {Main.nword(w) == Main.NWord.Other{} : Main.NWord}:
  %Equal.sym(Bool, String.eq(w, "--revision"), False{}, e1) : {Bool.pick(Main.NWord, _, Main.NWord.Revision{}, Bool.pick(Main.NWord, String.eq(w, "--change"), Main.NWord.Change{}, Bool.pick(Main.NWord, String.eq(w, "--private"), Main.NWord.Private{}, Bool.pick(Main.NWord, String.eq(w, "--shared"), Main.NWord.Shared{}, Bool.pick(Main.NWord, String.eq(w, "--delete"), Main.NWord.Delete{}, Bool.pick(Main.NWord, String.eq(w, "--fields"), Main.NWord.Fields{}, Main.NWord.Other{})))))) == Main.NWord.Other{} : Main.NWord}
  %Equal.sym(Bool, String.eq(w, "--change"), False{}, e2) : {Bool.pick(Main.NWord, _, Main.NWord.Change{}, Bool.pick(Main.NWord, String.eq(w, "--private"), Main.NWord.Private{}, Bool.pick(Main.NWord, String.eq(w, "--shared"), Main.NWord.Shared{}, Bool.pick(Main.NWord, String.eq(w, "--delete"), Main.NWord.Delete{}, Bool.pick(Main.NWord, String.eq(w, "--fields"), Main.NWord.Fields{}, Main.NWord.Other{}))))) == Main.NWord.Other{} : Main.NWord}
  %Equal.sym(Bool, String.eq(w, "--private"), False{}, e3) : {Bool.pick(Main.NWord, _, Main.NWord.Private{}, Bool.pick(Main.NWord, String.eq(w, "--shared"), Main.NWord.Shared{}, Bool.pick(Main.NWord, String.eq(w, "--delete"), Main.NWord.Delete{}, Bool.pick(Main.NWord, String.eq(w, "--fields"), Main.NWord.Fields{}, Main.NWord.Other{})))) == Main.NWord.Other{} : Main.NWord}
  %Equal.sym(Bool, String.eq(w, "--shared"), False{}, e4) : {Bool.pick(Main.NWord, _, Main.NWord.Shared{}, Bool.pick(Main.NWord, String.eq(w, "--delete"), Main.NWord.Delete{}, Bool.pick(Main.NWord, String.eq(w, "--fields"), Main.NWord.Fields{}, Main.NWord.Other{}))) == Main.NWord.Other{} : Main.NWord}
  %Equal.sym(Bool, String.eq(w, "--delete"), False{}, e5) : {Bool.pick(Main.NWord, _, Main.NWord.Delete{}, Bool.pick(Main.NWord, String.eq(w, "--fields"), Main.NWord.Fields{}, Main.NWord.Other{})) == Main.NWord.Other{} : Main.NWord}
  %Equal.sym(Bool, String.eq(w, "--fields"), False{}, e6) : {Bool.pick(Main.NWord, _, Main.NWord.Fields{}, Main.NWord.Other{}) == Main.NWord.Other{} : Main.NWord}
  {==}

# And it is among none of the lists of flags.
def nw.not_rc(+w: String, s1: {String.eq("--revision", w) == False{} : Bool}, s2: {String.eq("--change", w) == False{} : Bool}) -> {Rev.member(["--revision", "--change"], w) == False{} : Bool}:
  %Equal.sym(Bool, String.eq("--revision", w), False{}, s1) : {Bool.or(_, Bool.or(String.eq("--change", w), False{})) == False{} : Bool}
  %Equal.sym(Bool, String.eq("--change", w), False{}, s2) : {Bool.or(_, False{}) == False{} : Bool}
  {==}

def nw.not_ps(+w: String, s3: {String.eq("--private", w) == False{} : Bool}, s4: {String.eq("--shared", w) == False{} : Bool}) -> {Rev.member(["--private", "--shared"], w) == False{} : Bool}:
  %Equal.sym(Bool, String.eq("--private", w), False{}, s3) : {Bool.or(_, Bool.or(String.eq("--shared", w), False{})) == False{} : Bool}
  %Equal.sym(Bool, String.eq("--shared", w), False{}, s4) : {Bool.or(_, False{}) == False{} : Bool}
  {==}

def nw.not_shaping(+w: String, s1: {String.eq("--revision", w) == False{} : Bool}, s2: {String.eq("--change", w) == False{} : Bool}, s3: {String.eq("--private", w) == False{} : Bool}, s4: {String.eq("--shared", w) == False{} : Bool}) -> {Rev.member(["--revision", "--change", "--private", "--shared"], w) == False{} : Bool}:
  %Equal.sym(Bool, String.eq("--revision", w), False{}, s1) : {Bool.or(_, Bool.or(String.eq("--change", w), Bool.or(String.eq("--private", w), Bool.or(String.eq("--shared", w), False{})))) == False{} : Bool}
  %Equal.sym(Bool, String.eq("--change", w), False{}, s2) : {Bool.or(_, Bool.or(String.eq("--private", w), Bool.or(String.eq("--shared", w), False{}))) == False{} : Bool}
  %Equal.sym(Bool, String.eq("--private", w), False{}, s3) : {Bool.or(_, Bool.or(String.eq("--shared", w), False{})) == False{} : Bool}
  %Equal.sym(Bool, String.eq("--shared", w), False{}, s4) : {Bool.or(_, False{}) == False{} : Bool}
  {==}

def nw.not_flag(+w: String, s1: {String.eq("--revision", w) == False{} : Bool}, s2: {String.eq("--change", w) == False{} : Bool}, s3: {String.eq("--private", w) == False{} : Bool}, s4: {String.eq("--shared", w) == False{} : Bool}, s5: {String.eq("--delete", w) == False{} : Bool}, s6: {String.eq("--fields", w) == False{} : Bool}) -> {Rev.member(["--revision", "--change", "--private", "--shared", "--delete", "--fields"], w) == False{} : Bool}:
  %Equal.sym(Bool, String.eq("--revision", w), False{}, s1) : {Bool.or(_, Bool.or(String.eq("--change", w), Bool.or(String.eq("--private", w), Bool.or(String.eq("--shared", w), Bool.or(String.eq("--delete", w), Bool.or(String.eq("--fields", w), False{})))))) == False{} : Bool}
  %Equal.sym(Bool, String.eq("--change", w), False{}, s2) : {Bool.or(_, Bool.or(String.eq("--private", w), Bool.or(String.eq("--shared", w), Bool.or(String.eq("--delete", w), Bool.or(String.eq("--fields", w), False{}))))) == False{} : Bool}
  %Equal.sym(Bool, String.eq("--private", w), False{}, s3) : {Bool.or(_, Bool.or(String.eq("--shared", w), Bool.or(String.eq("--delete", w), Bool.or(String.eq("--fields", w), False{})))) == False{} : Bool}
  %Equal.sym(Bool, String.eq("--shared", w), False{}, s4) : {Bool.or(_, Bool.or(String.eq("--delete", w), Bool.or(String.eq("--fields", w), False{}))) == False{} : Bool}
  %Equal.sym(Bool, String.eq("--delete", w), False{}, s5) : {Bool.or(_, Bool.or(String.eq("--fields", w), False{})) == False{} : Bool}
  %Equal.sym(Bool, String.eq("--fields", w), False{}, s6) : {Bool.or(_, False{}) == False{} : Bool}
  {==}

# A word none of the flags joins the other words, and changes nothing else.
def nw.cons_other(+w: String, +rest: List<&2, String>, +p: Bool, +a: Maybe<&2, Bool>, +d: Bool, +f: Bool, +sh: List<&2, String>, +r: List<&2, String>, mrc: {Rev.member(["--revision", "--change"], w) == False{} : Bool}, mps: {Rev.member(["--private", "--shared"], w) == False{} : Bool}, e5: {String.eq(w, "--delete") == False{} : Bool}, e6: {String.eq(w, "--fields") == False{} : Bool}, msh: {Rev.member(["--revision", "--change", "--private", "--shared"], w) == False{} : Bool}, mot: {Rev.member(["--revision", "--change", "--private", "--shared", "--delete", "--fields"], w) == False{} : Bool}) -> {nw.from(rest, p, a, d, f, sh, List.append(&2, String, r, [w])) == nw.from(w <> rest, p, a, d, f, sh, r) : Main.NameCmd}:
  %Equal.sym(Bool, Rev.member(["--revision", "--change"], w), False{}, mrc) : {nw.from(rest, p, a, d, f, sh, List.append(&2, String, r, [w])) == nw.cons(w, rest, p, a, d, f, sh, r, _, Rev.member(["--private", "--shared"], w), String.eq(w, "--delete"), String.eq(w, "--fields"), Rev.member(["--revision", "--change", "--private", "--shared"], w), Bool.not(Rev.member(["--revision", "--change", "--private", "--shared", "--delete", "--fields"], w))) : Main.NameCmd}
  %Equal.sym(Bool, Rev.member(["--private", "--shared"], w), False{}, mps) : {nw.from(rest, p, a, d, f, sh, List.append(&2, String, r, [w])) == nw.cons(w, rest, p, a, d, f, sh, r, False{}, _, String.eq(w, "--delete"), String.eq(w, "--fields"), Rev.member(["--revision", "--change", "--private", "--shared"], w), Bool.not(Rev.member(["--revision", "--change", "--private", "--shared", "--delete", "--fields"], w))) : Main.NameCmd}
  %Equal.sym(Bool, String.eq(w, "--delete"), False{}, e5) : {nw.from(rest, p, a, d, f, sh, List.append(&2, String, r, [w])) == nw.cons(w, rest, p, a, d, f, sh, r, False{}, False{}, _, String.eq(w, "--fields"), Rev.member(["--revision", "--change", "--private", "--shared"], w), Bool.not(Rev.member(["--revision", "--change", "--private", "--shared", "--delete", "--fields"], w))) : Main.NameCmd}
  %Equal.sym(Bool, String.eq(w, "--fields"), False{}, e6) : {nw.from(rest, p, a, d, f, sh, List.append(&2, String, r, [w])) == nw.cons(w, rest, p, a, d, f, sh, r, False{}, False{}, False{}, _, Rev.member(["--revision", "--change", "--private", "--shared"], w), Bool.not(Rev.member(["--revision", "--change", "--private", "--shared", "--delete", "--fields"], w))) : Main.NameCmd}
  %Equal.sym(Bool, Rev.member(["--revision", "--change", "--private", "--shared"], w), False{}, msh) : {nw.from(rest, p, a, d, f, sh, List.append(&2, String, r, [w])) == nw.cons(w, rest, p, a, d, f, sh, r, False{}, False{}, False{}, False{}, _, Bool.not(Rev.member(["--revision", "--change", "--private", "--shared", "--delete", "--fields"], w))) : Main.NameCmd}
  %Equal.sym(Bool, Rev.member(["--revision", "--change", "--private", "--shared", "--delete", "--fields"], w), False{}, mot) : {nw.from(rest, p, a, d, f, sh, List.append(&2, String, r, [w])) == nw.cons(w, rest, p, a, d, f, sh, r, False{}, False{}, False{}, False{}, False{}, Bool.not(_)) : Main.NameCmd}
  %SortL.app_assoc(String, r, [w], nw.others(rest)) : {nw.from(rest, p, a, d, f, sh, List.append(&2, String, r, [w])) == Main.NameCmd{nw.pin(List.last(&2, String, nw.rc(rest)), p), nw.axis(List.last(&2, String, nw.ps(rest)), a), Bool.or(d, Rev.member(rest, "--delete")), Bool.or(f, Rev.member(rest, "--fields")), List.append(&2, String, sh, nw.shaping(rest)), _} : Main.NameCmd}
  {==}

# What one more word reads as, read on from the rest.
def nw.ih(rest: List<&2, String>) -> Type:
  @p2: Bool -> @a2: Maybe<&2, Bool> -> @d2: Bool -> @f2: Bool -> @sh2: List<&2, String> -> @r2: List<&2, String> -> {Main.name.args(rest, Main.NameCmd{p2, a2, d2, f2, sh2, r2}) == nw.from(rest, p2, a2, d2, f2, sh2, r2) : Main.NameCmd}

def nw.at_other(+w: String, +rest: List<&2, String>, +p: Bool, +a: Maybe<&2, Bool>, +d: Bool, +f: Bool, +sh: List<&2, String>, +r: List<&2, String>, +e1: {String.eq(w, "--revision") == False{} : Bool}, +e2: {String.eq(w, "--change") == False{} : Bool}, +e3: {String.eq(w, "--private") == False{} : Bool}, +e4: {String.eq(w, "--shared") == False{} : Bool}, +e5: {String.eq(w, "--delete") == False{} : Bool}, +e6: {String.eq(w, "--fields") == False{} : Bool}, ih: nw.ih(rest)) -> {Main.name.args(rest, Main.name.word(Main.NameCmd{p, a, d, f, sh, r}, Main.nword(w), w)) == nw.from(w <> rest, p, a, d, f, sh, r) : Main.NameCmd}:
  +s1 = nw.flip(w, "--revision", e1)
  +s2 = nw.flip(w, "--change", e2)
  +s3 = nw.flip(w, "--private", e3)
  +s4 = nw.flip(w, "--shared", e4)
  +s5 = nw.flip(w, "--delete", e5)
  +s6 = nw.flip(w, "--fields", e6)
  %Equal.sym(Main.NWord, Main.nword(w), Main.NWord.Other{}, nw.word_other(w, e1, e2, e3, e4, e5, e6)) : {Main.name.args(rest, Main.name.word(Main.NameCmd{p, a, d, f, sh, r}, _, w)) == nw.from(w <> rest, p, a, d, f, sh, r) : Main.NameCmd}
  Equal.trans(Main.NameCmd, Main.name.args(rest, Main.NameCmd{p, a, d, f, sh, List.append(&2, String, r, [w])}), nw.from(rest, p, a, d, f, sh, List.append(&2, String, r, [w])), nw.from(w <> rest, p, a, d, f, sh, r),
    ih(p, a, d, f, sh, List.append(&2, String, r, [w])),
    nw.cons_other(w, rest, p, a, d, f, sh, r, nw.not_rc(w, s1, s2), nw.not_ps(w, s3, s4), e5, e6, nw.not_shaping(w, s1, s2, s3, s4), nw.not_flag(w, s1, s2, s3, s4, s5, s6)))

# Each flag, read on from the rest.
def nw.at_revision(+rest: List<&2, String>, +p: Bool, +a: Maybe<&2, Bool>, +d: Bool, +f: Bool, +sh: List<&2, String>, +r: List<&2, String>, ih: nw.ih(rest)) -> {Main.name.args(rest, Main.name.word(Main.NameCmd{p, a, d, f, sh, r}, Main.nword("--revision"), "--revision")) == nw.from("--revision" <> rest, p, a, d, f, sh, r) : Main.NameCmd}:
  %nw.pin_last(nw.rc(rest), "--revision") : {Main.name.args(rest, Main.NameCmd{True{}, a, d, f, List.append(&2, String, sh, ["--revision"]), r}) == Main.NameCmd{_, nw.axis(List.last(&2, String, nw.ps(rest)), a), Bool.or(d, Rev.member(rest, "--delete")), Bool.or(f, Rev.member(rest, "--fields")), List.append(&2, String, sh, "--revision" <> nw.shaping(rest)), List.append(&2, String, r, nw.others(rest))} : Main.NameCmd}
  %SortL.app_assoc(String, sh, ["--revision"], nw.shaping(rest)) : {Main.name.args(rest, Main.NameCmd{True{}, a, d, f, List.append(&2, String, sh, ["--revision"]), r}) == Main.NameCmd{nw.pin(List.last(&2, String, nw.rc(rest)), True{}), nw.axis(List.last(&2, String, nw.ps(rest)), a), Bool.or(d, Rev.member(rest, "--delete")), Bool.or(f, Rev.member(rest, "--fields")), _, List.append(&2, String, r, nw.others(rest))} : Main.NameCmd}
  ih(True{}, a, d, f, List.append(&2, String, sh, ["--revision"]), r)

def nw.at_change(+rest: List<&2, String>, +p: Bool, +a: Maybe<&2, Bool>, +d: Bool, +f: Bool, +sh: List<&2, String>, +r: List<&2, String>, ih: nw.ih(rest)) -> {Main.name.args(rest, Main.name.word(Main.NameCmd{p, a, d, f, sh, r}, Main.nword("--change"), "--change")) == nw.from("--change" <> rest, p, a, d, f, sh, r) : Main.NameCmd}:
  %nw.pin_last(nw.rc(rest), "--change") : {Main.name.args(rest, Main.NameCmd{False{}, a, d, f, List.append(&2, String, sh, ["--change"]), r}) == Main.NameCmd{_, nw.axis(List.last(&2, String, nw.ps(rest)), a), Bool.or(d, Rev.member(rest, "--delete")), Bool.or(f, Rev.member(rest, "--fields")), List.append(&2, String, sh, "--change" <> nw.shaping(rest)), List.append(&2, String, r, nw.others(rest))} : Main.NameCmd}
  %SortL.app_assoc(String, sh, ["--change"], nw.shaping(rest)) : {Main.name.args(rest, Main.NameCmd{False{}, a, d, f, List.append(&2, String, sh, ["--change"]), r}) == Main.NameCmd{nw.pin(List.last(&2, String, nw.rc(rest)), False{}), nw.axis(List.last(&2, String, nw.ps(rest)), a), Bool.or(d, Rev.member(rest, "--delete")), Bool.or(f, Rev.member(rest, "--fields")), _, List.append(&2, String, r, nw.others(rest))} : Main.NameCmd}
  ih(False{}, a, d, f, List.append(&2, String, sh, ["--change"]), r)

def nw.at_private(+rest: List<&2, String>, +p: Bool, +a: Maybe<&2, Bool>, +d: Bool, +f: Bool, +sh: List<&2, String>, +r: List<&2, String>, ih: nw.ih(rest)) -> {Main.name.args(rest, Main.name.word(Main.NameCmd{p, a, d, f, sh, r}, Main.nword("--private"), "--private")) == nw.from("--private" <> rest, p, a, d, f, sh, r) : Main.NameCmd}:
  %nw.axis_last(nw.ps(rest), "--private") : {Main.name.args(rest, Main.NameCmd{p, Some{True{}}, d, f, List.append(&2, String, sh, ["--private"]), r}) == Main.NameCmd{nw.pin(List.last(&2, String, nw.rc(rest)), p), _, Bool.or(d, Rev.member(rest, "--delete")), Bool.or(f, Rev.member(rest, "--fields")), List.append(&2, String, sh, "--private" <> nw.shaping(rest)), List.append(&2, String, r, nw.others(rest))} : Main.NameCmd}
  %SortL.app_assoc(String, sh, ["--private"], nw.shaping(rest)) : {Main.name.args(rest, Main.NameCmd{p, Some{True{}}, d, f, List.append(&2, String, sh, ["--private"]), r}) == Main.NameCmd{nw.pin(List.last(&2, String, nw.rc(rest)), p), nw.axis(List.last(&2, String, nw.ps(rest)), Some{True{}}), Bool.or(d, Rev.member(rest, "--delete")), Bool.or(f, Rev.member(rest, "--fields")), _, List.append(&2, String, r, nw.others(rest))} : Main.NameCmd}
  ih(p, Some{True{}}, d, f, List.append(&2, String, sh, ["--private"]), r)

def nw.at_shared(+rest: List<&2, String>, +p: Bool, +a: Maybe<&2, Bool>, +d: Bool, +f: Bool, +sh: List<&2, String>, +r: List<&2, String>, ih: nw.ih(rest)) -> {Main.name.args(rest, Main.name.word(Main.NameCmd{p, a, d, f, sh, r}, Main.nword("--shared"), "--shared")) == nw.from("--shared" <> rest, p, a, d, f, sh, r) : Main.NameCmd}:
  %nw.axis_last(nw.ps(rest), "--shared") : {Main.name.args(rest, Main.NameCmd{p, Some{False{}}, d, f, List.append(&2, String, sh, ["--shared"]), r}) == Main.NameCmd{nw.pin(List.last(&2, String, nw.rc(rest)), p), _, Bool.or(d, Rev.member(rest, "--delete")), Bool.or(f, Rev.member(rest, "--fields")), List.append(&2, String, sh, "--shared" <> nw.shaping(rest)), List.append(&2, String, r, nw.others(rest))} : Main.NameCmd}
  %SortL.app_assoc(String, sh, ["--shared"], nw.shaping(rest)) : {Main.name.args(rest, Main.NameCmd{p, Some{False{}}, d, f, List.append(&2, String, sh, ["--shared"]), r}) == Main.NameCmd{nw.pin(List.last(&2, String, nw.rc(rest)), p), nw.axis(List.last(&2, String, nw.ps(rest)), Some{False{}}), Bool.or(d, Rev.member(rest, "--delete")), Bool.or(f, Rev.member(rest, "--fields")), _, List.append(&2, String, r, nw.others(rest))} : Main.NameCmd}
  ih(p, Some{False{}}, d, f, List.append(&2, String, sh, ["--shared"]), r)

def nw.at_delete(+rest: List<&2, String>, +p: Bool, +a: Maybe<&2, Bool>, +d: Bool, +f: Bool, +sh: List<&2, String>, +r: List<&2, String>, ih: nw.ih(rest)) -> {Main.name.args(rest, Main.name.word(Main.NameCmd{p, a, d, f, sh, r}, Main.nword("--delete"), "--delete")) == nw.from("--delete" <> rest, p, a, d, f, sh, r) : Main.NameCmd}:
  %Equal.sym(Bool, Bool.or(d, True{}), True{}, nw.or_true(d)) : {Main.name.args(rest, Main.NameCmd{p, a, True{}, f, sh, r}) == Main.NameCmd{nw.pin(List.last(&2, String, nw.rc(rest)), p), nw.axis(List.last(&2, String, nw.ps(rest)), a), _, Bool.or(f, Rev.member(rest, "--fields")), List.append(&2, String, sh, nw.shaping(rest)), List.append(&2, String, r, nw.others(rest))} : Main.NameCmd}
  ih(p, a, True{}, f, sh, r)

def nw.at_fields(+rest: List<&2, String>, +p: Bool, +a: Maybe<&2, Bool>, +d: Bool, +f: Bool, +sh: List<&2, String>, +r: List<&2, String>, ih: nw.ih(rest)) -> {Main.name.args(rest, Main.name.word(Main.NameCmd{p, a, d, f, sh, r}, Main.nword("--fields"), "--fields")) == nw.from("--fields" <> rest, p, a, d, f, sh, r) : Main.NameCmd}:
  %Equal.sym(Bool, Bool.or(f, True{}), True{}, nw.or_true(f)) : {Main.name.args(rest, Main.NameCmd{p, a, d, True{}, sh, r}) == Main.NameCmd{nw.pin(List.last(&2, String, nw.rc(rest)), p), nw.axis(List.last(&2, String, nw.ps(rest)), a), Bool.or(d, Rev.member(rest, "--delete")), _, List.append(&2, String, sh, nw.shaping(rest)), List.append(&2, String, r, nw.others(rest))} : Main.NameCmd}
  ih(p, a, d, True{}, sh, r)

# Which a word is: each flag in turn, or none of them.
def nw.step6(b: Bool, +w: String, +e1: {String.eq(w, "--revision") == False{} : Bool}, +e2: {String.eq(w, "--change") == False{} : Bool}, +e3: {String.eq(w, "--private") == False{} : Bool}, +e4: {String.eq(w, "--shared") == False{} : Bool}, +e5: {String.eq(w, "--delete") == False{} : Bool}, +e6: {String.eq(w, "--fields") == b : Bool}, +rest: List<&2, String>, +p: Bool, +a: Maybe<&2, Bool>, +d: Bool, +f: Bool, +sh: List<&2, String>, +r: List<&2, String>, ih: nw.ih(rest)) -> {Main.name.args(rest, Main.name.word(Main.NameCmd{p, a, d, f, sh, r}, Main.nword(w), w)) == nw.from(w <> rest, p, a, d, f, sh, r) : Main.NameCmd}:
  match b:
    case True{}:
      %Equal.sym(String, w, "--fields", S.eq_true(w, "--fields", e6)) : {Main.name.args(rest, Main.name.word(Main.NameCmd{p, a, d, f, sh, r}, Main.nword(_), _)) == nw.from(_ <> rest, p, a, d, f, sh, r) : Main.NameCmd}
      nw.at_fields(rest, p, a, d, f, sh, r, ih)
    case False{}:
      nw.at_other(w, rest, p, a, d, f, sh, r, e1, e2, e3, e4, e5, e6, ih)

def nw.step5(b: Bool, +w: String, +e1: {String.eq(w, "--revision") == False{} : Bool}, +e2: {String.eq(w, "--change") == False{} : Bool}, +e3: {String.eq(w, "--private") == False{} : Bool}, +e4: {String.eq(w, "--shared") == False{} : Bool}, +e5: {String.eq(w, "--delete") == b : Bool}, +rest: List<&2, String>, +p: Bool, +a: Maybe<&2, Bool>, +d: Bool, +f: Bool, +sh: List<&2, String>, +r: List<&2, String>, ih: nw.ih(rest)) -> {Main.name.args(rest, Main.name.word(Main.NameCmd{p, a, d, f, sh, r}, Main.nword(w), w)) == nw.from(w <> rest, p, a, d, f, sh, r) : Main.NameCmd}:
  match b:
    case True{}:
      %Equal.sym(String, w, "--delete", S.eq_true(w, "--delete", e5)) : {Main.name.args(rest, Main.name.word(Main.NameCmd{p, a, d, f, sh, r}, Main.nword(_), _)) == nw.from(_ <> rest, p, a, d, f, sh, r) : Main.NameCmd}
      nw.at_delete(rest, p, a, d, f, sh, r, ih)
    case False{}:
      nw.step6(String.eq(w, "--fields"), w, e1, e2, e3, e4, e5, {==}, rest, p, a, d, f, sh, r, ih)

def nw.step4(b: Bool, +w: String, +e1: {String.eq(w, "--revision") == False{} : Bool}, +e2: {String.eq(w, "--change") == False{} : Bool}, +e3: {String.eq(w, "--private") == False{} : Bool}, +e4: {String.eq(w, "--shared") == b : Bool}, +rest: List<&2, String>, +p: Bool, +a: Maybe<&2, Bool>, +d: Bool, +f: Bool, +sh: List<&2, String>, +r: List<&2, String>, ih: nw.ih(rest)) -> {Main.name.args(rest, Main.name.word(Main.NameCmd{p, a, d, f, sh, r}, Main.nword(w), w)) == nw.from(w <> rest, p, a, d, f, sh, r) : Main.NameCmd}:
  match b:
    case True{}:
      %Equal.sym(String, w, "--shared", S.eq_true(w, "--shared", e4)) : {Main.name.args(rest, Main.name.word(Main.NameCmd{p, a, d, f, sh, r}, Main.nword(_), _)) == nw.from(_ <> rest, p, a, d, f, sh, r) : Main.NameCmd}
      nw.at_shared(rest, p, a, d, f, sh, r, ih)
    case False{}:
      nw.step5(String.eq(w, "--delete"), w, e1, e2, e3, e4, {==}, rest, p, a, d, f, sh, r, ih)

def nw.step3(b: Bool, +w: String, +e1: {String.eq(w, "--revision") == False{} : Bool}, +e2: {String.eq(w, "--change") == False{} : Bool}, +e3: {String.eq(w, "--private") == b : Bool}, +rest: List<&2, String>, +p: Bool, +a: Maybe<&2, Bool>, +d: Bool, +f: Bool, +sh: List<&2, String>, +r: List<&2, String>, ih: nw.ih(rest)) -> {Main.name.args(rest, Main.name.word(Main.NameCmd{p, a, d, f, sh, r}, Main.nword(w), w)) == nw.from(w <> rest, p, a, d, f, sh, r) : Main.NameCmd}:
  match b:
    case True{}:
      %Equal.sym(String, w, "--private", S.eq_true(w, "--private", e3)) : {Main.name.args(rest, Main.name.word(Main.NameCmd{p, a, d, f, sh, r}, Main.nword(_), _)) == nw.from(_ <> rest, p, a, d, f, sh, r) : Main.NameCmd}
      nw.at_private(rest, p, a, d, f, sh, r, ih)
    case False{}:
      nw.step4(String.eq(w, "--shared"), w, e1, e2, e3, {==}, rest, p, a, d, f, sh, r, ih)

def nw.step2(b: Bool, +w: String, +e1: {String.eq(w, "--revision") == False{} : Bool}, +e2: {String.eq(w, "--change") == b : Bool}, +rest: List<&2, String>, +p: Bool, +a: Maybe<&2, Bool>, +d: Bool, +f: Bool, +sh: List<&2, String>, +r: List<&2, String>, ih: nw.ih(rest)) -> {Main.name.args(rest, Main.name.word(Main.NameCmd{p, a, d, f, sh, r}, Main.nword(w), w)) == nw.from(w <> rest, p, a, d, f, sh, r) : Main.NameCmd}:
  match b:
    case True{}:
      %Equal.sym(String, w, "--change", S.eq_true(w, "--change", e2)) : {Main.name.args(rest, Main.name.word(Main.NameCmd{p, a, d, f, sh, r}, Main.nword(_), _)) == nw.from(_ <> rest, p, a, d, f, sh, r) : Main.NameCmd}
      nw.at_change(rest, p, a, d, f, sh, r, ih)
    case False{}:
      nw.step3(String.eq(w, "--private"), w, e1, e2, {==}, rest, p, a, d, f, sh, r, ih)

def nw.step1(b: Bool, +w: String, +e1: {String.eq(w, "--revision") == b : Bool}, +rest: List<&2, String>, +p: Bool, +a: Maybe<&2, Bool>, +d: Bool, +f: Bool, +sh: List<&2, String>, +r: List<&2, String>, ih: nw.ih(rest)) -> {Main.name.args(rest, Main.name.word(Main.NameCmd{p, a, d, f, sh, r}, Main.nword(w), w)) == nw.from(w <> rest, p, a, d, f, sh, r) : Main.NameCmd}:
  match b:
    case True{}:
      %Equal.sym(String, w, "--revision", S.eq_true(w, "--revision", e1)) : {Main.name.args(rest, Main.name.word(Main.NameCmd{p, a, d, f, sh, r}, Main.nword(_), _)) == nw.from(_ <> rest, p, a, d, f, sh, r) : Main.NameCmd}
      nw.at_revision(rest, p, a, d, f, sh, r, ih)
    case False{}:
      nw.step2(String.eq(w, "--change"), w, e1, {==}, rest, p, a, d, f, sh, r, ih)

def nw.go(ws: List<&2, String>, +p: Bool, +a: Maybe<&2, Bool>, +d: Bool, +f: Bool, +sh: List<&2, String>, +r: List<&2, String>) -> {Main.name.args(ws, Main.NameCmd{p, a, d, f, sh, r}) == nw.from(ws, p, a, d, f, sh, r) : Main.NameCmd}:
  match ws:
    case Nil{}:
      %Equal.sym(Bool, Bool.or(d, False{}), d, nw.or_false(d)) : {Main.NameCmd{p, a, d, f, sh, r} == Main.NameCmd{p, a, _, Bool.or(f, False{}), List.append(&2, String, sh, Nil{}), List.append(&2, String, r, Nil{})} : Main.NameCmd}
      %Equal.sym(Bool, Bool.or(f, False{}), f, nw.or_false(f)) : {Main.NameCmd{p, a, d, f, sh, r} == Main.NameCmd{p, a, d, _, List.append(&2, String, sh, Nil{}), List.append(&2, String, r, Nil{})} : Main.NameCmd}
      %Equal.sym(List<&2, String>, List.append(&2, String, sh, Nil{}), sh, SortL.lapp_nil(String, sh)) : {Main.NameCmd{p, a, d, f, sh, r} == Main.NameCmd{p, a, d, f, _, List.append(&2, String, r, Nil{})} : Main.NameCmd}
      %Equal.sym(List<&2, String>, List.append(&2, String, r, Nil{}), r, SortL.lapp_nil(String, r)) : {Main.NameCmd{p, a, d, f, sh, r} == Main.NameCmd{p, a, d, f, sh, _} : Main.NameCmd}
      {==}
    case +w <> +rest:
      nw.step1(String.eq(w, "--revision"), w, {==}, rest, p, a, d, f, sh, r, p2 => a2 => d2 => f2 => sh2 => r2 => nw.go(rest, p2, a2, d2, f2, sh2, r2))

# `name` reads its words as their plain reading says.
def args_said(+ws: List<&2, String>) -> {Main.name.args(ws, Main.NameCmd{False{}, None{}, False{}, False{}, Nil{}, Nil{}}) == Main.NameCmd{String.eq(Maybe.default(&2, String, List.last(&2, String, List.filter(~String, ~(w => Rev.member(["--revision", "--change"], w)), ws)), ""), "--revision"), Maybe.map(&2, String, Bool, x => String.eq(x, "--private"), List.last(&2, String, List.filter(~String, ~(w => Rev.member(["--private", "--shared"], w)), ws))), Rev.member(ws, "--delete"), Rev.member(ws, "--fields"), List.filter(~String, ~(w => Rev.member(["--revision", "--change", "--private", "--shared"], w)), ws), List.filter(~String, ~(w => Bool.not(Rev.member(["--revision", "--change", "--private", "--shared", "--delete", "--fields"], w))), ws)} : Main.NameCmd}:
  %nw.pin_top(List.last(&2, String, nw.rc(ws))) : {Main.name.args(ws, Main.NameCmd{False{}, None{}, False{}, False{}, Nil{}, Nil{}}) == Main.NameCmd{_, Maybe.map(&2, String, Bool, x => String.eq(x, "--private"), List.last(&2, String, nw.ps(ws))), Rev.member(ws, "--delete"), Rev.member(ws, "--fields"), nw.shaping(ws), nw.others(ws)} : Main.NameCmd}
  %nw.axis_top(List.last(&2, String, nw.ps(ws))) : {Main.name.args(ws, Main.NameCmd{False{}, None{}, False{}, False{}, Nil{}, Nil{}}) == Main.NameCmd{nw.pin(List.last(&2, String, nw.rc(ws)), False{}), _, Rev.member(ws, "--delete"), Rev.member(ws, "--fields"), nw.shaping(ws), nw.others(ws)} : Main.NameCmd}
  nw.go(ws, False{}, None{}, False{}, False{}, Nil{}, Nil{})

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

# The revision `find` answers for a digest carries its own change.
def carries_at(b: Bool, +i: String, +change: String, +parents: List<&2, String>, +supersedes: List<&2, String>, +author: String, +when: String, +revised_by: Maybe<&2, String>, +revised: Maybe<&2, String>, +facts: List<&2, Rev.Header>, +message: String, +rest: List<&2, Main.Full>, +x: String, +g: Main.Full, e: {Bool.pick(Maybe<&2, Main.Full>, b, Some{Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}}, Main.find(rest, x)) == Some{g} : Maybe<&2, Main.Full>}, ih: {Main.find(rest, x) == Some{g} : Maybe<&2, Main.Full>} -> {Main.name.carries(rest, Main.id_of(g), Main.change_of(g)) == True{} : Bool}) -> {Main.name.carries(Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message} <> rest, Main.id_of(g), Main.change_of(g)) == True{} : Bool}:
  match b:
    case True{}:
      +d = B.some_eq_f(Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}, g, e)
      %d : {Main.name.carries(Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message} <> rest, Main.id_of(_), Main.change_of(_)) == True{} : Bool}
      AL.or_left(Bool.and(String.eq(i, i), String.eq(change, change)), Main.name.carries(rest, i, change), AL.and_intro(String.eq(i, i), String.eq(change, change), S.eq_refl(i), S.eq_refl(change)))
    case False{}:
      AL.or_right(Bool.and(String.eq(i, Main.id_of(g)), String.eq(change, Main.change_of(g))), Main.name.carries(rest, Main.id_of(g), Main.change_of(g)), ih(e))

def find_carries(fs: List<&2, Main.Full>, +x: String, +g: Main.Full, e: {Main.find(fs, x) == Some{g} : Maybe<&2, Main.Full>}) -> {Main.name.carries(fs, Main.id_of(g), Main.change_of(g)) == True{} : Bool}:
  match fs:
    case Nil{}:
      Empty.absurd({Main.name.carries(Nil{}, Main.id_of(g), Main.change_of(g)) == True{} : Bool}, (%e : {B.mdisc_f(_) : Type} Unit{}))
    case Main.Full{+i, +change, +parents, +supersedes, +author, +when, +revised_by, +revised, +facts, +message} <> +rest:
      carries_at(String.eq(i, x), i, change, parents, supersedes, author, when, revised_by, revised, facts, message, rest, x, g, e, h => find_carries(rest, x, g, h))

# The revision a target names is the one the store holds under the digest
# `resolve` reads it as, which every command resolves it by.
def found_is(+fs: List<&2, Main.Full>, +id: String, m: Maybe<&2, Main.Full>, +em: {Main.find(fs, id) == m : Maybe<&2, Main.Full>}, +f: Main.Full, e: {Main.resolved.found.r(id, m) == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}) -> {Main.find(fs, id) == Some{f} : Maybe<&2, Main.Full>}:
  match m:
    case None{}:
      Empty.absurd({Main.find(fs, id) == Some{f} : Maybe<&2, Main.Full>}, B.refuse(Main.Full, Main.resolved.found.r(id, None{}), f, {==}, e))
    case Some{+g}:
      Equal.trans(Maybe<&2, Main.Full>, Main.find(fs, id), Some{g}, Some{f}, em, Equal.cong(Main.Full, Maybe<&2, Main.Full>, x => Some{x}, g, f, B.done_eq(Main.Full, g, f, e)))

def resolved_is(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +sp: String, +id: String, er: {Main.resolve(fs, bs, sp) == Done{id} : Result<&2, &2, String, String>}, +f: Main.Full, e: {Main.resolved.r(fs, bs, sp) == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}) -> {Main.find(fs, id) == Some{f} : Maybe<&2, Main.Full>}:
  found_is(fs, id, Main.find(fs, id), {==}, f,
    Equal.trans(Result<&2, &2, Main.Refused, Main.Full>, Main.resolved.of.r(fs, Done{id}), Main.resolved.of.r(fs, Main.resolve(fs, bs, sp)), Done{f},
      Equal.cong(Result<&2, &2, String, String>, Result<&2, &2, Main.Refused, Main.Full>, r => Main.resolved.of.r(fs, r), Done{id}, Main.resolve(fs, bs, sp), Equal.sym(Result<&2, &2, String, String>, Main.resolve(fs, bs, sp), Done{id}, er)),
      e))

# `name` refuses an empty target before resolving it, and otherwise
# resolves it as every command does.
def name_resolved(b: Bool, -r: Result<&2, &2, Main.Refused, Main.Full>, -f: Main.Full, e: {Bool.pick(Result<&2, &2, Main.Refused, Main.Full>, b, Fail{Main.Refused{2, "a target cannot be empty"}}, r) == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}) -> {r == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}:
  match b:
    case True{}:
      Empty.absurd({r == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}, B.fail_done(Main.Full, Main.Refused{2, "a target cannot be empty"}, f, e))
    case False{}:
      e

def target_eq(-a: Bm.Target, -b: Bm.Target, h: {Done{a} == Done{b} : Result<&2, &2, Main.Refused, Bm.Target>}) -> {a == b : Bm.Target}:
  B.done_eq(Bm.Target, a, b, h)

# A file bookmark names the file `show` names at that revision and path.
def file_aimed(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +p: String, +pin: Bool, r: Result<&2, &2, Main.Refused, String>, +er: {Main.show.file.r(fs, bs, id, p) == r : Result<&2, &2, Main.Refused, String>}, +t: Bm.Target, e: {Result.map(&2, &2, Main.Refused, String, Bm.Target, file => Bm.Target.File{file}, r) == Done{t} : Result<&2, &2, Main.Refused, Bm.Target>}) -> {Main.name.aimed(fs, bs, id, Some{p}, pin, t) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.name.aimed(fs, bs, id, Some{p}, pin, t) == True{} : Bool}, B.fail_done(Bm.Target, x, t, e))
    case Done{+x}:
      %target_eq(Bm.Target.File{x}, t, e) : {Main.name.aimed(fs, bs, id, Some{p}, pin, _) == True{} : Bool}
      %Equal.sym(Result<&2, &2, Main.Refused, String>, Main.show.file.r(fs, bs, id, p), Done{x}, er) : {Main.name.shown(_, x) == True{} : Bool}
      S.eq_refl(x)

# The target is what was asked for, at the revision named.
def aimed_ok(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +f: Main.Full, path: Maybe<&2, String>, pin: Bool, +hc: {Main.name.carries(fs, Main.id_of(f), Main.change_of(f)) == True{} : Bool}, +t: Bm.Target, e: {Main.name.target.r(fs, bs, f, path, pin) == Done{t} : Result<&2, &2, Main.Refused, Bm.Target>}) -> {Main.name.aimed(fs, bs, Main.id_of(f), path, pin, t) == True{} : Bool}:
  match path pin:
    case Some{+p} True{}:
      file_aimed(fs, bs, Main.id_of(f), p, True{}, Main.show.file.r(fs, bs, Main.id_of(f), p), {==}, t, e)
    case Some{+p} False{}:
      file_aimed(fs, bs, Main.id_of(f), p, False{}, Main.show.file.r(fs, bs, Main.id_of(f), p), {==}, t, e)
    case None{} True{}:
      %target_eq(Bm.Target.Revision{Main.id_of(f)}, t, e) : {Main.name.aimed(fs, bs, Main.id_of(f), None{}, True{}, _) == True{} : Bool}
      S.eq_refl(Main.id_of(f))
    case None{} False{}:
      %target_eq(Bm.Target.Change{Main.change_of(f)}, t, e) : {Main.name.aimed(fs, bs, Main.id_of(f), None{}, False{}, _) == True{} : Bool}
      hc

def bm_eq(-a: Bm.Bookmark, -b: Bm.Bookmark, h: {Done{a} == Done{b} : Result<&2, &2, Main.Refused, Bm.Bookmark>}) -> {a == b : Bm.Bookmark}:
  B.done_eq(Bm.Bookmark, a, b, h)

def checked_unit(u: Unit, -n: String, e: {Main.name.checked.r(n) == Done{u} : Result<&2, &2, Main.Refused, Unit>}) -> {Main.name.checked.r(n) == Done{Unit{}} : Result<&2, &2, Main.Refused, Unit>}:
  match u:
    case Unit{}:
      e

def points3(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +n: String, +id: String, path: Maybe<&2, String>, pin: Bool, +axis: Maybe<&2, Bool>, +t: Bm.Target, +ht: {Main.name.aimed(fs, bs, id, path, pin, t) == True{} : Bool}, r: Result<&2, &2, Main.Refused, Unit>, +er: {Main.name.checked.r(n) == r : Result<&2, &2, Main.Refused, Unit>}, +b: Bm.Bookmark, e: {Result.bind(&2, &2, Main.Refused, Unit, Bm.Bookmark, r, u => Done{Bm.Bookmark{n, t, Maybe.default(&2, Bool, axis, Main.private_of(bs, n))}}) == Done{b} : Result<&2, &2, Main.Refused, Bm.Bookmark>}) -> {Main.name.points(fs, bs, n, id, path, pin, axis, b) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.name.points(fs, bs, n, id, path, pin, axis, b) == True{} : Bool}, B.fail_done(Bm.Bookmark, x, b, e))
    case Done{u}:
      %bm_eq(Bm.Bookmark{n, t, Maybe.default(&2, Bool, axis, Main.private_of(bs, n))}, b, e) : {Main.name.points(fs, bs, n, id, path, pin, axis, _) == True{} : Bool}
      %Equal.sym(Bool, String.eq(n, n), True{}, S.eq_refl(n)) : {Bool.and(_, Bool.and(Bool.not(Main.escapes(n)), Bool.and(Main.name.aimed(fs, bs, id, path, pin, t), Main.name.kept(bs, n, axis, Maybe.default(&2, Bool, axis, Main.private_of(bs, n)))))) == True{} : Bool}
      AL.and_intro(Bool.not(Main.escapes(n)), Bool.and(Main.name.aimed(fs, bs, id, path, pin, t), Main.name.kept(bs, n, axis, Maybe.default(&2, Bool, axis, Main.private_of(bs, n)))),
        AL.not_true(Main.escapes(n), stays(n, checked_unit(u, n, er))),
        AL.and_intro(Main.name.aimed(fs, bs, id, path, pin, t), Main.name.kept(bs, n, axis, Maybe.default(&2, Bool, axis, Main.private_of(bs, n))), ht, kept_ok(bs, n, axis)))

def points2(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +n: String, +f: Main.Full, +path: Maybe<&2, String>, +pin: Bool, +axis: Maybe<&2, Bool>, +hc: {Main.name.carries(fs, Main.id_of(f), Main.change_of(f)) == True{} : Bool}, r: Result<&2, &2, Main.Refused, Bm.Target>, +er: {Main.name.target.r(fs, bs, f, path, pin) == r : Result<&2, &2, Main.Refused, Bm.Target>}, +b: Bm.Bookmark, e: {Result.bind(&2, &2, Main.Refused, Bm.Target, Bm.Bookmark, r, t => Result.bind(&2, &2, Main.Refused, Unit, Bm.Bookmark, Main.name.checked.r(n), u => Done{Bm.Bookmark{n, t, Maybe.default(&2, Bool, axis, Main.private_of(bs, n))}})) == Done{b} : Result<&2, &2, Main.Refused, Bm.Bookmark>}) -> {Main.name.points(fs, bs, n, Main.id_of(f), path, pin, axis, b) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.name.points(fs, bs, n, Main.id_of(f), path, pin, axis, b) == True{} : Bool}, B.fail_done(Bm.Bookmark, x, b, e))
    case Done{+t}:
      points3(fs, bs, n, Main.id_of(f), path, pin, axis, t, aimed_ok(fs, bs, f, path, pin, hc, t, er), Main.name.checked.r(n), {==}, b, e)

def points1(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +n: String, +sp: String, +path: Maybe<&2, String>, +pin: Bool, +axis: Maybe<&2, Bool>, +id: String, +ei: {Main.resolve(fs, bs, sp) == Done{id} : Result<&2, &2, String, String>}, r: Result<&2, &2, Main.Refused, Main.Full>, +er: {Main.name.resolved.r(fs, bs, sp) == r : Result<&2, &2, Main.Refused, Main.Full>}, +b: Bm.Bookmark, e: {Result.bind(&2, &2, Main.Refused, Main.Full, Bm.Bookmark, r, f => Result.bind(&2, &2, Main.Refused, Bm.Target, Bm.Bookmark, Main.name.target.r(fs, bs, f, path, pin), t => Result.bind(&2, &2, Main.Refused, Unit, Bm.Bookmark, Main.name.checked.r(n), u => Done{Bm.Bookmark{n, t, Maybe.default(&2, Bool, axis, Main.private_of(bs, n))}}))) == Done{b} : Result<&2, &2, Main.Refused, Bm.Bookmark>}) -> {Main.name.points(fs, bs, n, id, path, pin, axis, b) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.name.points(fs, bs, n, id, path, pin, axis, b) == True{} : Bool}, B.fail_done(Bm.Bookmark, x, b, e))
    case Done{+f}:
      +found = resolved_is(fs, bs, sp, id, ei, f, name_resolved(String.is_empty(sp), Main.resolved.r(fs, bs, sp), f, er))
      %Equal.sym(String, id, Main.id_of(f), S.eq_true(id, Main.id_of(f), ChainL.find_id(fs, id, f, found))) : {Main.name.points(fs, bs, n, _, path, pin, axis, b) == True{} : Bool}
      points2(fs, bs, n, f, path, pin, axis, find_carries(fs, id, f, found), Main.name.target.r(fs, bs, f, path, pin), {==}, b, e)

# The bookmark `name` sets is named as asked, stays under `names/`, points
# at what the target and path name as every command resolves them, and is
# as private as asked or as it was.
def points_ok(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +n: String, +sp: String, +path: Maybe<&2, String>, +pin: Bool, +axis: Maybe<&2, Bool>, +b: Bm.Bookmark, e: {Main.name.stated.r(fs, bs, n, sp, path, pin, axis) == Done{b} : Result<&2, &2, Main.Refused, Bm.Bookmark>}, +id: String, ei: {Main.resolve(fs, bs, sp) == Done{id} : Result<&2, &2, String, String>}) -> {Main.name.points(fs, bs, n, id, path, pin, axis, b) == True{} : Bool}:
  points1(fs, bs, n, sp, path, pin, axis, id, ei, Main.name.resolved.r(fs, bs, sp), {==}, b, e)

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
