# `identity` writes one line, `author` and the name, and the file reads back
# as that author for work in any directory: the default block, which every
# `under` block defers to — wherever the name is one a revision can hold.
import Base
import ./identity.bend as Identity
import ./folder.bend as Folder
import ./text.bend as T
import ./bookmark_lemmas.bend as BmL
import ./anchor_lemmas.bend as AL
import ./composition_lemmas.bend as Comp
import ./editor_lemmas.bend as EditorL

# Characters
# ----------

# A character that is not a control character is not one that is.
def ctl.at(+c: Char, +d: Char, b: Bool, eb: {Char.is_eq(c, d) == b : Bool}, hd: {Folder.is_control(d) == True{} : Bool}, hc: {Folder.is_control(c) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Comp.false_true(Equal.trans(Bool, False{}, Folder.is_control(c), True{},
        Equal.sym(Bool, Folder.is_control(c), False{}, hc),
        Equal.trans(Bool, Folder.is_control(c), Folder.is_control(d), True{}, Equal.cong(Char, Bool, x => Folder.is_control(x), c, d, BmL.chr_eq(c, d, eb)), hd))))

def quiet(s: String) -> Bool:
  List.any(~&2, ~Char, ~Folder.is_control, String.to_list(s))

# A value with no control character in it has no newline in it.
def nonl(s: String, +h: {quiet(s) == False{} : Bool}) -> {BmL.nonl(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Char.is_eq(c, '\n'), False{}, ctl.at(c, '\n', Char.is_eq(c, '\n'), {==}, {==}, AL.or_false_l(Folder.is_control(c), quiet(t), h))) : {Bool.and(Bool.not(_), BmL.nonl(t)) == True{} : Bool}
      nonl(t, AL.or_false_r(Folder.is_control(c), quiet(t), h))

# Whether a string opens with a carriage return.
def cr_first(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Char.is_eq(c, '\r')

def cr_start(acc: String, h: {cr_first(acc) == False{} : Bool}) -> {String.starts_with(acc, "\r") == False{} : Bool}:
  match acc:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      %Equal.sym(Bool, Char.is_eq(c, '\r'), False{}, h) : {String.starts_with.if(t, SNil{}, _) == False{} : Bool}
      {==}

# Reversed onto something that does not open with a carriage return, a
# value with no control character in it does not either.
def cr_rev(s: String, +acc: String, +hs: {quiet(s) == False{} : Bool}, ha: {cr_first(acc) == False{} : Bool}) -> {String.starts_with(String.reverse.go(s, acc), "\r") == False{} : Bool}:
  match s:
    case SNil{}:
      cr_start(acc, ha)
    case SCon{+c, +t}:
      cr_rev(t, SCon{c, acc}, AL.or_false_r(Folder.is_control(c), quiet(t), hs), ctl.at(c, '\r', Char.is_eq(c, '\r'), {==}, {==}, AL.or_false_l(Folder.is_control(c), quiet(t), hs)))

# The line `identity` writes
# --------------------------

def reads_back(+file: String, +a: String, +directory: String, +home: Maybe<&2, String>, +h: {Identity.unusable(a) == False{} : Bool}) -> {Identity.from_text(file, Identity.wanted(a), directory, home) == Done{a} : Result<&2, &2, String, String>}:
  +q = AL.or_false_r(Folder.untrimmed(a), quiet(a), h)
  %Equal.sym(List<&2, String>, String.split(("author " ++ a) ++ SCon{'\n', SNil{}}, '\n'), ("author " ++ a) <> String.split(SNil{}, '\n'), BmL.split_nl("author " ++ a, SNil{}, nonl(a, q))) : {Identity.from_ids(file, Identity.parse.go(Folder.lines.trimmed(_), 1n, Done{Identity.Reading{Identity.Ids{None{}, Nil{}}, None{}, None{}, 0n}}), directory, home) == Done{a} : Result<&2, &2, String, String>}
  %Equal.sym(Bool, String.ends_with("author " ++ a, "\r"), False{}, cr_rev(a, " rohtua", q, {==})) : {Identity.from_ids(file, Identity.parse.go([Bool.pick(String, _, String.take("author " ++ a, Nat.sub(String.length("author " ++ a), 1n)), "author " ++ a)], 1n, Done{Identity.Reading{Identity.Ids{None{}, Nil{}}, None{}, None{}, 0n}}), directory, home) == Done{a} : Result<&2, &2, String, String>}
  %Equal.sym(Bool, Identity.unusable(a), False{}, h) : {Identity.from_ids(file, Identity.parse.go(Nil{}, 2n, Identity.line(Identity.Reading{Identity.Ids{None{}, Nil{}}, None{}, None{}, 0n}, 1n, Bool.pick(Identity.Said, _, Identity.Said.Unusable{}, Bool.pick(Identity.Said, String.eq("author", "under"), Identity.Said.Under{Identity.unslashed(a)}, Bool.pick(Identity.Said, String.eq("author", "author"), Identity.Said.Author{a}, Identity.Said.Other{}))))), directory, home) == Done{a} : Result<&2, &2, String, String>}
  %Equal.sym(Bool, Identity.unusable(a), False{}, h) : {Bool.pick(Result<&2, &2, String, String>, _, Fail{Identity.checked.said(a, Some{file})}, Done{a}) == Done{a} : Result<&2, &2, String, String>}
  {==}

# Where the file is
# -----------------

# The configuration directory the Rust tool's `identity_path` looks in:
# `$XDG_CONFIG_HOME` where it is set and not empty, and otherwise `.config`
# in the home — `$HOME`, or `$USERPROFILE` where `$HOME` is not set.
def config(xdg: Result<&1, &1, U32 & String, String>, home: Result<&1, &1, U32 & String, String>, profile: Result<&1, &1, U32 & String, String>) -> Maybe<&2, String>:
  Maybe.or(&2, String, EditorL.unless_empty(EditorL.set(xdg)), Maybe.map(&2, String, String, h => Identity.joined(h, ".config"), Maybe.or(&2, String, EditorL.set(home), EditorL.set(profile))))

def path_home(home: Result<&1, &1, U32 & String, String>, profile: Result<&1, &1, U32 & String, String>) -> {Identity.path.home(Identity.home.of(home, profile)) == Maybe.map(&2, String, String, d => Identity.joined(d, "historica/identity"), Maybe.map(&2, String, String, h => Identity.joined(h, ".config"), Maybe.or(&2, String, EditorL.set(home), EditorL.set(profile)))) : Maybe<&2, String>}:
  match home:
    case Done{h}:
      {==}
    case Fail{e}:
      match profile:
        case Done{p}:
          {==}
        case Fail{f}:
          {==}

def path_set(x: String, home: Result<&1, &1, U32 & String, String>, profile: Result<&1, &1, U32 & String, String>) -> {Identity.path.of(Done{x}, Identity.home.of(home, profile)) == Maybe.map(&2, String, String, d => Identity.joined(d, "historica/identity"), config(Done{x}, home, profile)) : Maybe<&2, String>}:
  match x:
    case SNil{}:
      path_home(home, profile)
    case SCon{c, t}:
      {==}

# The file is `historica/identity` in that directory.
def path_is(xdg: Result<&1, &1, U32 & String, String>, home: Result<&1, &1, U32 & String, String>, profile: Result<&1, &1, U32 & String, String>) -> {Identity.path.of(xdg, Identity.home.of(home, profile)) == Maybe.map(&2, String, String, d => Identity.joined(d, "historica/identity"), config(xdg, home, profile)) : Maybe<&2, String>}:
  match xdg:
    case Done{x}:
      path_set(x, home, profile)
    case Fail{e}:
      path_home(home, profile)

# The directory `identity` makes
# ------------------------------

def app_nil(s: String) -> {s ++ SNil{} == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      Equal.cong(String, String, x => SCon{h, x}, t ++ SNil{}, t, app_nil(t))

def app_assoc(a: String, -b: String, -c: String) -> {(a ++ b) ++ c == a ++ (b ++ c) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      Equal.cong(String, String, x => SCon{h, x}, (t ++ b) ++ c, t ++ (b ++ c), app_assoc(t, b, c))

def rev_twice(xs: String, acc: String, -tail: String) -> {String.reverse.go(String.reverse.go(xs, acc), tail) == String.reverse.go(acc, xs ++ tail) : String}:
  match xs:
    case SNil{}:
      {==}
    case SCon{h, t}:
      rev_twice(t, SCon{h, acc}, tail)

def rev_rev(+s: String) -> {String.reverse(String.reverse(s)) == s : String}:
  %app_nil(s) : {String.reverse(String.reverse(s)) == _ : String}
  rev_twice(s, SNil{}, SNil{})

def rev_go_app(a: String, -b: String, acc: String) -> {String.reverse.go(a ++ b, acc) == String.reverse.go(b, String.reverse.go(a, acc)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      rev_go_app(t, b, SCon{h, acc})

# The directory above a file named `identity`, its path reversed and
# walked to the first `/`, and reversed back.
def above(+d: String) -> {String.reverse(Identity.parent.go(String.reverse(d ++ "/identity"))) == d : String}:
  %Equal.sym(String, String.reverse.go(d ++ "/identity", SNil{}), String.reverse.go("/identity", String.reverse.go(d, SNil{})), rev_go_app(d, "/identity", SNil{})) : {String.reverse(Identity.parent.go(_)) == d : String}
  rev_rev(d)

# `Path::parent` of a file named `identity` in a directory is that
# directory.
def parent_file(+d: String, hd: {String.is_empty(d) == False{} : Bool}) -> {Identity.parent(d ++ "/identity") == d : String}:
  %Equal.sym(String, String.reverse(Identity.parent.go(String.reverse(d ++ "/identity"))), d, above(d)) : {Bool.pick(String, Bool.and(String.is_empty(_), String.starts_with(d ++ "/identity", "/")), "/", _) == d : String}
  %Equal.sym(Bool, String.is_empty(d), False{}, hd) : {Bool.pick(String, Bool.and(_, String.starts_with(d ++ "/identity", "/")), "/", d) == d : String}
  {==}

def filled(b: String, +c: Char, -t: String) -> {String.is_empty(b ++ SCon{c, t}) == False{} : Bool}:
  match b:
    case SNil{}:
      {==}
    case SCon{h, u}:
      {==}

def joined_in(c: Bool, +b: String) -> {Identity.parent(Bool.pick(String, c, b ++ "historica/identity", b ++ "/historica/identity")) ++ "/identity" == Bool.pick(String, c, b ++ "historica/identity", b ++ "/historica/identity") : String}:
  match c:
    case True{}:
      %app_assoc(b, "historica", "/identity") : {Identity.parent(_) ++ "/identity" == _ : String}
      %Equal.sym(String, Identity.parent((b ++ "historica") ++ "/identity"), b ++ "historica", parent_file(b ++ "historica", filled(b, 'h', "istorica"))) : {_ ++ "/identity" == (b ++ "historica") ++ "/identity" : String}
      {==}
    case False{}:
      %app_assoc(b, "/historica", "/identity") : {Identity.parent(_) ++ "/identity" == _ : String}
      %Equal.sym(String, Identity.parent((b ++ "/historica") ++ "/identity"), b ++ "/historica", parent_file(b ++ "/historica", filled(b, '/', "historica"))) : {_ ++ "/identity" == (b ++ "/historica") ++ "/identity" : String}
      {==}

# The file `identity` writes, joined to any directory, is `identity` in the
# directory `Path::parent` names.
def joined_file(+b: String) -> {Identity.parent(Identity.joined(b, "historica/identity")) ++ "/identity" == Identity.joined(b, "historica/identity") : String}:
  joined_in(Bool.or(String.is_empty(b), String.starts_with(String.reverse.go(b, SNil{}), "/")), b)

def mapped(m: Maybe<&2, String>, +file: String, e: {Maybe.map(&2, String, String, d => Identity.joined(d, "historica/identity"), m) == Some{file} : Maybe<&2, String>}) -> {Identity.parent(file) ++ "/identity" == file : String}:
  match m:
    case None{}:
      Empty.absurd({Identity.parent(file) ++ "/identity" == file : String}, Comp.false_true(Equal.cong(Maybe<&2, String>, Bool, x => Maybe.is_some(&2, String, x), None{}, Some{file}, e)))
    case Some{+d}:
      +same = Equal.cong(Maybe<&2, String>, String, x => Maybe.default(&2, String, x, SNil{}), Some{Identity.joined(d, "historica/identity")}, Some{file}, e)
      %same : {Identity.parent(_) ++ "/identity" == _ : String}
      joined_file(d)

def makes_home(home: Result<&1, &1, U32 & String, String>, profile: Result<&1, &1, U32 & String, String>, +file: String, e: {Identity.path.home(Identity.home.of(home, profile)) == Some{file} : Maybe<&2, String>}) -> {Identity.parent(file) ++ "/identity" == file : String}:
  match home:
    case Done{+h}:
      mapped(Some{Identity.joined(h, ".config")}, file, e)
    case Fail{f}:
      match profile:
        case Done{+p}:
          mapped(Some{Identity.joined(p, ".config")}, file, e)
        case Fail{g}:
          mapped(None{}, file, e)

def makes_set(x: String, home: Result<&1, &1, U32 & String, String>, profile: Result<&1, &1, U32 & String, String>, +file: String, e: {Identity.path.of(Done{x}, Identity.home.of(home, profile)) == Some{file} : Maybe<&2, String>}) -> {Identity.parent(file) ++ "/identity" == file : String}:
  match x:
    case SNil{}:
      makes_home(home, profile, file, e)
    case SCon{+c, +t}:
      mapped(Some{SCon{c, t}}, file, e)

# The directory `identity` makes before writing is the one its file is in,
# wherever the configuration directory is.
def makes_its_directory(xdg: Result<&1, &1, U32 & String, String>, home: Result<&1, &1, U32 & String, String>, profile: Result<&1, &1, U32 & String, String>, +file: String, e: {Identity.path.of(xdg, Identity.home.of(home, profile)) == Some{file} : Maybe<&2, String>}) -> {Identity.parent(file) ++ "/identity" == file : String}:
  match xdg:
    case Done{x}:
      makes_set(x, home, profile, file, e)
    case Fail{f}:
      makes_home(home, profile, file, e)
