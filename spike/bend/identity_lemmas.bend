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
import ./editor.bend as Editor
import ./string_lemmas.bend as S

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

# Who records
# -----------

def env_set(+a: String) -> {Identity.from_env(Done{a}) == Maybe.map(&2, String, Result<&2, &2, String, String>, x => Identity.checked(x, None{}), EditorL.unless_empty(EditorL.set(Done{a}))) : Maybe<&2, Result<&2, &2, String, String>>}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, t}:
      {==}

# `var("HISTORICA_AUTHOR").ok().filter(|a| !a.is_empty())`, then `check`.
def from_env(env: Result<&1, &1, U32 & String, String>) -> {Identity.from_env(env) == Maybe.map(&2, String, Result<&2, &2, String, String>, x => Identity.checked(x, None{}), EditorL.unless_empty(EditorL.set(env))) : Maybe<&2, Result<&2, &2, String, String>>}:
  match env:
    case Done{+a}:
      env_set(a)
    case Fail{e}:
      {==}

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

# The editor's file
# -----------------

def above_message(+d: String) -> {String.reverse(Identity.parent.go(String.reverse(d ++ "/historica-message"))) == d : String}:
  %Equal.sym(String, String.reverse.go(d ++ "/historica-message", SNil{}), String.reverse.go("/historica-message", String.reverse.go(d, SNil{})), rev_go_app(d, "/historica-message", SNil{})) : {String.reverse(Identity.parent.go(_)) == d : String}
  rev_rev(d)

def parent_message(+d: String, hd: {String.is_empty(d) == False{} : Bool}) -> {Identity.parent(d ++ "/historica-message") == d : String}:
  %Equal.sym(String, String.reverse(Identity.parent.go(String.reverse(d ++ "/historica-message"))), d, above_message(d)) : {Bool.pick(String, Bool.and(String.is_empty(_), String.starts_with(d ++ "/historica-message", "/")), "/", _) == d : String}
  %Equal.sym(Bool, String.is_empty(d), False{}, hd) : {Bool.pick(String, Bool.and(_, String.starts_with(d ++ "/historica-message", "/")), "/", d) == d : String}
  {==}

def scratch_in(+t: String, +he: {String.is_empty(t) == False{} : Bool}, +hs: {String.ends_with(t, "/") == False{} : Bool}) -> {Identity.parent(Editor.scratch(Done{t})) == t : String}:
  %Equal.sym(Bool, String.is_empty(t), False{}, he) : {Identity.parent(Bool.pick(String, Bool.or(_, String.ends_with(t, "/")), t ++ "historica-message", t ++ "/historica-message")) == t : String}
  %Equal.sym(Bool, String.ends_with(t, "/"), False{}, hs) : {Identity.parent(Bool.pick(String, Bool.or(False{}, _), t ++ "historica-message", t ++ "/historica-message")) == t : String}
  parent_message(t, he)

# The file the editor is given sits directly in the temporary directory.
def scratch_parent(r: Result<&1, &1, U32 & String, String>, +h: {EditorL.tmp_ok(r) == True{} : Bool}) -> {Identity.parent(Editor.scratch(r)) == EditorL.tmpdir(r) : String}:
  match r:
    case Done{+t}:
      scratch_in(t, AL.not_of_true(String.is_empty(t), Comp.and_left(Bool.not(String.is_empty(t)), Bool.not(String.ends_with(t, "/")), h)), AL.not_of_true(String.ends_with(t, "/"), Comp.and_right(Bool.not(String.is_empty(t)), Bool.not(String.ends_with(t, "/")), h)))
    case Fail{e}:
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

# The file's blocks
# -----------------

# A file's text from its lines, each ended by a newline.
def text(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      SNil{}
    case +l <> rest:
      l ++ SCon{'\n', text(rest)}

# The block stating the default author, and the blank line that ends it.
def default.lines(d: Maybe<&2, String>) -> List<&2, String>:
  match d:
    case None{}:
      Nil{}
    case Some{+a}:
      ["author " ++ a, SNil{}]

# A block for each directory: `under` it, then its author, and the blank
# line that ends it.
def under.lines(us: List<&2, T.Split>) -> List<&2, String>:
  match us:
    case Nil{}:
      Nil{}
    case T.Split{+dir, +a} <> rest:
      ("under " ++ dir) <> ("author " ++ a) <> SNil{} <> under.lines(rest)

# The lines of a file stating a default author, where there is one, and an
# author for each directory, in order.
def lines(d: Maybe<&2, String>, us: List<&2, T.Split>) -> List<&2, String>:
  List.append(&2, String, default.lines(d), under.lines(us))

# Whether one of these directories is `dir`.
def held(ds: List<&2, String>, +dir: String) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case +h <> rest:
      Bool.or(String.eq(h, dir), held(rest, dir))

def fits.default(d: Maybe<&2, String>) -> Bool:
  match d:
    case None{}:
      True{}
    case Some{+a}:
      Bool.not(Identity.unusable(a))

# Blocks the reading takes as written: every value one a revision can hold,
# each directory spelled without a trailing `/` — which the reading drops —
# and named by no block before it.
def fits.under(us: List<&2, T.Split>, +seen: List<&2, String>) -> Bool:
  match us:
    case Nil{}:
      True{}
    case T.Split{+dir, +a} <> rest:
      Bool.and(Bool.not(Identity.unusable(dir)), Bool.and(Bool.not(Identity.unusable(a)), Bool.and(Bool.not(String.ends_with(dir, "/")), Bool.and(Bool.not(held(seen, dir)), fits.under(rest, List.append(&2, String, seen, [dir]))))))

def fits(d: Maybe<&2, String>, us: List<&2, T.Split>) -> Bool:
  Bool.and(fits.default(d), fits.under(us, Nil{}))

# The number the line after these is read as, from `at`.
def after(ls: List<&2, String>, +at: Nat) -> Nat:
  match ls:
    case Nil{}:
      at
    case l <> rest:
      after(rest, 1n+at)

# From text to lines
# ------------------

# A line `lines()` gives back as it is: no newline in it, and no carriage
# return at its end.
def good(+l: String) -> Bool:
  Bool.and(BmL.nonl(l), Bool.not(String.ends_with(l, "\r")))

def all_good(ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case +l <> rest:
      Bool.and(good(l), all_good(rest))

def split_text(ls: List<&2, String>, +h: {all_good(ls) == True{} : Bool}) -> {String.split(text(ls), '\n') == List.append(&2, String, ls, [SNil{}]) : List<&2, String>}:
  match ls:
    case Nil{}:
      {==}
    case +l <> rest:
      +hl = Comp.and_left(good(l), all_good(rest), h)
      %Equal.sym(List<&2, String>, String.split(l ++ SCon{'\n', text(rest)}, '\n'), l <> String.split(text(rest), '\n'), BmL.split_nl(l, text(rest), Comp.and_left(BmL.nonl(l), Bool.not(String.ends_with(l, "\r")), hl))) : {_ == l <> List.append(&2, String, rest, [SNil{}]) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, x => l <> x, String.split(text(rest), '\n'), List.append(&2, String, rest, [SNil{}]), split_text(rest, Comp.and_right(good(l), all_good(rest), h)))

def unreturned(+l: String, h: {String.ends_with(l, "\r") == False{} : Bool}) -> {Folder.unreturned(l) == l : String}:
  %Equal.sym(Bool, String.ends_with(l, "\r"), False{}, h) : {Bool.pick(String, _, String.take(l, Nat.sub(String.length(l), 1n)), l) == l : String}
  {==}

def good_unreturned(+l: String, +hl: {good(l) == True{} : Bool}) -> {Folder.unreturned(l) == l : String}:
  unreturned(l, AL.not_of_true(String.ends_with(l, "\r"), Comp.and_right(BmL.nonl(l), Bool.not(String.ends_with(l, "\r")), hl)))

def trimmed_from(rest: List<&2, String>, +l: String, +hl: {good(l) == True{} : Bool}, +h: {all_good(rest) == True{} : Bool}) -> {Folder.lines.trimmed(l <> List.append(&2, String, rest, [SNil{}])) == l <> rest : List<&2, String>}:
  match rest:
    case Nil{}:
      %Equal.sym(String, Folder.unreturned(l), l, good_unreturned(l, hl)) : {_ <> Nil{} == [l] : List<&2, String>}
      {==}
    case +x <> r:
      %Equal.sym(String, Folder.unreturned(l), l, good_unreturned(l, hl)) : {_ <> Folder.lines.trimmed(x <> List.append(&2, String, r, [SNil{}])) == l <> x <> r : List<&2, String>}
      %Equal.sym(List<&2, String>, Folder.lines.trimmed(x <> List.append(&2, String, r, [SNil{}])), x <> r, trimmed_from(r, x, Comp.and_left(good(x), all_good(r), h), Comp.and_right(good(x), all_good(r), h))) : {l <> _ == l <> x <> r : List<&2, String>}
      {==}

def trimmed_text(ls: List<&2, String>, +h: {all_good(ls) == True{} : Bool}) -> {Folder.lines.trimmed(List.append(&2, String, ls, [SNil{}])) == ls : List<&2, String>}:
  match ls:
    case Nil{}:
      {==}
    case +l <> rest:
      trimmed_from(rest, l, Comp.and_left(good(l), all_good(rest), h), Comp.and_right(good(l), all_good(rest), h))

# What `lines()` reads of a file's text is its lines.
def text_lines(+ls: List<&2, String>, +h: {all_good(ls) == True{} : Bool}) -> {Folder.lines.trimmed(String.split(text(ls), '\n')) == ls : List<&2, String>}:
  %Equal.sym(List<&2, String>, String.split(text(ls), '\n'), List.append(&2, String, ls, [SNil{}]), split_text(ls, h)) : {Folder.lines.trimmed(_) == ls : List<&2, String>}
  trimmed_text(ls, h)

# The walk over the blocks
# ------------------------

def said_author(+a: String, h: {Identity.unusable(a) == False{} : Bool}) -> {Identity.said("author " ++ a) == Identity.Said.Author{a} : Identity.Said}:
  %Equal.sym(Bool, Identity.unusable(a), False{}, h) : {Bool.pick(Identity.Said, _, Identity.Said.Unusable{}, Bool.pick(Identity.Said, String.eq("author", "under"), Identity.Said.Under{Identity.unslashed(a)}, Bool.pick(Identity.Said, String.eq("author", "author"), Identity.Said.Author{a}, Identity.Said.Other{}))) == Identity.Said.Author{a} : Identity.Said}
  {==}

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

def trim_none(r: String, h: {String.starts_with(r, "/") == False{} : Bool}) -> {Folder.trim.go(r, Folder.slash_first(r)) == String.reverse(r) : String}:
  match r:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.trans(Bool, False{}, String.starts_with.if(t, SNil{}, Char.is_eq(c, '/')), Char.is_eq(c, '/'), Equal.sym(Bool, String.starts_with.if(t, SNil{}, Char.is_eq(c, '/')), False{}, h), sw_if(t, Char.is_eq(c, '/'))) : {Folder.trim.go(SCon{c, t}, _) == String.reverse(SCon{c, t}) : String}
      {==}

# A directory written without a trailing `/` is read as written.
def unslashed(+dir: String, h: {String.ends_with(dir, "/") == False{} : Bool}) -> {Identity.unslashed(dir) == dir : String}:
  %Equal.sym(String, Folder.trim.go(String.reverse(dir), Folder.slash_first(String.reverse(dir))), String.reverse(String.reverse(dir)), trim_none(String.reverse(dir), h)) : {_ == dir : String}
  rev_rev(dir)

def said_under(+dir: String, h: {Identity.unusable(dir) == False{} : Bool}, hs: {String.ends_with(dir, "/") == False{} : Bool}) -> {Identity.said("under " ++ dir) == Identity.Said.Under{dir} : Identity.Said}:
  %Equal.sym(Bool, Identity.unusable(dir), False{}, h) : {Bool.pick(Identity.Said, _, Identity.Said.Unusable{}, Bool.pick(Identity.Said, String.eq("under", "under"), Identity.Said.Under{Identity.unslashed(dir)}, Bool.pick(Identity.Said, String.eq("under", "author"), Identity.Said.Author{dir}, Identity.Said.Other{}))) == Identity.Said.Under{dir} : Identity.Said}
  %Equal.sym(String, Identity.unslashed(dir), dir, unslashed(dir, hs)) : {Identity.Said.Under{_} == Identity.Said.Under{dir} : Identity.Said}
  {==}

# An `author` line read, in a block that has none yet.
def go_author(-rest: List<&2, String>, -p: Nat, -ids: Identity.Ids, h: Maybe<&2, String>, -st: Nat, +a: String, +ha: {Identity.unusable(a) == False{} : Bool}) -> {Identity.parse.go(("author " ++ a) <> rest, 1n+p, Done{Identity.Reading{ids, h, None{}, st}}) == Identity.parse.go(rest, 1n+1n+p, Done{Identity.Reading{ids, h, Some{a}, Identity.begun(st, 1n+p)}}) : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  match h:
    case None{}:
      Equal.cong(Identity.Said, Result<&2, &2, Identity.Malformed, Identity.Ids>, s => Identity.parse.go(rest, 1n+1n+p, Identity.line(Identity.Reading{ids, None{}, None{}, st}, 1n+p, s)), Identity.said("author " ++ a), Identity.Said.Author{a}, said_author(a, ha))
    case Some{d}:
      Equal.cong(Identity.Said, Result<&2, &2, Identity.Malformed, Identity.Ids>, s => Identity.parse.go(rest, 1n+1n+p, Identity.line(Identity.Reading{ids, Some{d}, None{}, st}, 1n+p, s)), Identity.said("author " ++ a), Identity.Said.Author{a}, said_author(a, ha))

# An `under` line read, opening a block.
def go_under(-rest: List<&2, String>, -p: Nat, -ids: Identity.Ids, +dir: String, +hd: {Identity.unusable(dir) == False{} : Bool}, +hs: {String.ends_with(dir, "/") == False{} : Bool}) -> {Identity.parse.go(("under " ++ dir) <> rest, 1n+p, Done{Identity.Reading{ids, None{}, None{}, 0n}}) == Identity.parse.go(rest, 1n+1n+p, Done{Identity.Reading{ids, Some{dir}, None{}, 1n+p}}) : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  Equal.cong(Identity.Said, Result<&2, &2, Identity.Malformed, Identity.Ids>, s => Identity.parse.go(rest, 1n+1n+p, Identity.line(Identity.Reading{ids, None{}, None{}, 0n}, 1n+p, s)), Identity.said("under " ++ dir), Identity.Said.Under{dir}, said_under(dir, hd, hs))

def or_comm(a: Bool, b: Bool) -> {Bool.or(a, b) == Bool.or(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def or_f(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def claimed_app(prev: List<&2, T.Split>, +dir: String, -a: String, +x: String) -> {Identity.claimed(List.append(&2, T.Split, prev, [T.Split{dir, a}]), x) == Bool.or(Identity.claimed(prev, x), String.eq(dir, x)) : Bool}:
  match prev:
    case Nil{}:
      or_f(String.eq(dir, x))
    case T.Split{+h, b} <> rest:
      %Equal.sym(Bool, Identity.claimed(List.append(&2, T.Split, rest, [T.Split{dir, a}]), x), Bool.or(Identity.claimed(rest, x), String.eq(dir, x)), claimed_app(rest, dir, a, x)) : {Bool.or(String.eq(h, x), _) == Bool.or(Bool.or(String.eq(h, x), Identity.claimed(rest, x)), String.eq(dir, x)) : Bool}
      AL.or_assoc(String.eq(h, x), Identity.claimed(rest, x), String.eq(dir, x))

def sapp_nil(xs: List<&2, T.Split>) -> {List.append(&2, T.Split, xs, Nil{}) == xs : List<&2, T.Split>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      Equal.cong(List<&2, T.Split>, List<&2, T.Split>, l => x <> l, List.append(&2, T.Split, rest, Nil{}), rest, sapp_nil(rest))

def sapp_assoc(xs: List<&2, T.Split>, -ys: List<&2, T.Split>, -zs: List<&2, T.Split>) -> {List.append(&2, T.Split, List.append(&2, T.Split, xs, ys), zs) == List.append(&2, T.Split, xs, List.append(&2, T.Split, ys, zs)) : List<&2, T.Split>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      Equal.cong(List<&2, T.Split>, List<&2, T.Split>, l => x <> l, List.append(&2, T.Split, List.append(&2, T.Split, rest, ys), zs), List.append(&2, T.Split, rest, List.append(&2, T.Split, ys, zs)), sapp_assoc(rest, ys, zs))

# The blank line ending a directory's block files its author under it.
def go_close(+more: List<&2, String>, +p: Nat, +df: Maybe<&2, String>, +prev: List<&2, T.Split>, +dir: String, +a: String, +hc: {Identity.claimed(prev, dir) == False{} : Bool}) -> {Identity.parse.go(SNil{} <> more, 1n+1n+1n+p, Done{Identity.Reading{Identity.Ids{df, prev}, Some{dir}, Some{a}, 1n+p}}) == Identity.parse.go(more, 1n+1n+1n+1n+p, Done{Identity.Reading{Identity.Ids{df, List.append(&2, T.Split, prev, [T.Split{dir, a}])}, None{}, None{}, 0n}}) : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  Equal.cong(Bool, Result<&2, &2, Identity.Malformed, Identity.Ids>, c => Identity.parse.go(more, 1n+1n+1n+1n+p, Identity.closed(Bool.pick(Result<&2, &2, Identity.Malformed, Identity.Ids>, c, Fail{Identity.Malformed{Nat.max(1n+p, 1n), "two blocks claim one directory"}}, Done{Identity.Ids{df, List.append(&2, T.Split, prev, [T.Split{dir, a}])}}))), Identity.claimed(prev, dir), False{}, hc)

def fit_dir(+dir: String, +a: String, +seen: List<&2, String>, -rest: List<&2, T.Split>, +hf: {fits.under(T.Split{dir, a} <> rest, seen) == True{} : Bool}) -> {Identity.unusable(dir) == False{} : Bool}:
  AL.not_of_true(Identity.unusable(dir), Comp.and_left(Bool.not(Identity.unusable(dir)), Bool.and(Bool.not(Identity.unusable(a)), Bool.and(Bool.not(String.ends_with(dir, "/")), Bool.and(Bool.not(held(seen, dir)), fits.under(rest, List.append(&2, String, seen, [dir]))))), hf))

def fit_rest(+dir: String, +a: String, +seen: List<&2, String>, -rest: List<&2, T.Split>, +hf: {fits.under(T.Split{dir, a} <> rest, seen) == True{} : Bool}) -> {Bool.and(Bool.not(Identity.unusable(a)), Bool.and(Bool.not(String.ends_with(dir, "/")), Bool.and(Bool.not(held(seen, dir)), fits.under(rest, List.append(&2, String, seen, [dir]))))) == True{} : Bool}:
  Comp.and_right(Bool.not(Identity.unusable(dir)), Bool.and(Bool.not(Identity.unusable(a)), Bool.and(Bool.not(String.ends_with(dir, "/")), Bool.and(Bool.not(held(seen, dir)), fits.under(rest, List.append(&2, String, seen, [dir]))))), hf)

# The directories blocks are for.
def dirs(us: List<&2, T.Split>) -> List<&2, String>:
  match us:
    case Nil{}:
      Nil{}
    case T.Split{d, a} <> rest:
      d <> dirs(rest)

def claimed_held(us: List<&2, T.Split>, +x: String) -> {Identity.claimed(us, x) == held(dirs(us), x) : Bool}:
  match us:
    case Nil{}:
      {==}
    case T.Split{+h, a} <> rest:
      Equal.cong(Bool, Bool, c => Bool.or(String.eq(h, x), c), Identity.claimed(rest, x), held(dirs(rest), x), claimed_held(rest, x))

def dirs_app(us: List<&2, T.Split>, +dir: String, -a: String) -> {dirs(List.append(&2, T.Split, us, [T.Split{dir, a}])) == List.append(&2, String, dirs(us), [dir]) : List<&2, String>}:
  match us:
    case Nil{}:
      {==}
    case T.Split{+h, b} <> rest:
      Equal.cong(List<&2, String>, List<&2, String>, l => h <> l, dirs(List.append(&2, T.Split, rest, [T.Split{dir, a}])), List.append(&2, String, dirs(rest), [dir]), dirs_app(rest, dir, a))

# Blocks for directories, read one after another from a closed block: each
# files its author under its directory, which no block before it named.
def under_blocks(us: List<&2, T.Split>, +df: Maybe<&2, String>, +prev: List<&2, T.Split>, +p: Nat, +more: List<&2, String>, +hf: {fits.under(us, dirs(prev)) == True{} : Bool}) -> {Identity.parse.go(List.append(&2, String, under.lines(us), more), 1n+p, Done{Identity.Reading{Identity.Ids{df, prev}, None{}, None{}, 0n}}) == Identity.parse.go(more, after(under.lines(us), 1n+p), Done{Identity.Reading{Identity.Ids{df, List.append(&2, T.Split, prev, us)}, None{}, None{}, 0n}}) : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  match us:
    case Nil{}:
      %Equal.sym(List<&2, T.Split>, List.append(&2, T.Split, prev, Nil{}), prev, sapp_nil(prev)) : {Identity.parse.go(more, 1n+p, Done{Identity.Reading{Identity.Ids{df, prev}, None{}, None{}, 0n}}) == Identity.parse.go(more, 1n+p, Done{Identity.Reading{Identity.Ids{df, _}, None{}, None{}, 0n}}) : Result<&2, &2, Identity.Malformed, Identity.Ids>}
      {==}
    case T.Split{+dir, +a} <> +rest:
      +seen = dirs(prev)
      +hd = fit_dir(dir, a, seen, rest, hf)
      +h1 = fit_rest(dir, a, seen, rest, hf)
      +ha = AL.not_of_true(Identity.unusable(a), Comp.and_left(Bool.not(Identity.unusable(a)), Bool.and(Bool.not(String.ends_with(dir, "/")), Bool.and(Bool.not(held(seen, dir)), fits.under(rest, List.append(&2, String, seen, [dir])))), h1))
      +h2 = Comp.and_right(Bool.not(Identity.unusable(a)), Bool.and(Bool.not(String.ends_with(dir, "/")), Bool.and(Bool.not(held(seen, dir)), fits.under(rest, List.append(&2, String, seen, [dir])))), h1)
      +hs = AL.not_of_true(String.ends_with(dir, "/"), Comp.and_left(Bool.not(String.ends_with(dir, "/")), Bool.and(Bool.not(held(seen, dir)), fits.under(rest, List.append(&2, String, seen, [dir]))), h2))
      +h3 = Comp.and_right(Bool.not(String.ends_with(dir, "/")), Bool.and(Bool.not(held(seen, dir)), fits.under(rest, List.append(&2, String, seen, [dir]))), h2)
      +hn = AL.not_of_true(held(seen, dir), Comp.and_left(Bool.not(held(seen, dir)), fits.under(rest, List.append(&2, String, seen, [dir])), h3))
      +s = {T.Split{dir, a} : T.Split}
      +hr = Equal.trans(Bool, fits.under(rest, dirs(List.append(&2, T.Split, prev, [s]))), fits.under(rest, List.append(&2, String, seen, [dir])), True{},
        Equal.cong(List<&2, String>, Bool, l => fits.under(rest, l), dirs(List.append(&2, T.Split, prev, [s])), List.append(&2, String, seen, [dir]), dirs_app(prev, dir, a)),
        Comp.and_right(Bool.not(held(seen, dir)), fits.under(rest, List.append(&2, String, seen, [dir])), h3))
      +X = List.append(&2, String, under.lines(rest), more)
      +A0 = Identity.parse.go(("under " ++ dir) <> ("author " ++ a) <> SNil{} <> X, 1n+p, Done{Identity.Reading{Identity.Ids{df, prev}, None{}, None{}, 0n}})
      +A1 = Identity.parse.go(("author " ++ a) <> SNil{} <> X, 1n+1n+p, Done{Identity.Reading{Identity.Ids{df, prev}, Some{dir}, None{}, 1n+p}})
      +A2 = Identity.parse.go(SNil{} <> X, 1n+1n+1n+p, Done{Identity.Reading{Identity.Ids{df, prev}, Some{dir}, Some{a}, 1n+p}})
      +A3 = Identity.parse.go(X, 1n+1n+1n+1n+p, Done{Identity.Reading{Identity.Ids{df, List.append(&2, T.Split, prev, [s])}, None{}, None{}, 0n}})
      +A4 = Identity.parse.go(more, after(under.lines(rest), 1n+1n+1n+1n+p), Done{Identity.Reading{Identity.Ids{df, List.append(&2, T.Split, List.append(&2, T.Split, prev, [s]), rest)}, None{}, None{}, 0n}})
      +A5 = Identity.parse.go(more, after(under.lines(rest), 1n+1n+1n+1n+p), Done{Identity.Reading{Identity.Ids{df, List.append(&2, T.Split, prev, s <> rest)}, None{}, None{}, 0n}})
      +step1 = go_under(("author " ++ a) <> SNil{} <> X, p, Identity.Ids{df, prev}, dir, hd, hs)
      +step2 = go_author(SNil{} <> X, 1n+p, Identity.Ids{df, prev}, Some{dir}, 1n+p, a, ha)
      +step3 = go_close(X, p, df, prev, dir, a, Equal.trans(Bool, Identity.claimed(prev, dir), held(seen, dir), False{}, claimed_held(prev, dir), hn))
      +step4 = under_blocks(rest, df, List.append(&2, T.Split, prev, [s]), 1n+1n+1n+p, more, hr)
      +step5 = Equal.cong(List<&2, T.Split>, Result<&2, &2, Identity.Malformed, Identity.Ids>, l => Identity.parse.go(more, after(under.lines(rest), 1n+1n+1n+1n+p), Done{Identity.Reading{Identity.Ids{df, l}, None{}, None{}, 0n}}), List.append(&2, T.Split, List.append(&2, T.Split, prev, [s]), rest), List.append(&2, T.Split, prev, s <> rest), sapp_assoc(prev, [s], rest))
      Equal.trans(Result<&2, &2, Identity.Malformed, Identity.Ids>, A0, A1, A5, step1,
        Equal.trans(Result<&2, &2, Identity.Malformed, Identity.Ids>, A1, A2, A5, step2,
          Equal.trans(Result<&2, &2, Identity.Malformed, Identity.Ids>, A2, A3, A5, step3,
            Equal.trans(Result<&2, &2, Identity.Malformed, Identity.Ids>, A3, A4, A5, step4, step5))))

# A block for the default author, read from the file's first line.
def default_block(d: Maybe<&2, String>, +more: List<&2, String>, +hf: {fits.default(d) == True{} : Bool}) -> {Identity.parse.go(List.append(&2, String, default.lines(d), more), 1n, Done{Identity.Reading{Identity.Ids{None{}, Nil{}}, None{}, None{}, 0n}}) == Identity.parse.go(more, after(default.lines(d), 1n), Done{Identity.Reading{Identity.Ids{d, Nil{}}, None{}, None{}, 0n}}) : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  match d:
    case None{}:
      {==}
    case Some{+a}:
      go_author(SNil{} <> more, 0n, Identity.Ids{None{}, Nil{}}, None{}, 0n, a, AL.not_of_true(Identity.unusable(a), hf))

# The file's blocks, read from its first line: the reading has the default
# author and each directory's, with the line after them next.
def go_lines(d: Maybe<&2, String>, +us: List<&2, T.Split>, +more: List<&2, String>, +hf: {fits(d, us) == True{} : Bool}) -> {Identity.parse.go(List.append(&2, String, lines(d, us), more), 1n, Done{Identity.Reading{Identity.Ids{None{}, Nil{}}, None{}, None{}, 0n}}) == Identity.parse.go(more, after(lines(d, us), 1n), Done{Identity.Reading{Identity.Ids{d, us}, None{}, None{}, 0n}}) : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  match d:
    case None{}:
      under_blocks(us, None{}, Nil{}, 0n, more, hf)
    case Some{+a}:
      +ha = Comp.and_left(Bool.not(Identity.unusable(a)), fits.under(us, Nil{}), hf)
      +hu = Comp.and_right(Bool.not(Identity.unusable(a)), fits.under(us, Nil{}), hf)
      +Y = List.append(&2, String, under.lines(us), more)
      Equal.trans(Result<&2, &2, Identity.Malformed, Identity.Ids>, Identity.parse.go(("author " ++ a) <> SNil{} <> Y, 1n, Done{Identity.Reading{Identity.Ids{None{}, Nil{}}, None{}, None{}, 0n}}), Identity.parse.go(Y, 3n, Done{Identity.Reading{Identity.Ids{Some{a}, Nil{}}, None{}, None{}, 0n}}), Identity.parse.go(more, after(under.lines(us), 3n), Done{Identity.Reading{Identity.Ids{Some{a}, us}, None{}, None{}, 0n}}),
        default_block(Some{a}, Y, ha),
        under_blocks(us, Some{a}, Nil{}, 2n, more, hu))

def usable_quiet(+v: String, +h: {Identity.unusable(v) == False{} : Bool}) -> {quiet(v) == False{} : Bool}:
  AL.or_false_r(Folder.untrimmed(v), quiet(v), h)

def good_author(+a: String, +h: {Identity.unusable(a) == False{} : Bool}) -> {good("author " ++ a) == True{} : Bool}:
  AL.and_intro(BmL.nonl("author " ++ a), Bool.not(String.ends_with("author " ++ a, "\r")), nonl(a, usable_quiet(a, h)), AL.not_true(String.ends_with("author " ++ a, "\r"), cr_rev(a, " rohtua", usable_quiet(a, h), {==})))

def good_under(+d: String, +h: {Identity.unusable(d) == False{} : Bool}) -> {good("under " ++ d) == True{} : Bool}:
  AL.and_intro(BmL.nonl("under " ++ d), Bool.not(String.ends_with("under " ++ d, "\r")), nonl(d, usable_quiet(d, h)), AL.not_true(String.ends_with("under " ++ d, "\r"), cr_rev(d, " rednu", usable_quiet(d, h), {==})))

def under_good(us: List<&2, T.Split>, +seen: List<&2, String>, +hf: {fits.under(us, seen) == True{} : Bool}) -> {all_good(under.lines(us)) == True{} : Bool}:
  match us:
    case Nil{}:
      {==}
    case T.Split{+dir, +a} <> +rest:
      +hd = fit_dir(dir, a, seen, rest, hf)
      +h1 = fit_rest(dir, a, seen, rest, hf)
      +ha = AL.not_of_true(Identity.unusable(a), Comp.and_left(Bool.not(Identity.unusable(a)), Bool.and(Bool.not(String.ends_with(dir, "/")), Bool.and(Bool.not(held(seen, dir)), fits.under(rest, List.append(&2, String, seen, [dir])))), h1))
      +h2 = Comp.and_right(Bool.not(Identity.unusable(a)), Bool.and(Bool.not(String.ends_with(dir, "/")), Bool.and(Bool.not(held(seen, dir)), fits.under(rest, List.append(&2, String, seen, [dir])))), h1)
      +h3 = Comp.and_right(Bool.not(String.ends_with(dir, "/")), Bool.and(Bool.not(held(seen, dir)), fits.under(rest, List.append(&2, String, seen, [dir]))), h2)
      +hr = Comp.and_right(Bool.not(held(seen, dir)), fits.under(rest, List.append(&2, String, seen, [dir])), h3)
      AL.and_intro(good("under " ++ dir), all_good(("author " ++ a) <> SNil{} <> under.lines(rest)), good_under(dir, hd),
        AL.and_intro(good("author " ++ a), all_good(SNil{} <> under.lines(rest)), good_author(a, ha), under_good(rest, List.append(&2, String, seen, [dir]), hr)))

# Every line of such a file is one `lines()` gives back as written.
def good_lines(d: Maybe<&2, String>, +us: List<&2, T.Split>, +hf: {fits(d, us) == True{} : Bool}) -> {all_good(lines(d, us)) == True{} : Bool}:
  match d:
    case None{}:
      under_good(us, Nil{}, hf)
    case Some{+a}:
      AL.and_intro(good("author " ++ a), all_good(SNil{} <> under.lines(us)), good_author(a, AL.not_of_true(Identity.unusable(a), Comp.and_left(Bool.not(Identity.unusable(a)), fits.under(us, Nil{}), hf))), under_good(us, Nil{}, Comp.and_right(Bool.not(Identity.unusable(a)), fits.under(us, Nil{}), hf)))

def lapp_nil(xs: List<&2, String>) -> {List.append(&2, String, xs, Nil{}) == xs : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      Equal.cong(List<&2, String>, List<&2, String>, l => x <> l, List.append(&2, String, rest, Nil{}), rest, lapp_nil(rest))

# A file of blocks reads back as the blocks it states: the default author
# and every directory's, in order.
def reads_blocks(+d: Maybe<&2, String>, +us: List<&2, T.Split>, +hf: {fits(d, us) == True{} : Bool}) -> {Identity.parse(text(lines(d, us))) == Done{Identity.Ids{d, us}} : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  +ls = lines(d, us)
  %Equal.sym(List<&2, String>, Folder.lines.trimmed(String.split(text(ls), '\n')), ls, text_lines(ls, good_lines(d, us, hf))) : {Identity.parse.go(_, 1n, Done{Identity.Reading{Identity.Ids{None{}, Nil{}}, None{}, None{}, 0n}}) == Done{Identity.Ids{d, us}} : Result<&2, &2, Identity.Malformed, Identity.Ids>}
  %lapp_nil(ls) : {Identity.parse.go(_, 1n, Done{Identity.Reading{Identity.Ids{None{}, Nil{}}, None{}, None{}, 0n}}) == Done{Identity.Ids{d, us}} : Result<&2, &2, Identity.Malformed, Identity.Ids>}
  go_lines(d, us, Nil{}, hf)

# What follows the blocks
# -----------------------

def all_good_app(xs: List<&2, String>, -ys: List<&2, String>, +hx: {all_good(xs) == True{} : Bool}, hy: {all_good(ys) == True{} : Bool}) -> {all_good(List.append(&2, String, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +x <> rest:
      AL.and_intro(good(x), all_good(List.append(&2, String, rest, ys)), Comp.and_left(good(x), all_good(rest), hx), all_good_app(rest, ys, Comp.and_right(good(x), all_good(rest), hx), hy))

def after_succ(ls: List<&2, String>, +at: Nat) -> {after(ls, 1n+at) == 1n+after(ls, at) : Nat}:
  match ls:
    case Nil{}:
      {==}
    case l <> rest:
      after_succ(rest, 1n+at)

def after_zero(ls: List<&2, String>) -> {after(ls, 0n) == List.length(&2, String, ls) : Nat}:
  match ls:
    case Nil{}:
      {==}
    case l <> +rest:
      %Equal.sym(Nat, after(rest, 1n), 1n+after(rest, 0n), after_succ(rest, 0n)) : {_ == 1n+List.length(&2, String, rest) : Nat}
      Equal.cong(Nat, Nat, n => 1n+n, after(rest, 0n), List.length(&2, String, rest), after_zero(rest))

# The line after the blocks is numbered one past how many lines they take.
def after_one(+ls: List<&2, String>) -> {after(ls, 1n) == 1n+List.length(&2, String, ls) : Nat}:
  Equal.trans(Nat, after(ls, 1n), 1n+after(ls, 0n), 1n+List.length(&2, String, ls), after_succ(ls, 0n), Equal.cong(Nat, Nat, n => 1n+n, after(ls, 0n), List.length(&2, String, ls), after_zero(ls)))

# Whatever lines follow the blocks are read from a closed block holding
# every author the blocks state, numbered from the line after them.
def after_blocks(+d: Maybe<&2, String>, +us: List<&2, T.Split>, +bad: List<&2, String>, +hf: {fits(d, us) == True{} : Bool}, +hb: {all_good(bad) == True{} : Bool}) -> {Identity.parse(text(List.append(&2, String, lines(d, us), bad))) == Identity.parse.go(bad, 1n+List.length(&2, String, lines(d, us)), Done{Identity.Reading{Identity.Ids{d, us}, None{}, None{}, 0n}}) : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  +ls = List.append(&2, String, lines(d, us), bad)
  %Equal.sym(List<&2, String>, Folder.lines.trimmed(String.split(text(ls), '\n')), ls, text_lines(ls, all_good_app(lines(d, us), bad, good_lines(d, us, hf), hb))) : {Identity.parse.go(_, 1n, Done{Identity.Reading{Identity.Ids{None{}, Nil{}}, None{}, None{}, 0n}}) == Identity.parse.go(bad, 1n+List.length(&2, String, lines(d, us)), Done{Identity.Reading{Identity.Ids{d, us}, None{}, None{}, 0n}}) : Result<&2, &2, Identity.Malformed, Identity.Ids>}
  Equal.trans(Result<&2, &2, Identity.Malformed, Identity.Ids>, Identity.parse.go(ls, 1n, Done{Identity.Reading{Identity.Ids{None{}, Nil{}}, None{}, None{}, 0n}}), Identity.parse.go(bad, after(lines(d, us), 1n), Done{Identity.Reading{Identity.Ids{d, us}, None{}, None{}, 0n}}), Identity.parse.go(bad, 1n+List.length(&2, String, lines(d, us)), Done{Identity.Reading{Identity.Ids{d, us}, None{}, None{}, 0n}}),
    go_lines(d, us, bad, hf),
    Equal.cong(Nat, Result<&2, &2, Identity.Malformed, Identity.Ids>, n => Identity.parse.go(bad, n, Done{Identity.Reading{Identity.Ids{d, us}, None{}, None{}, 0n}}), after(lines(d, us), 1n), 1n+List.length(&2, String, lines(d, us)), after_one(lines(d, us))))

# Whether a string holds a control character.
def has_control(+s: String) -> Bool:
  quiet(s)

def said_under_any(+dir: String, h: {Identity.unusable(dir) == False{} : Bool}) -> {Identity.said("under " ++ dir) == Identity.Said.Under{Identity.unslashed(dir)} : Identity.Said}:
  %Equal.sym(Bool, Identity.unusable(dir), False{}, h) : {Bool.pick(Identity.Said, _, Identity.Said.Unusable{}, Bool.pick(Identity.Said, String.eq("under", "under"), Identity.Said.Under{Identity.unslashed(dir)}, Bool.pick(Identity.Said, String.eq("under", "author"), Identity.Said.Author{dir}, Identity.Said.Other{}))) == Identity.Said.Under{Identity.unslashed(dir)} : Identity.Said}
  {==}

def go_under_any(-rest: List<&2, String>, -p: Nat, -ids: Identity.Ids, +dir: String, +hd: {Identity.unusable(dir) == False{} : Bool}) -> {Identity.parse.go(("under " ++ dir) <> rest, 1n+p, Done{Identity.Reading{ids, None{}, None{}, 0n}}) == Identity.parse.go(rest, 1n+1n+p, Done{Identity.Reading{ids, Some{Identity.unslashed(dir)}, None{}, 1n+p}}) : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  Equal.cong(Identity.Said, Result<&2, &2, Identity.Malformed, Identity.Ids>, s => Identity.parse.go(rest, 1n+1n+p, Identity.line(Identity.Reading{ids, None{}, None{}, 0n}, 1n+p, s)), Identity.said("under " ++ dir), Identity.Said.Under{Identity.unslashed(dir)}, said_under_any(dir, hd))

def max_one(p: Nat) -> {Nat.max(1n+p, 1n) == 1n+p : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      {==}

# A block of two `author` lines is refused at the second.
def two_authors(-ids: Identity.Ids, +p: Nat, +a: String, +b: String, +ha: {Identity.unusable(a) == False{} : Bool}, +hb: {Identity.unusable(b) == False{} : Bool}) -> {Identity.parse.go(["author " ++ a, "author " ++ b], 1n+p, Done{Identity.Reading{ids, None{}, None{}, 0n}}) == Fail{Identity.Malformed{1n+1n+p, "a block states one author"}} : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  Equal.trans(Result<&2, &2, Identity.Malformed, Identity.Ids>, Identity.parse.go(["author " ++ a, "author " ++ b], 1n+p, Done{Identity.Reading{ids, None{}, None{}, 0n}}), Identity.parse.go(["author " ++ b], 1n+1n+p, Done{Identity.Reading{ids, None{}, Some{a}, 1n+p}}), Fail{Identity.Malformed{1n+1n+p, "a block states one author"}},
    go_author(["author " ++ b], p, ids, None{}, 0n, a, ha),
    Equal.cong(Identity.Said, Result<&2, &2, Identity.Malformed, Identity.Ids>, s => Identity.parse.go(Nil{}, 1n+1n+1n+p, Identity.line(Identity.Reading{ids, None{}, Some{a}, 1n+p}, 1n+1n+p, s)), Identity.said("author " ++ b), Identity.Said.Author{b}, said_author(b, hb)))

# An `under` line after an `author` line is refused where it stands.
def under_after_author(-ids: Identity.Ids, +p: Nat, +a: String, +dir: String, +ha: {Identity.unusable(a) == False{} : Bool}, +hd: {Identity.unusable(dir) == False{} : Bool}) -> {Identity.parse.go(["author " ++ a, "under " ++ dir], 1n+p, Done{Identity.Reading{ids, None{}, None{}, 0n}}) == Fail{Identity.Malformed{1n+1n+p, "`under` heads a block, so it comes first"}} : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  Equal.trans(Result<&2, &2, Identity.Malformed, Identity.Ids>, Identity.parse.go(["author " ++ a, "under " ++ dir], 1n+p, Done{Identity.Reading{ids, None{}, None{}, 0n}}), Identity.parse.go(["under " ++ dir], 1n+1n+p, Done{Identity.Reading{ids, None{}, Some{a}, 1n+p}}), Fail{Identity.Malformed{1n+1n+p, "`under` heads a block, so it comes first"}},
    go_author(["under " ++ dir], p, ids, None{}, 0n, a, ha),
    Equal.cong(Identity.Said, Result<&2, &2, Identity.Malformed, Identity.Ids>, s => Identity.parse.go(Nil{}, 1n+1n+1n+p, Identity.line(Identity.Reading{ids, None{}, Some{a}, 1n+p}, 1n+1n+p, s)), Identity.said("under " ++ dir), Identity.Said.Under{Identity.unslashed(dir)}, said_under_any(dir, hd)))

# A block of two `under` lines is refused at the second.
def two_dirs(-ids: Identity.Ids, +p: Nat, +d1: String, +d2: String, +h1: {Identity.unusable(d1) == False{} : Bool}, +h2: {Identity.unusable(d2) == False{} : Bool}) -> {Identity.parse.go(["under " ++ d1, "under " ++ d2], 1n+p, Done{Identity.Reading{ids, None{}, None{}, 0n}}) == Fail{Identity.Malformed{1n+1n+p, "a block names one directory"}} : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  Equal.trans(Result<&2, &2, Identity.Malformed, Identity.Ids>, Identity.parse.go(["under " ++ d1, "under " ++ d2], 1n+p, Done{Identity.Reading{ids, None{}, None{}, 0n}}), Identity.parse.go(["under " ++ d2], 1n+1n+p, Done{Identity.Reading{ids, Some{Identity.unslashed(d1)}, None{}, 1n+p}}), Fail{Identity.Malformed{1n+1n+p, "a block names one directory"}},
    go_under_any(["under " ++ d2], p, ids, d1, h1),
    Equal.cong(Identity.Said, Result<&2, &2, Identity.Malformed, Identity.Ids>, s => Identity.parse.go(Nil{}, 1n+1n+1n+p, Identity.line(Identity.Reading{ids, Some{Identity.unslashed(d1)}, None{}, 1n+p}, 1n+1n+p, s)), Identity.said("under " ++ d2), Identity.Said.Under{Identity.unslashed(d2)}, said_under_any(d2, h2)))

# A block naming a directory and ending with the file states no author,
# which is said at its first line.
def dir_alone(-ids: Identity.Ids, +p: Nat, +dir: String, +hd: {Identity.unusable(dir) == False{} : Bool}) -> {Identity.parse.go(["under " ++ dir], 1n+p, Done{Identity.Reading{ids, None{}, None{}, 0n}}) == Fail{Identity.Malformed{1n+p, "a block naming a directory states no author"}} : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  Equal.trans(Result<&2, &2, Identity.Malformed, Identity.Ids>, Identity.parse.go(["under " ++ dir], 1n+p, Done{Identity.Reading{ids, None{}, None{}, 0n}}), Identity.parse.go(Nil{}, 1n+1n+p, Done{Identity.Reading{ids, Some{Identity.unslashed(dir)}, None{}, 1n+p}}), Fail{Identity.Malformed{1n+p, "a block naming a directory states no author"}},
    go_under_any(Nil{}, p, ids, dir, hd),
    Equal.cong(Nat, Result<&2, &2, Identity.Malformed, Identity.Ids>, n => Fail{Identity.Malformed{n, "a block naming a directory states no author"}}, Nat.max(1n+p, 1n), 1n+p, max_one(p)))

# A second block of `author` alone is refused at its first line.
def second_default(-us: List<&2, T.Split>, +p: Nat, -a0: String, +b: String, +hb: {Identity.unusable(b) == False{} : Bool}) -> {Identity.parse.go(["author " ++ b], 1n+p, Done{Identity.Reading{Identity.Ids{Some{a0}, us}, None{}, None{}, 0n}}) == Fail{Identity.Malformed{1n+p, "two blocks state a default author"}} : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  Equal.trans(Result<&2, &2, Identity.Malformed, Identity.Ids>, Identity.parse.go(["author " ++ b], 1n+p, Done{Identity.Reading{Identity.Ids{Some{a0}, us}, None{}, None{}, 0n}}), Identity.parse.go(Nil{}, 1n+1n+p, Done{Identity.Reading{Identity.Ids{Some{a0}, us}, None{}, Some{b}, 1n+p}}), Fail{Identity.Malformed{1n+p, "two blocks state a default author"}},
    go_author(Nil{}, p, Identity.Ids{Some{a0}, us}, None{}, 0n, b, hb),
    Equal.cong(Nat, Result<&2, &2, Identity.Malformed, Identity.Ids>, n => Fail{Identity.Malformed{n, "two blocks state a default author"}}, Nat.max(1n+p, 1n), 1n+p, max_one(p)))

def split.key(m: Maybe<&2, T.Split>) -> String:
  match m:
    case None{}:
      SNil{}
    case Some{T.Split{k, v}}:
      k

def get_claimed(us: List<&2, T.Split>, i: Nat, +dir: String, -x: String, e: {List.get(&2, T.Split, us, i) == Some{T.Split{dir, x}} : Maybe<&2, T.Split>}) -> {Identity.claimed(us, dir) == True{} : Bool}:
  match us i:
    case Nil{} _:
      Empty.absurd({Identity.claimed(Nil{}, dir) == True{} : Bool}, Comp.false_true(Equal.cong(Maybe<&2, T.Split>, Bool, m => Maybe.is_some(&2, T.Split, m), None{}, Some{T.Split{dir, x}}, e)))
    case T.Split{+h, +a} <> +rest 0n:
      +same = Equal.cong(Maybe<&2, T.Split>, String, m => split.key(m), Some{T.Split{h, a}}, Some{T.Split{dir, x}}, e)
      %same : {Bool.or(String.eq(h, _), Identity.claimed(rest, dir)) == True{} : Bool}
      %Equal.sym(Bool, String.eq(h, h), True{}, S.eq_refl(h)) : {Bool.or(_, Identity.claimed(rest, dir)) == True{} : Bool}
      {==}
    case T.Split{+h, a} <> rest 1n+j:
      AL.or_right(String.eq(h, dir), Identity.claimed(rest, dir), get_claimed(rest, j, dir, x, e))

# A second block for a directory a block before it named is refused at
# its first line.
def dir_again(+d: Maybe<&2, String>, +us: List<&2, T.Split>, +p: Nat, +dir: String, +b: String, +i: Nat, -x: String, +e: {List.get(&2, T.Split, us, i) == Some{T.Split{dir, x}} : Maybe<&2, T.Split>}, +hd: {Identity.unusable(dir) == False{} : Bool}, +hs: {String.ends_with(dir, "/") == False{} : Bool}, +hb: {Identity.unusable(b) == False{} : Bool}) -> {Identity.parse.go(["under " ++ dir, "author " ++ b], 1n+p, Done{Identity.Reading{Identity.Ids{d, us}, None{}, None{}, 0n}}) == Fail{Identity.Malformed{1n+p, "two blocks claim one directory"}} : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  +end = Identity.parse.go(Nil{}, 1n+1n+1n+p, Done{Identity.Reading{Identity.Ids{d, us}, Some{dir}, Some{b}, 1n+p}})
  Equal.trans(Result<&2, &2, Identity.Malformed, Identity.Ids>, Identity.parse.go(["under " ++ dir, "author " ++ b], 1n+p, Done{Identity.Reading{Identity.Ids{d, us}, None{}, None{}, 0n}}), Identity.parse.go(["author " ++ b], 1n+1n+p, Done{Identity.Reading{Identity.Ids{d, us}, Some{dir}, None{}, 1n+p}}), Fail{Identity.Malformed{1n+p, "two blocks claim one directory"}},
    go_under(["author " ++ b], p, Identity.Ids{d, us}, dir, hd, hs),
    Equal.trans(Result<&2, &2, Identity.Malformed, Identity.Ids>, Identity.parse.go(["author " ++ b], 1n+1n+p, Done{Identity.Reading{Identity.Ids{d, us}, Some{dir}, None{}, 1n+p}}), end, Fail{Identity.Malformed{1n+p, "two blocks claim one directory"}},
      go_author(Nil{}, 1n+p, Identity.Ids{d, us}, Some{dir}, 1n+p, b, hb),
      Equal.trans(Result<&2, &2, Identity.Malformed, Identity.Ids>, end, Fail{Identity.Malformed{Nat.max(1n+p, 1n), "two blocks claim one directory"}}, Fail{Identity.Malformed{1n+p, "two blocks claim one directory"}},
        Equal.cong(Bool, Result<&2, &2, Identity.Malformed, Identity.Ids>, c => Bool.pick(Result<&2, &2, Identity.Malformed, Identity.Ids>, c, Fail{Identity.Malformed{Nat.max(1n+p, 1n), "two blocks claim one directory"}}, Done{Identity.Ids{d, List.append(&2, T.Split, us, [T.Split{dir, b}])}}), Identity.claimed(us, dir), True{}, get_claimed(us, i, dir, x, e)),
        Equal.cong(Nat, Result<&2, &2, Identity.Malformed, Identity.Ids>, n => Fail{Identity.Malformed{n, "two blocks claim one directory"}}, Nat.max(1n+p, 1n), 1n+p, max_one(p)))))

# Lines that are not a key and a value
# ------------------------------------

def spaced(+c: Char, t: String, h: {T.has_char(SCon{c, t}, ' ') == False{} : Bool}) -> {Char.is_eq(c, ' ') == False{} : Bool}:
  AL.or_false_l(Char.is_eq(c, ' '), T.has_char(t, ' '), h)

def spaced_rest(+c: Char, t: String, h: {T.has_char(SCon{c, t}, ' ') == False{} : Bool}) -> {T.has_char(t, ' ') == False{} : Bool}:
  AL.or_false_r(Char.is_eq(c, ' '), T.has_char(t, ' '), h)

# A key with no space in it, a space and a value split at that space.
def split_key(k: String, +v: String, +acc: String, +hk: {T.has_char(k, ' ') == False{} : Bool}) -> {T.split_once.fast(k ++ SCon{' ', v}, acc, T.space_first(k ++ SCon{' ', v})) == Some{T.Split{String.reverse(String.reverse.go(k, acc)), v}} : Maybe<&2, T.Split>}:
  match k:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Char.is_eq(c, ' '), False{}, spaced(c, t, hk)) : {T.split_once.fast(SCon{c, t ++ SCon{' ', v}}, acc, _) == Some{T.Split{String.reverse(String.reverse.go(t, SCon{c, acc})), v}} : Maybe<&2, T.Split>}
      split_key(t, v, SCon{c, acc}, spaced_rest(c, t, hk))

def split_kv(+k: String, +v: String, +hk: {T.has_char(k, ' ') == False{} : Bool}) -> {T.split_once(k ++ SCon{' ', v}) == Some{T.Split{k, v}} : Maybe<&2, T.Split>}:
  %Equal.sym(Maybe<&2, T.Split>, T.split_once.fast(k ++ SCon{' ', v}, SNil{}, T.space_first(k ++ SCon{' ', v})), Some{T.Split{String.reverse(String.reverse.go(k, SNil{})), v}}, split_key(k, v, SNil{}, hk)) : {_ == Some{T.Split{k, v}} : Maybe<&2, T.Split>}
  %Equal.sym(String, String.reverse(String.reverse(k)), k, rev_rev(k)) : {Some{T.Split{_, v}} == Some{T.Split{k, v}} : Maybe<&2, T.Split>}
  {==}

# A line with no space in it does not split.
def split_none(w: String, +acc: String, +hw: {T.has_char(w, ' ') == False{} : Bool}) -> {T.split_once.fast(w, acc, T.space_first(w)) == None{} : Maybe<&2, T.Split>}:
  match w:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Char.is_eq(c, ' '), False{}, spaced(c, t, hw)) : {T.split_once.fast(SCon{c, t}, acc, _) == None{} : Maybe<&2, T.Split>}
      split_none(t, SCon{c, acc}, spaced_rest(c, t, hw))

def said_other(+k: String, +v: String, +hk: {T.has_char(k, ' ') == False{} : Bool}, +hv: {Identity.unusable(v) == False{} : Bool}, +hu: {String.eq(k, "under") == False{} : Bool}, +ha: {String.eq(k, "author") == False{} : Bool}) -> {Identity.said(k ++ SCon{' ', v}) == Identity.Said.Other{} : Identity.Said}:
  %Equal.sym(Bool, String.is_empty(k ++ SCon{' ', v}), False{}, filled(k, ' ', v)) : {Bool.pick(Identity.Said, _, Identity.Said.Blank{}, Identity.said.cut(T.split_once(k ++ SCon{' ', v}))) == Identity.Said.Other{} : Identity.Said}
  %Equal.sym(Maybe<&2, T.Split>, T.split_once(k ++ SCon{' ', v}), Some{T.Split{k, v}}, split_kv(k, v, hk)) : {Identity.said.cut(_) == Identity.Said.Other{} : Identity.Said}
  %Equal.sym(Bool, Identity.unusable(v), False{}, hv) : {Bool.pick(Identity.Said, _, Identity.Said.Unusable{}, Bool.pick(Identity.Said, String.eq(k, "under"), Identity.Said.Under{Identity.unslashed(v)}, Bool.pick(Identity.Said, String.eq(k, "author"), Identity.Said.Author{v}, Identity.Said.Other{}))) == Identity.Said.Other{} : Identity.Said}
  %Equal.sym(Bool, String.eq(k, "under"), False{}, hu) : {Bool.pick(Identity.Said, _, Identity.Said.Under{Identity.unslashed(v)}, Bool.pick(Identity.Said, String.eq(k, "author"), Identity.Said.Author{v}, Identity.Said.Other{})) == Identity.Said.Other{} : Identity.Said}
  %Equal.sym(Bool, String.eq(k, "author"), False{}, ha) : {Bool.pick(Identity.Said, _, Identity.Said.Author{v}, Identity.Said.Other{}) == Identity.Said.Other{} : Identity.Said}
  {==}

def said_unusable(+k: String, +v: String, +hk: {T.has_char(k, ' ') == False{} : Bool}, +hv: {Folder.untrimmed(v) == True{} : Bool}) -> {Identity.said(k ++ SCon{' ', v}) == Identity.Said.Unusable{} : Identity.Said}:
  %Equal.sym(Bool, String.is_empty(k ++ SCon{' ', v}), False{}, filled(k, ' ', v)) : {Bool.pick(Identity.Said, _, Identity.Said.Blank{}, Identity.said.cut(T.split_once(k ++ SCon{' ', v}))) == Identity.Said.Unusable{} : Identity.Said}
  %Equal.sym(Maybe<&2, T.Split>, T.split_once(k ++ SCon{' ', v}), Some{T.Split{k, v}}, split_kv(k, v, hk)) : {Identity.said.cut(_) == Identity.Said.Unusable{} : Identity.Said}
  %Equal.sym(Bool, Folder.untrimmed(v), True{}, hv) : {Bool.pick(Identity.Said, Bool.or(_, quiet(v)), Identity.Said.Unusable{}, Bool.pick(Identity.Said, String.eq(k, "under"), Identity.Said.Under{Identity.unslashed(v)}, Bool.pick(Identity.Said, String.eq(k, "author"), Identity.Said.Author{v}, Identity.Said.Other{}))) == Identity.Said.Unusable{} : Identity.Said}
  {==}

def said_unsplit(+w: String, +hw: {T.has_char(w, ' ') == False{} : Bool}, +he: {String.is_empty(w) == False{} : Bool}) -> {Identity.said(w) == Identity.Said.Unsplit{} : Identity.Said}:
  %Equal.sym(Bool, String.is_empty(w), False{}, he) : {Bool.pick(Identity.Said, _, Identity.Said.Blank{}, Identity.said.cut(T.split_once(w))) == Identity.Said.Unsplit{} : Identity.Said}
  %Equal.sym(Maybe<&2, T.Split>, T.split_once.fast(w, SNil{}, T.space_first(w)), None{}, split_none(w, SNil{}, hw)) : {Identity.said.cut(_) == Identity.Said.Unsplit{} : Identity.Said}
  {==}

# A line that is one of these is refused where it stands, whatever block
# it would be in.
def refused_line(-ids: Identity.Ids, -p: Nat, +l: String, -s: Identity.Said, -why: String, e: {Identity.said(l) == s : Identity.Said}, f: {Identity.line(Identity.Reading{ids, None{}, None{}, 0n}, 1n+p, s) == Fail{Identity.Malformed{1n+p, why}} : Result<&2, &2, Identity.Malformed, Identity.Reading>}) -> {Identity.parse.go([l], 1n+p, Done{Identity.Reading{ids, None{}, None{}, 0n}}) == Fail{Identity.Malformed{1n+p, why}} : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  %Equal.sym(Identity.Said, Identity.said(l), s, e) : {Identity.parse.go(Nil{}, 1n+1n+p, Identity.line(Identity.Reading{ids, None{}, None{}, 0n}, 1n+p, _)) == Fail{Identity.Malformed{1n+p, why}} : Result<&2, &2, Identity.Malformed, Identity.Ids>}
  %Equal.sym(Result<&2, &2, Identity.Malformed, Identity.Reading>, Identity.line(Identity.Reading{ids, None{}, None{}, 0n}, 1n+p, s), Fail{Identity.Malformed{1n+p, why}}, f) : {Identity.parse.go(Nil{}, 1n+1n+p, _) == Fail{Identity.Malformed{1n+p, why}} : Result<&2, &2, Identity.Malformed, Identity.Ids>}
  {==}

# The laws
# --------

def good1(+l: String, +g: {good(l) == True{} : Bool}) -> {all_good([l]) == True{} : Bool}:
  AL.and_intro(good(l), True{}, g, {==})

def good2(+l1: String, +l2: String, +g1: {good(l1) == True{} : Bool}, +g2: {good(l2) == True{} : Bool}) -> {all_good([l1, l2]) == True{} : Bool}:
  AL.and_intro(good(l1), all_good([l2]), g1, good1(l2, g2))

def good_kv(+k: String, +v: String, +hk: {quiet(k) == False{} : Bool}, +hv: {quiet(v) == False{} : Bool}) -> {good(k ++ SCon{' ', v}) == True{} : Bool}:
  AL.and_intro(BmL.nonl(k ++ SCon{' ', v}), Bool.not(String.ends_with(k ++ SCon{' ', v}, "\r")), BmL.nonl_app(k, SCon{' ', v}, nonl(k, hk), nonl(v, hv)),
    AL.not_true(String.ends_with(k ++ SCon{' ', v}, "\r"), Equal.trans(Bool, String.starts_with(String.reverse.go(k ++ SCon{' ', v}, SNil{}), "\r"), String.starts_with(String.reverse.go(v, SCon{' ', String.reverse.go(k, SNil{})}), "\r"), False{},
      Equal.cong(String, Bool, x => String.starts_with(x, "\r"), String.reverse.go(k ++ SCon{' ', v}, SNil{}), String.reverse.go(v, SCon{' ', String.reverse.go(k, SNil{})}), rev_go_app(k, SCon{' ', v}, SNil{})),
      cr_rev(v, SCon{' ', String.reverse.go(k, SNil{})}, hv, {==}))))

def good_word(+w: String, +hw: {quiet(w) == False{} : Bool}) -> {good(w) == True{} : Bool}:
  AL.and_intro(BmL.nonl(w), Bool.not(String.ends_with(w, "\r")), nonl(w, hw), AL.not_true(String.ends_with(w, "\r"), cr_rev(w, SNil{}, hw, {==})))

# Lines after the blocks that the reading refuses are refused in the file.
def refuses(+d: Maybe<&2, String>, +us: List<&2, T.Split>, +bad: List<&2, String>, -why: Identity.Malformed, +hf: {fits(d, us) == True{} : Bool}, +hb: {all_good(bad) == True{} : Bool}, +e: {Identity.parse.go(bad, 1n+List.length(&2, String, lines(d, us)), Done{Identity.Reading{Identity.Ids{d, us}, None{}, None{}, 0n}}) == Fail{why} : Result<&2, &2, Identity.Malformed, Identity.Ids>}) -> {Identity.parse(text(List.append(&2, String, lines(d, us), bad))) == Fail{why} : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  Equal.trans(Result<&2, &2, Identity.Malformed, Identity.Ids>, Identity.parse(text(List.append(&2, String, lines(d, us), bad))), Identity.parse.go(bad, 1n+List.length(&2, String, lines(d, us)), Done{Identity.Reading{Identity.Ids{d, us}, None{}, None{}, 0n}}), Fail{why}, after_blocks(d, us, bad, hf, hb), e)

def refuses_two_authors(+d: Maybe<&2, String>, +us: List<&2, T.Split>, +a: String, +b: String, +hf: {fits(d, us) == True{} : Bool}, +ha: {Identity.unusable(a) == False{} : Bool}, +hb: {Identity.unusable(b) == False{} : Bool}) -> {Identity.parse(text(List.append(&2, String, lines(d, us), ["author " ++ a, "author " ++ b]))) == Fail{Identity.Malformed{1n+1n+List.length(&2, String, lines(d, us)), "a block states one author"}} : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  refuses(d, us, ["author " ++ a, "author " ++ b], Identity.Malformed{1n+1n+List.length(&2, String, lines(d, us)), "a block states one author"}, hf, good2("author " ++ a, "author " ++ b, good_author(a, ha), good_author(b, hb)),
    two_authors(Identity.Ids{d, us}, List.length(&2, String, lines(d, us)), a, b, ha, hb))

def refuses_under_after_author(+d: Maybe<&2, String>, +us: List<&2, T.Split>, +a: String, +dir: String, +hf: {fits(d, us) == True{} : Bool}, +ha: {Identity.unusable(a) == False{} : Bool}, +hd: {Identity.unusable(dir) == False{} : Bool}) -> {Identity.parse(text(List.append(&2, String, lines(d, us), ["author " ++ a, "under " ++ dir]))) == Fail{Identity.Malformed{1n+1n+List.length(&2, String, lines(d, us)), "`under` heads a block, so it comes first"}} : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  refuses(d, us, ["author " ++ a, "under " ++ dir], Identity.Malformed{1n+1n+List.length(&2, String, lines(d, us)), "`under` heads a block, so it comes first"}, hf, good2("author " ++ a, "under " ++ dir, good_author(a, ha), good_under(dir, hd)),
    under_after_author(Identity.Ids{d, us}, List.length(&2, String, lines(d, us)), a, dir, ha, hd))

def refuses_two_directories(+d: Maybe<&2, String>, +us: List<&2, T.Split>, +d1: String, +d2: String, +hf: {fits(d, us) == True{} : Bool}, +h1: {Identity.unusable(d1) == False{} : Bool}, +h2: {Identity.unusable(d2) == False{} : Bool}) -> {Identity.parse(text(List.append(&2, String, lines(d, us), ["under " ++ d1, "under " ++ d2]))) == Fail{Identity.Malformed{1n+1n+List.length(&2, String, lines(d, us)), "a block names one directory"}} : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  refuses(d, us, ["under " ++ d1, "under " ++ d2], Identity.Malformed{1n+1n+List.length(&2, String, lines(d, us)), "a block names one directory"}, hf, good2("under " ++ d1, "under " ++ d2, good_under(d1, h1), good_under(d2, h2)),
    two_dirs(Identity.Ids{d, us}, List.length(&2, String, lines(d, us)), d1, d2, h1, h2))

def refuses_directory_alone(+d: Maybe<&2, String>, +us: List<&2, T.Split>, +dir: String, +hf: {fits(d, us) == True{} : Bool}, +hd: {Identity.unusable(dir) == False{} : Bool}) -> {Identity.parse(text(List.append(&2, String, lines(d, us), ["under " ++ dir]))) == Fail{Identity.Malformed{1n+List.length(&2, String, lines(d, us)), "a block naming a directory states no author"}} : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  refuses(d, us, ["under " ++ dir], Identity.Malformed{1n+List.length(&2, String, lines(d, us)), "a block naming a directory states no author"}, hf, good1("under " ++ dir, good_under(dir, hd)),
    dir_alone(Identity.Ids{d, us}, List.length(&2, String, lines(d, us)), dir, hd))

def refuses_second_default(+a0: String, +us: List<&2, T.Split>, +b: String, +hf: {fits(Some{a0}, us) == True{} : Bool}, +hb: {Identity.unusable(b) == False{} : Bool}) -> {Identity.parse(text(List.append(&2, String, lines(Some{a0}, us), ["author " ++ b]))) == Fail{Identity.Malformed{1n+List.length(&2, String, lines(Some{a0}, us)), "two blocks state a default author"}} : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  refuses(Some{a0}, us, ["author " ++ b], Identity.Malformed{1n+List.length(&2, String, lines(Some{a0}, us)), "two blocks state a default author"}, hf, good1("author " ++ b, good_author(b, hb)),
    second_default(us, List.length(&2, String, lines(Some{a0}, us)), a0, b, hb))

def refuses_directory_again(+d: Maybe<&2, String>, +us: List<&2, T.Split>, +i: Nat, +dir: String, -x: String, +b: String, +hf: {fits(d, us) == True{} : Bool}, +e: {List.get(&2, T.Split, us, i) == Some{T.Split{dir, x}} : Maybe<&2, T.Split>}, +hd: {Identity.unusable(dir) == False{} : Bool}, +hs: {String.ends_with(dir, "/") == False{} : Bool}, +hb: {Identity.unusable(b) == False{} : Bool}) -> {Identity.parse(text(List.append(&2, String, lines(d, us), ["under " ++ dir, "author " ++ b]))) == Fail{Identity.Malformed{1n+List.length(&2, String, lines(d, us)), "two blocks claim one directory"}} : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  refuses(d, us, ["under " ++ dir, "author " ++ b], Identity.Malformed{1n+List.length(&2, String, lines(d, us)), "two blocks claim one directory"}, hf, good2("under " ++ dir, "author " ++ b, good_under(dir, hd), good_author(b, hb)),
    dir_again(d, us, List.length(&2, String, lines(d, us)), dir, b, i, x, e, hd, hs, hb))

def refuses_unknown_key(+d: Maybe<&2, String>, +us: List<&2, T.Split>, +k: String, +v: String, +hf: {fits(d, us) == True{} : Bool}, +hs: {T.has_char(k, ' ') == False{} : Bool}, +hc: {has_control(k) == False{} : Bool}, +hu: {String.eq(k, "under") == False{} : Bool}, +ha: {String.eq(k, "author") == False{} : Bool}, +hv: {Identity.unusable(v) == False{} : Bool}) -> {Identity.parse(text(List.append(&2, String, lines(d, us), [k ++ SCon{' ', v}]))) == Fail{Identity.Malformed{1n+List.length(&2, String, lines(d, us)), "the keys are `author` and `under`"}} : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  refuses(d, us, [k ++ SCon{' ', v}], Identity.Malformed{1n+List.length(&2, String, lines(d, us)), "the keys are `author` and `under`"}, hf, good1(k ++ SCon{' ', v}, good_kv(k, v, hc, usable_quiet(v, hv))),
    refused_line(Identity.Ids{d, us}, List.length(&2, String, lines(d, us)), k ++ SCon{' ', v}, Identity.Said.Other{}, "the keys are `author` and `under`", said_other(k, v, hs, hv, hu, ha), {==}))

def refuses_unusable_value(+d: Maybe<&2, String>, +us: List<&2, T.Split>, +k: String, +v: String, +hf: {fits(d, us) == True{} : Bool}, +hs: {T.has_char(k, ' ') == False{} : Bool}, +hc: {has_control(k) == False{} : Bool}, +hv: {Folder.untrimmed(v) == True{} : Bool}, +hq: {has_control(v) == False{} : Bool}) -> {Identity.parse(text(List.append(&2, String, lines(d, us), [k ++ SCon{' ', v}]))) == Fail{Identity.Malformed{1n+List.length(&2, String, lines(d, us)), "a value is not empty, carries no leading or trailing space, and holds no control character"}} : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  refuses(d, us, [k ++ SCon{' ', v}], Identity.Malformed{1n+List.length(&2, String, lines(d, us)), "a value is not empty, carries no leading or trailing space, and holds no control character"}, hf, good1(k ++ SCon{' ', v}, good_kv(k, v, hc, hq)),
    refused_line(Identity.Ids{d, us}, List.length(&2, String, lines(d, us)), k ++ SCon{' ', v}, Identity.Said.Unusable{}, "a value is not empty, carries no leading or trailing space, and holds no control character", said_unusable(k, v, hs, hv), {==}))

def refuses_unsplit(+d: Maybe<&2, String>, +us: List<&2, T.Split>, +w: String, +hf: {fits(d, us) == True{} : Bool}, +he: {String.is_empty(w) == False{} : Bool}, +hs: {T.has_char(w, ' ') == False{} : Bool}, +hc: {has_control(w) == False{} : Bool}) -> {Identity.parse(text(List.append(&2, String, lines(d, us), [w]))) == Fail{Identity.Malformed{1n+List.length(&2, String, lines(d, us)), "a line is a key, a space, and a value"}} : Result<&2, &2, Identity.Malformed, Identity.Ids>}:
  refuses(d, us, [w], Identity.Malformed{1n+List.length(&2, String, lines(d, us)), "a line is a key, a space, and a value"}, hf, good1(w, good_word(w, hc)),
    refused_line(Identity.Ids{d, us}, List.length(&2, String, lines(d, us)), w, Identity.Said.Unsplit{}, "a line is a key, a space, and a value", said_unsplit(w, hs, he), {==}))
