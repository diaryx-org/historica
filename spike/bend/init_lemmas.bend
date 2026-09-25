# What `init` lays down, and where: a store under the root it names and
# nothing beside it, joined to the directory it runs in as `Path::join`
# joins, holding text the format holds.
import Base
import ./commands.bend as Main
import ./revision.bend as Rev
import ./string_lemmas.bend as S
import ./blamed_lemmas.bend as B
import ./check.bend as Check
import ./store.bend as Store
import ./utf8.bend as Utf8

# Under a root
# ------------

# A component a path may have and stay where it is put: not empty, and
# not `.` or `..`.
def component(+c: String) -> Bool:
  Bool.not(Bool.or(String.is_empty(c), Bool.or(String.eq(c, "."), String.eq(c, ".."))))

def components(cs: List<&2, String>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case +c <> rest:
      Bool.and(component(c), components(rest))

# What follows a root in a path under it: a `/`, then components.
def below(s: String) -> Bool:
  match s:
    case SCon{'/', rest}:
      components(String.split(rest, '/'))
    case _:
      False{}

# `p` is under `root`: `root`, and then what `below` accepts.
def inside(+root: String, +p: String) -> Bool:
  Bool.and(String.starts_with(p, root), below(String.drop(p, String.length(root))))

# What a path is in: everything before its last `/`.
def parent.go(r: String) -> String:
  match r:
    case SNil{}:
      SNil{}
    case SCon{'/', rest}:
      rest
    case SCon{c, rest}:
      parent.go(rest)

def parent(s: String) -> String:
  String.reverse(parent.go(String.reverse(s)))

# The directories a layout makes, relative to its root.
def rels(+root: String, ds: List<&2, String>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> rest:
      String.drop(d, String.length(root)) <> rels(root, rest)

# A note lands in the root itself, or in a directory the layout makes.
def lands(+root: String, +ds: List<&2, String>, +p: String) -> Bool:
  +r = parent(String.drop(p, String.length(root)))
  Bool.or(String.is_empty(r), Rev.member(rels(root, ds), r))

def dirs.inside(+root: String, ds: List<&2, String>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case +d <> rest:
      Bool.and(inside(root, d), dirs.inside(root, rest))

def notes.inside(+root: String, +ds: List<&2, String>, ns: List<&2, Main.Note>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Main.Note{+p, t} <> rest:
      Bool.and(Bool.and(inside(root, p), lands(root, ds, p)), notes.inside(root, ds, rest))

# Every directory a layout makes is under the root, and every note it
# writes is too, in the root or in a directory it makes.
def within(+root: String, l: Main.Layout) -> Bool:
  match l:
    case Main.Layout{+ds, ns}:
      Bool.and(dirs.inside(root, ds), notes.inside(root, ds, ns))

def drop_app(root: String, +s: String) -> {String.drop(root ++ s, String.length(root)) == s : String}:
  match root:
    case SNil{}:
      match s:
        case SNil{}:
          {==}
        case SCon{h, t}:
          {==}
    case SCon{h, t}:
      drop_app(t, s)

def drop_zero(s: String) -> {String.drop(s, 0n) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

def starts_app(+root: String, +s: String) -> {String.starts_with(root ++ s, root) == True{} : Bool}:
  B.sw_ext(root, root, s, B.sw_refl(root))

# A path put under a root is under it exactly when it was under no root.
def inside_under(+root: String, +p: String) -> {inside(root, root ++ p) == inside(SNil{}, p) : Bool}:
  +a = Equal.sym(Bool, String.starts_with(root ++ p, root), True{}, starts_app(root, p))
  %a : {Bool.and(_, below(String.drop(root ++ p, String.length(root)))) == inside(SNil{}, p) : Bool}
  +b = Equal.sym(String, String.drop(root ++ p, String.length(root)), p, drop_app(root, p))
  %b : {Bool.and(True{}, below(_)) == inside(SNil{}, p) : Bool}
  +c = Equal.sym(Bool, String.starts_with(p, SNil{}), True{}, B.sw_nil(p))
  %c : {Bool.and(True{}, below(p)) == Bool.and(_, below(String.drop(p, 0n))) : Bool}
  +d = Equal.sym(String, String.drop(p, 0n), p, drop_zero(p))
  %d : {Bool.and(True{}, below(p)) == Bool.and(True{}, below(_)) : Bool}
  {==}

def rels_under(+root: String, ds: List<&2, String>) -> {rels(root, Main.init.under.dirs(root, ds)) == rels(SNil{}, ds) : List<&2, String>}:
  match ds:
    case Nil{}:
      {==}
    case +d <> rest:
      +a = Equal.sym(String, String.drop(root ++ d, String.length(root)), d, drop_app(root, d))
      %a : {_ <> rels(root, Main.init.under.dirs(root, rest)) == rels(SNil{}, d <> rest) : List<&2, String>}
      +b = Equal.sym(String, String.drop(d, 0n), d, drop_zero(d))
      %b : {d <> rels(root, Main.init.under.dirs(root, rest)) == _ <> rels(SNil{}, rest) : List<&2, String>}
      %Equal.sym(List<&2, String>, rels(root, Main.init.under.dirs(root, rest)), rels(SNil{}, rest), rels_under(root, rest)) : {d <> _ == d <> rels(SNil{}, rest) : List<&2, String>}
      {==}

def lands_under(+root: String, +ds: List<&2, String>, +p: String) -> {lands(root, Main.init.under.dirs(root, ds), root ++ p) == lands(SNil{}, ds, p) : Bool}:
  +a = Equal.sym(String, String.drop(root ++ p, String.length(root)), p, drop_app(root, p))
  %a : {Bool.or(String.is_empty(parent(_)), Rev.member(rels(root, Main.init.under.dirs(root, ds)), parent(_))) == lands(SNil{}, ds, p) : Bool}
  +b = Equal.sym(List<&2, String>, rels(root, Main.init.under.dirs(root, ds)), rels(SNil{}, ds), rels_under(root, ds))
  %b : {Bool.or(String.is_empty(parent(p)), Rev.member(_, parent(p))) == lands(SNil{}, ds, p) : Bool}
  +c = Equal.sym(String, String.drop(p, 0n), p, drop_zero(p))
  %c : {Bool.or(String.is_empty(parent(p)), Rev.member(rels(SNil{}, ds), parent(p))) == Bool.or(String.is_empty(parent(_)), Rev.member(rels(SNil{}, ds), parent(_))) : Bool}
  {==}

def dirs_under(+root: String, ds: List<&2, String>) -> {dirs.inside(root, Main.init.under.dirs(root, ds)) == dirs.inside(SNil{}, ds) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case +d <> rest:
      %Equal.sym(Bool, inside(root, root ++ d), inside(SNil{}, d), inside_under(root, d)) : {Bool.and(_, dirs.inside(root, Main.init.under.dirs(root, rest))) == dirs.inside(SNil{}, d <> rest) : Bool}
      %Equal.sym(Bool, dirs.inside(root, Main.init.under.dirs(root, rest)), dirs.inside(SNil{}, rest), dirs_under(root, rest)) : {Bool.and(inside(SNil{}, d), _) == dirs.inside(SNil{}, d <> rest) : Bool}
      {==}

def notes_under(+root: String, +ds: List<&2, String>, ns: List<&2, Main.Note>) -> {notes.inside(root, Main.init.under.dirs(root, ds), Main.init.under.notes(root, ns)) == notes.inside(SNil{}, ds, ns) : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Main.Note{+p, +t} <> rest:
      %Equal.sym(Bool, inside(root, root ++ p), inside(SNil{}, p), inside_under(root, p)) : {Bool.and(Bool.and(_, lands(root, Main.init.under.dirs(root, ds), root ++ p)), notes.inside(root, Main.init.under.dirs(root, ds), Main.init.under.notes(root, rest))) == notes.inside(SNil{}, ds, Main.Note{p, t} <> rest) : Bool}
      %Equal.sym(Bool, lands(root, Main.init.under.dirs(root, ds), root ++ p), lands(SNil{}, ds, p), lands_under(root, ds, p)) : {Bool.and(Bool.and(inside(SNil{}, p), _), notes.inside(root, Main.init.under.dirs(root, ds), Main.init.under.notes(root, rest))) == notes.inside(SNil{}, ds, Main.Note{p, t} <> rest) : Bool}
      %Equal.sym(Bool, notes.inside(root, Main.init.under.dirs(root, ds), Main.init.under.notes(root, rest)), notes.inside(SNil{}, ds, rest), notes_under(root, ds, rest)) : {Bool.and(Bool.and(inside(SNil{}, p), lands(SNil{}, ds, p)), _) == notes.inside(SNil{}, ds, Main.Note{p, t} <> rest) : Bool}
      {==}

def within_under(+root: String, l: Main.Layout) -> {within(root, Main.init.under(root, l)) == within(SNil{}, l) : Bool}:
  match l:
    case Main.Layout{+ds, +ns}:
      %Equal.sym(Bool, dirs.inside(root, Main.init.under.dirs(root, ds)), dirs.inside(SNil{}, ds), dirs_under(root, ds)) : {Bool.and(_, notes.inside(root, Main.init.under.dirs(root, ds), Main.init.under.notes(root, ns))) == within(SNil{}, Main.Layout{ds, ns}) : Bool}
      %Equal.sym(Bool, notes.inside(root, Main.init.under.dirs(root, ds), Main.init.under.notes(root, ns)), notes.inside(SNil{}, ds, ns), notes_under(root, ds, ns)) : {Bool.and(dirs.inside(SNil{}, ds), _) == within(SNil{}, Main.Layout{ds, ns}) : Bool}
      {==}

# `init` lays down nothing outside the root it names. Its layout is one
# relative to the root, put under it — where anything goes inside the store
# does not depend on where the store is — so it is enough that the relative
# one keeps below its root.
def only_its_store(+root: String) -> {within(root, Main.init.layout(root)) == True{} : Bool}:
  %Equal.sym(Bool, within(root, Main.init.under(root, Main.init.laid())), within(SNil{}, Main.init.laid()), within_under(root, Main.init.laid())) : {_ == True{} : Bool}
  {==}

# Where the root is
# -----------------

# An absolute `<dir>` is where the store goes, whatever directory `init`
# runs in.
def absolute(+base: String, +other: String, +d: String) -> {Main.init.root(base, Some{"/" ++ d}) == Main.init.root(other, Some{"/" ++ d}) : String}:
  match d:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

# `path_join` by its cases: a path joined to a base that needs a `/`, and
# to one that does not.
def join_rel(+base: String, +p: String, ep: {String.starts_with(p, "/") == False{} : Bool}, eb: {Bool.or(String.is_empty(base), String.ends_with(base, "/")) == False{} : Bool}) -> {Main.path_join(base, p) == base ++ "/" ++ p : String}:
  %Equal.sym(Bool, String.starts_with(p, "/"), False{}, ep) : {Bool.pick(String, _, p, Bool.pick(String, Bool.or(String.is_empty(base), String.ends_with(base, "/")), base ++ p, base ++ "/" ++ p)) == base ++ "/" ++ p : String}
  %Equal.sym(Bool, Bool.or(String.is_empty(base), String.ends_with(base, "/")), False{}, eb) : {Bool.pick(String, False{}, p, Bool.pick(String, _, base ++ p, base ++ "/" ++ p)) == base ++ "/" ++ p : String}
  {==}

def join_slash(+base: String, +p: String, ep: {String.starts_with(p, "/") == False{} : Bool}, eb: {Bool.or(String.is_empty(base), String.ends_with(base, "/")) == True{} : Bool}) -> {Main.path_join(base, p) == base ++ p : String}:
  %Equal.sym(Bool, String.starts_with(p, "/"), False{}, ep) : {Bool.pick(String, _, p, Bool.pick(String, Bool.or(String.is_empty(base), String.ends_with(base, "/")), base ++ p, base ++ "/" ++ p)) == base ++ p : String}
  %Equal.sym(Bool, Bool.or(String.is_empty(base), String.ends_with(base, "/")), True{}, eb) : {Bool.pick(String, False{}, p, Bool.pick(String, _, base ++ p, base ++ "/" ++ p)) == base ++ p : String}
  {==}

def empty_app(p: String, +x: String, ne: {String.is_empty(x) == False{} : Bool}) -> {String.is_empty(p ++ x) == False{} : Bool}:
  match p:
    case SNil{}:
      ne
    case SCon{h, t}:
      {==}

def sw_if_nil(c: Bool, +z: String, +w: String) -> {String.starts_with.if(z ++ w, SNil{}, c) == String.starts_with.if(z, SNil{}, c) : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, String.starts_with(z ++ w, SNil{}), True{}, B.sw_nil(z ++ w)) : {_ == String.starts_with(z, SNil{}) : Bool}
      %Equal.sym(Bool, String.starts_with(z, SNil{}), True{}, B.sw_nil(z)) : {True{} == _ : Bool}
      {==}
    case False{}:
      {==}

# Whether a path starts with `/` is its first character's to say.
def sw_slash(x: String, +w: String, ne: {String.is_empty(x) == False{} : Bool}) -> {String.starts_with(x ++ w, "/") == String.starts_with(x, "/") : Bool}:
  match x:
    case SNil{}:
      Empty.absurd({String.starts_with(w, "/") == String.starts_with(SNil{}, "/") : Bool}, S.true_false(ne))
    case SCon{+y, +z}:
      sw_if_nil(Char.is_eq(y, '/'), z, w)

def rev_nonempty(d: String, ne: {String.is_empty(d) == False{} : Bool}) -> {String.is_empty(String.reverse(d)) == False{} : Bool}:
  match d:
    case SNil{}:
      Empty.absurd({String.is_empty(String.reverse(SNil{})) == False{} : Bool}, S.true_false(ne))
    case SCon{+h, +t}:
      %Equal.sym(String, String.reverse.go(t, SCon{h, SNil{}}), String.reverse.go(t, SNil{}) ++ SCon{h, SNil{}}, B.rev_acc(t, SCon{h, SNil{}})) : {String.is_empty(_) == False{} : Bool}
      empty_app(String.reverse.go(t, SNil{}), SCon{h, SNil{}}, {==})

# And whether it ends with one, its last character's.
def ends_slash_app(+p: String, +d: String, ne: {String.is_empty(d) == False{} : Bool}) -> {String.ends_with(p ++ d, "/") == String.ends_with(d, "/") : Bool}:
  %Equal.sym(String, String.reverse(p ++ d), String.reverse(d) ++ String.reverse(p), B.rev_app(p, d)) : {String.starts_with(_, "/") == String.ends_with(d, "/") : Bool}
  sw_slash(String.reverse(d), String.reverse(p), rev_nonempty(d, ne))

def ends_slash(+p: String) -> {String.ends_with(p ++ "/", "/") == True{} : Bool}:
  B.ends_pre(p, "/", "/", B.ends_refl("/"))

def or_ff(a: Bool, b: Bool, ea: {a == False{} : Bool}, eb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  %Equal.sym(Bool, a, False{}, ea) : {Bool.or(_, b) == False{} : Bool}
  eb

def or_ft(a: Bool, b: Bool, eb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      eb

# `history` joined under a path and under that path with a `/` after it is
# one path.
def join_once(+p: String, +d: String, +e: {String.is_empty(d) == False{} : Bool}, f: {String.ends_with(d, "/") == False{} : Bool}) -> {Main.path_join(p ++ (d ++ "/"), "history") == Main.path_join(p ++ d, "history") : String}:
  +pd = Equal.sym(String, (p ++ d) ++ "/", p ++ (d ++ "/"), B.app_assoc(p, d, "/"))
  +slashed = Equal.trans(Bool, String.ends_with(p ++ (d ++ "/"), "/"), String.ends_with((p ++ d) ++ "/", "/"), True{},
    Equal.cong(String, Bool, x => String.ends_with(x, "/"), p ++ (d ++ "/"), (p ++ d) ++ "/", pd), ends_slash(p ++ d))
  +left = join_slash(p ++ (d ++ "/"), "history", {==}, or_ft(String.is_empty(p ++ (d ++ "/")), String.ends_with(p ++ (d ++ "/"), "/"), slashed))
  +bare = Equal.trans(Bool, String.ends_with(p ++ d, "/"), String.ends_with(d, "/"), False{}, ends_slash_app(p, d, e), f)
  +right = join_rel(p ++ d, "history", {==}, or_ff(String.is_empty(p ++ d), String.ends_with(p ++ d, "/"), empty_app(p, d, e), bare))
  %Equal.sym(String, Main.path_join(p ++ (d ++ "/"), "history"), (p ++ (d ++ "/")) ++ "history", left) : {_ == Main.path_join(p ++ d, "history") : String}
  %Equal.sym(String, Main.path_join(p ++ d, "history"), (p ++ d) ++ "/history", right) : {(p ++ (d ++ "/")) ++ "history" == _ : String}
  %Equal.sym(String, (p ++ (d ++ "/")) ++ "history", p ++ ((d ++ "/") ++ "history"), B.app_assoc(p, d ++ "/", "history")) : {_ == (p ++ d) ++ "/history" : String}
  %Equal.sym(String, (d ++ "/") ++ "history", d ++ "/history", B.app_assoc(d, "/", "history")) : {p ++ _ == (p ++ d) ++ "/history" : String}
  Equal.sym(String, (p ++ d) ++ "/history", p ++ (d ++ "/history"), B.app_assoc(p, d, "/history"))

def slash_picked(a: Bool, b: Bool, +base: String, +d: String, e: {String.is_empty(d) == False{} : Bool}, f: {String.ends_with(d, "/") == False{} : Bool}) -> {Main.path_join(Bool.pick(String, a, d ++ "/", Bool.pick(String, b, base ++ (d ++ "/"), base ++ "/" ++ (d ++ "/"))), "history") == Main.path_join(Bool.pick(String, a, d, Bool.pick(String, b, base ++ d, base ++ "/" ++ d)), "history") : String}:
  match a b:
    case True{} _:
      join_once(SNil{}, d, e, f)
    case False{} True{}:
      join_once(base, d, e, f)
    case False{} False{}:
      join_once(base, "/" ++ d, {==}, Equal.trans(Bool, String.ends_with("/" ++ d, "/"), String.ends_with(d, "/"), False{}, ends_slash_app("/", d, e), f))

def slash_cases(+base: String, +d: String, +a: Bool, ea: {String.starts_with(d, "/") == a : Bool}, +b: Bool, eb: {Bool.or(String.is_empty(base), String.ends_with(base, "/")) == b : Bool}, +e: {String.is_empty(d) == False{} : Bool}, f: {String.ends_with(d, "/") == False{} : Bool}) -> {Main.init.root(base, Some{d ++ "/"}) == Main.init.root(base, Some{d}) : String}:
  %Equal.sym(Bool, String.starts_with(d ++ "/", "/"), String.starts_with(d, "/"), sw_slash(d, "/", e)) : {Main.path_join(Bool.pick(String, _, d ++ "/", Bool.pick(String, Bool.or(String.is_empty(base), String.ends_with(base, "/")), base ++ (d ++ "/"), base ++ "/" ++ (d ++ "/"))), "history") == Main.init.root(base, Some{d}) : String}
  %Equal.sym(Bool, String.starts_with(d, "/"), a, ea) : {Main.path_join(Bool.pick(String, _, d ++ "/", Bool.pick(String, Bool.or(String.is_empty(base), String.ends_with(base, "/")), base ++ (d ++ "/"), base ++ "/" ++ (d ++ "/"))), "history") == Main.path_join(Bool.pick(String, _, d, Bool.pick(String, Bool.or(String.is_empty(base), String.ends_with(base, "/")), base ++ d, base ++ "/" ++ d)), "history") : String}
  %Equal.sym(Bool, Bool.or(String.is_empty(base), String.ends_with(base, "/")), b, eb) : {Main.path_join(Bool.pick(String, a, d ++ "/", Bool.pick(String, _, base ++ (d ++ "/"), base ++ "/" ++ (d ++ "/"))), "history") == Main.path_join(Bool.pick(String, a, d, Bool.pick(String, _, base ++ d, base ++ "/" ++ d)), "history") : String}
  slash_picked(a, b, base, d, e, f)

# `init <dir>/` makes the store `init <dir>` makes.
def slash_once(+base: String, +d: String, +e: {String.is_empty(d) == False{} : Bool}, f: {String.ends_with(d, "/") == False{} : Bool}) -> {Main.init.root(base, Some{d ++ "/"}) == Main.init.root(base, Some{d}) : String}:
  slash_cases(base, d, String.starts_with(d, "/"), {==}, Bool.or(String.is_empty(base), String.ends_with(base, "/")), {==}, e, f)

# `init .` names `<base>/./history`: `.` is joined, not resolved.
def dot_kept(+base: String, e: {String.is_empty(base) == False{} : Bool}, f: {String.ends_with(base, "/") == False{} : Bool}) -> {Main.init.root(base, Some{"."}) == base ++ "/./history" : String}:
  +inner = join_rel(base, ".", {==}, or_ff(String.is_empty(base), String.ends_with(base, "/"), e, f))
  %Equal.sym(String, Main.path_join(base, "."), base ++ "/.", inner) : {Main.path_join(_, "history") == base ++ "/./history" : String}
  +bare = Equal.trans(Bool, String.ends_with(base ++ "/.", "/"), String.ends_with("/.", "/"), False{}, ends_slash_app(base, "/.", {==}), {==})
  +outer = join_rel(base ++ "/.", "history", {==}, or_ff(String.is_empty(base ++ "/."), String.ends_with(base ++ "/.", "/"), empty_app(base, "/.", {==}), bare))
  %Equal.sym(String, Main.path_join(base ++ "/.", "history"), (base ++ "/.") ++ "/history", outer) : {_ == base ++ "/./history" : String}
  B.app_assoc(base, "/.", "/history")

# Text
# ----

# A Unicode scalar value: at most U+10FFFF, and not a surrogate.
def scalar(+x: U32) -> Bool:
  Bool.and(U32.is_le(x, 1114111), Bool.or(U32.is_lt(x, 55296), U32.is_gt(x, 57343)))

# A character the format's text holds: a newline, or a scalar value that
# is no control character — printable ASCII, the common case, asked first.
def plain(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(Bool.and(U32.is_ge(x, 32), U32.is_lt(x, 127)), Bool.or(U32.is_eq(x, 10), Bool.and(U32.is_ge(x, 160), scalar(x))))

def plains(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(plain(c), plains(t))

# Text as the format holds it: lines of plain characters, each ended by a
# newline.
def text(+s: String) -> Bool:
  Bool.and(String.ends_with(s, "\n"), plains(s))

def notes.text(ns: List<&2, Main.Note>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Main.Note{p, +t} <> rest:
      Bool.and(text(t), notes.text(rest))

def texts(l: Main.Layout) -> Bool:
  match l:
    case Main.Layout{ds, ns}:
      notes.text(ns)

# A new store
# -----------

# The text of the note a layout writes at `p`, relative to its root.
def written(ns: List<&2, Main.Note>, +p: String) -> Maybe<&2, String>:
  match ns:
    case Nil{}:
      None{}
    case Main.Note{+q, t} <> rest:
      Bool.pick(Maybe<&2, String>, String.eq(q, p), Some{t}, written(rest, p))

# `historica.txt` as `check` reads it: the bytes written there, as text.
def header.of(w: Maybe<&2, String>) -> Maybe<&2, String>:
  match w:
    case None{}:
      None{}
    case Some{t}:
      Some{Utf8.decode(Utf8.encode(t))}

# The notes a layout writes in `skipped/`, each read as `check` reads a
# rule file: the bytes written there, as the text `read_to_string` reads.
def rules(+root: String, ns: List<&2, Main.Note>) -> Check.Stating:
  match ns:
    case Nil{}:
      Check.Stating{Nil{}, Nil{}}
    case Main.Note{+p, +t} <> rest:
      +more = rules(root, rest)
      Bool.pick(Check.Stating, String.starts_with(p, "/skipped/"), Check.stating.then(Check.skipped.read(root ++ p, Store.utf8.of(Utf8.encode(t))), more), more)

# Whether a layout writes anything in a directory that holds documents.
def documents(ns: List<&2, Main.Note>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Main.Note{+p, t} <> rest:
      Bool.or(Bool.or(String.starts_with(p, "/revisions/"), Bool.or(String.starts_with(p, "/operations/"), String.starts_with(p, "/names/"))), documents(rest))

# A store holding a layout at `root` and nothing else: it writes no
# document, and what `check`'s pass gathers from it — the header, whether
# `skipped.txt` is there, and `skipped/` — is nothing to report.
def passes(+root: String, l: Main.Layout) -> Bool:
  match l:
    case Main.Layout{ds, +ns}:
      Bool.and(Bool.not(documents(ns)), List.is_empty(&2, Check.Finding, Check.found(Check.Gathered{root, header.of(written(ns, "/historica.txt")), Check.Walked{Nil{}, Nil{}}, Nil{}, Check.Walked{Nil{}, Nil{}}, Nil{}, Check.Texts{Nil{}, Nil{}}, Maybe.is_some(&2, String, written(ns, "/skipped.txt")), rules(root, ns), Check.Walked{Nil{}, Nil{}}, Nil{}})))

def main() -> Unit:
  Unit{}
