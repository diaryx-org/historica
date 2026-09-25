# The folder beside the store, and what it does not take: the working copy,
# as `historica::working` reads it.
#
# Decision 0011: the folder holding `history/` is the working copy,
# everything in it is tracked, and `history/skipped/` names the exceptions —
# one rule to a file (decision 0045), on two axes (0051): what a rule matches
# and whether it travels. Nothing is remembered between commands; the folder
# is walked every time.
#
# The host lists one directory at a time (`Store.folder`) and says what each
# entry is without following it. Everything else is decided here: which
# directories are walked at all, which files a rule keeps out, which paths
# the format can hold, and that `history/` itself is never tracked. A path
# the walk refuses — a name that is not UTF-8, a device, a path the format
# cannot spell — is left out, which is all `diff` and `blame` do with one;
# `walk.all` also says why, as `status` does.
#
# Decision 0033: a name is read in Unicode normal form C (`nfc.bend`), as
# the Rust walk reads it, so a name the filesystem hands back decomposed is
# the path it was recorded as. The folder keeps its own spelling, which is
# what has to be opened: a directory is listed by the name it was listed
# under, and `on_disk` finds a path's spelling again for a read.

import Base
import ./text.bend as T
import ./store.bend as Store
import ./bookmark.bend as Bm
import ./nfc.bend as Nfc
import ./nfc_tables.bend as Tab

def die(-A: Type, code: U32, msg: String) -> IO(A):
  IO.die(A, code, "historica: " ++ msg)

# Rules
# -----

# What a rule matches: one path, a directory and everything beneath it, a
# file's own name at any depth, or a directory's name at any depth and
# everything beneath it. A name is a pattern in which `*` is any run of
# characters and nothing else is special.
type Scope is Data:
  Scope.Path{value: String}
  Scope.Under{value: String}
  Scope.Name{pattern: String}
  Scope.NameUnder{pattern: String}

def line_error() -> String:
  "a line is a key, a space, and a value"

def value_error() -> String:
  "a value is not empty and carries no leading or trailing space"

# Rust's `char::is_whitespace`: the Unicode `White_Space` property.
def is_ws(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(Bool.or(Bool.and(U32.is_ge(x, 9), U32.is_le(x, 13)), U32.is_eq(x, 32)),
        Bool.or(Bool.or(U32.is_eq(x, 133), U32.is_eq(x, 160)),
          Bool.or(Bool.or(U32.is_eq(x, 5760), Bool.and(U32.is_ge(x, 8192), U32.is_le(x, 8202))),
            Bool.or(Bool.or(U32.is_eq(x, 8232), U32.is_eq(x, 8233)),
              Bool.or(Bool.or(U32.is_eq(x, 8239), U32.is_eq(x, 8287)), U32.is_eq(x, 12288))))))

def first_char(s: String) -> Maybe<&2, Char>:
  match s:
    case SNil{}:
      None{}
    case SCon{c, t}:
      Some{c}

def ws_at(m: Maybe<&2, Char>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{c}:
      is_ws(c)

# Empty, or with whitespace at either end: what `value != value.trim()` asks.
def untrimmed(+v: String) -> Bool:
  Bool.or(String.is_empty(v), Bool.or(ws_at(first_char(v)), ws_at(first_char(String.reverse(v)))))

def trim_slashes(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{'/', t}:
      trim_slashes(t)
    case SCon{c, t}:
      String.reverse(SCon{c, t})

def all_stars(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{'*', t}:
      all_stars(t)
    case SCon{c, t}:
      False{}

def has_slash(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{'/', t}:
      True{}
    case SCon{c, t}:
      has_slash(t)

def pattern(+v: String) -> Result<&2, &2, String, String>:
  Bool.pick(Result<&2, &2, String, String>, String.is_empty(v), Fail{"a pattern is not empty"},
    Bool.pick(Result<&2, &2, String, String>, has_slash(v), Fail{"a pattern is one path component and holds no `/`: a path is spelled with `skip`"},
      Bool.pick(Result<&2, &2, String, String>, all_stars(v), Fail{"a pattern of nothing but `*` is the whole folder, which rules exist to name the exceptions to"},
        Done{v})))

def scope.named(+v: String, under: Bool) -> Result<&2, &2, String, Scope>:
  match under:
    case True{}:
      Result.map(&2, &2, String, String, Scope, p => Scope.NameUnder{p}, pattern(v))
    case False{}:
      Result.map(&2, &2, String, String, Scope, p => Scope.Name{p}, pattern(v))

def scope.of(+v: String, name: Bool, +under: Bool) -> Result<&2, &2, String, Scope>:
  match name:
    case False{}:
      Bool.pick(Result<&2, &2, String, Scope>, under, Done{Scope.Under{v}}, Done{Scope.Path{v}})
    case True{}:
      scope.named(v, under)

def scope.value(+v: String, name: Bool) -> Result<&2, &2, String, Scope>:
  +bare = trim_slashes(String.reverse(v))
  Bool.pick(Result<&2, &2, String, Scope>, String.is_empty(bare), Fail{value_error()}, scope.of(bare, name, String.ends_with(v, "/")))

def scope.keyed(+v: String, path: Bool, name: Bool, retired: Bool) -> Result<&2, &2, String, Scope>:
  match path:
    case True{}:
      scope.value(v, False{})
    case False{}:
      match name:
        case True{}:
          scope.value(v, True{})
        case False{}:
          match retired:
            case True{}:
              Fail{"`skip-suffix` is retired: an ending is now `skip-name *` and the ending, matched against a file's own name"}
            case False{}:
              Fail{"the keys are `skip`, `skip-name`, `private` and `private-name`"}

def scope.key(+k: String, +v: String) -> Result<&2, &2, String, Scope>:
  scope.keyed(v, Bool.or(String.eq(k, "skip"), String.eq(k, "private")), Bool.or(String.eq(k, "skip-name"), String.eq(k, "private-name")), String.eq(k, "skip-suffix"))

def scope.cut(cut: Maybe<&2, T.Split>) -> Result<&2, &2, String, Scope>:
  match cut:
    case None{}:
      Fail{line_error()}
    case Some{T.Split{k, +v}}:
      Bool.pick(Result<&2, &2, String, Scope>, untrimmed(v), Fail{value_error()}, scope.key(k, v))

# `Rule::parse`: one line.
def scope(+line: String) -> Result<&2, &2, String, Scope>:
  scope.cut(T.split_once(line))

# What one line of a rule file is.
type Said is Data:
  Said.Nothing{}
  Said.Rule{scope: Scope}
  Said.Wrong{because: String}

def said.of(r: Result<&2, &2, String, Scope>) -> Said:
  match r:
    case Fail{e}:
      Said.Wrong{e}
    case Done{s}:
      Said.Rule{s}

def said(+line: String) -> Said:
  Bool.pick(Said, Bool.or(String.is_empty(line), String.starts_with(line, "#")), Said.Nothing{}, said.of(scope(line)))

# `str::lines`: split at each newline, a `\r` before it dropped, and no
# empty line after a final newline.
def unreturned(+l: String) -> String:
  Bool.pick(String, String.ends_with(l, "\r"), String.take(l, Nat.sub(String.length(l), 1n)), l)

def lines.trimmed(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> Nil{}:
      Bool.pick(List<&2, String>, String.is_empty(l), Nil{}, [unreturned(l)])
    case l <> rest:
      unreturned(l) <> lines.trimmed(rest)

# What a file states so far: nothing, one rule, or why it is not a rule file.
type Stated is Data:
  Stated.None{}
  Stated.One{scope: Scope}
  Stated.Wrong{error: String}

def stated.line(st: Stated, +at: Nat, s: Said) -> Stated:
  match st s:
    case Stated.Wrong{e} _:
      Stated.Wrong{e}
    case Stated.None{} Said.Nothing{}:
      Stated.None{}
    case Stated.None{} Said.Rule{sc}:
      Stated.One{sc}
    case Stated.None{} Said.Wrong{e}:
      Stated.Wrong{"line " ++ Nat.show(at) ++ ": " ++ e}
    case Stated.One{sc} Said.Nothing{}:
      Stated.One{sc}
    case Stated.One{sc} _:
      Stated.Wrong{"line " ++ Nat.show(at) ++ ": a file states one rule, and this is a second"}

def stated.go(ls: List<&2, String>, +at: Nat, st: Stated) -> Stated:
  match ls:
    case Nil{}:
      st
    case +l <> rest:
      stated.go(rest, 1n+at, stated.line(st, at, said(l)))

# What a stated rule is: a path with a value, or a name that is one
# component, not empty and not only `*` (`LAWS.rules_are_well_formed`).
def scope.ok(sc: Scope) -> Bool:
  match sc:
    case Scope.Path{+v}:
      Bool.not(String.is_empty(v))
    case Scope.Under{+v}:
      Bool.not(String.is_empty(v))
    case Scope.Name{+p}:
      Bool.and(Bool.not(String.is_empty(p)), Bool.and(Bool.not(has_slash(p)), Bool.not(all_stars(p))))
    case Scope.NameUnder{+p}:
      Bool.and(Bool.not(String.is_empty(p)), Bool.and(Bool.not(has_slash(p)), Bool.not(all_stars(p))))

def stated.ok(st: Stated) -> Bool:
  match st:
    case Stated.One{sc}:
      scope.ok(sc)
    case Stated.None{}:
      True{}
    case Stated.Wrong{e}:
      True{}

# `Skipped::rule_in`: the rule one file states, if any.
def rule_in(+text: String) -> Stated:
  stated.go(lines.trimmed(String.split(text, '\n')), 1n, Stated.None{})

# Matching
# --------

def until_slash(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{'/', t}:
      SNil{}
    case SCon{c, t}:
      SCon{c, until_slash(t)}

def last_component(+path: String) -> String:
  String.reverse(until_slash(String.reverse(path)))

# What follows the first place `run` stands in `s`.
def after(s: String, +run: String, +n: Nat, hit: Bool) -> Maybe<&2, String>:
  match s hit:
    case SNil{} True{}:
      Some{SNil{}}
    case SNil{} False{}:
      None{}
    case SCon{c, t} True{}:
      Some{String.drop(SCon{c, t}, n)}
    case SCon{c, +t} False{}:
      after(t, run, n, String.starts_with(t, run))

# `Pattern::matches`, past the first run: each run between stars found at
# its leftmost, and the last one ending the component.
def runs.match(runs: List<&2, String>, m: Maybe<&2, String>) -> Bool:
  match runs m:
    case _ None{}:
      False{}
    case Nil{} Some{s}:
      String.is_empty(s)
    case +last <> Nil{} Some{+s}:
      Bool.and(Nat.is_ge(String.length(s), String.length(last)), String.ends_with(s, last))
    case +run <> more Some{+s}:
      runs.match(more, after(s, run, String.length(run), String.starts_with(s, run)))

def matches.of(+component: String, runs: List<&2, String>) -> Bool:
  match runs:
    case Nil{}:
      String.is_empty(component)
    case +first <> rest:
      Bool.and(String.starts_with(component, first), runs.match(rest, Some{String.drop(component, String.length(first))}))

def matches(+pattern: String, +component: String) -> Bool:
  matches.of(component, String.split(pattern, '*'))

def any_but_last(+pattern: String, parts: List<&2, String>) -> Bool:
  match parts:
    case Nil{}:
      False{}
    case p <> Nil{}:
      False{}
    case p <> rest:
      Bool.or(matches(pattern, p), any_but_last(pattern, rest))

def covers(sc: Scope, +path: String) -> Bool:
  match sc:
    case Scope.Path{v}:
      String.eq(path, v)
    case Scope.Under{v}:
      String.starts_with(path, v ++ "/")
    case Scope.Name{p}:
      matches(p, last_component(path))
    case Scope.NameUnder{p}:
      any_but_last(p, String.split(path, '/'))

# `Skipped::skips`: whether history takes this file.
def skips(rules: List<&2, Scope>, +path: String) -> Bool:
  match rules:
    case Nil{}:
      False{}
    case sc <> rest:
      Bool.or(covers(sc, path), skips(rest, path))

def covers_directory(sc: Scope, +path: String) -> Bool:
  match sc:
    case Scope.Path{v}:
      String.eq(path, v)
    case Scope.Under{v}:
      String.eq(path, v)
    case Scope.Name{p}:
      False{}
    case Scope.NameUnder{p}:
      matches(p, last_component(path))

# `Skipped::skips_directory`: whether a directory is skipped whole.
def skips_directory(rules: List<&2, Scope>, +path: String) -> Bool:
  match rules:
    case Nil{}:
      False{}
    case sc <> rest:
      Bool.or(covers_directory(sc, path), skips_directory(rest, path))

# Reading the rules
# -----------------

# Decision 0022: a name the platform writes into every directory it touches.
def platform_name(+name: String) -> Bool:
  Bool.or(String.starts_with(name, "._"),
    Bool.or(Bool.or(String.eq(name, ".DS_Store"), String.eq(name, "Thumbs.db")),
      Bool.or(Bool.or(String.eq(name, "desktop.ini"), String.eq(name, ".localized")),
        Bool.or(String.eq(name, ".directory"), String.eq(name, "@eaDir")))))

# A rule's value in normal form C, as `Rule::parse` stores it once it has
# checked it: the walk's paths are in that form, and a rule matches them.
def scope.normal(sc: Scope) -> Scope:
  match sc:
    case Scope.Path{v}:
      Scope.Path{Nfc.nfc(v)}
    case Scope.Under{v}:
      Scope.Under{Nfc.nfc(v)}
    case Scope.Name{p}:
      Scope.Name{Nfc.nfc(p)}
    case Scope.NameUnder{p}:
      Scope.NameUnder{Nfc.nfc(p)}

def rules.stated(+file: String, st: Stated) -> IO(List<&2, Scope>):
  match st:
    case Stated.None{}:
      IO.pure(List<&2, Scope>, Nil{})
    case Stated.One{sc}:
      IO.pure(List<&2, Scope>, [scope.normal(sc)])
    case Stated.Wrong{e}:
      die(List<&2, Scope>, 1, file ++ ": " ++ e)

# In path order, so the file refused is the first the Rust loader reaches.
def rules.go(+root: String, paths: List<&2, String>) -> IO(List<&2, Scope>):
  match paths:
    case Nil{}:
      IO.pure(List<&2, Scope>, Nil{})
    case +p <> rest:
      do IO<List<&2, Scope>>:
        +file : String = root ++ "/" ++ p
        text : String <- Store.read_text(file)
        here : List<&2, Scope> <- rules.stated(file, rule_in(text))
        later : List<&2, Scope> <- rules.go(root, rest)
        return List.append(&2, Scope, here, later)

def rules.keep(+p: String, +rest: List<&2, String>) -> List<&2, String>:
  Bool.pick(List<&2, String>, Bool.or(String.is_empty(p), platform_name(last_component(p))), rest, p <> rest)

def rules.kept(ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      rules.keep(p, rules.kept(rest))

# `read_skipped`: every rule `history/skipped/` states, the store refused in
# the words the Rust tool uses where a file there is not one rule.
def rules(+root: String) -> IO(List<&2, Scope>):
  do IO<List<&2, Scope>>:
    paths : List<&2, String> <- Store.skipped_paths(root)
    rules.go(root, rules.kept(paths))

# The walk
# --------

# A tracked file: a regular one, with whether it can be run and its length,
# or a link and where it points.
type Found is Data:
  Found.File{path: String, runs: Bool, size: Nat}
  Found.Link{path: String, target: String}

def found.path(f: Found) -> String:
  match f:
    case Found.File{p, r, n}:
      p
    case Found.Link{p, t}:
      p

# One directory's listing as it is read: the directories to walk next, the
# files found so far, and — after an `l` line — the link whose target the
# next line is, empty where the link is not tracked.
type Listing is Data:
  Listing{dirs: List<&2, String>, found: List<&2, Found>, link: Maybe<&2, String>}

def joined(+prefix: String, +name: String) -> String:
  Bool.pick(String, String.is_empty(prefix), name, prefix ++ "/" ++ name)

# `history/` is not tracked, and says so without a rule.
def is_store(+prefix: String, +name: String) -> Bool:
  Bool.and(String.is_empty(prefix), String.eq(name, "history"))

# Whether the walk takes a file: not the store, not skipped, and a path the
# format can hold.
def tracked(+prefix: String, +name: String, +rules: List<&2, Scope>) -> Bool:
  +path = joined(prefix, name)
  Bool.and(Bool.not(is_store(prefix, name)), Bool.and(Bool.not(skips(rules, path)), Bm.name_ok(path)))

def listing.took(dirs: List<&2, String>, +found: List<&2, Found>, +prefix: String, +runs: Bool, size: String, +name: String, take: Bool) -> Listing:
  match take:
    case True{}:
      Listing{dirs, Found.File{joined(prefix, name), runs, Maybe.default(&2, Nat, Nat.read(size), 0n)} <> found, None{}}
    case False{}:
      Listing{dirs, found, None{}}

def listing.file(dirs: List<&2, String>, +found: List<&2, Found>, +prefix: String, +rules: List<&2, Scope>, +runs: Bool, cut: Maybe<&2, T.Split>) -> Listing:
  match cut:
    case None{}:
      Listing{dirs, found, None{}}
    case Some{T.Split{size, +name}}:
      listing.took(dirs, found, prefix, runs, size, name, tracked(prefix, name, rules))

def listing.dir(+dirs: List<&2, String>, +found: List<&2, Found>, +prefix: String, +rules: List<&2, Scope>, +name: String, skip: Bool) -> Listing:
  match skip:
    case True{}:
      Listing{dirs, found, None{}}
    case False{}:
      Listing{joined(prefix, name) <> dirs, found, None{}}

def listing.link(+dirs: List<&2, String>, +found: List<&2, Found>, +prefix: String, +name: String, take: Bool) -> Listing:
  match take:
    case True{}:
      Listing{dirs, found, Some{joined(prefix, name)}}
    case False{}:
      Listing{dirs, found, Some{SNil{}}}

# What an entry's kind letter is: `d`, `f`, `l`, or anything else.
def listing.kind(+dirs: List<&2, String>, +found: List<&2, Found>, +prefix: String, +rules: List<&2, Scope>, +name: String, d: Bool, f: Bool, l: Bool) -> Listing:
  match d:
    case True{}:
      listing.dir(dirs, found, prefix, rules, name, Bool.or(is_store(prefix, name), skips_directory(rules, joined(prefix, name))))
    case False{}:
      match f:
        case True{}:
          listing.file(dirs, found, prefix, rules, String.starts_with(name, "1"), T.split_once(String.drop(name, 2n)))
        case False{}:
          match l:
            case True{}:
              listing.link(dirs, found, prefix, name, tracked(prefix, name, rules))
            case False{}:
              Listing{dirs, found, None{}}

def listing.entry(+dirs: List<&2, String>, +found: List<&2, Found>, +prefix: String, +rules: List<&2, Scope>, +name: String, +kind: String) -> Listing:
  listing.kind(dirs, found, prefix, rules, name, String.eq(kind, "d"), String.eq(kind, "f"), String.eq(kind, "l"))

def listing.linked(dirs: List<&2, String>, +found: List<&2, Found>, +p: String, line: String, empty: Bool) -> Listing:
  match empty:
    case True{}:
      Listing{dirs, found, None{}}
    case False{}:
      Listing{dirs, Found.Link{p, line} <> found, None{}}

def listing.line(l: Listing, +prefix: String, +rules: List<&2, Scope>, +line: String) -> Listing:
  match l:
    case Listing{dirs, found, Some{+p}}:
      listing.linked(dirs, found, p, line, String.is_empty(p))
    case Listing{dirs, found, None{}}:
      listing.entry(dirs, found, prefix, rules, String.drop(line, 2n), String.take(line, 1n))

# What a listing may hold: no file and no link a rule skips, no directory
# a rule skips whole, and a link waiting for its target only where the link
# is tracked (`LAWS.listing_skips_nothing`).
def none_skipped(+rules: List<&2, Scope>, fs: List<&2, Found>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case f <> rest:
      Bool.and(Bool.not(skips(rules, found.path(f))), none_skipped(rules, rest))

def dirs_kept(+rules: List<&2, Scope>, ds: List<&2, String>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case +d <> rest:
      Bool.and(Bool.not(skips_directory(rules, d)), dirs_kept(rules, rest))

def link_kept(+rules: List<&2, Scope>, link: Maybe<&2, String>) -> Bool:
  match link:
    case None{}:
      True{}
    case Some{+p}:
      Bool.or(String.is_empty(p), Bool.not(skips(rules, p)))

def listing.ok(+rules: List<&2, Scope>, l: Listing) -> Bool:
  match l:
    case Listing{dirs, found, link}:
      Bool.and(dirs_kept(rules, dirs), Bool.and(none_skipped(rules, found), link_kept(rules, link)))

def listing.go(ls: List<&2, String>, +prefix: String, +rules: List<&2, Scope>, l: Listing) -> Listing:
  match ls:
    case Nil{}:
      l
    case line <> rest:
      listing.go(rest, prefix, rules, listing.line(l, prefix, rules, line))

def listing.dirs(l: Listing) -> List<&2, String>:
  match l:
    case Listing{dirs, found, link}:
      dirs

def listing.found(l: Listing) -> List<&2, Found>:
  match l:
    case Listing{dirs, found, link}:
      found

# A directory that will not be read is not a fact about the folder; it is
# not knowing, and the command stops.
def listed.of(r: Result<&1, &1, U32 & String, String>) -> IO(String):
  match r:
    case Fail{Tuple{code, msg}}:
      die(String, 1, msg)
    case Done{text}:
      IO.pure(String, text)

def listed(+dir: String) -> IO(String):
  do IO<String>:
    r : Result<&1, &1, U32 & String, String> <- Store.listing_of(dir)
    listed.of(r)

# Refusals
# --------

# Rust's `char::is_control`: C0, DEL and C1.
def is_control(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(U32.is_lt(x, 32), Bool.and(U32.is_ge(x, 127), U32.is_lt(x, 160)))

# Why `check_path` refuses a path a listing can hand back: a name, or names
# joined, is never empty and holds no `.` or `..` component, so what is left
# is space at either end and a control character. Unicode normal form C is
# not here, as nowhere in this port.
def path_fault(+path: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, Bool.or(String.starts_with(path, " "), String.ends_with(path, " ")), Some{"it has leading or trailing space"},
    Bool.pick(Maybe<&2, String>, List.any(~&2, ~Char, ~is_control, String.to_list(path)), Some{"it holds a control character"}, None{}))

# What one entry is refused for, in `working::walk`'s order: the store and
# what a rule skips are never refused; then anything that is neither a file
# nor a link; then a path the format cannot spell; then a link whose target
# is not UTF-8.
def refusal.spelled(+path: String, fault: Maybe<&2, String>, unreadable: Bool) -> Maybe<&2, T.Split>:
  match fault:
    case Some{because}:
      Some{T.Split{path, because}}
    case None{}:
      Bool.pick(Maybe<&2, T.Split>, unreadable, Some{T.Split{path, "a link pointing at a name that is not UTF-8"}}, None{})

def refusal.kind(+path: String, other: Bool, unreadable: Bool) -> Maybe<&2, T.Split>:
  match other:
    case True{}:
      Some{T.Split{path, "not a regular file"}}
    case False{}:
      refusal.spelled(path, path_fault(path), unreadable)

def refusal.of(+prefix: String, +rules: List<&2, Scope>, +name: String, other: Bool, unreadable: Bool) -> Maybe<&2, T.Split>:
  Bool.pick(Maybe<&2, T.Split>, Bool.or(is_store(prefix, name), skips(rules, joined(prefix, name))), None{}, refusal.kind(joined(prefix, name), other, unreadable))

def refusal.push(r: Maybe<&2, T.Split>, rest: List<&2, T.Split>) -> List<&2, T.Split>:
  match r:
    case None{}:
      rest
    case Some{x}:
      x <> rest

def refusal.file(+prefix: String, +rules: List<&2, Scope>, cut: Maybe<&2, T.Split>) -> Maybe<&2, T.Split>:
  match cut:
    case None{}:
      None{}
    case Some{T.Split{size, +name}}:
      refusal.of(prefix, rules, name, False{}, False{})

# One listing line: `f` and `l` are refused only for their spelling, `L`
# for its target too, `o` for what it is; `d` is walked and `u` has no name
# to report.
def refusal.line.of(+prefix: String, +rules: List<&2, Scope>, +kind: String, +name: String) -> Maybe<&2, T.Split>:
  Bool.pick(Maybe<&2, T.Split>, String.eq(kind, "f"), refusal.file(prefix, rules, T.split_once(String.drop(name, 2n))),
  Bool.pick(Maybe<&2, T.Split>, Bool.or(String.eq(kind, "l"), String.eq(kind, "L")), refusal.of(prefix, rules, name, False{}, String.eq(kind, "L")),
  Bool.pick(Maybe<&2, T.Split>, String.eq(kind, "o"), refusal.of(prefix, rules, name, True{}, False{}), None{})))

def refusal.line(+prefix: String, +rules: List<&2, Scope>, +line: String) -> Maybe<&2, T.Split>:
  refusal.line.of(prefix, rules, String.take(line, 1n), String.drop(line, 2n))

# A listing's refusals, onto `acc`: `after` says the line is the target of
# the link before it, which is no entry.
def refusals.go(ls: List<&2, String>, +prefix: String, +rules: List<&2, Scope>, after: Bool, acc: List<&2, T.Split>) -> List<&2, T.Split>:
  match ls after:
    case Nil{} _:
      acc
    case line <> rest True{}:
      refusals.go(rest, prefix, rules, False{}, acc)
    case +line <> rest False{}:
      refusals.go(rest, prefix, rules, String.eq(String.take(line, 1n), "l"), refusal.push(refusal.line(prefix, rules, line), acc))

# What `LAWS.walk_refuses_nothing_skipped` asks of refusals: none names a
# path a rule skips, since a rule is how a person silences one.
def refusal_ok(+rules: List<&2, Scope>, r: Maybe<&2, T.Split>) -> Bool:
  match r:
    case None{}:
      True{}
    case Some{T.Split{+p, b}}:
      Bool.not(skips(rules, p))

def refused_kept(+rules: List<&2, Scope>, rs: List<&2, T.Split>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case T.Split{+p, b} <> rest:
      Bool.and(Bool.not(skips(rules, p)), refused_kept(rules, rest))

# The order `working::walk` meets paths in: each directory's names in byte
# order, a directory's contents where its name falls. That is path order
# with `/` below every other character, and no name holds a NUL. It is
# taken over code points, which leaves room above every character for a
# place no name spells.
def walked_points(cs: List<&2, Char>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case Chr{+x} <> rest:
      Bool.pick(U32, U32.is_eq(x, 47), 0, x) <> walked_points(rest)

def points.le(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  match a b:
    case Nil{} _:
      True{}
    case x <> xs Nil{}:
      False{}
    case +x <> xs +y <> ys:
      Bool.or(U32.is_lt(x, y), Bool.and(U32.is_eq(x, y), points.le(xs, ys)))

def refused.path(r: T.Split) -> String:
  match r:
    case T.Split{p, b}:
      p

# Names in normal form C
# ---------------------

# A listing as the walk reads it: each entry's name in normal form C, and a
# link's target, on the line after it, as the folder spells it — a target
# is a string, and `record` resolves it before it normalises it. A name
# that cannot be spelled stays as the host spelled it.
def normal.sized(+runs: String, cut: Maybe<&2, T.Split>) -> String:
  match cut:
    case None{}:
      runs
    case Some{T.Split{size, name}}:
      runs ++ " " ++ size ++ " " ++ Nfc.nfc(name)

def normal.file(cut: Maybe<&2, T.Split>) -> String:
  match cut:
    case None{}:
      SNil{}
    case Some{T.Split{runs, rest}}:
      normal.sized(runs, T.split_once(rest))

def normal.line(+line: String) -> String:
  Bool.pick(String, String.starts_with(line, "f "), "f " ++ normal.file(T.split_once(String.drop(line, 2n))),
    Bool.pick(String, String.starts_with(line, "u "), line, String.take(line, 2n) ++ Nfc.nfc(String.drop(line, 2n))))

def normal.lines(ls: List<&2, String>, after: Bool) -> List<&2, String>:
  match ls after:
    case Nil{} _:
      Nil{}
    case line <> rest True{}:
      line <> normal.lines(rest, False{})
    case +line <> rest False{}:
      normal.line(line) <> normal.lines(rest, String.starts_with(line, "l "))

# The name a listing line gives its entry.
def entry.sized(cut: Maybe<&2, T.Split>) -> String:
  match cut:
    case None{}:
      SNil{}
    case Some{T.Split{size, name}}:
      name

def entry.file(cut: Maybe<&2, T.Split>) -> String:
  match cut:
    case None{}:
      SNil{}
    case Some{T.Split{runs, rest}}:
      entry.sized(T.split_once(rest))

def entry.name(+line: String) -> String:
  Bool.pick(String, String.starts_with(line, "f "), entry.file(T.split_once(String.drop(line, 2n))), String.drop(line, 2n))

# The directories a listing walks next, as the folder spells them: those
# `listing.dir` takes, in the order the listing holds them.
def raw.dir(+line: String, +prefix: String, +disk: String, +rules: List<&2, Scope>, d: Bool, +later: List<&2, String>) -> List<&2, String>:
  match d:
    case False{}:
      later
    case True{}:
      +name = Nfc.nfc(String.drop(line, 2n))
      Bool.pick(List<&2, String>, Bool.or(is_store(prefix, name), skips_directory(rules, joined(prefix, name))), later, joined(disk, String.drop(line, 2n)) <> later)

def raw.dirs(ls: List<&2, String>, +prefix: String, +disk: String, +rules: List<&2, Scope>, after: Bool) -> List<&2, String>:
  match ls after:
    case Nil{} _:
      Nil{}
    case line <> rest True{}:
      raw.dirs(rest, prefix, disk, rules, False{})
    case +line <> rest False{}:
      raw.dir(line, prefix, disk, rules, String.starts_with(line, "d "), raw.dirs(rest, prefix, disk, rules, String.starts_with(line, "l ")))

# Each directory to walk, as the walk names it and as the folder spells it.
def paired(ns: List<&2, String>, ds: List<&2, String>) -> List<&2, T.Split>:
  match ns ds:
    case n <> nr d <> dr:
      T.Split{n, d} <> paired(nr, dr)
    case _ _:
      Nil{}

# Two names the filesystem tells apart can be one path in normal form C;
# the Rust walk keeps the one it met last, which a stable sort of the walk's
# files — each put on the front as it was met — leaves first.
def distinct.same(fs: List<&2, Found>, +last: String) -> Bool:
  match fs:
    case f <> rest:
      String.eq(found.path(f), last)
    case _:
      False{}

def distinct.go(fs: List<&2, Found>, +last: String, same: Bool) -> List<&2, Found>:
  match fs same:
    case Nil{} _:
      Nil{}
    case f <> +rest True{}:
      distinct.go(rest, last, distinct.same(rest, last))
    case +f <> +rest False{}:
      f <> distinct.go(rest, found.path(f), distinct.same(rest, found.path(f)))

def distinct(fs: List<&2, Found>) -> List<&2, Found>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> +rest:
      f <> distinct.go(rest, found.path(f), distinct.same(rest, found.path(f)))

# No two files in a row at one path: what `LAWS.the_walk_yields_a_path_once`
# says of what the walk yields.
def apart.go(fs: List<&2, Found>, +last: String) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case +f <> rest:
      Bool.and(Bool.not(String.eq(found.path(f), last)), apart.go(rest, found.path(f)))

def apart(fs: List<&2, Found>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case +f <> rest:
      apart.go(rest, found.path(f))

# Names that cannot be spelled
# ----------------------------

# A name the host cannot spell as UTF-8 is refused in the Rust tool's words
# whatever the rules say, since no rule can name it, and is not walked
# into: `WorkingError::NotUtf8`. The host hands the name over as
# `to_string_lossy` spells it, and the refusal names where it is on disk,
# as the Rust tool's does.
def unspelled.because() -> String:
  "not a name this format can hold"

# A refusal and where the walk met it.
type Keyed is Data:
  Keyed{key: List<&2, U32>, refusal: T.Split}

def keyed.key(k: Keyed) -> List<&2, U32>:
  match k:
    case Keyed{key, r}:
      key

def keyed.refusal(k: Keyed) -> T.Split:
  match k:
    case Keyed{key, r}:
      r

# Where the `k`th name that cannot be spelled after `before` was met: after
# `before` and all beneath it, and before the entry after it. Its lossy
# spelling cannot say, since it does not sort as the bytes do.
def unspelled.key(+before: String, +k: U32) -> List<&2, U32>:
  List.append(&2, U32, walked_points(String.to_list(before)), [0, (1114112 + k : U32)])

def unspelled.is(ls: List<&2, String>) -> Bool:
  match ls:
    case +line <> rest:
      String.starts_with(line, "u ")
    case _:
      False{}

# A listing's names that cannot be spelled, keyed: `before` is the path of
# the entry before, or the directory's own with a `/` after it; `after`
# says the line is the target of the link before it, and `odd` that it
# names what cannot be spelled.
def unspelled.go(ls: List<&2, String>, +prefix: String, +dir: String, +before: String, +k: U32, after: Bool, odd: Bool, acc: List<&2, Keyed>) -> List<&2, Keyed>:
  match ls after odd:
    case Nil{} _ _:
      acc
    case line <> +rest True{} _:
      unspelled.go(rest, prefix, dir, before, k, False{}, unspelled.is(rest), acc)
    case +line <> +rest False{} True{}:
      unspelled.go(rest, prefix, dir, before, (k + 1 : U32), False{}, unspelled.is(rest), Keyed{unspelled.key(before, k), T.Split{dir ++ "/" ++ String.drop(line, 2n), unspelled.because()}} <> acc)
    case +line <> +rest False{} False{}:
      unspelled.go(rest, prefix, dir, joined(prefix, entry.name(line)), 0, String.starts_with(line, "l "), unspelled.is(rest), acc)

# How many names a listing holds that cannot be spelled: its `u` lines, a
# link's target aside, with `odd` saying whether the line at the head is
# one. What `LAWS.a_name_that_cannot_be_spelled_is_refused` counts the
# refusals against.
def unspelled.count(ls: List<&2, String>, after: Bool, odd: Bool) -> Nat:
  match ls after odd:
    case Nil{} _ _:
      0n
    case line <> +rest True{} _:
      unspelled.count(rest, False{}, unspelled.is(rest))
    case line <> +rest False{} True{}:
      1n+unspelled.count(rest, False{}, unspelled.is(rest))
    case +line <> +rest False{} False{}:
      unspelled.count(rest, String.starts_with(line, "l "), unspelled.is(rest))

# `ls` as the walk reads it, `prefix` the directory's path, and `dir` where
# it is on disk.
def unspelled(+ls: List<&2, String>, +prefix: String, +dir: String) -> List<&2, Keyed>:
  unspelled.go(ls, prefix, dir, Bool.pick(String, String.is_empty(prefix), SNil{}, prefix ++ "/"), 0, False{}, unspelled.is(ls), Nil{})

def keyed.all(rs: List<&2, T.Split>) -> List<&2, Keyed>:
  match rs:
    case Nil{}:
      Nil{}
    case +r <> rest:
      Keyed{walked_points(String.to_list(refused.path(r))), r} <> keyed.all(rest)

def unkeyed(ks: List<&2, Keyed>) -> List<&2, T.Split>:
  match ks:
    case Nil{}:
      Nil{}
    case k <> rest:
      keyed.refusal(k) <> unkeyed(rest)

# Every refusal in the order the Rust walk makes them.
def walk.refusals(rs: List<&2, T.Split>, odd: List<&2, Keyed>) -> List<&2, T.Split>:
  unkeyed(List.sort(~Keyed, ~(a => b => points.le(keyed.key(a), keyed.key(b))), List.append(&2, Keyed, keyed.all(rs), odd)))

# The walk
# --------

# Everything one walk of the folder turned up: the files it tracks, and the
# paths it refused with why.
type Walked is Data:
  Walked{found: List<&2, Found>, refused: List<&2, T.Split>}

def walked.found(w: Walked) -> List<&2, Found>:
  match w:
    case Walked{found, refused}:
      found

def walked.refused(w: Walked) -> List<&2, T.Split>:
  match w:
    case Walked{found, refused}:
      refused

# One directory at a time: `pending` holds each still to list, as the walk
# names it and as the folder spells it, and `odd` the names that cannot be
# spelled, keyed.
def walk.go(fuel: Nat, +repo: String, +rules: List<&2, Scope>, pending: List<&2, T.Split>, found: List<&2, Found>, refused: List<&2, T.Split>, odd: List<&2, Keyed>) -> IO(Walked):
  match fuel pending:
    case 0n _:
      IO.pure(Walked, Walked{found, walk.refusals(refused, odd)})
    case 1n+q Nil{}:
      IO.pure(Walked, Walked{found, walk.refusals(refused, odd)})
    case 1n+q T.Split{+dir, +disk} <> rest:
      do IO<Walked>:
        +at : String = Bool.pick(String, String.is_empty(disk), repo, repo ++ "/" ++ disk)
        got : String <- listed(at)
        +raw : List<&2, String> = String.split(got, '\n')
        +ls : List<&2, String> = normal.lines(raw, False{})
        +l : Listing = listing.go(ls, dir, rules, Listing{Nil{}, found, None{}})
        +next : List<&2, T.Split> = paired(listing.dirs(l), List.reverse(&2, String, raw.dirs(raw, dir, disk, rules, False{})))
        walk.go(q, repo, rules, List.append(&2, T.Split, next, rest), listing.found(l), refusals.go(ls, dir, rules, False{}, refused), List.append(&2, Keyed, unspelled(ls, dir, at), odd))

# Every file the working copy tracks, in path order, and every path it
# refused, in the order the Rust walk refuses them.
def walk.all(+repo: String, +rules: List<&2, Scope>) -> IO(Walked):
  do IO<Walked>:
    w : Walked <- walk.go(U32.to_nat(1000000), repo, rules, [T.Split{SNil{}, SNil{}}], Nil{}, Nil{}, Nil{})
    +w2 : Walked = w
    return Walked{distinct(List.sort(~Found, ~(a => b => String.is_le(found.path(a), found.path(b))), walked.found(w2))), walked.refused(w2)}

# Every file the working copy tracks, in path order.
def walk(+repo: String, +rules: List<&2, Scope>) -> IO(List<&2, Found>):
  do IO<List<&2, Found>>:
    w : Walked <- walk.all(repo, rules)
    return walked.found(w)

# Where a path is on disk
# -----------------------

# A path of ASCII none of whose characters another character decomposes to
# has one spelling, itself: `nfc_tables.bend` says which those are.
def member(xs: List<&2, U32>, +x: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(U32.is_eq(y, x), member(rest, x))

def plain(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{+x}, t}:
      Bool.and(Bool.and(U32.is_lt(x, 128), Bool.not(member(Tab.ascii_images(), x))), plain(t))

# Whether this line spells `want`.
def spelling.take(+line: String, +want: String, got: Maybe<&2, String>) -> Maybe<&2, String>:
  +name = entry.name(line)
  Bool.pick(Maybe<&2, String>, Bool.and(Bool.not(String.starts_with(line, "u ")), String.eq(Nfc.nfc(name), want)), Some{name}, got)

# The name a listing spells `want` with: the last whose normal form it is,
# as the walk keeps the last.
def spelling.go(ls: List<&2, String>, +want: String, got: Maybe<&2, String>, after: Bool) -> Maybe<&2, String>:
  match ls after:
    case Nil{} _:
      got
    case line <> rest True{}:
      spelling.go(rest, want, got, False{})
    case +line <> rest False{}:
      spelling.go(rest, want, spelling.take(line, want, got), String.starts_with(line, "l "))

def spelling(ls: List<&2, String>, +want: String) -> String:
  Maybe.default(&2, String, spelling.go(ls, want, None{}, False{}), want)

def listing.lines(r: Result<&1, &1, U32 & String, String>) -> List<&2, String>:
  match r:
    case Fail{e}:
      Nil{}
    case Done{text}:
      String.split(text, '\n')

# A directory's listing, from those read already or from the host. One
# that will not be read spells nothing, and the read that follows fails in
# the host's words.
def listing.read(+dir: String, cached: Maybe<&2, List<&2, String>>) -> IO(List<&2, String>):
  match cached:
    case Some{ls}:
      IO.pure(List<&2, String>, ls)
    case None{}:
      do IO<List<&2, String>>:
        r : Result<&1, &1, U32 & String, String> <- Store.listing_of(dir)
        return listing.lines(r)

# A path spelled as far as it has been, and the listings read so far.
type Spelt is Data:
  Spelt{path: String, seen: Map<&2, List<&2, String>>}

def spelt.path(s: Spelt) -> String:
  match s:
    case Spelt{p, m}:
      p

def spelt.seen(s: Spelt) -> Map<&2, List<&2, String>>:
  match s:
    case Spelt{p, m}:
      m

def cached.of(ls: List<&2, String>) -> Maybe<&2, List<&2, String>>:
  match ls:
    case Nil{}:
      None{}
    case l <> rest:
      Some{l <> rest}

def cached(r: Map<&2, List<&2, String>> & List<&2, String>) -> Maybe<&2, List<&2, String>>:
  (m, ls) = r
  cached.of(ls)

def on_disk.plain(ps: List<&2, String>) -> Bool:
  match ps:
    case c <> rest:
      plain(c)
    case _:
      True{}

# One component after another: one that has one spelling as it is, and any
# other read against the listing of the directory it is in.
def on_disk.go(parts: List<&2, String>, +repo: String, +at: String, +seen: Map<&2, List<&2, String>>, simple: Bool) -> IO(Spelt):
  match parts simple:
    case Nil{} _:
      IO.pure(Spelt, Spelt{at, seen})
    case +c <> +rest True{}:
      on_disk.go(rest, repo, joined(at, c), seen, on_disk.plain(rest))
    case +c <> +rest False{}:
      do IO<Spelt>:
        +dir : String = Bool.pick(String, String.is_empty(at), repo, repo ++ "/" ++ at)
        ls : List<&2, String> <- listing.read(dir, cached(Map.get(List<&2, String>, Nil{}, seen, dir)))
        +ls2 : List<&2, String> = ls
        on_disk.go(rest, repo, joined(at, spelling(ls2, c)), Map.set(&2, List<&2, String>, seen, dir, ls2), on_disk.plain(rest))

def on_disk.one(+repo: String, +p: String, +seen: Map<&2, List<&2, String>>) -> IO(Spelt):
  +parts = String.split(p, '/')
  on_disk.go(parts, repo, SNil{}, seen, on_disk.plain(parts))

def on_disk.all.go(ps: List<&2, String>, +repo: String, +seen: Map<&2, List<&2, String>>) -> IO(List<&2, String>):
  match ps:
    case Nil{}:
      IO.pure(List<&2, String>, Nil{})
    case +p <> rest:
      do IO<List<&2, String>>:
        s : Spelt <- on_disk.one(repo, p, seen)
        +s2 : Spelt = s
        more : List<&2, String> <- on_disk.all.go(rest, repo, spelt.seen(s2))
        return spelt.path(s2) <> more

# Where each path the walk named is under `repo`, as the folder spells it,
# which is where it has to be opened: the walk's path is in normal form C,
# and the file may not be. A directory is listed at most once for all of
# them, and only where a component could be spelled another way.
def on_disk.all(+repo: String, ps: List<&2, String>) -> IO(List<&2, String>):
  on_disk.all.go(ps, repo, Map.new(&2, List<&2, String>))

def on_disk(+repo: String, +p: String) -> IO(String):
  do IO<String>:
    s : Spelt <- on_disk.one(repo, p, Map.new(&2, List<&2, String>))
    return spelt.path(s)

# Text
# ----

# Decision 0017's rule for a file nobody has recorded: text is valid UTF-8
# with no NUL byte, and everything else is bytes. The validator is Rust's
# `str::from_utf8`: no overlong form, no surrogate, nothing past U+10FFFF.
type Utf is Data:
  Utf{need: U32, lo: U32, hi: U32, ok: Bool}

def utf.lead(+b: U32) -> Utf:
  Bool.pick(Utf, U32.is_lt(b, 128), Utf{0, 128, 191, True{}},
  Bool.pick(Utf, Bool.and(U32.is_ge(b, 194), U32.is_le(b, 223)), Utf{1, 128, 191, True{}},
  Bool.pick(Utf, U32.is_eq(b, 224), Utf{2, 160, 191, True{}},
  Bool.pick(Utf, U32.is_eq(b, 237), Utf{2, 128, 159, True{}},
  Bool.pick(Utf, Bool.and(U32.is_ge(b, 225), U32.is_le(b, 239)), Utf{2, 128, 191, True{}},
  Bool.pick(Utf, U32.is_eq(b, 240), Utf{3, 144, 191, True{}},
  Bool.pick(Utf, Bool.and(U32.is_ge(b, 241), U32.is_le(b, 243)), Utf{3, 128, 191, True{}},
  Bool.pick(Utf, U32.is_eq(b, 244), Utf{3, 128, 143, True{}}, Utf{0, 0, 0, False{}}))))))))

def utf.step(st: Utf, +b: U32) -> Utf:
  match st:
    case Utf{+need, +lo, +hi, ok}:
      Bool.pick(Utf, ok,
        Bool.pick(Utf, U32.is_eq(need, 0), utf.lead(b), Utf{(need - 1 : U32), 128, 191, Bool.and(U32.is_ge(b, lo), U32.is_le(b, hi))}),
        Utf{0, 0, 0, False{}})

def utf.go(bs: List<&2, U32>, st: Utf) -> Utf:
  match bs:
    case Nil{}:
      st
    case +b <> rest:
      utf.go(rest, utf.step(st, b))

def utf.done(st: Utf) -> Bool:
  match st:
    case Utf{need, lo, hi, ok}:
      Bool.and(ok, U32.is_eq(need, 0))

# `String::from_utf8` would take it: what a file recorded as lines must stay.
def is_utf8(bs: List<&2, U32>) -> Bool:
  utf.done(utf.go(bs, Utf{0, 128, 191, True{}}))

def has_nul(bs: List<&2, U32>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case +b <> rest:
      Bool.or(U32.is_eq(b, 0), has_nul(rest))

# Decision 0017's text: UTF-8 with no NUL.
def is_text(+bs: List<&2, U32>) -> Bool:
  Bool.and(Bool.not(has_nul(bs)), is_utf8(bs))

# `String::from_utf8_lossy`: each character decoded, and each maximal run
# that cannot begin or finish one — the Unicode "maximal subpart" — read as
# U+FFFD. A byte that breaks a sequence is read again as a start.
type Dec is Data:
  Dec{need: U32, lo: U32, hi: U32, acc: U32, out: String}

def lossy.lead(+out: String, +b: U32) -> Dec:
  Bool.pick(Dec, U32.is_lt(b, 128), Dec{0, 128, 191, 0, SCon{Chr{b}, out}},
  Bool.pick(Dec, Bool.and(U32.is_ge(b, 194), U32.is_le(b, 223)), Dec{1, 128, 191, U32.and(b, 31), out},
  Bool.pick(Dec, U32.is_eq(b, 224), Dec{2, 160, 191, U32.and(b, 15), out},
  Bool.pick(Dec, U32.is_eq(b, 237), Dec{2, 128, 159, U32.and(b, 15), out},
  Bool.pick(Dec, Bool.and(U32.is_ge(b, 225), U32.is_le(b, 239)), Dec{2, 128, 191, U32.and(b, 15), out},
  Bool.pick(Dec, U32.is_eq(b, 240), Dec{3, 144, 191, U32.and(b, 7), out},
  Bool.pick(Dec, Bool.and(U32.is_ge(b, 241), U32.is_le(b, 243)), Dec{3, 128, 191, U32.and(b, 7), out},
  Bool.pick(Dec, U32.is_eq(b, 244), Dec{3, 128, 143, U32.and(b, 7), out}, Dec{0, 128, 191, 0, SCon{Chr{65533}, out}}))))))))

def lossy.cont(+need: U32, +acc: U32, +out: String, +b: U32) -> Dec:
  +got = ((acc * 64 : U32) + U32.and(b, 63) : U32)
  Bool.pick(Dec, U32.is_eq(need, 1), Dec{0, 128, 191, 0, SCon{Chr{got}, out}}, Dec{(need - 1 : U32), 128, 191, got, out})

def lossy.step(st: Dec, +b: U32) -> Dec:
  match st:
    case Dec{+need, +lo, +hi, +acc, +out}:
      Bool.pick(Dec, U32.is_eq(need, 0), lossy.lead(out, b),
        Bool.pick(Dec, Bool.and(U32.is_ge(b, lo), U32.is_le(b, hi)), lossy.cont(need, acc, out, b), lossy.lead(SCon{Chr{65533}, out}, b)))

def lossy.go(bs: List<&2, U32>, st: Dec) -> Dec:
  match bs:
    case Nil{}:
      st
    case +b <> rest:
      lossy.go(rest, lossy.step(st, b))

def lossy.done(st: Dec) -> String:
  match st:
    case Dec{+need, lo, hi, acc, +out}:
      String.reverse(Bool.pick(String, U32.is_eq(need, 0), out, SCon{Chr{65533}, out}))

def lossy(bs: List<&2, U32>) -> String:
  lossy.done(lossy.go(bs, Dec{0, 128, 191, 0, SNil{}}))
