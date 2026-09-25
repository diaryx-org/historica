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
# Not here: Unicode normal form C. A name the filesystem hands back
# decomposed is compared as it is spelled, as everywhere else in this port.

import Base
import ./text.bend as T
import ./store.bend as Store
import ./bookmark.bend as Bm

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

# Whether a string opens with a `/`, asked with `Char.is_eq` so a proof can
# follow the walk below over a character it does not know.
def slash_first(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Char.is_eq(c, '/')

def trim.go(s: String, slash: Bool) -> String:
  match s slash:
    case SNil{} _:
      SNil{}
    case SCon{c, +t} True{}:
      trim.go(t, slash_first(t))
    case SCon{c, t} False{}:
      String.reverse(SCon{c, t})

# The reversed string past its leading `/`s, turned back the right way.
def trim_slashes(+s: String) -> String:
  trim.go(s, slash_first(s))

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
    case SCon{c, t}:
      Bool.or(Char.is_eq(c, '/'), has_slash(t))

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
# empty line after a final newline. A `\r` ending the text with no newline
# after it ends no line, and stays.
def unreturned(+l: String) -> String:
  Bool.pick(String, String.ends_with(l, "\r"), String.take(l, Nat.sub(String.length(l), 1n)), l)

def lines.trimmed(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> Nil{}:
      Bool.pick(List<&2, String>, String.is_empty(l), Nil{}, [l])
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

def rules.stated(+file: String, st: Stated) -> IO(List<&2, Scope>):
  match st:
    case Stated.None{}:
      IO.pure(List<&2, Scope>, Nil{})
    case Stated.One{sc}:
      IO.pure(List<&2, Scope>, [sc])
    case Stated.Wrong{e}:
      die(List<&2, Scope>, 1, file ++ ": " ++ e)

# A rule file whose bytes are not UTF-8 is refused before it is read.
def rules.read(+file: String, r: Result<&2, &2, String, String>) -> IO(List<&2, Scope>):
  match r:
    case Fail{e}:
      die(List<&2, Scope>, 1, file ++ ": " ++ e)
    case Done{+text}:
      rules.stated(file, rule_in(text))

# In path order, so the file refused is the first the Rust loader reaches.
def rules.go(+root: String, paths: List<&2, String>) -> IO(List<&2, Scope>):
  match paths:
    case Nil{}:
      IO.pure(List<&2, Scope>, Nil{})
    case +p <> rest:
      do IO<List<&2, Scope>>:
        +file : String = root ++ "/" ++ p
        r : Result<&2, &2, String, String> <- Store.read_utf8(file)
        here : List<&2, Scope> <- rules.read(file, r)
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
# with `/` below every other character, and no name holds a NUL.
def walked_key.go(cs: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case Nil{}:
      Nil{}
    case Chr{+x} <> rest:
      Bool.pick(Char, U32.is_eq(x, 47), Chr{0}, Chr{x}) <> walked_key.go(rest)

def walked_le(+a: String, +b: String) -> Bool:
  String.is_le(String.from_list(walked_key.go(String.to_list(a))), String.from_list(walked_key.go(String.to_list(b))))

def refused.path(r: T.Split) -> String:
  match r:
    case T.Split{p, b}:
      p

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

def walk.go(fuel: Nat, +repo: String, +rules: List<&2, Scope>, pending: List<&2, String>, found: List<&2, Found>, refused: List<&2, T.Split>) -> IO(Walked):
  match fuel pending:
    case 0n _:
      IO.pure(Walked, Walked{found, refused})
    case 1n+q Nil{}:
      IO.pure(Walked, Walked{found, refused})
    case 1n+q +dir <> rest:
      do IO<Walked>:
        got : String <- listed(Bool.pick(String, String.is_empty(dir), repo, repo ++ "/" ++ dir))
        +text : String = got
        +l : Listing = listing.go(String.split(text, '\n'), dir, rules, Listing{Nil{}, found, None{}})
        walk.go(q, repo, rules, List.append(&2, String, listing.dirs(l), rest), listing.found(l), refusals.go(String.split(text, '\n'), dir, rules, False{}, refused))

# Every file the working copy tracks, in path order, and every path it
# refused, in the order the Rust walk refuses them.
def walk.all(+repo: String, +rules: List<&2, Scope>) -> IO(Walked):
  do IO<Walked>:
    w : Walked <- walk.go(U32.to_nat(1000000), repo, rules, [SNil{}], Nil{}, Nil{})
    +w2 : Walked = w
    return Walked{List.sort(~Found, ~(a => b => String.is_le(found.path(a), found.path(b))), walked.found(w2)),
      List.sort(~T.Split, ~(a => b => walked_le(refused.path(a), refused.path(b))), walked.refused(w2))}

# Every file the working copy tracks, in path order.
def walk(+repo: String, +rules: List<&2, Scope>) -> IO(List<&2, Found>):
  do IO<List<&2, Found>>:
    w : Walked <- walk.all(repo, rules)
    return walked.found(w)

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
