# Who a person says they are, read from their own configuration: the Rust
# tool's `record::identity`, and the `identity` command that writes it.
#
# Decision 0010: an author is a claim, so nothing is guessed. Who records is
# `$HISTORICA_AUTHOR` where it is set and not empty, and otherwise what the
# identity file says for the repository being recorded in — the file under
# `$XDG_CONFIG_HOME`, or under `$HOME/.config`, at `historica/identity`. The
# file is blocks of `key value` lines with a blank line between: a block
# with no `under` line states the default author, and one headed `under
# <directory>` the author for work beneath it, the deepest such directory
# winning. Where neither says, the refusal names the file and the line to
# put in it; `identity <author>` writes that line.

import Base
import ./text.bend as T
import ./store.bend as Store
import ./folder.bend as Folder
import ./notes.bend as Notes

# The file, under the configuration directory.
def FILE() -> String:
  "historica/identity"

# `Path::join`: a path that is absolute replaces what it is joined to, and
# the empty path joined to anything is that thing.
def joined(+base: String, +p: String) -> String:
  Bool.pick(String, String.starts_with(p, "/"), p,
  Bool.pick(String, Bool.or(String.is_empty(base), String.ends_with(base, "/")), base ++ p, base ++ "/" ++ p))

# `identity_path`: under `$XDG_CONFIG_HOME` where it is set and not empty,
# and under `.config` in the home directory otherwise — `$HOME`, or
# `$USERPROFILE` where that is all there is. Neither set, there is nowhere.
def home.of(home: Result<&1, &1, U32 & String, String>, profile: Result<&1, &1, U32 & String, String>) -> Maybe<&2, String>:
  match home profile:
    case Done{h} _:
      Some{h}
    case Fail{e} Done{p}:
      Some{p}
    case Fail{e} Fail{f}:
      None{}

def path.home(home: Maybe<&2, String>) -> Maybe<&2, String>:
  match home:
    case Some{+h}:
      Some{joined(joined(h, ".config"), FILE())}
    case None{}:
      None{}

def path.of(xdg: Result<&1, &1, U32 & String, String>, home: Maybe<&2, String>) -> Maybe<&2, String>:
  match xdg:
    case Done{+x}:
      Bool.pick(Maybe<&2, String>, String.is_empty(x), path.home(home), Some{joined(x, FILE())})
    case Fail{e}:
      path.home(home)

def path() -> IO(Maybe<&2, String>):
  do IO<Maybe<&2, String>>:
    xdg : Result<&1, &1, U32 & String, String> <- IO.get_env("XDG_CONFIG_HOME")
    home : Result<&1, &1, U32 & String, String> <- IO.get_env("HOME")
    profile : Result<&1, &1, U32 & String, String> <- IO.get_env("USERPROFILE")
    return path.of(xdg, home.of(home, profile))

# The file's grammar
# ------------------

# What the file says: a default author, and each directory's.
type Ids is Data:
  Ids{default: Maybe<&2, String>, under: List<&2, T.Split>}

# A line that is not what was wanted there, counted from one.
type Malformed is Data:
  Malformed{at: Nat, because: String}

# What one line is.
type Said is Data:
  Said.Blank{}
  Said.Unsplit{}
  Said.Unusable{}
  Said.Under{directory: String}
  Said.Author{author: String}
  Said.Other{}

# A value is not empty, carries no leading or trailing space, and holds no
# control character.
def unusable(+v: String) -> Bool:
  Bool.or(Folder.untrimmed(v), List.any(~&2, ~Char, ~Folder.is_control, String.to_list(v)))

# `trim_end_matches('/')`: `Folder.trim_slashes` walks the reversed path.
def unslashed(+v: String) -> String:
  Folder.trim_slashes(String.reverse(v))

def said.keyed(+k: String, +v: String) -> Said:
  Bool.pick(Said, unusable(v), Said.Unusable{},
  Bool.pick(Said, String.eq(k, "under"), Said.Under{unslashed(v)},
  Bool.pick(Said, String.eq(k, "author"), Said.Author{v}, Said.Other{})))

def said.cut(cut: Maybe<&2, T.Split>) -> Said:
  match cut:
    case None{}:
      Said.Unsplit{}
    case Some{T.Split{+k, +v}}:
      said.keyed(k, v)

def said(+line: String) -> Said:
  Bool.pick(Said, String.is_empty(line), Said.Blank{}, said.cut(T.split_once(line)))

def claimed(us: List<&2, T.Split>, +d: String) -> Bool:
  match us:
    case Nil{}:
      False{}
    case T.Split{+h, a} <> rest:
      Bool.or(String.eq(h, d), claimed(rest, d))

# A block ended: its author the default, or the author under its directory.
def close(who: Maybe<&2, String>, heading: Maybe<&2, String>, ids: Ids, +at: Nat) -> Result<&2, &2, Malformed, Ids>:
  match who heading ids:
    case None{} None{} kept:
      Done{kept}
    case None{} Some{h} _:
      Fail{Malformed{at, "a block naming a directory states no author"}}
    case Some{a} None{} Ids{None{}, us}:
      Done{Ids{Some{a}, us}}
    case Some{a} None{} Ids{Some{d}, us}:
      Fail{Malformed{at, "two blocks state a default author"}}
    case Some{a} Some{+h} Ids{d, +us}:
      Bool.pick(Result<&2, &2, Malformed, Ids>, claimed(us, h), Fail{Malformed{at, "two blocks claim one directory"}},
        Done{Ids{d, List.append(&2, T.Split, us, [T.Split{h, a}])}})

# Where the reading has got to: the blocks closed so far, and the one open
# — its heading, its author, and the line it started on, or none yet.
type Reading is Data:
  Reading{ids: Ids, heading: Maybe<&2, String>, author: Maybe<&2, String>, started: Nat}

def closed(r: Result<&2, &2, Malformed, Ids>) -> Result<&2, &2, Malformed, Reading>:
  match r:
    case Fail{m}:
      Fail{m}
    case Done{ids}:
      Done{Reading{ids, None{}, None{}, 0n}}

def begun(+started: Nat, +at: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_eq(started, 0n), at, started)

def line(r: Reading, +at: Nat, s: Said) -> Result<&2, &2, Malformed, Reading>:
  match r s:
    case Reading{ids, h, a, +started} Said.Blank{}:
      closed(close(a, h, ids, Nat.max(started, 1n)))
    case Reading{ids, h, a, started} Said.Unsplit{}:
      Fail{Malformed{at, "a line is a key, a space, and a value"}}
    case Reading{ids, h, a, started} Said.Unusable{}:
      Fail{Malformed{at, "a value is not empty, carries no leading or trailing space, and holds no control character"}}
    case Reading{ids, Some{h}, a, started} Said.Under{d}:
      Fail{Malformed{at, "a block names one directory"}}
    case Reading{ids, None{}, Some{a}, started} Said.Under{d}:
      Fail{Malformed{at, "`under` heads a block, so it comes first"}}
    case Reading{ids, None{}, None{}, started} Said.Under{d}:
      Done{Reading{ids, Some{d}, None{}, begun(started, at)}}
    case Reading{ids, h, Some{a}, started} Said.Author{b}:
      Fail{Malformed{at, "a block states one author"}}
    case Reading{ids, h, None{}, started} Said.Author{b}:
      Done{Reading{ids, h, Some{b}, begun(started, at)}}
    case Reading{ids, h, a, started} Said.Other{}:
      Fail{Malformed{at, "the keys are `author` and `under`"}}

def parse.end(r: Reading) -> Result<&2, &2, Malformed, Ids>:
  match r:
    case Reading{ids, h, a, +started}:
      close(a, h, ids, Nat.max(started, 1n))

def parse.go(ls: List<&2, String>, +at: Nat, st: Result<&2, &2, Malformed, Reading>) -> Result<&2, &2, Malformed, Ids>:
  match ls st:
    case _ Fail{m}:
      Fail{m}
    case Nil{} Done{r}:
      parse.end(r)
    case +l <> rest Done{r}:
      parse.go(rest, 1n+at, line(r, at, said(l)))

# `Identities::parse`.
def parse(+text: String) -> Result<&2, &2, Malformed, Ids>:
  parse.go(Folder.lines.trimmed(String.split(text, '\n')), 1n, Done{Reading{Ids{None{}, Nil{}}, None{}, None{}, 0n}})

# Whose work a directory is
# ------------------------

# A path as its components, as `Path::components` reads it: the root a
# component of its own, a separator repeated or at the end nothing, and a
# `.` nothing except where a relative path begins with it.
def parts(ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      +more = parts(rest)
      Bool.pick(List<&2, String>, Bool.or(String.is_empty(p), String.eq(p, ".")), more, p <> more)

def components.of(absolute: Bool, ps: List<&2, String>) -> List<&2, String>:
  match absolute ps:
    case True{} _:
      "/" <> parts(ps)
    case False{} Nil{}:
      Nil{}
    case False{} +p <> rest:
      +more = parts(rest)
      Bool.pick(List<&2, String>, Bool.or(String.is_empty(p), String.eq(p, ".")), Bool.pick(List<&2, String>, String.is_empty(p), more, "." <> more), p <> more)

def components(+path: String) -> List<&2, String>:
  components.of(String.starts_with(path, "/"), String.split(path, '/'))

def prefix(ps: List<&2, String>, qs: List<&2, String>) -> Bool:
  match ps qs:
    case Nil{} _:
      True{}
    case p <> more Nil{}:
      False{}
    case +p <> more +q <> rest:
      Bool.and(String.eq(p, q), prefix(more, rest))

# `~/work` as the person meant it; with no home, nothing.
def expand(+d: String, +home: Maybe<&2, String>) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.starts_with(d, "~/"), Maybe.map(&2, String, String, h => joined(h, String.drop(d, 2n)), home),
    Bool.pick(Maybe<&2, String>, String.eq(d, "~"), home, Some{d}))

# The deepest directory a block names that the work sits in or beneath,
# counted in components, and whose it is.
type Best is Data:
  Best{depth: Nat, author: String}

def best.author(b: Best) -> String:
  match b:
    case Best{n, a}:
      a

def deeper(e: Maybe<&2, List<&2, String>>, +dir: List<&2, String>, +a: String, best: Maybe<&2, Best>) -> Maybe<&2, Best>:
  match e best:
    case None{} _:
      best
    case Some{+cs} None{}:
      Bool.pick(Maybe<&2, Best>, prefix(cs, dir), Some{Best{List.length(&2, String, cs), a}}, None{})
    case Some{+cs} Some{Best{+n, +b}}:
      Bool.pick(Maybe<&2, Best>, Bool.and(prefix(cs, dir), Nat.is_gt(List.length(&2, String, cs), n)),
        Some{Best{List.length(&2, String, cs), a}}, Some{Best{n, b}})

# Each block's directory against the work's, the deepest holding it
# winning and the first of two as deep keeping it.
def deepest(us: List<&2, T.Split>, +dir: List<&2, String>, +home: Maybe<&2, String>, best: Maybe<&2, Best>) -> Maybe<&2, String>:
  match us:
    case Nil{}:
      Maybe.map(&2, Best, String, b => best.author(b), best)
    case T.Split{+d, +a} <> rest:
      deepest(rest, dir, home, deeper(Maybe.map(&2, String, List<&2, String>, e => components(e), expand(d, home)), dir, a, best))

# `Identities::author_for`: who records work in `directory`.
def author_under(ids: Ids, +directory: String, +home: Maybe<&2, String>) -> Maybe<&2, String>:
  match ids:
    case Ids{d, us}:
      Maybe.or(&2, String, deepest(us, components(directory), home, None{}), d)

# Who records
# -----------

# An author a revision document can hold; the refusal says where it came
# from.
def checked.said(+who: String, file: Maybe<&2, String>) -> String:
  match file:
    case Some{f}:
      "`" ++ who ++ "` in " ++ f ++ " cannot be an author: a header value is not empty, carries no leading or trailing space, and holds no control character"
    case None{}:
      "`" ++ who ++ "` in $HISTORICA_AUTHOR cannot be an author: a header value is not empty, carries no leading or trailing space, and holds no control character"

def checked(+who: String, +file: Maybe<&2, String>) -> Result<&2, &2, String, String>:
  Bool.pick(Result<&2, &2, String, String>, unusable(who), Fail{checked.said(who, file)}, Done{who})

def nowhere() -> String:
  "this platform has no configuration directory; set $HISTORICA_AUTHOR instead"

def no_identity(+file: String) -> String:
  "nobody has said who you are, and nothing is guessed: write `author Your Name <you@example.com>` in " ++ file ++ ", or run `historica identity \"Your Name <you@example.com>\"`"

def malformed(+file: String, m: Malformed) -> String:
  match m:
    case Malformed{at, because}:
      file ++ ": line " ++ Nat.show(at) ++ ": " ++ because

def named(+file: String, a: Maybe<&2, String>) -> Result<&2, &2, String, String>:
  match a:
    case None{}:
      Fail{file ++ " states no author for this directory and no default one"}
    case Some{+x}:
      checked(x, Some{file})

# What the file says of work in `directory`, `~` being `home`.
def from_ids(+file: String, r: Result<&2, &2, Malformed, Ids>, +directory: String, +home: Maybe<&2, String>) -> Result<&2, &2, String, String>:
  match r:
    case Fail{m}:
      Fail{malformed(file, m)}
    case Done{ids}:
      named(file, author_under(ids, directory, home))

def from_text(+file: String, +text: String, +directory: String, +home: Maybe<&2, String>) -> Result<&2, &2, String, String>:
  from_ids(file, parse(text), directory, home)

# An identity file whose bytes are not UTF-8 is refused, naming it.
def from_read(+file: String, r: Result<&2, &2, String, String>, +directory: String, +home: Maybe<&2, String>) -> Result<&2, &2, String, String>:
  match r:
    case Fail{e}:
      Fail{file ++ ": " ++ e}
    case Done{text}:
      from_text(file, text, directory, home)

def from_file(+file: String, +directory: String, +home: Maybe<&2, String>, r: Result<&1, &1, U32 & String, File>) -> IO(Result<&2, &2, String, String>):
  match r:
    case Fail{Tuple{+code, msg}}:
      IO.pure(Result<&2, &2, String, String>, Bool.pick(Result<&2, &2, String, String>, U32.is_eq(code, 2), Fail{no_identity(file)}, Fail{file ++ ": " ++ Store.os_error(code, msg)}))
    case Done{f}:
      do IO<Result<&2, &2, String, String>>:
        File.close(f)
        r : Result<&2, &2, String, String> <- Store.read_utf8(file)
        return from_read(file, r, directory, home)

def author.at(p: Maybe<&2, String>, +directory: String, +home: Maybe<&2, String>) -> IO(Result<&2, &2, String, String>):
  match p:
    case None{}:
      IO.pure(Result<&2, &2, String, String>, Fail{nowhere()})
    case Some{+file}:
      do IO<Result<&2, &2, String, String>>:
        r : Result<&1, &1, U32 & String, File> <- File.open(file, "r")
        from_file(file, directory, home, r)

def author.file(+directory: String) -> IO(Result<&2, &2, String, String>):
  do IO<Result<&2, &2, String, String>>:
    p : Maybe<&2, String> <- path()
    home : Result<&1, &1, U32 & String, String> <- IO.get_env("HOME")
    profile : Result<&1, &1, U32 & String, String> <- IO.get_env("USERPROFILE")
    author.at(p, directory, home.of(home, profile))

# What `$HISTORICA_AUTHOR` decides: set and not empty, the author it
# names, or the refusal of one no revision can hold; otherwise nothing, and
# the file decides.
def from_env(env: Result<&1, &1, U32 & String, String>) -> Maybe<&2, Result<&2, &2, String, String>>:
  match env:
    case Done{+a}:
      Bool.pick(Maybe<&2, Result<&2, &2, String, String>>, String.is_empty(a), None{}, Some{checked(a, None{})})
    case Fail{e}:
      None{}

def author.decided(m: Maybe<&2, Result<&2, &2, String, String>>, +directory: String) -> IO(Result<&2, &2, String, String>):
  match m:
    case Some{r}:
      IO.pure(Result<&2, &2, String, String>, r)
    case None{}:
      author.file(directory)

def author.of(env: Result<&1, &1, U32 & String, String>, +directory: String) -> IO(Result<&2, &2, String, String>):
  author.decided(from_env(env), directory)

# `author_for`: who is recording work in `directory` — the environment
# first, for scripts, tests and machines where a file is inconvenient; then
# the identity file; then a refusal that names the file and the line.
def author(+directory: String) -> IO(Result<&2, &2, String, String>):
  do IO<Result<&2, &2, String, String>>:
    env : Result<&1, &1, U32 & String, String> <- IO.get_env("HISTORICA_AUTHOR")
    author.of(env, directory)

# identity <author>
# -----------------

def die(-A: Type, +code: U32, msg: String) -> IO(A):
  IO.die(A, code, "historica: " ++ msg ++ Bool.pick(String, U32.is_eq(code, 2), "\n\n" ++ Notes.USAGE(), SNil{}))

# The directory a path is in: `Path::parent`, for a path that names a file.
# The walk is over the reversed path, each character asked with
# `Char.is_eq` so that a proof can follow it over one it does not know.
def parent.go(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, +t}:
      Bool.pick(String, Char.is_eq(c, '/'), t, parent.go(t))

def parent(+file: String) -> String:
  +up = String.reverse(parent.go(String.reverse(file)))
  Bool.pick(String, Bool.and(String.is_empty(up), String.starts_with(file, "/")), "/", up)

# The line a refusal to record asks for, which is the whole file for a
# person who has one author to say.
def wanted(+who: String) -> String:
  "author " ++ who ++ "\n"

def written(+file: String, r: Result<&1, &1, U32 & String, String>) -> IO(Unit):
  match r:
    case Fail{Tuple{code, msg}}:
      die(Unit, 1, msg)
    case Done{x}:
      IO.print("wrote " ++ file)

def fresh(+file: String, +who: String, there: Result<&1, &1, U32 & String, String>) -> IO(Unit):
  match there:
    case Done{x}:
      die(Unit, 1, file ++ " already exists; edit it rather than having it rewritten")
    case Fail{e}:
      do IO<Unit>:
        w : Result<&1, &1, U32 & String, String> <- Store.written(file ++ "\n" ++ wanted(who))
        written(file, w)

def made(+file: String, +who: String, m: Result<&1, &1, U32 & String, String>) -> IO(Unit):
  match m:
    case Fail{Tuple{code, msg}}:
      die(Unit, 1, msg)
    case Done{x}:
      do IO<Unit>:
        there : Result<&1, &1, U32 & String, String> <- Store.really(file)
        fresh(file, who, there)

def set.at(+who: String, p: Maybe<&2, String>) -> IO(Unit):
  match p:
    case None{}:
      die(Unit, 1, "this platform has no configuration directory to write to")
    case Some{+file}:
      do IO<Unit>:
        m : Result<&1, &1, U32 & String, String> <- Store.made(parent(file))
        made(file, who, m)

# `identity <author>`: the file written with the one line, where there is
# no file yet — one already there is a person's own, and is edited rather
# than rewritten. Nothing is asked of a store; there need not be one.
def set(args: List<&2, String>) -> IO(Unit):
  match args:
    case Nil{}:
      die(Unit, 2, "`identity` wants a name, as `Name <you@example.com>`")
    case a <> extra <> more:
      die(Unit, 2, "`identity` takes one name, and `" ++ extra ++ "` is a second")
    case +a <> Nil{}:
      do IO<Unit>:
        p : Maybe<&2, String> <- path()
        set.at(a, p)
