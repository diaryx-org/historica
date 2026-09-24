# Bookmarks: `names/<name>.txt`, the only files in a store that change.
#
# A bookmark's name is its path below `names/` without `.txt`, so
# `names/feature/x.txt` is the bookmark `feature/x`, and a name is spelled
# the way a tracked path is — which is `Rev.is_path`, and no control
# character. (Unicode normal form C is not checked here, as it is not for a
# path.) A file whose path is not such a name is no bookmark, and is passed
# over, as the Rust tool's loader passes it over and its `check` notes it.
#
# The file is one line — `change`, `revision` or `file` and what it names —
# and at most one more, which is `private`: the name stays out of an export.

import Base
import ./text.bend as T
import ./ident.bend as Id
import ./revision.bend as Rev

type Target is Data:
  Target.Change{id: String}
  Target.Revision{id: String}
  Target.File{id: String}

type Bookmark is Data:
  Bookmark{name: String, target: Target, private: Bool}

# What one file states, before it has a name.
type Stated is Data:
  Stated{target: Target, private: Bool}

def name_of(b: Bookmark) -> String:
  match b:
    case Bookmark{name, target, private}:
      name

def target_of(b: Bookmark) -> Target:
  match b:
    case Bookmark{name, target, private}:
      target

# What kind of thing a target names, as a person would say it.
def kind(t: Target) -> String:
  match t:
    case Target.Change{id}:
      "change"
    case Target.Revision{id}:
      "revision"
    case Target.File{id}:
      "file"

# The target line, as the file spells it.
def show_target(t: Target) -> String:
  match t:
    case Target.Change{id}:
      "change " ++ id
    case Target.Revision{id}:
      "revision " ++ id
    case Target.File{id}:
      "file " ++ id

# One bookmark in a line, for a person.
def show(b: Bookmark) -> String:
  match b:
    case Bookmark{name, target, private}:
      show_target(target) ++ Bool.pick(String, private, " (private)", SNil{})

# Names
# -----

def name_ok(+n: String) -> Bool:
  Bool.and(Rev.is_path(n), Bool.not(List.any(~&2, ~Char, ~Rev.is_control, String.to_list(n))))

def name.of(+n: String, txt: Bool) -> Maybe<&2, String>:
  match txt:
    case False{}:
      None{}
    case True{}:
      +bare = String.take(n, Nat.sub(String.length(n), 4n))
      Bool.pick(Maybe<&2, String>, name_ok(bare), Some{bare}, None{})

# The bookmark a file under `names/` is, given its path below the root.
def name(+path: String) -> Maybe<&2, String>:
  +below = String.drop(path, 6n)
  name.of(below, String.ends_with(below, ".txt"))

# The file
# --------

def target_error() -> String:
  "a bookmark is one line: `change` and a change ID, `revision` and a digest, or `file` and a file identifier"

def axis_error() -> String:
  "a bookmark is one line, and at most one more, which is `private`; a file stating anything else below its target may have been written by a newer Historica than this one"

def target.kind(+key: String, +value: String) -> Result<&2, &2, String, Target>:
  match key:
    case "change":
      Bool.pick(Result<&2, &2, String, Target>, Id.is_assigned(value), Done{Target.Change{value}}, Fail{target_error()})
    case "revision":
      Bool.pick(Result<&2, &2, String, Target>, Id.is_digest(value), Done{Target.Revision{value}}, Fail{target_error()})
    case "file":
      Bool.pick(Result<&2, &2, String, Target>, Id.is_assigned(value), Done{Target.File{value}}, Fail{target_error()})
    case _:
      Fail{target_error()}

def target(cut: Maybe<&2, T.Split>) -> Result<&2, &2, String, Target>:
  match cut:
    case None{}:
      Fail{target_error()}
    case Some{T.Split{key, value}}:
      target.kind(key, value)

def axis(rest: List<&2, String>) -> Result<&2, &2, String, Bool>:
  match rest:
    case Nil{}:
      Done{False{}}
    case "private" <> Nil{}:
      Done{True{}}
    case _:
      Fail{axis_error()}

# One final newline ends the last line rather than starting another.
def lines.of(ls: List<&2, String>, n: Nat) -> List<&2, String>:
  List.take(&2, String, ls, Nat.sub(n, 1n))

def lines.trim(+ls: List<&2, String>, last_empty: Bool) -> List<&2, String>:
  +n = List.length(&2, String, ls)
  Bool.pick(List<&2, String>, Bool.and(last_empty, Nat.is_ge(n, 2n)), lines.of(ls, n), ls)

def last_empty(ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case l <> Nil{}:
      String.is_empty(l)
    case l <> rest:
      last_empty(rest)

def parse.axis(t: Target, a: Result<&2, &2, String, Bool>) -> Result<&2, &2, String, Stated>:
  match a:
    case Fail{e}:
      Fail{e}
    case Done{p}:
      Done{Stated{t, p}}

def parse.target(r: Result<&2, &2, String, Target>, rest: List<&2, String>) -> Result<&2, &2, String, Stated>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      parse.axis(t, axis(rest))

def parse.lines(ls: List<&2, String>) -> Result<&2, &2, String, Stated>:
  match ls:
    case Nil{}:
      Fail{target_error()}
    case first <> rest:
      parse.target(target(T.split_once(first)), rest)

# A bookmark file, from its text: the target line is read before the rest,
# so a file wrong in both says what is wrong with the first.
def parse(+text: String) -> Result<&2, &2, String, Stated>:
  +ls = String.split(text, '\n')
  parse.lines(lines.trim(ls, last_empty(ls)))

# The file the Rust tool writes for a bookmark: the target line, and
# `private` below it where the name stays out of an export. A target is
# well formed where its identifier is spelled as its kind is: what `parse`
# reads back (`LAWS.bookmark_reads_back`).
def private_line(p: Bool) -> String:
  match p:
    case True{}:
      "private\n"
    case False{}:
      SNil{}

def write(st: Stated) -> String:
  match st:
    case Stated{t, p}:
      show_target(t) ++ SCon{'\n', private_line(p)}

def target_ok(t: Target) -> Bool:
  match t:
    case Target.Change{+id}:
      Id.is_assigned(id)
    case Target.Revision{id}:
      Id.is_digest(id)
    case Target.File{+id}:
      Id.is_assigned(id)

# Lookup
# ------

def find(bs: List<&2, Bookmark>, +name: String) -> Maybe<&2, Target>:
  match bs:
    case Nil{}:
      None{}
    case Bookmark{+n, target, private} <> rest:
      Bool.pick(Maybe<&2, Target>, String.eq(n, name), Some{target}, find(rest, name))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Maybe.show(~&2, ~String, ~(s => s), name("names/feature/x.txt")))
    IO.print(Maybe.show(~&2, ~String, ~(s => s), name("names/notes")))
    IO.print(Maybe.show(~&2, ~String, ~(s => s), name("names/ lead.txt")))
