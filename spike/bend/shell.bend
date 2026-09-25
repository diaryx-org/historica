# What the command line asks for before any command runs, and what it asks
# for when the command word is none this tool has: the Rust tool's `run`,
# `main` and decision 0072's `dispatch`.
#
# `help`, `-h`, `--help` and no arguments at all print the usage text of the
# default build — which has `fetch` and the dispatch paragraph — to stdout;
# `-V` and `--version` print the version; a usage error prints its message,
# a blank line and the same text to stderr and exits 2 (`Main.die` says it).
# `-C <dir>` is read by `store.bend`, which is where it matters.
#
# A word that is no command here may still name a program beside this one:
# `historica git import` runs `historica-git import`, found on `PATH`, in
# the directory `-C` names, with this process's standard streams, and ends
# with its code. A word spelled with anything but ASCII letters, digits and
# interior hyphens is never looked for — a word with a `/` in it would run a
# file by its position — and neither that nor a program `PATH` does not have
# is anything but "there is no such command".

import Base
import ./commands.bend as Main
import ./store.bend as Store
import ./notes.bend as Notes
import ./bookmark.bend as Bm

# The workspace's version, which `historica --version` says. `check.py`
# holds it to the workspace's `Cargo.toml`, so a release the port has not
# caught up with fails there.
def VERSION() -> String:
  "1.0.0-rc.4"

def usage() -> IO(Unit):
  IO.write(Notes.USAGE() ++ "\n")

def version() -> IO(Unit):
  IO.print("historica " ++ VERSION())

# Decision 0072
# -------------

# The alphabet a word looked for on `PATH` is spelled in.
def spelling(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(Bool.or(Bool.and(U32.is_ge(x, 97), U32.is_le(x, 122)), Bool.and(U32.is_ge(x, 65), U32.is_le(x, 90))),
        Bool.or(Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)), U32.is_eq(x, 45)))

def spelled(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(spelling(c), spelled(t))

# Whether a word may be looked for on `PATH` at all.
def dispatchable(+w: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(w)),
    Bool.and(Bool.not(String.starts_with(w, "-")),
      Bool.and(Bool.not(String.ends_with(w, "-")), spelled(w))))

# What a word the tool has no command for comes to: a program to run, or
# the refusal a typo gets.
type Plan is Data:
  Plan.Run{dir: String, program: String, args: List<&2, String>}
  Plan.Missing{message: String}

def missing(+word: String) -> String:
  "there is no `" ++ word ++ "` command"

def plan(+base: String, +word: String, args: List<&2, String>) -> Plan:
  Bool.pick(Plan, dispatchable(word), Plan.Run{base, "historica-" ++ word, args}, Plan.Missing{missing(word)})

# How a run ends this process: with the program's own code, so that a
# script wrapping `historica git` sees what wrapping `historica-git` would
# have shown it; a program `PATH` has none of is the plain typo, and any
# other failure to start it, or a signal ending it, is said.
type Ending is Data:
  Ending.Code{code: Nat}
  Ending.Refused{code: U32, message: String}

def ending(+word: String, r: Result<&1, &1, U32 & String, String>) -> Ending:
  match r:
    case Fail{Tuple{+code, msg}}:
      Bool.pick(Ending, U32.is_eq(code, 2), Ending.Refused{2, missing(word)}, Ending.Refused{1, "historica-" ++ word ++ ": " ++ msg})
    case Done{+answer}:
      Bool.pick(Ending, String.eq(answer, "signal"), Ending.Refused{1, "historica-" ++ word ++ " was killed"},
        Ending.Code{Maybe.default(&2, Nat, Nat.read(answer), 1n)})

def ended(e: Ending) -> IO(Unit):
  match e:
    case Ending.Code{+n}:
      Store.ended(n)
    case Ending.Refused{code, msg}:
      Main.die(Unit, code, msg)

def elsewhere.planned(+word: String, p: Plan) -> IO(Unit):
  match p:
    case Plan.Missing{msg}:
      Main.die(Unit, 2, msg)
    case Plan.Run{dir, program, args}:
      do IO<Unit>:
        r : Result<&1, &1, U32 & String, String> <- Store.ran(dir, program, args)
        ended(ending(word, r))

def elsewhere(+base: String, +word: String, args: List<&2, String>) -> IO(Unit):
  elsewhere.planned(word, plan(base, word, args))

# A command line the command refuses once it has opened the store: the
# Rust tool's `show`, `files`, `cat` and `names` open it before they count
# their words, so a store that will not open says so first.
def refused.opened(+msg: String) -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    rs : List<&2, Store.Doc> <- Store.revisions(r)
    bs : List<&2, Bm.Bookmark> <- Main.bookmarks(r)
    Main.die(Unit, 2, msg)
