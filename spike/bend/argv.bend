# The command line, as the Rust tool's `run` reads it before a command
# word: `-C <dir>` as often as it is given, the last counting; `help`, `-h`
# or `--help`, and `-V` or `--version`, each ending the reading; any other
# word starting `-` refused; and the first word that is none of these the
# command, every word after it an argument the command reads itself.
#
# Read twice in a run and alike both times: by `main.bend`, to choose what
# to do, and by `store.bend`, to know where the store is looked for from —
# `-C`'s directory, which every command runs in as if started there. The
# command line is the one thing both can ask for, so neither has to be
# handed the other's answer.

import Base

# What a command line asks for.
type Asked is Data:
  Asked.Usage{}
  Asked.Version{}
  Asked.Wrong{message: String}
  Asked.Command{base: Maybe<&2, String>, word: String, rest: List<&2, String>}

# What the word in front is, before the command — or, after `-C`, that it
# is the directory.
type Lead is Data:
  Lead.Base{}
  Lead.Usage{}
  Lead.Version{}
  Lead.Option{}
  Lead.Word{}
  Lead.Dir{}

def lead.of(+w: String) -> Lead:
  Bool.pick(Lead, String.eq(w, "-C"), Lead.Base{},
  Bool.pick(Lead, Bool.or(String.eq(w, "help"), Bool.or(String.eq(w, "-h"), String.eq(w, "--help"))), Lead.Usage{},
  Bool.pick(Lead, Bool.or(String.eq(w, "-V"), String.eq(w, "--version")), Lead.Version{},
  Bool.pick(Lead, String.starts_with(w, "-"), Lead.Option{}, Lead.Word{}))))

def lead(args: List<&2, String>) -> Lead:
  match args:
    case Nil{}:
      Lead.Usage{}
    case +w <> rest:
      lead.of(w)

# Read one word at a time: `-C` leaves the next word to be read as its
# directory (`Lead.Dir`), which is where a missing one is refused.
def read.go(args: List<&2, String>, base: Maybe<&2, String>, k: Lead) -> Asked:
  match args k:
    case Nil{} Lead.Dir{}:
      Asked.Wrong{"`-C` wants a directory"}
    case Nil{} _:
      Asked.Usage{}
    case d <> +rest Lead.Dir{}:
      read.go(rest, Some{d}, lead(rest))
    case w <> rest Lead.Base{}:
      read.go(rest, base, Lead.Dir{})
    case w <> rest Lead.Usage{}:
      Asked.Usage{}
    case w <> rest Lead.Version{}:
      Asked.Version{}
    case w <> rest Lead.Option{}:
      Asked.Wrong{"`" ++ w ++ "` is not an option here"}
    case w <> rest Lead.Word{}:
      Asked.Command{base, w, rest}

def read(+args: List<&2, String>) -> Asked:
  read.go(args, None{}, lead(args))

# A command line as the laws spell it: `-C` before each of `ds`, then the
# command word and its arguments; and the directory the last of them names,
# or `b` where there are none (`LAWS.argv_reads_its_words`).
def spelled(ds: List<&2, String>, +w: String, +rest: List<&2, String>) -> List<&2, String>:
  match ds:
    case Nil{}:
      w <> rest
    case d <> more:
      "-C" <> d <> spelled(more, w, rest)

def last(ds: List<&2, String>, b: Maybe<&2, String>) -> Maybe<&2, String>:
  match ds:
    case Nil{}:
      b
    case d <> more:
      last(more, Some{d})

# The directory a command runs in, as `-C` gave it, if it did.
def base.of(a: Asked) -> Maybe<&2, String>:
  match a:
    case Asked.Command{b, w, r}:
      b
    case _:
      None{}

def base(+args: List<&2, String>) -> Maybe<&2, String>:
  base.of(read(args))

# `IO.args` hands back a list of its own kind; this is the one the rest of
# the port reads.
def reusable(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> reusable(t)

def args() -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    xs : List<String> <- IO.args()
    return reusable(xs)
