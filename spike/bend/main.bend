# historica, in Bend: the readable core of the format, over the store it finds.
#
# The reading commands `historica` has, in the shape it has them: the store is
# the `history` directory here or above, and a target is `head`, a change ID
# or a revision digest, either abbreviated to any unambiguous prefix.
#
#   bend main.bend -- log [<target>|<from>..<to>] [--limit <n>] [--author <text>]
#                         [--grep <text>] [--since <when>] [--until <when>]
#                         [--path <path>] [--fields]
#                                            the history, newest first
#   bend main.bend -- show <target> [<path>] one document as stored
#   bend main.bend -- files <target>         the file set at a revision
#   bend main.bend -- cat <target> <path>    one file's content at a revision
#   bend main.bend -- check                  every document, named by digest
#   bend main.bend -- names                  the bookmarks, and what they point at
#   bend main.bend -- replay <ops docs..>    the file a chain of documents makes
#   bend main.bend -- diff [<target>] [<path>] [--onto <target>] [--color <when>]
#                                            what a revision did, or the folder
#                                            against the head, rendered
#   bend main.bend -- blame [<target>] <path> [--lines <first>..<last>]
#                                            who wrote each line
#   bend main.bend -- opdiff <parent> <child> the operation document between two files
#   bend main.bend -- status [--onto <target>] [--merge <target>]..
#                                            where the folder is, and what it
#                                            differs by
#   bend main.bend -- update [<target>] [--dry-run]
#                                            the folder made to hold a head
#   bend main.bend -- merge [<target>..]     what the heads say together,
#                                            written into the folder
#   bend main.bend -- forget <target> <path> [--lines <first>..<last>]
#                                            destroy some of what history
#                                            holds of a file, keeping its shape
#
# Or compile it: `bend main.bend -o main.c`, then link the archive `ffi/`
# builds — `check.py` does both. What `bend main.bend` runs and what the
# binary runs are the same program over two adapters (`store.bend`).
#
# A target may also be a bookmark (`names/`), which wins over any other
# spelling, `head` included; a path may be `file:` and a file identifier or
# a file bookmark, or `path:` and a path. A merge's resolution — the file
# stated whole, by `keep` and `insert` — is read where an `edit` names one.

import Base
import ./commands.bend as C
import ./update.bend as U
import ./merging.bend as M
import ./forget.bend as F

def usage() -> IO(Unit):
  C.die(Unit, 2, "usage: init [<dir>] | log [<target>|<from>..<to>] [--limit <n>] [--author <text>] [--grep <text>] [--since <when>] [--until <when>] [--path <path>] [--fields] | show <target> [<path>] | files <target> | cat <target> <path> | check | names | diff [<target>] [<path>] [--onto <target>] [--color <when>] | blame [<target>] <path> [--lines <first>..<last>] | status [--onto <target>] [--merge <target>] | name <bookmark> <target> [<path>] [--revision|--change] [--private|--shared] [--fields] | name --delete <bookmark> | record --dry-run [<path>..] [--onto <target>] [--merge <target>] [--move <old>=<new>] [--at <file>=<path>] [--accept <path>] [--bytes <path>] [--lines <path>] | update [<target>] [--dry-run] | merge [<target>..] | forget <target> <path> [--lines <first>..<last>] [--dry-run] [--fields] | replay <ops docs..> | opdiff <parent> <child>")

def dispatch(args: List<&2, String>) -> IO(Unit):
  match args:
    case "log" <> args:
      C.log(args)
    case "show" <> t <> Nil{}:
      C.show(t, None{})
    case "show" <> t <> p <> Nil{}:
      C.show(t, Some{p})
    case "files" <> t <> Nil{}:
      C.files(t)
    case "cat" <> t <> p <> Nil{}:
      C.cat(t, p)
    case "check" <> Nil{}:
      C.check()
    case "names" <> Nil{}:
      C.names()
    case "names" <> extra <> rest:
      C.die(Unit, 2, "`names` takes no arguments, and `" ++ extra ++ "` is one")
    case "replay" <> paths:
      C.replay(paths)
    case "diff" <> args:
      C.diff(args)
    case "blame" <> args:
      C.blame(args)
    case "status" <> args:
      C.status(args)
    case "record" <> args:
      C.record(args)
    case "name" <> args:
      C.name(args)
    case "abandon" <> args:
      C.abandon(args)
    case "amend" <> args:
      C.amend(args)
    case "carry" <> args:
      C.carry(args)
    case "init" <> args:
      C.init(args)
    case "update" <> args:
      U.update(args)
    case "merge" <> args:
      M.merge(args)
    case "forget" <> args:
      F.forget(args)
    case "opdiff" <> parent <> child <> Nil{}:
      C.opdiff(parent, child)
    case _:
      usage()

def reusable(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> reusable(t)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    dispatch(reusable(args))
