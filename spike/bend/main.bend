# historica, in Bend: the readable core of the format, over the store it finds.
#
# The commands `historica` has, in the shape it has them: the store is the
# `history` directory here or above — here being `-C`'s directory where the
# command line names one — and a target is `head`, a change ID or a revision
# digest, either abbreviated to any unambiguous prefix. `help` prints the
# usage the Rust tool prints, and a word that is no command here is looked
# for on `PATH` as `historica-<word>` (decision 0072; `shell.bend`).
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
#   bend main.bend -- arrange [-n|--dry-run] [--refile]
#                                            the store's files renamed to
#                                            the names decision 0006 gives
#   bend main.bend -- prune [--dry-run] [--fields]
#                                            superseded work nothing stands
#                                            on removed, and what only it named
#   bend main.bend -- receive <dir> [--dry-run] [--join-unrelated] [--fields]
#                                            another store's history unioned
#                                            into this one
#   bend main.bend -- offer <dir>             the manifest a published copy
#                                            cannot give, on standard output
#   bend main.bend -- export <dir> [<target>] [--files-only] [-n|--dry-run]
#                                            the copy a person takes away:
#                                            the folder and its ancestry
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
import ./argv.bend as Argv
import ./shell.bend as Shell
import ./identity.bend as Identity
import ./skip.bend as Skip
import ./check.bend as Check
import ./arrange.bend as Arrange
import ./prune.bend as Prune
import ./receive.bend as Receive
import ./offer.bend as Offer
import ./export.bend as Export
import ./update.bend as U
import ./merging.bend as M
import ./forget.bend as F

def dispatch(+base: String, all: List<&2, String>) -> IO(Unit):
  match all:
    case "log" <> args:
      C.log(args)
    case "show" <> t <> Nil{}:
      C.show(t, None{})
    case "show" <> t <> p <> Nil{}:
      C.show(t, Some{p})
    case "show" <> Nil{}:
      Shell.refused.opened("`show` wants a target")
    case "show" <> t <> p <> extra <> more:
      Shell.refused.opened("`show` takes a target and one path, and `" ++ extra ++ "` is a third argument")
    case "files" <> t <> Nil{}:
      C.files(t)
    case "files" <> Nil{}:
      Shell.refused.opened("`files` wants a target")
    case "files" <> t <> extra <> more:
      Shell.refused.opened("`files` takes one target, and `" ++ extra ++ "` is a second")
    case "cat" <> t <> p <> Nil{}:
      C.cat(t, p)
    case "cat" <> Nil{}:
      Shell.refused.opened("`cat` wants a target")
    case "cat" <> t <> Nil{}:
      Shell.refused.opened("`cat` wants a path")
    case "cat" <> t <> p <> extra <> more:
      Shell.refused.opened("`cat` takes a target and a path, and `" ++ extra ++ "` is a third argument")
    case "check" <> args:
      Check.check(args)
    case "names" <> Nil{}:
      C.names()
    case "names" <> extra <> rest:
      Shell.refused.opened("`names` takes no arguments, and `" ++ extra ++ "` is one")
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
    case "skip" <> args:
      Skip.skip(args)
    case "identity" <> args:
      Identity.set(args)
    case "update" <> args:
      U.update(args)
    case "merge" <> args:
      M.merge(args)
    case "arrange" <> args:
      Arrange.arrange(args)
    case "prune" <> args:
      Prune.prune(args)
    case "receive" <> args:
      Receive.receive(args)
    case "offer" <> args:
      Offer.offer(args)
    case "export" <> args:
      Export.export(args)
    case "forget" <> args:
      F.forget(args)
    case "opdiff" <> parent <> child <> Nil{}:
      C.opdiff(parent, child)
    case word <> args:
      Shell.elsewhere(base, word, args)
    case Nil{}:
      Shell.usage()

def asked(a: Argv.Asked) -> IO(Unit):
  match a:
    case Argv.Asked.Usage{}:
      Shell.usage()
    case Argv.Asked.Version{}:
      Shell.version()
    case Argv.Asked.Wrong{msg}:
      C.die(Unit, 2, msg)
    case Argv.Asked.Command{base, word, rest}:
      dispatch(Maybe.default(&2, String, base, "."), word <> rest)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&2, String> <- Argv.args()
    asked(Argv.read(args))
