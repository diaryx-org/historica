# What `log` lists. Every revision it lists satisfies every filter asked
# of it — author, message, dates, and the file a revision must touch —
# whatever the limit: the filters take entries out and change nothing about
# the ones that stay, and the limit counts what they left.
import Base
import ./commands.bend as Main
import ./anchor_lemmas.bend as AL
import ./composition_lemmas.bend as Comp

def keep_full_ok(b: Bool, +f: Main.Full, rest: List<&2, Main.Full>, +fl: Main.Filter, eb: {Main.keeps(fl, f) == b : Bool}, hr: {Main.all_kept(fl, rest) == True{} : Bool}) -> {Main.all_kept(fl, Main.keep_full(b, f, rest)) == True{} : Bool}:
  match b:
    case True{}:
      AL.and_intro(Main.keeps(fl, f), Main.all_kept(fl, rest), eb, hr)
    case False{}:
      hr

def kept_ok(+fl: Main.Filter, fs: List<&2, Main.Full>) -> {Main.all_kept(fl, Main.kept(fl, fs)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +rest:
      keep_full_ok(Main.keeps(fl, f), f, Main.kept(fl, rest), fl, {==}, kept_ok(fl, rest))

def take_ok(fs: List<&2, Main.Full>, n: Nat, +fl: Main.Filter, +h: {Main.all_kept(fl, fs) == True{} : Bool}) -> {Main.all_kept(fl, List.take(&2, Main.Full, fs, n)) == True{} : Bool}:
  match fs n:
    case Nil{} _:
      {==}
    case +f <> rest 0n:
      {==}
    case +f <> rest 1n+q:
      AL.and_intro(Main.keeps(fl, f), Main.all_kept(fl, List.take(&2, Main.Full, rest, q)), Comp.and_left(Main.keeps(fl, f), Main.all_kept(fl, rest), h), take_ok(rest, q, fl, Comp.and_right(Main.keeps(fl, f), Main.all_kept(fl, rest), h)))

def limited_ok(fs: List<&2, Main.Full>, limit: Maybe<&2, Nat>, +fl: Main.Filter, h: {Main.all_kept(fl, fs) == True{} : Bool}) -> {Main.all_kept(fl, Main.limited(fs, limit)) == True{} : Bool}:
  match limit:
    case None{}:
      h
    case Some{n}:
      take_ok(fs, n, fl, h)

def listed_ok(+fl: Main.Filter, +fs: List<&2, Main.Full>, limit: Maybe<&2, Nat>) -> {Main.all_kept(fl, Main.limited(Main.kept(fl, fs), limit)) == True{} : Bool}:
  limited_ok(Main.kept(fl, fs), limit, fl, kept_ok(fl, fs))
