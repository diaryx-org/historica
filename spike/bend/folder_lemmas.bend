# The folder's walk takes nothing a rule skips. The host lists a directory
# a line an entry; reading that listing adds a file, or a link, only where
# no rule skips its path, and a directory to walk next only where no rule
# skips it whole. `walk` reads each directory's listing onto what the last
# left, starting from nothing, so no file it returns is one a rule skips.
import Base
import ./folder.bend as F
import ./text.bend as T
import ./bookmark.bend as Bm
import ./composition_lemmas.bend as Comp
import ./merge_lemmas.bend as ML
import ./anchor_lemmas.bend as AL

def ok3(a: Bool, b: Bool, -c: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}, ec: {c == True{} : Bool}) -> {Bool.and(a, Bool.and(b, c)) == True{} : Bool}:
  AL.and_intro(a, Bool.and(b, c), ea, AL.and_intro(b, c, eb, ec))

def linked_ok(+rules: List<&2, F.Scope>, +dirs: List<&2, String>, +found: List<&2, F.Found>, +p: String, +line: String, empty: Bool, ee: {String.is_empty(p) == empty : Bool}, hd: {F.dirs_kept(rules, dirs) == True{} : Bool}, hf: {F.none_skipped(rules, found) == True{} : Bool}, hl: {Bool.or(String.is_empty(p), Bool.not(F.skips(rules, p))) == True{} : Bool}) -> {F.listing.ok(rules, F.listing.linked(dirs, found, p, line, empty)) == True{} : Bool}:
  match empty:
    case True{}:
      ok3(F.dirs_kept(rules, dirs), F.none_skipped(rules, found), True{}, hd, hf, {==})
    case False{}:
      ok3(F.dirs_kept(rules, dirs), F.none_skipped(rules, F.Found.Link{p, line} <> found), True{}, hd,
        AL.and_intro(Bool.not(F.skips(rules, p)), F.none_skipped(rules, found), ML.or_left_false(String.is_empty(p), Bool.not(F.skips(rules, p)), hl, ee), hf),
        {==})

def dir_ok(+rules: List<&2, F.Scope>, +dirs: List<&2, String>, +found: List<&2, F.Found>, +prefix: String, +name: String, skip: Bool, es: {Bool.or(F.is_store(prefix, name), F.skips_directory(rules, F.joined(prefix, name))) == skip : Bool}, hd: {F.dirs_kept(rules, dirs) == True{} : Bool}, hf: {F.none_skipped(rules, found) == True{} : Bool}) -> {F.listing.ok(rules, F.listing.dir(dirs, found, prefix, rules, name, skip)) == True{} : Bool}:
  match skip:
    case True{}:
      ok3(F.dirs_kept(rules, dirs), F.none_skipped(rules, found), True{}, hd, hf, {==})
    case False{}:
      ok3(F.dirs_kept(rules, F.joined(prefix, name) <> dirs), F.none_skipped(rules, found), True{},
        AL.and_intro(Bool.not(F.skips_directory(rules, F.joined(prefix, name))), F.dirs_kept(rules, dirs), AL.not_true(F.skips_directory(rules, F.joined(prefix, name)), AL.or_false_r(F.is_store(prefix, name), F.skips_directory(rules, F.joined(prefix, name)), es)), hd),
        hf, {==})

# A file is taken only where `tracked` says so, which asks the rules first.
def took_ok(+rules: List<&2, F.Scope>, +dirs: List<&2, String>, +found: List<&2, F.Found>, +prefix: String, +runs: Bool, +size: String, +name: String, take: Bool, et: {F.tracked(prefix, name, rules) == take : Bool}, hd: {F.dirs_kept(rules, dirs) == True{} : Bool}, hf: {F.none_skipped(rules, found) == True{} : Bool}) -> {F.listing.ok(rules, F.listing.took(dirs, found, prefix, runs, size, name, take)) == True{} : Bool}:
  match take:
    case True{}:
      ok3(F.dirs_kept(rules, dirs), F.none_skipped(rules, F.Found.File{F.joined(prefix, name), runs, Maybe.default(&2, Nat, Nat.read(size), 0n)} <> found), True{}, hd,
        AL.and_intro(Bool.not(F.skips(rules, F.joined(prefix, name))), F.none_skipped(rules, found),
          Comp.and_left(Bool.not(F.skips(rules, F.joined(prefix, name))), Bm.name_ok(F.joined(prefix, name)), Comp.and_right(Bool.not(F.is_store(prefix, name)), Bool.and(Bool.not(F.skips(rules, F.joined(prefix, name))), Bm.name_ok(F.joined(prefix, name))), et)),
          hf),
        {==})
    case False{}:
      ok3(F.dirs_kept(rules, dirs), F.none_skipped(rules, found), True{}, hd, hf, {==})

def file_ok(+rules: List<&2, F.Scope>, +dirs: List<&2, String>, +found: List<&2, F.Found>, +prefix: String, +runs: Bool, cut: Maybe<&2, T.Split>, hd: {F.dirs_kept(rules, dirs) == True{} : Bool}, hf: {F.none_skipped(rules, found) == True{} : Bool}) -> {F.listing.ok(rules, F.listing.file(dirs, found, prefix, rules, runs, cut)) == True{} : Bool}:
  match cut:
    case None{}:
      ok3(F.dirs_kept(rules, dirs), F.none_skipped(rules, found), True{}, hd, hf, {==})
    case Some{T.Split{+size, +name}}:
      took_ok(rules, dirs, found, prefix, runs, size, name, F.tracked(prefix, name, rules), {==}, hd, hf)

def link_ok(+rules: List<&2, F.Scope>, +dirs: List<&2, String>, +found: List<&2, F.Found>, +prefix: String, +name: String, take: Bool, et: {F.tracked(prefix, name, rules) == take : Bool}, hd: {F.dirs_kept(rules, dirs) == True{} : Bool}, hf: {F.none_skipped(rules, found) == True{} : Bool}) -> {F.listing.ok(rules, F.listing.link(dirs, found, prefix, name, take)) == True{} : Bool}:
  match take:
    case True{}:
      ok3(F.dirs_kept(rules, dirs), F.none_skipped(rules, found), Bool.or(String.is_empty(F.joined(prefix, name)), Bool.not(F.skips(rules, F.joined(prefix, name)))), hd, hf,
        AL.or_right(String.is_empty(F.joined(prefix, name)), Bool.not(F.skips(rules, F.joined(prefix, name))),
          Comp.and_left(Bool.not(F.skips(rules, F.joined(prefix, name))), Bm.name_ok(F.joined(prefix, name)), Comp.and_right(Bool.not(F.is_store(prefix, name)), Bool.and(Bool.not(F.skips(rules, F.joined(prefix, name))), Bm.name_ok(F.joined(prefix, name))), et))))
    case False{}:
      ok3(F.dirs_kept(rules, dirs), F.none_skipped(rules, found), True{}, hd, hf, {==})

def kind_ok(+rules: List<&2, F.Scope>, +dirs: List<&2, String>, +found: List<&2, F.Found>, +prefix: String, +name: String, d: Bool, f: Bool, l: Bool, hd: {F.dirs_kept(rules, dirs) == True{} : Bool}, hf: {F.none_skipped(rules, found) == True{} : Bool}) -> {F.listing.ok(rules, F.listing.kind(dirs, found, prefix, rules, name, d, f, l)) == True{} : Bool}:
  match d:
    case True{}:
      dir_ok(rules, dirs, found, prefix, name, Bool.or(F.is_store(prefix, name), F.skips_directory(rules, F.joined(prefix, name))), {==}, hd, hf)
    case False{}:
      match f:
        case True{}:
          file_ok(rules, dirs, found, prefix, String.starts_with(name, "1"), T.split_once(String.drop(name, 2n)), hd, hf)
        case False{}:
          match l:
            case True{}:
              link_ok(rules, dirs, found, prefix, name, F.tracked(prefix, name, rules), {==}, hd, hf)
            case False{}:
              ok3(F.dirs_kept(rules, dirs), F.none_skipped(rules, found), True{}, hd, hf, {==})

def line_ok(l: F.Listing, +prefix: String, +rules: List<&2, F.Scope>, +line: String, +h: {F.listing.ok(rules, l) == True{} : Bool}) -> {F.listing.ok(rules, F.listing.line(l, prefix, rules, line)) == True{} : Bool}:
  match l:
    case F.Listing{+dirs, +found, Some{+p}}:
      linked_ok(rules, dirs, found, p, line, String.is_empty(p), {==},
        Comp.and_left(F.dirs_kept(rules, dirs), Bool.and(F.none_skipped(rules, found), F.link_kept(rules, Some{p})), h),
        Comp.and_left(F.none_skipped(rules, found), F.link_kept(rules, Some{p}), Comp.and_right(F.dirs_kept(rules, dirs), Bool.and(F.none_skipped(rules, found), F.link_kept(rules, Some{p})), h)),
        Comp.and_right(F.none_skipped(rules, found), F.link_kept(rules, Some{p}), Comp.and_right(F.dirs_kept(rules, dirs), Bool.and(F.none_skipped(rules, found), F.link_kept(rules, Some{p})), h)))
    case F.Listing{+dirs, +found, None{}}:
      kind_ok(rules, dirs, found, prefix, String.drop(line, 2n), String.eq(String.take(line, 1n), "d"), String.eq(String.take(line, 1n), "f"), String.eq(String.take(line, 1n), "l"),
        Comp.and_left(F.dirs_kept(rules, dirs), Bool.and(F.none_skipped(rules, found), True{}), h),
        Comp.and_left(F.none_skipped(rules, found), True{}, Comp.and_right(F.dirs_kept(rules, dirs), Bool.and(F.none_skipped(rules, found), True{}), h)))

def listing_ok(ls: List<&2, String>, +prefix: String, +rules: List<&2, F.Scope>, +l: F.Listing, h: {F.listing.ok(rules, l) == True{} : Bool}) -> {F.listing.ok(rules, F.listing.go(ls, prefix, rules, l)) == True{} : Bool}:
  match ls:
    case Nil{}:
      h
    case +line <> rest:
      listing_ok(rest, prefix, rules, F.listing.line(l, prefix, rules, line), line_ok(l, prefix, rules, line, h))
