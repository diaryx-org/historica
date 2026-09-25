# One directory's listing, read back by the walk. `Store.folder` writes an
# entry a line — `d <name>`, `f <x> <size> <name>`, `l <name>` with its
# target on the next line, `L <name>`, `o <name>`, `u <lossy name>` — and
# the walk reads each line as the entry the host wrote it for: its kind,
# its name in normal form C, a file's execute bit and size, a link's target
# as the folder spells it, and a directory beside where the folder spells
# it. What it takes of those is the rules' business and `tracked`'s; that
# it asks them of the entry the host listed is this file's.
import Base
import ./folder.bend as F
import ./text.bend as T
import ./nfc.bend as Nfc
import ./bookmark.bend as Bm
import ./string_lemmas.bend as S
import ./bookmark_lemmas.bend as BmL
import ./skip_lemmas.bend as SkipL
import ./composition_lemmas.bend as Comp
import ./anchor_lemmas.bend as AL
import ./host_lemmas.bend as HostL
import ./sort_lemmas.bend as SortL

# What the host lists
# -------------------

# One entry of a directory as the host knows it: a directory, a regular
# file with whether any execute bit is set and its size as the host spells
# it, a link and its target, a link whose target cannot be a line,
# anything else, and a name that is not UTF-8, spelled lossily.
type Entry is Data:
  Entry.Dir{name: String}
  Entry.File{runs: Bool, size: String, name: String}
  Entry.Link{name: String, target: String}
  Entry.Unreadable{name: String}
  Entry.Other{name: String}
  Entry.Unspelled{lossy: String}

def flag(r: Bool) -> String:
  match r:
    case True{}:
      "1"
    case False{}:
      "0"

# The lines the host writes for them, as `folder` in `ffi/src/lib.rs`
# writes them.
def lines(es: List<&2, Entry>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Entry.Dir{n} <> rest:
      ("d " ++ n) <> lines(rest)
    case Entry.File{r, z, n} <> rest:
      ("f " ++ flag(r) ++ " " ++ z ++ " " ++ n) <> lines(rest)
    case Entry.Link{n, t} <> rest:
      ("l " ++ n) <> t <> lines(rest)
    case Entry.Unreadable{n} <> rest:
      ("L " ++ n) <> lines(rest)
    case Entry.Other{n} <> rest:
      ("o " ++ n) <> lines(rest)
    case Entry.Unspelled{x} <> rest:
      ("u " ++ x) <> lines(rest)

# And the listing: the lines joined, as `lines.join("\n")`.
def text(es: List<&2, Entry>) -> String:
  String.join(lines(es), "\n")

# What the host writes of each entry is one line: a name holding a newline
# is left out, a link whose target holds one is `L`, and a size is digits.
def entry_ok(e: Entry) -> Bool:
  match e:
    case Entry.Dir{n}:
      BmL.nonl(n)
    case Entry.File{r, +z, n}:
      Bool.and(Bool.and(BmL.nonl(z), HostL.nosep(z, ' ')), BmL.nonl(n))
    case Entry.Link{n, t}:
      Bool.and(BmL.nonl(n), BmL.nonl(t))
    case Entry.Unreadable{n}:
      BmL.nonl(n)
    case Entry.Other{n}:
      BmL.nonl(n)
    case Entry.Unspelled{x}:
      BmL.nonl(x)

def entries_ok(es: List<&2, Entry>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> rest:
      Bool.and(entry_ok(e), entries_ok(rest))

# The entries with each name in normal form C, which is how the walk reads
# a name; a link's target and a name that cannot be spelled stay.
def normal(es: List<&2, Entry>) -> List<&2, Entry>:
  match es:
    case Nil{}:
      Nil{}
    case Entry.Dir{n} <> rest:
      Entry.Dir{Nfc.nfc(n)} <> normal(rest)
    case Entry.File{r, z, n} <> rest:
      Entry.File{r, z, Nfc.nfc(n)} <> normal(rest)
    case Entry.Link{n, t} <> rest:
      Entry.Link{Nfc.nfc(n), t} <> normal(rest)
    case Entry.Unreadable{n} <> rest:
      Entry.Unreadable{Nfc.nfc(n)} <> normal(rest)
    case Entry.Other{n} <> rest:
      Entry.Other{Nfc.nfc(n)} <> normal(rest)
    case Entry.Unspelled{x} <> rest:
      Entry.Unspelled{x} <> normal(rest)

# What the walk makes of them
# ---------------------------

# The directories to walk into: each named, as the walk names it — its
# name in normal form C under `dir` — beside where the folder spells it,
# under `disk`; all but the store and those a rule skips whole.
def dirs(es: List<&2, Entry>, +dir: String, +disk: String, +rules: List<&2, F.Scope>) -> List<&2, T.Split>:
  match es:
    case Nil{}:
      Nil{}
    case Entry.Dir{+n} <> rest:
      List.filter.put(T.Split, T.Split{F.joined(dir, Nfc.nfc(n)), F.joined(disk, n)}, dirs(rest, dir, disk, rules), Bool.not(Bool.or(F.is_store(dir, Nfc.nfc(n)), F.skips_directory(rules, F.joined(dir, Nfc.nfc(n))))))
    case e <> rest:
      dirs(rest, dir, disk, rules)

def firsts(xs: List<&2, T.Split>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case T.Split{a, b} <> rest:
      a <> firsts(rest)

def seconds(xs: List<&2, T.Split>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case T.Split{a, b} <> rest:
      b <> seconds(rest)

# The files and links it takes: each at its name in normal form C under
# `dir`, a file with its execute bit and its size read as a number, a link
# with its target; those `tracked` takes.
def found(es: List<&2, Entry>, +dir: String, +rules: List<&2, F.Scope>) -> List<&2, F.Found>:
  match es:
    case Nil{}:
      Nil{}
    case Entry.File{r, z, +n} <> rest:
      List.filter.put(F.Found, F.Found.File{F.joined(dir, Nfc.nfc(n)), r, Maybe.default(&2, Nat, Nat.read(z), 0n)}, found(rest, dir, rules), F.tracked(dir, Nfc.nfc(n), rules))
    case Entry.Link{+n, t} <> rest:
      List.filter.put(F.Found, F.Found.Link{F.joined(dir, Nfc.nfc(n)), t}, found(rest, dir, rules), F.tracked(dir, Nfc.nfc(n), rules))
    case e <> rest:
      found(rest, dir, rules)

def put(m: Maybe<&2, T.Split>, rest: List<&2, T.Split>) -> List<&2, T.Split>:
  match m:
    case None{}:
      rest
    case Some{x}:
      x <> rest

# What it refuses, as `refusal.of` words it: a file or a link for its path,
# a link whose target cannot be a line for that too, anything else for
# what it is; a directory is walked, and a name that cannot be spelled is
# `odd`'s.
def refused(es: List<&2, Entry>, +dir: String, +rules: List<&2, F.Scope>) -> List<&2, T.Split>:
  match es:
    case Nil{}:
      Nil{}
    case Entry.File{r, z, n} <> rest:
      put(F.refusal.of(dir, rules, Nfc.nfc(n), False{}, False{}), refused(rest, dir, rules))
    case Entry.Link{n, t} <> rest:
      put(F.refusal.of(dir, rules, Nfc.nfc(n), False{}, False{}), refused(rest, dir, rules))
    case Entry.Unreadable{n} <> rest:
      put(F.refusal.of(dir, rules, Nfc.nfc(n), False{}, True{}), refused(rest, dir, rules))
    case Entry.Other{n} <> rest:
      put(F.refusal.of(dir, rules, Nfc.nfc(n), True{}, False{}), refused(rest, dir, rules))
    case e <> rest:
      refused(rest, dir, rules)

# Each name that cannot be spelled, refused where it is on disk, `at`, in
# `WorkingError::NotUtf8`'s words.
def odd(es: List<&2, Entry>, +at: String) -> List<&2, T.Split>:
  match es:
    case Nil{}:
      Nil{}
    case Entry.Unspelled{x} <> rest:
      T.Split{at ++ "/" ++ x, "not a name this format can hold"} <> odd(rest, at)
    case e <> rest:
      odd(rest, at)

# What the walk holds after a listing, with the names that cannot be
# spelled as their refusals: where each was met is the walk's order, which
# the key keeps and this does not ask.
type Seen is Data:
  Seen{pending: List<&2, T.Split>, found: List<&2, F.Found>, refused: List<&2, T.Split>, odd: List<&2, T.Split>}

def seen(w: F.Walking) -> Seen:
  match w:
    case F.Walking{p, f, r, o}:
      Seen{p, f, r, F.unkeyed(o)}

# Strings
# -------

def sw_empty(t: String) -> {String.starts_with(t, SNil{}) == True{} : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{h, r}:
      {==}

# A word with no space in it, a space, and the rest: cut at that space.
def split_word.go(z: String, +n: String, +acc: String, +h: {HostL.nosep(z, ' ') == True{} : Bool}) -> {T.split_once.fast(z ++ SCon{' ', n}, acc, T.space_first(z ++ SCon{' ', n})) == Some{T.Split{String.reverse(String.reverse.go(z, acc)), n}} : Maybe<&2, T.Split>}:
  match z:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Char.is_eq(c, ' '), False{}, AL.not_of_true(Char.is_eq(c, ' '), Comp.and_left(Bool.not(Char.is_eq(c, ' ')), HostL.nosep(t, ' '), h))) : {T.split_once.fast(SCon{c, t ++ SCon{' ', n}}, acc, _) == Some{T.Split{String.reverse(String.reverse.go(t, SCon{c, acc})), n}} : Maybe<&2, T.Split>}
      split_word.go(t, n, SCon{c, acc}, Comp.and_right(Bool.not(Char.is_eq(c, ' ')), HostL.nosep(t, ' '), h))

def split_word(+z: String, +n: String, +h: {HostL.nosep(z, ' ') == True{} : Bool}) -> {T.split_once(z ++ " " ++ n) == Some{T.Split{z, n}} : Maybe<&2, T.Split>}:
  %SkipL.rev_rev(z) : {T.split_once(z ++ " " ++ n) == Some{T.Split{_, n}} : Maybe<&2, T.Split>}
  split_word.go(z, n, SNil{}, h)

# A name in normal form C, as the walk reads it past its kind and a space.
def named(n: String) -> {String.take(n, 0n) ++ Nfc.nfc(String.drop(n, 0n)) == Nfc.nfc(n) : String}:
  match n:
    case SNil{}:
      {==}
    case SCon{c, t}:
      {==}

def named_line(+k: Char, +n: String) -> {SCon{k, SCon{' ', String.take(n, 0n) ++ Nfc.nfc(String.drop(n, 0n))}} == SCon{k, SCon{' ', Nfc.nfc(n)}} : String}:
  Equal.cong(String, String, x => SCon{k, SCon{' ', x}}, String.take(n, 0n) ++ Nfc.nfc(String.drop(n, 0n)), Nfc.nfc(n), named(n))

# A file's line, its name in normal form C.
def file_line(r: Bool, +z: String, +n: String, +h: {HostL.nosep(z, ' ') == True{} : Bool}) -> {F.normal.line("f " ++ flag(r) ++ " " ++ z ++ " " ++ n) == "f " ++ flag(r) ++ " " ++ z ++ " " ++ Nfc.nfc(n) : String}:
  match r:
    case True{}:
      %Equal.sym(Maybe<&2, T.Split>, T.split_once(z ++ " " ++ n), Some{T.Split{z, n}}, split_word(z, n, h)) : {"f " ++ F.normal.sized("1", _) == "f 1 " ++ z ++ " " ++ Nfc.nfc(n) : String}
      {==}
    case False{}:
      %Equal.sym(Maybe<&2, T.Split>, T.split_once(z ++ " " ++ n), Some{T.Split{z, n}}, split_word(z, n, h)) : {"f " ++ F.normal.sized("0", _) == "f 0 " ++ z ++ " " ++ Nfc.nfc(n) : String}
      {==}

def unspelled_line(+x: String) -> {F.normal.line("u " ++ x) == "u " ++ x : String}:
  %Equal.sym(Bool, String.starts_with(x, SNil{}), True{}, sw_empty(x)) : {Bool.pick(String, _, "u " ++ x, String.take("u " ++ x, 2n) ++ Nfc.nfc(String.drop("u " ++ x, 2n))) == "u " ++ x : String}
  {==}

def file_ok(+r: Bool, +z: String, +n: String, +rest: List<&2, Entry>, +h: {entries_ok(Entry.File{r, z, n} <> rest) == True{} : Bool}) -> {HostL.nosep(z, ' ') == True{} : Bool}:
  Comp.and_right(BmL.nonl(z), HostL.nosep(z, ' '), Comp.and_left(Bool.and(BmL.nonl(z), HostL.nosep(z, ' ')), BmL.nonl(n), Comp.and_left(entry_ok(Entry.File{r, z, n}), entries_ok(rest), h)))

def rest_ok(+e: Entry, +rest: List<&2, Entry>, +h: {entries_ok(e <> rest) == True{} : Bool}) -> {entries_ok(rest) == True{} : Bool}:
  Comp.and_right(entry_ok(e), entries_ok(rest), h)

# Normal form C
# -------------

# The walk reads each name the host lists in normal form C, and a link's
# target, and a name that cannot be spelled, as the host wrote them.
def normal_lines(es: List<&2, Entry>, +h: {entries_ok(es) == True{} : Bool}) -> {F.normal.lines(lines(es), False{}) == lines(normal(es)) : List<&2, String>}:
  match es:
    case Nil{}:
      {==}
    case Entry.Dir{+n} <> +rest:
      %Equal.sym(String, F.normal.line("d " ++ n), "d " ++ Nfc.nfc(n), named_line('d', n)) : {_ <> F.normal.lines(lines(rest), False{}) == ("d " ++ Nfc.nfc(n)) <> lines(normal(rest)) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, l => ("d " ++ Nfc.nfc(n)) <> l, F.normal.lines(lines(rest), False{}), lines(normal(rest)), normal_lines(rest, rest_ok(Entry.Dir{n}, rest, h)))
    case Entry.File{+r, +z, +n} <> +rest:
      %Equal.sym(String, F.normal.line("f " ++ flag(r) ++ " " ++ z ++ " " ++ n), "f " ++ flag(r) ++ " " ++ z ++ " " ++ Nfc.nfc(n), file_line(r, z, n, file_ok(r, z, n, rest, h))) : {_ <> F.normal.lines(lines(rest), String.starts_with("f " ++ flag(r) ++ " " ++ z ++ " " ++ n, "l ")) == ("f " ++ flag(r) ++ " " ++ z ++ " " ++ Nfc.nfc(n)) <> lines(normal(rest)) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, l => ("f " ++ flag(r) ++ " " ++ z ++ " " ++ Nfc.nfc(n)) <> l, F.normal.lines(lines(rest), False{}), lines(normal(rest)), normal_lines(rest, rest_ok(Entry.File{r, z, n}, rest, h)))
    case Entry.Link{+n, +t} <> +rest:
      %Equal.sym(String, F.normal.line("l " ++ n), "l " ++ Nfc.nfc(n), named_line('l', n)) : {_ <> F.normal.lines(t <> lines(rest), String.starts_with(n, SNil{})) == ("l " ++ Nfc.nfc(n)) <> t <> lines(normal(rest)) : List<&2, String>}
      %Equal.sym(Bool, String.starts_with(n, SNil{}), True{}, sw_empty(n)) : {("l " ++ Nfc.nfc(n)) <> F.normal.lines(t <> lines(rest), _) == ("l " ++ Nfc.nfc(n)) <> t <> lines(normal(rest)) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, l => ("l " ++ Nfc.nfc(n)) <> t <> l, F.normal.lines(lines(rest), False{}), lines(normal(rest)), normal_lines(rest, rest_ok(Entry.Link{n, t}, rest, h)))
    case Entry.Unreadable{+n} <> +rest:
      %Equal.sym(String, F.normal.line("L " ++ n), "L " ++ Nfc.nfc(n), named_line('L', n)) : {_ <> F.normal.lines(lines(rest), False{}) == ("L " ++ Nfc.nfc(n)) <> lines(normal(rest)) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, l => ("L " ++ Nfc.nfc(n)) <> l, F.normal.lines(lines(rest), False{}), lines(normal(rest)), normal_lines(rest, rest_ok(Entry.Unreadable{n}, rest, h)))
    case Entry.Other{+n} <> +rest:
      %Equal.sym(String, F.normal.line("o " ++ n), "o " ++ Nfc.nfc(n), named_line('o', n)) : {_ <> F.normal.lines(lines(rest), False{}) == ("o " ++ Nfc.nfc(n)) <> lines(normal(rest)) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, l => ("o " ++ Nfc.nfc(n)) <> l, F.normal.lines(lines(rest), False{}), lines(normal(rest)), normal_lines(rest, rest_ok(Entry.Other{n}, rest, h)))
    case Entry.Unspelled{+x} <> +rest:
      %Equal.sym(String, F.normal.line("u " ++ x), "u " ++ x, unspelled_line(x)) : {_ <> F.normal.lines(lines(rest), False{}) == ("u " ++ x) <> lines(normal(rest)) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, l => ("u " ++ x) <> l, F.normal.lines(lines(rest), False{}), lines(normal(rest)), normal_lines(rest, rest_ok(Entry.Unspelled{x}, rest, h)))

# The listing read
# ----------------

# A path the format can hold is not empty.
def held_full(p: String, e: {Bm.name_ok(p) == True{} : Bool}) -> {String.is_empty(p) == False{} : Bool}:
  match p:
    case SNil{}:
      Empty.absurd({String.is_empty(SNil{}) == False{} : Bool}, S.false_true(e))
    case SCon{c, t}:
      {==}

# So a link the walk takes is at a path, and its target is read for it.
def tracked_full(+prefix: String, +name: String, +rules: List<&2, F.Scope>, e: {F.tracked(prefix, name, rules) == True{} : Bool}) -> {String.is_empty(F.joined(prefix, name)) == False{} : Bool}:
  held_full(F.joined(prefix, name), Comp.and_right(Bool.not(F.skips(rules, F.joined(prefix, name))), Bm.name_ok(F.joined(prefix, name)), Comp.and_right(Bool.not(F.is_store(prefix, name)), Bool.and(Bool.not(F.skips(rules, F.joined(prefix, name))), Bm.name_ok(F.joined(prefix, name))), e)))

def dir_case(skip: Bool, +prefix: String, +disk: String, +rules: List<&2, F.Scope>, +n: String, ls: List<&2, String>, rest: List<&2, Entry>, +ds: List<&2, String>, +fs: List<&2, F.Found>, iht: {F.listing.go(ls, prefix, rules, F.Listing{ds, fs, None{}}) == F.Listing{List.reverse.go(&2, String, firsts(dirs(rest, prefix, disk, rules)), ds), List.reverse.go(&2, F.Found, found(rest, prefix, rules), fs), None{}} : F.Listing}, ihf: {F.listing.go(ls, prefix, rules, F.Listing{F.joined(prefix, Nfc.nfc(n)) <> ds, fs, None{}}) == F.Listing{List.reverse.go(&2, String, firsts(dirs(rest, prefix, disk, rules)), F.joined(prefix, Nfc.nfc(n)) <> ds), List.reverse.go(&2, F.Found, found(rest, prefix, rules), fs), None{}} : F.Listing}) -> {F.listing.go(ls, prefix, rules, F.listing.dir(ds, fs, prefix, rules, Nfc.nfc(n), skip)) == F.Listing{List.reverse.go(&2, String, firsts(List.filter.put(T.Split, T.Split{F.joined(prefix, Nfc.nfc(n)), F.joined(disk, n)}, dirs(rest, prefix, disk, rules), Bool.not(skip))), ds), List.reverse.go(&2, F.Found, found(rest, prefix, rules), fs), None{}} : F.Listing}:
  match skip:
    case True{}:
      iht
    case False{}:
      ihf

def took_case(take: Bool, +r: Bool, +prefix: String, +disk: String, +rules: List<&2, F.Scope>, +z: String, +n: String, ls: List<&2, String>, rest: List<&2, Entry>, +ds: List<&2, String>, +fs: List<&2, F.Found>, iht: {F.listing.go(ls, prefix, rules, F.Listing{ds, F.Found.File{F.joined(prefix, Nfc.nfc(n)), r, Maybe.default(&2, Nat, Nat.read(z), 0n)} <> fs, None{}}) == F.Listing{List.reverse.go(&2, String, firsts(dirs(rest, prefix, disk, rules)), ds), List.reverse.go(&2, F.Found, found(rest, prefix, rules), F.Found.File{F.joined(prefix, Nfc.nfc(n)), r, Maybe.default(&2, Nat, Nat.read(z), 0n)} <> fs), None{}} : F.Listing}, ihf: {F.listing.go(ls, prefix, rules, F.Listing{ds, fs, None{}}) == F.Listing{List.reverse.go(&2, String, firsts(dirs(rest, prefix, disk, rules)), ds), List.reverse.go(&2, F.Found, found(rest, prefix, rules), fs), None{}} : F.Listing}) -> {F.listing.go(ls, prefix, rules, F.listing.took(ds, fs, prefix, r, z, Nfc.nfc(n), take)) == F.Listing{List.reverse.go(&2, String, firsts(dirs(rest, prefix, disk, rules)), ds), List.reverse.go(&2, F.Found, List.filter.put(F.Found, F.Found.File{F.joined(prefix, Nfc.nfc(n)), r, Maybe.default(&2, Nat, Nat.read(z), 0n)}, found(rest, prefix, rules), take), fs), None{}} : F.Listing}:
  match take:
    case True{}:
      iht
    case False{}:
      ihf

def link_case(take: Bool, +prefix: String, +disk: String, +rules: List<&2, F.Scope>, +n: String, +t: String, ls: List<&2, String>, rest: List<&2, Entry>, +ds: List<&2, String>, +fs: List<&2, F.Found>, et: {F.tracked(prefix, Nfc.nfc(n), rules) == take : Bool}, iht: {F.listing.go(ls, prefix, rules, F.Listing{ds, F.Found.Link{F.joined(prefix, Nfc.nfc(n)), t} <> fs, None{}}) == F.Listing{List.reverse.go(&2, String, firsts(dirs(rest, prefix, disk, rules)), ds), List.reverse.go(&2, F.Found, found(rest, prefix, rules), F.Found.Link{F.joined(prefix, Nfc.nfc(n)), t} <> fs), None{}} : F.Listing}, ihf: {F.listing.go(ls, prefix, rules, F.Listing{ds, fs, None{}}) == F.Listing{List.reverse.go(&2, String, firsts(dirs(rest, prefix, disk, rules)), ds), List.reverse.go(&2, F.Found, found(rest, prefix, rules), fs), None{}} : F.Listing}) -> {F.listing.go(t <> ls, prefix, rules, F.listing.link(ds, fs, prefix, Nfc.nfc(n), take)) == F.Listing{List.reverse.go(&2, String, firsts(dirs(rest, prefix, disk, rules)), ds), List.reverse.go(&2, F.Found, List.filter.put(F.Found, F.Found.Link{F.joined(prefix, Nfc.nfc(n)), t}, found(rest, prefix, rules), take), fs), None{}} : F.Listing}:
  match take:
    case True{}:
      %Equal.sym(Bool, String.is_empty(F.joined(prefix, Nfc.nfc(n))), False{}, tracked_full(prefix, Nfc.nfc(n), rules, et)) : {F.listing.go(ls, prefix, rules, F.listing.linked(ds, fs, F.joined(prefix, Nfc.nfc(n)), t, _)) == F.Listing{List.reverse.go(&2, String, firsts(dirs(rest, prefix, disk, rules)), ds), List.reverse.go(&2, F.Found, found(rest, prefix, rules), F.Found.Link{F.joined(prefix, Nfc.nfc(n)), t} <> fs), None{}} : F.Listing}
      iht
    case False{}:
      ihf

def file_case(r: Bool, +z: String, +n: String, +prefix: String, +disk: String, +rules: List<&2, F.Scope>, ls: List<&2, String>, rest: List<&2, Entry>, +ds: List<&2, String>, +fs: List<&2, F.Found>, +hz: {HostL.nosep(z, ' ') == True{} : Bool}, iht: {F.listing.go(ls, prefix, rules, F.Listing{ds, F.Found.File{F.joined(prefix, Nfc.nfc(n)), r, Maybe.default(&2, Nat, Nat.read(z), 0n)} <> fs, None{}}) == F.Listing{List.reverse.go(&2, String, firsts(dirs(rest, prefix, disk, rules)), ds), List.reverse.go(&2, F.Found, found(rest, prefix, rules), F.Found.File{F.joined(prefix, Nfc.nfc(n)), r, Maybe.default(&2, Nat, Nat.read(z), 0n)} <> fs), None{}} : F.Listing}, ihf: {F.listing.go(ls, prefix, rules, F.Listing{ds, fs, None{}}) == F.Listing{List.reverse.go(&2, String, firsts(dirs(rest, prefix, disk, rules)), ds), List.reverse.go(&2, F.Found, found(rest, prefix, rules), fs), None{}} : F.Listing}) -> {F.listing.go(("f " ++ flag(r) ++ " " ++ z ++ " " ++ Nfc.nfc(n)) <> ls, prefix, rules, F.Listing{ds, fs, None{}}) == F.Listing{List.reverse.go(&2, String, firsts(dirs(rest, prefix, disk, rules)), ds), List.reverse.go(&2, F.Found, List.filter.put(F.Found, F.Found.File{F.joined(prefix, Nfc.nfc(n)), r, Maybe.default(&2, Nat, Nat.read(z), 0n)}, found(rest, prefix, rules), F.tracked(prefix, Nfc.nfc(n), rules)), fs), None{}} : F.Listing}:
  match r:
    case True{}:
      %Equal.sym(String, String.drop(z ++ " " ++ Nfc.nfc(n), 0n), z ++ " " ++ Nfc.nfc(n), HostL.drop_zero(z ++ " " ++ Nfc.nfc(n))) : {F.listing.go(ls, prefix, rules, F.listing.file(ds, fs, prefix, rules, True{}, T.split_once(_))) == F.Listing{List.reverse.go(&2, String, firsts(dirs(rest, prefix, disk, rules)), ds), List.reverse.go(&2, F.Found, List.filter.put(F.Found, F.Found.File{F.joined(prefix, Nfc.nfc(n)), True{}, Maybe.default(&2, Nat, Nat.read(z), 0n)}, found(rest, prefix, rules), F.tracked(prefix, Nfc.nfc(n), rules)), fs), None{}} : F.Listing}
      %Equal.sym(Maybe<&2, T.Split>, T.split_once(z ++ " " ++ Nfc.nfc(n)), Some{T.Split{z, Nfc.nfc(n)}}, split_word(z, Nfc.nfc(n), hz)) : {F.listing.go(ls, prefix, rules, F.listing.file(ds, fs, prefix, rules, True{}, _)) == F.Listing{List.reverse.go(&2, String, firsts(dirs(rest, prefix, disk, rules)), ds), List.reverse.go(&2, F.Found, List.filter.put(F.Found, F.Found.File{F.joined(prefix, Nfc.nfc(n)), True{}, Maybe.default(&2, Nat, Nat.read(z), 0n)}, found(rest, prefix, rules), F.tracked(prefix, Nfc.nfc(n), rules)), fs), None{}} : F.Listing}
      took_case(F.tracked(prefix, Nfc.nfc(n), rules), True{}, prefix, disk, rules, z, n, ls, rest, ds, fs, iht, ihf)
    case False{}:
      %Equal.sym(String, String.drop(z ++ " " ++ Nfc.nfc(n), 0n), z ++ " " ++ Nfc.nfc(n), HostL.drop_zero(z ++ " " ++ Nfc.nfc(n))) : {F.listing.go(ls, prefix, rules, F.listing.file(ds, fs, prefix, rules, False{}, T.split_once(_))) == F.Listing{List.reverse.go(&2, String, firsts(dirs(rest, prefix, disk, rules)), ds), List.reverse.go(&2, F.Found, List.filter.put(F.Found, F.Found.File{F.joined(prefix, Nfc.nfc(n)), False{}, Maybe.default(&2, Nat, Nat.read(z), 0n)}, found(rest, prefix, rules), F.tracked(prefix, Nfc.nfc(n), rules)), fs), None{}} : F.Listing}
      %Equal.sym(Maybe<&2, T.Split>, T.split_once(z ++ " " ++ Nfc.nfc(n)), Some{T.Split{z, Nfc.nfc(n)}}, split_word(z, Nfc.nfc(n), hz)) : {F.listing.go(ls, prefix, rules, F.listing.file(ds, fs, prefix, rules, False{}, _)) == F.Listing{List.reverse.go(&2, String, firsts(dirs(rest, prefix, disk, rules)), ds), List.reverse.go(&2, F.Found, List.filter.put(F.Found, F.Found.File{F.joined(prefix, Nfc.nfc(n)), False{}, Maybe.default(&2, Nat, Nat.read(z), 0n)}, found(rest, prefix, rules), F.tracked(prefix, Nfc.nfc(n), rules)), fs), None{}} : F.Listing}
      took_case(F.tracked(prefix, Nfc.nfc(n), rules), False{}, prefix, disk, rules, z, n, ls, rest, ds, fs, iht, ihf)

# The walk reads the host's lines, their names in normal form C, as the
# entries the host wrote them for: a directory onto those to walk next, a
# file or a link onto those found, where the rules and `tracked` take
# them, and nothing else onto either.
def listing_go(es: List<&2, Entry>, +prefix: String, +disk: String, +rules: List<&2, F.Scope>, +ds: List<&2, String>, +fs: List<&2, F.Found>, +h: {entries_ok(es) == True{} : Bool}) -> {F.listing.go(lines(normal(es)), prefix, rules, F.Listing{ds, fs, None{}}) == F.Listing{List.reverse.go(&2, String, firsts(dirs(es, prefix, disk, rules)), ds), List.reverse.go(&2, F.Found, found(es, prefix, rules), fs), None{}} : F.Listing}:
  match es:
    case Nil{}:
      {==}
    case Entry.Dir{+n} <> +rest:
      +hr = rest_ok(Entry.Dir{n}, rest, h)
      %Equal.sym(String, String.drop(Nfc.nfc(n), 0n), Nfc.nfc(n), HostL.drop_zero(Nfc.nfc(n))) : {F.listing.go(lines(normal(rest)), prefix, rules, F.listing.dir(ds, fs, prefix, rules, _, Bool.or(F.is_store(prefix, _), F.skips_directory(rules, F.joined(prefix, _))))) == F.Listing{List.reverse.go(&2, String, firsts(dirs(Entry.Dir{n} <> rest, prefix, disk, rules)), ds), List.reverse.go(&2, F.Found, found(rest, prefix, rules), fs), None{}} : F.Listing}
      dir_case(Bool.or(F.is_store(prefix, Nfc.nfc(n)), F.skips_directory(rules, F.joined(prefix, Nfc.nfc(n)))), prefix, disk, rules, n, lines(normal(rest)), rest, ds, fs, listing_go(rest, prefix, disk, rules, ds, fs, hr), listing_go(rest, prefix, disk, rules, F.joined(prefix, Nfc.nfc(n)) <> ds, fs, hr))
    case Entry.File{+r, +z, +n} <> +rest:
      +hr = rest_ok(Entry.File{r, z, n}, rest, h)
      file_case(r, z, n, prefix, disk, rules, lines(normal(rest)), rest, ds, fs, file_ok(r, z, n, rest, h), listing_go(rest, prefix, disk, rules, ds, F.Found.File{F.joined(prefix, Nfc.nfc(n)), r, Maybe.default(&2, Nat, Nat.read(z), 0n)} <> fs, hr), listing_go(rest, prefix, disk, rules, ds, fs, hr))
    case Entry.Link{+n, +t} <> +rest:
      +hr = rest_ok(Entry.Link{n, t}, rest, h)
      %Equal.sym(String, String.drop(Nfc.nfc(n), 0n), Nfc.nfc(n), HostL.drop_zero(Nfc.nfc(n))) : {F.listing.go(t <> lines(normal(rest)), prefix, rules, F.listing.link(ds, fs, prefix, _, F.tracked(prefix, _, rules))) == F.Listing{List.reverse.go(&2, String, firsts(dirs(rest, prefix, disk, rules)), ds), List.reverse.go(&2, F.Found, found(Entry.Link{n, t} <> rest, prefix, rules), fs), None{}} : F.Listing}
      link_case(F.tracked(prefix, Nfc.nfc(n), rules), prefix, disk, rules, n, t, lines(normal(rest)), rest, ds, fs, {==}, listing_go(rest, prefix, disk, rules, ds, F.Found.Link{F.joined(prefix, Nfc.nfc(n)), t} <> fs, hr), listing_go(rest, prefix, disk, rules, ds, fs, hr))
    case Entry.Unreadable{+n} <> +rest:
      listing_go(rest, prefix, disk, rules, ds, fs, rest_ok(Entry.Unreadable{n}, rest, h))
    case Entry.Other{+n} <> +rest:
      listing_go(rest, prefix, disk, rules, ds, fs, rest_ok(Entry.Other{n}, rest, h))
    case Entry.Unspelled{+x} <> +rest:
      listing_go(rest, prefix, disk, rules, ds, fs, rest_ok(Entry.Unspelled{x}, rest, h))

def raw_case(skip: Bool, +disk: String, +n: String, -x: String, +later: List<&2, String>, -rest: List<&2, T.Split>, ih: {later == seconds(rest) : List<&2, String>}) -> {Bool.pick(List<&2, String>, skip, later, F.joined(disk, n) <> later) == seconds(List.filter.put(T.Split, T.Split{x, F.joined(disk, n)}, rest, Bool.not(skip))) : List<&2, String>}:
  match skip:
    case True{}:
      ih
    case False{}:
      Equal.cong(List<&2, String>, List<&2, String>, l => F.joined(disk, n) <> l, later, seconds(rest), ih)

# And each directory it walks into next it lists where the folder spells
# it: the name the host gave, under where the folder spells this one.
def raw_dirs(es: List<&2, Entry>, +prefix: String, +disk: String, +rules: List<&2, F.Scope>) -> {F.raw.dirs(lines(es), prefix, disk, rules, False{}) == seconds(dirs(es, prefix, disk, rules)) : List<&2, String>}:
  match es:
    case Nil{}:
      {==}
    case Entry.Dir{+n} <> +rest:
      %Equal.sym(Bool, String.starts_with(n, SNil{}), True{}, sw_empty(n)) : {F.raw.dir("d " ++ n, prefix, disk, rules, _, F.raw.dirs(lines(rest), prefix, disk, rules, False{})) == seconds(dirs(Entry.Dir{n} <> rest, prefix, disk, rules)) : List<&2, String>}
      %Equal.sym(String, String.drop(n, 0n), n, HostL.drop_zero(n)) : {Bool.pick(List<&2, String>, Bool.or(F.is_store(prefix, Nfc.nfc(_)), F.skips_directory(rules, F.joined(prefix, Nfc.nfc(_)))), F.raw.dirs(lines(rest), prefix, disk, rules, False{}), F.joined(disk, _) <> F.raw.dirs(lines(rest), prefix, disk, rules, False{})) == seconds(dirs(Entry.Dir{n} <> rest, prefix, disk, rules)) : List<&2, String>}
      raw_case(Bool.or(F.is_store(prefix, Nfc.nfc(n)), F.skips_directory(rules, F.joined(prefix, Nfc.nfc(n)))), disk, n, F.joined(prefix, Nfc.nfc(n)), F.raw.dirs(lines(rest), prefix, disk, rules, False{}), dirs(rest, prefix, disk, rules), raw_dirs(rest, prefix, disk, rules))
    case Entry.File{r, z, n} <> +rest:
      raw_dirs(rest, prefix, disk, rules)
    case Entry.Link{+n, t} <> +rest:
      %Equal.sym(Bool, String.starts_with(n, SNil{}), True{}, sw_empty(n)) : {F.raw.dirs(t <> lines(rest), prefix, disk, rules, _) == seconds(dirs(rest, prefix, disk, rules)) : List<&2, String>}
      raw_dirs(rest, prefix, disk, rules)
    case Entry.Unreadable{n} <> +rest:
      raw_dirs(rest, prefix, disk, rules)
    case Entry.Other{n} <> +rest:
      raw_dirs(rest, prefix, disk, rules)
    case Entry.Unspelled{x} <> +rest:
      raw_dirs(rest, prefix, disk, rules)

# Refusals
# --------

def push_put(m: Maybe<&2, T.Split>, -xs: List<&2, T.Split>, -acc: List<&2, T.Split>) -> {List.reverse.go(&2, T.Split, xs, F.refusal.push(m, acc)) == List.reverse.go(&2, T.Split, put(m, xs), acc) : List<&2, T.Split>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# What one refusal, pushed, leaves: the rest refused onto it.
def refused_step(+m: Maybe<&2, T.Split>, ls: List<&2, String>, +prefix: String, +rules: List<&2, F.Scope>, rest: List<&2, Entry>, +acc: List<&2, T.Split>, ih: {F.refusals.go(ls, prefix, rules, False{}, F.refusal.push(m, acc)) == List.reverse.go(&2, T.Split, refused(rest, prefix, rules), F.refusal.push(m, acc)) : List<&2, T.Split>}) -> {F.refusals.go(ls, prefix, rules, False{}, F.refusal.push(m, acc)) == List.reverse.go(&2, T.Split, put(m, refused(rest, prefix, rules)), acc) : List<&2, T.Split>}:
  Equal.trans(List<&2, T.Split>, F.refusals.go(ls, prefix, rules, False{}, F.refusal.push(m, acc)), List.reverse.go(&2, T.Split, refused(rest, prefix, rules), F.refusal.push(m, acc)), List.reverse.go(&2, T.Split, put(m, refused(rest, prefix, rules)), acc), ih, push_put(m, refused(rest, prefix, rules), acc))

def refused_file(r: Bool, +z: String, +n: String, +prefix: String, +rules: List<&2, F.Scope>, ls: List<&2, String>, rest: List<&2, Entry>, +acc: List<&2, T.Split>, +hz: {HostL.nosep(z, ' ') == True{} : Bool}, e: {F.refusals.go(ls, prefix, rules, False{}, F.refusal.push(F.refusal.of(prefix, rules, Nfc.nfc(n), False{}, False{}), acc)) == List.reverse.go(&2, T.Split, put(F.refusal.of(prefix, rules, Nfc.nfc(n), False{}, False{}), refused(rest, prefix, rules)), acc) : List<&2, T.Split>}) -> {F.refusals.go(("f " ++ flag(r) ++ " " ++ z ++ " " ++ Nfc.nfc(n)) <> ls, prefix, rules, False{}, acc) == List.reverse.go(&2, T.Split, put(F.refusal.of(prefix, rules, Nfc.nfc(n), False{}, False{}), refused(rest, prefix, rules)), acc) : List<&2, T.Split>}:
  match r:
    case True{}:
      %Equal.sym(String, String.drop(z ++ " " ++ Nfc.nfc(n), 0n), z ++ " " ++ Nfc.nfc(n), HostL.drop_zero(z ++ " " ++ Nfc.nfc(n))) : {F.refusals.go(ls, prefix, rules, False{}, F.refusal.push(F.refusal.file(prefix, rules, T.split_once(_)), acc)) == List.reverse.go(&2, T.Split, put(F.refusal.of(prefix, rules, Nfc.nfc(n), False{}, False{}), refused(rest, prefix, rules)), acc) : List<&2, T.Split>}
      %Equal.sym(Maybe<&2, T.Split>, T.split_once(z ++ " " ++ Nfc.nfc(n)), Some{T.Split{z, Nfc.nfc(n)}}, split_word(z, Nfc.nfc(n), hz)) : {F.refusals.go(ls, prefix, rules, False{}, F.refusal.push(F.refusal.file(prefix, rules, _), acc)) == List.reverse.go(&2, T.Split, put(F.refusal.of(prefix, rules, Nfc.nfc(n), False{}, False{}), refused(rest, prefix, rules)), acc) : List<&2, T.Split>}
      e
    case False{}:
      %Equal.sym(String, String.drop(z ++ " " ++ Nfc.nfc(n), 0n), z ++ " " ++ Nfc.nfc(n), HostL.drop_zero(z ++ " " ++ Nfc.nfc(n))) : {F.refusals.go(ls, prefix, rules, False{}, F.refusal.push(F.refusal.file(prefix, rules, T.split_once(_)), acc)) == List.reverse.go(&2, T.Split, put(F.refusal.of(prefix, rules, Nfc.nfc(n), False{}, False{}), refused(rest, prefix, rules)), acc) : List<&2, T.Split>}
      %Equal.sym(Maybe<&2, T.Split>, T.split_once(z ++ " " ++ Nfc.nfc(n)), Some{T.Split{z, Nfc.nfc(n)}}, split_word(z, Nfc.nfc(n), hz)) : {F.refusals.go(ls, prefix, rules, False{}, F.refusal.push(F.refusal.file(prefix, rules, _), acc)) == List.reverse.go(&2, T.Split, put(F.refusal.of(prefix, rules, Nfc.nfc(n), False{}, False{}), refused(rest, prefix, rules)), acc) : List<&2, T.Split>}
      e

# The walk refuses what each entry the host listed is refused for, and a
# link's target is no entry.
def refusals_go(es: List<&2, Entry>, +prefix: String, +rules: List<&2, F.Scope>, +acc: List<&2, T.Split>, +h: {entries_ok(es) == True{} : Bool}) -> {F.refusals.go(lines(normal(es)), prefix, rules, False{}, acc) == List.reverse.go(&2, T.Split, refused(es, prefix, rules), acc) : List<&2, T.Split>}:
  match es:
    case Nil{}:
      {==}
    case Entry.Dir{+n} <> +rest:
      refusals_go(rest, prefix, rules, acc, rest_ok(Entry.Dir{n}, rest, h))
    case Entry.File{+r, +z, +n} <> +rest:
      refused_file(r, z, n, prefix, rules, lines(normal(rest)), rest, acc, file_ok(r, z, n, rest, h), refused_step(F.refusal.of(prefix, rules, Nfc.nfc(n), False{}, False{}), lines(normal(rest)), prefix, rules, rest, acc, refusals_go(rest, prefix, rules, F.refusal.push(F.refusal.of(prefix, rules, Nfc.nfc(n), False{}, False{}), acc), rest_ok(Entry.File{r, z, n}, rest, h))))
    case Entry.Link{+n, +t} <> +rest:
      %Equal.sym(String, String.drop(Nfc.nfc(n), 0n), Nfc.nfc(n), HostL.drop_zero(Nfc.nfc(n))) : {F.refusals.go(lines(normal(rest)), prefix, rules, False{}, F.refusal.push(F.refusal.of(prefix, rules, _, False{}, False{}), acc)) == List.reverse.go(&2, T.Split, put(F.refusal.of(prefix, rules, Nfc.nfc(n), False{}, False{}), refused(rest, prefix, rules)), acc) : List<&2, T.Split>}
      refused_step(F.refusal.of(prefix, rules, Nfc.nfc(n), False{}, False{}), lines(normal(rest)), prefix, rules, rest, acc, refusals_go(rest, prefix, rules, F.refusal.push(F.refusal.of(prefix, rules, Nfc.nfc(n), False{}, False{}), acc), rest_ok(Entry.Link{n, t}, rest, h)))
    case Entry.Unreadable{+n} <> +rest:
      %Equal.sym(String, String.drop(Nfc.nfc(n), 0n), Nfc.nfc(n), HostL.drop_zero(Nfc.nfc(n))) : {F.refusals.go(lines(normal(rest)), prefix, rules, False{}, F.refusal.push(F.refusal.of(prefix, rules, _, False{}, True{}), acc)) == List.reverse.go(&2, T.Split, put(F.refusal.of(prefix, rules, Nfc.nfc(n), False{}, True{}), refused(rest, prefix, rules)), acc) : List<&2, T.Split>}
      refused_step(F.refusal.of(prefix, rules, Nfc.nfc(n), False{}, True{}), lines(normal(rest)), prefix, rules, rest, acc, refusals_go(rest, prefix, rules, F.refusal.push(F.refusal.of(prefix, rules, Nfc.nfc(n), False{}, True{}), acc), rest_ok(Entry.Unreadable{n}, rest, h)))
    case Entry.Other{+n} <> +rest:
      %Equal.sym(String, String.drop(Nfc.nfc(n), 0n), Nfc.nfc(n), HostL.drop_zero(Nfc.nfc(n))) : {F.refusals.go(lines(normal(rest)), prefix, rules, False{}, F.refusal.push(F.refusal.of(prefix, rules, _, True{}, False{}), acc)) == List.reverse.go(&2, T.Split, put(F.refusal.of(prefix, rules, Nfc.nfc(n), True{}, False{}), refused(rest, prefix, rules)), acc) : List<&2, T.Split>}
      refused_step(F.refusal.of(prefix, rules, Nfc.nfc(n), True{}, False{}), lines(normal(rest)), prefix, rules, rest, acc, refusals_go(rest, prefix, rules, F.refusal.push(F.refusal.of(prefix, rules, Nfc.nfc(n), True{}, False{}), acc), rest_ok(Entry.Other{n}, rest, h)))
    case Entry.Unspelled{+x} <> +rest:
      refusals_go(rest, prefix, rules, acc, rest_ok(Entry.Unspelled{x}, rest, h))

# Names that cannot be spelled
# ----------------------------

# Each name the host could not spell is refused once, onto what was
# refused before, whatever the entry before it and the count.
def odd_back(es: List<&2, Entry>, +prefix: String, +at: String, +before: String, +k: U32, +acc: List<&2, F.Keyed>) -> {F.unkeyed(F.unspelled.go(lines(normal(es)), prefix, at, before, k, False{}, F.unspelled.is(lines(normal(es))), acc)) == List.reverse.go(&2, T.Split, odd(es, at), F.unkeyed(acc)) : List<&2, T.Split>}:
  match es:
    case Nil{}:
      {==}
    case Entry.Dir{+n} <> +rest:
      odd_back(rest, prefix, at, F.joined(prefix, F.entry.name("d " ++ Nfc.nfc(n))), 0, acc)
    case Entry.File{+r, +z, +n} <> +rest:
      odd_back(rest, prefix, at, F.joined(prefix, F.entry.name("f " ++ flag(r) ++ " " ++ z ++ " " ++ Nfc.nfc(n))), 0, acc)
    case Entry.Link{+n, +t} <> +rest:
      %Equal.sym(Bool, String.starts_with(Nfc.nfc(n), SNil{}), True{}, sw_empty(Nfc.nfc(n))) : {F.unkeyed(F.unspelled.go(t <> lines(normal(rest)), prefix, at, F.joined(prefix, F.entry.name("l " ++ Nfc.nfc(n))), 0, _, F.unspelled.is(t <> lines(normal(rest))), acc)) == List.reverse.go(&2, T.Split, odd(rest, at), F.unkeyed(acc)) : List<&2, T.Split>}
      odd_back(rest, prefix, at, F.joined(prefix, F.entry.name("l " ++ Nfc.nfc(n))), 0, acc)
    case Entry.Unreadable{+n} <> +rest:
      odd_back(rest, prefix, at, F.joined(prefix, F.entry.name("L " ++ Nfc.nfc(n))), 0, acc)
    case Entry.Other{+n} <> +rest:
      odd_back(rest, prefix, at, F.joined(prefix, F.entry.name("o " ++ Nfc.nfc(n))), 0, acc)
    case Entry.Unspelled{+x} <> +rest:
      %Equal.sym(Bool, String.starts_with(x, SNil{}), True{}, sw_empty(x)) : {F.unkeyed(F.unspelled.go(("u " ++ x) <> lines(normal(rest)), prefix, at, before, k, False{}, _, acc)) == List.reverse.go(&2, T.Split, odd(rest, at), T.Split{at ++ "/" ++ x, "not a name this format can hold"} <> F.unkeyed(acc)) : List<&2, T.Split>}
      %HostL.drop_zero(x) : {F.unkeyed(F.unspelled.go(lines(normal(rest)), prefix, at, before, (k + 1 : U32), False{}, F.unspelled.is(lines(normal(rest))), F.Keyed{F.unspelled.key(before, k), T.Split{at ++ "/" ++ String.drop(x, 0n), F.unspelled.because()}} <> acc)) == List.reverse.go(&2, T.Split, odd(rest, at), T.Split{at ++ "/" ++ _, "not a name this format can hold"} <> F.unkeyed(acc)) : List<&2, T.Split>}
      odd_back(rest, prefix, at, before, (k + 1 : U32), F.Keyed{F.unspelled.key(before, k), T.Split{at ++ "/" ++ String.drop(x, 0n), F.unspelled.because()}} <> acc)

def odd_all(es: List<&2, Entry>, +prefix: String, +at: String) -> {F.unkeyed(F.unspelled(lines(normal(es)), prefix, at)) == List.reverse(&2, T.Split, odd(es, at)) : List<&2, T.Split>}:
  odd_back(es, prefix, at, Bool.pick(String, String.is_empty(prefix), SNil{}, prefix ++ "/"), 0, Nil{})

def unkeyed_app(xs: List<&2, F.Keyed>, -ys: List<&2, F.Keyed>) -> {F.unkeyed(List.append(&2, F.Keyed, xs, ys)) == List.append(&2, T.Split, F.unkeyed(xs), F.unkeyed(ys)) : List<&2, T.Split>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      Equal.cong(List<&2, T.Split>, List<&2, T.Split>, l => F.keyed.refusal(x) <> l, F.unkeyed(List.append(&2, F.Keyed, rest, ys)), List.append(&2, T.Split, F.unkeyed(rest), F.unkeyed(ys)), unkeyed_app(rest, ys))

# Pairing
# -------

# The directories the listing names and where the folder spells them,
# each turned round onto what was there, pair as the directories do.
def paired_rev(xs: List<&2, T.Split>, +a: List<&2, String>, +b: List<&2, String>) -> {F.paired(List.reverse.go(&2, String, firsts(xs), a), List.reverse.go(&2, String, seconds(xs), b)) == List.reverse.go(&2, T.Split, xs, F.paired(a, b)) : List<&2, T.Split>}:
  match xs:
    case Nil{}:
      {==}
    case T.Split{+x, +y} <> rest:
      paired_rev(rest, x <> a, y <> b)

# The listing's lines
# -------------------

def file_nonl(r: Bool, +z: String, +n: String, +hz: {BmL.nonl(z) == True{} : Bool}, hn: {BmL.nonl(n) == True{} : Bool}) -> {BmL.nonl("f " ++ flag(r) ++ " " ++ z ++ " " ++ n) == True{} : Bool}:
  match r:
    case True{}:
      HostL.nonl_app(z, " " ++ n, hz, hn)
    case False{}:
      HostL.nonl_app(z, " " ++ n, hz, hn)

def lines_nonl(es: List<&2, Entry>, +h: {entries_ok(es) == True{} : Bool}) -> {HostL.all_nonl(lines(es)) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case Entry.Dir{+n} <> +rest:
      AL.and_intro(BmL.nonl(n), HostL.all_nonl(lines(rest)), Comp.and_left(BmL.nonl(n), entries_ok(rest), h), lines_nonl(rest, rest_ok(Entry.Dir{n}, rest, h)))
    case Entry.File{+r, +z, +n} <> +rest:
      +he = Comp.and_left(Bool.and(Bool.and(BmL.nonl(z), HostL.nosep(z, ' ')), BmL.nonl(n)), entries_ok(rest), h)
      AL.and_intro(BmL.nonl("f " ++ flag(r) ++ " " ++ z ++ " " ++ n), HostL.all_nonl(lines(rest)), file_nonl(r, z, n, Comp.and_left(BmL.nonl(z), HostL.nosep(z, ' '), Comp.and_left(Bool.and(BmL.nonl(z), HostL.nosep(z, ' ')), BmL.nonl(n), he)), Comp.and_right(Bool.and(BmL.nonl(z), HostL.nosep(z, ' ')), BmL.nonl(n), he)), lines_nonl(rest, rest_ok(Entry.File{r, z, n}, rest, h)))
    case Entry.Link{+n, +t} <> +rest:
      +he = Comp.and_left(Bool.and(BmL.nonl(n), BmL.nonl(t)), entries_ok(rest), h)
      AL.and_intro(BmL.nonl(n), HostL.all_nonl(t <> lines(rest)), Comp.and_left(BmL.nonl(n), BmL.nonl(t), he), AL.and_intro(BmL.nonl(t), HostL.all_nonl(lines(rest)), Comp.and_right(BmL.nonl(n), BmL.nonl(t), he), lines_nonl(rest, rest_ok(Entry.Link{n, t}, rest, h))))
    case Entry.Unreadable{+n} <> +rest:
      AL.and_intro(BmL.nonl(n), HostL.all_nonl(lines(rest)), Comp.and_left(BmL.nonl(n), entries_ok(rest), h), lines_nonl(rest, rest_ok(Entry.Unreadable{n}, rest, h)))
    case Entry.Other{+n} <> +rest:
      AL.and_intro(BmL.nonl(n), HostL.all_nonl(lines(rest)), Comp.and_left(BmL.nonl(n), entries_ok(rest), h), lines_nonl(rest, rest_ok(Entry.Other{n}, rest, h)))
    case Entry.Unspelled{+x} <> +rest:
      AL.and_intro(BmL.nonl(x), HostL.all_nonl(lines(rest)), Comp.and_left(BmL.nonl(x), entries_ok(rest), h), lines_nonl(rest, rest_ok(Entry.Unspelled{x}, rest, h)))

# The host's text, split at its newlines, is its lines.
def split_lines(e: Entry, +rest: List<&2, Entry>, +h: {entries_ok(e <> rest) == True{} : Bool}) -> {String.split(text(e <> rest), '\n') == lines(e <> rest) : List<&2, String>}:
  match e:
    case Entry.Dir{+n}:
      HostL.split_join("d " ++ n, lines(rest), lines_nonl(Entry.Dir{n} <> rest, h))
    case Entry.File{+r, +z, +n}:
      HostL.split_join("f " ++ flag(r) ++ " " ++ z ++ " " ++ n, lines(rest), lines_nonl(Entry.File{r, z, n} <> rest, h))
    case Entry.Link{+n, +t}:
      HostL.split_join("l " ++ n, t <> lines(rest), lines_nonl(Entry.Link{n, t} <> rest, h))
    case Entry.Unreadable{+n}:
      HostL.split_join("L " ++ n, lines(rest), lines_nonl(Entry.Unreadable{n} <> rest, h))
    case Entry.Other{+n}:
      HostL.split_join("o " ++ n, lines(rest), lines_nonl(Entry.Other{n} <> rest, h))
    case Entry.Unspelled{+x}:
      HostL.split_join("u " ++ x, lines(rest), lines_nonl(Entry.Unspelled{x} <> rest, h))

# The walk's step
# ---------------

def step_lines(+es: List<&2, Entry>, +dir: String, +disk: String, +at: String, +rules: List<&2, F.Scope>, +rest: List<&2, T.Split>, +found0: List<&2, F.Found>, +refused0: List<&2, T.Split>, +odd0: List<&2, F.Keyed>, +h: {entries_ok(es) == True{} : Bool}, e: {lines(es) == String.split(text(es), '\n') : List<&2, String>}) -> {seen(F.walk.step(text(es), dir, disk, at, rules, rest, found0, refused0, odd0)) == Seen{List.append(&2, T.Split, List.reverse(&2, T.Split, dirs(es, dir, disk, rules)), rest), List.reverse.go(&2, F.Found, found(es, dir, rules), found0), List.reverse.go(&2, T.Split, refused(es, dir, rules), refused0), List.append(&2, T.Split, List.reverse(&2, T.Split, odd(es, at)), F.unkeyed(odd0))} : Seen}:
  %e : {seen(F.Walking{List.append(&2, T.Split, F.paired(F.listing.dirs(F.listing.go(F.normal.lines(_, False{}), dir, rules, F.Listing{Nil{}, found0, None{}})), List.reverse(&2, String, F.raw.dirs(_, dir, disk, rules, False{}))), rest), F.listing.found(F.listing.go(F.normal.lines(_, False{}), dir, rules, F.Listing{Nil{}, found0, None{}})), F.refusals.go(F.normal.lines(_, False{}), dir, rules, False{}, refused0), List.append(&2, F.Keyed, F.unspelled(F.normal.lines(_, False{}), dir, at), odd0)}) == Seen{List.append(&2, T.Split, List.reverse(&2, T.Split, dirs(es, dir, disk, rules)), rest), List.reverse.go(&2, F.Found, found(es, dir, rules), found0), List.reverse.go(&2, T.Split, refused(es, dir, rules), refused0), List.append(&2, T.Split, List.reverse(&2, T.Split, odd(es, at)), F.unkeyed(odd0))} : Seen}
  %Equal.sym(List<&2, String>, F.normal.lines(lines(es), False{}), lines(normal(es)), normal_lines(es, h)) : {seen(F.Walking{List.append(&2, T.Split, F.paired(F.listing.dirs(F.listing.go(_, dir, rules, F.Listing{Nil{}, found0, None{}})), List.reverse(&2, String, F.raw.dirs(lines(es), dir, disk, rules, False{}))), rest), F.listing.found(F.listing.go(_, dir, rules, F.Listing{Nil{}, found0, None{}})), F.refusals.go(_, dir, rules, False{}, refused0), List.append(&2, F.Keyed, F.unspelled(_, dir, at), odd0)}) == Seen{List.append(&2, T.Split, List.reverse(&2, T.Split, dirs(es, dir, disk, rules)), rest), List.reverse.go(&2, F.Found, found(es, dir, rules), found0), List.reverse.go(&2, T.Split, refused(es, dir, rules), refused0), List.append(&2, T.Split, List.reverse(&2, T.Split, odd(es, at)), F.unkeyed(odd0))} : Seen}
  %Equal.sym(F.Listing, F.listing.go(lines(normal(es)), dir, rules, F.Listing{Nil{}, found0, None{}}), F.Listing{List.reverse.go(&2, String, firsts(dirs(es, dir, disk, rules)), Nil{}), List.reverse.go(&2, F.Found, found(es, dir, rules), found0), None{}}, listing_go(es, dir, disk, rules, Nil{}, found0, h)) : {seen(F.Walking{List.append(&2, T.Split, F.paired(F.listing.dirs(_), List.reverse(&2, String, F.raw.dirs(lines(es), dir, disk, rules, False{}))), rest), F.listing.found(_), F.refusals.go(lines(normal(es)), dir, rules, False{}, refused0), List.append(&2, F.Keyed, F.unspelled(lines(normal(es)), dir, at), odd0)}) == Seen{List.append(&2, T.Split, List.reverse(&2, T.Split, dirs(es, dir, disk, rules)), rest), List.reverse.go(&2, F.Found, found(es, dir, rules), found0), List.reverse.go(&2, T.Split, refused(es, dir, rules), refused0), List.append(&2, T.Split, List.reverse(&2, T.Split, odd(es, at)), F.unkeyed(odd0))} : Seen}
  %Equal.sym(List<&2, String>, F.raw.dirs(lines(es), dir, disk, rules, False{}), seconds(dirs(es, dir, disk, rules)), raw_dirs(es, dir, disk, rules)) : {seen(F.Walking{List.append(&2, T.Split, F.paired(List.reverse.go(&2, String, firsts(dirs(es, dir, disk, rules)), Nil{}), List.reverse(&2, String, _)), rest), List.reverse.go(&2, F.Found, found(es, dir, rules), found0), F.refusals.go(lines(normal(es)), dir, rules, False{}, refused0), List.append(&2, F.Keyed, F.unspelled(lines(normal(es)), dir, at), odd0)}) == Seen{List.append(&2, T.Split, List.reverse(&2, T.Split, dirs(es, dir, disk, rules)), rest), List.reverse.go(&2, F.Found, found(es, dir, rules), found0), List.reverse.go(&2, T.Split, refused(es, dir, rules), refused0), List.append(&2, T.Split, List.reverse(&2, T.Split, odd(es, at)), F.unkeyed(odd0))} : Seen}
  %Equal.sym(List<&2, T.Split>, F.paired(List.reverse.go(&2, String, firsts(dirs(es, dir, disk, rules)), Nil{}), List.reverse.go(&2, String, seconds(dirs(es, dir, disk, rules)), Nil{})), List.reverse.go(&2, T.Split, dirs(es, dir, disk, rules), F.paired(Nil{}, Nil{})), paired_rev(dirs(es, dir, disk, rules), Nil{}, Nil{})) : {seen(F.Walking{List.append(&2, T.Split, _, rest), List.reverse.go(&2, F.Found, found(es, dir, rules), found0), F.refusals.go(lines(normal(es)), dir, rules, False{}, refused0), List.append(&2, F.Keyed, F.unspelled(lines(normal(es)), dir, at), odd0)}) == Seen{List.append(&2, T.Split, List.reverse(&2, T.Split, dirs(es, dir, disk, rules)), rest), List.reverse.go(&2, F.Found, found(es, dir, rules), found0), List.reverse.go(&2, T.Split, refused(es, dir, rules), refused0), List.append(&2, T.Split, List.reverse(&2, T.Split, odd(es, at)), F.unkeyed(odd0))} : Seen}
  %Equal.sym(List<&2, T.Split>, F.refusals.go(lines(normal(es)), dir, rules, False{}, refused0), List.reverse.go(&2, T.Split, refused(es, dir, rules), refused0), refusals_go(es, dir, rules, refused0, h)) : {seen(F.Walking{List.append(&2, T.Split, List.reverse(&2, T.Split, dirs(es, dir, disk, rules)), rest), List.reverse.go(&2, F.Found, found(es, dir, rules), found0), _, List.append(&2, F.Keyed, F.unspelled(lines(normal(es)), dir, at), odd0)}) == Seen{List.append(&2, T.Split, List.reverse(&2, T.Split, dirs(es, dir, disk, rules)), rest), List.reverse.go(&2, F.Found, found(es, dir, rules), found0), List.reverse.go(&2, T.Split, refused(es, dir, rules), refused0), List.append(&2, T.Split, List.reverse(&2, T.Split, odd(es, at)), F.unkeyed(odd0))} : Seen}
  %Equal.sym(List<&2, T.Split>, F.unkeyed(List.append(&2, F.Keyed, F.unspelled(lines(normal(es)), dir, at), odd0)), List.append(&2, T.Split, F.unkeyed(F.unspelled(lines(normal(es)), dir, at)), F.unkeyed(odd0)), unkeyed_app(F.unspelled(lines(normal(es)), dir, at), odd0)) : {Seen{List.append(&2, T.Split, List.reverse(&2, T.Split, dirs(es, dir, disk, rules)), rest), List.reverse.go(&2, F.Found, found(es, dir, rules), found0), List.reverse.go(&2, T.Split, refused(es, dir, rules), refused0), _} == Seen{List.append(&2, T.Split, List.reverse(&2, T.Split, dirs(es, dir, disk, rules)), rest), List.reverse.go(&2, F.Found, found(es, dir, rules), found0), List.reverse.go(&2, T.Split, refused(es, dir, rules), refused0), List.append(&2, T.Split, List.reverse(&2, T.Split, odd(es, at)), F.unkeyed(odd0))} : Seen}
  %Equal.sym(List<&2, T.Split>, F.unkeyed(F.unspelled(lines(normal(es)), dir, at)), List.reverse(&2, T.Split, odd(es, at)), odd_all(es, dir, at)) : {Seen{List.append(&2, T.Split, List.reverse(&2, T.Split, dirs(es, dir, disk, rules)), rest), List.reverse.go(&2, F.Found, found(es, dir, rules), found0), List.reverse.go(&2, T.Split, refused(es, dir, rules), refused0), List.append(&2, T.Split, _, F.unkeyed(odd0))} == Seen{List.append(&2, T.Split, List.reverse(&2, T.Split, dirs(es, dir, disk, rules)), rest), List.reverse.go(&2, F.Found, found(es, dir, rules), found0), List.reverse.go(&2, T.Split, refused(es, dir, rules), refused0), List.append(&2, T.Split, List.reverse(&2, T.Split, odd(es, at)), F.unkeyed(odd0))} : Seen}
  {==}

# `a_listing_is_walked_as_the_host_wrote_it`.
def step_reads(es: List<&2, Entry>, +dir: String, +disk: String, +at: String, +rules: List<&2, F.Scope>, +rest: List<&2, T.Split>, +found0: List<&2, F.Found>, +refused0: List<&2, T.Split>, +odd0: List<&2, F.Keyed>, +h: {entries_ok(es) == True{} : Bool}) -> {seen(F.walk.step(text(es), dir, disk, at, rules, rest, found0, refused0, odd0)) == Seen{List.append(&2, T.Split, List.reverse(&2, T.Split, dirs(es, dir, disk, rules)), rest), List.reverse.go(&2, F.Found, found(es, dir, rules), found0), List.reverse.go(&2, T.Split, refused(es, dir, rules), refused0), List.append(&2, T.Split, List.reverse(&2, T.Split, odd(es, at)), F.unkeyed(odd0))} : Seen}:
  match es:
    case Nil{}:
      {==}
    case +e <> +more:
      step_lines(e <> more, dir, disk, at, rules, rest, found0, refused0, odd0, h, Equal.sym(List<&2, String>, String.split(text(e <> more), '\n'), lines(e <> more), split_lines(e, more, h)))

# The files the walk yields
# -------------------------

# The first of a list, as a list of none or one.
def first(xs: List<&2, F.Found>) -> List<&2, F.Found>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      [x]

def eq_flip.cmp(c: Cmp) -> {Cmp.is_eq(SortL.cflip(c)) == Cmp.is_eq(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# Two strings are one either way round.
def eq_sym(+a: String, +b: String) -> {String.eq(b, a) == String.eq(a, b) : Bool}:
  %Equal.sym(Bool, String.eq(b, a), Cmp.is_eq(String.order(b, a)), S.eq_order(b, a)) : {_ == String.eq(a, b) : Bool}
  %Equal.sym(Bool, String.eq(a, b), Cmp.is_eq(String.order(a, b)), S.eq_order(a, b)) : {Cmp.is_eq(String.order(b, a)) == _ : Bool}
  %Equal.sym(Cmp, String.order(b, a), SortL.cflip(String.order(a, b)), SortL.str_flip(a, b)) : {Cmp.is_eq(_) == Cmp.is_eq(String.order(a, b)) : Bool}
  eq_flip.cmp(String.order(a, b))

def le_ne.cmp(c: Cmp, h1: {Cmp.is_le(c) == True{} : Bool}, h2: {Cmp.is_eq(SortL.cflip(c)) == False{} : Bool}) -> {Cmp.is_le(SortL.cflip(c)) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_le(SortL.cflip(EQ{})) == False{} : Bool}, S.true_false(h2))
    case GT{}:
      Empty.absurd({Cmp.is_le(SortL.cflip(GT{})) == False{} : Bool}, S.false_true(h1))

# A string no larger than another it is not is smaller: the other is not
# no larger than it.
def le_ne(+a: String, +b: String, h1: {String.is_le(a, b) == True{} : Bool}, h2: {String.eq(b, a) == False{} : Bool}) -> {String.is_le(b, a) == False{} : Bool}:
  %Equal.sym(Cmp, String.order(b, a), SortL.cflip(String.order(a, b)), SortL.str_flip(a, b)) : {Cmp.is_le(_) == False{} : Bool}
  le_ne.cmp(String.order(a, b), h1, (%SortL.str_flip(a, b) : {Cmp.is_eq(_) == False{} : Bool}
    (%S.eq_order(b, a) : {_ == False{} : Bool}
      h2)))

def pick_nil(b: Bool) -> {Bool.pick(List<&2, F.Found>, b, Nil{}, Nil{}) == Nil{} : List<&2, F.Found>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def dropped_pick(e: Bool, +f: F.Found, +xs: List<&2, F.Found>) -> {Bool.pick(List<&2, F.Found>, e, Nil{}, first(xs)) == Bool.pick(List<&2, F.Found>, e, Nil{}, first(Bool.pick(List<&2, F.Found>, e, f <> xs, xs))) : List<&2, F.Found>}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

# The file kept for a path the one before did not have.
def kept_pick(c: Bool, d: Bool, +f: F.Found, +xs: List<&2, F.Found>, -ys: List<&2, F.Found>, +ih: {ys == Bool.pick(List<&2, F.Found>, c, Nil{}, first(xs)) : List<&2, F.Found>}, hcd: {c == True{} : Bool} -> {d == False{} : Bool}, hdc: {d == True{} : Bool} -> {c == False{} : Bool} -> {xs == Nil{} : List<&2, F.Found>}) -> {Bool.pick(List<&2, F.Found>, c, f <> ys, ys) == Bool.pick(List<&2, F.Found>, d, Nil{}, first(Bool.pick(List<&2, F.Found>, c, f <> xs, xs))) : List<&2, F.Found>}:
  match c:
    case True{}:
      %Equal.sym(Bool, d, False{}, hcd({==})) : {f <> ys == Bool.pick(List<&2, F.Found>, _, Nil{}, [f]) : List<&2, F.Found>}
      Equal.cong(List<&2, F.Found>, List<&2, F.Found>, l => f <> l, ys, Nil{}, ih)
    case False{}:
      match d:
        case False{}:
          ih
        case True{}:
          Equal.trans(List<&2, F.Found>, ys, first(xs), Nil{}, ih, Equal.cong(List<&2, F.Found>, List<&2, F.Found>, l => first(l), xs, Nil{}, hdc({==}, {==})))

# The path a file is at is not the one before it, so neither is a path
# that file is at.
def not_last(+q: String, +last: String, +p: String, e: {String.eq(q, last) == False{} : Bool}, ec: {String.eq(q, p) == True{} : Bool}) -> {String.eq(last, p) == False{} : Bool}:
  %S.eq_true(q, p, ec) : {String.eq(last, _) == False{} : Bool}
  %Equal.sym(Bool, String.eq(last, q), String.eq(q, last), eq_sym(q, last)) : {_ == False{} : Bool}
  e

# And the path before it, no larger than it and not it, is past no file
# after it.
def beyond(+q: String, +last: String, +p: String, hl: {String.is_le(last, q) == True{} : Bool}, e: {String.eq(q, last) == False{} : Bool}, ed: {String.eq(last, p) == True{} : Bool}) -> {String.is_le(q, p) == False{} : Bool}:
  %S.eq_true(last, p, ed) : {String.is_le(q, _) == False{} : Bool}
  le_ne(last, q, hl, e)

# Past a path, the walk's files in path order, less those at it: each path
# they hold once, at the first file there.
def dk(fs: List<&2, F.Found>, +last: String, same: Bool, +es: {F.distinct.same(fs, last) == same : Bool}, +p: String, +hs: {SortL.sorted.from(~F.Found, ~(f => F.found.path(f)), fs, last) == True{} : Bool}) -> {SortL.keyed(~F.Found, ~(f => F.found.path(f)), p, F.distinct.go(fs, last, same)) == Bool.pick(List<&2, F.Found>, String.eq(last, p), Nil{}, first(SortL.keyed(~F.Found, ~(f => F.found.path(f)), p, fs))) : List<&2, F.Found>}:
  match fs same:
    case Nil{} _:
      Equal.sym(List<&2, F.Found>, Bool.pick(List<&2, F.Found>, String.eq(last, p), Nil{}, Nil{}), Nil{}, pick_nil(String.eq(last, p)))
    case +f <> +rest True{}:
      +at = S.eq_true(F.found.path(f), last, es)
      +hr = SortL.band_r(String.is_le(last, F.found.path(f)), SortL.sorted.from(~F.Found, ~(f => F.found.path(f)), rest, F.found.path(f)), hs)
      +ih = dk(rest, last, F.distinct.same(rest, last), {==}, p, (%at : {SortL.sorted.from(~F.Found, ~(f => F.found.path(f)), rest, _) == True{} : Bool}
        hr))
      %Equal.sym(String, F.found.path(f), last, at) : {SortL.keyed(~F.Found, ~(f => F.found.path(f)), p, F.distinct.go(rest, last, F.distinct.same(rest, last))) == Bool.pick(List<&2, F.Found>, String.eq(last, p), Nil{}, first(Bool.pick(List<&2, F.Found>, String.eq(_, p), f <> SortL.keyed(~F.Found, ~(f => F.found.path(f)), p, rest), SortL.keyed(~F.Found, ~(f => F.found.path(f)), p, rest)))) : List<&2, F.Found>}
      Equal.trans(List<&2, F.Found>, SortL.keyed(~F.Found, ~(f => F.found.path(f)), p, F.distinct.go(rest, last, F.distinct.same(rest, last))), Bool.pick(List<&2, F.Found>, String.eq(last, p), Nil{}, first(SortL.keyed(~F.Found, ~(f => F.found.path(f)), p, rest))), Bool.pick(List<&2, F.Found>, String.eq(last, p), Nil{}, first(Bool.pick(List<&2, F.Found>, String.eq(last, p), f <> SortL.keyed(~F.Found, ~(f => F.found.path(f)), p, rest), SortL.keyed(~F.Found, ~(f => F.found.path(f)), p, rest)))),
        ih, dropped_pick(String.eq(last, p), f, SortL.keyed(~F.Found, ~(f => F.found.path(f)), p, rest)))
    case +f <> +rest False{}:
      +hl = SortL.band_l(String.is_le(last, F.found.path(f)), SortL.sorted.from(~F.Found, ~(f => F.found.path(f)), rest, F.found.path(f)), hs)
      +hr = SortL.band_r(String.is_le(last, F.found.path(f)), SortL.sorted.from(~F.Found, ~(f => F.found.path(f)), rest, F.found.path(f)), hs)
      kept_pick(String.eq(F.found.path(f), p), String.eq(last, p), f, SortL.keyed(~F.Found, ~(f => F.found.path(f)), p, rest), SortL.keyed(~F.Found, ~(f => F.found.path(f)), p, F.distinct.go(rest, F.found.path(f), F.distinct.same(rest, F.found.path(f)))),
        dk(rest, F.found.path(f), F.distinct.same(rest, F.found.path(f)), {==}, p, hr),
        ec => not_last(F.found.path(f), last, p, es, ec),
        ed => ec => SortL.keyed_none(~F.Found, ~(f => F.found.path(f)), rest, F.found.path(f), p, beyond(F.found.path(f), last, p, hl, es, ed), hr))

def head_pick(c: Bool, +f: F.Found, +xs: List<&2, F.Found>, -ys: List<&2, F.Found>, +ih: {ys == Bool.pick(List<&2, F.Found>, c, Nil{}, first(xs)) : List<&2, F.Found>}) -> {Bool.pick(List<&2, F.Found>, c, f <> ys, ys) == first(Bool.pick(List<&2, F.Found>, c, f <> xs, xs)) : List<&2, F.Found>}:
  match c:
    case True{}:
      Equal.cong(List<&2, F.Found>, List<&2, F.Found>, l => f <> l, ys, Nil{}, ih)
    case False{}:
      ih

# Files in path order keep, at each path, the first file there.
def distinct_keyed(ys: List<&2, F.Found>, +p: String, +hs: {SortL.sorted(~F.Found, ~(f => F.found.path(f)), ys) == True{} : Bool}) -> {SortL.keyed(~F.Found, ~(f => F.found.path(f)), p, F.distinct(ys)) == first(SortL.keyed(~F.Found, ~(f => F.found.path(f)), p, ys)) : List<&2, F.Found>}:
  match ys:
    case Nil{}:
      {==}
    case +f <> +rest:
      head_pick(String.eq(F.found.path(f), p), f, SortL.keyed(~F.Found, ~(f => F.found.path(f)), p, rest), SortL.keyed(~F.Found, ~(f => F.found.path(f)), p, F.distinct.go(rest, F.found.path(f), F.distinct.same(rest, F.found.path(f)))),
        dk(rest, F.found.path(f), F.distinct.same(rest, F.found.path(f)), {==}, p, SortL.band_r(String.is_le(SNil{}, F.found.path(f)), SortL.sorted.from(~F.Found, ~(f => F.found.path(f)), rest, F.found.path(f)), hs)))

# And stay in path order.
def ds_sorted(fs: List<&2, F.Found>, +last: String, same: Bool, +es: {F.distinct.same(fs, last) == same : Bool}, +k: String, +hk: {String.is_le(k, last) == True{} : Bool}, +hs: {SortL.sorted.from(~F.Found, ~(f => F.found.path(f)), fs, last) == True{} : Bool}) -> {SortL.sorted.from(~F.Found, ~(f => F.found.path(f)), F.distinct.go(fs, last, same), k) == True{} : Bool}:
  match fs same:
    case Nil{} _:
      {==}
    case +f <> +rest True{}:
      ds_sorted(rest, last, F.distinct.same(rest, last), {==}, k, hk, (%S.eq_true(F.found.path(f), last, es) : {SortL.sorted.from(~F.Found, ~(f => F.found.path(f)), rest, _) == True{} : Bool}
        SortL.band_r(String.is_le(last, F.found.path(f)), SortL.sorted.from(~F.Found, ~(f => F.found.path(f)), rest, F.found.path(f)), hs)))
    case +f <> +rest False{}:
      +hl = SortL.band_l(String.is_le(last, F.found.path(f)), SortL.sorted.from(~F.Found, ~(f => F.found.path(f)), rest, F.found.path(f)), hs)
      +hr = SortL.band_r(String.is_le(last, F.found.path(f)), SortL.sorted.from(~F.Found, ~(f => F.found.path(f)), rest, F.found.path(f)), hs)
      SortL.band_i(String.is_le(k, F.found.path(f)), SortL.sorted.from(~F.Found, ~(f => F.found.path(f)), F.distinct.go(rest, F.found.path(f), F.distinct.same(rest, F.found.path(f))), F.found.path(f)),
        SortL.str_le(k, last, F.found.path(f), hk, hl),
        ds_sorted(rest, F.found.path(f), F.distinct.same(rest, F.found.path(f)), {==}, F.found.path(f), SortL.le_self(F.found.path(f)), hr))

def distinct_sorted(ys: List<&2, F.Found>, +hs: {SortL.sorted(~F.Found, ~(f => F.found.path(f)), ys) == True{} : Bool}) -> {SortL.sorted(~F.Found, ~(f => F.found.path(f)), F.distinct(ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +f <> +rest:
      SortL.band_i(String.is_le(SNil{}, F.found.path(f)), SortL.sorted.from(~F.Found, ~(f => F.found.path(f)), F.distinct.go(rest, F.found.path(f), F.distinct.same(rest, F.found.path(f))), F.found.path(f)),
        SortL.le_empty(F.found.path(f)),
        ds_sorted(rest, F.found.path(f), F.distinct.same(rest, F.found.path(f)), {==}, F.found.path(f), SortL.le_self(F.found.path(f)), SortL.band_r(String.is_le(SNil{}, F.found.path(f)), SortL.sorted.from(~F.Found, ~(f => F.found.path(f)), rest, F.found.path(f)), hs)))

# `the_walk_yields_its_files_in_path_order`.
def finish_sorted(+fs: List<&2, F.Found>, +rs: List<&2, T.Split>) -> {SortL.sorted(~F.Found, ~(f => F.found.path(f)), F.walked.found(F.walk.finish(F.Walked{fs, rs}))) == True{} : Bool}:
  distinct_sorted(List.sort(~F.Found, ~(a => b => String.is_le(F.found.path(a), F.found.path(b))), fs), SortL.sort_sorted(~F.Found, ~(f => F.found.path(f)), fs))

# `the_walk_keeps_the_file_it_met_last`.
def finish_keeps(+fs: List<&2, F.Found>, +rs: List<&2, T.Split>, +p: String) -> {SortL.keyed(~F.Found, ~(f => F.found.path(f)), p, F.walked.found(F.walk.finish(F.Walked{fs, rs}))) == first(SortL.keyed(~F.Found, ~(f => F.found.path(f)), p, fs)) : List<&2, F.Found>}:
  %SortL.sort_keyed(~F.Found, ~(f => F.found.path(f)), fs, p) : {SortL.keyed(~F.Found, ~(f => F.found.path(f)), p, F.distinct(List.sort(~F.Found, ~(a => b => String.is_le(F.found.path(a), F.found.path(b))), fs))) == first(_) : List<&2, F.Found>}
  distinct_keyed(List.sort(~F.Found, ~(a => b => String.is_le(F.found.path(a), F.found.path(b))), fs), p, SortL.sort_sorted(~F.Found, ~(f => F.found.path(f)), fs))
