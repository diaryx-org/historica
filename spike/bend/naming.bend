# What a store calls the files a record writes, as `naming.rs` works it
# out: a revision under the month and the day its author experienced and
# the first line of its message, and each file of content beneath that at
# the path it had in the folder. Decision 0019 is why the names are
# readable, and why the name a file is written under is the one it keeps.
#
# And one question `record` asks of timestamps before it writes: whether
# this machine's clock reads earlier than work the store already holds.

import Base
import ./text.bend as T
import ./folder.bend as Folder

# Characters
# ----------

# `char::is_whitespace`: Unicode's White_Space.
def is_space(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(Bool.and(U32.is_ge(x, 9), U32.is_le(x, 13)), Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 133), Bool.or(U32.is_eq(x, 160),
        Bool.or(U32.is_eq(x, 5760), Bool.or(Bool.and(U32.is_ge(x, 8192), U32.is_le(x, 8202)), Bool.or(U32.is_eq(x, 8232),
          Bool.or(U32.is_eq(x, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), U32.is_eq(x, 12288)))))))))))

# What a summary gives up to a space: the separators and the characters a
# filesystem reserves somewhere, and every control character.
def reserved(+c: Char) -> Bool:
  Bool.or(Folder.is_control(c), T.has_char("/\\:*?\"<>|", c))

# A summary's ends lose dots as well as space, so a name neither hides the
# file nor ends in a dot a filesystem would drop.
def spare(+c: Char) -> Bool:
  Bool.or(Char.is_eq(c, '.'), is_space(c))

def drop_spare(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      Bool.pick(String, spare(c), drop_spare(rest), SCon{c, rest})

def trim_spare(+s: String) -> String:
  String.reverse(drop_spare(String.reverse(drop_spare(s))))

def trim_end_spare(+s: String) -> String:
  String.reverse(drop_spare(String.reverse(s)))

def drop_space(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      Bool.pick(String, is_space(c), drop_space(rest), SCon{c, rest})

# `str::trim`: whitespace off both ends.
def trim_space(+s: String) -> String:
  String.reverse(drop_space(String.reverse(drop_space(s))))

# Summaries
# ---------

# `str::lines().next()`: up to the first newline, less a carriage return
# before it.
def first_line.go(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, rest}:
      Bool.pick(String, Char.is_eq(c, '\n'), SNil{}, SCon{c, first_line.go(rest)})

def first_line(+s: String) -> String:
  +line = first_line.go(s)
  Bool.pick(String, String.ends_with(line, "\r"), String.take(line, Nat.sub(String.length(line), 1n)), line)

def spaced(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, rest}:
      SCon{Bool.pick(Char, Bool.or(reserved(c), is_space(c)), ' ', c), spaced(rest)}

def nonempty(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      +later = nonempty(rest)
      Bool.pick(List<&2, String>, String.is_empty(x), later, x <> later)

# `split_whitespace`, joined by one space.
def collapsed(+s: String) -> String:
  String.join(nonempty(String.split(spaced(s), ' ')), " ")

# Everything before the last space, where there is one.
def before_last_space(s: String) -> Maybe<&2, String>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +rest}:
      Bool.pick(Maybe<&2, String>, Char.is_eq(c, ' '), Some{String.reverse(rest)}, before_last_space(rest))

def clip.cut(+cut: String, words: Maybe<&2, String>) -> String:
  match words:
    case Some{+w}:
      Bool.pick(String, String.is_empty(w), String.reverse(drop_space(String.reverse(cut))), w)
    case None{}:
      String.reverse(drop_space(String.reverse(cut)))

# Sixty characters at most, cut between words where a space allows it.
def clip(+s: String, +limit: Nat) -> String:
  Bool.pick(String, Nat.is_le(String.length(s), limit), s,
    clip.cut(String.take(s, limit), before_last_space(String.reverse(String.take(s, limit)))))

def SUMMARY_CHARS() -> Nat:
  60n

def CHANGE_CHARS() -> Nat:
  8n

def DIGEST_CHARS() -> Nat:
  12n

def summary.of(+change: String, +trimmed: String) -> String:
  Bool.pick(String, String.is_empty(trimmed), String.take(change, CHANGE_CHARS()), trimmed)

# The first line of a message as a name can carry it, or the change's
# first letters where nothing of it survives.
def summary(+message: String, +change: String) -> String:
  summary.of(change, trim_end_spare(clip(trim_spare(collapsed(first_line(message))), SUMMARY_CHARS())))

# `YYYY-MM/YYYY-MM-DD <summary>`: the month is a directory, and the name
# still says the date.
def compose(+when: String, +message: String, +change: String) -> String:
  String.take(when, 7n) ++ "/" ++ String.take(when, 10n) ++ " " ++ summary(message, change)

# A revision the store already holds, as far as its name goes.
type Named is Data:
  Named{when: String, message: String, change: String}

def base_of(n: Named) -> String:
  match n:
    case Named{+when, +message, +change}:
      compose(when, message, change)

def change_of(n: Named) -> String:
  match n:
    case Named{when, message, change}:
      change

def sharing_base(ns: List<&2, Named>, +base: String) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case n <> rest:
      Bool.or(String.eq(base_of(n), base), sharing_base(rest, base))

def sharing_change(ns: List<&2, Named>, +base: String, +change: String) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case +n <> rest:
      Bool.or(Bool.and(String.eq(base_of(n), base), String.eq(change_of(n), change)), sharing_change(rest, base, change))

def stem.of(+base: String, +change: String, +id: String, shares: Bool, same: Bool) -> String:
  Bool.pick(String, shares,
    Bool.pick(String, same, base ++ " " ++ String.take(change, CHANGE_CHARS()) ++ " " ++ String.take(id, DIGEST_CHARS()), base ++ " " ++ String.take(change, CHANGE_CHARS())),
    base)

# `stem_for`: the base, and where another revision already has it, the
# change's first letters too, and where that is the same change, the
# revision's own digest's.
def stem(+when: String, +message: String, +change: String, +id: String, +ns: List<&2, Named>) -> String:
  +base = compose(when, message, change)
  stem.of(base, change, id, sharing_base(ns, base), sharing_change(ns, base, change))

# Filing content
# --------------

def OPS() -> String:
  ".ops.txt"

# A path with every control character a space: the one thing a filename may
# not carry.
def scrubbed(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, rest}:
      SCon{Bool.pick(Char, Folder.is_control(c), ' ', c), scrubbed(rest)}

def last(+p: String) -> String:
  Maybe.default(&2, String, List.get(&2, String, List.reverse(&2, String, String.split(p, '/')), 0n), SNil{})

def head.of(parts: List<&2, String>) -> String:
  match parts:
    case Nil{}:
      SNil{}
    case +x <> +rest:
      String.join(List.reverse(&2, String, rest), "/") ++ Bool.pick(String, List.is_empty(&2, String, rest), SNil{}, "/")

# Everything up to and including the last `/`.
def head(+p: String) -> String:
  head.of(List.reverse(&2, String, String.split(p, '/')))

def member(xs: List<&2, String>, +x: String) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(String.eq(y, x), member(rest, x))

# The names a platform writes into every directory it touches, which
# `check` walks past, so content filed under one would never be seen.
def platform_name(+n: String) -> Bool:
  Bool.or(String.starts_with(n, "._"), member([".DS_Store", "Thumbs.db", "desktop.ini", ".localized", ".directory", "@eaDir"], n))

def unsuffixed(+s: String) -> String:
  Bool.pick(String, String.ends_with(s, OPS()), String.take(s, Nat.sub(String.length(s), String.length(OPS()))), s)

# A name made distinct by the digest's first letters, before the suffix
# where it is a document.
def suffixed(+name: String, +held: String, +document: Bool) -> String:
  +suffix = String.take(held, DIGEST_CHARS())
  Bool.pick(String, document, head(name) ++ unsuffixed(last(name)) ++ " " ++ suffix ++ OPS(), head(name) ++ last(name) ++ " " ++ suffix)

# One file of content: the digest that names it, where the file sat, and
# whether it is an operation document rather than a payload.
type Filing is Data:
  Filing{held: String, path: String, document: Bool}

# A filing and the name it would have if nothing else were filed.
type Wanted is Data:
  Wanted{held: String, name: String, document: Bool}

def wanted.of(+held: String, +path: String, +document: Bool) -> Wanted:
  +p = scrubbed(path)
  Wanted{held, Bool.pick(String, document, p ++ OPS(), Bool.pick(String, Bool.or(String.ends_with(last(p), OPS()), platform_name(last(p))), suffixed(p, held, False{}), p)), document}

def wanted(f: Filing) -> Wanted:
  match f:
    case Filing{+held, +path, +document}:
      wanted.of(held, path, document)

def wanted.key(w: Wanted) -> String:
  match w:
    case Wanted{held, name, d}:
      held ++ name

def wanted.name(w: Wanted) -> String:
  match w:
    case Wanted{held, name, d}:
      name

# Every directory a name sits in: each prefix before a `/`.
def prefixes.go(parts: List<&2, String>, +at: String) -> List<&2, String>:
  match parts:
    case Nil{}:
      Nil{}
    case +p <> Nil{}:
      Nil{}
    case +p <> rest:
      +here = Bool.pick(String, String.is_empty(at), p, at ++ "/" ++ p)
      here <> prefixes.go(rest, here)

def prefixes(+n: String) -> List<&2, String>:
  prefixes.go(String.split(n, '/'), SNil{})

def count(xs: List<&2, String>, +x: String) -> Nat:
  match xs:
    case Nil{}:
      0n
    case y <> rest:
      +later = count(rest, x)
      Bool.pick(Nat, String.eq(y, x), Nat.add(1n, later), later)

def settled(+dirs: List<&2, String>, +names: List<&2, String>, w: Wanted) -> T.Split:
  match w:
    case Wanted{+held, +name, +document}:
      T.Split{held, Bool.pick(String, member(dirs, name), held ++ Bool.pick(String, document, OPS(), SNil{}),
        Bool.pick(String, Nat.is_gt(count(names, name), 1n), suffixed(name, held, document), name))}

def settled_all(+dirs: List<&2, String>, +names: List<&2, String>, ws: List<&2, Wanted>) -> List<&2, T.Split>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      settled(dirs, names, w) <> settled_all(dirs, names, rest)

# `naming::filed`: each digest's name beneath the revision's stem. A name
# that is some other name's directory gives way to the digest, and a name
# two digests want gains the digest's first letters. Where one digest is
# filed twice the later name stands, as a map written in order would say.
def filed(fs: List<&2, Filing>) -> List<&2, T.Split>:
  +ws = List.sort(~Wanted, ~(a => b => String.is_le(wanted.key(a), wanted.key(b))), T.map(~Filing, ~Wanted, ~(f => wanted(f)), fs))
  +names = T.map(~Wanted, ~String, ~(w => wanted.name(w)), ws)
  +dirs = List.concat(&2, String, T.map(~String, ~List<&2, String>, ~(n => prefixes(n)), names))
  settled_all(dirs, names, ws)

# The name a digest is filed under, the last one `filed` gave it.
def filed_as(fs: List<&2, T.Split>, +held: String) -> String:
  match fs:
    case Nil{}:
      held
    case T.Split{+h, +n} <> rest:
      +later = filed_as(rest, held)
      Bool.pick(String, Bool.and(String.eq(h, held), String.eq(later, held)), n, later)

# Instants
# --------

def field(+s: String, +from: Nat, +len: Nat) -> Nat:
  Maybe.default(&2, Nat, Nat.read(String.take(String.drop(s, from), len)), 0n)

def leap(+y: Nat) -> Bool:
  Bool.and(Nat.is_eq(Nat.mod(y, 4n), 0n), Bool.or(Bool.not(Nat.is_eq(Nat.mod(y, 100n), 0n)), Nat.is_eq(Nat.mod(y, 400n), 0n)))

# Days before the first of a year, counted from year zero's.
def days_before_year(+y: Nat) -> Nat:
  Nat.sub(Nat.add(Nat.add(Nat.mul(365n, y), Nat.div(Nat.add(y, 3n), 4n)), Nat.div(Nat.add(y, 399n), 400n)), Nat.div(Nat.add(y, 99n), 100n))

def days_before_month(+y: Nat, +m: Nat) -> Nat:
  Nat.add(Maybe.default(&2, Nat, List.get(&2, Nat, [0n, 31n, 59n, 90n, 120n, 151n, 181n, 212n, 243n, 273n, 304n, 334n], Nat.sub(m, 1n)), 0n),
    Bool.pick(Nat, Bool.and(Nat.is_gt(m, 2n), leap(y)), 1n, 0n))

# A timestamp as seconds from an origin a day before year zero, which no
# offset can reach below: what `record` compares to see a clock that is
# behind the store. Only the order means anything.
def instant(+w: String) -> Nat:
  +y = field(w, 0n, 4n)
  +days = Nat.add(Nat.add(days_before_year(y), days_before_month(y, field(w, 5n, 2n))), Nat.sub(field(w, 8n, 2n), 1n))
  +local = Nat.add(Nat.mul(days, 86400n), Nat.add(Nat.add(Nat.mul(field(w, 11n, 2n), 3600n), Nat.mul(field(w, 14n, 2n), 60n)), field(w, 17n, 2n)))
  +offset = Nat.add(Nat.mul(field(w, 20n, 2n), 3600n), Nat.mul(field(w, 23n, 2n), 60n))
  Bool.pick(Nat, String.starts_with(String.drop(w, 19n), "-"), Nat.add(Nat.add(local, 86400n), offset), Nat.sub(Nat.add(local, 86400n), offset))

# The latest of some timestamps, the last of several at one instant, as
# `max_by_key` keeps it.
def newest(ws: List<&2, String>, +best: Maybe<&2, String>) -> Maybe<&2, String>:
  match ws:
    case Nil{}:
      best
    case +w <> rest:
      newest(rest, Bool.pick(Maybe<&2, String>, Nat.is_ge(instant(w), Maybe.default(&2, Nat, Maybe.map(&2, String, Nat, b => instant(b), best), 0n)), Some{w}, best))

# What the laws ask of a name
# ---------------------------

# Whether every character of a string passes a test.
def every(~p: Char -> Bool, s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, rest}:
      Bool.and(p(c), every(~p, rest))

# A name holding nothing a filesystem reserves, and no control character.
def plain(s: String) -> Bool:
  every(~(c => Bool.not(reserved(c))), s)

# A name that is the directory `month` and one plain name inside it
# (`LAWS.a_revision_is_filed_under_its_month`).
def in_month(month: String, s: String) -> Bool:
  match month s:
    case SNil{} SNil{}:
      False{}
    case SNil{} SCon{c, rest}:
      Bool.and(Char.is_eq(c, '/'), plain(rest))
    case SCon{m, ms} SNil{}:
      False{}
    case SCon{m, ms} SCon{c, rest}:
      Bool.and(Char.is_eq(c, m), in_month(ms, rest))

# Whether a string begins with a dot or a space.
def spare_start(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, rest}:
      spare(c)

# A summary's ends (`LAWS.a_summary_gives_up_its_ends`): it neither begins
# nor ends with a dot or a space.
def trimmed(+s: String) -> Bool:
  Bool.not(Bool.or(spare_start(s), spare_start(String.reverse(s))))

# A name with no control character in it, which is what a filed path is
# scrubbed of (`LAWS.content_is_filed_under_a_name_a_filesystem_holds`).
def controlless(s: String) -> Bool:
  every(~(c => Bool.not(Folder.is_control(c))), s)

def show_split(s: T.Split) -> String:
  match s:
    case T.Split{a, b}:
      a ++ "=" ++ b

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(compose("2025-08-19T00:47:11-06:00", "File  docs/README.md  under docs\nmore", "qpvuntsmwlrkzxonmvtplsyq"))
    IO.print(compose("2025-08-19T00:47:11-06:00", "Fix: the parser? <yes> \"quoted\" | piped *star*\n", "qpvuntsmwlrkzxonmvtplsyq"))
    IO.print(compose("2025-08-19T00:47:11-06:00", "Say what the parser refuses...\n", "qpvuntsmwlrkzxonmvtplsyq"))
    IO.print(compose("2025-08-19T00:47:11-06:00", "?*|\n", "qpvuntsmwlrkzxonmvtplsyq"))
    IO.print(compose("2025-08-19T00:47:11-06:00", "one two three four five six seven eight nine ten eleven twelve thirteen\n", "qpvuntsmwlrkzxonmvtplsyq"))
    IO.print(compose("2025-08-19T00:47:11-06:00", ".hidden would be a hidden file\n", "qpvuntsmwlrkzxonmvtplsyq"))
    IO.print(String.join(T.map(~T.Split, ~String, ~(s => show_split(s)), filed([Filing{"bb", "a/b.txt", True{}}, Filing{"aa", "a", False{}}, Filing{"cc", "x/.DS_Store", False{}}, Filing{"dd", "y", False{}}, Filing{"ee", "y", False{}}])), " | "))
    IO.print(Nat.show(instant("2026-01-02T03:04:05+01:00")) ++ " " ++ Nat.show(instant("2026-01-02T02:04:05+00:00")) ++ " " ++ Nat.show(instant("2026-01-01T21:04:05-05:00")))
