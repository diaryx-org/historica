# The revision document — who recorded what, when, and why — and the
# history a set of them makes: a Merkle DAG that merges by set union, with
# explicit parents and explicit supersession, and no timestamp in identity.

import Base
import ./text.bend as T
import ./ident.bend as Id
import ./utf8.bend as Utf8
import ./words.bend as W

# The model
# ---------

type Header is Data:
  Header{key: String, value: String}

# A parsed document. The causal headers are fields; the file facts — add,
# move, mode, drop, edit, text, bytes, link — and a tool's own headers stay
# as headers, in the order the document must state them.
type Rev is Data:
  Rev{change: String, parents: List<&2, String>, supersedes: List<&2, String>,
      author: String, when: String, revised_by: Maybe<&2, String>, revised: Maybe<&2, String>,
      facts: List<&2, Header>, message: String}

# Keys
# ----

# What a header is, decided before the walk reaches it.
type Key is Data:
  Key.Change{}
  Key.Parent{}
  Key.Supersedes{}
  Key.Author{}
  Key.When{}
  Key.RevisedBy{}
  Key.Revised{}
  Key.Add{}
  Key.Move{}
  Key.Mode{}
  Key.Drop{}
  Key.Edit{}
  Key.Text{}
  Key.Bytes{}
  Key.Link{}
  Key.Extension{}
  Key.Unknown{}

# Where a key sits in the fixed order. A tool's own headers share the last
# rank, and the dot is what says a header is one.
def rank(k: Key) -> Nat:
  match k:
    case Key.Change{}:
      0n
    case Key.Parent{}:
      1n
    case Key.Supersedes{}:
      2n
    case Key.Author{}:
      3n
    case Key.When{}:
      4n
    case Key.RevisedBy{}:
      5n
    case Key.Revised{}:
      6n
    case Key.Add{}:
      7n
    case Key.Move{}:
      8n
    case Key.Mode{}:
      9n
    case Key.Drop{}:
      10n
    case Key.Edit{}:
      11n
    case Key.Text{}:
      12n
    case Key.Bytes{}:
      13n
    case Key.Link{}:
      14n
    case Key.Extension{}:
      15n
    case Key.Unknown{}:
      99n

# Whether a key may appear more than once.
def repeatable(k: Key) -> Bool:
  match k:
    case Key.Change{}:
      False{}
    case Key.Author{}:
      False{}
    case Key.When{}:
      False{}
    case Key.RevisedBy{}:
      False{}
    case Key.Revised{}:
      False{}
    case Key.Unknown{}:
      False{}
    case _:
      True{}

def is_key_char(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(Bool.and(U32.is_ge(x, 97), U32.is_le(x, 122)), Bool.or(U32.is_eq(x, 45), U32.is_eq(x, 46)))

def no_empty_part(parts: List<&2, String>) -> Bool:
  match parts:
    case Nil{}:
      True{}
    case p <> rest:
      Bool.and(Bool.not(String.is_empty(p)), no_empty_part(rest))

# Lowercase letters, hyphens and dots, with no empty part between dots.
def shaped_key(+k: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(k)), Bool.and(T.all_chars(~is_key_char, k), no_empty_part(String.split(k, '.'))))

def classify.named(+k: String, dotted: Bool) -> Key:
  match dotted:
    case True{}:
      Key.Extension{}
    case False{}:
      Key.Unknown{}

# The keys the format names, in rank order. `classify` walks the table
# rather than matching the key against fifteen literals, so a proof can say
# which key a header is from the comparison that chose it
# (`revision_lemmas.classify_named`).
type Named is Data:
  Named{name: String, key: Key}

def keys() -> List<&2, Named>:
  [Named{"change", Key.Change{}}, Named{"parent", Key.Parent{}}, Named{"supersedes", Key.Supersedes{}},
   Named{"author", Key.Author{}}, Named{"when", Key.When{}}, Named{"revised-by", Key.RevisedBy{}},
   Named{"revised", Key.Revised{}}, Named{"add", Key.Add{}}, Named{"move", Key.Move{}}, Named{"mode", Key.Mode{}},
   Named{"drop", Key.Drop{}}, Named{"edit", Key.Edit{}}, Named{"text", Key.Text{}}, Named{"bytes", Key.Bytes{}},
   Named{"link", Key.Link{}}]

def classify.go(table: List<&2, Named>, +k: String) -> Key:
  match table:
    case Nil{}:
      classify.named(k, T.has_char(k, '.'))
    case Named{name, key} <> rest:
      Bool.pick(Key, T.same(k, name), key, classify.go(rest, k))

def classify(+k: String) -> Key:
  classify.go(keys(), k)

def classify_head(hs: List<&2, Header>) -> Key:
  match hs:
    case Nil{}:
      Key.Unknown{}
    case Header{k, v} <> rest:
      classify(k)

# Values
# ------

def is_control(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(U32.is_lt(x, 32), Bool.and(U32.is_ge(x, 127), U32.is_lt(x, 160)))

def is_digit_char(c: Char) -> Bool:
  Char.is_digit(c)

# A timestamp is exactly `2025-08-19T09:02:40-06:00`: RFC 3339 with an
# explicit signed offset, and `Z` is not a spelling this format has.
def timestamp.shape(s: String, tpl: String) -> Bool:
  match s tpl:
    case SNil{} SNil{}:
      True{}
    case SCon{c, ct} SCon{'d', tt}:
      Bool.and(Char.is_digit(c), timestamp.shape(ct, tt))
    case SCon{+c, ct} SCon{'s', tt}:
      Bool.and(Bool.or(Char.is_eq(c, '+'), Char.is_eq(c, '-')), timestamp.shape(ct, tt))
    case SCon{c, ct} SCon{t, tt}:
      Bool.and(Char.is_eq(c, t), timestamp.shape(ct, tt))
    case _ _:
      False{}

def field(+s: String, from: Nat, len: Nat) -> Nat:
  Maybe.default(&2, Nat, Nat.read(String.take(String.drop(s, from), len)), 0n)

def within(+s: String, from: Nat, len: Nat, lo: Nat, hi: Nat) -> Bool:
  +n = field(s, from, len)
  Bool.and(Nat.is_ge(n, lo), Nat.is_le(n, hi))

# The days in a month of the Gregorian calendar, leap years included.
def is_leap(+year: Nat) -> Bool:
  Bool.and(Nat.is_eq(Nat.mod(year, 4n), 0n), Bool.or(Bool.not(Nat.is_eq(Nat.mod(year, 100n), 0n)), Nat.is_eq(Nat.mod(year, 400n), 0n)))

def days_in(+year: Nat, month: Nat) -> Nat:
  match month:
    case 2n:
      Bool.pick(Nat, is_leap(year), 29n, 28n)
    case 4n:
      30n
    case 6n:
      30n
    case 9n:
      30n
    case 11n:
      30n
    case _:
      31n

# `-00:00` is refused: RFC 3339 spells an unknown offset that way, and this
# format writes `+00:00` for UTC.
def unknown_offset(+s: String) -> Bool:
  String.ends_with(s, "-00:00")

def is_timestamp.dated(+s: String, +month: Nat) -> Bool:
  Bool.and(Bool.and(Nat.is_ge(month, 1n), Nat.is_le(month, 12n)), within(s, 8n, 2n, 1n, days_in(field(s, 0n, 4n), month)))

def is_timestamp(+s: String) -> Bool:
  Bool.and(timestamp.shape(s, "dddd-dd-ddTdd:dd:ddsdd:dd"),
    Bool.and(is_timestamp.dated(s, field(s, 5n, 2n)),
      Bool.and(Bool.and(within(s, 11n, 2n, 0n, 23n), within(s, 14n, 2n, 0n, 59n)),
        Bool.and(within(s, 17n, 2n, 0n, 59n), Bool.and(Bool.and(within(s, 20n, 2n, 0n, 23n), within(s, 23n, 2n, 0n, 59n)), Bool.not(unknown_offset(s)))))))

# A path is relative, with no empty component and no `.` or `..`, and no
# leading or trailing space, and no backslash. (Unicode normal form C is not
# checked here.)
#
# One walk decides it: `part` is what the component so far is — nothing, a
# `.`, a `..`, or a name — and a component is closed at each `/` and at the
# end, where only a name will do.
type Part is Data:
  Part.Empty{}
  Part.Dot{}
  Part.Dots{}
  Part.Name{}

def part.named(part: Part) -> Bool:
  match part:
    case Part.Name{}:
      True{}
    case _:
      False{}

def part.next(part: Part, +c: Char) -> Part:
  match part:
    case Part.Empty{}:
      Bool.pick(Part, Char.is_eq(c, '.'), Part.Dot{}, Part.Name{})
    case Part.Dot{}:
      Bool.pick(Part, Char.is_eq(c, '.'), Part.Dots{}, Part.Name{})
    case _:
      Part.Name{}

def is_path.go(p: String, part: Part, last: Bool) -> Bool:
  match p:
    case SNil{}:
      Bool.and(part.named(part), Bool.not(last))
    case SCon{'/', t}:
      Bool.and(part.named(part), is_path.go(t, Part.Empty{}, False{}))
    case SCon{'\\', t}:
      False{}
    case SCon{+c, t}:
      is_path.go(t, part.next(part, c), Char.is_eq(c, ' '))

def is_path(p: String) -> Bool:
  match p:
    case SCon{' ', t}:
      False{}
    case _:
      is_path.go(p, Part.Empty{}, False{})

# A value that is a file ID and one more thing, cut at the first space.
def entry(v: String) -> Maybe<&2, T.Split>:
  T.split_once(v)

def entry_ok(~second: String -> Bool, cut: Maybe<&2, T.Split>) -> Bool:
  match cut:
    case None{}:
      False{}
    case Some{T.Split{file, rest}}:
      Bool.and(Id.is_assigned(file), second(rest))

def is_mode(m: String) -> Bool:
  match m:
    case "plain":
      True{}
    case "executable":
      True{}
    case _:
      False{}

def link_target_ok.of(t: String, named: Maybe<&2, String>) -> Bool:
  match named:
    case None{}:
      Bool.not(String.is_empty(t))
    case Some{file}:
      Id.is_assigned(file)

def link_target_ok(+t: String) -> Bool:
  link_target_ok.of(t, T.strip_prefix(t, "file:"))

# Whether a value has the shape its key demands.
def value_ok(k: Key, +v: String) -> Bool:
  match k:
    case Key.Change{}:
      Id.is_assigned(v)
    case Key.Parent{}:
      Id.is_digest(v)
    case Key.Supersedes{}:
      Id.is_digest(v)
    case Key.Author{}:
      True{}
    case Key.When{}:
      is_timestamp(v)
    case Key.RevisedBy{}:
      True{}
    case Key.Revised{}:
      is_timestamp(v)
    case Key.Add{}:
      entry_ok(~(p => is_path(p)), entry(v))
    case Key.Move{}:
      entry_ok(~(p => is_path(p)), entry(v))
    case Key.Mode{}:
      entry_ok(~is_mode, entry(v))
    case Key.Drop{}:
      Id.is_assigned(v)
    case Key.Edit{}:
      entry_ok(~(d => Id.is_digest(d)), entry(v))
    case Key.Text{}:
      entry_ok(~(d => Id.is_digest(d)), entry(v))
    case Key.Bytes{}:
      entry_ok(~(d => Id.is_digest(d)), entry(v))
    case Key.Link{}:
      entry_ok(~(t => link_target_ok(t)), entry(v))
    case Key.Extension{}:
      True{}
    case Key.Unknown{}:
      False{}

# Order
# -----

# The rules between one header and the one before it: keys in rank order, a
# key repeated only if it may be, and repeated facts sorted — by value, or
# by key for a tool's own headers — with nothing stated twice.
def order.sorted(+key: String, c: Cmp) -> Maybe<&2, String>:
  match c:
    case EQ{}:
      Some{"the header `" ++ key ++ "` states one fact twice"}
    case LT{}:
      Some{"the header `" ++ key ++ "` is out of order among its repeats"}
    case GT{}:
      None{}

def order.same_rank.of(+key: String, +value: String, +last_key: String, +last_value: String, repeats: Bool, extension: Bool) -> Maybe<&2, String>:
  match repeats:
    case False{}:
      Some{"the header `" ++ key ++ "` is repeated"}
    case True{}:
      order.sorted(key, Bool.pick(Cmp, extension, Id.order(key, last_key), Id.order(value, last_value)))

def order.same_rank(+k: Key, +key: String, +value: String, +last_key: String, +last_value: String) -> Maybe<&2, String>:
  order.same_rank.of(key, value, last_key, last_value, repeatable(k), Nat.is_eq(rank(k), 15n))

def order.of(k: Key, +key: String, +value: String, last: Maybe<&2, Header>, last_rank: Nat, c: Cmp) -> Maybe<&2, String>:
  match last c:
    case None{} _:
      None{}
    case Some{Header{lk, lv}} LT{}:
      Some{"the header `" ++ key ++ "` comes after `" ++ lk ++ "`"}
    case Some{Header{lk, lv}} GT{}:
      None{}
    case Some{Header{lk, lv}} EQ{}:
      order.same_rank(k, key, value, lk, lv)

def order(+k: Key, +key: String, +value: String, last: Maybe<&2, Header>, +last_rank: Nat) -> Maybe<&2, String>:
  order.of(k, key, value, last, last_rank, Nat.cmp(rank(k), last_rank))

def line_error(at: Nat, e: Maybe<&2, String>) -> Maybe<&2, String>:
  match e:
    case None{}:
      None{}
    case Some{msg}:
      Some{"line " ++ Nat.show(at) ++ ": " ++ msg}

# The first complaint about a header, given what it is.
def check(+k: Key, +key: String, +value: String, last: Maybe<&2, Header>, last_rank: Nat) -> Maybe<&2, String>:
  match k:
    case Key.Unknown{}:
      Some{"an unknown header `" ++ key ++ "`"}
    case _:
      Maybe.or(&2, String, order(k, key, value, last, last_rank),
        Bool.pick(Maybe<&2, String>, value_ok(k, value), None{}, Some{"a malformed `" ++ key ++ "` value: " ++ value}))

# Every header in turn. `k` is what the head of `hs` is.
def validate(hs: List<&2, Header>, +k: Key, last: Maybe<&2, Header>, last_rank: Nat, +at: Nat) -> Maybe<&2, String>:
  match hs:
    case Nil{}:
      None{}
    case Header{+key, +value} <> +rest:
      Maybe.or(&2, String, line_error(at, check(k, key, value, last, last_rank)),
        validate(rest, classify_head(rest), Some{Header{key, value}}, rank(k), 1n+at))

# Extraction
# ----------

def keep(b: Bool, x: String, rest: List<&2, String>) -> List<&2, String>:
  match b:
    case True{}:
      x <> rest
    case False{}:
      rest

def keep_header(b: Bool, x: Header, rest: List<&2, Header>) -> List<&2, Header>:
  match b:
    case True{}:
      x <> rest
    case False{}:
      rest

def value_of(hs: List<&2, Header>, +key: String) -> Maybe<&2, String>:
  match hs:
    case Nil{}:
      None{}
    case Header{+k, v} <> rest:
      Bool.pick(Maybe<&2, String>, String.eq(k, key), Some{v}, value_of(rest, key))

def values_of(hs: List<&2, Header>, +key: String) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case Header{+k, v} <> rest:
      keep(String.eq(k, key), v, values_of(rest, key))

# The file each value under a key names, which is its first word.
def files_of(hs: List<&2, Header>, +key: String) -> List<&2, String>:
  T.map(~String, ~String, ~(v => T.word(v)), values_of(hs, key))

# The headers that are facts about files, or a tool's own.
def facts_of(hs: List<&2, Header>) -> List<&2, Header>:
  match hs:
    case Nil{}:
      Nil{}
    case Header{+k, v} <> rest:
      keep_header(Nat.is_ge(rank(classify(k)), 7n), Header{k, v}, facts_of(rest))

def member(xs: List<&2, String>, +x: String) -> Bool:
  List.contains(~String, ~(a => b => String.eq(a, b)), xs, x)

# The strings of `xs` that are not in `ys`.
def without(xs: List<&2, String>, +ys: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      keep(Bool.not(member(ys, x)), x, without(rest, ys))

# `disjoint`, `subset` and `unique` are asked of a revision's file lists,
# and a revision that adds a folder names thousands of files, so each walks
# one list against a `Set` of the other — a trie over the name — rather than
# against the list itself, which was the two lengths multiplied. `r` is the
# answer for the item before, with the set handed back.
def disjoint.go(xs: List<&2, String>, r: Set() & Bool) -> Bool:
  match xs r:
    case _ Tuple{s, True{}}:
      False{}
    case Nil{} Tuple{s, False{}}:
      True{}
    case x <> rest Tuple{s, False{}}:
      disjoint.go(rest, Set.has(s, x))

def disjoint.of(xs: List<&2, String>, ys: List<&2, String>) -> Bool:
  disjoint.go(xs, (Set.from_list(ys), False{}))

# The set is built from the shorter list, since disjointness is symmetric
# and most of a revision's file lists are empty.
def disjoint.by(xs: List<&2, String>, ys: List<&2, String>, ys_shorter: Bool) -> Bool:
  match ys_shorter:
    case True{}:
      disjoint.of(xs, ys)
    case False{}:
      disjoint.of(ys, xs)

def disjoint(+xs: List<&2, String>, +ys: List<&2, String>) -> Bool:
  disjoint.by(xs, ys, Nat.is_le(List.length(&2, String, ys), List.length(&2, String, xs)))

def subset.go(xs: List<&2, String>, r: Set() & Bool) -> Bool:
  match xs r:
    case _ Tuple{s, False{}}:
      False{}
    case Nil{} Tuple{s, True{}}:
      True{}
    case x <> rest Tuple{s, True{}}:
      subset.go(rest, Set.has(s, x))

def subset(xs: List<&2, String>, +ys: List<&2, String>) -> Bool:
  subset.go(xs, (Set.from_list(ys), True{}))

# `x` is the item just looked for and not yet added; it joins the set once
# the answer says it was not there.
def unique.go(xs: List<&2, String>, +x: String, r: Set() & Bool) -> Bool:
  match xs r:
    case _ Tuple{s, True{}}:
      False{}
    case Nil{} Tuple{s, False{}}:
      True{}
    case +y <> rest Tuple{s, False{}}:
      unique.go(rest, y, Set.has(Set.add(s, x), y))

def unique(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      unique.go(rest, x, Set.has(Set.new(), x))

# Assembly
# --------

def required(v: Maybe<&2, String>, key: String) -> Result<&2, &2, String, String>:
  match v:
    case None{}:
      Fail{"the header `" ++ key ++ "` is missing"}
    case Some{s}:
      Done{s}

def ensure(ok: Bool, msg: String) -> Result<&2, &2, String, Unit>:
  Bool.pick(Result<&2, &2, String, Unit>, ok, Done{Unit{}}, Fail{msg})

def maybe_eq(a: Maybe<&2, String>, +b: String) -> Bool:
  match a:
    case None{}:
      False{}
    case Some{s}:
      String.eq(s, b)

# A file may not be stated twice under one key, and two facts that cannot
# both be true of one file may not both be stated.
def facts_ok(+hs: List<&2, Header>) -> Result<&2, &2, String, Unit>:
  +added = files_of(hs, "add")
  +moved = files_of(hs, "move")
  +dropped = files_of(hs, "drop")
  +edited = files_of(hs, "edit")
  +modes = files_of(hs, "mode")
  +bytes = files_of(hs, "bytes")
  +links = files_of(hs, "link")
  +texts = files_of(hs, "text")
  do Result<&2, &2, String, Unit>:
    ensure(Bool.and(Bool.and(unique(added), unique(moved)), Bool.and(Bool.and(unique(dropped), unique(edited)), Bool.and(Bool.and(unique(modes), unique(bytes)), Bool.and(unique(links), unique(texts))))), "a file is stated twice under one key")
    ensure(Bool.and(disjoint(added, moved), Bool.and(disjoint(added, dropped), disjoint(added, edited))), "a file is added and also moved, dropped or edited")
    ensure(disjoint(moved, dropped), "a file is moved and also dropped")
    ensure(Bool.and(Bool.and(disjoint(dropped, edited), disjoint(dropped, bytes)), Bool.and(disjoint(dropped, modes), disjoint(dropped, links))), "a file is dropped and also given content, a mode or a target")
    ensure(subset(texts, added), "a `text` names a file this revision does not add")
    ensure(Bool.and(Bool.and(disjoint(edited, texts), disjoint(edited, bytes)), Bool.and(Bool.and(disjoint(edited, links), disjoint(texts, bytes)), Bool.and(disjoint(texts, links), disjoint(bytes, links)))), "a file's content is stated twice, in two models")

# What `assemble` checks once the three required headers are found.
def assemble.checks(+hs: List<&2, Header>, +author: String) -> Result<&2, &2, String, Unit>:
  +supersedes = values_of(hs, "supersedes")
  +revised = value_of(hs, "revised")
  +revised_by = value_of(hs, "revised-by")
  do Result<&2, &2, String, Unit>:
    ensure(Bool.or(List.is_empty(&2, String, supersedes), Maybe.is_some(&2, String, revised)), "a revision that supersedes must say when it was revised")
    ensure(Bool.or(Bool.not(List.is_empty(&2, String, supersedes)), Bool.and(Maybe.is_none(&2, String, revised), Maybe.is_none(&2, String, revised_by))), "`revised` and `revised-by` need a `supersedes`")
    ensure(Bool.not(maybe_eq(revised_by, author)), "`revised-by` names the author, which says nothing")
    facts_ok(hs)

def assemble.checked(ok: Result<&2, &2, String, Unit>, r: Rev) -> Result<&2, &2, String, Rev>:
  match ok:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      Done{r}

def assemble.when(+hs: List<&2, Header>, message: String, change: String, +author: String, w: Result<&2, &2, String, String>) -> Result<&2, &2, String, Rev>:
  match w:
    case Fail{e}:
      Fail{e}
    case Done{when}:
      assemble.checked(assemble.checks(hs, author), Rev{change, values_of(hs, "parent"), values_of(hs, "supersedes"), author, when, value_of(hs, "revised-by"), value_of(hs, "revised"), facts_of(hs), message})

def assemble.author(+hs: List<&2, Header>, message: String, change: String, a: Result<&2, &2, String, String>) -> Result<&2, &2, String, Rev>:
  match a:
    case Fail{e}:
      Fail{e}
    case Done{author}:
      assemble.when(hs, message, change, author, required(value_of(hs, "when"), "when"))

def assemble.change(+hs: List<&2, Header>, message: String, c: Result<&2, &2, String, String>) -> Result<&2, &2, String, Rev>:
  match c:
    case Fail{e}:
      Fail{e}
    case Done{change}:
      assemble.author(hs, message, change, required(value_of(hs, "author"), "author"))

# One def per stage, each taking the last stage's result, so that a proof
# opens the assembly a `match` at a time (`revision_lemmas.assembled`).
def assemble(+hs: List<&2, Header>, message: String) -> Result<&2, &2, String, Rev>:
  assemble.change(hs, message, required(value_of(hs, "change"), "change"))

# Parsing
# -------

# The message is the rest of the file, verbatim, newline or no newline.
def unlines(ls: List<&2, T.Line>) -> String:
  match ls:
    case Nil{}:
      SNil{}
    case T.Line{t, n} <> rest:
      t ++ Bool.pick(String, n, "\n", SNil{}) ++ unlines(rest)

# What one walk over a header's value finds: whether it starts or ends with
# a space, and whether it holds a control character.
type Scan is Data:
  Scan{padded: Bool, control: Bool}

def scan.go(s: String, last: Bool, control: Bool, first: Bool) -> Scan:
  match s:
    case SNil{}:
      Scan{Bool.or(first, last), control}
    case SCon{+c, t}:
      scan.go(t, Char.is_eq(c, ' '), Bool.or(control, is_control(c)), first)

def scan(s: String) -> Scan:
  match s:
    case SNil{}:
      Scan{False{}, False{}}
    case SCon{+c, t}:
      scan.go(t, Char.is_eq(c, ' '), is_control(c), Char.is_eq(c, ' '))

def header_of.scanned(+k: String, v: String, sc: Scan) -> Result<&2, &2, String, Header>:
  match sc:
    case Scan{padded, control}:
      do Result<&2, &2, String, Header>:
        ensure(Bool.not(padded), "the header `" ++ k ++ "` has a padded value")
        ensure(Bool.not(control), "the header `" ++ k ++ "` holds a control character")
        return Header{k, v}

def header_of(+t: String, cut: Maybe<&2, T.Split>) -> Result<&2, &2, String, Header>:
  match cut:
    case None{}:
      Fail{"the header `" ++ t ++ "` has no value"}
    case Some{T.Split{+k, +v}}:
      do Result<&2, &2, String, Header>:
        ensure(shaped_key(k), "a malformed key `" ++ k ++ "`")
        ensure(Bool.not(String.is_empty(v)), "the header `" ++ k ++ "` has no value")
        header_of.scanned(k, v, scan(v))

# The headers and the message. Headers run to the first blank line, after
# which the message is everything, and must be something.
type Split is Data:
  Headers{headers: List<&2, Header>, message: String}

def head_header(ls: List<&2, T.Line>) -> Result<&2, &2, String, Header>:
  match ls:
    case T.Line{+t, True{}} <> rest:
      header_of(t, T.split_once(t))
    case _:
      Done{Header{SNil{}, SNil{}}}

# `h` is the head of `ls` read as a header, decided before the walk.
def headers.go(ls: List<&2, T.Line>, h: Result<&2, &2, String, Header>, +at: Nat, acc: List<&2, Header>) -> Result<&2, &2, String, Split>:
  match ls h:
    case Nil{} _:
      Done{Headers{List.reverse(&2, Header, acc), SNil{}}}
    case T.Line{SNil{}, term} <> Nil{} _:
      Fail{"line " ++ Nat.show(at) ++ ": a blank line with no message after it"}
    case T.Line{SNil{}, term} <> rest _:
      Done{Headers{List.reverse(&2, Header, acc), unlines(rest)}}
    case T.Line{t, False{}} <> rest _:
      Fail{"line " ++ Nat.show(at) ++ ": unterminated line"}
    case T.Line{t, True{}} <> rest Fail{e}:
      Fail{"line " ++ Nat.show(at) ++ ": " ++ e}
    case T.Line{t, True{}} <> +rest Done{hd}:
      headers.go(rest, head_header(rest), 1n+at, hd <> acc)

def parse.validated(hs: List<&2, Header>, message: String, complaint: Maybe<&2, String>) -> Result<&2, &2, String, Rev>:
  match complaint:
    case Some{e}:
      Fail{e}
    case None{}:
      assemble(hs, message)

def parse.split(s: Result<&2, &2, String, Split>) -> Result<&2, &2, String, Rev>:
  match s:
    case Fail{e}:
      Fail{e}
    case Done{Headers{+hs, message}}:
      parse.validated(hs, message, validate(hs, classify_head(hs), None{}, 0n, 2n))

def parse.head(+t: String, historica: Bool, +rest: List<&2, T.Line>) -> Result<&2, &2, String, Rev>:
  match historica:
    case True{}:
      parse.split(headers.go(rest, head_header(rest), 2n, Nil{}))
    case False{}:
      Bool.pick(Result<&2, &2, String, Rev>, String.starts_with(t, "historica-"), Fail{"line 1: an unknown version `" ++ t ++ "`, likely a newer historica"}, Fail{"line 1: not a historica document"})

def parse.preamble(ls: List<&2, T.Line>) -> Result<&2, &2, String, Rev>:
  match ls:
    case T.Line{+t, term} <> rest:
      parse.head(t, Bool.and(term, T.same(t, "historica")), rest)
    case Nil{}:
      Fail{"an empty document"}

# The Rust tool's words
# ---------------------
#
# The Rust tool reads a revision two ways (decision 0061): opening a store
# reads each document's shape and its `change`, `parent` and `supersedes`
# (`format::revision`), and whatever asks what a revision did reads it
# whole (`RevisionDocument::parse`), splitting every header before it
# weighs any. Each is read over again here in its own order, for what the
# parser above does not say as the Rust tool does: which line a refused
# document is refused on, and why. The parser above decides whether a
# document is accepted; these only word a refusal.

# A header as `split_header` leaves it.
type WH is Data:
  WH{at: Nat, key: String, value: String}

def w.split.value(+at: Nat, +key: String, +value: String) -> Result<&2, &2, String, WH>:
  Bool.pick(Result<&2, &2, String, WH>, Bool.not(shaped_key(key)), Fail{W.at(at, W.malformed_key(key))},
  Bool.pick(Result<&2, &2, String, WH>, String.is_empty(value), Fail{W.at(at, W.empty_value())},
  Bool.pick(Result<&2, &2, String, WH>, Bool.or(String.starts_with(value, " "), String.ends_with(value, " ")), Fail{W.at(at, W.padded_value())},
  Bool.pick(Result<&2, &2, String, WH>, List.any(~&2, ~Char, ~is_control, String.to_list(value)), Fail{W.at(at, W.control_character())},
    Done{WH{at, key, value}}))))

# `split_header`: a key, one space, and a value.
def w.split(+at: Nat, cut: Maybe<&2, T.Split>) -> Result<&2, &2, String, WH>:
  match cut:
    case None{}:
      Fail{W.at(at, W.empty_value())}
    case Some{T.Split{+k, +v}}:
      w.split.value(at, k, v)

# `rank`: where a key may appear in the fixed order.
def w.rank(+key: String) -> Maybe<&2, Nat>:
  Bool.pick(Maybe<&2, Nat>, String.eq(key, "change"), Some{0n},
  Bool.pick(Maybe<&2, Nat>, String.eq(key, "parent"), Some{1n},
  Bool.pick(Maybe<&2, Nat>, String.eq(key, "supersedes"), Some{2n},
  Bool.pick(Maybe<&2, Nat>, String.eq(key, "author"), Some{3n},
  Bool.pick(Maybe<&2, Nat>, String.eq(key, "when"), Some{4n},
  Bool.pick(Maybe<&2, Nat>, String.eq(key, "revised-by"), Some{5n},
  Bool.pick(Maybe<&2, Nat>, String.eq(key, "revised"), Some{6n},
  Bool.pick(Maybe<&2, Nat>, String.eq(key, "add"), Some{7n},
  Bool.pick(Maybe<&2, Nat>, String.eq(key, "move"), Some{8n},
  Bool.pick(Maybe<&2, Nat>, String.eq(key, "mode"), Some{9n},
  Bool.pick(Maybe<&2, Nat>, String.eq(key, "drop"), Some{10n},
  Bool.pick(Maybe<&2, Nat>, String.eq(key, "edit"), Some{11n},
  Bool.pick(Maybe<&2, Nat>, String.eq(key, "text"), Some{12n},
  Bool.pick(Maybe<&2, Nat>, String.eq(key, "bytes"), Some{13n},
  Bool.pick(Maybe<&2, Nat>, String.eq(key, "link"), Some{14n},
  Bool.pick(Maybe<&2, Nat>, T.has_char(key, '.'), Some{15n}, None{}))))))))))))))))

def w.repeatable(+r: Nat) -> Bool:
  Bool.or(Bool.or(Nat.is_eq(r, 1n), Nat.is_eq(r, 2n)), Nat.is_ge(r, 7n))

# The header before this one: its rank, its key and its value.
type WPrev is Data:
  WPrev{rank: Nat, key: String, value: String}

def w.order.sorted(+key: String, +this: String, +last: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.eq(this, last), Some{W.duplicate_fact(key)},
    Bool.pick(Maybe<&2, String>, String.is_lt(this, last), Some{W.repeated_key_out_of_order(key)}, None{}))

# `check_order`: the rules between one header line and the one before it.
def w.order(prev: Maybe<&2, WPrev>, +r: Nat, +key: String, +value: String) -> Maybe<&2, String>:
  match prev:
    case None{}:
      None{}
    case Some{WPrev{+lr, +lk, +lv}}:
      Bool.pick(Maybe<&2, String>, Nat.is_lt(r, lr), Some{W.keys_out_of_order(key, lk)},
      Bool.pick(Maybe<&2, String>, Bool.not(Nat.is_eq(r, lr)), None{},
      Bool.pick(Maybe<&2, String>, Bool.not(w.repeatable(r)), Some{W.repeated_header(key)},
        w.order.sorted(key, Bool.pick(String, Nat.is_eq(r, 15n), key, value), Bool.pick(String, Nat.is_eq(r, 15n), lk, lv)))))

# Timestamps
# ----------

def w.byte(bs: List<&2, U32>, +i: Nat) -> U32:
  Maybe.default(&2, U32, List.get(&2, U32, bs, i), 0)

def w.is_digit(+b: U32) -> Bool:
  Bool.and(U32.is_ge(b, 48), U32.is_le(b, 57))

def w.digits(count: Nat, +bs: List<&2, U32>, +i: Nat) -> Bool:
  match count:
    case 0n:
      True{}
    case 1n+c:
      Bool.and(w.is_digit(w.byte(bs, i)), w.digits(c, bs, 1n+i))

def w.num(count: Nat, +bs: List<&2, U32>, +i: Nat, +acc: Nat) -> Nat:
  match count:
    case 0n:
      acc
    case 1n+c:
      w.num(c, bs, 1n+i, Nat.add(Nat.mul(acc, 10n), Nat.sub(U32.to_nat(w.byte(bs, i)), 48n)))

def w.at_is(+bs: List<&2, U32>, +i: Nat, +b: U32) -> Bool:
  U32.is_eq(w.byte(bs, i), b)

def w.time.checked(+minus: Bool, +year: Nat, +month: Nat, +day: Nat, +hour: Nat, +minute: Nat, +second: Nat, +oh: Nat, +om: Nat) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, Bool.or(Nat.is_lt(month, 1n), Nat.is_gt(month, 12n)), Some{"there is no such month"},
  Bool.pick(Maybe<&2, String>, Bool.or(Nat.is_lt(day, 1n), Nat.is_gt(day, days_in(year, month))), Some{"there is no such day in that month"},
  Bool.pick(Maybe<&2, String>, Bool.or(Nat.is_gt(hour, 23n), Bool.or(Nat.is_gt(minute, 59n), Nat.is_gt(second, 59n))), Some{"there is no such time of day"},
  Bool.pick(Maybe<&2, String>, Bool.or(Nat.is_gt(oh, 23n), Nat.is_gt(om, 59n)), Some{"there is no such offset"},
  Bool.pick(Maybe<&2, String>, Bool.and(minus, Bool.and(Nat.is_eq(oh, 0n), Nat.is_eq(om, 0n))), Some{"`-00:00` means an unknown offset; write `+00:00` for UTC"}, None{})))))

def w.time.numbers(+bs: List<&2, U32>) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>,
    Bool.and(Bool.and(Bool.and(w.digits(4n, bs, 0n), w.digits(2n, bs, 5n)), Bool.and(w.digits(2n, bs, 8n), w.digits(2n, bs, 11n))),
      Bool.and(Bool.and(w.digits(2n, bs, 14n), w.digits(2n, bs, 17n)), Bool.and(w.digits(2n, bs, 20n), w.digits(2n, bs, 23n)))),
    w.time.checked(w.at_is(bs, 19n, 45), w.num(4n, bs, 0n, 0n), w.num(2n, bs, 5n, 0n), w.num(2n, bs, 8n, 0n), w.num(2n, bs, 11n, 0n), w.num(2n, bs, 14n, 0n), w.num(2n, bs, 17n, 0n), w.num(2n, bs, 20n, 0n), w.num(2n, bs, 23n, 0n)),
    Some{"it holds something that is not a digit"})

# `Timestamp::check`, byte for byte: why a value is not a timestamp.
def w.time.bytes(+bs: List<&2, U32>) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, Bool.not(Nat.is_eq(List.length(&2, U32, bs), 25n)), Some{"it is the wrong length, or carries fractional seconds"},
  Bool.pick(Maybe<&2, String>, Bool.not(Bool.and(Bool.and(Bool.and(w.at_is(bs, 4n, 45), w.at_is(bs, 7n, 45)), Bool.and(w.at_is(bs, 10n, 84), w.at_is(bs, 13n, 58))), Bool.and(w.at_is(bs, 16n, 58), w.at_is(bs, 22n, 58)))),
    Some{"its separators are in the wrong places"},
  Bool.pick(Maybe<&2, String>, Bool.not(Bool.or(w.at_is(bs, 19n, 43), w.at_is(bs, 19n, 45))), Some{"its offset needs a sign; `Z` is not a spelling this format has"},
    w.time.numbers(bs))))

def w.time(+value: String) -> Maybe<&2, String>:
  w.time.bytes(Utf8.encode(value))

# Paths
# -----

def w.components(ps: List<&2, String>) -> Maybe<&2, String>:
  match ps:
    case Nil{}:
      None{}
    case +p <> rest:
      Bool.pick(Maybe<&2, String>, String.is_empty(p), Some{"it has an empty component"},
        Bool.pick(Maybe<&2, String>, Bool.or(String.eq(p, "."), String.eq(p, "..")), Some{"`.` and `..` are not components"}, w.components(rest)))

# `check_path`: why a value is not a path a revision may name. Unicode
# normal form C is not asked, as nowhere in this port.
def w.path(+value: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.is_empty(value), Some{"it is empty"},
  Bool.pick(Maybe<&2, String>, String.starts_with(value, "/"), Some{"it begins with `/`, and a path is relative to the repository root"},
  Bool.pick(Maybe<&2, String>, String.ends_with(value, "/"), Some{"it ends with `/`, and a path names a file rather than a directory"},
  Bool.pick(Maybe<&2, String>, Bool.or(String.starts_with(value, " "), String.ends_with(value, " ")), Some{"it has leading or trailing space"},
  Bool.pick(Maybe<&2, String>, List.any(~&2, ~Char, ~is_control, String.to_list(value)), Some{"it holds a control character"},
    w.components(String.split(value, '/')))))))

# What has been read
# ------------------

type WCore is Data:
  WCore{change: Bool, author: Maybe<&2, String>, when: Bool, revised_by: Maybe<&2, String>, revised: Bool, supersedes: Bool}

type WFiles is Data:
  WFiles{added: List<&2, String>, moved: List<&2, String>, modes: List<&2, String>, dropped: List<&2, String>, edited: List<&2, String>, text: List<&2, String>, bytes: List<&2, String>, links: List<&2, String>}

type WS is Data:
  WS{prev: Maybe<&2, WPrev>, core: WCore, files: WFiles}

def w.start() -> WS:
  WS{None{}, WCore{False{}, None{}, False{}, None{}, False{}, False{}}, WFiles{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}}}

def w.core.set(+key: String, +value: String, c: WCore) -> WCore:
  match c:
    case WCore{+ch, +au, +wh, +rb, +rv, +su}:
      Bool.pick(WCore, String.eq(key, "change"), WCore{True{}, au, wh, rb, rv, su},
      Bool.pick(WCore, String.eq(key, "author"), WCore{ch, Some{value}, wh, rb, rv, su},
      Bool.pick(WCore, String.eq(key, "when"), WCore{ch, au, True{}, rb, rv, su},
      Bool.pick(WCore, String.eq(key, "revised-by"), WCore{ch, au, wh, Some{value}, rv, su},
      Bool.pick(WCore, String.eq(key, "revised"), WCore{ch, au, wh, rb, True{}, su},
      Bool.pick(WCore, String.eq(key, "supersedes"), WCore{ch, au, wh, rb, rv, True{}}, WCore{ch, au, wh, rb, rv, su}))))))

def w.files.of(+key: String, f: WFiles) -> List<&2, String>:
  match f:
    case WFiles{+ad, +mv, +md, +dr, +ed, +tx, +by, +ln}:
      Bool.pick(List<&2, String>, String.eq(key, "add"), ad,
      Bool.pick(List<&2, String>, String.eq(key, "move"), mv,
      Bool.pick(List<&2, String>, String.eq(key, "mode"), md,
      Bool.pick(List<&2, String>, String.eq(key, "drop"), dr,
      Bool.pick(List<&2, String>, String.eq(key, "edit"), ed,
      Bool.pick(List<&2, String>, String.eq(key, "text"), tx,
      Bool.pick(List<&2, String>, String.eq(key, "bytes"), by, ln)))))))

def w.files.add(+key: String, +file: String, f: WFiles) -> WFiles:
  match f:
    case WFiles{+ad, +mv, +md, +dr, +ed, +tx, +by, +ln}:
      Bool.pick(WFiles, String.eq(key, "add"), WFiles{List.append(&2, String, ad, [file]), mv, md, dr, ed, tx, by, ln},
      Bool.pick(WFiles, String.eq(key, "move"), WFiles{ad, List.append(&2, String, mv, [file]), md, dr, ed, tx, by, ln},
      Bool.pick(WFiles, String.eq(key, "mode"), WFiles{ad, mv, List.append(&2, String, md, [file]), dr, ed, tx, by, ln},
      Bool.pick(WFiles, String.eq(key, "drop"), WFiles{ad, mv, md, List.append(&2, String, dr, [file]), ed, tx, by, ln},
      Bool.pick(WFiles, String.eq(key, "edit"), WFiles{ad, mv, md, dr, List.append(&2, String, ed, [file]), tx, by, ln},
      Bool.pick(WFiles, String.eq(key, "text"), WFiles{ad, mv, md, dr, ed, List.append(&2, String, tx, [file]), by, ln},
      Bool.pick(WFiles, String.eq(key, "bytes"), WFiles{ad, mv, md, dr, ed, tx, List.append(&2, String, by, [file]), ln},
        WFiles{ad, mv, md, dr, ed, tx, by, List.append(&2, String, ln, [file])})))))))

# A file stated under `key`, once.
def w.stated(+at: Nat, +key: String, +file: String, st: WS) -> Result<&2, &2, String, WS>:
  match st:
    case WS{+p, +c, +f}:
      Bool.pick(Result<&2, &2, String, WS>, member(w.files.of(key, f), file), Fail{W.at(at, W.file_stated_twice(key, file))},
        Done{WS{p, c, w.files.add(key, file, f)}})

def w.core(+key: String, +value: String, st: WS) -> WS:
  match st:
    case WS{+p, +c, +f}:
      WS{p, w.core.set(key, value, c), f}

def w.file_id(+n: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, Id.is_assigned(n), None{}, Some{W.malformed_file_id(n)})

# What a tree header's second field must be.
def w.second(+at: Nat, +key: String, +file: String, +second: String, +st: WS) -> Result<&2, &2, String, WS>:
  +bad = Bool.pick(Maybe<&2, String>, Bool.or(String.eq(key, "add"), String.eq(key, "move")), Maybe.map(&2, String, String, b => W.malformed_path(second, b), w.path(second)),
    Bool.pick(Maybe<&2, String>, String.eq(key, "mode"), Bool.pick(Maybe<&2, String>, Bool.or(String.eq(second, "plain"), String.eq(second, "executable")), None{}, Some{W.unknown_mode(second)}),
    Bool.pick(Maybe<&2, String>, String.eq(key, "link"), Maybe.default(&2, Maybe<&2, String>, Maybe.map(&2, String, Maybe<&2, String>, n => w.file_id(n), T.strip_prefix(second, "file:")), None{}),
      Bool.pick(Maybe<&2, String>, T.is_digest(second), None{}, Some{W.malformed_digest(key, second)}))))
  Maybe.default(&2, Result<&2, &2, String, WS>, Maybe.map(&2, String, Result<&2, &2, String, WS>, e => Fail{W.at(at, e)}, bad), w.stated(at, key, file, st))

def w.entry(+at: Nat, +key: String, +st: WS, cut: Maybe<&2, T.Split>) -> Result<&2, &2, String, WS>:
  match cut:
    case None{}:
      Fail{W.at(at, W.malformed_file_entry(key))}
    case Some{T.Split{+file, +second}}:
      Bool.pick(Result<&2, &2, String, WS>, Id.is_assigned(file), w.second(at, key, file, second, st), Fail{W.at(at, W.malformed_file_id(file))})

# A value, read as far as the reading asks: `cheap` reads the causal ones.
def w.value(+at: Nat, +key: String, +value: String, +cheap: Bool, +st: WS) -> Result<&2, &2, String, WS>:
  Bool.pick(Result<&2, &2, String, WS>, String.eq(key, "change"),
    Bool.pick(Result<&2, &2, String, WS>, Id.is_assigned(value), Done{w.core(key, value, st)}, Fail{W.at(at, W.malformed_change_id(value))}),
  Bool.pick(Result<&2, &2, String, WS>, Bool.or(String.eq(key, "parent"), String.eq(key, "supersedes")),
    Bool.pick(Result<&2, &2, String, WS>, T.is_digest(value), Done{w.core(key, value, st)}, Fail{W.at(at, W.malformed_digest(key, value))}),
  Bool.pick(Result<&2, &2, String, WS>, Bool.or(String.eq(key, "when"), String.eq(key, "revised")),
    Bool.pick(Result<&2, &2, String, WS>, cheap, Done{w.core(key, value, st)},
      Maybe.default(&2, Result<&2, &2, String, WS>, Maybe.map(&2, String, Result<&2, &2, String, WS>, b => Fail{W.at(at, W.malformed_timestamp(value, b))}, w.time(value)), Done{w.core(key, value, st)})),
  Bool.pick(Result<&2, &2, String, WS>, Bool.or(String.eq(key, "author"), String.eq(key, "revised-by")), Done{w.core(key, value, st)},
  Bool.pick(Result<&2, &2, String, WS>, Bool.or(cheap, T.has_char(key, '.')), Done{st},
  Bool.pick(Result<&2, &2, String, WS>, String.eq(key, "drop"),
    Bool.pick(Result<&2, &2, String, WS>, Id.is_assigned(value), w.stated(at, key, value, st), Fail{W.at(at, W.malformed_file_id(value))}),
    w.entry(at, key, st, T.split_once(value))))))))

def w.prev(st: WS) -> Maybe<&2, WPrev>:
  match st:
    case WS{p, c, f}:
      p

def w.ranked(+at: Nat, +key: String, +value: String, +cheap: Bool, st: WS, r: Maybe<&2, Nat>) -> Result<&2, &2, String, WS>:
  match st r:
    case _ None{}:
      Fail{W.at(at, W.unknown_header(key))}
    case WS{+p, +c, +f} Some{+rk}:
      Maybe.default(&2, Result<&2, &2, String, WS>, Maybe.map(&2, String, Result<&2, &2, String, WS>, e => Fail{W.at(at, e)}, w.order(p, rk, key, value)),
        w.value(at, key, value, cheap, WS{Some{WPrev{rk, key, value}}, c, f}))

# One header weighed: its rank, its order, its value.
def w.weigh(+cheap: Bool, st: Result<&2, &2, String, WS>, h: WH) -> Result<&2, &2, String, WS>:
  match st h:
    case Fail{e} _:
      Fail{e}
    case Done{s} WH{+at, +key, +value}:
      w.ranked(at, key, value, cheap, s, w.rank(key))

def w.assemble(hs: List<&2, WH>, st: Result<&2, &2, String, WS>) -> Result<&2, &2, String, WS>:
  match hs:
    case Nil{}:
      st
    case h <> rest:
      w.assemble(rest, w.weigh(False{}, st, h))

def w.redundant(+last: Nat, au: Maybe<&2, String>, rb: Maybe<&2, String>) -> Maybe<&2, String>:
  match au rb:
    case Some{+a} Some{+b}:
      Bool.pick(Maybe<&2, String>, String.eq(a, b), Some{W.at(last, W.redundant_revised_by())}, None{})
    case _ _:
      None{}

# The block's own rules, at the last line read: what must be stated, and
# what may not be.
def w.required(+last: Nat, c: WCore) -> Maybe<&2, String>:
  match c:
    case WCore{ch, +au, wh, +rb, +rv, su}:
      Bool.pick(Maybe<&2, String>, Bool.not(ch), Some{W.at(last, W.missing_header("change"))},
      Bool.pick(Maybe<&2, String>, Maybe.is_none(&2, String, au), Some{W.at(last, W.missing_header("author"))},
      Bool.pick(Maybe<&2, String>, Bool.not(wh), Some{W.at(last, W.missing_header("when"))},
      Bool.pick(Maybe<&2, String>, Bool.not(su),
        Bool.pick(Maybe<&2, String>, rv, Some{W.at(last, W.rewrite_without_supersedes("revised"))},
          Bool.pick(Maybe<&2, String>, Maybe.is_some(&2, String, rb), Some{W.at(last, W.rewrite_without_supersedes("revised-by"))}, w.redundant(last, au, rb))),
        Bool.pick(Maybe<&2, String>, rv, w.redundant(last, au, rb), Some{W.at(last, W.missing_header("revised"))})))))


# Decision 0008's contradictions, in the order the Rust tool asks them,
# file by file.
def w.clash(+last: Nat, +first: String, +file: String, checks: List<&2, T.Split>) -> Maybe<&2, String>:
  match checks:
    case Nil{}:
      None{}
    case T.Split{+second, +held} <> rest:
      Bool.pick(Maybe<&2, String>, String.eq(held, "1"), Some{W.at(last, W.contradictory(first, second, file))}, w.clash(last, first, file, rest))

def w.in(+xs: List<&2, String>, +file: String) -> String:
  Bool.pick(String, member(xs, file), "1", "0")

def w.clashes.added(fs: List<&2, String>, +last: Nat, +f: WFiles) -> Maybe<&2, String>:
  match fs f:
    case Nil{} _:
      None{}
    case +x <> rest WFiles{+ad, +mv, +md, +dr, +ed, +tx, +by, +ln}:
      Maybe.or(&2, String, w.clash(last, "add", x, [T.Split{"move", w.in(mv, x)}, T.Split{"drop", w.in(dr, x)}, T.Split{"edit", w.in(ed, x)}]),
        w.clashes.added(rest, last, WFiles{ad, mv, md, dr, ed, tx, by, ln}))

def w.clashes.moved(fs: List<&2, String>, +last: Nat, +dr: List<&2, String>) -> Maybe<&2, String>:
  match fs:
    case Nil{}:
      None{}
    case +x <> rest:
      Maybe.or(&2, String, w.clash(last, "move", x, [T.Split{"drop", w.in(dr, x)}]), w.clashes.moved(rest, last, dr))

def w.clashes.dropped(fs: List<&2, String>, +last: Nat, +f: WFiles) -> Maybe<&2, String>:
  match fs f:
    case Nil{} _:
      None{}
    case +x <> rest WFiles{+ad, +mv, +md, +dr, +ed, +tx, +by, +ln}:
      Maybe.or(&2, String, w.clash(last, "drop", x, [T.Split{"edit", w.in(ed, x)}, T.Split{"bytes", w.in(by, x)}, T.Split{"mode", w.in(md, x)}, T.Split{"link", w.in(ln, x)}]),
        w.clashes.dropped(rest, last, WFiles{ad, mv, md, dr, ed, tx, by, ln}))

def w.clashes.linked(fs: List<&2, String>, +last: Nat, +f: WFiles) -> Maybe<&2, String>:
  match fs f:
    case Nil{} _:
      None{}
    case +x <> rest WFiles{+ad, +mv, +md, +dr, +ed, +tx, +by, +ln}:
      Maybe.or(&2, String, w.clash(last, "link", x, [T.Split{"text", w.in(tx, x)}, T.Split{"bytes", w.in(by, x)}, T.Split{"edit", w.in(ed, x)}, T.Split{"mode", w.in(md, x)}]),
        w.clashes.linked(rest, last, WFiles{ad, mv, md, dr, ed, tx, by, ln}))

def w.clashes.text(fs: List<&2, String>, +last: Nat, +ad: List<&2, String>, +by: List<&2, String>) -> Maybe<&2, String>:
  match fs:
    case Nil{}:
      None{}
    case +x <> rest:
      Maybe.or(&2, String, w.clash(last, "text", x, [T.Split{"bytes", w.in(by, x)}]),
        Bool.pick(Maybe<&2, String>, member(ad, x), w.clashes.text(rest, last, ad, by), Some{W.at(last, W.text_without_add(x))}))

def w.clashes.bytes(fs: List<&2, String>, +last: Nat, +ed: List<&2, String>) -> Maybe<&2, String>:
  match fs:
    case Nil{}:
      None{}
    case +x <> rest:
      Maybe.or(&2, String, w.clash(last, "edit", x, [T.Split{"bytes", w.in(ed, x)}]), w.clashes.bytes(rest, last, ed))

def w.clashes(+last: Nat, f: WFiles) -> Maybe<&2, String>:
  match f:
    case WFiles{+ad, +mv, +md, +dr, +ed, +tx, +by, +ln}:
      Maybe.or(&2, String, w.clashes.added(ad, last, WFiles{ad, mv, md, dr, ed, tx, by, ln}),
      Maybe.or(&2, String, w.clashes.moved(mv, last, dr),
      Maybe.or(&2, String, w.clashes.dropped(dr, last, WFiles{ad, mv, md, dr, ed, tx, by, ln}),
      Maybe.or(&2, String, w.clashes.linked(ln, last, WFiles{ad, mv, md, dr, ed, tx, by, ln}),
      Maybe.or(&2, String, w.clashes.text(tx, last, ad, by), w.clashes.bytes(by, last, ed))))))

# The header block: what is left, the lines read, the headers split, and
# whether the reading has stopped. `cheap` weighs each header as it is
# split, as opening a store does; the whole reading splits them all first.
type WHs is Data:
  WHs{rest: List<&2, T.Line>, n: Nat, hs: List<&2, WH>, st: WS, done: Bool}

def w.hs.split(+rest: List<&2, T.Line>, +at: Nat, +hs: List<&2, WH>, +cheap: Bool, +st: WS, r: Result<&2, &2, String, WH>) -> Result<&2, &2, String, WHs>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+h}:
      Bool.pick(Result<&2, &2, String, WHs>, cheap,
        Result.map(&2, &2, String, WS, WHs, s => WHs{rest, at, hs, s, False{}}, w.weigh(True{}, Done{st}, h)),
        Done{WHs{rest, at, List.append(&2, WH, hs, [h]), st, False{}}})

def w.hs.line(+t: String, +term: Bool, +rest: List<&2, T.Line>, +n: Nat, +hs: List<&2, WH>, +cheap: Bool, +st: WS) -> Result<&2, &2, String, WHs>:
  Bool.pick(Result<&2, &2, String, WHs>, String.is_empty(t),
    Bool.pick(Result<&2, &2, String, WHs>, List.is_empty(&2, T.Line, rest), Fail{W.at(1n+n, W.empty_body_after_separator())}, Done{WHs{rest, 1n+n, hs, st, True{}}}),
    Bool.pick(Result<&2, &2, String, WHs>, term, w.hs.split(rest, 1n+n, hs, cheap, st, w.split(1n+n, T.split_once(t))), Fail{W.at(1n+n, W.unterminated())}))

def w.hs.step(+cheap: Bool, r: WHs) -> Result<&2, &2, String, WHs>:
  match r:
    case WHs{Nil{}, +n, +hs, +st, done}:
      Done{WHs{Nil{}, n, hs, st, True{}}}
    case WHs{T.Line{+t, +term} <> +rest, +n, +hs, +st, done}:
      Bool.pick(Result<&2, &2, String, WHs>, done, Done{WHs{T.Line{t, term} <> rest, n, hs, st, True{}}}, w.hs.line(t, term, rest, n, hs, cheap, st))

def w.hs.go(fuel: Nat, +cheap: Bool, r: Result<&2, &2, String, WHs>) -> Result<&2, &2, String, WHs>:
  match fuel r:
    case _ Fail{e}:
      Fail{e}
    case 0n Done{st}:
      Done{st}
    case 1n+p Done{st}:
      w.hs.go(p, cheap, w.hs.step(cheap, st))

def w.core.of(st: WS) -> WCore:
  match st:
    case WS{p, c, f}:
      c

def w.files.all(st: WS) -> WFiles:
  match st:
    case WS{p, c, f}:
      f

def w.whole.end(+last: Nat, r: Result<&2, &2, String, WS>) -> Maybe<&2, String>:
  match r:
    case Fail{e}:
      Some{e}
    case Done{+st}:
      Maybe.or(&2, String, w.required(last, w.core.of(st)), w.clashes(last, w.files.all(st)))

def w.block(+cheap: Bool, r: Result<&2, &2, String, WHs>) -> Maybe<&2, String>:
  match r:
    case Fail{e}:
      Some{e}
    case Done{WHs{rest, +n, hs, +st, done}}:
      Bool.pick(Maybe<&2, String>, cheap, w.required(n, w.core.of(st)), w.whole.end(n, w.assemble(hs, Done{st})))

def w.preamble(+cheap: Bool, ls: List<&2, T.Line>) -> Maybe<&2, String>:
  match ls:
    case Nil{}:
      Some{W.at(1n, W.empty())}
    case T.Line{+t, +term} <> +rest:
      Maybe.or(&2, String, W.preamble(t, term), w.block(cheap, w.hs.go(1n+List.length(&2, T.Line, rest), cheap, Done{WHs{rest, 1n, Nil{}, w.start(), False{}}})))

# The line of the first carriage return, which the Rust tool refuses before
# anything else, wherever it is.
def w.cr(ls: List<&2, T.Line>, +n: Nat) -> Maybe<&2, Nat>:
  match ls:
    case Nil{}:
      None{}
    case T.Line{t, term} <> rest:
      Bool.pick(Maybe<&2, Nat>, T.has_char(t, '\r'), Some{1n+n}, w.cr(rest, 1n+n))

def w.read(+cheap: Bool, +s: String) -> Maybe<&2, String>:
  +ls = T.lines(s)
  Bool.pick(Maybe<&2, String>, W.bom(s), Some{W.at(1n, W.byte_order_mark())},
    Maybe.default(&2, Maybe<&2, String>, Maybe.map(&2, Nat, Maybe<&2, String>, n => Some{W.at(n, W.carriage_return())}, w.cr(ls, 0n)), w.preamble(cheap, ls)))

# Why the Rust tool refuses these bytes as a revision it reads whole, in
# its words: none where it would not.
def refusal(+s: String) -> Maybe<&2, String>:
  w.read(False{}, s)

# Why opening a store refuses them (`format::revision`): the shape, and the
# values that name revisions.
def refusal.opening(+s: String) -> Maybe<&2, String>:
  w.read(True{}, s)

# What opening a store reads of a revision it accepts: the header block's
# values, and the message. A command that asks what the revision did reads
# it whole, and the refusal of that reading is its to say.
def opening.pair(cut: Maybe<&2, T.Split>) -> List<&2, Header>:
  match cut:
    case None{}:
      Nil{}
    case Some{T.Split{k, v}}:
      [Header{k, v}]

def opening.headers(ls: List<&2, T.Line>) -> List<&2, Header>:
  match ls:
    case Nil{}:
      Nil{}
    case T.Line{+t, term} <> rest:
      +more = opening.headers(rest)
      Bool.pick(List<&2, Header>, String.is_empty(t), Nil{}, List.append(&2, Header, opening.pair(T.split_once(t)), more))

def opening.message(ls: List<&2, T.Line>) -> String:
  match ls:
    case Nil{}:
      SNil{}
    case T.Line{+t, term} <> +rest:
      Bool.pick(String, String.is_empty(t), unlines(rest), opening.message(rest))

def opening.rev(+ls: List<&2, T.Line>) -> Rev:
  +hs = opening.headers(ls)
  Rev{Maybe.default(&2, String, value_of(hs, "change"), SNil{}), values_of(hs, "parent"), values_of(hs, "supersedes"),
    Maybe.default(&2, String, value_of(hs, "author"), SNil{}), Maybe.default(&2, String, value_of(hs, "when"), SNil{}),
    value_of(hs, "revised-by"), value_of(hs, "revised"), Nil{}, opening.message(ls)}

def opening.tail(ls: List<&2, T.Line>) -> List<&2, T.Line>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      rest

def opening.read(+s: String) -> Maybe<&2, Rev>:
  Bool.pick(Maybe<&2, Rev>, Maybe.is_some(&2, String, refusal.opening(s)), None{}, Some{opening.rev(opening.tail(T.lines(s)))})

def worded(+s: String, r: Result<&2, &2, String, Rev>) -> Result<&2, &2, String, Rev>:
  match r:
    case Done{d}:
      Done{d}
    case Fail{e}:
      Fail{Maybe.default(&2, String, refusal(s), e)}

# A revision document, from its text.
def parse(+s: String) -> Result<&2, &2, String, Rev>:
  worded(s, Bool.pick(Result<&2, &2, String, Rev>, T.has_char(s, '\r'), Fail{"a carriage return"}, parse.preamble(T.lines(s))))

# Writing
# -------

def each(+key: String, vs: List<&2, String>) -> String:
  match vs:
    case Nil{}:
      SNil{}
    case v <> rest:
      key ++ " " ++ v ++ "\n" ++ each(key, rest)

def optional(key: String, v: Maybe<&2, String>) -> String:
  match v:
    case None{}:
      SNil{}
    case Some{s}:
      key ++ " " ++ s ++ "\n"

def write_facts(hs: List<&2, Header>) -> String:
  match hs:
    case Nil{}:
      SNil{}
    case Header{k, v} <> rest:
      k ++ " " ++ v ++ "\n" ++ write_facts(rest)

# The exact bytes of a document: `write(parse(s)) == s` for every `s` parse
# accepts, since the parser admits one spelling.
def write(r: Rev) -> String:
  match r:
    case Rev{change, parents, supersedes, author, when, revised_by, revised, facts, +message}:
      "historica\n" ++ "change " ++ change ++ "\n" ++ each("parent", parents) ++ each("supersedes", supersedes)
        ++ "author " ++ author ++ "\n" ++ "when " ++ when ++ "\n" ++ optional("revised-by", revised_by) ++ optional("revised", revised)
        ++ write_facts(facts) ++ Bool.pick(String, String.is_empty(message), SNil{}, "\n" ++ message)

# History
# -------

# One immutable point in causal history, as the core sees it: its digest,
# the change it is a version of, its parents, what it replaces, and why.
type Revision is Data:
  Revision{id: String, change: String, parents: List<&2, String>, supersedes: List<&2, String>, message: String}

def of_doc(id: String, r: Rev) -> Revision:
  match r:
    case Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      Revision{id, change, parents, supersedes, message}

# A grow-only set of revisions by digest. Two replicas merge by union, and
# receiving a revision twice is idempotent, because a digest names bytes.
def History() -> Data:
  Map<&2, Revision>

def empty() -> History():
  Map.new(&2, Revision)

def insert(h: History(), r: Revision) -> History():
  match r:
    case Revision{+id, change, parents, supersedes, message}:
      Map.set(&2, Revision, h, id, Revision{id, change, parents, supersedes, message})

def merge(h: History(), other: History()) -> History():
  Map.union(&2, Revision, h, other)

def revisions(h: History()) -> List<&2, Revision>:
  Map.values(&2, Revision, h)

def id_of(r: Revision) -> String:
  match r:
    case Revision{id, change, parents, supersedes, message}:
      id

def change_of(r: Revision) -> String:
  match r:
    case Revision{id, change, parents, supersedes, message}:
      change

def parents_of(r: Revision) -> List<&2, String>:
  match r:
    case Revision{id, change, parents, supersedes, message}:
      parents

def supersedes_of(r: Revision) -> List<&2, String>:
  match r:
    case Revision{id, change, parents, supersedes, message}:
      supersedes

def message_of(r: Revision) -> String:
  match r:
    case Revision{id, change, parents, supersedes, message}:
      message

def ids(rs: List<&2, Revision>) -> List<&2, String>:
  T.map(~Revision, ~String, ~(r => id_of(r)), rs)

# Every parent any revision names.
def all_parents(rs: List<&2, Revision>) -> List<&2, String>:
  T.concat(String, T.map(~Revision, ~List<&2, String>, ~(r => parents_of(r)), rs))

# Every revision some revision has replaced. It need not be present: the
# successor carries the evidence.
def superseded(h: History()) -> List<&2, String>:
  T.concat(String, T.map(~Revision, ~List<&2, String>, ~(r => supersedes_of(r)), revisions(h)))

# Revisions no revision names as a parent. A pure graph question, so a
# superseded revision can be one; filter with `superseded` to show only
# current work. A missing parent does not make its child a head.
def heads(h: History()) -> List<&2, String>:
  +rs = revisions(h)
  +named = all_parents(rs)
  without(ids(rs), named)

# Parents named but not present: history transport has not delivered.
def missing_parents(h: History()) -> List<&2, String>:
  +rs = revisions(h)
  +present = ids(rs)
  without(all_parents(rs), present)

# What one change ID currently means.
type ChangeState is Data:
  UnknownChange{}
  Resolved{id: String}
  Divergent{ids: List<&2, String>}
  Abandoned{}

def keep_revision(b: Bool, x: Revision, rest: List<&2, Revision>) -> List<&2, Revision>:
  match b:
    case True{}:
      x <> rest
    case False{}:
      rest

def revisions_of.go(rs: List<&2, Revision>, +change: String) -> List<&2, Revision>:
  match rs:
    case Nil{}:
      Nil{}
    case Revision{id, +c, parents, supersedes, message} <> rest:
      keep_revision(String.eq(c, change), Revision{id, c, parents, supersedes, message}, revisions_of.go(rest, change))

def revisions_of(h: History(), +change: String) -> List<&2, Revision>:
  revisions_of.go(revisions(h), change)

def change_state.of(any: Bool, current: List<&2, String>) -> ChangeState:
  match current:
    case Nil{}:
      Bool.pick(ChangeState, any, Abandoned{}, UnknownChange{})
    case only <> Nil{}:
      Resolved{only}
    case first <> second <> rest:
      Divergent{first <> second <> rest}

# Head discovery over supersession edges, the rule `heads` applies to
# parent edges: one current revision resolves the change, several diverge,
# and none — every one replaced by a revision of another change — abandons it.
def change_state(+h: History(), change: String) -> ChangeState:
  +of_change = ids(revisions_of(h, change))
  +gone = superseded(h)
  change_state.of(Bool.not(List.is_empty(&2, String, of_change)), without(of_change, gone))
