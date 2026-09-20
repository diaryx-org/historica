# The revision document — who recorded what, when, and why — and the
# history a set of them makes: a Merkle DAG that merges by set union, with
# explicit parents and explicit supersession, and no timestamp in identity.

import Base
import ./text.bend as T
import ./ident.bend as Id

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

def classify(+k: String) -> Key:
  match k:
    case "change":
      Key.Change{}
    case "parent":
      Key.Parent{}
    case "supersedes":
      Key.Supersedes{}
    case "author":
      Key.Author{}
    case "when":
      Key.When{}
    case "revised-by":
      Key.RevisedBy{}
    case "revised":
      Key.Revised{}
    case "add":
      Key.Add{}
    case "move":
      Key.Move{}
    case "mode":
      Key.Mode{}
    case "drop":
      Key.Drop{}
    case "edit":
      Key.Edit{}
    case "text":
      Key.Text{}
    case "bytes":
      Key.Bytes{}
    case "link":
      Key.Link{}
    case _:
      classify.named(k, T.has_char(k, '.'))

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

def is_timestamp(+s: String) -> Bool:
  Bool.and(timestamp.shape(s, "dddd-dd-ddTdd:dd:ddsdd:dd"),
    Bool.and(Bool.and(within(s, 5n, 2n, 1n, 12n), within(s, 8n, 2n, 1n, 31n)),
      Bool.and(Bool.and(within(s, 11n, 2n, 0n, 23n), within(s, 14n, 2n, 0n, 59n)),
        Bool.and(within(s, 17n, 2n, 0n, 60n), Bool.and(within(s, 20n, 2n, 0n, 23n), within(s, 23n, 2n, 0n, 59n))))))

# A path is relative, with no empty component and no `.` or `..`, and no
# leading or trailing space. (Unicode normal form C is not checked here.)
def path_part_ok(p: String) -> Bool:
  match p:
    case "":
      False{}
    case ".":
      False{}
    case "..":
      False{}
    case _:
      True{}

def is_path(+p: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(p)),
    Bool.and(Bool.not(Bool.or(String.starts_with(p, " "), String.ends_with(p, " "))),
      Bool.and(Bool.not(T.has_char(p, '\\')), List.all(~&2, ~String, ~path_part_ok, String.split(p, '/')))))

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

def disjoint(xs: List<&2, String>, +ys: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(Bool.not(member(ys, x)), disjoint(rest, ys))

def subset(xs: List<&2, String>, +ys: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(member(ys, x), subset(rest, ys))

def unique(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> +rest:
      Bool.and(Bool.not(member(rest, x)), unique(rest))

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

def assemble(+hs: List<&2, Header>, message: String) -> Result<&2, &2, String, Rev>:
  +supersedes = values_of(hs, "supersedes")
  +revised = value_of(hs, "revised")
  +revised_by = value_of(hs, "revised-by")
  do Result<&2, &2, String, Rev>:
    change : String <- required(value_of(hs, "change"), "change")
    +author : String <- required(value_of(hs, "author"), "author")
    when : String <- required(value_of(hs, "when"), "when")
    ensure(Bool.or(List.is_empty(&2, String, supersedes), Maybe.is_some(&2, String, revised)), "a revision that supersedes must say when it was revised")
    ensure(Bool.or(Bool.not(List.is_empty(&2, String, supersedes)), Bool.and(Maybe.is_none(&2, String, revised), Maybe.is_none(&2, String, revised_by))), "`revised` and `revised-by` need a `supersedes`")
    ensure(Bool.not(maybe_eq(revised_by, author)), "`revised-by` names the author, which says nothing")
    facts_ok(hs)
    return Rev{change, values_of(hs, "parent"), supersedes, author, when, revised_by, revised, facts_of(hs), message}

# Parsing
# -------

# The message is the rest of the file, verbatim, newline or no newline.
def unlines(ls: List<&2, T.Line>) -> String:
  match ls:
    case Nil{}:
      SNil{}
    case T.Line{t, n} <> rest:
      t ++ Bool.pick(String, n, "\n", SNil{}) ++ unlines(rest)

def header_of(+t: String, cut: Maybe<&2, T.Split>) -> Result<&2, &2, String, Header>:
  match cut:
    case None{}:
      Fail{"the header `" ++ t ++ "` has no value"}
    case Some{T.Split{+k, +v}}:
      do Result<&2, &2, String, Header>:
        ensure(shaped_key(k), "a malformed key `" ++ k ++ "`")
        ensure(Bool.not(String.is_empty(v)), "the header `" ++ k ++ "` has no value")
        ensure(Bool.not(Bool.or(String.starts_with(v, " "), String.ends_with(v, " "))), "the header `" ++ k ++ "` has a padded value")
        ensure(Bool.not(List.any(~&2, ~Char, ~is_control, String.to_list(v))), "the header `" ++ k ++ "` holds a control character")
        return Header{k, v}

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

def parse.preamble(ls: List<&2, T.Line>) -> Result<&2, &2, String, Rev>:
  match ls:
    case T.Line{"historica", True{}} <> +rest:
      parse.split(headers.go(rest, head_header(rest), 2n, Nil{}))
    case T.Line{+t, term} <> rest:
      Bool.pick(Result<&2, &2, String, Rev>, String.starts_with(t, "historica-"), Fail{"line 1: an unknown version `" ++ t ++ "`, likely a newer historica"}, Fail{"line 1: not a historica document"})
    case Nil{}:
      Fail{"an empty document"}

# A revision document, from its text.
def parse(+s: String) -> Result<&2, &2, String, Rev>:
  Bool.pick(Result<&2, &2, String, Rev>, T.has_char(s, '\r'), Fail{"a carriage return"}, parse.preamble(T.lines(s)))

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
