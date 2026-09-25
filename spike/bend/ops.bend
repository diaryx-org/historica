# The operation document: what one revision did to one file, and the file
# materialised by replaying it. Positions are indices into the parent state,
# counted from zero, and none of them move; a delete quotes what it removed,
# so a document that disagrees with the parent it claims to edit is caught at
# replay rather than absorbed.

import Base
import ./text.bend as T
import ./utf8.bend as Utf8
import ./sha256.bend as Sha
import ./words.bend as W

# The model
# ---------

# One line of a file, terminator included: `terminated` is whether a newline
# ends it, which only a file's last item may lack, and `forgotten` says the
# text was destroyed and the marker stands where it was.
type Item is Data:
  Item{text: String, terminated: Bool, forgotten: Bool}

type Verb is Data:
  Delete{}
  Insert{}

# One operation: a delete of `items` at `at`, or an insert of them before it.
type Op is Data:
  Op{verb: Verb, at: Nat, items: List<&2, Item>}

# A parsed document. `forgets` names the document this one stands in for;
# `result` is the digest of the file the operations produce.
type Doc is Data:
  Doc{forgets: Maybe<&2, String>, result: Maybe<&2, String>, ops: List<&2, Op>}

def line(text: String) -> Item:
  Item{text, True{}, False{}}

def unterminated(text: String) -> Item:
  Item{text, False{}, False{}}

def forgotten() -> Item:
  Item{SNil{}, True{}, True{}}

def verb_is(a: Verb, b: Verb) -> Bool:
  match a b:
    case Delete{} Delete{}:
      True{}
    case Insert{} Insert{}:
      True{}
    case _ _:
      False{}

def prefix(k: Verb) -> Char:
  match k:
    case Delete{}:
      '-'
    case Insert{}:
      '+'

# Whether a recorded item matches one found at replay. A forgotten item on
# either side ignores text, but the terminators must still agree.
def agrees(a: Item, b: Item) -> Bool:
  match a b:
    case Item{t1, n1, f1} Item{t2, n2, f2}:
      Bool.and(Bool.not(Bool.xor(n1, n2)), Bool.or(Bool.or(f1, f2), T.same(t1, t2)))

# Whether two items are the same line, for the diff. A forgotten item is
# nobody's line.
def same(a: Item, b: Item) -> Bool:
  match a b:
    case Item{t1, n1, f1} Item{t2, n2, f2}:
      Bool.and(Bool.not(Bool.or(f1, f2)), Bool.and(T.same(t1, t2), Bool.not(Bool.xor(n1, n2))))

def count(op: Op) -> Nat:
  match op:
    case Op{k, at, items}:
      List.length(&2, Item, items)

# The position past the last item a delete removes; an insert removes none.
def end(op: Op) -> Nat:
  match op:
    case Op{k, at, items}:
      match k:
        case Delete{}:
          Nat.add(at, List.length(&2, Item, items))
        case Insert{}:
          at

# States
# ------

# A file as items, the reverse of `text`: a last line with no terminator
# becomes an item that says so.
def from_text.go(parts: List<&2, String>) -> List<&2, Item>:
  match parts:
    case Nil{}:
      Nil{}
    case +last <> Nil{}:
      Bool.pick(List<&2, Item>, String.is_empty(last), Nil{}, [unterminated(last)])
    case h <> t:
      line(h) <> from_text.go(t)

def from_text(s: String) -> List<&2, Item>:
  from_text.go(String.split(s, '\n'))

def shown(it: Item) -> String:
  match it:
    case Item{tx, n, f}:
      Bool.pick(String, f, "\\ forgotten", tx)

def terminator(it: Item) -> String:
  match it:
    case Item{t, n, f}:
      Bool.pick(String, n, "\n", SNil{})

# The file's bytes, as a string. A forgotten item shows its marker.
def text(items: List<&2, Item>) -> String:
  match items:
    case Nil{}:
      SNil{}
    case +it <> rest:
      shown(it) ++ terminator(it) ++ text(rest)

def state_digest(items: List<&2, Item>) -> String:
  Sha.digest(Utf8.encode(text(items)))

def any_forgotten(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}:
      False{}
    case Item{t, n, f} <> rest:
      Bool.or(f, any_forgotten(rest))

# Whether every item but the last is terminated.
def terminated_but_last(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}:
      True{}
    case it <> Nil{}:
      True{}
    case Item{t, n, f} <> rest:
      Bool.and(n, terminated_but_last(rest))

# Parsing
# -------

def fail(-A: Data, at: Nat, msg: String) -> Result<&2, &2, String, A>:
  Fail{"line " ++ Nat.show(at) ++ ": " ++ msg}

def ensure(ok: Bool, at: Nat, msg: String) -> Result<&2, &2, String, Unit>:
  Bool.pick(Result<&2, &2, String, Unit>, ok, Done{Unit{}}, fail(Unit, at, msg))

# The items after an operation line, in reverse, and what follows them.
type Taken is Data:
  Taken{items: List<&2, Item>, rest: List<&2, T.Line>, at: Nat}

# What one line under an operation is: a prefixed item, a marker, or the
# end of the run. Classified before the walk reaches it, because the walk
# may only match what a pattern bound.
type Read is Data:
  Body{text: String}
  NoNewline{}
  Forgotten{}
  Other{}

def classify.of(stripped: Maybe<&2, String>, no_newline: Bool, forgot: Bool) -> Read:
  match stripped:
    case Some{body}:
      Body{body}
    case None{}:
      match no_newline:
        case True{}:
          NoNewline{}
        case False{}:
          match forgot:
            case True{}:
              Forgotten{}
            case False{}:
              Other{}

def classify(+t: String, p: Char) -> Read:
  classify.of(T.strip_prefix(t, String.from_list([p])), T.same(t, "\\ no newline"), T.same(t, "\\ forgotten"))

def classify_head(ls: List<&2, T.Line>, p: Char) -> Read:
  match ls:
    case Nil{}:
      Other{}
    case T.Line{t, term} <> rest:
      classify(t, p)

# The items under an operation. `r` is what the head of `ls` is.
def take_items(ls: List<&2, T.Line>, r: Read, at: Nat, +p: Char, acc: List<&2, Item>) -> Result<&2, &2, String, Taken>:
  match ls r:
    case Nil{} _:
      Done{Taken{acc, Nil{}, at}}
    case T.Line{t, True{}} <> +rest Body{body}:
      take_items(rest, classify_head(rest, p), 1n+at, p, line(body) <> acc)
    case T.Line{t, False{}} <> rest Body{body}:
      fail(Taken, at, "unterminated line")
    case T.Line{t, True{}} <> +rest NoNewline{}:
      match acc:
        case Item{t2, True{}, f2} <> acc_rest:
          take_items(rest, classify_head(rest, p), 1n+at, p, Item{t2, False{}, f2} <> acc_rest)
        case _:
          fail(Taken, at, "`\\ no newline` without an item above it")
    case T.Line{t, False{}} <> rest NoNewline{}:
      fail(Taken, at, "unterminated line")
    case T.Line{t, True{}} <> +rest Forgotten{}:
      take_items(rest, classify_head(rest, p), 1n+at, p, forgotten() <> acc)
    case T.Line{t, False{}} <> rest Forgotten{}:
      fail(Taken, at, "unterminated line")
    case T.Line{t, term} <> rest Other{}:
      Done{Taken{acc, T.Line{t, term} <> rest, at}}

# The header line of an operation, its items, and the ordering rule against
# the operation before it, all decided before the walk over operations
# takes its next step.
type Next is Data:
  More{op: Op, rest: List<&2, T.Line>, at: Nat}
  End{}
  Bad{at: Nat, msg: String}

# Two operations at one position: a delete may precede an insert, and
# nothing else may share a position. Past that, nothing may count into a run
# being deleted, and two deletes that meet are one delete.
def ordered.same(prev: Verb, next: Verb) -> Maybe<&2, String>:
  match prev next:
    case Delete{} Insert{}:
      None{}
    case Delete{} Delete{}:
      Some{"two operations overlap"}
    case Insert{} Delete{}:
      Some{"a delete after an insert at one position"}
    case Insert{} Insert{}:
      Some{"two inserts at one position"}

def ordered.after(prev: Op, next_verb: Verb, next_at: Nat) -> Maybe<&2, String>:
  match prev:
    case Op{Delete{}, at, items}:
      +stop = Nat.add(at, List.length(&2, Item, items))
      +next_at = next_at
      Bool.pick(Maybe<&2, String>, Nat.is_lt(next_at, stop), Some{"two operations overlap"},
        Bool.pick(Maybe<&2, String>, Bool.and(Nat.is_eq(next_at, stop), verb_is(next_verb, Delete{})), Some{"two deletes that meet are one delete"}, None{}))
    case Op{Insert{}, at, items}:
      None{}

def ordered.of(prev: Op, next_verb: Verb, +next_at: Nat, c: Cmp) -> Maybe<&2, String>:
  match prev c:
    case _ LT{}:
      Some{"operations out of order"}
    case Op{v, at, items} EQ{}:
      ordered.same(v, next_verb)
    case _ GT{}:
      ordered.after(prev, next_verb, next_at)

# The complaint, if the next operation may not follow the previous one.
def ordered(prev: Maybe<&2, Op>, next: Op) -> Maybe<&2, String>:
  match prev next:
    case None{} _:
      None{}
    case Some{Op{pv, +pat, pitems}} Op{nv, +nat, nitems}:
      ordered.of(Op{pv, pat, pitems}, nv, nat, Nat.cmp(nat, pat))

def next_op.fin(op: Op, rest: List<&2, T.Line>, at: Nat, complaint: Maybe<&2, String>) -> Next:
  match complaint:
    case None{}:
      More{op, rest, at}
    case Some{msg}:
      Bad{at, msg}

# The items are in. A delete's count must agree with them, and neither
# operation may be empty.
def next_op.count(+op: Op, +n: Nat, rest: List<&2, T.Line>, at: Nat, at2: Nat, expected: Maybe<&2, Nat>) -> Next:
  match expected:
    case None{}:
      Bool.pick(Next, Nat.is_eq(n, 0n), Bad{at, "an insert with no items"}, More{op, rest, at2})
    case Some{expected_n}:
      Bool.pick(Next, Nat.is_eq(n, expected_n), More{op, rest, at2}, Bad{at, "a delete whose count disagrees with its items"})

def next_op.items(verb: Verb, pos: Nat, expected: Maybe<&2, Nat>, at: Nat, taken: Result<&2, &2, String, Taken>) -> Next:
  match taken:
    case Fail{e}:
      Bad{at, e}
    case Done{Taken{rev, rest, at2}}:
      +items = List.reverse(&2, Item, rev)
      next_op.count(Op{verb, pos, items}, List.length(&2, Item, items), rest, at, at2, expected)

def next_op.delete(+rest: List<&2, T.Line>, +at: Nat, pos: Maybe<&2, Nat>, count: Maybe<&2, Nat>, spaced: Bool) -> Next:
  match pos count spaced:
    case Some{p} Some{0n} False{}:
      Bad{at, "a delete of nothing"}
    case Some{p} Some{c} False{}:
      next_op.items(Delete{}, p, Some{c}, at, take_items(rest, classify_head(rest, '-'), 1n+at, '-', Nil{}))
    case _ _ _:
      Bad{at, "a malformed delete"}

def next_op.delete_args(+rest: List<&2, T.Line>, +at: Nat, args: Maybe<&2, T.Split>) -> Next:
  match args:
    case None{}:
      Bad{at, "a malformed delete"}
    case Some{T.Split{pos, +cnt}}:
      next_op.delete(rest, at, T.number(pos), T.number(cnt), T.has_char(cnt, ' '))

def next_op.insert(+rest: List<&2, T.Line>, +at: Nat, pos: Maybe<&2, Nat>) -> Next:
  match pos:
    case None{}:
      Bad{at, "a malformed insert"}
    case Some{p}:
      next_op.items(Insert{}, p, None{}, at, take_items(rest, classify_head(rest, '+'), 1n+at, '+', Nil{}))

# The operation line, once its keyword is known.
def next_op.keyword(+rest: List<&2, T.Line>, +at: Nat, +t: String, +args: String, is_delete: Bool, is_insert: Bool, is_content: Bool, is_marker: Bool) -> Next:
  match is_delete:
    case True{}:
      next_op.delete_args(rest, at, T.split_once(args))
    case False{}:
      match is_insert:
        case True{}:
          Bool.pick(Next, Bool.or(String.is_empty(args), T.has_char(args, ' ')), Bad{at, "a malformed insert"}, next_op.insert(rest, at, T.number(args)))
        case False{}:
          match is_content:
            case True{}:
              Bad{at, "content without an operation"}
            case False{}:
              Bool.pick(Next, is_marker, Bad{at, "`\\ no newline` without an item above it"}, Bad{at, "an unknown operation: " ++ t})

def next_op.split(+rest: List<&2, T.Line>, +at: Nat, +t: String, cut: Maybe<&2, T.Split>) -> Next:
  match cut:
    case None{}:
      next_op.keyword(rest, at, t, SNil{}, T.same(t, "delete"), T.same(t, "insert"), Bool.or(String.starts_with(t, "-"), String.starts_with(t, "+")), T.same(t, "\\ no newline"))
    case Some{T.Split{+kw, args}}:
      next_op.keyword(rest, at, t, args, T.same(kw, "delete"), T.same(kw, "insert"), Bool.or(String.starts_with(t, "-"), String.starts_with(t, "+")), False{})

# The next operation under the walk, or the end, or a complaint. Whether it
# may follow what came before is `next_op.bounded`'s question.
def next_op(ls: List<&2, T.Line>, +at: Nat) -> Next:
  match ls:
    case Nil{}:
      End{}
    case T.Line{+t, False{}} <> rest:
      Bad{at, "unterminated line"}
    case T.Line{+t, True{}} <> rest:
      Bool.pick(Next, T.has_char(t, '\r'), Bad{at, "a carriage return in an operation line"}, next_op.split(rest, at, t, T.split_once(t)))

# Keep the last deleted region across inserts. Checking only the immediate
# predecessor would let a replacement hide an overlapping or adjacent delete.
def remember_delete(op: Op, previous: Maybe<&2, Op>) -> Maybe<&2, Op>:
  match op:
    case Op{Delete{}, at, items}:
      Some{Op{Delete{}, at, items}}
    case Op{Insert{}, at, items}:
      previous

# An operation may follow both the previous operation and the last delete.
# This is the only place the parser orders operations.
def next_op.bounded(prev: Maybe<&2, Op>, previous_delete: Maybe<&2, Op>, n: Next) -> Next:
  match n:
    case End{}:
      End{}
    case Bad{at, msg}:
      Bad{at, msg}
    case More{+op, rest, at}:
      next_op.fin(op, rest, at, Maybe.or(&2, String, ordered(prev, op), ordered(previous_delete, op)))

# Every operation. The fuel is the line count, which a step always eats into.
def parse.ops(fuel: Nat, n: Next, acc: List<&2, Op>, previous_delete: Maybe<&2, Op>) -> Result<&2, &2, String, List<&2, Op>>:
  match fuel n:
    case _ End{}:
      Done{List.reverse(&2, Op, acc)}
    case _ Bad{at, msg}:
      fail(List<&2, Op>, at, msg)
    case 0n _:
      Fail{"the walk ran out of lines"}
    case 1n+p More{+op, rest, at}:
      +deletion = remember_delete(op, previous_delete)
      parse.ops(p, next_op.bounded(Some{op}, deletion, next_op(rest, at)), op <> acc, deletion)

# A `\ no newline` may mark only the last item of the last operation of its
# kind: past it, nothing of that kind is left to count into.
def has_verb(ops: List<&2, Op>, +v: Verb) -> Bool:
  match ops:
    case Nil{}:
      False{}
    case Op{v2, at, items} <> rest:
      Bool.or(verb_is(v2, v), has_verb(rest, v))

def last_terminated(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}:
      True{}
    case Item{t, n, f} <> Nil{}:
      n
    case it <> rest:
      last_terminated(rest)

def markers_ok(ops: List<&2, Op>) -> Bool:
  match ops:
    case Nil{}:
      True{}
    case Op{v, at, +items} <> +rest:
      Bool.and(terminated_but_last(items), Bool.and(Bool.or(last_terminated(items), Bool.not(has_verb(rest, v))), markers_ok(rest)))

def parse.body(forgets: Maybe<&2, String>, result: Maybe<&2, String>, ops: Result<&2, &2, String, List<&2, Op>>) -> Result<&2, &2, String, Doc>:
  match ops:
    case Fail{e}:
      Fail{e}
    case Done{Nil{}}:
      Fail{"no operations"}
    case Done{+o <> +os}:
      Bool.pick(Result<&2, &2, String, Doc>, markers_ok(o <> os), Done{Doc{forgets, result, o <> os}}, Fail{"`\\ no newline` on an item that is not last"})

# The blank line every document has between its headers and its body.
def parse.separator(forgets: Maybe<&2, String>, result: Maybe<&2, String>, ls: List<&2, T.Line>, at: Nat) -> Result<&2, &2, String, Doc>:
  match ls:
    case T.Line{SNil{}, True{}} <> +rest:
      parse.body(forgets, result, parse.ops(1n+List.length(&2, T.Line, rest), next_op.bounded(None{}, None{}, next_op(rest, 1n+at)), Nil{}, None{}))
    case _:
      fail(Doc, at, "missing the blank line after the headers")

# A header that may be present: its value, and the lines after it.
type Headed is Data:
  Headed{value: Maybe<&2, String>, rest: List<&2, T.Line>, at: Nat}

def header.of(t: String, term: Bool, rest: List<&2, T.Line>, at: Nat, stripped: Maybe<&2, String>) -> Headed:
  match stripped:
    case None{}:
      Headed{None{}, T.Line{t, term} <> rest, at}
    case Some{value}:
      Headed{Some{value}, rest, 1n+at}

def header(ls: List<&2, T.Line>, at: Nat, key: String) -> Headed:
  match ls:
    case Nil{}:
      Headed{None{}, Nil{}, at}
    case T.Line{+t, +term} <> rest:
      header.of(t, term, rest, at, Bool.pick(Maybe<&2, String>, term, T.strip_prefix(t, key), None{}))

def valid_digest(v: Maybe<&2, String>) -> Bool:
  match v:
    case None{}:
      True{}
    case Some{d}:
      T.is_digest(d)

def parse.result(forgets: Maybe<&2, String>, h: Headed) -> Result<&2, &2, String, Doc>:
  match forgets h:
    case Some{f} Headed{Some{r}, rest, at}:
      fail(Doc, at, "a result beside forgets")
    case _ Headed{+result, rest, +at}:
      Bool.pick(Result<&2, &2, String, Doc>, valid_digest(result), parse.separator(forgets, result, rest, at), fail(Doc, at, "a malformed result"))

def parse.forgets(h: Headed) -> Result<&2, &2, String, Doc>:
  match h:
    case Headed{+forgets, rest, +at}:
      Bool.pick(Result<&2, &2, String, Doc>, valid_digest(forgets), parse.result(forgets, header(rest, at, "result ")), fail(Doc, at, "a malformed forgets"))

def parse.preamble(ls: List<&2, T.Line>) -> Result<&2, &2, String, Doc>:
  match ls:
    case T.Line{+t, True{}} <> rest:
      Bool.pick(Result<&2, &2, String, Doc>, T.same(t, "historica"), parse.forgets(header(rest, 2n, "forgets ")), fail(Doc, 1n, "not a historica document: " ++ t))
    case _:
      fail(Doc, 1n, "not a historica document")

# The Rust tool's words
# ---------------------
#
# `OperationDocument::parse` read over again in its own order, for what the
# parser above does not say the way the Rust tool does: which line a
# refused document is refused on, and why. The parser above decides whether
# a document is accepted; this only words a refusal. A `delete` reads the
# items it counts and no more, the headers are tried before the blank line,
# and every line is numbered as `Lines` numbers it — what a person reading
# the message and the file side by side needs to agree.

def w.fail(-A: Data, +line: Nat, +kind: String) -> Result<&2, &2, String, A>:
  Fail{W.at(line, kind)}

# What is left, and how many lines have been read.
type WAt is Data:
  WAt{rest: List<&2, T.Line>, n: Nat}

def w.header.value(+key: String, +forgetting: Bool, +term: Bool, +t: String, +value: String, +rest: List<&2, T.Line>, +at: Nat) -> Result<&2, &2, String, WAt>:
  Bool.pick(Result<&2, &2, String, WAt>, Bool.not(term), w.fail(WAt, at, W.unterminated()),
  Bool.pick(Result<&2, &2, String, WAt>, T.has_char(t, '\r'), w.fail(WAt, at, W.carriage_return_in_operation()),
  Bool.pick(Result<&2, &2, String, WAt>, forgetting, w.fail(WAt, at, W.result_of_forgetting()),
  Bool.pick(Result<&2, &2, String, WAt>, T.is_digest(value), Done{WAt{rest, at}}, w.fail(WAt, at, W.malformed_digest(key, value))))))

def w.header.of(+key: String, +forgetting: Bool, +t: String, +term: Bool, +rest: List<&2, T.Line>, +n: Nat, v: Maybe<&2, String>) -> Result<&2, &2, String, WAt>:
  match v:
    case None{}:
      Done{WAt{T.Line{t, term} <> rest, n}}
    case Some{+value}:
      w.header.value(key, forgetting, term, t, value, rest, 1n+n)

# `forgets` or `result`, if the next line is one; `forgetting` refuses a
# `result` beside a `forgets`.
def w.header(ls: List<&2, T.Line>, +n: Nat, +key: String, +forgetting: Bool) -> Result<&2, &2, String, WAt>:
  match ls:
    case Nil{}:
      Done{WAt{Nil{}, n}}
    case T.Line{+t, +term} <> +rest:
      w.header.of(key, forgetting, t, term, rest, n, T.strip_prefix(t, key ++ " "))

def w.stated(a: WAt, +n: Nat) -> Bool:
  match a:
    case WAt{r, m}:
      Bool.not(Nat.is_eq(m, n))

# The blank line, terminated or not.
def w.separator(ls: List<&2, T.Line>, +n: Nat) -> Result<&2, &2, String, WAt>:
  match ls:
    case Nil{}:
      w.fail(WAt, n, W.missing_separator())
    case T.Line{t, term} <> rest:
      Bool.pick(Result<&2, &2, String, WAt>, String.is_empty(t), Done{WAt{rest, 1n+n}}, w.fail(WAt, 1n+n, W.missing_separator()))

# An operation as ordering asks after it, and a `\ no newline` where it was.
type WOp is Data:
  WOp{delete: Bool, at: Nat, count: Nat}

type WMark is Data:
  WMark{op: Nat, item: Nat, line: Nat, prefix: Char}

# What a line under an operation is.
type WItem is Data:
  WItem.End{}
  WItem.Marker{}
  WItem.Item{term: Bool}

def w.item.of(ls: List<&2, T.Line>, +prefix: Char) -> WItem:
  match ls:
    case Nil{}:
      WItem.End{}
    case T.Line{+t, +term} <> rest:
      Bool.pick(WItem, T.same(t, "\\ no newline"), WItem.Marker{},
        Bool.pick(WItem, Bool.or(T.same(t, "\\ forgotten"), String.starts_with(t, String.from_list([prefix]))), WItem.Item{term}, WItem.End{}))

# Reading the items of one operation: what is left, the lines read, the
# items read, the markers so far, and whether the reading has stopped.
type WItems is Data:
  WItems{rest: List<&2, T.Line>, n: Nat, count: Nat, marks: List<&2, WMark>, done: Bool}

def w.marker.of(+t: String, +term: Bool, +rest: List<&2, T.Line>, +n: Nat, +count: Nat, +op: Nat, +prefix: Char, +marks: List<&2, WMark>) -> Result<&2, &2, String, WItems>:
  Bool.pick(Result<&2, &2, String, WItems>, T.same(t, "\\ no newline"),
    Bool.pick(Result<&2, &2, String, WItems>, term, Done{WItems{rest, 1n+n, 1n+count, List.append(&2, WMark, marks, [WMark{op, count, 1n+n, prefix}]), False{}}}, w.fail(WItems, 1n+n, W.unterminated())),
    Done{WItems{T.Line{t, term} <> rest, n, 1n+count, marks, False{}}})

# An item read, and the `\ no newline` under it if there is one.
def w.marker(ls: List<&2, T.Line>, +n: Nat, +count: Nat, +op: Nat, +prefix: Char, +marks: List<&2, WMark>) -> Result<&2, &2, String, WItems>:
  match ls:
    case Nil{}:
      Done{WItems{Nil{}, n, 1n+count, marks, False{}}}
    case T.Line{+t, +term} <> +rest:
      w.marker.of(t, term, rest, n, count, op, prefix, marks)

def w.tail(ls: List<&2, T.Line>) -> List<&2, T.Line>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      rest

def w.item.read(+ls: List<&2, T.Line>, +n: Nat, +count: Nat, +op: Nat, +prefix: Char, +marks: List<&2, WMark>, k: WItem) -> Result<&2, &2, String, WItems>:
  match k:
    case WItem.End{}:
      Done{WItems{ls, n, count, marks, True{}}}
    case WItem.Marker{}:
      w.fail(WItems, 1n+n, W.no_newline_without_item())
    case WItem.Item{term}:
      Bool.pick(Result<&2, &2, String, WItems>, term, w.marker(w.tail(ls), 1n+n, count, op, prefix, marks), w.fail(WItems, 1n+n, W.unterminated()))

def w.enough(expected: Maybe<&2, Nat>, +count: Nat) -> Bool:
  match expected:
    case None{}:
      False{}
    case Some{c}:
      Nat.is_eq(c, count)

def w.item.step(+prefix: Char, +expected: Maybe<&2, Nat>, +op: Nat, st: WItems) -> Result<&2, &2, String, WItems>:
  match st:
    case WItems{+ls, +n, +count, +marks, done}:
      Bool.pick(Result<&2, &2, String, WItems>, Bool.or(done, w.enough(expected, count)), Done{WItems{ls, n, count, marks, True{}}},
        w.item.read(ls, n, count, op, prefix, marks, w.item.of(ls, prefix)))

def w.items.go(fuel: Nat, +prefix: Char, +expected: Maybe<&2, Nat>, +op: Nat, r: Result<&2, &2, String, WItems>) -> Result<&2, &2, String, WItems>:
  match fuel r:
    case _ Fail{e}:
      Fail{e}
    case 0n Done{st}:
      Done{st}
    case 1n+p Done{st}:
      w.items.go(p, prefix, expected, op, w.item.step(prefix, expected, op, st))

# `items`: a `delete` reads the count it states and stops; an `insert`
# reads while the lines are its own. A count the lines do not reach is
# refused where the reading stopped.
def w.counted(expected: Maybe<&2, Nat>, r: Result<&2, &2, String, WItems>) -> Result<&2, &2, String, WItems>:
  match expected r:
    case _ Fail{e}:
      Fail{e}
    case None{} Done{st}:
      Done{st}
    case Some{+c} Done{WItems{+ls, +n, +count, marks, done}}:
      Bool.pick(Result<&2, &2, String, WItems>, Nat.is_eq(c, count), Done{WItems{ls, n, count, marks, done}}, w.fail(WItems, n, W.delete_count_disagrees(c, count)))

def w.items(+ls: List<&2, T.Line>, +n: Nat, +prefix: Char, +expected: Maybe<&2, Nat>, +op: Nat, +marks: List<&2, WMark>) -> Result<&2, &2, String, WItems>:
  w.counted(expected, w.items.go(1n+List.length(&2, T.Line, ls), prefix, expected, op, Done{WItems{ls, n, 0n, marks, False{}}}))

# One operation read: what it is, and where the reading got to.
type WRead is Data:
  WRead{op: WOp, rest: List<&2, T.Line>, n: Nat, marks: List<&2, WMark>}

def w.read.delete(+pos: Nat, r: Result<&2, &2, String, WItems>) -> Result<&2, &2, String, WRead>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{WItems{ls, n, count, marks, done}}:
      Done{WRead{WOp{True{}, pos, count}, ls, n, marks}}

def w.read.insert(+pos: Nat, +at: Nat, r: Result<&2, &2, String, WItems>) -> Result<&2, &2, String, WRead>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{WItems{ls, n, +count, marks, done}}:
      Bool.pick(Result<&2, &2, String, WRead>, Nat.is_eq(count, 0n), w.fail(WRead, at, W.empty_insert()), Done{WRead{WOp{False{}, pos, count}, ls, n, marks}})

def w.delete.numbers(+rest: List<&2, T.Line>, +at: Nat, +index: Nat, +marks: List<&2, WMark>, +pos: String, +cnt: String, p: Maybe<&2, Nat>, c: Maybe<&2, Nat>) -> Result<&2, &2, String, WRead>:
  match p c:
    case None{} _:
      w.fail(WRead, at, W.malformed_number(pos))
    case Some{x} None{}:
      w.fail(WRead, at, W.malformed_number(cnt))
    case Some{+x} Some{+y}:
      Bool.pick(Result<&2, &2, String, WRead>, Nat.is_eq(y, 0n), w.fail(WRead, at, W.empty_delete()),
        w.read.delete(x, w.items(rest, at, '-', Some{y}, index, marks)))

def w.delete.fields(+rest: List<&2, T.Line>, +at: Nat, +index: Nat, +marks: List<&2, WMark>, f: Maybe<&2, T.Split>) -> Result<&2, &2, String, WRead>:
  match f:
    case None{}:
      w.fail(WRead, at, W.malformed_delete())
    case Some{T.Split{+pos, +cnt}}:
      Bool.pick(Result<&2, &2, String, WRead>, T.has_char(cnt, ' '), w.fail(WRead, at, W.malformed_delete()),
        w.delete.numbers(rest, at, index, marks, pos, cnt, T.number(pos), T.number(cnt)))

def w.insert.number(+rest: List<&2, T.Line>, +at: Nat, +index: Nat, +marks: List<&2, WMark>, +args: String, p: Maybe<&2, Nat>) -> Result<&2, &2, String, WRead>:
  match p:
    case None{}:
      w.fail(WRead, at, W.malformed_number(args))
    case Some{+x}:
      w.read.insert(x, at, w.items(rest, at, '+', None{}, index, marks))

def w.first(t: String) -> Char:
  match t:
    case SNil{}:
      ' '
    case SCon{c, r}:
      c

# `operation`: the keyword, then what it takes.
def w.op(+t: String, +kw: String, +args: String, +rest: List<&2, T.Line>, +at: Nat, +index: Nat, +marks: List<&2, WMark>) -> Result<&2, &2, String, WRead>:
  +cr = T.has_char(t, '\r')
  Bool.pick(Result<&2, &2, String, WRead>, T.same(kw, "delete"),
    Bool.pick(Result<&2, &2, String, WRead>, cr, w.fail(WRead, at, W.carriage_return_in_operation()), w.delete.fields(rest, at, index, marks, T.split_once(args))),
  Bool.pick(Result<&2, &2, String, WRead>, T.same(kw, "insert"),
    Bool.pick(Result<&2, &2, String, WRead>, cr, w.fail(WRead, at, W.carriage_return_in_operation()),
      Bool.pick(Result<&2, &2, String, WRead>, Bool.or(String.is_empty(args), T.has_char(args, ' ')), w.fail(WRead, at, W.malformed_insert()), w.insert.number(rest, at, index, marks, args, T.number(args)))),
  Bool.pick(Result<&2, &2, String, WRead>, Bool.or(String.starts_with(t, "-"), String.starts_with(t, "+")), w.fail(WRead, at, W.content_without_operation(w.first(t))),
  Bool.pick(Result<&2, &2, String, WRead>, T.same(t, "\\ no newline"), w.fail(WRead, at, W.no_newline_without_item()),
  Bool.pick(Result<&2, &2, String, WRead>, cr, w.fail(WRead, at, W.carriage_return_in_operation()), w.fail(WRead, at, W.unknown_operation(t)))))))

def w.op.cut(+t: String, +rest: List<&2, T.Line>, +at: Nat, +index: Nat, +marks: List<&2, WMark>, cut: Maybe<&2, T.Split>) -> Result<&2, &2, String, WRead>:
  match cut:
    case None{}:
      w.op(t, t, SNil{}, rest, at, index, marks)
    case Some{T.Split{+kw, +args}}:
      w.op(t, kw, args, rest, at, index, marks)

# `ordered`: one operation held against the one before it.
def w.op.at(o: WOp) -> Nat:
  match o:
    case WOp{d, a, c}:
      a

def w.ordered.same(prev: WOp, next: WOp) -> Maybe<&2, String>:
  match prev next:
    case WOp{True{}, a, c} WOp{False{}, b, d}:
      None{}
    case WOp{True{}, a, c} WOp{True{}, +b, d}:
      Some{W.overlapping(b)}
    case WOp{False{}, a, c} WOp{True{}, +b, d}:
      Some{W.delete_after_insert(b)}
    case WOp{False{}, a, c} WOp{False{}, +b, d}:
      Some{W.inserts_at_one_position(b)}

def w.ordered.after(prev: WOp, next: WOp) -> Maybe<&2, String>:
  match prev next:
    case WOp{False{}, a, c} _:
      None{}
    case WOp{True{}, +a, +c} WOp{nd, +b, +d}:
      +end = Nat.add(a, c)
      Bool.pick(Maybe<&2, String>, Nat.is_lt(b, end), Some{W.overlapping(b)},
        Bool.pick(Maybe<&2, String>, Bool.and(Nat.is_eq(b, end), nd), Some{W.adjacent_deletes(a, Nat.add(c, d))}, None{}))

def w.ordered.cmp(+prev: WOp, +next: WOp, c: Cmp) -> Maybe<&2, String>:
  match c:
    case LT{}:
      Some{W.operations_out_of_order(w.op.at(next), w.op.at(prev))}
    case EQ{}:
      w.ordered.same(prev, next)
    case GT{}:
      w.ordered.after(prev, next)

def w.ordered(prev: Maybe<&2, WOp>, +next: WOp) -> Maybe<&2, String>:
  match prev:
    case None{}:
      None{}
    case Some{+p}:
      w.ordered.cmp(p, next, Nat.cmp(w.op.at(next), w.op.at(p)))

# Reading the operations: what is left, the lines read, the operations in
# order, the last `delete`, the markers, and whether the reading stopped.
type WOps is Data:
  WOps{rest: List<&2, T.Line>, n: Nat, ops: List<&2, WOp>, last_delete: Maybe<&2, WOp>, marks: List<&2, WMark>, done: Bool}

def w.last(os: List<&2, WOp>) -> Maybe<&2, WOp>:
  match os:
    case Nil{}:
      None{}
    case o <> Nil{}:
      Some{o}
    case o <> rest:
      w.last(rest)

def w.is_delete(o: WOp) -> Bool:
  match o:
    case WOp{d, a, c}:
      d

def w.op.added(+at: Nat, +ops: List<&2, WOp>, +last_delete: Maybe<&2, WOp>, r: Result<&2, &2, String, WRead>) -> Result<&2, &2, String, WOps>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{WRead{+o, rest, n, marks}}:
      Maybe.default(&2, Result<&2, &2, String, WOps>,
        Maybe.map(&2, String, Result<&2, &2, String, WOps>, e => Fail{W.at(at, e)}, Maybe.or(&2, String, w.ordered(w.last(ops), o), w.ordered(last_delete, o))),
        Done{WOps{rest, n, List.append(&2, WOp, ops, [o]), Bool.pick(Maybe<&2, WOp>, w.is_delete(o), Some{o}, last_delete), marks, False{}}})

def w.ops.line(+ops: List<&2, WOp>, +last_delete: Maybe<&2, WOp>, +marks: List<&2, WMark>, ls: List<&2, T.Line>, +n: Nat) -> Result<&2, &2, String, WOps>:
  match ls:
    case Nil{}:
      Done{WOps{Nil{}, n, ops, last_delete, marks, True{}}}
    case T.Line{+t, term} <> +rest:
      Bool.pick(Result<&2, &2, String, WOps>, term,
        w.op.added(1n+n, ops, last_delete, w.op.cut(t, rest, 1n+n, List.length(&2, WOp, ops), marks, T.split_once(t))),
        w.fail(WOps, 1n+n, W.unterminated()))

def w.ops.step(st: WOps) -> Result<&2, &2, String, WOps>:
  match st:
    case WOps{+ls, +n, +ops, +ld, +marks, done}:
      Bool.pick(Result<&2, &2, String, WOps>, done, Done{WOps{ls, n, ops, ld, marks, True{}}}, w.ops.line(ops, ld, marks, ls, n))

def w.ops.go(fuel: Nat, r: Result<&2, &2, String, WOps>) -> Result<&2, &2, String, WOps>:
  match fuel r:
    case _ Fail{e}:
      Fail{e}
    case 0n Done{st}:
      Done{st}
    case 1n+p Done{st}:
      w.ops.go(p, w.ops.step(st))

# `check_markers`: a marker marks its kind's last item.
def w.kind.in(os: List<&2, WOp>, +delete: Bool) -> Bool:
  match os:
    case Nil{}:
      False{}
    case o <> rest:
      Bool.or(Bool.not(Bool.xor(w.is_delete(o), delete)), w.kind.in(rest, delete))

def w.later(os: List<&2, WOp>, +i: Nat, +delete: Bool) -> Bool:
  match os i:
    case Nil{} _:
      False{}
    case o <> rest 0n:
      w.kind.in(rest, delete)
    case o <> rest 1n+j:
      w.later(rest, j, delete)

def w.count(o: Maybe<&2, WOp>) -> Nat:
  match o:
    case None{}:
      0n
    case Some{WOp{d, a, c}}:
      c

def w.marks(+os: List<&2, WOp>, ms: List<&2, WMark>) -> Maybe<&2, String>:
  match ms:
    case Nil{}:
      None{}
    case WMark{+op, +item, +line, +prefix} <> rest:
      +o = List.get(&2, WOp, os, op)
      +last = Bool.and(Nat.is_eq(1n+item, w.count(o)), Bool.not(w.later(os, op, Maybe.default(&2, Bool, Maybe.map(&2, WOp, Bool, x => w.is_delete(x), o), False{}))))
      Bool.pick(Maybe<&2, String>, last, w.marks(os, rest), Some{W.at(line, W.no_newline_not_last(prefix))})

def w.body(r: Result<&2, &2, String, WOps>) -> Maybe<&2, String>:
  match r:
    case Fail{e}:
      Some{e}
    case Done{WOps{ls, +n, +ops, ld, marks, done}}:
      Bool.pick(Maybe<&2, String>, List.is_empty(&2, WOp, ops), Some{W.at(n, W.no_operations())}, w.marks(ops, marks))

def w.after(r: Result<&2, &2, String, WAt>) -> Maybe<&2, String>:
  match r:
    case Fail{e}:
      Some{e}
    case Done{WAt{+ls, +n}}:
      w.body(w.ops.go(1n+List.length(&2, T.Line, ls), Done{WOps{ls, n, Nil{}, None{}, Nil{}, False{}}}))

def w.separator.at(a: WAt) -> Result<&2, &2, String, WAt>:
  match a:
    case WAt{ls, n}:
      w.separator(ls, n)

def w.results(r: Result<&2, &2, String, WAt>, +forgetting: Bool) -> Maybe<&2, String>:
  match r:
    case Fail{e}:
      Some{e}
    case Done{WAt{+ls, +n}}:
      w.after(Result.bind(&2, &2, String, WAt, WAt, w.header(ls, n, "result", forgetting), a => w.separator.at(a)))

def w.forgets(ls: List<&2, T.Line>) -> Maybe<&2, String>:
  +h = w.header(ls, 1n, "forgets", False{})
  w.results(h, Result.default(&2, &2, String, Bool, Result.map(&2, &2, String, WAt, Bool, a => w.stated(a, 1n), h), False{}))

def w.first.line(ls: List<&2, T.Line>) -> Maybe<&2, String>:
  match ls:
    case Nil{}:
      Some{W.at(1n, W.empty())}
    case T.Line{+t, +term} <> rest:
      Bool.pick(Maybe<&2, String>, T.has_char(t, '\r'), Some{W.at(1n, W.carriage_return_in_operation())},
        Maybe.or(&2, String, W.preamble(t, term), w.forgets(rest)))

# Why the Rust tool refuses these bytes as an operation document, in its
# words: none where it would not.
def refusal(+s: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, W.bom(s), Some{W.at(1n, W.byte_order_mark())}, w.first.line(T.lines(s)))

# A refusal from the parser above, worded as the Rust tool words it.
def worded(+s: String, r: Result<&2, &2, String, Doc>) -> Result<&2, &2, String, Doc>:
  match r:
    case Done{d}:
      Done{d}
    case Fail{e}:
      Fail{Maybe.default(&2, String, refusal(s), e)}

# An operation document, from its text.
def parse(+s: String) -> Result<&2, &2, String, Doc>:
  worded(s, parse.preamble(T.lines(s)))

# Writing
# -------

def write_item(+p: Char, it: Item) -> String:
  match it:
    case Item{tx, n, f}:
      Bool.pick(String, f, "\\ forgotten\n", String.from_list([p]) ++ tx ++ "\n") ++ Bool.pick(String, n, SNil{}, "\\ no newline\n")

def write_items(+p: Char, items: List<&2, Item>) -> String:
  match items:
    case Nil{}:
      SNil{}
    case it <> rest:
      write_item(p, it) ++ write_items(p, rest)

def write_op(op: Op) -> String:
  match op:
    case Op{Delete{}, at, +items}:
      "delete " ++ T.spell(at) ++ " " ++ T.spell(List.length(&2, Item, items)) ++ "\n" ++ write_items('-', items)
    case Op{Insert{}, at, items}:
      "insert " ++ T.spell(at) ++ "\n" ++ write_items('+', items)

def write_ops(ops: List<&2, Op>) -> String:
  match ops:
    case Nil{}:
      SNil{}
    case op <> rest:
      write_op(op) ++ write_ops(rest)

def header_line(key: String, v: Maybe<&2, String>) -> String:
  match v:
    case None{}:
      SNil{}
    case Some{d}:
      key ++ " " ++ d ++ "\n"

# The exact bytes of a document: `write(parse(s)) == s` for every `s` parse
# accepts, since the parser admits one spelling.
def write(doc: Doc) -> String:
  match doc:
    case Doc{forgets, result, ops}:
      "historica\n" ++ header_line("forgets", forgets) ++ header_line("result", result) ++ "\n" ++ write_ops(ops)

# Replay
# ------

# `n` items moved from the state onto the accumulator, which is reversed.
type Advanced is Data:
  Advanced{acc: List<&2, Item>, rest: List<&2, Item>}

def advance(n: Nat, state: List<&2, Item>, acc: List<&2, Item>) -> Advanced:
  match n state:
    case 0n _:
      Advanced{acc, state}
    case 1n+p Nil{}:
      Advanced{acc, Nil{}}
    case 1n+p it <> rest:
      advance(p, rest, it <> acc)

# How many items an advance holds, kept and left together.
def advance_width(a: Advanced) -> Nat:
  match a:
    case Advanced{acc, rest}:
      Nat.add(List.length(&2, Item, acc), List.length(&2, Item, rest))

# The state past a deleted run, and whether the run was what the document
# quoted.
type Dropped is Data:
  Dropped{rest: List<&2, Item>, agreed: Bool}

def drop_checked(recorded: List<&2, Item>, state: List<&2, Item>, ok: Bool) -> Dropped:
  match recorded state:
    case Nil{} _:
      Dropped{state, ok}
    case r <> rs Nil{}:
      Dropped{Nil{}, False{}}
    case r <> rs s <> ss:
      drop_checked(rs, ss, Bool.and(ok, agrees(r, s)))

# The walk brought up to the next operation: the items before it kept, and
# if it is a delete, its run dropped and checked. Done before the walk's
# step so the step matches only what a pattern bound.
type Landed is Data:
  Landed{acc: List<&2, Item>, rest: List<&2, Item>, agreed: Bool}

def land.dropped(acc: List<&2, Item>, d: Dropped) -> Landed:
  match d:
    case Dropped{rest, agreed}:
      Landed{acc, rest, agreed}

def land.delete(items: List<&2, Item>, adv: Advanced) -> Landed:
  match adv:
    case Advanced{acc, state}:
      land.dropped(acc, drop_checked(items, state, True{}))

def land.insert(adv: Advanced) -> Landed:
  match adv:
    case Advanced{acc, state}:
      Landed{acc, state, True{}}

def land(ops: List<&2, Op>, pos: Nat, state: List<&2, Item>, acc: List<&2, Item>) -> Landed:
  match ops:
    case Nil{}:
      Landed{acc, state, True{}}
    case Op{Insert{}, at, items} <> rest:
      land.insert(advance(Nat.sub(at, pos), state, acc))
    case Op{Delete{}, at, items} <> rest:
      land.delete(items, advance(Nat.sub(at, pos), state, acc))

# `pos` is how far into the parent the walk has come. An insert never moves
# it, and an insert that follows a delete at the same position counts from
# before the run the delete removed, which the walk is already past.
def apply.go(ops: List<&2, Op>, l: Landed, +pos: Nat, err: Maybe<&2, String>) -> Result<&2, &2, String, List<&2, Item>>:
  match ops l:
    case Nil{} Landed{acc, state, agreed}:
      match err:
        case None{}:
          Done{List.append(&2, Item, List.reverse(&2, Item, acc), state)}
        case Some{e}:
          Fail{e}
    case Op{Insert{}, +at, items} <> +rest Landed{acc, state, agreed}:
      +pos2 = Nat.max(pos, at)
      apply.go(rest, land(rest, pos2, state, List.append(&2, Item, List.reverse(&2, Item, items), acc)), pos2, err)
    case Op{Delete{}, +at, items} <> +rest Landed{acc, state, agreed}:
      +pos2 = Nat.add(at, List.length(&2, Item, items))
      apply.go(rest, land(rest, pos2, state, acc), pos2,
        Maybe.or(&2, String, err, Bool.pick(Maybe<&2, String>, agreed, None{}, Some{"a delete at " ++ Nat.show(at) ++ " quotes lines the parent does not hold"})))

def in_range(ops: List<&2, Op>, +len: Nat) -> Bool:
  match ops:
    case Nil{}:
      True{}
    case op <> rest:
      Bool.and(Nat.is_le(end(op), len), in_range(rest, len))

def check_result.of(+stated: String, forgot: Bool, +found: String) -> Result<&2, &2, String, Unit>:
  match forgot:
    case True{}:
      Done{Unit{}}
    case False{}:
      Bool.pick(Result<&2, &2, String, Unit>, T.same(stated, found), Done{Unit{}}, Fail{"the result stated is " ++ stated ++ " but the replay produced " ++ found})

# Decision 0031: a replay is held to the digest the document states, except
# where forgetting has put bytes in the file that nobody hashed.
def check_result(result: Maybe<&2, String>, +items: List<&2, Item>) -> Result<&2, &2, String, Unit>:
  match result:
    case None{}:
      Done{Unit{}}
    case Some{stated}:
      check_result.of(stated, any_forgotten(items), state_digest(items))

def apply.checked(result: Maybe<&2, String>, +items: List<&2, Item>) -> Result<&2, &2, String, List<&2, Item>>:
  do Result<&2, &2, String, List<&2, Item>>:
    ensure(terminated_but_last(items), 0n, "an item without a newline that is not the last")
    check_result(result, items)
    return items

# The parent state with the document's operations applied, or why not.
# The cursor walk requires parser-ordered operations. A hand-built Doc must
# obey the same ordering/non-overlap rules; Spec.result has no such cursor.
def apply(+state: List<&2, Item>, doc: Doc) -> Result<&2, &2, String, List<&2, Item>>:
  match doc:
    case Doc{forgets, result, +ops}:
      do Result<&2, &2, String, List<&2, Item>>:
        Bool.pick(Result<&2, &2, String, Unit>, in_range(ops, List.length(&2, Item, state)), Done{Unit{}}, Fail{"an operation counts past the end of the parent"})
        items : List<&2, Item> <- apply.go(ops, land(ops, 0n, state, Nil{}), 0n, None{})
        apply.checked(result, items)

# Blocks
# ------

# An edit block: what one delete, one insert, or a delete and the insert
# that replaces it does at one position.
type Edit is Data:
  Insertion{items: List<&2, Item>}
  Deletion{recorded: List<&2, Item>}
  Replacement{recorded: List<&2, Item>, inserted: List<&2, Item>}

def operations(+at: Nat, edit: Edit) -> List<&2, Op>:
  match edit:
    case Insertion{items}:
      [Op{Insert{}, at, items}]
    case Deletion{recorded}:
      [Op{Delete{}, at, recorded}]
    case Replacement{recorded, inserted}:
      [Op{Delete{}, at, recorded}, Op{Insert{}, at, inserted}]

# A document as a script of blocks. Each block sits `gap` parent items past
# where the previous block finished, so the blocks never overlap and never
# run backwards: the shape the parser's ordering rules admit.
type Step is Data:
  Step{gap: Nat, edit: Edit}

# How many parent items a block removes; the next block counts from there.
def consumed(edit: Edit) -> Nat:
  match edit:
    case Insertion{items}:
      0n
    case Deletion{recorded}:
      List.length(&2, Item, recorded)
    case Replacement{recorded, inserted}:
      List.length(&2, Item, recorded)

# What a block puts where the consumed items were.
def inserted(edit: Edit) -> List<&2, Item>:
  match edit:
    case Insertion{items}:
      items
    case Deletion{recorded}:
      Nil{}
    case Replacement{recorded, items}:
      items

def script(steps: List<&2, Step>, +at: Nat) -> List<&2, Op>:
  match steps:
    case Nil{}:
      Nil{}
    case Step{gap, +edit} <> rest:
      +here = Nat.add(at, gap)
      List.append(&2, Op, operations(here, edit), script(rest, Nat.add(here, consumed(edit))))

# Diff
# ----

# The writing half: the operations that take one state to another, by the
# longest common subsequence of their items. Applying the answer to the
# parent reproduces the child; the decomposition is this tool's judgement.

def item_at(items: List<&2, Item>, n: Nat) -> Item:
  match items n:
    case Nil{} _:
      forgotten()
    case it <> rest 0n:
      it
    case it <> rest 1n+p:
      item_at(rest, p)

# Interning
# ---------

# The table asks the same question of the same two items over and over —
# `same`, which walks two lines character by character — once for every one
# of its (n+1)(m+1) cells. So each item takes a number first, and the cells
# compare numbers: the number is the item's identity, and two items take the
# same one exactly when `same` holds of them.
#
# `same` is text and terminator together, and is false of a forgotten item
# whatever it is compared with, itself included. So the key is the
# terminator written in front of the text, and a forgotten item is not keyed
# at all — it takes a fresh number, which nothing else can hold.
#
# The keys are a `Map`, which is a trie over the key's own characters: the
# numbering is the items' first-seen order and nothing is hashed, so two
# runs of the same diff give the same table.
type Pool is Data:
  Pool{seen: Map<&2, U32>, next: U32}

def pool() -> Pool:
  Pool{Map.new(&2, U32), 1}

# A number nothing else holds, for an item that is nobody's line.
def intern.fresh(p: Pool) -> Pool & U32:
  match p:
    case Pool{seen, +n}:
      (Pool{seen, (n + 1 : U32)}, n)

def intern.known(p: Pool, +k: String, +held: U32) -> Pool & U32:
  match p:
    case Pool{+seen, +n}:
      Bool.pick(Pool & U32, U32.is_eq(held, 0), (Pool{Map.set(&2, U32, seen, k, n), (n + 1 : U32)}, n), (Pool{seen, n}, held))

def intern.at(p: Pool, +k: String, r: Map<&2, U32> & U32) -> Pool & U32:
  (m, held) = r
  intern.known(p, k, held)

def intern.keyed(p: Pool, +k: String) -> Pool & U32:
  match p:
    case Pool{+seen, next}:
      intern.at(Pool{seen, next}, k, Map.get(U32, 0, seen, k))

def intern.text(p: Pool, +text: String, terminated: Bool) -> Pool & U32:
  intern.keyed(p, SCon{Bool.pick(Char, terminated, Chr{116}, Chr{102}), text})

def intern.item(p: Pool, text: String, terminated: Bool, forgotten: Bool) -> Pool & U32:
  match forgotten:
    case True{}:
      intern.fresh(p)
    case False{}:
      intern.text(p, text, terminated)

def intern.one(p: Pool, it: Item) -> Pool & U32:
  match it:
    case Item{text, terminated, forgotten}:
      intern.item(p, text, terminated, forgotten)

# The items numbered in order. The pool threads through as the pair the last
# item returned, so the walk is one function and the numbers come out
# reversed, to be turned round once at the end.
def intern.go(items: List<&2, Item>, r: Pool & U32, acc: List<&2, U32>) -> Pool & List<&2, U32>:
  match items r:
    case Nil{} Tuple{p, h}:
      (p, List.reverse(&2, U32, h <> acc))
    case it <> rest Tuple{p, h}:
      intern.go(rest, intern.one(p, it), h <> acc)

def intern(items: List<&2, Item>, p: Pool) -> Pool & List<&2, U32>:
  match items:
    case Nil{}:
      (p, Nil{})
    case it <> rest:
      intern.go(rest, intern.one(p, it), Nil{})

# The table
# ---------

def u32_at(xs: List<&2, U32>, n: Nat) -> U32:
  match xs n:
    case Nil{} _:
      0
    case x <> rest 0n:
      x
    case x <> rest 1n+p:
      u32_at(rest, p)

def cell(table: List<&2, List<&2, U32>>, i: Nat, j: Nat) -> U32:
  match table i:
    case Nil{} _:
      0
    case row <> rest 0n:
      u32_at(row, j)
    case row <> rest 1n+p:
      cell(rest, p, j)

# The next row of the table from the one above it: `prev` is that row from
# column j on, and `left` the cell just filled in this row. A cell counts a
# common subsequence, so it is a number rather than a `Nat`: the counts here
# run to the length of the file, and a unary `Nat.max` of two of them costs
# what it counts.
def next_row(new: List<&2, U32>, prev: List<&2, U32>, +x: U32, +left: U32) -> List<&2, U32>:
  match new prev:
    case y <> ys d <> +u <> rest:
      +v = Bool.pick(U32, U32.is_eq(x, y), (d + 1 : U32), Bool.pick(U32, U32.is_ge(u, left), u, left))
      v <> next_row(ys, u <> rest, x, v)
    case _ _:
      Nil{}

def rows(old: List<&2, U32>, +new: List<&2, U32>, prev: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match old:
    case Nil{}:
      Nil{}
    case x <> xs:
      +row = {0 <> next_row(new, prev, x, 0) : List<&2, U32>}
      row <> rows(xs, new, row)

def table.of(old: List<&2, U32>, +new: List<&2, U32>) -> List<&2, List<&2, U32>>:
  +zeros = List.replicate(U32, 1n+List.length(&2, U32, new), 0)
  zeros <> rows(old, new, zeros)

def table.both(+oi: List<&2, U32>, r: Pool & List<&2, U32>) -> List<&2, List<&2, U32>>:
  (p, +ni) = r
  table.of(oi, ni)

def table.ids(new: List<&2, Item>, r: Pool & List<&2, U32>) -> List<&2, List<&2, U32>>:
  (p, +oi) = r
  table.both(oi, intern(new, p))

# Row i, column j is the length of the longest common subsequence of the
# first i old items and the first j new ones.
def table(old: List<&2, Item>, new: List<&2, Item>) -> List<&2, List<&2, U32>>:
  table.ids(new, intern(old, pool()))

# The cell the backtrack stands on
# --------------------------------

# `cell` is what a cell of the table means, and what the zipper below
# answers; nothing calls it any more. It walked the table from row zero and
# the row from column zero for every question, and the backtrack asks two of
# them at every one of its (n+m) steps, so the walk cost the table's own size
# over again — two thirds of `diff`'s second and a half on three thousand
# lines.
#
# The backtrack only ever moves to (i-1, j), (i, j-1) or (i-1, j-1), so it
# needs no random access at all: it needs the cell it stands on, the one left
# of it, and the one above it. The zipper holds the current row and the row
# above it, each reversed and cut at the current column, so that the cell,
# its neighbour and the step left are all the head of a list; the rows below
# stay as they were built, and one of them is cut when the walk drops a row.
# A step left is free, and a step up costs the column it is at, which is what
# the reversal of one row costs and is paid once per row rather than twice
# per cell.
#
# `Zip` is threaded through `step` and `backtrack` the way the table was.
# `diff_lemmas.back` never looks inside either: the verdict's `up_wins` is
# generalised as a `Bool`, so the lemma carries the zipper where it carried
# the table, and moves it by the same three functions the walk does.
type Zip is Data:
  Zip{cur: List<&2, U32>, above: List<&2, U32>, below: List<&2, List<&2, U32>>, at: U32}

# The first `n` of a row, reversed: the row cut at a column, head first.
def rev_take(row: List<&2, U32>, +n: U32, acc: List<&2, U32>, more: Bool) -> List<&2, U32>:
  match row more:
    case Nil{} False{}:
      acc
    case Nil{} True{}:
      acc
    case x <> rest False{}:
      acc
    case x <> rest True{}:
      rev_take(rest, (n - 1 : U32), x <> acc, U32.is_gt(n, 1))

def rev_pre(row: List<&2, U32>, +n: U32) -> List<&2, U32>:
  rev_take(row, n, Nil{}, U32.is_gt(n, 0))

def u_head(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case x <> rest:
      x

def u_tail(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      rest

def row_head(rs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      r

def row_tail(rs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      rest

# The cell above, and the cell to the left.
def zip.up(z: Zip) -> U32:
  match z:
    case Zip{cur, above, below, at}:
      u_head(above)

def zip.left(z: Zip) -> U32:
  match z:
    case Zip{cur, above, below, at}:
      u_head(u_tail(cur))

# One column left: both rows lose their head, and the rows below stand.
def zip.left_move(z: Zip) -> Zip:
  match z:
    case Zip{cur, above, below, at}:
      Zip{u_tail(cur), u_tail(above), below, (at - 1 : U32)}

# One row up: the row above becomes the row, and the row below it is cut at
# the column the walk is still at.
def zip.up_move(z: Zip) -> Zip:
  match z:
    case Zip{cur, above, +below, +at}:
      Zip{above, rev_pre(row_head(below), (at + 1 : U32)), row_tail(below), at}

# Up and left at once: the row above loses its head as it becomes the row.
def zip.diag(z: Zip) -> Zip:
  match z:
    case Zip{cur, above, +below, +at}:
      Zip{u_tail(above), rev_pre(row_head(below), at), row_tail(below), (at - 1 : U32)}

# The zipper at the last cell: the table with its rows in reverse, the last
# two of them cut at the last column.
def zip.of(+rs: List<&2, List<&2, U32>>, +m: U32) -> Zip:
  Zip{rev_pre(row_head(rs), (m + 1 : U32)),
      rev_pre(row_head(row_tail(rs)), (m + 1 : U32)),
      row_tail(row_tail(rs)), m}

def zip.start(old: List<&2, Item>, new: List<&2, Item>, +m: Nat) -> Zip:
  zip.of(List.reverse(&2, List<&2, U32>, table(old, new)), U32.from_nat(m))

# Which way the backtrack goes from a cell.
type Verdict is Data:
  Diag{}
  Up{}
  Left{}
  Stop{}

def step.of(matched: Bool, up_wins: Bool) -> Verdict:
  match matched:
    case True{}:
      Diag{}
    case False{}:
      Bool.pick(Verdict, up_wins, Up{}, Left{})

def step(+old: List<&2, Item>, +new: List<&2, Item>, +z: Zip, i: Nat, j: Nat) -> Verdict:
  match i j:
    case 0n 0n:
      Stop{}
    case 0n 1n+q:
      Left{}
    case 1n+p 0n:
      Up{}
    case 1n+p 1n+q:
      +p = p
      +q = q
      step.of(same(item_at(old, p), item_at(new, q)), U32.is_ge(zip.up(z), zip.left(z)))

type Move is Data:
  Keep{}
  Del{x: Item}
  Ins{y: Item}

# From the last cell back to the first, collecting the edit script forwards.
def backtrack(fuel: Nat, v: Verdict, i: Nat, j: Nat, +old: List<&2, Item>, +new: List<&2, Item>, +z: Zip, script: List<&2, Move>) -> List<&2, Move>:
  match fuel v:
    case _ Stop{}:
      script
    case 0n _:
      script
    case 1n+f Diag{}:
      +i2 = Nat.sub(i, 1n)
      +j2 = Nat.sub(j, 1n)
      +z2 = zip.diag(z)
      backtrack(f, step(old, new, z2, i2, j2), i2, j2, old, new, z2, Keep{} <> script)
    case 1n+f Up{}:
      +i2 = Nat.sub(i, 1n)
      +j = j
      +z2 = zip.up_move(z)
      backtrack(f, step(old, new, z2, i2, j), i2, j, old, new, z2, Del{item_at(old, i2)} <> script)
    case 1n+f Left{}:
      +j2 = Nat.sub(j, 1n)
      +i = i
      +z2 = zip.left_move(z)
      backtrack(f, step(old, new, z2, i, j2), i, j2, old, new, z2, Ins{item_at(new, j2)} <> script)

def edits(+old: List<&2, Item>, +new: List<&2, Item>) -> List<&2, Move>:
  +n = List.length(&2, Item, old)
  +m = List.length(&2, Item, new)
  +z = zip.start(old, new, m)
  backtrack(Nat.add(n, m), step(old, new, z, n, m), n, m, old, new, z, Nil{})

# The block a run of edits makes: minus lines above plus lines, both
# anchored where the run began, so a replacement is one block.
def block(dels: List<&2, Item>, ins: List<&2, Item>) -> Edit:
  match dels ins:
    case Nil{} ins:
      Insertion{ins}
    case d <> ds Nil{}:
      Deletion{d <> ds}
    case d <> ds i <> it:
      Replacement{d <> ds, i <> it}

# Between one block and the next, how many lines were kept. A run ends at a
# kept line, which lengthens the gap when no run is open and otherwise
# starts the next gap, or at the end; deleted and inserted lines arrive
# reversed.
def runs.close(+gap: Nat, dels: List<&2, Item>, ins: List<&2, Item>, rest: List<&2, Step>) -> List<&2, Step>:
  match dels ins:
    case Nil{} Nil{}:
      rest
    case _ _:
      Step{gap, block(List.reverse(&2, Item, dels), List.reverse(&2, Item, ins))} <> rest

def runs(edits: List<&2, Move>, +gap: Nat, dels: List<&2, Item>, ins: List<&2, Item>) -> List<&2, Step>:
  match edits:
    case Nil{}:
      runs.close(gap, dels, ins, Nil{})
    case Keep{} <> rest:
      match dels ins:
        case Nil{} Nil{}:
          runs(rest, 1n+gap, Nil{}, Nil{})
        case _ _:
          Step{gap, block(List.reverse(&2, Item, dels), List.reverse(&2, Item, ins))} <> runs(rest, 1n, Nil{}, Nil{})
    case Del{x} <> rest:
      runs(rest, gap, x <> dels, ins)
    case Ins{y} <> rest:
      runs(rest, gap, dels, y <> ins)

def diff.of(ops: List<&2, Op>, result: String) -> Maybe<&2, Doc>:
  match ops:
    case Nil{}:
      None{}
    case op <> rest:
      Some{Doc{None{}, Some{result}, op <> rest}}

# The document that takes `parent` to `child`, or None where they agree.
def diff(parent: List<&2, Item>, +child: List<&2, Item>) -> Maybe<&2, Doc>:
  diff.of(script(runs(edits(parent, child), 0n, Nil{}, Nil{}), 0n), state_digest(child))
