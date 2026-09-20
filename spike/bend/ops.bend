# The operation document: what one revision did to one file, and the file
# materialised by replaying it. Positions are indices into the parent state,
# counted from zero, and none of them move; a delete quotes what it removed,
# so a document that disagrees with the parent it claims to edit is caught at
# replay rather than absorbed.

import Base
import ./text.bend as T
import ./utf8.bend as Utf8
import ./sha256.bend as Sha

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
      Bool.and(Bool.not(Bool.xor(n1, n2)), Bool.or(Bool.or(f1, f2), String.eq(t1, t2)))

# Whether two items are the same line, for the diff. A forgotten item is
# nobody's line.
def same(a: Item, b: Item) -> Bool:
  match a b:
    case Item{t1, n1, f1} Item{t2, n2, f2}:
      Bool.and(Bool.not(Bool.or(f1, f2)), Bool.and(String.eq(t1, t2), Bool.not(Bool.xor(n1, n2))))

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
  classify.of(T.strip_prefix(t, String.from_list([p])), String.eq(t, "\\ no newline"), String.eq(t, "\\ forgotten"))

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
    case T.Line{t, term} <> +rest NoNewline{}:
      match acc:
        case Item{t2, True{}, f2} <> acc_rest:
          take_items(rest, classify_head(rest, p), 1n+at, p, Item{t2, False{}, f2} <> acc_rest)
        case _:
          fail(Taken, at, "`\\ no newline` without an item above it")
    case T.Line{t, term} <> +rest Forgotten{}:
      take_items(rest, classify_head(rest, p), 1n+at, p, forgotten() <> acc)
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
def next_op.count(+prev: Maybe<&2, Op>, +op: Op, +n: Nat, rest: List<&2, T.Line>, at: Nat, at2: Nat, expected: Maybe<&2, Nat>) -> Next:
  match expected:
    case None{}:
      Bool.pick(Next, Nat.is_eq(n, 0n), Bad{at, "an insert with no items"}, next_op.fin(op, rest, at2, ordered(prev, op)))
    case Some{expected_n}:
      Bool.pick(Next, Nat.is_eq(n, expected_n), next_op.fin(op, rest, at2, ordered(prev, op)), Bad{at, "a delete whose count disagrees with its items"})

def next_op.items(+prev: Maybe<&2, Op>, verb: Verb, pos: Nat, expected: Maybe<&2, Nat>, at: Nat, taken: Result<&2, &2, String, Taken>) -> Next:
  match taken:
    case Fail{e}:
      Bad{at, e}
    case Done{Taken{rev, rest, at2}}:
      +items = List.reverse(&2, Item, rev)
      next_op.count(prev, Op{verb, pos, items}, List.length(&2, Item, items), rest, at, at2, expected)

def next_op.delete(+rest: List<&2, T.Line>, +at: Nat, +prev: Maybe<&2, Op>, pos: Maybe<&2, Nat>, count: Maybe<&2, Nat>, spaced: Bool) -> Next:
  match pos count spaced:
    case Some{p} Some{0n} False{}:
      Bad{at, "a delete of nothing"}
    case Some{p} Some{c} False{}:
      next_op.items(prev, Delete{}, p, Some{c}, at, take_items(rest, classify_head(rest, '-'), 1n+at, '-', Nil{}))
    case _ _ _:
      Bad{at, "a malformed delete"}

def next_op.delete_args(+rest: List<&2, T.Line>, +at: Nat, +prev: Maybe<&2, Op>, args: Maybe<&2, T.Split>) -> Next:
  match args:
    case None{}:
      Bad{at, "a malformed delete"}
    case Some{T.Split{pos, +cnt}}:
      next_op.delete(rest, at, prev, T.number(pos), T.number(cnt), T.has_char(cnt, ' '))

def next_op.insert(+rest: List<&2, T.Line>, +at: Nat, +prev: Maybe<&2, Op>, pos: Maybe<&2, Nat>) -> Next:
  match pos:
    case None{}:
      Bad{at, "a malformed insert"}
    case Some{p}:
      next_op.items(prev, Insert{}, p, None{}, at, take_items(rest, classify_head(rest, '+'), 1n+at, '+', Nil{}))

# The operation line, once its keyword is known.
def next_op.keyword(+rest: List<&2, T.Line>, +at: Nat, +prev: Maybe<&2, Op>, +t: String, +args: String, is_delete: Bool, is_insert: Bool, is_content: Bool, is_marker: Bool) -> Next:
  match is_delete:
    case True{}:
      next_op.delete_args(rest, at, prev, T.split_once(args))
    case False{}:
      match is_insert:
        case True{}:
          Bool.pick(Next, Bool.or(String.is_empty(args), T.has_char(args, ' ')), Bad{at, "a malformed insert"}, next_op.insert(rest, at, prev, T.number(args)))
        case False{}:
          match is_content:
            case True{}:
              Bad{at, "content without an operation"}
            case False{}:
              Bool.pick(Next, is_marker, Bad{at, "`\\ no newline` without an item above it"}, Bad{at, "an unknown operation: " ++ t})

def next_op.split(+rest: List<&2, T.Line>, +at: Nat, +prev: Maybe<&2, Op>, +t: String, cut: Maybe<&2, T.Split>) -> Next:
  match cut:
    case None{}:
      next_op.keyword(rest, at, prev, t, SNil{}, String.eq(t, "delete"), String.eq(t, "insert"), Bool.or(String.starts_with(t, "-"), String.starts_with(t, "+")), String.eq(t, "\\ no newline"))
    case Some{T.Split{+kw, args}}:
      next_op.keyword(rest, at, prev, t, args, String.eq(kw, "delete"), String.eq(kw, "insert"), Bool.or(String.starts_with(t, "-"), String.starts_with(t, "+")), False{})

# The next operation under the walk, or the end, or a complaint.
def next_op(ls: List<&2, T.Line>, +at: Nat, +prev: Maybe<&2, Op>) -> Next:
  match ls:
    case Nil{}:
      End{}
    case T.Line{+t, False{}} <> rest:
      Bad{at, "unterminated line"}
    case T.Line{+t, True{}} <> rest:
      Bool.pick(Next, T.has_char(t, '\r'), Bad{at, "a carriage return in an operation line"}, next_op.split(rest, at, prev, t, T.split_once(t)))

# Keep the last deleted region across inserts. Checking only the immediate
# predecessor lets a replacement hide an overlapping or adjacent delete.
def remember_delete(op: Op, previous: Maybe<&2, Op>) -> Maybe<&2, Op>:
  match op:
    case Op{Delete{}, at, items}:
      Some{Op{Delete{}, at, items}}
    case Op{Insert{}, at, items}:
      previous

def next_op.bounded(previous_delete: Maybe<&2, Op>, n: Next) -> Next:
  match n:
    case End{}:
      End{}
    case Bad{at, msg}:
      Bad{at, msg}
    case More{+op, rest, at}:
      next_op.fin(op, rest, at, ordered(previous_delete, op))

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
      parse.ops(p, next_op.bounded(deletion, next_op(rest, at, Some{op})), op <> acc, deletion)

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
      parse.body(forgets, result, parse.ops(1n+List.length(&2, T.Line, rest), next_op(rest, 1n+at, None{}), Nil{}, None{}))
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
    case T.Line{+t, term} <> rest:
      header.of(t, term, rest, at, T.strip_prefix(t, key))

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
      Bool.pick(Result<&2, &2, String, Doc>, String.eq(t, "historica"), parse.forgets(header(rest, 2n, "forgets ")), fail(Doc, 1n, "not a historica document: " ++ t))
    case _:
      fail(Doc, 1n, "not a historica document")

# An operation document, from its text.
def parse(s: String) -> Result<&2, &2, String, Doc>:
  parse.preamble(T.lines(s))

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
      "delete " ++ Nat.show(at) ++ " " ++ Nat.show(List.length(&2, Item, items)) ++ "\n" ++ write_items('-', items)
    case Op{Insert{}, at, items}:
      "insert " ++ Nat.show(at) ++ "\n" ++ write_items('+', items)

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
      Bool.pick(Result<&2, &2, String, Unit>, String.eq(stated, found), Done{Unit{}}, Fail{"the result stated is " ++ stated ++ " but the replay produced " ++ found})

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

def nat_at(xs: List<&2, Nat>, n: Nat) -> Nat:
  match xs n:
    case Nil{} _:
      0n
    case x <> rest 0n:
      x
    case x <> rest 1n+p:
      nat_at(rest, p)

def cell(table: List<&2, List<&2, Nat>>, i: Nat, j: Nat) -> Nat:
  match table i:
    case Nil{} _:
      0n
    case row <> rest 0n:
      nat_at(row, j)
    case row <> rest 1n+p:
      cell(rest, p, j)

# The next row of the table from the one above it: `prev` is that row from
# column j on, and `left` the cell just filled in this row.
def next_row(new: List<&2, Item>, prev: List<&2, Nat>, +x: Item, +left: Nat) -> List<&2, Nat>:
  match new prev:
    case y <> ys d <> +u <> rest:
      +v = Bool.pick(Nat, same(x, y), 1n+d, Nat.max(u, left))
      v <> next_row(ys, u <> rest, x, v)
    case _ _:
      Nil{}

def rows(old: List<&2, Item>, +new: List<&2, Item>, prev: List<&2, Nat>) -> List<&2, List<&2, Nat>>:
  match old:
    case Nil{}:
      Nil{}
    case x <> xs:
      +row = {0n <> next_row(new, prev, x, 0n) : List<&2, Nat>}
      row <> rows(xs, new, row)

# Row i, column j is the length of the longest common subsequence of the
# first i old items and the first j new ones.
def table(old: List<&2, Item>, +new: List<&2, Item>) -> List<&2, List<&2, Nat>>:
  +zeros = List.replicate(Nat, 1n+List.length(&2, Item, new), 0n)
  zeros <> rows(old, new, zeros)

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

def step(+old: List<&2, Item>, +new: List<&2, Item>, +tbl: List<&2, List<&2, Nat>>, i: Nat, j: Nat) -> Verdict:
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
      step.of(same(item_at(old, p), item_at(new, q)), Nat.is_ge(cell(tbl, p, 1n+q), cell(tbl, 1n+p, q)))

type Edit is Data:
  Keep{}
  Del{x: Item}
  Ins{y: Item}

# From the last cell back to the first, collecting the edit script forwards.
def backtrack(fuel: Nat, v: Verdict, i: Nat, j: Nat, +old: List<&2, Item>, +new: List<&2, Item>, +tbl: List<&2, List<&2, Nat>>, script: List<&2, Edit>) -> List<&2, Edit>:
  match fuel v:
    case _ Stop{}:
      script
    case 0n _:
      script
    case 1n+f Diag{}:
      +i2 = Nat.sub(i, 1n)
      +j2 = Nat.sub(j, 1n)
      backtrack(f, step(old, new, tbl, i2, j2), i2, j2, old, new, tbl, Keep{} <> script)
    case 1n+f Up{}:
      +i2 = Nat.sub(i, 1n)
      +j = j
      backtrack(f, step(old, new, tbl, i2, j), i2, j, old, new, tbl, Del{item_at(old, i2)} <> script)
    case 1n+f Left{}:
      +j2 = Nat.sub(j, 1n)
      +i = i
      backtrack(f, step(old, new, tbl, i, j2), i, j2, old, new, tbl, Ins{item_at(new, j2)} <> script)

def script(+old: List<&2, Item>, +new: List<&2, Item>) -> List<&2, Edit>:
  +n = List.length(&2, Item, old)
  +m = List.length(&2, Item, new)
  +tbl = table(old, new)
  backtrack(Nat.add(n, m), step(old, new, tbl, n, m), n, m, old, new, tbl, Nil{})

# A run of edits between two kept lines is one delete and one insert, both
# anchored where the run began: a replacement is minus lines above plus lines.
def flush(+start: Nat, dels: List<&2, Item>, ins: List<&2, Item>, acc: List<&2, Op>) -> List<&2, Op>:
  match dels ins:
    case Nil{} Nil{}:
      acc
    case Nil{} i <> it:
      Op{Insert{}, start, List.reverse(&2, Item, i <> it)} <> acc
    case d <> ds Nil{}:
      Op{Delete{}, start, List.reverse(&2, Item, d <> ds)} <> acc
    case d <> ds i <> it:
      Op{Insert{}, start, List.reverse(&2, Item, i <> it)} <> Op{Delete{}, start, List.reverse(&2, Item, d <> ds)} <> acc

def group(edits: List<&2, Edit>, +p: Nat, start: Nat, dels: List<&2, Item>, ins: List<&2, Item>, acc: List<&2, Op>) -> List<&2, Op>:
  match edits:
    case Nil{}:
      List.reverse(&2, Op, flush(start, dels, ins, acc))
    case Keep{} <> rest:
      group(rest, 1n+p, 1n+p, Nil{}, Nil{}, flush(start, dels, ins, acc))
    case Del{x} <> rest:
      group(rest, 1n+p, start, x <> dels, ins, acc)
    case Ins{y} <> rest:
      group(rest, p, start, dels, y <> ins, acc)

def diff.of(ops: List<&2, Op>, result: String) -> Maybe<&2, Doc>:
  match ops:
    case Nil{}:
      None{}
    case op <> rest:
      Some{Doc{None{}, Some{result}, op <> rest}}

# The document that takes `parent` to `child`, or None where they agree.
def diff(parent: List<&2, Item>, +child: List<&2, Item>) -> Maybe<&2, Doc>:
  diff.of(group(script(parent, child), 0n, 0n, Nil{}, Nil{}, Nil{}), state_digest(child))
