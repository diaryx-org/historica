# The resolution document: a merge's file, stated whole (decision 0032).
#
# Where a merge's parents disagree about a file, its `edit` line may name
# one of these rather than an operation document:
#
#   historica
#   result <digest of the assembled file>
#
#   keep <document> <first> <count>
#   insert
#   +a line the person wrote while resolving
#
# A `keep` takes a run of the items a document minted — an operation
# document's inserts, a resolution's own inserts, or a payload's lines —
# counted in that document's order, and an `insert` mints new ones. The
# pieces, concatenated, are the file: no positions and no parent state.
#
# Reading is as strict as the Rust reader's: pieces are maximal, so two
# `keep`s of one document whose ranges meet are one `keep`, and two
# `insert`s that meet are one `insert`.

import Base
import ./text.bend as T
import ./ops.bend as Ops
import ./words.bend as W

type Piece is Data:
  Piece.Keep{document: String, first: Nat, count: Nat}
  Piece.Insert{items: List<&2, Ops.Item>}

type Doc is Data:
  Doc{forgets: Maybe<&2, String>, result: Maybe<&2, String>, pieces: List<&2, Piece>}

# Which grammar an `edit` names is said by the document's own bytes: the
# first line after the headers is a `keep` or an `insert` with no position.
def blank.body(parts: List<&2, String>) -> Bool:
  match parts:
    case +first <> rest:
      Bool.or(String.starts_with(first, "keep "), String.eq(first, "insert"))
    case Nil{}:
      False{}

# The text after the first blank line: `newline` is whether the character
# before was one, and `after_blank` whether it was the second in a row.
def blank.go(chars: String, newline: Bool, after_blank: Bool) -> Maybe<&2, String>:
  match chars:
    case SNil{}:
      Bool.pick(Maybe<&2, String>, after_blank, Some{SNil{}}, None{})
    case SCon{+c, +rest}:
      Bool.pick(Maybe<&2, String>, after_blank, Some{SCon{c, rest}}, blank.go(rest, Char.is_eq(c, '\n'), Bool.and(newline, Char.is_eq(c, '\n'))))

def blank.found(body: Maybe<&2, String>) -> Bool:
  match body:
    case None{}:
      False{}
    case Some{b}:
      blank.body(String.split(b, '\n'))

def is_resolution(s: String) -> Bool:
  blank.found(blank.go(s, False{}, False{}))

# Parsing
# -------

def fail(-A: Data, at: Nat, msg: String) -> Result<&2, &2, String, A>:
  Ops.fail(A, at, msg)

# One piece read, and where the reading goes on from.
type Next is Data:
  Next{piece: Result<&2, &2, String, Piece>, rest: List<&2, T.Line>, at: Nat}

def keep.numbers(+at: Nat, d: String, digest: Bool, first: Maybe<&2, Nat>, count: Maybe<&2, Nat>, f: String, c: String) -> Result<&2, &2, String, Piece>:
  match digest first count:
    case False{} _ _:
      fail(Piece, at, "`keep` names " ++ d ++ ", which is not a digest")
    case True{} None{} _:
      fail(Piece, at, "`" ++ f ++ "` is not a position")
    case True{} Some{x} None{}:
      fail(Piece, at, "`" ++ c ++ "` is not a count")
    case True{} Some{x} Some{0n}:
      fail(Piece, at, "a `keep` that keeps nothing states nothing; delete the line")
    case True{} Some{x} Some{n}:
      Done{Piece.Keep{d, x, n}}


def keep.fields(+at: Nat, +line: String, fields: List<&2, String>) -> Result<&2, &2, String, Piece>:
  match fields:
    case +d <> +f <> +c <> Nil{}:
      keep.numbers(at, d, T.is_digest(d), T.number(f), T.number(c), f, c)
    case _:
      fail(Piece, at, "`" ++ line ++ "` is not an operation")

def insert.taken(+at: Nat, taken: Result<&2, &2, String, Ops.Taken>) -> Next:
  match taken:
    case Fail{e}:
      Next{Fail{e}, Nil{}, at}
    case Done{Ops.Taken{Nil{}, rest, at2}}:
      Next{fail(Piece, at, "an `insert` adds at least one item; add a `+` line, or delete the `insert`"), Nil{}, at2}
    case Done{Ops.Taken{items, rest, at2}}:
      Next{Done{Piece.Insert{List.reverse(&2, Ops.Item, items)}}, rest, at2}

def next.insert(+t: String, +rest: List<&2, T.Line>, +at: Nat, is_insert: Bool) -> Next:
  match is_insert:
    case True{}:
      insert.taken(at, Ops.take_items(rest, Ops.classify_head(rest, '+'), 1n+at, '+', Nil{}))
    case False{}:
      Next{fail(Piece, at, "`" ++ t ++ "` is not an operation"), Nil{}, at}


def next.line(+t: String, term: Bool, rest: List<&2, T.Line>, +at: Nat, keep: Maybe<&2, String>, positioned: Maybe<&2, String>) -> Next:
  match term keep positioned:
    case False{} _ _:
      Next{fail(Piece, at, "unterminated line"), Nil{}, at}
    case True{} Some{args} _:
      Next{keep.fields(at, t, String.split(args, ' ')), rest, 1n+at}
    case True{} None{} Some{p}:
      Next{fail(Piece, at, "a resolution's `insert` takes no position — the pieces are the file, in order — and `insert " ++ p ++ "` states one; delete the number"), Nil{}, at}
    case True{} None{} None{}:
      next.insert(t, rest, at, T.same(t, "insert"))

def next(ls: List<&2, T.Line>, +at: Nat) -> Next:
  match ls:
    case Nil{}:
      Next{fail(Piece, at, "no pieces"), Nil{}, at}
    case T.Line{+t, term} <> rest:
      next.line(t, term, rest, at, T.strip_prefix(t, "keep "), T.strip_prefix(t, "insert "))

# Two pieces that meet are one piece.
def meets(last: Maybe<&2, Piece>, next: Piece) -> Bool:
  match last next:
    case Some{Piece.Keep{d, f, c}} Piece.Keep{d2, f2, c2}:
      Bool.and(String.eq(d, d2), Nat.is_eq(Nat.add(f, c), f2))
    case Some{Piece.Insert{a}} Piece.Insert{b}:
      True{}
    case _ _:
      False{}

def meets.said(p: Piece) -> String:
  match p:
    case Piece.Keep{d, f, c}:
      "two `keep`s of one document whose ranges meet are one `keep`; join them, so that one byte sequence spells this resolution"
    case Piece.Insert{items}:
      "two `insert`s that meet are one `insert`; join them, so that one byte sequence spells this resolution"

# The pieces so far, newest first, and what the walk has left.
type Pieces is Data:
  Pieces{done: Result<&2, &2, String, List<&2, Piece>>, rest: List<&2, T.Line>, at: Nat}

def pieces.took(+before: List<&2, Piece>, +at: Nat, meet: Bool, p: Piece, rest: List<&2, T.Line>, at2: Nat) -> Pieces:
  match meet:
    case True{}:
      Pieces{fail(List<&2, Piece>, at, meets.said(p)), Nil{}, at2}
    case False{}:
      Pieces{Done{p <> before}, rest, at2}

def pieces.last(ps: List<&2, Piece>) -> Maybe<&2, Piece>:
  match ps:
    case Nil{}:
      None{}
    case p <> rest:
      Some{p}

def pieces.step(+before: List<&2, Piece>, +at: Nat, n: Next) -> Pieces:
  match n:
    case Next{Fail{e}, rest, at2}:
      Pieces{Fail{e}, Nil{}, at2}
    case Next{Done{+p}, rest, at2}:
      pieces.took(before, at, meets(pieces.last(before), p), p, rest, at2)

def pieces.go(fuel: Nat, p: Pieces) -> Result<&2, &2, String, List<&2, Piece>>:
  match fuel p:
    case _ Pieces{Fail{e}, rest, at}:
      Fail{e}
    case _ Pieces{Done{done}, Nil{}, at}:
      Done{List.reverse(&2, Piece, done)}
    case 0n Pieces{done, rest, at}:
      done
    case 1n+f Pieces{Done{+done}, +rest, +at}:
      pieces.go(f, pieces.step(done, at, next(rest, at)))

def pieces(+ls: List<&2, T.Line>, +at: Nat) -> Result<&2, &2, String, List<&2, Piece>>:
  pieces.go(1n+List.length(&2, T.Line, ls), Pieces{Done{Nil{}}, ls, at})

def body(forgets: Maybe<&2, String>, result: Maybe<&2, String>, +at: Nat, ps: Result<&2, &2, String, List<&2, Piece>>) -> Result<&2, &2, String, Doc>:
  match ps:
    case Fail{e}:
      Fail{e}
    case Done{Nil{}}:
      fail(Doc, at, "no pieces")
    case Done{some}:
      Done{Doc{forgets, result, some}}

def separator(forgets: Maybe<&2, String>, result: Maybe<&2, String>, ls: List<&2, T.Line>, +at: Nat) -> Result<&2, &2, String, Doc>:
  match ls:
    case T.Line{SNil{}, True{}} <> +rest:
      body(forgets, result, 1n+at, pieces(rest, 1n+at))
    case _:
      fail(Doc, at, "missing the blank line after the headers")

# A resolution states its result, unless it forgets: the file it assembles
# is then the destroyed state, and a digest would confirm a guess at it.
def headers.result(forgets: Maybe<&2, String>, h: Ops.Headed) -> Result<&2, &2, String, Doc>:
  match forgets h:
    case Some{f} Ops.Headed{Some{r}, rest, at}:
      fail(Doc, at, "a result beside forgets")
    case None{} Ops.Headed{None{}, rest, at}:
      fail(Doc, at, "the header `result` is missing")
    case _ Ops.Headed{+result, rest, +at}:
      Bool.pick(Result<&2, &2, String, Doc>, Ops.valid_digest(result), separator(forgets, result, rest, at), fail(Doc, at, "a malformed result"))

def headers.forgets(h: Ops.Headed) -> Result<&2, &2, String, Doc>:
  match h:
    case Ops.Headed{+forgets, rest, +at}:
      Bool.pick(Result<&2, &2, String, Doc>, Ops.valid_digest(forgets), headers.result(forgets, Ops.header(rest, at, "result ")), fail(Doc, at, "a malformed forgets"))

def preamble(ls: List<&2, T.Line>) -> Result<&2, &2, String, Doc>:
  match ls:
    case T.Line{+t, True{}} <> rest:
      Bool.pick(Result<&2, &2, String, Doc>, T.same(t, "historica"), headers.forgets(Ops.header(rest, 2n, "forgets ")), fail(Doc, 1n, "not a historica document: " ++ t))
    case _:
      fail(Doc, 1n, "not a historica document")

# The Rust tool's words
# ---------------------
#
# `ResolutionDocument::parse` read over again in its own order, as
# `Ops.refusal` reads an operation document: only to say why, and on which
# line, a document the parser above refuses is refused.

def w.result.value(+forgetting: Bool, +term: Bool, +t: String, +value: String, +rest: List<&2, T.Line>, +at: Nat) -> Result<&2, &2, String, Ops.WAt>:
  Bool.pick(Result<&2, &2, String, Ops.WAt>, Bool.not(term), Ops.w.fail(Ops.WAt, at, W.unterminated()),
  Bool.pick(Result<&2, &2, String, Ops.WAt>, T.has_char(t, '\r'), Ops.w.fail(Ops.WAt, at, W.carriage_return_in_operation()),
  Bool.pick(Result<&2, &2, String, Ops.WAt>, forgetting, Ops.w.fail(Ops.WAt, at, W.result_of_forgetting()),
  Bool.pick(Result<&2, &2, String, Ops.WAt>, T.is_digest(value), Done{Ops.WAt{rest, at}}, Ops.w.fail(Ops.WAt, at, W.malformed_digest("result", value))))))

def w.result.of(+forgetting: Bool, +t: String, +term: Bool, +rest: List<&2, T.Line>, +n: Nat, v: Maybe<&2, String>) -> Result<&2, &2, String, Ops.WAt>:
  match v:
    case None{}:
      Bool.pick(Result<&2, &2, String, Ops.WAt>, forgetting, Done{Ops.WAt{T.Line{t, term} <> rest, n}}, Ops.w.fail(Ops.WAt, 1n+n, W.missing_header("result")))
    case Some{+value}:
      w.result.value(forgetting, term, t, value, rest, 1n+n)

# `result`, which a resolution states unless it forgets one.
def w.result(ls: List<&2, T.Line>, +n: Nat, +forgetting: Bool) -> Result<&2, &2, String, Ops.WAt>:
  match ls:
    case Nil{}:
      Bool.pick(Result<&2, &2, String, Ops.WAt>, forgetting, Done{Ops.WAt{Nil{}, n}}, Ops.w.fail(Ops.WAt, n, W.missing_header("result")))
    case T.Line{+t, +term} <> +rest:
      w.result.of(forgetting, t, term, rest, n, T.strip_prefix(t, "result "))

# A piece as maximality asks after it.
type WPiece is Data:
  WPiece.Keep{document: String, first: Nat, count: Nat}
  WPiece.Insert{}

type WRead is Data:
  WRead{piece: WPiece, rest: List<&2, T.Line>, n: Nat}

# An `insert`'s lines: what is left, the lines read, the items, and whether
# the reading has stopped.
type WIns is Data:
  WIns{rest: List<&2, T.Line>, n: Nat, count: Nat, done: Bool}

def w.ins.line(+t: String, +term: Bool, +rest: List<&2, T.Line>, +n: Nat, +count: Nat) -> Result<&2, &2, String, WIns>:
  Bool.pick(Result<&2, &2, String, WIns>, T.same(t, "\\ no newline"),
    Bool.pick(Result<&2, &2, String, WIns>, Nat.is_eq(count, 0n), Ops.w.fail(WIns, 1n+n, W.no_newline_without_item()),
      Bool.pick(Result<&2, &2, String, WIns>, term, Done{WIns{rest, 1n+n, count, False{}}}, Ops.w.fail(WIns, 1n+n, W.unterminated()))),
  Bool.pick(Result<&2, &2, String, WIns>, Bool.or(T.same(t, "\\ forgotten"), String.starts_with(t, "+")),
    Bool.pick(Result<&2, &2, String, WIns>, term, Done{WIns{rest, 1n+n, 1n+count, False{}}}, Ops.w.fail(WIns, 1n+n, W.unterminated())),
    Done{WIns{T.Line{t, term} <> rest, n, count, True{}}}))

def w.ins.step(st: WIns) -> Result<&2, &2, String, WIns>:
  match st:
    case WIns{Nil{}, +n, +count, done}:
      Done{WIns{Nil{}, n, count, True{}}}
    case WIns{T.Line{+t, +term} <> +rest, +n, +count, done}:
      Bool.pick(Result<&2, &2, String, WIns>, done, Done{WIns{T.Line{t, term} <> rest, n, count, True{}}}, w.ins.line(t, term, rest, n, count))

def w.ins.go(fuel: Nat, r: Result<&2, &2, String, WIns>) -> Result<&2, &2, String, WIns>:
  match fuel r:
    case _ Fail{e}:
      Fail{e}
    case 0n Done{st}:
      Done{st}
    case 1n+p Done{st}:
      w.ins.go(p, w.ins.step(st))

def w.ins.end(+at: Nat, r: Result<&2, &2, String, WIns>) -> Result<&2, &2, String, WRead>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{WIns{rest, n, +count, done}}:
      Bool.pick(Result<&2, &2, String, WRead>, Nat.is_eq(count, 0n), Ops.w.fail(WRead, at, W.empty_insert()), Done{WRead{WPiece.Insert{}, rest, n}})

def w.keep.numbers(+rest: List<&2, T.Line>, +at: Nat, +d: String, +first: String, +count: String, f: Maybe<&2, Nat>, c: Maybe<&2, Nat>) -> Result<&2, &2, String, WRead>:
  match f c:
    case None{} _:
      Ops.w.fail(WRead, at, W.malformed_number(first))
    case Some{x} None{}:
      Ops.w.fail(WRead, at, W.malformed_number(count))
    case Some{+x} Some{+y}:
      Bool.pick(Result<&2, &2, String, WRead>, Nat.is_eq(y, 0n), Ops.w.fail(WRead, at, W.empty_keep()), Done{WRead{WPiece.Keep{d, x, y}, rest, at}})

def w.keep.fields(+rest: List<&2, T.Line>, +at: Nat, +args: String, fs: List<&2, String>) -> Result<&2, &2, String, WRead>:
  match fs:
    case +d <> +first <> +count <> Nil{}:
      Bool.pick(Result<&2, &2, String, WRead>, T.is_digest(d),
        w.keep.numbers(rest, at, d, first, count, T.number(first), T.number(count)),
        Ops.w.fail(WRead, at, W.malformed_digest("keep", d)))
    case _:
      Ops.w.fail(WRead, at, W.unknown_operation("keep " ++ args))

def w.piece.insert(+t: String, +rest: List<&2, T.Line>, +at: Nat, positioned: Maybe<&2, String>) -> Result<&2, &2, String, WRead>:
  match positioned:
    case Some{+p}:
      Ops.w.fail(WRead, at, W.insert_with_position(p))
    case None{}:
      Ops.w.fail(WRead, at, W.unknown_operation(t))

def w.piece.of(+t: String, +rest: List<&2, T.Line>, +at: Nat, keep: Maybe<&2, String>) -> Result<&2, &2, String, WRead>:
  match keep:
    case Some{+args}:
      w.keep.fields(rest, at, args, String.split(args, ' '))
    case None{}:
      Bool.pick(Result<&2, &2, String, WRead>, T.same(t, "insert"),
        w.ins.end(at, w.ins.go(1n+List.length(&2, T.Line, rest), Done{WIns{rest, at, 0n, False{}}})),
        w.piece.insert(t, rest, at, T.strip_prefix(t, "insert ")))

# `maximal`: two `keep`s of one document that meet, or two `insert`s.
def w.maximal(last: Maybe<&2, WPiece>, next: WPiece) -> Maybe<&2, String>:
  match last next:
    case Some{WPiece.Keep{+d, +f, +c}} WPiece.Keep{+e, +g, h}:
      Bool.pick(Maybe<&2, String>, Bool.and(String.eq(d, e), Nat.is_eq(Nat.add(f, c), g)), Some{W.adjacent_keeps()}, None{})
    case Some{WPiece.Insert{}} WPiece.Insert{}:
      Some{W.adjacent_inserts()}
    case _ _:
      None{}

# Reading the pieces: what is left, the lines read, the last piece, how
# many, and whether the reading has stopped.
type WPieces is Data:
  WPieces{rest: List<&2, T.Line>, n: Nat, last: Maybe<&2, WPiece>, count: Nat, done: Bool}

def w.piece.added(+at: Nat, last: Maybe<&2, WPiece>, +count: Nat, r: Result<&2, &2, String, WRead>) -> Result<&2, &2, String, WPieces>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{WRead{+p, rest, n}}:
      Maybe.default(&2, Result<&2, &2, String, WPieces>, Maybe.map(&2, String, Result<&2, &2, String, WPieces>, e => Fail{W.at(at, e)}, w.maximal(last, p)),
        Done{WPieces{rest, n, Some{p}, 1n+count, False{}}})

def w.pieces.line(+t: String, +term: Bool, +rest: List<&2, T.Line>, +n: Nat, +last: Maybe<&2, WPiece>, +count: Nat) -> Result<&2, &2, String, WPieces>:
  Bool.pick(Result<&2, &2, String, WPieces>, Bool.not(term), Ops.w.fail(WPieces, 1n+n, W.unterminated()),
    Bool.pick(Result<&2, &2, String, WPieces>, T.has_char(t, '\r'), Ops.w.fail(WPieces, 1n+n, W.carriage_return_in_operation()),
      w.piece.added(1n+n, last, count, w.piece.of(t, rest, 1n+n, T.strip_prefix(t, "keep ")))))

def w.pieces.step(st: WPieces) -> Result<&2, &2, String, WPieces>:
  match st:
    case WPieces{Nil{}, +n, +last, +count, done}:
      Done{WPieces{Nil{}, n, last, count, True{}}}
    case WPieces{T.Line{+t, +term} <> +rest, +n, +last, +count, done}:
      Bool.pick(Result<&2, &2, String, WPieces>, done, Done{WPieces{T.Line{t, term} <> rest, n, last, count, True{}}}, w.pieces.line(t, term, rest, n, last, count))

def w.pieces.go(fuel: Nat, r: Result<&2, &2, String, WPieces>) -> Result<&2, &2, String, WPieces>:
  match fuel r:
    case _ Fail{e}:
      Fail{e}
    case 0n Done{st}:
      Done{st}
    case 1n+p Done{st}:
      w.pieces.go(p, w.pieces.step(st))

def w.body(r: Result<&2, &2, String, WPieces>) -> Maybe<&2, String>:
  match r:
    case Fail{e}:
      Some{e}
    case Done{WPieces{ls, +n, last, +count, done}}:
      Bool.pick(Maybe<&2, String>, Nat.is_eq(count, 0n), Some{W.at(n, W.no_operations())}, None{})

def w.after(r: Result<&2, &2, String, Ops.WAt>) -> Maybe<&2, String>:
  match r:
    case Fail{e}:
      Some{e}
    case Done{Ops.WAt{+ls, +n}}:
      w.body(w.pieces.go(1n+List.length(&2, T.Line, ls), Done{WPieces{ls, n, None{}, 0n, False{}}}))

def w.results(r: Result<&2, &2, String, Ops.WAt>, +forgetting: Bool) -> Maybe<&2, String>:
  match r:
    case Fail{e}:
      Some{e}
    case Done{Ops.WAt{+ls, +n}}:
      w.after(Result.bind(&2, &2, String, Ops.WAt, Ops.WAt, w.result(ls, n, forgetting), a => Ops.w.separator.at(a)))

def w.forgets(ls: List<&2, T.Line>) -> Maybe<&2, String>:
  +h = Ops.w.header(ls, 1n, "forgets", False{})
  w.results(h, Result.default(&2, &2, String, Bool, Result.map(&2, &2, String, Ops.WAt, Bool, a => Ops.w.stated(a, 1n), h), False{}))

def w.first.line(ls: List<&2, T.Line>) -> Maybe<&2, String>:
  match ls:
    case Nil{}:
      Some{W.at(1n, W.empty())}
    case T.Line{+t, +term} <> rest:
      Bool.pick(Maybe<&2, String>, T.has_char(t, '\r'), Some{W.at(1n, W.carriage_return_in_operation())},
        Maybe.or(&2, String, W.preamble(t, term), w.forgets(rest)))

# Why the Rust tool refuses these bytes as a resolution, in its words.
def refusal(+s: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, W.bom(s), Some{W.at(1n, W.byte_order_mark())}, w.first.line(T.lines(s)))

def worded(+s: String, r: Result<&2, &2, String, Doc>) -> Result<&2, &2, String, Doc>:
  match r:
    case Done{d}:
      Done{d}
    case Fail{e}:
      Fail{Maybe.default(&2, String, refusal(s), e)}

def parse(+s: String) -> Result<&2, &2, String, Doc>:
  worded(s, preamble(T.lines(s)))

# Writing
# -------

# The exact bytes of a resolution, as the Rust writer spells one: the
# headers, the blank line, and each piece — a `keep` as its three fields, an
# `insert` as its items, `\ forgotten` where one's text was destroyed.
def write.piece(p: Piece) -> String:
  match p:
    case Piece.Keep{d, first, count}:
      "keep " ++ d ++ " " ++ T.spell(first) ++ " " ++ T.spell(count) ++ "\n"
    case Piece.Insert{items}:
      "insert\n" ++ Ops.write_items('+', items)

def write.pieces(ps: List<&2, Piece>) -> String:
  match ps:
    case Nil{}:
      SNil{}
    case p <> rest:
      write.piece(p) ++ write.pieces(rest)

def write(d: Doc) -> String:
  match d:
    case Doc{forgets, result, pieces}:
      "historica\n" ++ Ops.header_line("forgets", forgets) ++ Ops.header_line("result", result) ++ "\n" ++ write.pieces(pieces)

# What a resolution names
# -----------------------

def keeps.of(ps: List<&2, Piece>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Piece.Keep{d, f, c} <> rest:
      d <> keeps.of(rest)
    case Piece.Insert{items} <> rest:
      keeps.of(rest)

# The documents a resolution keeps items of, which a reader fetches before
# it assembles; nothing, for one that does not parse, whose fault the
# assembling reports.
def keeps(r: Result<&2, &2, String, Doc>) -> List<&2, String>:
  match r:
    case Fail{e}:
      Nil{}
    case Done{Doc{forgets, result, ps}}:
      keeps.of(ps)

# The items a resolution mints: its `insert` pieces, in order.
def minted.of(ps: List<&2, Piece>) -> List<&2, Ops.Item>:
  match ps:
    case Nil{}:
      Nil{}
    case Piece.Keep{d, f, c} <> rest:
      minted.of(rest)
    case Piece.Insert{items} <> rest:
      List.append(&2, Ops.Item, items, minted.of(rest))

def minted(d: Doc) -> List<&2, Ops.Item>:
  match d:
    case Doc{forgets, result, ps}:
      minted.of(ps)

def sample() -> String:
  "historica\nresult 07a9e448f01c537968c69f3fc819f5ca1913b905cfdac762796d122043df8378\n\nkeep 880553fca8fcea94e325ee2cfb48e5a985cc797f39a14cc6d3cedecfeb2ae4d2 0 1\ninsert\n+new\n\\ no newline\n"

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Bool.show(is_resolution(sample())))
    IO.print(Nat.show(List.length(&2, String, keeps(parse(sample())))))
