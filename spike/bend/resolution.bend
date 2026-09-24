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

def parse(s: String) -> Result<&2, &2, String, Doc>:
  preamble(T.lines(s))

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

# Writing
# -------

# The bytes the Rust tool writes for a resolution: the preamble and headers
# an operation document has, a blank line, and each piece — a `keep` line,
# or `insert` and its items spelled as an operation document spells them.
def write.piece(p: Piece) -> String:
  match p:
    case Piece.Keep{d, f, c}:
      "keep " ++ d ++ " " ++ T.spell(f) ++ " " ++ T.spell(c) ++ "\n"
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
    case Doc{forgets, result, ps}:
      "historica\n" ++ Ops.header_line("forgets", forgets) ++ Ops.header_line("result", result) ++ "\n" ++ write.pieces(ps)

def sample() -> String:
  "historica\nresult 07a9e448f01c537968c69f3fc819f5ca1913b905cfdac762796d122043df8378\n\nkeep 880553fca8fcea94e325ee2cfb48e5a985cc797f39a14cc6d3cedecfeb2ae4d2 0 1\ninsert\n+new\n\\ no newline\n"

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Bool.show(is_resolution(sample())))
    IO.print(Nat.show(List.length(&2, String, keeps(parse(sample())))))
