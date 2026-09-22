# Lines, fields and numbers: what every document parser here reads with.

import Base

# One line of a document, and whether a newline ended it. Only the last line
# of a file can lack one, and only a revision's message may keep it that way.
type Line is Data:
  Line{text: String, terminated: Bool}

# A file as lines. A file ending in a newline has no empty ragged line after
# it: the split's trailing empty string is the terminator, not a line.
def lines.go(parts: List<&2, String>) -> List<&2, Line>:
  match parts:
    case Nil{}:
      Nil{}
    case +last <> Nil{}:
      Bool.pick(List<&2, Line>, String.is_empty(last), Nil{}, [Line{last, False{}}])
    case h <> t:
      Line{h, True{}} <> lines.go(t)

def lines(s: String) -> List<&2, Line>:
  lines.go(String.split(s, '\n'))

# A string cut at its first space: the word before it and everything after.
type Split is Data:
  Split{head: String, rest: String}

def split_once.go(s: String, +acc: String) -> Maybe<&2, Split>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      Bool.pick(Maybe<&2, Split>, Char.is_eq(c, ' '), Some{Split{String.reverse(acc), t}}, split_once.go(t, SCon{c, acc}))

# Whether a string opens with a space: the question `split_once.go` asks of
# each character, asked here of the tail before the walk reaches it.
def space_first(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Char.is_eq(c, ' ')

# `split_once.go` with the answer for the head carried in, so the tail is
# never reused: `go` marks the tail `+t` and hands one copy to the untaken
# branch, which a strict `Bool.pick` walks to the end of the string, so the
# other copy is made whole at every character — a line's length squared, at
# every header of a document. This walks to the space and stops.
# `spelling_lemmas.split_fast` says it is `go`.
def split_once.fast(s: String, +acc: String, hit: Bool) -> Maybe<&2, Split>:
  match s hit:
    case SNil{} _:
      None{}
    case SCon{c, t} True{}:
      Some{Split{String.reverse(acc), t}}
    case SCon{c, +t} False{}:
      split_once.fast(t, SCon{c, acc}, space_first(t))

def split_once(+s: String) -> Maybe<&2, Split>:
  split_once.fast(s, SNil{}, space_first(s))

# The word before the first space, or the whole string.
def word.of(s: String, cut: Maybe<&2, Split>) -> String:
  match cut:
    case None{}:
      s
    case Some{Split{h, r}}:
      h

def word(+s: String) -> String:
  word.of(s, split_once(s))

# List.map for reusable elements, which Base's is not.
def map(~A: Data, ~B: Data, ~f: A -> B, xs: List<&2, A>) -> List<&2, B>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      f(h) <> map(~A, ~B, ~f, t)

def concat(-A: Data, xss: List<&2, List<&2, A>>) -> List<&2, A>:
  match xss:
    case Nil{}:
      Nil{}
    case xs <> rest:
      List.append(&2, A, xs, concat(A, rest))

def has_char(s: String, +c: Char) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{h, t}:
      Bool.or(Char.is_eq(h, c), has_char(t, c))

def all_chars(~f: Char -> Bool, s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{h, t}:
      Bool.and(f(h), all_chars(~f, t))

# Decimal numbers, read and spelled by the same digit table, so that the
# proofs can follow the digits rather than the arithmetic of a machine word.
# Digits are little-endian lists of naturals below ten.
def digits_table() -> List<&2, Char>:
  ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']

def digit_of.go(table: List<&2, Char>, +c: Char, +k: Nat) -> Maybe<&2, Nat>:
  match table:
    case Nil{}:
      None{}
    case ch <> rest:
      Bool.pick(Maybe<&2, Nat>, Char.is_eq(c, ch), Some{k}, digit_of.go(rest, c, 1n+k))

def digit_of(c: Char) -> Maybe<&2, Nat>:
  digit_of.go(digits_table(), c, 0n)

def char_of.go(table: List<&2, Char>, +k: Nat, +d: Nat) -> Char:
  match table:
    case Nil{}:
      '?'
    case ch <> rest:
      Bool.pick(Char, Nat.is_eq(k, d), ch, char_of.go(rest, 1n+k, d))

def char_of(d: Nat) -> Char:
  char_of.go(digits_table(), 0n, d)

# The digits of a string read backwards, least significant first.
def to_digits.push(d: Maybe<&2, Nat>, ds: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
  match d ds:
    case Some{x} Some{xs}:
      Some{x <> xs}
    case _ _:
      None{}

def to_digits(rs: String) -> Maybe<&2, List<&2, Nat>>:
  match rs:
    case SNil{}:
      Some{Nil{}}
    case SCon{c, t}:
      to_digits.push(digit_of(c), to_digits(t))

# Ten times a number. `mul10.spec` is what the proofs follow; `mul10`
# accumulates, so the stack does not grow with the number.
def mul10.spec(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+mul10.spec(p)

def mul10.go(n: Nat, acc: Nat) -> Nat:
  match n:
    case 0n:
      acc
    case 1n+p:
      mul10.go(p, 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+acc)

def mul10(n: Nat) -> Nat:
  mul10.go(n, 0n)

def value(ds: List<&2, Nat>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case d <> rest:
      Nat.add(d, mul10(value(rest)))

# A canonical spelling has a nonzero leading digit unless it is `0` alone;
# read backwards, the last digit is nonzero unless it is the only one.
def normalized.tail(ds: List<&2, Nat>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case +d <> Nil{}:
      Bool.and(Nat.is_lt(d, 10n), Nat.is_lt(0n, d))
    case d <> rest:
      Bool.and(Nat.is_lt(d, 10n), normalized.tail(rest))

def normalized(ds: List<&2, Nat>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case d <> Nil{}:
      Nat.is_lt(d, 10n)
    case d <> rest:
      Bool.and(Nat.is_lt(d, 10n), normalized.tail(rest))

def number.of(ds: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, Nat>:
  match ds:
    case None{}:
      None{}
    case Some{+xs}:
      Bool.pick(Maybe<&2, Nat>, normalized(xs), Some{value(xs)}, None{})

def number(s: String) -> Maybe<&2, Nat>:
  number.of(to_digits(String.reverse(s)))

# Counting up in digits: the successor of a little-endian digit list.
def dsucc(ds: List<&2, Nat>) -> List<&2, Nat>:
  match ds:
    case Nil{}:
      [1n]
    case +d <> +rest:
      Bool.pick(List<&2, Nat>, Nat.is_eq(d, 9n), 0n <> dsucc(rest), (1n+d) <> rest)

# `digits.spec` is the definition the proofs follow; `digits` counts the
# same way with an accumulator, so the stack does not grow with the number.
def digits.spec(n: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      [0n]
    case 1n+p:
      dsucc(digits.spec(p))

def digits.go(n: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      acc
    case 1n+p:
      digits.go(p, dsucc(acc))

def digits(n: Nat) -> List<&2, Nat>:
  digits.go(n, [0n])

def chars(ds: List<&2, Nat>) -> String:
  match ds:
    case Nil{}:
      SNil{}
    case d <> rest:
      SCon{char_of(d), chars(rest)}

# The canonical spelling of a number.
def spell(n: Nat) -> String:
  String.reverse(chars(digits(n)))

def is_hex(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(Char.is_digit(Chr{x}), Bool.and(U32.is_ge(x, 97), U32.is_le(x, 102)))

# Sixty-four lowercase hex characters: the spelling of a SHA-256.
def is_digest(+s: String) -> Bool:
  Bool.and(Nat.is_eq(String.length(s), 64n), all_chars(~is_hex, s))

# Structural equality, which a proof can open where `String.eq`'s three-way
# comparison cannot.
def same(a: String, b: String) -> Bool:
  match a b:
    case SNil{} SNil{}:
      True{}
    case SCon{x, xt} SCon{y, yt}:
      Bool.and(Char.is_eq(x, y), same(xt, yt))
    case _ _:
      False{}

def strip_prefix(+s: String, p: String) -> Maybe<&2, String>:
  match s p:
    case _ SNil{}:
      Some{s}
    case SNil{} SCon{y, yt}:
      None{}
    case SCon{x, +xt} SCon{y, yt}:
      Bool.pick(Maybe<&2, String>, Char.is_eq(x, y), strip_prefix(xt, yt), None{})

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Nat.show(List.length(&2, Line, lines("a\nb\n"))))
    IO.print(Nat.show(List.length(&2, Line, lines("a\nb"))))
    IO.print(Maybe.show(~&2, ~Nat, ~Nat.show, number("042")))
    IO.print(Maybe.show(~&2, ~Nat, ~Nat.show, number("42")))
    IO.print(spell(0n) ++ " " ++ spell(10n) ++ " " ++ spell(4090n))
    IO.print(word("insert 3 4"))
