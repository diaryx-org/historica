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

def split_once(s: String) -> Maybe<&2, Split>:
  split_once.go(s, SNil{})

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

# A canonical decimal: digits only, and no leading zero unless it is `0`.
def canonical_number(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{Chr{d}, SNil{}}:
      Char.is_digit(Chr{d})
    case SCon{+h, t}:
      Bool.and(Bool.and(Char.is_digit(h), Bool.not(Char.is_eq(h, '0'))), all_chars(~Char.is_digit, t))

def number(+s: String) -> Maybe<&2, Nat>:
  Bool.pick(Maybe<&2, Nat>, canonical_number(s), Nat.read(s), None{})

def is_hex(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(Char.is_digit(Chr{x}), Bool.and(U32.is_ge(x, 97), U32.is_le(x, 102)))

# Sixty-four lowercase hex characters: the spelling of a SHA-256.
def is_digest(+s: String) -> Bool:
  Bool.and(Nat.is_eq(String.length(s), 64n), all_chars(~is_hex, s))

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
    IO.print(word("insert 3 4"))
