# Bytes and strings. A Bend String is a list of code points and a store is
# bytes, and the digest is of the bytes; so a document is read as bytes,
# hashed as bytes, and decoded to be parsed, and a file this port produces is
# encoded before it is hashed.

import Base

# Decoding
# --------

# One code point off the front of a byte list, and what is left.
type Step is Data:
  Step{c: Char, rest: List<&2, U32>}

# One continuation byte's six bits onto an accumulator.
def cont(+acc: U32, b: U32) -> U32:
  ((acc << 6n) .|. (b .&. 63) : U32)

# A code point as a Char. What a lead byte's bits say may not be a scalar
# value — a byte of 0xF8 or above, or a surrogate spelled in three bytes —
# and a Char must be one on every backend, so such a sequence decodes to
# U+FFFD, as a text editor shows it.
def chr.of(x: U32, bad: Bool) -> Char:
  match bad:
    case True{}:
      Chr{65533}
    case False{}:
      Chr{x}

def chr(+x: U32) -> Char:
  chr.of(x, Bool.or(U32.is_gt(x, 1114111), Bool.and(U32.is_ge(x, 55296), U32.is_le(x, 57343))))

# The rest after a lead byte of two, three or four, and the code point.
# A truncated sequence decodes to what its bits say rather than being
# refused: the parsers refuse the document later on its own terms, and the
# digest is of the bytes regardless.
def decode.two(acc: U32, bs: List<&2, U32>) -> Step:
  match bs:
    case b1 <> rest:
      Step{chr(cont(acc, b1)), rest}
    case _:
      Step{Chr{acc}, Nil{}}

def decode.three(acc: U32, bs: List<&2, U32>) -> Step:
  match bs:
    case b1 <> b2 <> rest:
      Step{chr(cont(cont(acc, b1), b2)), rest}
    case _:
      Step{Chr{acc}, Nil{}}

def decode.four(acc: U32, bs: List<&2, U32>) -> Step:
  match bs:
    case b1 <> b2 <> b3 <> rest:
      Step{chr(cont(cont(cont(acc, b1), b2), b3)), rest}
    case _:
      Step{Chr{acc}, Nil{}}

# One code point off the front, given a lead byte and where it falls.
def decode.lead(+b: U32, rest: List<&2, U32>, one: Bool, two: Bool, three: Bool) -> Step:
  match one:
    case True{}:
      Step{Chr{b}, rest}
    case False{}:
      match two:
        case True{}:
          decode.two((b .&. 31 : U32), rest)
        case False{}:
          match three:
            case True{}:
              decode.three((b .&. 15 : U32), rest)
            case False{}:
              decode.four((b .&. 7 : U32), rest)

def decode.step(bs: List<&2, U32>) -> Maybe<&2, Step>:
  match bs:
    case Nil{}:
      None{}
    case +b <> rest:
      Some{decode.lead(b, rest, U32.is_lt(b, 128), U32.is_lt(b, 224), U32.is_lt(b, 240))}

# A byte sequence as code points. The fuel is the byte count: a step consumes
# at least one byte, so the fuel is never what stops the walk, and it is what
# lets a step that consumes a variable number of them count as smaller.
def decode.go(fuel: Nat, step: Maybe<&2, Step>) -> String:
  match fuel step:
    case _ None{}:
      SNil{}
    case 0n _:
      SNil{}
    case 1n+p Some{cr}:
      Step{c, rest} = cr
      SCon{c, decode.go(p, decode.step(rest))}

def decode(+bs: List<&2, U32>) -> String:
  decode.go(List.length(&2, U32, bs), decode.step(bs))

# The same, told the byte count.
def decode.sized(bs: List<&2, U32>, n: Nat) -> String:
  decode.go(n, decode.step(bs))

# Encoding
# --------

# Validating
# ----------
#
# `str::from_utf8`'s refusal, in `Utf8Error`'s words: the index the valid
# prefix runs to, and how many bytes past it are no character — or, where
# the bytes stop inside one, that the sequence is incomplete. A file of
# names or rules, and the identity file, are read as text and refused so.

def v.cont(+b: U32) -> Bool:
  Bool.and(U32.is_ge(b, 128), U32.is_le(b, 191))

def v.in(+b: U32, +lo: U32, +hi: U32) -> Bool:
  Bool.and(U32.is_ge(b, lo), U32.is_le(b, hi))

def v.invalid(+n: Nat, +i: Nat) -> Maybe<&2, String>:
  Some{"invalid utf-8 sequence of " ++ Nat.show(n) ++ " bytes from index " ++ Nat.show(i)}

def v.incomplete(+i: Nat) -> Maybe<&2, String>:
  Some{"incomplete utf-8 byte sequence from index " ++ Nat.show(i)}

# The second byte a lead byte allows, which is narrower than any
# continuation byte for `E0`, `ED`, `F0` and `F4`.
def v.second(+lead: U32, +b: U32) -> Bool:
  Bool.pick(Bool, U32.is_eq(lead, 224), v.in(b, 160, 191),
  Bool.pick(Bool, U32.is_eq(lead, 237), v.in(b, 128, 159),
  Bool.pick(Bool, U32.is_eq(lead, 240), v.in(b, 144, 191),
  Bool.pick(Bool, U32.is_eq(lead, 244), v.in(b, 128, 143), v.cont(b)))))

# The width a lead byte of more than one byte gives its sequence, and 0
# for a byte that leads none.
def v.width.more(+b: U32) -> Nat:
  Bool.pick(Nat, v.in(b, 194, 223), 2n,
  Bool.pick(Nat, v.in(b, 224, 239), 3n,
  Bool.pick(Nat, v.in(b, 240, 244), 4n, 0n)))

def v.width(+b: U32) -> Nat:
  Bool.pick(Nat, U32.is_lt(b, 128), 1n, v.width.more(b))

# What is left after one character, or why there is none.
type V is Data:
  V.Next{rest: List<&2, U32>, width: Nat}
  V.Bad{why: String}

def v.tail3(+w: Nat, +i: Nat, bs: List<&2, U32>) -> V:
  match bs:
    case Nil{}:
      Bool.pick(V, Nat.is_ge(w, 4n), V.Bad{Maybe.default(&2, String, v.incomplete(i), SNil{})}, V.Next{Nil{}, 3n})
    case +c3 <> +rest3:
      Bool.pick(V, Nat.is_lt(w, 4n), V.Next{c3 <> rest3, 3n},
        Bool.pick(V, Bool.not(v.cont(c3)), V.Bad{Maybe.default(&2, String, v.invalid(3n, i), SNil{})}, V.Next{rest3, 4n}))

def v.tail2(+w: Nat, +i: Nat, bs: List<&2, U32>) -> V:
  match bs:
    case Nil{}:
      Bool.pick(V, Nat.is_ge(w, 3n), V.Bad{Maybe.default(&2, String, v.incomplete(i), SNil{})}, V.Next{Nil{}, 2n})
    case +c2 <> +rest2:
      Bool.pick(V, Nat.is_lt(w, 3n), V.Next{c2 <> rest2, 2n},
        Bool.pick(V, Bool.not(v.cont(c2)), V.Bad{Maybe.default(&2, String, v.invalid(2n, i), SNil{})}, v.tail3(w, i, rest2)))

def v.tail(+lead: U32, +w: Nat, +i: Nat, bs: List<&2, U32>) -> V:
  match bs:
    case Nil{}:
      Bool.pick(V, Nat.is_ge(w, 2n), V.Bad{Maybe.default(&2, String, v.incomplete(i), SNil{})}, V.Next{Nil{}, 1n})
    case +c1 <> +rest1:
      Bool.pick(V, Nat.is_lt(w, 2n), V.Next{c1 <> rest1, 1n},
        Bool.pick(V, Bool.not(Bool.pick(Bool, Nat.is_eq(w, 2n), v.cont(c1), v.second(lead, c1))), V.Bad{Maybe.default(&2, String, v.invalid(1n, i), SNil{})},
          v.tail2(w, i, rest1)))

def v.step(+i: Nat, bs: List<&2, U32>) -> Maybe<&2, V>:
  match bs:
    case Nil{}:
      None{}
    case +b <> rest:
      +w = v.width(b)
      Some{Bool.pick(V, Nat.is_eq(w, 0n), V.Bad{Maybe.default(&2, String, v.invalid(1n, i), SNil{})}, v.tail(b, w, i, rest))}

def v.go(fuel: Nat, +i: Nat, s: Maybe<&2, V>) -> Maybe<&2, String>:
  match fuel s:
    case _ None{}:
      None{}
    case _ Some{V.Bad{why}}:
      Some{why}
    case 0n _:
      None{}
    case 1n+p Some{V.Next{rest, +w}}:
      v.go(p, Nat.add(i, w), v.step(Nat.add(i, w), rest))

# Why these bytes are not UTF-8, as the Rust tool says it; none where they
# are.
def invalid(+bs: List<&2, U32>) -> Maybe<&2, String>:
  v.go(List.length(&2, U32, bs), 0n, v.step(0n, bs))

def encode.char(+c: U32, rest: List<&2, U32>, one: Bool, two: Bool, three: Bool) -> List<&2, U32>:
  match one:
    case True{}:
      c <> rest
    case False{}:
      match two:
        case True{}:
          (192 .|. (c >> 6n) : U32) <> (128 .|. (c .&. 63) : U32) <> rest
        case False{}:
          match three:
            case True{}:
              (224 .|. (c >> 12n) : U32) <> (128 .|. ((c >> 6n) .&. 63) : U32) <> (128 .|. (c .&. 63) : U32) <> rest
            case False{}:
              (240 .|. (c >> 18n) : U32) <> (128 .|. ((c >> 12n) .&. 63) : U32) <> (128 .|. ((c >> 6n) .&. 63) : U32) <> (128 .|. (c .&. 63) : U32) <> rest

def encode(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{+c}, t}:
      encode.char(c, encode(t), U32.is_lt(c, 128), U32.is_lt(c, 2048), U32.is_lt(c, 65536))

# Files
# -----

# A whole file, as bytes. Each step hands the handle back beside its
# result, so each is its own def that takes the pair apart.
def read_file.got(got: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(List<&2, U32>):
  (f, r) = got
  do IO<List<&2, U32>>:
    File.close(f)
    IO.pass(List<&2, U32>, r)

def read_file.sized(sized: File & Result<&1, &1, U32 & String, U32>) -> IO(List<&2, U32>):
  (f, r) = sized
  do IO<List<&2, U32>>:
    n : U32 <- IO.pass(U32, r)
    got : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, n)
    read_file.got(got)

def read_file(path: String) -> IO(List<&2, U32>):
  do IO<List<&2, U32>>:
    f : File <- IO.try(File, File.open(path, "r"))
    sized : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
    read_file.sized(sized)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(decode(encode("café 🌛")))
    IO.print(Nat.show(List.length(&2, U32, encode("café 🌛"))))
