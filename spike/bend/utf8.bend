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
