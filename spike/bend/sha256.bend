# SHA-256 over a list of bytes, for a store where every document is named by
# the digest of its own bytes. The hash itself is bend-sha256, a packed-array
# implementation with its own checked proofs, pinned here by content hash:
# https://github.com/Giulio2002/bend-sha256. This module packs the byte list
# into the words it wants, four big-endian bytes to a U32, and spells the
# eight words it returns as the sixty-four hex characters `shasum -a 256`
# prints. Messages are assumed shorter than 2^32 bits, which is every file
# this port will meet.

import Base
import 0xda83506fb9f059ead7afcfa2f498df5f/sha256.bend as Packed

# The digest: eight words, in the order the standard names them.
type Hash is Data:
  H{a: U32, b: U32, c: U32, d: U32, e: U32, f: U32, g: U32, h: U32}

# Packing
# -------

def pack(+b0: U32, +b1: U32, +b2: U32, +b3: U32) -> U32:
  (((((b0 .&. 255) << 24n) .|. ((b1 .&. 255) << 16n)) .|. ((b2 .&. 255) << 8n)) .|. (b3 .&. 255) : U32)

# The smallest array depth whose capacity holds `words` words; `fuel` bounds
# the doubling, and 32 doublings is far past any message the port will meet.
def depth(fuel: Nat, c: Cmp, +words: Nat, +cap: Nat, acc: Nat) -> Nat:
  match fuel c:
    case 0n _: acc
    case _ LT{}: acc
    case _ EQ{}: acc
    case 1n+p GT{}:
      depth(p, Nat.cmp(words, Nat.mul(cap, 2n)), words, Nat.mul(cap, 2n), Nat.add(acc, 1n))

# Fills the array word by word; a ragged tail packs against zero bytes, which
# the hash ignores past the byte length it is told.
def fill(bs: List<&2, U32>, +i: U32, a: Array<U32>) -> Array<U32>:
  match bs:
    case Nil{}: a
    case b0 <> Nil{}: Array.set(U32, a, i, pack(b0, 0, 0, 0))
    case b0 <> b1 <> Nil{}: Array.set(U32, a, i, pack(b0, b1, 0, 0))
    case b0 <> b1 <> b2 <> Nil{}: Array.set(U32, a, i, pack(b0, b1, b2, 0))
    case b0 <> b1 <> b2 <> b3 <> rest:
      fill(rest, U32.inc(i), Array.set(U32, a, i, pack(b0, b1, b2, b3)))

def packed(bs: List<&2, U32>, +length: Nat) -> Array<U32>:
  +words = Nat.div(Nat.add(length, 3n), 4n)
  fill(bs, 0, Array.new(U32, depth(32n, Nat.cmp(words, 1n), words, 1n, 0n), 0))

# The digest
# ----------

# Eight words read in turn; each get hands the array back for the next.
def gather.go(n: Nat, +i: U32, pair: Array<U32> & U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n pair:
    case 0n Tuple{a, w}:
      List.reverse(&2, U32, w <> acc)
    case 1n+p Tuple{a, w}:
      gather.go(p, U32.inc(i), Array.get(U32, a, i), w <> acc)

def as_hash(ws: List<&2, U32>) -> Hash:
  match ws:
    case a <> b <> c <> d <> e <> f <> g <> h <> rest:
      H{a, b, c, d, e, f, g, h}
    case _:
      H{0, 0, 0, 0, 0, 0, 0, 0}

# The eight words the hash returns, as a Hash. `None` is the hash refusing a
# byte length past the array's capacity, which `packed` never produces; the
# zero hash keeps this total.
def gather(r: Maybe<&1, Array<U32>>) -> Hash:
  match r:
    case None{}:
      H{0, 0, 0, 0, 0, 0, 0, 0}
    case Some{a}:
      as_hash(gather.go(7n, 1, Array.get(U32, a, 0), Nil{}))

# The SHA-256 of a byte list, as eight words.
def digest_words(+bs: List<&2, U32>) -> Hash:
  +n = List.length(&2, U32, bs)
  gather(Packed.sha256(packed(bs, n), n))

def hex_digit.pick(+n: U32, small: Bool) -> Char:
  match small:
    case True{}:
      Chr{(48 + n : U32)}
    case False{}:
      Chr{(87 + n : U32)}

def hex_digit(+n: U32) -> Char:
  hex_digit.pick(n, U32.is_lt(n, 10))

# Eight lowercase hex digits, most significant first.
def hex_word(+w: U32) -> String:
  String.from_list([ hex_digit((w >> 28n : U32)), hex_digit(((w >> 24n) .&. 15 : U32)),
                     hex_digit(((w >> 20n) .&. 15 : U32)), hex_digit(((w >> 16n) .&. 15 : U32)),
                     hex_digit(((w >> 12n) .&. 15 : U32)), hex_digit(((w >> 8n) .&. 15 : U32)),
                     hex_digit(((w >> 4n) .&. 15 : U32)), hex_digit((w .&. 15 : U32)) ])

def show_hash(st: Hash) -> String:
  match st:
    case H{a, b, c, d, e, f, g, h}:
      String.concat([hex_word(a), hex_word(b), hex_word(c), hex_word(d), hex_word(e), hex_word(f), hex_word(g), hex_word(h)])

# The digest of a byte list, spelled as the sixty-four hex characters
# `shasum -a 256` prints.
def digest(bs: List<&2, U32>) -> String:
  show_hash(digest_words(bs))

# ASCII only: a String whose chars are all below 128, as bytes.
def ascii_bytes(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      c <> ascii_bytes(t)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(digest(ascii_bytes("")))
    IO.print(digest(ascii_bytes("abc")))
    IO.print(digest(ascii_bytes("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")))
    IO.print(digest(ascii_bytes(String.repeat("a", 200n))))
