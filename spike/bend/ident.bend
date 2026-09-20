# The two kinds of name in a store. A digest is sixty-four lowercase hex
# characters; an assigned identifier — a change ID or a file ID — is
# twenty-four characters from `k` to `z`, an alphabet no hexadecimal digest
# can be spelled in, so neither can be mistaken for the other. The spelling
# is reversed hex: nibble 0 is `z` and nibble 15 is `k`.

import Base
import ./text.bend as T

def is_letter(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.and(U32.is_ge(x, 107), U32.is_le(x, 122))

# Whether a string is a change ID or a file ID.
def is_assigned(+s: String) -> Bool:
  Bool.and(Nat.is_eq(String.length(s), 24n), T.all_chars(~is_letter, s))

def is_digest(s: String) -> Bool:
  T.is_digest(s)

# The spelling of bytes, two letters each.
def spell_nibble(+n: U32) -> Char:
  Chr{(122 - n : U32)}

def spell(bs: List<&2, U32>) -> String:
  match bs:
    case Nil{}:
      SNil{}
    case +b <> rest:
      SCon{spell_nibble((b >> 4n : U32)), SCon{spell_nibble((b .&. 15 : U32)), spell(rest)}}

# The bytes a spelling names, or None where a character is not a letter of
# the alphabet or the count is odd.
def decipher.pair(+hi: U32, +lo: U32, rest: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match rest:
    case None{}:
      None{}
    case Some{bs}:
      Bool.pick(Maybe<&2, List<&2, U32>>, Bool.and(is_letter(Chr{hi}), is_letter(Chr{lo})),
        Some{(((122 - hi) << 4n) .|. (122 - lo) : U32) <> bs}, None{})

def decipher(s: String) -> Maybe<&2, List<&2, U32>>:
  match s:
    case SNil{}:
      Some{Nil{}}
    case SCon{h, SNil{}}:
      None{}
    case SCon{Chr{hi}, SCon{Chr{lo}, rest}}:
      decipher.pair(hi, lo, decipher(rest))

# Assigned identifiers order as they read, which is backwards through their
# bytes; digests order as they read too, and hex reads forwards. Both are
# string order, which is what every sorted header relies on.
def order(a: String, b: String) -> Cmp:
  String.order(a, b)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(spell([0, 255, 16]))
    IO.print(Bool.show(is_assigned("qpvuntsmwlrkzxonmvtplsyq")))
    IO.print(Bool.show(is_assigned("qpvuntsmwlrkzxonmvtplsy")))
    IO.print(Maybe.show(~&2, ~List<&2, U32>, ~(bs => List.show(~&2, ~U32, ~U32.show, bs)), decipher("zzkkzy")))
