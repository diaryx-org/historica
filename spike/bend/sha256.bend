# SHA-256 over a list of bytes, for a store where every document is named by
# the digest of its own bytes. Base has no hash, so this is the one from FIPS
# 180-4, written on U32 with the bit operations Base does have. Messages are
# assumed shorter than 2^32 bits, which is every file this port will meet.

import Base

# The running hash: eight words, in the order the standard names them.
type Hash is Data:
  H{a: U32, b: U32, c: U32, d: U32, e: U32, f: U32, g: U32, h: U32}

def rotr(+x: U32, +n: Nat) -> U32:
  ((x >> n) .|. (x << Nat.sub(32n, n)) : U32)

def big_sigma0(+a: U32) -> U32:
  ((rotr(a, 2n) .^. rotr(a, 13n)) .^. rotr(a, 22n) : U32)

def big_sigma1(+e: U32) -> U32:
  ((rotr(e, 6n) .^. rotr(e, 11n)) .^. rotr(e, 25n) : U32)

def small_sigma0(+x: U32) -> U32:
  ((rotr(x, 7n) .^. rotr(x, 18n)) .^. (x >> 3n) : U32)

def small_sigma1(+x: U32) -> U32:
  ((rotr(x, 17n) .^. rotr(x, 19n)) .^. (x >> 10n) : U32)

def choose(+e: U32, f: U32, g: U32) -> U32:
  ((e .&. f) .^. (U32.not(e) .&. g) : U32)

def majority(+a: U32, +b: U32, +c: U32) -> U32:
  (((a .&. b) .^. (a .&. c)) .^. (b .&. c) : U32)

# The round constants: the fractional parts of the cube roots of the first
# sixty-four primes.
def K() -> List<&2, U32>:
  [ 1116352408, 1899447441, 3049323471, 3921009573,  961987163, 1508970993, 2453635748, 2870763221,
    3624381080,  310598401,  607225278, 1426881987, 1925078388, 2162078206, 2614888103, 3248222580,
    3835390401, 4022224774,  264347078,  604807628,  770255983, 1249150122, 1555081692, 1996064986,
    2554220882, 2821834349, 2952996808, 3210313671, 3336571891, 3584528711,  113926993,  338241895,
     666307205,  773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037,
    2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909,  275423344,
     430227734,  506948616,  659060556,  883997877,  958139571, 1322822218, 1537002063, 1747873779,
    1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298 ]

# The initial hash: the fractional parts of the square roots of the first
# eight primes.
def initial() -> Hash:
  H{1779033703, 3144134277, 1013904242, 2773480762, 1359893119, 2600822924, 528734635, 1541459225}

# Padding
# -------

# Bytes become words, four at a time, big-endian. The caller has padded, so
# the count is a multiple of four; a ragged tail would be dropped.
def words(bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case b0 <> b1 <> b2 <> b3 <> rest:
      ((((b0 << 24n) .|. (b1 << 16n)) .|. (b2 << 8n)) .|. b3 : U32) <> words(rest)
    case _:
      Nil{}

# The standard's padding: a 1 bit, zeros to 56 mod 64, then the bit length
# in eight big-endian bytes. `n` is the byte count, kept as a U32 alongside
# the walk so no Nat is ever converted.
def trailer(+n: U32) -> List<&2, U32>:
  zeros = List.replicate(U32, U32.to_nat(((119 - (n .&. 63)) .&. 63 : U32)), 0)
  +bits_lo = (n << 3n : U32)
  +bits_hi = (n >> 29n : U32)
  tail = {[ (bits_hi >> 24n : U32), ((bits_hi >> 16n) .&. 255 : U32), ((bits_hi >> 8n) .&. 255 : U32), (bits_hi .&. 255 : U32),
            (bits_lo >> 24n : U32), ((bits_lo >> 16n) .&. 255 : U32), ((bits_lo >> 8n) .&. 255 : U32), (bits_lo .&. 255 : U32) ] : List<&2, U32>}
  128 <> List.append(&2, U32, zeros, tail)

def pad(bs: List<&2, U32>, n: U32) -> List<&2, U32>:
  match bs:
    case Nil{}:
      trailer(n)
    case b <> rest:
      b <> pad(rest, (n + 1 : U32))

# The message schedule
# --------------------

# A word of the schedule by how far back it is, on the schedule kept newest
# first. A miss is impossible once sixteen words are in; 0 keeps it total.
def back(ws: List<&2, U32>, n: Nat) -> U32:
  match ws n:
    case Nil{} _:
      0
    case w <> t 0n:
      w
    case w <> t 1n+p:
      back(t, p)

# Extends the schedule `left` more times: W[i] is σ1(W[i-2]) + W[i-7] +
# σ0(W[i-15]) + W[i-16]. `rev` is newest first, so those are 1, 6, 14, 15.
def extend(left: Nat, +rev: List<&2, U32>) -> List<&2, U32>:
  match left:
    case 0n:
      List.reverse(&2, U32, rev)
    case 1n+p:
      w = (((small_sigma1(back(rev, 1n)) + back(rev, 6n)) + small_sigma0(back(rev, 14n))) + back(rev, 15n) : U32)
      extend(p, w <> rev)

def schedule(block: List<&2, U32>) -> List<&2, U32>:
  extend(48n, List.reverse(&2, U32, block))

# Compression
# -----------

def round(st: Hash, +w: U32, +k: U32) -> Hash:
  match st:
    case H{+a, +b, +c, d, +e, +f, +g, h}:
      t1 = ((((h + big_sigma1(e)) + choose(e, f, g)) + k) + w : U32)
      +t1 = t1
      t2 = (big_sigma0(a) + majority(a, b, c) : U32)
      H{(t1 + t2 : U32), a, b, c, (d + t1 : U32), e, f, g}

def rounds(ws: List<&2, U32>, ks: List<&2, U32>, st: Hash) -> Hash:
  match ws ks:
    case w <> wt k <> kt:
      rounds(wt, kt, round(st, w, k))
    case _ _:
      st

def add_hash(x: Hash, y: Hash) -> Hash:
  match x y:
    case H{a, b, c, d, e, f, g, h} H{a2, b2, c2, d2, e2, f2, g2, h2}:
      H{(a + a2 : U32), (b + b2 : U32), (c + c2 : U32), (d + d2 : U32),
        (e + e2 : U32), (f + f2 : U32), (g + g2 : U32), (h + h2 : U32)}

# Every sixteen-word block, in order. The input is a padded message, so a
# ragged tail cannot occur; one would be dropped.
def blocks(ws: List<&2, U32>, +st: Hash) -> Hash:
  match ws:
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> w14 <> w15 <> rest:
      block = {[w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] : List<&2, U32>}
      blocks(rest, add_hash(st, rounds(schedule(block), K(), st)))
    case _:
      st

# The digest
# ----------

# The SHA-256 of a byte list, as eight words.
def digest_words(bs: List<&2, U32>) -> Hash:
  blocks(words(pad(bs, 0)), initial())

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
