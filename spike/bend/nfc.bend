# Unicode normal form C, as the Rust tool computes it: decision 0033's one
# spelling of a path, which `historica::format::nfc` takes from the
# `unicode-normalization` crate. A name the filesystem hands back
# decomposed, a path a person's keyboard spelled another way, and the path a
# store records are one path once each is in this form.
#
# The crate's algorithm, step for step, over a string's code points:
#
# - decompose each character fully and canonically — a Hangul syllable by
#   arithmetic, anything else by the table — so that `é` is `e` and U+0301;
# - put each run of characters with a combining class other than 0 in order
#   of class, keeping characters of one class as they came: canonical
#   ordering, which is what makes two orders of the same marks one string;
# - compose again, left to right: each character joins the last starter
#   where a pair makes something of them and nothing between them is of its
#   class or higher, or, for a starter, where nothing is between them at
#   all. The pairs are the primary composites, so a character the standard
#   excludes from composition stays decomposed.
#
# The tables are `nfc_tables.bend`, which `nfc.py` writes from what the
# crate answers of every scalar value, so the Unicode version is the Rust
# tool's (17.0.0), not Python's. `check.py`'s `nfc` stage holds `nfc` to the
# crate on a large sample, and each decomposition to the crate's own.
#
# A string of characters below U+0300 is its own normal form, which the
# tables say and the crate's quick check knows, and is handed back without
# a lookup: every ASCII path, and very nearly every path there is.

import Base
import ./nfc_tables.bend as Tab
import ./utf8.bend as Utf8

# Code points
# -----------

def points(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{x}, t}:
      x <> points(t)

def spelled(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case x <> rest:
      SCon{Chr{x}, spelled(rest)}

# The tables, read once for a string.
type Tabs is Data:
  Tabs{classes: List<&2, U32>, decompositions: List<&2, List<&2, U32>>, pairs: List<&2, U32>}

def tabs() -> Tabs:
  Tabs{Tab.classes(), Tab.decompositions(), Tab.pairs()}

def tabs.classes(t: Tabs) -> List<&2, U32>:
  match t:
    case Tabs{cs, ds, ps}:
      cs

def tabs.decompositions(t: Tabs) -> List<&2, List<&2, U32>>:
  match t:
    case Tabs{cs, ds, ps}:
      ds

def tabs.pairs(t: Tabs) -> List<&2, U32>:
  match t:
    case Tabs{cs, ds, ps}:
      ps

# Hangul
# ------

# Unicode's conjoining jamo arithmetic (3.12): a syllable is a leading
# consonant, a vowel and perhaps a trailing consonant, numbered from
# U+AC00, and decomposes and composes by counting rather than by table.
def hangul.is(+c: U32) -> Bool:
  Bool.and(U32.is_ge(c, 44032), U32.is_le(c, 55203))

def hangul.trail(+l: U32, +v: U32, +t: U32) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, U32.is_eq(t, 0), [l, v], [l, v, (4519 + t : U32)])

def hangul.parts(+c: U32) -> List<&2, U32>:
  +s = (c - 44032 : U32)
  hangul.trail((4352 + (s / 588 : U32) : U32), (4449 + ((s % 588 : U32) / 28 : U32) : U32), (s % 28 : U32))

# A leading consonant and a vowel make a syllable of two; a syllable of two
# and a trailing consonant make one of three.
def hangul.lv(+a: U32, +b: U32) -> Bool:
  Bool.and(Bool.and(U32.is_ge(a, 4352), U32.is_le(a, 4370)), Bool.and(U32.is_ge(b, 4449), U32.is_le(b, 4469)))

def hangul.lvt(+a: U32, +b: U32) -> Bool:
  Bool.and(Bool.and(hangul.is(a), U32.is_eq(((a - 44032 : U32) % 28 : U32), 0)), Bool.and(U32.is_ge(b, 4520), U32.is_le(b, 4546)))

# Classes
# -------

# Whether `c` comes before the run at the head of the table, which is in
# order: then no run below holds it either.
def run.after(rs: List<&2, U32>, +c: U32) -> Bool:
  match rs:
    case lo <> rest:
      U32.is_lt(c, lo)
    case _:
      True{}

# The class of the run at the head, where it reaches `c`.
def run.holds(rs: List<&2, U32>, +c: U32) -> Maybe<&2, U32>:
  match rs:
    case lo <> hi <> k <> rest:
      Bool.pick(Maybe<&2, U32>, U32.is_le(c, hi), Some{k}, None{})
    case _:
      None{}

def class.go(rs: List<&2, U32>, +c: U32, after: Bool, held: Maybe<&2, U32>) -> U32:
  match rs after held:
    case _ True{} _:
      0
    case _ False{} Some{k}:
      k
    case lo <> hi <> k <> +rest False{} None{}:
      class.go(rest, c, run.after(rest, c), run.holds(rest, c))
    case _ False{} None{}:
      0

# A character's canonical combining class: 0, a starter, unless a run says.
def class(+rs: List<&2, U32>, +c: U32) -> U32:
  class.go(rs, c, run.after(rs, c), run.holds(rs, c))

# Decomposition
# -------------

# How `c` compares with the character the head entry decomposes, the end of
# the table being past everything.
def entry.cmp(es: List<&2, List<&2, U32>>, +c: U32) -> Cmp:
  match es:
    case Con{Con{k, ds}, rest}:
      U32.cmp(c, k)
    case _:
      LT{}

def entry.go(es: List<&2, List<&2, U32>>, +c: U32, o: Cmp) -> List<&2, U32>:
  match es o:
    case _ LT{}:
      [c]
    case Con{Con{k, ds}, rest} EQ{}:
      ds
    case e <> +rest GT{}:
      entry.go(rest, c, entry.cmp(rest, c))
    case _ _:
      [c]

# One character's full canonical decomposition: itself for ASCII, which
# never decomposes, the jamo for a syllable, and otherwise what the table
# says or itself.
def decompose.one.of(+es: List<&2, List<&2, U32>>, +c: U32, ascii: Bool, syllable: Bool) -> List<&2, U32>:
  match ascii:
    case True{}:
      [c]
    case False{}:
      match syllable:
        case True{}:
          hangul.parts(c)
        case False{}:
          entry.go(es, c, entry.cmp(es, c))

def decompose.one(+es: List<&2, List<&2, U32>>, +c: U32) -> List<&2, U32>:
  decompose.one.of(es, c, U32.is_lt(c, 128), hangul.is(c))

def decompose(+es: List<&2, List<&2, U32>>, cs: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> rest:
      List.append(&2, U32, decompose.one(es, c), decompose(es, rest))

# Canonical ordering
# ------------------

# A character and its class, which ordering and composition both read.
type Mark is Data:
  Mark{c: U32, k: U32}

def mark.char(m: Mark) -> U32:
  match m:
    case Mark{c, k}:
      c

def mark.class(m: Mark) -> U32:
  match m:
    case Mark{c, k}:
      k

def unmarked(ms: List<&2, Mark>) -> List<&2, U32>:
  match ms:
    case Nil{}:
      Nil{}
    case m <> rest:
      mark.char(m) <> unmarked(rest)

def marked(+rs: List<&2, U32>, cs: List<&2, U32>) -> List<&2, Mark>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> rest:
      Mark{c, class(rs, c)} <> marked(rs, rest)

# Whether `m` goes after the head of a run: its class is no lower, so that
# marks of one class keep the order they came in.
def goes_after(run: List<&2, Mark>, +m: Mark) -> Bool:
  match run:
    case r <> rest:
      U32.is_le(mark.class(r), mark.class(m))
    case _:
      True{}

# One mark into a run already in order of class, after every mark of its
# class: an insertion sort, which is stable.
def insert.go(run: List<&2, Mark>, +m: Mark, after: Bool) -> List<&2, Mark>:
  match run after:
    case Nil{} _:
      [m]
    case r <> +rest True{}:
      r <> insert.go(rest, m, goes_after(rest, m))
    case r <> rest False{}:
      m <> r <> rest

def insert(+run: List<&2, Mark>, +m: Mark) -> List<&2, Mark>:
  insert.go(run, m, goes_after(run, m))

def starts(ms: List<&2, Mark>) -> Bool:
  match ms:
    case m <> rest:
      U32.is_eq(mark.class(m), 0)
    case _:
      True{}

# Each run of marks between starters, sorted by class as it closes: at the
# next starter, or at the end.
def order.go(ms: List<&2, Mark>, run: List<&2, Mark>, starter: Bool) -> List<&2, Mark>:
  match ms starter:
    case Nil{} _:
      run
    case m <> +rest True{}:
      List.append(&2, Mark, run, m <> order.go(rest, Nil{}, starts(rest)))
    case m <> +rest False{}:
      order.go(rest, insert(run, m), starts(rest))

def order(+ms: List<&2, Mark>) -> List<&2, Mark>:
  order.go(ms, Nil{}, starts(ms))

# Composition
# -----------

def lex(first: Cmp, then: Cmp) -> Cmp:
  match first:
    case LT{}:
      LT{}
    case EQ{}:
      then
    case GT{}:
      GT{}

# How the pair `a`, `b` compares with the head of the table, which is in
# order of the first and then the second, the end being past everything.
def pair.cmp(ps: List<&2, U32>, +a: U32, +b: U32) -> Cmp:
  match ps:
    case x <> y <> z <> rest:
      lex(U32.cmp(a, x), U32.cmp(b, y))
    case _:
      LT{}

def pair.go(ps: List<&2, U32>, +a: U32, +b: U32, o: Cmp) -> Maybe<&2, U32>:
  match ps o:
    case _ LT{}:
      None{}
    case x <> y <> z <> rest EQ{}:
      Some{z}
    case x <> y <> z <> +rest GT{}:
      pair.go(rest, a, b, pair.cmp(rest, a, b))
    case _ _:
      None{}

def compose.of(+ps: List<&2, U32>, +a: U32, +b: U32, lv: Bool, lvt: Bool) -> Maybe<&2, U32>:
  match lv:
    case True{}:
      Some{(44032 + ((((a - 4352 : U32) * 588 : U32) + ((b - 4449 : U32) * 28 : U32)) : U32) : U32)}
    case False{}:
      match lvt:
        case True{}:
          Some{(a + (b - 4519 : U32) : U32)}
        case False{}:
          pair.go(ps, a, b, pair.cmp(ps, a, b))

# What `a` and `b` compose to, if anything: the crate's `compose`.
def compose(+ps: List<&2, U32>, +a: U32, +b: U32) -> Maybe<&2, U32>:
  compose.of(ps, a, b, hangul.lv(a, b), hangul.lvt(a, b))

# The composition walk's state, the crate's `Recompositions`: what is out,
# reversed; the starter characters may still join; the class of the last
# character that did not join it, where one did not; and those characters,
# reversed.
type Walk is Data:
  Walk{out: List<&2, U32>, starter: Maybe<&2, U32>, last: Maybe<&2, U32>, held: List<&2, U32>}

# No starter yet: a mark goes out as it is, and a starter is taken.
def step.lone(+out: List<&2, U32>, +c: U32, +k: U32) -> Walk:
  Bool.pick(Walk, U32.is_eq(k, 0), Walk{out, Some{c}, None{}, Nil{}}, Walk{c <> out, None{}, None{}, Nil{}})

# What did not join: a starter closes the run and becomes the one joined
# to; anything else waits behind it.
def step.kept(+out: List<&2, U32>, +s: U32, +held: List<&2, U32>, +c: U32, +k: U32) -> Walk:
  Bool.pick(Walk, U32.is_eq(k, 0), Walk{List.append(&2, U32, held, s <> out), Some{c}, None{}, Nil{}}, Walk{out, Some{s}, Some{k}, c <> held})

def step.joined(out: List<&2, U32>, last: Maybe<&2, U32>, held: List<&2, U32>, joined: Maybe<&2, U32>, +s: U32, +c: U32, +k: U32) -> Walk:
  match joined:
    case Some{r}:
      Walk{out, Some{r}, last, held}
    case None{}:
      step.kept(out, s, held, c, k)

# Behind something that did not join: only a character of a higher class
# than the last of those may still join the starter; one of the same class
# or lower is blocked from it.
def step.behind(+ps: List<&2, U32>, out: List<&2, U32>, +s: U32, +l: U32, held: List<&2, U32>, +c: U32, +k: U32, higher: Bool) -> Walk:
  match higher:
    case True{}:
      step.joined(out, Some{l}, held, compose(ps, s, c), s, c, k)
    case False{}:
      step.kept(out, s, held, c, k)

# The last starter and one more character: next to it, they may join, and
# behind what did not join, as `step.behind` says.
def step.at(+ps: List<&2, U32>, out: List<&2, U32>, +s: U32, last: Maybe<&2, U32>, held: List<&2, U32>, +c: U32, +k: U32) -> Walk:
  match last:
    case None{}:
      step.joined(out, None{}, held, compose(ps, s, c), s, c, k)
    case Some{+l}:
      step.behind(ps, out, s, l, held, c, k, U32.is_lt(l, k))

def step(+ps: List<&2, U32>, w: Walk, m: Mark) -> Walk:
  match w m:
    case Walk{out, None{}, last, held} Mark{+c, +k}:
      step.lone(out, c, k)
    case Walk{out, Some{+s}, last, held} Mark{+c, +k}:
      step.at(ps, out, s, last, held, c, k)

def walk.go(+ps: List<&2, U32>, ms: List<&2, Mark>, w: Walk) -> Walk:
  match ms:
    case Nil{}:
      w
    case m <> rest:
      walk.go(ps, rest, step(ps, w, m))

# What the walk leaves: the starter, and what waited behind it.
def walk.done(w: Walk) -> List<&2, U32>:
  match w:
    case Walk{out, None{}, last, held}:
      List.reverse(&2, U32, List.append(&2, U32, held, out))
    case Walk{out, Some{s}, last, held}:
      List.reverse(&2, U32, List.append(&2, U32, held, s <> out))

def recompose(+ps: List<&2, U32>, ms: List<&2, Mark>) -> List<&2, U32>:
  walk.done(walk.go(ps, ms, Walk{Nil{}, None{}, None{}, Nil{}}))

# Normal form C
# -------------

# The code points of a string, decomposed, ordered and composed.
def nfc.points(t: Tabs, cs: List<&2, U32>) -> List<&2, U32>:
  match t:
    case Tabs{+rs, +es, +ps}:
      recompose(ps, order(marked(rs, decompose(es, cs))))

# Every character below the first that normalising could change.
def quick(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{+x}, t}:
      Bool.and(Bool.or(U32.is_lt(x, 128), U32.is_lt(x, Tab.inert_below())), quick(t))

def nfc.of(+s: String, fast: Bool) -> String:
  match fast:
    case True{}:
      s
    case False{}:
      spelled(nfc.points(tabs(), points(s)))

# `s` in normal form C: `historica::format::nfc`.
def nfc(+s: String) -> String:
  nfc.of(s, quick(s))

# Whether `s` is already in normal form C: the rule `check_path` holds a
# path a document states to.
def is_nfc(+s: String) -> Bool:
  String.eq(nfc(s), s)

# `check.py`'s `nfc` stage
# ------------------------

# Canonical decomposition and ordering alone: normal form D, which is what
# composition starts from.
def nfd.points(t: Tabs, cs: List<&2, U32>) -> List<&2, U32>:
  match t:
    case Tabs{+rs, +es, ps}:
      unmarked(order(marked(rs, decompose(es, cs))))

def shown(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case x <> Nil{}:
      U32.show(x)
    case x <> rest:
      U32.show(x) ++ " " ++ shown(rest)

# Each line's normal forms C and D, as code points in decimal with a bar
# between: what `ffi/examples/nfc_tables.rs nfc` prints of the same line.
def cases(+t: Tabs, ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      SNil{}
    case SNil{} <> rest:
      cases(t, rest)
    case +l <> rest:
      shown(points(nfc(l))) ++ "|" ++ shown(nfd.points(t, points(l))) ++ "\n" ++ cases(t, rest)

def main.of(args: List<&1, String>) -> IO(Unit):
  match args:
    case Nil{}:
      IO.print("nfc.bend <cases>: one string a line")
    case path <> rest:
      do IO<Unit>:
        bs : List<&2, U32> <- Utf8.read_file(path)
        IO.write(cases(tabs(), String.lines(Utf8.decode(bs))))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    main.of(args)
