# `diff` gives a file of bytes the size the host stated for its payload, and
# nothing else: sizing what it compares changes no side but one whose size
# was unknown, which keeps its digest and has a size only where the host
# answered a line for that very digest.
import Base
import ./ops.bend as Ops
import ./text.bend as T
import ./commands.bend as Main
import ./string_lemmas.bend as S
import ./anchor_lemmas.bend as AL
import ./composition_lemmas.bend as Comp

def ndisc(m: Maybe<&2, Nat>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some(-n: Nat, e: {None{} == Some{n} : Maybe<&2, Nat>}) -> Empty:
  %e : {ndisc(_) : Type}
  Unit{}

# Sameness is reflexive
# ---------------------

def xor_self(b: Bool) -> {Bool.not(Bool.xor(b, b)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def item_refl(it: Ops.Item) -> {Main.item_eq(it, it) == True{} : Bool}:
  match it:
    case Ops.Item{+t, +n, +f}:
      AL.and_intro(String.eq(t, t), Bool.and(Bool.not(Bool.xor(n, n)), Bool.not(Bool.xor(f, f))), S.eq_refl(t),
        AL.and_intro(Bool.not(Bool.xor(n, n)), Bool.not(Bool.xor(f, f)), xor_self(n), xor_self(f)))

def items_refl(xs: List<&2, Ops.Item>) -> {Main.items_eq(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Main.item_eq(x, x), Main.items_eq(rest, rest), item_refl(x), items_refl(rest))

def same_refl(s: Maybe<&2, Main.Side>) -> {Main.side.same(s, s) == True{} : Bool}:
  match s:
    case None{}:
      {==}
    case Some{Main.Side.Lines{+items}}:
      items_refl(items)
    case Some{Main.Side.Whole{+d, None{}}}:
      AL.and_intro(String.eq(d, d), True{}, S.eq_refl(d), {==})
    case Some{Main.Side.Whole{+d, Some{+k}}}:
      AL.and_intro(String.eq(d, d), Nat.is_eq(k, k), S.eq_refl(d), Comp.eq_refl(k))

# A size believed is one stated
# -----------------------------

# The line believed for a digest names it, and gives the size read.
def hit_says(c: Bool, +st: String, +x: String, +d: String, +n: Nat, +more: List<&2, String>, +R: List<&2, T.Split>, +ew: {String.eq(T.word(st), x) == True{} : Bool}, +ec: {String.eq(x, d) == c : Bool}, e: {Bool.pick(Maybe<&2, Nat>, c, Nat.read(String.drop(st, 65n)), Main.size_of(R, d)) == Some{n} : Maybe<&2, Nat>}, ih: {Main.size_of(R, d) == Some{n} : Maybe<&2, Nat>} -> {Main.stat.says(more, d, n) == True{} : Bool}) -> {Main.stat.says(st <> more, d, n) == True{} : Bool}:
  match c:
    case True{}:
      +wx = S.eq_true(T.word(st), x, ew)
      +xd = S.eq_true(x, d, ec)
      AL.or_left(Bool.and(String.eq(T.word(st), d), Main.nat.is(Nat.read(String.drop(st, 65n)), n)), Main.stat.says(more, d, n),
        AL.and_intro(String.eq(T.word(st), d), Main.nat.is(Nat.read(String.drop(st, 65n)), n),
          (%Equal.sym(String, T.word(st), d, Equal.trans(String, T.word(st), x, d, wx, xd)) : {String.eq(_, d) == True{} : Bool}; S.eq_refl(d)),
          (%Equal.sym(Maybe<&2, Nat>, Nat.read(String.drop(st, 65n)), Some{n}, e) : {Main.nat.is(_, n) == True{} : Bool}; Comp.eq_refl(n))))
    case False{}:
      AL.or_right(Bool.and(String.eq(T.word(st), d), Main.nat.is(Nat.read(String.drop(st, 65n)), n)), Main.stat.says(more, d, n), ih(e))

def believed_says(b: Bool, +st: String, +x: String, +d: String, +n: Nat, +more: List<&2, String>, +R: List<&2, T.Split>, +eb: {String.eq(T.word(st), x) == b : Bool}, e: {Main.size_of(Main.sizes.believed(x, st, R, b), d) == Some{n} : Maybe<&2, Nat>}, ih: {Main.size_of(R, d) == Some{n} : Maybe<&2, Nat>} -> {Main.stat.says(more, d, n) == True{} : Bool}) -> {Main.stat.says(st <> more, d, n) == True{} : Bool}:
  match b:
    case True{}:
      hit_says(String.eq(x, d), st, x, d, n, more, R, eb, {==}, e, ih)
    case False{}:
      AL.or_right(Bool.and(String.eq(T.word(st), d), Main.nat.is(Nat.read(String.drop(st, 65n)), n)), Main.stat.says(more, d, n), ih(e))

# Whatever size `size_of` finds for a digest among those believed, the host
# stated it for that digest.
def says(found: List<&2, T.Split>, stats: List<&2, String>, +d: String, +n: Nat, e: {Main.size_of(Main.sizes.read(found, stats), d) == Some{n} : Maybe<&2, Nat>}) -> {Main.stat.says(stats, d, n) == True{} : Bool}:
  match found stats:
    case Nil{} _:
      Empty.absurd({Main.stat.says(stats, d, n) == True{} : Bool}, none_some(n, e))
    case T.Split{+x, p} <> rest Nil{}:
      Empty.absurd({Main.stat.says(Nil{}, d, n) == True{} : Bool}, none_some(n, e))
    case T.Split{+x, p} <> +rest +st <> +more:
      believed_says(String.eq(T.word(st), x), st, x, d, n, more, Main.sizes.read(rest, more), {==}, e, h => says(rest, more, d, n, h))

# One side
# --------

def given_ok(+stats: List<&2, String>, +found: List<&2, T.Split>, +d: String, m: Maybe<&2, Nat>, +em: {Main.size_of(Main.sizes.read(found, stats), d) == m : Maybe<&2, Nat>}) -> {Main.side.given(stats, d, Some{Main.Side.Whole{d, m}}) == True{} : Bool}:
  match m:
    case None{}:
      S.eq_refl(d)
    case Some{+n}:
      AL.and_intro(String.eq(d, d), Main.stat.says(stats, d, n), S.eq_refl(d), says(found, stats, d, n, em))

def side_told(+stats: List<&2, String>, +found: List<&2, T.Split>, s: Maybe<&2, Main.Side>) -> {Main.side.told(stats, s, Main.side.sized(Main.sizes.read(found, stats), s)) == True{} : Bool}:
  match s:
    case None{}:
      {==}
    case Some{Main.Side.Lines{+items}}:
      items_refl(items)
    case Some{Main.Side.Whole{+d, None{}}}:
      given_ok(stats, found, d, Main.size_of(Main.sizes.read(found, stats), d), {==})
    case Some{Main.Side.Whole{+d, Some{+k}}}:
      AL.and_intro(String.eq(d, d), Nat.is_eq(k, k), S.eq_refl(d), Comp.eq_refl(k))

# Sizing what `diff` compares changes no side but one whose size was
# unknown, and gives that one only a size the host stated for its digest.
def sized_told(+found: List<&2, T.Split>, +stats: List<&2, String>, cs: List<&2, Main.Compared>) -> {Main.sizes.told(stats, cs, Main.sized(Main.sizes.read(found, stats), cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Main.Compared{+f, +t, +b, +a, +m, +g} <> +rest:
      AL.and_intro(Bool.and(Main.side.told(stats, b, Main.side.sized(Main.sizes.read(found, stats), b)), Main.side.told(stats, a, Main.side.sized(Main.sizes.read(found, stats), a))), Main.sizes.told(stats, rest, Main.sized(Main.sizes.read(found, stats), rest)),
        AL.and_intro(Main.side.told(stats, b, Main.side.sized(Main.sizes.read(found, stats), b)), Main.side.told(stats, a, Main.side.sized(Main.sizes.read(found, stats), a)), side_told(stats, found, b), side_told(stats, found, a)),
        sized_told(found, stats, rest))
