# `diff` gives a file of bytes the size the host stated for its payload,
# and only that: sizing what it compares changes no side but one whose size
# was unknown, which keeps its digest and has a size only where a line the
# host answered names that very digest; and where the host answered the
# stat of a payload it located with the digest, a space and a size, a file
# of bytes with that payload is given that size.
import Base
import ./ops.bend as Ops
import ./text.bend as T
import ./commands.bend as Main
import ./string_lemmas.bend as S
import ./anchor_lemmas.bend as AL
import ./composition_lemmas.bend as Comp
import ./revision.bend as Rev
import ./plan_lemmas.bend as PlanL

def ndisc(m: Maybe<&2, Nat>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some(-n: Nat, e: {None{} == Some{n} : Maybe<&2, Nat>}) -> Empty:
  %e : {ndisc(_) : Type}
  Unit{}

# A size stated is given
# ----------------------

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def zdisc(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

def zero_succ(-p: Nat, e: {0n == 1n+p : Nat}) -> Empty:
  %e : {zdisc(_) : Type}
  Unit{}

def succ_zero(-p: Nat, e: {1n+p == 0n : Nat}) -> Empty:
  zero_succ(p, Equal.sym(Nat, 1n+p, 0n, e))

def or_false_l(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      {==}

def or_false_r(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, S.true_false(e))
    case False{}:
      e

def believed_app(b: Bool, +d: String, +st: String, -A: List<&2, T.Split>, -B: List<&2, T.Split>) -> {Main.sizes.believed(d, st, List.append(&2, T.Split, A, B), b) == List.append(&2, T.Split, Main.sizes.believed(d, st, A, b), B) : List<&2, T.Split>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# The host answers one stat line for each payload it located, so what is
# believed of the payloads before and after one is believed of each part.
def read_app(f1: List<&2, T.Split>, s1: List<&2, String>, hl: {List.length(&2, T.Split, f1) == List.length(&2, String, s1) : Nat}, +f2: List<&2, T.Split>, +s2: List<&2, String>) -> {Main.sizes.read(List.append(&2, T.Split, f1, f2), List.append(&2, String, s1, s2)) == List.append(&2, T.Split, Main.sizes.read(f1, s1), Main.sizes.read(f2, s2)) : List<&2, T.Split>}:
  match f1 s1:
    case Nil{} Nil{}:
      {==}
    case Nil{} st <> more:
      Empty.absurd({Main.sizes.read(f2, List.append(&2, String, st <> more, s2)) == List.append(&2, T.Split, Nil{}, Main.sizes.read(f2, s2)) : List<&2, T.Split>}, zero_succ(List.length(&2, String, more), hl))
    case T.Split{+x, +p} <> rest Nil{}:
      Empty.absurd({Main.sizes.read(List.append(&2, T.Split, T.Split{x, p} <> rest, f2), s2) == List.append(&2, T.Split, Main.sizes.read(T.Split{x, p} <> rest, Nil{}), Main.sizes.read(f2, s2)) : List<&2, T.Split>}, succ_zero(List.length(&2, T.Split, rest), hl))
    case T.Split{+x, +p} <> rest +st <> more:
      %Equal.sym(List<&2, T.Split>, Main.sizes.read(List.append(&2, T.Split, rest, f2), List.append(&2, String, more, s2)), List.append(&2, T.Split, Main.sizes.read(rest, more), Main.sizes.read(f2, s2)), read_app(rest, more, Equal.cong(Nat, Nat, k => pred(k), 1n+List.length(&2, T.Split, rest), 1n+List.length(&2, String, more), hl), f2, s2)) : {Main.sizes.believed(x, st, _, String.eq(T.word(st), x)) == List.append(&2, T.Split, Main.sizes.believed(x, st, Main.sizes.read(rest, more), String.eq(T.word(st), x)), Main.sizes.read(f2, s2)) : List<&2, T.Split>}
      believed_app(String.eq(T.word(st), x), x, st, Main.sizes.read(rest, more), Main.sizes.read(f2, s2))

def drop_after(t: String, +x: String, +k: Nat) -> {String.drop(t ++ x, Nat.add(String.length(t), k)) == String.drop(x, k) : String}:
  match t:
    case SNil{}:
      {==}
    case SCon{h, rest}:
      drop_after(rest, x, k)

def drop_zero(s: String) -> {String.drop(s, 0n) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

# The size after a sixty-four character digest and a space.
def size_at(+d: String, +size: String, hd: {String.length(d) == 64n : Nat}) -> {String.drop(d ++ (" " ++ size), 65n) == size : String}:
  %hd : {String.drop(d ++ (" " ++ size), Nat.add(_, 1n)) == size : String}
  Equal.trans(String, String.drop(d ++ (" " ++ size), Nat.add(String.length(d), 1n)), String.drop(size, 0n), size, drop_after(d, " " ++ size, 1n), drop_zero(size))

# The line the host answered for a digest is believed, with the size after it.
def read_head(+d: String, +p: String, +size: String, hd: {String.length(d) == 64n : Nat}, hs: {T.all_chars(~(c => Bool.not(Char.is_eq(c, ' '))), d) == True{} : Bool}, +f2: List<&2, T.Split>, +s2: List<&2, String>) -> {Main.sizes.read(T.Split{d, p} <> f2, (d ++ (" " ++ size)) <> s2) == T.Split{d, size} <> Main.sizes.read(f2, s2) : List<&2, T.Split>}:
  %Equal.sym(String, T.word(d ++ (" " ++ size)), d, PlanL.word_first(d, size, hs)) : {Main.sizes.believed(d, d ++ (" " ++ size), Main.sizes.read(f2, s2), String.eq(_, d)) == T.Split{d, size} <> Main.sizes.read(f2, s2) : List<&2, T.Split>}
  %Equal.sym(Bool, String.eq(d, d), True{}, S.eq_refl(d)) : {Main.sizes.believed(d, d ++ (" " ++ size), Main.sizes.read(f2, s2), _) == T.Split{d, size} <> Main.sizes.read(f2, s2) : List<&2, T.Split>}
  %Equal.sym(String, String.drop(d ++ (" " ++ size), 65n), size, size_at(d, size, hd)) : {T.Split{d, _} <> Main.sizes.read(f2, s2) == T.Split{d, size} <> Main.sizes.read(f2, s2) : List<&2, T.Split>}
  {==}

# What is believed of other payloads says nothing of this one.
def skip_hit(c: Bool, +x: String, +st: String, +d: String, -R: List<&2, T.Split>, +Y: List<&2, T.Split>, ex: {String.eq(x, d) == False{} : Bool}, ih: {Main.size_of(List.append(&2, T.Split, R, Y), d) == Main.size_of(Y, d) : Maybe<&2, Nat>}) -> {Main.size_of(List.append(&2, T.Split, Main.sizes.believed(x, st, R, c), Y), d) == Main.size_of(Y, d) : Maybe<&2, Nat>}:
  match c:
    case True{}:
      %Equal.sym(Bool, String.eq(x, d), False{}, ex) : {Bool.pick(Maybe<&2, Nat>, _, Nat.read(String.drop(st, 65n)), Main.size_of(List.append(&2, T.Split, R, Y), d)) == Main.size_of(Y, d) : Maybe<&2, Nat>}
      ih
    case False{}:
      ih

def skip_others(f1: List<&2, T.Split>, s1: List<&2, String>, +d: String, +hn: {Rev.member(T.map(~T.Split, ~String, ~(x => Main.split.head(x)), f1), d) == False{} : Bool}, +Y: List<&2, T.Split>) -> {Main.size_of(List.append(&2, T.Split, Main.sizes.read(f1, s1), Y), d) == Main.size_of(Y, d) : Maybe<&2, Nat>}:
  match f1 s1:
    case Nil{} _:
      {==}
    case T.Split{+x, p} <> rest Nil{}:
      {==}
    case T.Split{+x, p} <> +rest +st <> more:
      skip_hit(String.eq(T.word(st), x), x, st, d, Main.sizes.read(rest, more), Y,
        or_false_l(String.eq(x, d), Rev.member(T.map(~T.Split, ~String, ~(x => Main.split.head(x)), rest), d), hn),
        skip_others(rest, more, d, or_false_r(String.eq(x, d), Rev.member(T.map(~T.Split, ~String, ~(x => Main.split.head(x)), rest), d), hn), Y))

# So the size given a payload is the one the host answered for it.
def size_given(+f1: List<&2, T.Split>, +s1: List<&2, String>, hl: {List.length(&2, T.Split, f1) == List.length(&2, String, s1) : Nat}, +d: String, hn: {Rev.member(T.map(~T.Split, ~String, ~(x => Main.split.head(x)), f1), d) == False{} : Bool}, hd: {String.length(d) == 64n : Nat}, hs: {T.all_chars(~(c => Bool.not(Char.is_eq(c, ' '))), d) == True{} : Bool}, +p: String, +f2: List<&2, T.Split>, +size: String, +n: Nat, hz: {Nat.read(size) == Some{n} : Maybe<&2, Nat>}, +s2: List<&2, String>) -> {Main.size_of(Main.sizes.read(List.append(&2, T.Split, f1, T.Split{d, p} <> f2), List.append(&2, String, s1, (d ++ (" " ++ size)) <> s2)), d) == Some{n} : Maybe<&2, Nat>}:
  %Equal.sym(List<&2, T.Split>, Main.sizes.read(List.append(&2, T.Split, f1, T.Split{d, p} <> f2), List.append(&2, String, s1, (d ++ (" " ++ size)) <> s2)), List.append(&2, T.Split, Main.sizes.read(f1, s1), Main.sizes.read(T.Split{d, p} <> f2, (d ++ (" " ++ size)) <> s2)), read_app(f1, s1, hl, T.Split{d, p} <> f2, (d ++ (" " ++ size)) <> s2)) : {Main.size_of(_, d) == Some{n} : Maybe<&2, Nat>}
  %Equal.sym(List<&2, T.Split>, Main.sizes.read(T.Split{d, p} <> f2, (d ++ (" " ++ size)) <> s2), T.Split{d, size} <> Main.sizes.read(f2, s2), read_head(d, p, size, hd, hs, f2, s2)) : {Main.size_of(List.append(&2, T.Split, Main.sizes.read(f1, s1), _), d) == Some{n} : Maybe<&2, Nat>}
  %Equal.sym(Maybe<&2, Nat>, Main.size_of(List.append(&2, T.Split, Main.sizes.read(f1, s1), T.Split{d, size} <> Main.sizes.read(f2, s2)), d), Main.size_of(T.Split{d, size} <> Main.sizes.read(f2, s2), d), skip_others(f1, s1, d, hn, T.Split{d, size} <> Main.sizes.read(f2, s2))) : {_ == Some{n} : Maybe<&2, Nat>}
  %Equal.sym(Bool, String.eq(d, d), True{}, S.eq_refl(d)) : {Bool.pick(Maybe<&2, Nat>, _, Nat.read(size), Main.size_of(Main.sizes.read(f2, s2), d)) == Some{n} : Maybe<&2, Nat>}
  hz

# A file of bytes that went, or that came, is shown with the size the host
# answered for its payload.
def sized_given(+f1: List<&2, T.Split>, +s1: List<&2, String>, hl: {List.length(&2, T.Split, f1) == List.length(&2, String, s1) : Nat}, +d: String, hn: {Rev.member(T.map(~T.Split, ~String, ~(x => Main.split.head(x)), f1), d) == False{} : Bool}, hd: {String.length(d) == 64n : Nat}, hs: {T.all_chars(~(c => Bool.not(Char.is_eq(c, ' '))), d) == True{} : Bool}, +p: String, +f2: List<&2, T.Split>, +size: String, +n: Nat, hz: {Nat.read(size) == Some{n} : Maybe<&2, Nat>}, +s2: List<&2, String>, +from: Maybe<&2, String>, +to: Maybe<&2, String>, +modes: Maybe<&2, T.Split>, +targets: Maybe<&2, Main.Retarget>) -> {Main.sized(Main.sizes.read(List.append(&2, T.Split, f1, T.Split{d, p} <> f2), List.append(&2, String, s1, (d ++ (" " ++ size)) <> s2)), [Main.Compared{from, to, Some{Main.Side.Whole{d, None{}}}, None{}, modes, targets}, Main.Compared{from, to, None{}, Some{Main.Side.Whole{d, None{}}}, modes, targets}]) == [Main.Compared{from, to, Some{Main.Side.Whole{d, Some{n}}}, None{}, modes, targets}, Main.Compared{from, to, None{}, Some{Main.Side.Whole{d, Some{n}}}, modes, targets}] : List<&2, Main.Compared>}:
  %Equal.sym(Maybe<&2, Nat>, Main.size_of(Main.sizes.read(List.append(&2, T.Split, f1, T.Split{d, p} <> f2), List.append(&2, String, s1, (d ++ (" " ++ size)) <> s2)), d), Some{n}, size_given(f1, s1, hl, d, hn, hd, hs, p, f2, size, n, hz, s2)) : {[Main.Compared{from, to, Some{Main.Side.Whole{d, _}}, None{}, modes, targets}, Main.Compared{from, to, None{}, Some{Main.Side.Whole{d, _}}, modes, targets}] == [Main.Compared{from, to, Some{Main.Side.Whole{d, Some{n}}}, None{}, modes, targets}, Main.Compared{from, to, None{}, Some{Main.Side.Whole{d, Some{n}}}, modes, targets}] : List<&2, Main.Compared>}
  {==}

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
