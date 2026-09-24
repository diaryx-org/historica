# What `diff` prints, `patch` reads back. The hunks diff groups a comparison
# into — each run of lines within three of a change — read as `patch` reads
# a unified diff, without fuzz, take the lines that are not arrivals to the
# lines that are not removals; so the hunks diff draws for a document take
# the parent to the child.
import Base
import ./ops.bend as Ops
import ./commands.bend as Main
import ./laid_lemmas.bend as LaidL
import ./position_lemmas.bend as Pos
import ./composition_lemmas.bend as Comp
import ./merge_lemmas.bend as ML
import ./string_lemmas.bend as S

# Basics
# ------

def nat_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat_refl(p)

def xor_self(b: Bool) -> {Bool.not(Bool.xor(b, b)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def item_refl(x: Ops.Item) -> {Main.item_eq(x, x) == True{} : Bool}:
  match x:
    case Ops.Item{+t, +n, +f}:
      ML.and_intro(String.eq(t, t), Bool.and(Bool.not(Bool.xor(n, n)), Bool.not(Bool.xor(f, f))), S.eq_refl(t), ML.and_intro(Bool.not(Bool.xor(n, n)), Bool.not(Bool.xor(f, f)), xor_self(n), xor_self(f)))

def lapp_nil(xs: List<&2, Ops.Item>) -> {List.append(&2, Ops.Item, xs, Nil{}) == xs : List<&2, Ops.Item>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => x <> l, List.append(&2, Ops.Item, rest, Nil{}), rest, lapp_nil(rest))

def nlapp_nil(xs: List<&2, Main.Numbered>) -> {List.append(&2, Main.Numbered, xs, Nil{}) == xs : List<&2, Main.Numbered>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Equal.cong(List<&2, Main.Numbered>, List<&2, Main.Numbered>, l => x <> l, List.append(&2, Main.Numbered, rest, Nil{}), rest, nlapp_nil(rest))

# Two marks a line cannot both have.
def clash(+s: String, +x: String, +y: String, ex: {String.eq(s, x) == True{} : Bool}, ey: {String.eq(s, y) == True{} : Bool}, ne: {String.eq(x, y) == False{} : Bool}) -> Empty:
  S.false_true(Equal.trans(Bool, False{}, String.eq(x, y), True{}, Equal.sym(Bool, String.eq(x, y), False{}, ne),
    Equal.trans(Bool, String.eq(x, y), String.eq(s, y), True{}, Equal.cong(String, Bool, z => String.eq(z, y), x, s, Equal.sym(String, s, x, S.eq_true(s, x, ex))), ey)))

# The lines of a hunk, and each side of them
# ------------------------------------------

def nlaids(ns: List<&2, Main.Numbered>) -> List<&2, Main.Laid>:
  match ns:
    case Nil{}:
      Nil{}
    case Main.Numbered{l, b, a} <> rest:
      l <> nlaids(rest)

def lold(ns: List<&2, Main.Numbered>) -> List<&2, Ops.Item>:
  Main.laid.old(nlaids(ns))

def lnew(ns: List<&2, Main.Numbered>) -> List<&2, Ops.Item>:
  Main.laid.new(nlaids(ns))

def sign_ok(+s: String) -> Bool:
  Bool.or(String.eq(s, "+"), Bool.or(String.eq(s, "-"), String.eq(s, " ")))

def nsigns(ns: List<&2, Main.Numbered>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Main.Numbered{Main.Laid{s, it}, b, a} <> rest:
      Bool.and(sign_ok(s), nsigns(rest))

def lsigns(ls: List<&2, Main.Laid>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Main.Laid{s, it} <> rest:
      Bool.and(sign_ok(s), lsigns(rest))

# Reading a hunk's lines
# ----------------------

def line_plus(+it: Ops.Item, -b: Nat, -a: Nat, q: List<&2, Ops.Item>, o: List<&2, Ops.Item>, t: Nat, g: Nat) -> {Main.patch.line(Main.Numbered{Main.Laid{"+", it}, b, a}, Main.Patched{q, o, t, g}) == Done{Main.Patched{q, List.append(&2, Ops.Item, o, [it]), t, 1n+g}} : Result<&2, &2, String, Main.Patched>}:
  {==}

def line_minus(+it: Ops.Item, -b: Nat, -a: Nat, q: List<&2, Ops.Item>, o: List<&2, Ops.Item>, t: Nat, g: Nat) -> {Main.patch.line(Main.Numbered{Main.Laid{"-", it}, b, a}, Main.Patched{it <> q, o, t, g}) == Done{Main.Patched{q, o, 1n+t, g}} : Result<&2, &2, String, Main.Patched>}:
  %Equal.sym(Bool, Main.item_eq(it, it), True{}, item_refl(it)) : {Main.patch.same(_, False{}, it, q, o, t, g) == Done{Main.Patched{q, o, 1n+t, g}} : Result<&2, &2, String, Main.Patched>}
  {==}

def line_space(+it: Ops.Item, -b: Nat, -a: Nat, q: List<&2, Ops.Item>, o: List<&2, Ops.Item>, t: Nat, g: Nat) -> {Main.patch.line(Main.Numbered{Main.Laid{" ", it}, b, a}, Main.Patched{it <> q, o, t, g}) == Done{Main.Patched{q, List.append(&2, Ops.Item, o, [it]), 1n+t, 1n+g}} : Result<&2, &2, String, Main.Patched>}:
  %Equal.sym(Bool, Main.item_eq(it, it), True{}, item_refl(it)) : {Main.patch.same(_, True{}, it, q, o, t, g) == Done{Main.Patched{q, List.append(&2, Ops.Item, o, [it]), 1n+t, 1n+g}} : Result<&2, &2, String, Main.Patched>}
  {==}

# Each line of a hunk read in turn: context and removals off the parent,
# context and arrivals written, and each side's lines counted.
def lines_sign(bp: Bool, bm: Bool, bs: Bool, +s: String, +it: Ops.Item, +rest: List<&2, Main.Numbered>, +p: List<&2, Ops.Item>, +o: List<&2, Ops.Item>, +t: Nat, +g: Nat, ebp: {String.eq(s, "+") == bp : Bool}, ebm: {String.eq(s, "-") == bm : Bool}, ebs: {String.eq(s, " ") == bs : Bool}, hs: {Bool.or(bp, Bool.or(bm, bs)) == True{} : Bool}, ih: @o2: List<&2, Ops.Item> -> @t2: Nat -> @g2: Nat -> {Main.patch.lines(rest, Done{Main.Patched{List.append(&2, Ops.Item, lold(rest), p), o2, t2, g2}}) == Done{Main.Patched{p, List.append(&2, Ops.Item, o2, lnew(rest)), Nat.add(Main.hunk.count(rest, "+"), t2), Nat.add(Main.hunk.count(rest, "-"), g2)}} : Result<&2, &2, String, Main.Patched>}) -> {Main.patch.lines(rest, Main.patch.sign(bp, bm, bs, it, Main.Patched{List.append(&2, Ops.Item, Main.laid.side(bp, it, lold(rest)), p), o, t, g})) == Done{Main.Patched{p, List.append(&2, Ops.Item, o, Main.laid.side(bm, it, lnew(rest))), Nat.add(Nat.add(Bool.pick(Nat, bp, 0n, 1n), Main.hunk.count(rest, "+")), t), Nat.add(Nat.add(Bool.pick(Nat, bm, 0n, 1n), Main.hunk.count(rest, "-")), g)}} : Result<&2, &2, String, Main.Patched>}:
  match bp bm bs:
    case True{} True{} _:
      Empty.absurd({Main.patch.lines(rest, Main.patch.sign(True{}, True{}, bs, it, Main.Patched{List.append(&2, Ops.Item, Main.laid.side(True{}, it, lold(rest)), p), o, t, g})) == Done{Main.Patched{p, List.append(&2, Ops.Item, o, Main.laid.side(True{}, it, lnew(rest))), Nat.add(Nat.add(Bool.pick(Nat, True{}, 0n, 1n), Main.hunk.count(rest, "+")), t), Nat.add(Nat.add(Bool.pick(Nat, True{}, 0n, 1n), Main.hunk.count(rest, "-")), g)}} : Result<&2, &2, String, Main.Patched>}, clash(s, "+", "-", ebp, ebm, {==}))
    case True{} False{} True{}:
      Empty.absurd({Main.patch.lines(rest, Main.patch.sign(True{}, False{}, True{}, it, Main.Patched{List.append(&2, Ops.Item, Main.laid.side(True{}, it, lold(rest)), p), o, t, g})) == Done{Main.Patched{p, List.append(&2, Ops.Item, o, Main.laid.side(False{}, it, lnew(rest))), Nat.add(Nat.add(Bool.pick(Nat, True{}, 0n, 1n), Main.hunk.count(rest, "+")), t), Nat.add(Nat.add(Bool.pick(Nat, False{}, 0n, 1n), Main.hunk.count(rest, "-")), g)}} : Result<&2, &2, String, Main.Patched>}, clash(s, "+", " ", ebp, ebs, {==}))
    case True{} False{} False{}:
      %LaidL.app_assoc(o, [it], lnew(rest)) : {Main.patch.lines(rest, Done{Main.Patched{List.append(&2, Ops.Item, lold(rest), p), List.append(&2, Ops.Item, o, [it]), t, 1n+g}}) == Done{Main.Patched{p, _, Nat.add(Main.hunk.count(rest, "+"), t), 1n+Nat.add(Main.hunk.count(rest, "-"), g)}} : Result<&2, &2, String, Main.Patched>}
      %Pos.add_succ(Main.hunk.count(rest, "-"), g) : {Main.patch.lines(rest, Done{Main.Patched{List.append(&2, Ops.Item, lold(rest), p), List.append(&2, Ops.Item, o, [it]), t, 1n+g}}) == Done{Main.Patched{p, List.append(&2, Ops.Item, List.append(&2, Ops.Item, o, [it]), lnew(rest)), Nat.add(Main.hunk.count(rest, "+"), t), _}} : Result<&2, &2, String, Main.Patched>}
      ih(List.append(&2, Ops.Item, o, [it]), t, 1n+g)
    case False{} True{} True{}:
      Empty.absurd({Main.patch.lines(rest, Main.patch.sign(False{}, True{}, True{}, it, Main.Patched{List.append(&2, Ops.Item, Main.laid.side(False{}, it, lold(rest)), p), o, t, g})) == Done{Main.Patched{p, List.append(&2, Ops.Item, o, Main.laid.side(True{}, it, lnew(rest))), Nat.add(Nat.add(Bool.pick(Nat, False{}, 0n, 1n), Main.hunk.count(rest, "+")), t), Nat.add(Nat.add(Bool.pick(Nat, True{}, 0n, 1n), Main.hunk.count(rest, "-")), g)}} : Result<&2, &2, String, Main.Patched>}, clash(s, "-", " ", ebm, ebs, {==}))
    case False{} True{} False{}:
      %Equal.sym(Bool, Main.item_eq(it, it), True{}, item_refl(it)) : {Main.patch.lines(rest, Main.patch.same(_, False{}, it, List.append(&2, Ops.Item, lold(rest), p), o, t, g)) == Done{Main.Patched{p, List.append(&2, Ops.Item, o, lnew(rest)), 1n+Nat.add(Main.hunk.count(rest, "+"), t), Nat.add(Main.hunk.count(rest, "-"), g)}} : Result<&2, &2, String, Main.Patched>}
      %Pos.add_succ(Main.hunk.count(rest, "+"), t) : {Main.patch.lines(rest, Done{Main.Patched{List.append(&2, Ops.Item, lold(rest), p), o, 1n+t, g}}) == Done{Main.Patched{p, List.append(&2, Ops.Item, o, lnew(rest)), _, Nat.add(Main.hunk.count(rest, "-"), g)}} : Result<&2, &2, String, Main.Patched>}
      ih(o, 1n+t, g)
    case False{} False{} True{}:
      %LaidL.app_assoc(o, [it], lnew(rest)) : {Main.patch.lines(rest, Main.patch.sign(False{}, False{}, True{}, it, Main.Patched{List.append(&2, Ops.Item, it <> lold(rest), p), o, t, g})) == Done{Main.Patched{p, _, 1n+Nat.add(Main.hunk.count(rest, "+"), t), 1n+Nat.add(Main.hunk.count(rest, "-"), g)}} : Result<&2, &2, String, Main.Patched>}
      %Equal.sym(Bool, Main.item_eq(it, it), True{}, item_refl(it)) : {Main.patch.lines(rest, Main.patch.same(_, True{}, it, List.append(&2, Ops.Item, lold(rest), p), o, t, g)) == Done{Main.Patched{p, List.append(&2, Ops.Item, List.append(&2, Ops.Item, o, [it]), lnew(rest)), 1n+Nat.add(Main.hunk.count(rest, "+"), t), 1n+Nat.add(Main.hunk.count(rest, "-"), g)}} : Result<&2, &2, String, Main.Patched>}
      %Pos.add_succ(Main.hunk.count(rest, "+"), t) : {Main.patch.lines(rest, Done{Main.Patched{List.append(&2, Ops.Item, lold(rest), p), List.append(&2, Ops.Item, o, [it]), 1n+t, 1n+g}}) == Done{Main.Patched{p, List.append(&2, Ops.Item, List.append(&2, Ops.Item, o, [it]), lnew(rest)), _, 1n+Nat.add(Main.hunk.count(rest, "-"), g)}} : Result<&2, &2, String, Main.Patched>}
      %Pos.add_succ(Main.hunk.count(rest, "-"), g) : {Main.patch.lines(rest, Done{Main.Patched{List.append(&2, Ops.Item, lold(rest), p), List.append(&2, Ops.Item, o, [it]), 1n+t, 1n+g}}) == Done{Main.Patched{p, List.append(&2, Ops.Item, List.append(&2, Ops.Item, o, [it]), lnew(rest)), Nat.add(Main.hunk.count(rest, "+"), 1n+t), _}} : Result<&2, &2, String, Main.Patched>}
      ih(List.append(&2, Ops.Item, o, [it]), 1n+t, 1n+g)
    case False{} False{} False{}:
      Empty.absurd({Main.patch.lines(rest, Main.patch.sign(False{}, False{}, False{}, it, Main.Patched{List.append(&2, Ops.Item, Main.laid.side(False{}, it, lold(rest)), p), o, t, g})) == Done{Main.Patched{p, List.append(&2, Ops.Item, o, Main.laid.side(False{}, it, lnew(rest))), Nat.add(Nat.add(Bool.pick(Nat, False{}, 0n, 1n), Main.hunk.count(rest, "+")), t), Nat.add(Nat.add(Bool.pick(Nat, False{}, 0n, 1n), Main.hunk.count(rest, "-")), g)}} : Result<&2, &2, String, Main.Patched>}, S.false_true(hs))

def lines_ok(ks: List<&2, Main.Numbered>, +p: List<&2, Ops.Item>, +o: List<&2, Ops.Item>, +t: Nat, +g: Nat, +hs: {nsigns(ks) == True{} : Bool}) -> {Main.patch.lines(ks, Done{Main.Patched{List.append(&2, Ops.Item, lold(ks), p), o, t, g}}) == Done{Main.Patched{p, List.append(&2, Ops.Item, o, lnew(ks)), Nat.add(Main.hunk.count(ks, "+"), t), Nat.add(Main.hunk.count(ks, "-"), g)}} : Result<&2, &2, String, Main.Patched>}:
  match ks:
    case Nil{}:
      %lapp_nil(o) : {Done{Main.Patched{p, _, t, g}} == Done{Main.Patched{p, List.append(&2, Ops.Item, o, Nil{}), t, g}} : Result<&2, &2, String, Main.Patched>}
      {==}
    case Main.Numbered{Main.Laid{+s, +it}, b, a} <> +rest:
      lines_sign(String.eq(s, "+"), String.eq(s, "-"), String.eq(s, " "), s, it, rest, p, o, t, g, {==}, {==}, {==}, Comp.and_left(sign_ok(s), nsigns(rest), hs),
        o2 => t2 => g2 => lines_ok(rest, p, o2, t2, g2, Comp.and_right(sign_ok(s), nsigns(rest), hs)))

# Finding a hunk
# --------------

def succ_ne(+m: Nat, at: Nat) -> {Nat.is_eq(1n+Nat.add(m, at), at) == False{} : Bool}:
  match at:
    case 0n:
      {==}
    case 1n+q:
      %Equal.sym(Nat, Nat.add(m, 1n+q), 1n+Nat.add(m, q), Pos.add_succ(m, q)) : {Nat.is_eq(1n+_, 1n+q) == False{} : Bool}
      succ_ne(m, q)

def skip_here(q: List<&2, Ops.Item>, +at: Nat, +nat: Nat) -> {Main.patch.skip(q, at, nat, at, nat) == Done{Main.Skipped{Nil{}, q}} : Result<&2, &2, String, Main.Skipped>}:
  match q:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(at, at), True{}, nat_refl(at)) : {Main.patch.end(_, Nat.is_eq(nat, nat)) == Done{Main.Skipped{Nil{}, Nil{}}} : Result<&2, &2, String, Main.Skipped>}
      %Equal.sym(Bool, Nat.is_eq(nat, nat), True{}, nat_refl(nat)) : {Main.patch.end(True{}, _) == Done{Main.Skipped{Nil{}, Nil{}}} : Result<&2, &2, String, Main.Skipped>}
      {==}
    case x <> xs:
      %Equal.sym(Bool, Nat.is_eq(at, at), True{}, nat_refl(at)) : {Main.patch.here(_, Nat.is_eq(nat, nat), x, xs, Main.patch.skip(xs, 1n+at, 1n+nat, at, nat)) == Done{Main.Skipped{Nil{}, x <> xs}} : Result<&2, &2, String, Main.Skipped>}
      %Equal.sym(Bool, Nat.is_eq(nat, nat), True{}, nat_refl(nat)) : {Main.patch.here(True{}, _, x, xs, Main.patch.skip(xs, 1n+at, 1n+nat, at, nat)) == Done{Main.Skipped{Nil{}, x <> xs}} : Result<&2, &2, String, Main.Skipped>}
      {==}

# The parent's lines before a hunk are copied, and it is found where its
# header says.
def skip_ok(g: List<&2, Ops.Item>, +q: List<&2, Ops.Item>, +at: Nat, +nat: Nat, +so: Nat, +sn: Nat, +eo: {Nat.add(List.length(&2, Ops.Item, g), at) == so : Nat}, en: {Nat.add(List.length(&2, Ops.Item, g), nat) == sn : Nat}) -> {Main.patch.skip(List.append(&2, Ops.Item, g, q), at, nat, so, sn) == Done{Main.Skipped{g, q}} : Result<&2, &2, String, Main.Skipped>}:
  match g:
    case Nil{}:
      %eo : {Main.patch.skip(List.append(&2, Ops.Item, Nil{}, q), at, nat, _, sn) == Done{Main.Skipped{Nil{}, q}} : Result<&2, &2, String, Main.Skipped>}
      %en : {Main.patch.skip(List.append(&2, Ops.Item, Nil{}, q), at, nat, at, _) == Done{Main.Skipped{Nil{}, q}} : Result<&2, &2, String, Main.Skipped>}
      skip_here(q, at, nat)
    case +x <> +rest:
      %Equal.sym(Result<&2, &2, String, Main.Skipped>, Main.patch.skip(List.append(&2, Ops.Item, rest, q), 1n+at, 1n+nat, so, sn), Done{Main.Skipped{rest, q}},
        skip_ok(rest, q, 1n+at, 1n+nat, so, sn, Equal.trans(Nat, Nat.add(List.length(&2, Ops.Item, rest), 1n+at), 1n+Nat.add(List.length(&2, Ops.Item, rest), at), so, Pos.add_succ(List.length(&2, Ops.Item, rest), at), eo), Equal.trans(Nat, Nat.add(List.length(&2, Ops.Item, rest), 1n+nat), 1n+Nat.add(List.length(&2, Ops.Item, rest), nat), sn, Pos.add_succ(List.length(&2, Ops.Item, rest), nat), en)))
        : {Main.patch.here(Nat.is_eq(so, at), Nat.is_eq(sn, nat), x, List.append(&2, Ops.Item, rest, q), _) == Done{Main.Skipped{x <> rest, q}} : Result<&2, &2, String, Main.Skipped>}
      %Equal.sym(Bool, Nat.is_eq(so, at), False{},
        Equal.trans(Bool, Nat.is_eq(so, at), Nat.is_eq(1n+Nat.add(List.length(&2, Ops.Item, rest), at), at), False{},
          Equal.cong(Nat, Bool, z => Nat.is_eq(z, at), so, 1n+Nat.add(List.length(&2, Ops.Item, rest), at), Equal.sym(Nat, 1n+Nat.add(List.length(&2, Ops.Item, rest), at), so, eo)),
          succ_ne(List.length(&2, Ops.Item, rest), at)))
        : {Main.patch.here(_, Nat.is_eq(sn, nat), x, List.append(&2, Ops.Item, rest, q), Done{Main.Skipped{rest, q}}) == Done{Main.Skipped{x <> rest, q}} : Result<&2, &2, String, Main.Skipped>}
      {==}

# A hunk begins where its first line is: a side holding none of its lines
# names the line before, which is the start of the file.
def from_nz(+c: Nat, +x: Nat, ez: {Nat.is_eq(c, 0n) == False{} : Bool}) -> {Main.patch.from(Main.hunk.side(c, x), c) == x : Nat}:
  %Equal.sym(Bool, Nat.is_eq(c, 0n), False{}, ez) : {Bool.pick(Nat, _, 1n+Bool.pick(Nat, _, 0n, x), Bool.pick(Nat, _, 0n, x)) == x : Nat}
  {==}

def from_one(+c: Nat, +x: Nat, z: Bool, ez: {Nat.is_eq(c, 0n) == z : Bool}, e1: {x == 1n : Nat}) -> {Main.patch.from(Main.hunk.side(c, x), c) == x : Nat}:
  match z:
    case False{}:
      from_nz(c, x, ez)
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(c, 0n), True{}, ez) : {Bool.pick(Nat, _, 1n+Bool.pick(Nat, _, 0n, x), Bool.pick(Nat, _, 0n, x)) == x : Nat}
      Equal.sym(Nat, x, 1n, e1)

# A hunk opening on a context line holds a line on each side.
def space_count(+s: String, -it: Ops.Item, -bk: Nat, -ak: Nat, -rest: List<&2, Main.Numbered>, +m: String, e: {String.eq(s, " ") == True{} : Bool}, ne: {String.eq(" ", m) == False{} : Bool}) -> {Nat.is_eq(Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, m), 0n) == False{} : Bool}:
  %Equal.sym(String, s, " ", S.eq_true(s, " ", e)) : {Nat.is_eq(Main.hunk.count(Main.Numbered{Main.Laid{_, it}, bk, ak} <> rest, m), 0n) == False{} : Bool}
  %Equal.sym(Bool, String.eq(" ", m), False{}, ne) : {Nat.is_eq(Nat.add(Bool.pick(Nat, _, 0n, 1n), Main.hunk.count(rest, m)), 0n) == False{} : Bool}
  {==}

def add0_eq(+c: Nat) -> {Nat.is_eq(Nat.add(c, 0n), c) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(c, 0n), c, Comp.add_zero(c)) : {Nat.is_eq(_, c) == True{} : Bool}
  nat_refl(c)

def from_old(b1: Bool, +s: String, +it: Ops.Item, +bk: Nat, +ak: Nat, +rest: List<&2, Main.Numbered>, eb1: {String.eq(s, " ") == b1 : Bool}, hf: {Bool.or(b1, Bool.and(Nat.is_eq(bk, 1n), Nat.is_eq(ak, 1n))) == True{} : Bool}) -> {Main.patch.from(Main.hunk.side(Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+"), bk), Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+")) == bk : Nat}:
  match b1:
    case True{}:
      from_nz(Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+"), bk, space_count(s, it, bk, ak, rest, "+", eb1, {==}))
    case False{}:
      from_one(Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+"), bk, Nat.is_eq(Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+"), 0n), {==}, ML.nat_eq(bk, 1n, Comp.and_left(Nat.is_eq(bk, 1n), Nat.is_eq(ak, 1n), hf)))

def from_new(b1: Bool, +s: String, +it: Ops.Item, +bk: Nat, +ak: Nat, +rest: List<&2, Main.Numbered>, eb1: {String.eq(s, " ") == b1 : Bool}, hf: {Bool.or(b1, Bool.and(Nat.is_eq(bk, 1n), Nat.is_eq(ak, 1n))) == True{} : Bool}) -> {Main.patch.from(Main.hunk.side(Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"), ak), Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-")) == ak : Nat}:
  match b1:
    case True{}:
      from_nz(Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"), ak, space_count(s, it, bk, ak, rest, "-", eb1, {==}))
    case False{}:
      from_one(Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"), ak, Nat.is_eq(Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"), 0n), {==}, ML.nat_eq(ak, 1n, Comp.and_right(Nat.is_eq(bk, 1n), Nat.is_eq(ak, 1n), hf)))

# One hunk read: found where its header says after the parent's lines
# before it, its lines read off the parent, its counts right; the parent
# left is what follows it, and the next lines are numbered on.
def hunk_step(+s: String, +it: Ops.Item, +bk: Nat, +ak: Nat, +rest: List<&2, Main.Numbered>, +g: List<&2, Ops.Item>, +p: List<&2, Ops.Item>, +w: List<&2, Ops.Item>, +at: Nat, +nat: Nat, +hs: {nsigns(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest) == True{} : Bool}, +eb: {Nat.add(List.length(&2, Ops.Item, g), at) == bk : Nat}, +ea: {Nat.add(List.length(&2, Ops.Item, g), nat) == ak : Nat}, +hf: {Bool.or(String.eq(s, " "), Bool.and(Nat.is_eq(bk, 1n), Nat.is_eq(ak, 1n))) == True{} : Bool}) -> {Main.patch.step(Main.hunk.of(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest), Main.Patching{List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lold(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest), p)), w, at, nat}) == Done{Main.Patching{p, List.append(&2, Ops.Item, List.append(&2, Ops.Item, w, g), lnew(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest)), Nat.add(bk, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+")), Nat.add(ak, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"))}} : Result<&2, &2, String, Main.Patching>}:
  %Equal.sym(Nat, Main.patch.from(Main.hunk.side(Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+"), bk), Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+")), bk, from_old(String.eq(s, " "), s, it, bk, ak, rest, {==}, hf)) : {Main.patch.hunk(Main.patch.skip(List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lold(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest), p)), at, nat, _, Main.patch.from(Main.hunk.side(Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"), ak), Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"))), Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, w, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+"), Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"), _, Main.patch.from(Main.hunk.side(Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"), ak), Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"))) == Done{Main.Patching{p, List.append(&2, Ops.Item, List.append(&2, Ops.Item, w, g), lnew(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest)), Nat.add(bk, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+")), Nat.add(ak, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"))}} : Result<&2, &2, String, Main.Patching>}
  %Equal.sym(Nat, Main.patch.from(Main.hunk.side(Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"), ak), Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-")), ak, from_new(String.eq(s, " "), s, it, bk, ak, rest, {==}, hf)) : {Main.patch.hunk(Main.patch.skip(List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lold(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest), p)), at, nat, bk, _), Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, w, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+"), Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"), bk, _) == Done{Main.Patching{p, List.append(&2, Ops.Item, List.append(&2, Ops.Item, w, g), lnew(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest)), Nat.add(bk, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+")), Nat.add(ak, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"))}} : Result<&2, &2, String, Main.Patching>}
  %Equal.sym(Result<&2, &2, String, Main.Skipped>, Main.patch.skip(List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lold(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest), p)), at, nat, bk, ak), Done{Main.Skipped{g, List.append(&2, Ops.Item, lold(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest), p)}}, skip_ok(g, List.append(&2, Ops.Item, lold(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest), p), at, nat, bk, ak, eb, ea)) : {Main.patch.hunk(_, Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, w, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+"), Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"), bk, ak) == Done{Main.Patching{p, List.append(&2, Ops.Item, List.append(&2, Ops.Item, w, g), lnew(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest)), Nat.add(bk, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+")), Nat.add(ak, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"))}} : Result<&2, &2, String, Main.Patching>}
  %Equal.sym(Result<&2, &2, String, Main.Patched>, Main.patch.lines(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, Done{Main.Patched{List.append(&2, Ops.Item, lold(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest), p), Nil{}, 0n, 0n}}), Done{Main.Patched{p, List.append(&2, Ops.Item, Nil{}, lnew(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest)), Nat.add(Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+"), 0n), Nat.add(Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"), 0n)}}, lines_ok(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, p, Nil{}, 0n, 0n, hs)) : {Main.patch.done(_, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+"), Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"), List.append(&2, Ops.Item, w, g), Nat.add(bk, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+")), Nat.add(ak, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"))) == Done{Main.Patching{p, List.append(&2, Ops.Item, List.append(&2, Ops.Item, w, g), lnew(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest)), Nat.add(bk, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+")), Nat.add(ak, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"))}} : Result<&2, &2, String, Main.Patching>}
  %Equal.sym(Bool, Nat.is_eq(Nat.add(Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+"), 0n), Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+")), True{}, add0_eq(Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+"))) : {Main.patch.check(Bool.and(_, Nat.is_eq(Nat.add(Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"), 0n), Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"))), Main.Patching{p, List.append(&2, Ops.Item, List.append(&2, Ops.Item, w, g), lnew(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest)), Nat.add(bk, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+")), Nat.add(ak, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"))}) == Done{Main.Patching{p, List.append(&2, Ops.Item, List.append(&2, Ops.Item, w, g), lnew(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest)), Nat.add(bk, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+")), Nat.add(ak, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"))}} : Result<&2, &2, String, Main.Patching>}
  %Equal.sym(Bool, Nat.is_eq(Nat.add(Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"), 0n), Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-")), True{}, add0_eq(Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"))) : {Main.patch.check(Bool.and(True{}, _), Main.Patching{p, List.append(&2, Ops.Item, List.append(&2, Ops.Item, w, g), lnew(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest)), Nat.add(bk, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+")), Nat.add(ak, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"))}) == Done{Main.Patching{p, List.append(&2, Ops.Item, List.append(&2, Ops.Item, w, g), lnew(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest)), Nat.add(bk, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "+")), Nat.add(ak, Main.hunk.count(Main.Numbered{Main.Laid{s, it}, bk, ak} <> rest, "-"))}} : Result<&2, &2, String, Main.Patching>}
  {==}

# Lists of numbered lines
# -----------------------

def nlapp_assoc(xs: List<&2, Main.Numbered>, -ys: List<&2, Main.Numbered>, -zs: List<&2, Main.Numbered>) -> {List.append(&2, Main.Numbered, List.append(&2, Main.Numbered, xs, ys), zs) == List.append(&2, Main.Numbered, xs, List.append(&2, Main.Numbered, ys, zs)) : List<&2, Main.Numbered>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Equal.cong(List<&2, Main.Numbered>, List<&2, Main.Numbered>, l => x <> l, List.append(&2, Main.Numbered, List.append(&2, Main.Numbered, rest, ys), zs), List.append(&2, Main.Numbered, rest, List.append(&2, Main.Numbered, ys, zs)), nlapp_assoc(rest, ys, zs))

def assoc3(+w: List<&2, Ops.Item>, +g: List<&2, Ops.Item>, +x: List<&2, Ops.Item>, +y: List<&2, Ops.Item>) -> {List.append(&2, Ops.Item, List.append(&2, Ops.Item, List.append(&2, Ops.Item, w, g), x), y) == List.append(&2, Ops.Item, w, List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, x, y))) : List<&2, Ops.Item>}:
  Equal.trans(List<&2, Ops.Item>, List.append(&2, Ops.Item, List.append(&2, Ops.Item, List.append(&2, Ops.Item, w, g), x), y), List.append(&2, Ops.Item, List.append(&2, Ops.Item, w, g), List.append(&2, Ops.Item, x, y)), List.append(&2, Ops.Item, w, List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, x, y))),
    LaidL.app_assoc(List.append(&2, Ops.Item, w, g), x, y), LaidL.app_assoc(w, g, List.append(&2, Ops.Item, x, y)))

def len_snoc(g: List<&2, Ops.Item>, -it: Ops.Item) -> {List.length(&2, Ops.Item, List.append(&2, Ops.Item, g, [it])) == 1n+List.length(&2, Ops.Item, g) : Nat}:
  match g:
    case Nil{}:
      {==}
    case x <> rest:
      Equal.cong(Nat, Nat, v => 1n+v, List.length(&2, Ops.Item, List.append(&2, Ops.Item, rest, [it])), 1n+List.length(&2, Ops.Item, rest), len_snoc(rest, it))

def not_false(x: Bool, e: {Bool.not(x) == False{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, S.true_false(e))

def or_true_r(x: Bool) -> {Bool.or(x, True{}) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# Each side of a hunk grown by a line.
def old_snoc(ks: List<&2, Main.Numbered>, +s: String, +it: Ops.Item, -b: Nat, -a: Nat, +r: List<&2, Ops.Item>) -> {List.append(&2, Ops.Item, lold(List.append(&2, Main.Numbered, ks, [Main.Numbered{Main.Laid{s, it}, b, a}])), r) == List.append(&2, Ops.Item, lold(ks), Main.laid.side(String.eq(s, "+"), it, r)) : List<&2, Ops.Item>}:
  match ks:
    case Nil{}:
      Equal.sym(List<&2, Ops.Item>, Main.laid.side(String.eq(s, "+"), it, r), List.append(&2, Ops.Item, Main.laid.side(String.eq(s, "+"), it, Nil{}), r), LaidL.side_app(String.eq(s, "+"), it, Nil{}, r))
    case Main.Numbered{Main.Laid{+s2, +it2}, b2, a2} <> rest:
      Equal.trans(List<&2, Ops.Item>, List.append(&2, Ops.Item, Main.laid.side(String.eq(s2, "+"), it2, lold(List.append(&2, Main.Numbered, rest, [Main.Numbered{Main.Laid{s, it}, b, a}]))), r), Main.laid.side(String.eq(s2, "+"), it2, List.append(&2, Ops.Item, lold(List.append(&2, Main.Numbered, rest, [Main.Numbered{Main.Laid{s, it}, b, a}])), r)), List.append(&2, Ops.Item, Main.laid.side(String.eq(s2, "+"), it2, lold(rest)), Main.laid.side(String.eq(s, "+"), it, r)),
        Equal.sym(List<&2, Ops.Item>, Main.laid.side(String.eq(s2, "+"), it2, List.append(&2, Ops.Item, lold(List.append(&2, Main.Numbered, rest, [Main.Numbered{Main.Laid{s, it}, b, a}])), r)), List.append(&2, Ops.Item, Main.laid.side(String.eq(s2, "+"), it2, lold(List.append(&2, Main.Numbered, rest, [Main.Numbered{Main.Laid{s, it}, b, a}]))), r), LaidL.side_app(String.eq(s2, "+"), it2, lold(List.append(&2, Main.Numbered, rest, [Main.Numbered{Main.Laid{s, it}, b, a}])), r)),
        Equal.trans(List<&2, Ops.Item>, Main.laid.side(String.eq(s2, "+"), it2, List.append(&2, Ops.Item, lold(List.append(&2, Main.Numbered, rest, [Main.Numbered{Main.Laid{s, it}, b, a}])), r)), Main.laid.side(String.eq(s2, "+"), it2, List.append(&2, Ops.Item, lold(rest), Main.laid.side(String.eq(s, "+"), it, r))), List.append(&2, Ops.Item, Main.laid.side(String.eq(s2, "+"), it2, lold(rest)), Main.laid.side(String.eq(s, "+"), it, r)),
          Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => Main.laid.side(String.eq(s2, "+"), it2, l), List.append(&2, Ops.Item, lold(List.append(&2, Main.Numbered, rest, [Main.Numbered{Main.Laid{s, it}, b, a}])), r), List.append(&2, Ops.Item, lold(rest), Main.laid.side(String.eq(s, "+"), it, r)), old_snoc(rest, s, it, b, a, r)),
          LaidL.side_app(String.eq(s2, "+"), it2, lold(rest), Main.laid.side(String.eq(s, "+"), it, r))))

def new_snoc(ks: List<&2, Main.Numbered>, +s: String, +it: Ops.Item, -b: Nat, -a: Nat, +r: List<&2, Ops.Item>) -> {List.append(&2, Ops.Item, lnew(List.append(&2, Main.Numbered, ks, [Main.Numbered{Main.Laid{s, it}, b, a}])), r) == List.append(&2, Ops.Item, lnew(ks), Main.laid.side(String.eq(s, "-"), it, r)) : List<&2, Ops.Item>}:
  match ks:
    case Nil{}:
      Equal.sym(List<&2, Ops.Item>, Main.laid.side(String.eq(s, "-"), it, r), List.append(&2, Ops.Item, Main.laid.side(String.eq(s, "-"), it, Nil{}), r), LaidL.side_app(String.eq(s, "-"), it, Nil{}, r))
    case Main.Numbered{Main.Laid{+s2, +it2}, b2, a2} <> rest:
      Equal.trans(List<&2, Ops.Item>, List.append(&2, Ops.Item, Main.laid.side(String.eq(s2, "-"), it2, lnew(List.append(&2, Main.Numbered, rest, [Main.Numbered{Main.Laid{s, it}, b, a}]))), r), Main.laid.side(String.eq(s2, "-"), it2, List.append(&2, Ops.Item, lnew(List.append(&2, Main.Numbered, rest, [Main.Numbered{Main.Laid{s, it}, b, a}])), r)), List.append(&2, Ops.Item, Main.laid.side(String.eq(s2, "-"), it2, lnew(rest)), Main.laid.side(String.eq(s, "-"), it, r)),
        Equal.sym(List<&2, Ops.Item>, Main.laid.side(String.eq(s2, "-"), it2, List.append(&2, Ops.Item, lnew(List.append(&2, Main.Numbered, rest, [Main.Numbered{Main.Laid{s, it}, b, a}])), r)), List.append(&2, Ops.Item, Main.laid.side(String.eq(s2, "-"), it2, lnew(List.append(&2, Main.Numbered, rest, [Main.Numbered{Main.Laid{s, it}, b, a}]))), r), LaidL.side_app(String.eq(s2, "-"), it2, lnew(List.append(&2, Main.Numbered, rest, [Main.Numbered{Main.Laid{s, it}, b, a}])), r)),
        Equal.trans(List<&2, Ops.Item>, Main.laid.side(String.eq(s2, "-"), it2, List.append(&2, Ops.Item, lnew(List.append(&2, Main.Numbered, rest, [Main.Numbered{Main.Laid{s, it}, b, a}])), r)), Main.laid.side(String.eq(s2, "-"), it2, List.append(&2, Ops.Item, lnew(rest), Main.laid.side(String.eq(s, "-"), it, r))), List.append(&2, Ops.Item, Main.laid.side(String.eq(s2, "-"), it2, lnew(rest)), Main.laid.side(String.eq(s, "-"), it, r)),
          Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => Main.laid.side(String.eq(s2, "-"), it2, l), List.append(&2, Ops.Item, lnew(List.append(&2, Main.Numbered, rest, [Main.Numbered{Main.Laid{s, it}, b, a}])), r), List.append(&2, Ops.Item, lnew(rest), Main.laid.side(String.eq(s, "-"), it, r)), new_snoc(rest, s, it, b, a, r)),
          LaidL.side_app(String.eq(s2, "-"), it2, lnew(rest), Main.laid.side(String.eq(s, "-"), it, r))))

def count_snoc(ks: List<&2, Main.Numbered>, +s: String, -it: Ops.Item, -b: Nat, -a: Nat, +m: String) -> {Main.hunk.count(List.append(&2, Main.Numbered, ks, [Main.Numbered{Main.Laid{s, it}, b, a}]), m) == Nat.add(Main.hunk.count(ks, m), Bool.pick(Nat, String.eq(s, m), 0n, 1n)) : Nat}:
  match ks:
    case Nil{}:
      Comp.add_zero(Bool.pick(Nat, String.eq(s, m), 0n, 1n))
    case Main.Numbered{Main.Laid{+s2, it2}, b2, a2} <> rest:
      Equal.trans(Nat, Nat.add(Bool.pick(Nat, String.eq(s2, m), 0n, 1n), Main.hunk.count(List.append(&2, Main.Numbered, rest, [Main.Numbered{Main.Laid{s, it}, b, a}]), m)), Nat.add(Bool.pick(Nat, String.eq(s2, m), 0n, 1n), Nat.add(Main.hunk.count(rest, m), Bool.pick(Nat, String.eq(s, m), 0n, 1n))), Nat.add(Nat.add(Bool.pick(Nat, String.eq(s2, m), 0n, 1n), Main.hunk.count(rest, m)), Bool.pick(Nat, String.eq(s, m), 0n, 1n)),
        Equal.cong(Nat, Nat, v => Nat.add(Bool.pick(Nat, String.eq(s2, m), 0n, 1n), v), Main.hunk.count(List.append(&2, Main.Numbered, rest, [Main.Numbered{Main.Laid{s, it}, b, a}]), m), Nat.add(Main.hunk.count(rest, m), Bool.pick(Nat, String.eq(s, m), 0n, 1n)), count_snoc(rest, s, it, b, a, m)),
        Equal.sym(Nat, Nat.add(Nat.add(Bool.pick(Nat, String.eq(s2, m), 0n, 1n), Main.hunk.count(rest, m)), Bool.pick(Nat, String.eq(s, m), 0n, 1n)), Nat.add(Bool.pick(Nat, String.eq(s2, m), 0n, 1n), Nat.add(Main.hunk.count(rest, m), Bool.pick(Nat, String.eq(s, m), 0n, 1n))), Pos.add_assoc(Bool.pick(Nat, String.eq(s2, m), 0n, 1n), Main.hunk.count(rest, m), Bool.pick(Nat, String.eq(s, m), 0n, 1n))))

def nsigns_snoc(ks: List<&2, Main.Numbered>, +s: String, -it: Ops.Item, -b: Nat, -a: Nat, +hk: {nsigns(ks) == True{} : Bool}, hs: {sign_ok(s) == True{} : Bool}) -> {nsigns(List.append(&2, Main.Numbered, ks, [Main.Numbered{Main.Laid{s, it}, b, a}])) == True{} : Bool}:
  match ks:
    case Nil{}:
      ML.and_intro(sign_ok(s), True{}, hs, {==})
    case Main.Numbered{Main.Laid{+s2, it2}, b2, a2} <> +rest:
      ML.and_intro(sign_ok(s2), nsigns(List.append(&2, Main.Numbered, rest, [Main.Numbered{Main.Laid{s, it}, b, a}])), Comp.and_left(sign_ok(s2), nsigns(rest), hk), nsigns_snoc(rest, s, it, b, a, Comp.and_right(sign_ok(s2), nsigns(rest), hk), hs))

# A line's number on a side is the one before it, or one more.
def num_next(z: Bool, +b: Nat, +x: Nat, +c: Nat, h: {b == Nat.add(x, c) : Nat}) -> {Bool.pick(Nat, z, b, 1n+b) == Nat.add(x, Nat.add(c, Bool.pick(Nat, z, 0n, 1n))) : Nat}:
  match z:
    case True{}:
      %Equal.sym(Nat, Nat.add(c, 0n), c, Comp.add_zero(c)) : {b == Nat.add(x, _) : Nat}
      h
    case False{}:
      %Equal.sym(Nat, Nat.add(c, 1n), 1n+Nat.add(c, 0n), Pos.add_succ(c, 0n)) : {1n+b == Nat.add(x, _) : Nat}
      %Equal.sym(Nat, Nat.add(c, 0n), c, Comp.add_zero(c)) : {1n+b == Nat.add(x, 1n+_) : Nat}
      %Equal.sym(Nat, Nat.add(x, 1n+c), 1n+Nat.add(x, c), Pos.add_succ(x, c)) : {1n+b == _ : Nat}
      Equal.cong(Nat, Nat, v => 1n+v, b, Nat.add(x, c), h)

# The walk
# --------

# The hunks the rest of the walk closes, the lines `ks` already shown
# before it.
def cut_with(ks: List<&2, Main.Numbered>, c: Main.Cut) -> List<&2, Main.Hunk>:
  match c:
    case Main.Cut{ls, hs}:
      Main.hunks.close(List.append(&2, Main.Numbered, ks, ls), hs)

def with_nil(c: Main.Cut) -> {cut_with(Nil{}, c) == Main.cut.close(c) : List<&2, Main.Hunk>}:
  match c:
    case Main.Cut{ls, hs}:
      {==}

def step_true(+ks: List<&2, Main.Numbered>, +n: Main.Numbered, c: Main.Cut) -> {cut_with(ks, Main.cut.step(n, True{}, c)) == cut_with(List.append(&2, Main.Numbered, ks, [n]), c) : List<&2, Main.Hunk>}:
  match c:
    case Main.Cut{+ls, hs}:
      Equal.cong(List<&2, Main.Numbered>, List<&2, Main.Hunk>, l => Main.hunks.close(l, hs), List.append(&2, Main.Numbered, ks, n <> ls), List.append(&2, Main.Numbered, List.append(&2, Main.Numbered, ks, [n]), ls), Equal.sym(List<&2, Main.Numbered>, List.append(&2, Main.Numbered, List.append(&2, Main.Numbered, ks, [n]), ls), List.append(&2, Main.Numbered, ks, n <> ls), nlapp_assoc(ks, [n], ls)))

def step_false(-ks: List<&2, Main.Numbered>, -n: Main.Numbered, c: Main.Cut) -> {cut_with(ks, Main.cut.step(n, False{}, c)) == Main.hunks.close(List.append(&2, Main.Numbered, ks, Nil{}), cut_with(Nil{}, c)) : List<&2, Main.Hunk>}:
  match c:
    case Main.Cut{ls, hs}:
      {==}

# Where a hunk may open: on a context line, or at the top of both sides.
def fresh(ls: List<&2, Main.Laid>, +b: Nat, +a: Nat) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Main.Laid{s, it} <> rest:
      Bool.or(String.eq(s, " "), Bool.and(Nat.is_eq(b, 1n), Nat.is_eq(a, 1n)))

# The open hunk's first line is where the reading stands, `x` and `y`, and
# opens as a hunk may; with none open, the next line opens as one may.
def start_ok(ks: List<&2, Main.Numbered>, ls: List<&2, Main.Laid>, +b: Nat, +a: Nat, +x: Nat, +y: Nat) -> Bool:
  match ks:
    case Nil{}:
      fresh(ls, b, a)
    case Main.Numbered{Main.Laid{sk, itk}, +bk, +ak} <> kr:
      Bool.and(Nat.is_eq(x, bk), Bool.and(Nat.is_eq(y, ak), Bool.or(String.eq(sk, " "), Bool.and(Nat.is_eq(bk, 1n), Nat.is_eq(ak, 1n)))))

def fresh_one(ls: List<&2, Main.Laid>) -> {fresh(ls, 1n, 1n) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Main.Laid{s, it} <> rest:
      or_true_r(String.eq(s, " "))

# A line no change is near is a context line.
def near_fresh(ls: List<&2, Main.Laid>, +b: Nat, +a: Nat, e: {Main.changed.near(ls, 3n) == False{} : Bool}) -> {fresh(ls, b, a) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Main.Laid{+s, it} <> rest:
      %Equal.sym(Bool, String.eq(s, " "), True{}, not_false(String.eq(s, " "), ML.or_false_left(Main.laid.changed(s), Main.changed.near(rest, 2n), e))) : {Bool.or(_, Bool.and(Nat.is_eq(b, 1n), Nat.is_eq(a, 1n))) == True{} : Bool}
      {==}

def start_snoc(ks: List<&2, Main.Numbered>, +s: String, +it: Ops.Item, -rest: List<&2, Main.Laid>, +b: Nat, +a: Nat, +x: Nat, +y: Nat, h1: {b == Nat.add(x, Main.hunk.count(ks, "+")) : Nat}, h2: {a == Nat.add(y, Main.hunk.count(ks, "-")) : Nat}, h3: {start_ok(ks, Main.Laid{s, it} <> rest, b, a, x, y) == True{} : Bool}) -> {start_ok(List.append(&2, Main.Numbered, ks, [Main.Numbered{Main.Laid{s, it}, b, a}]), rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), x, y) == True{} : Bool}:
  match ks:
    case Nil{}:
      ML.and_intro(Nat.is_eq(x, b), Bool.and(Nat.is_eq(y, a), Bool.or(String.eq(s, " "), Bool.and(Nat.is_eq(b, 1n), Nat.is_eq(a, 1n)))),
        Equal.trans(Bool, Nat.is_eq(x, b), Nat.is_eq(x, x), True{}, Equal.cong(Nat, Bool, v => Nat.is_eq(x, v), b, x, Equal.trans(Nat, b, Nat.add(x, 0n), x, h1, Comp.add_zero(x))), nat_refl(x)),
        ML.and_intro(Nat.is_eq(y, a), Bool.or(String.eq(s, " "), Bool.and(Nat.is_eq(b, 1n), Nat.is_eq(a, 1n))),
          Equal.trans(Bool, Nat.is_eq(y, a), Nat.is_eq(y, y), True{}, Equal.cong(Nat, Bool, v => Nat.is_eq(y, v), a, y, Equal.trans(Nat, a, Nat.add(y, 0n), y, h2, Comp.add_zero(y))), nat_refl(y)),
          h3))
    case Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr:
      h3

# Closing a hunk: it is read, and the hunks after it are read from where it
# leaves the parent.
def close_ok(+sk: String, +itk: Ops.Item, +bk: Nat, +ak: Nat, +kr: List<&2, Main.Numbered>, +g: List<&2, Ops.Item>, +p: List<&2, Ops.Item>, +q: List<&2, Ops.Item>, +w: List<&2, Ops.Item>, +at: Nat, +nat: Nat, xs: List<&2, Main.Hunk>, +hk: {nsigns(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr) == True{} : Bool}, +h3: {Bool.and(Nat.is_eq(Nat.add(List.length(&2, Ops.Item, g), at), bk), Bool.and(Nat.is_eq(Nat.add(List.length(&2, Ops.Item, g), nat), ak), Bool.or(String.eq(sk, " "), Bool.and(Nat.is_eq(bk, 1n), Nat.is_eq(ak, 1n))))) == True{} : Bool}, e: {Main.patch.go(xs, Done{Main.Patching{p, List.append(&2, Ops.Item, List.append(&2, Ops.Item, w, g), lnew(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr)), Nat.add(bk, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "+")), Nat.add(ak, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "-"))}}) == Done{List.append(&2, Ops.Item, List.append(&2, Ops.Item, List.append(&2, Ops.Item, w, g), lnew(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr)), q)} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Main.patch.go(Main.hunk.of(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr) <> xs, Done{Main.Patching{List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lold(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr), p)), w, at, nat}}) == Done{List.append(&2, Ops.Item, w, List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lnew(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr), q)))} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  %Equal.sym(Result<&2, &2, String, Main.Patching>, Main.patch.step(Main.hunk.of(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr), Main.Patching{List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lold(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr), p)), w, at, nat}), Done{Main.Patching{p, List.append(&2, Ops.Item, List.append(&2, Ops.Item, w, g), lnew(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr)), Nat.add(bk, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "+")), Nat.add(ak, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "-"))}}, hunk_step(sk, itk, bk, ak, kr, g, p, w, at, nat, hk, ML.nat_eq(Nat.add(List.length(&2, Ops.Item, g), at), bk, Comp.and_left(Nat.is_eq(Nat.add(List.length(&2, Ops.Item, g), at), bk), Bool.and(Nat.is_eq(Nat.add(List.length(&2, Ops.Item, g), nat), ak), Bool.or(String.eq(sk, " "), Bool.and(Nat.is_eq(bk, 1n), Nat.is_eq(ak, 1n)))), h3)), ML.nat_eq(Nat.add(List.length(&2, Ops.Item, g), nat), ak, Comp.and_left(Nat.is_eq(Nat.add(List.length(&2, Ops.Item, g), nat), ak), Bool.or(String.eq(sk, " "), Bool.and(Nat.is_eq(bk, 1n), Nat.is_eq(ak, 1n))), Comp.and_right(Nat.is_eq(Nat.add(List.length(&2, Ops.Item, g), at), bk), Bool.and(Nat.is_eq(Nat.add(List.length(&2, Ops.Item, g), nat), ak), Bool.or(String.eq(sk, " "), Bool.and(Nat.is_eq(bk, 1n), Nat.is_eq(ak, 1n)))), h3))), Comp.and_right(Nat.is_eq(Nat.add(List.length(&2, Ops.Item, g), nat), ak), Bool.or(String.eq(sk, " "), Bool.and(Nat.is_eq(bk, 1n), Nat.is_eq(ak, 1n))), Comp.and_right(Nat.is_eq(Nat.add(List.length(&2, Ops.Item, g), at), bk), Bool.and(Nat.is_eq(Nat.add(List.length(&2, Ops.Item, g), nat), ak), Bool.or(String.eq(sk, " "), Bool.and(Nat.is_eq(bk, 1n), Nat.is_eq(ak, 1n)))), h3)))) : {Main.patch.go(xs, _) == Done{List.append(&2, Ops.Item, w, List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lnew(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr), q)))} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %assoc3(w, g, lnew(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr), q) : {Main.patch.go(xs, Done{Main.Patching{p, List.append(&2, Ops.Item, List.append(&2, Ops.Item, w, g), lnew(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr)), Nat.add(bk, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "+")), Nat.add(ak, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "-"))}}) == Done{_} : Result<&2, &2, String, List<&2, Ops.Item>>}
  e

# One line of the walk: shown, it joins the open hunk; not shown, it is a
# context line, and closes the hunk open before it.
def walk_cons(sh: Bool, +s: String, +it: Ops.Item, +rest: List<&2, Main.Laid>, +b: Nat, +a: Nat, +owed: Nat, +ks: List<&2, Main.Numbered>, +g: List<&2, Ops.Item>, +w: List<&2, Ops.Item>, +at: Nat, +nat: Nat, +esh: {Main.hunks.showing(Main.laid.changed(s), owed, Main.changed.near(rest, 3n)) == sh : Bool}, hsg: {sign_ok(s) == True{} : Bool}, +hk: {nsigns(ks) == True{} : Bool}, +h1: {b == Nat.add(Nat.add(List.length(&2, Ops.Item, g), at), Main.hunk.count(ks, "+")) : Nat}, +h2: {a == Nat.add(Nat.add(List.length(&2, Ops.Item, g), nat), Main.hunk.count(ks, "-")) : Nat}, +h3: {start_ok(ks, Main.Laid{s, it} <> rest, b, a, Nat.add(List.length(&2, Ops.Item, g), at), Nat.add(List.length(&2, Ops.Item, g), nat)) == True{} : Bool}, ih: @ks2: List<&2, Main.Numbered> -> @g2: List<&2, Ops.Item> -> @w2: List<&2, Ops.Item> -> @at2: Nat -> @nat2: Nat -> {nsigns(ks2) == True{} : Bool} -> {Bool.pick(Nat, String.eq(s, "+"), b, 1n+b) == Nat.add(Nat.add(List.length(&2, Ops.Item, g2), at2), Main.hunk.count(ks2, "+")) : Nat} -> {Bool.pick(Nat, String.eq(s, "-"), a, 1n+a) == Nat.add(Nat.add(List.length(&2, Ops.Item, g2), nat2), Main.hunk.count(ks2, "-")) : Nat} -> {start_ok(ks2, rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Nat.add(List.length(&2, Ops.Item, g2), at2), Nat.add(List.length(&2, Ops.Item, g2), nat2)) == True{} : Bool} -> {Main.patch.go(cut_with(ks2, Main.hunks.walk(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Main.hunks.owed(Main.laid.changed(s), owed))), Done{Main.Patching{List.append(&2, Ops.Item, g2, List.append(&2, Ops.Item, lold(ks2), Main.laid.old(rest))), w2, at2, nat2}}) == Done{List.append(&2, Ops.Item, w2, List.append(&2, Ops.Item, g2, List.append(&2, Ops.Item, lnew(ks2), Main.laid.new(rest))))} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Main.patch.go(cut_with(ks, Main.cut.step(Main.Numbered{Main.Laid{s, it}, b, a}, sh, Main.hunks.walk(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Main.hunks.owed(Main.laid.changed(s), owed)))), Done{Main.Patching{List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lold(ks), Main.laid.side(String.eq(s, "+"), it, Main.laid.old(rest)))), w, at, nat}}) == Done{List.append(&2, Ops.Item, w, List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lnew(ks), Main.laid.side(String.eq(s, "-"), it, Main.laid.new(rest)))))} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match sh:
    case True{}:
      %Equal.sym(List<&2, Main.Hunk>, cut_with(ks, Main.cut.step(Main.Numbered{Main.Laid{s, it}, b, a}, True{}, Main.hunks.walk(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Main.hunks.owed(Main.laid.changed(s), owed)))), cut_with(List.append(&2, Main.Numbered, ks, [Main.Numbered{Main.Laid{s, it}, b, a}]), Main.hunks.walk(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Main.hunks.owed(Main.laid.changed(s), owed))), step_true(ks, Main.Numbered{Main.Laid{s, it}, b, a}, Main.hunks.walk(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Main.hunks.owed(Main.laid.changed(s), owed)))) : {Main.patch.go(_, Done{Main.Patching{List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lold(ks), Main.laid.side(String.eq(s, "+"), it, Main.laid.old(rest)))), w, at, nat}}) == Done{List.append(&2, Ops.Item, w, List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lnew(ks), Main.laid.side(String.eq(s, "-"), it, Main.laid.new(rest)))))} : Result<&2, &2, String, List<&2, Ops.Item>>}
      %old_snoc(ks, s, it, b, a, Main.laid.old(rest)) : {Main.patch.go(cut_with(List.append(&2, Main.Numbered, ks, [Main.Numbered{Main.Laid{s, it}, b, a}]), Main.hunks.walk(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Main.hunks.owed(Main.laid.changed(s), owed))), Done{Main.Patching{List.append(&2, Ops.Item, g, _), w, at, nat}}) == Done{List.append(&2, Ops.Item, w, List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lnew(ks), Main.laid.side(String.eq(s, "-"), it, Main.laid.new(rest)))))} : Result<&2, &2, String, List<&2, Ops.Item>>}
      %new_snoc(ks, s, it, b, a, Main.laid.new(rest)) : {Main.patch.go(cut_with(List.append(&2, Main.Numbered, ks, [Main.Numbered{Main.Laid{s, it}, b, a}]), Main.hunks.walk(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Main.hunks.owed(Main.laid.changed(s), owed))), Done{Main.Patching{List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lold(List.append(&2, Main.Numbered, ks, [Main.Numbered{Main.Laid{s, it}, b, a}])), Main.laid.old(rest))), w, at, nat}}) == Done{List.append(&2, Ops.Item, w, List.append(&2, Ops.Item, g, _))} : Result<&2, &2, String, List<&2, Ops.Item>>}
      ih(List.append(&2, Main.Numbered, ks, [Main.Numbered{Main.Laid{s, it}, b, a}]), g, w, at, nat, nsigns_snoc(ks, s, it, b, a, hk, hsg), Equal.trans(Nat, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Nat.add(Nat.add(List.length(&2, Ops.Item, g), at), Nat.add(Main.hunk.count(ks, "+"), Bool.pick(Nat, String.eq(s, "+"), 0n, 1n))), Nat.add(Nat.add(List.length(&2, Ops.Item, g), at), Main.hunk.count(List.append(&2, Main.Numbered, ks, [Main.Numbered{Main.Laid{s, it}, b, a}]), "+")), num_next(String.eq(s, "+"), b, Nat.add(List.length(&2, Ops.Item, g), at), Main.hunk.count(ks, "+"), h1), Equal.cong(Nat, Nat, v => Nat.add(Nat.add(List.length(&2, Ops.Item, g), at), v), Nat.add(Main.hunk.count(ks, "+"), Bool.pick(Nat, String.eq(s, "+"), 0n, 1n)), Main.hunk.count(List.append(&2, Main.Numbered, ks, [Main.Numbered{Main.Laid{s, it}, b, a}]), "+"), Equal.sym(Nat, Main.hunk.count(List.append(&2, Main.Numbered, ks, [Main.Numbered{Main.Laid{s, it}, b, a}]), "+"), Nat.add(Main.hunk.count(ks, "+"), Bool.pick(Nat, String.eq(s, "+"), 0n, 1n)), count_snoc(ks, s, it, b, a, "+")))), Equal.trans(Nat, Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Nat.add(Nat.add(List.length(&2, Ops.Item, g), nat), Nat.add(Main.hunk.count(ks, "-"), Bool.pick(Nat, String.eq(s, "-"), 0n, 1n))), Nat.add(Nat.add(List.length(&2, Ops.Item, g), nat), Main.hunk.count(List.append(&2, Main.Numbered, ks, [Main.Numbered{Main.Laid{s, it}, b, a}]), "-")), num_next(String.eq(s, "-"), a, Nat.add(List.length(&2, Ops.Item, g), nat), Main.hunk.count(ks, "-"), h2), Equal.cong(Nat, Nat, v => Nat.add(Nat.add(List.length(&2, Ops.Item, g), nat), v), Nat.add(Main.hunk.count(ks, "-"), Bool.pick(Nat, String.eq(s, "-"), 0n, 1n)), Main.hunk.count(List.append(&2, Main.Numbered, ks, [Main.Numbered{Main.Laid{s, it}, b, a}]), "-"), Equal.sym(Nat, Main.hunk.count(List.append(&2, Main.Numbered, ks, [Main.Numbered{Main.Laid{s, it}, b, a}]), "-"), Nat.add(Main.hunk.count(ks, "-"), Bool.pick(Nat, String.eq(s, "-"), 0n, 1n)), count_snoc(ks, s, it, b, a, "-")))), start_snoc(ks, s, it, rest, b, a, Nat.add(List.length(&2, Ops.Item, g), at), Nat.add(List.length(&2, Ops.Item, g), nat), h1, h2, h3))
    case False{}:
      match ks:
        case Nil{}:
          %Equal.sym(List<&2, Main.Hunk>, cut_with(Nil{}, Main.cut.step(Main.Numbered{Main.Laid{s, it}, b, a}, False{}, Main.hunks.walk(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Main.hunks.owed(Main.laid.changed(s), owed)))), Main.hunks.close(List.append(&2, Main.Numbered, ks, Nil{}), cut_with(Nil{}, Main.hunks.walk(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Main.hunks.owed(Main.laid.changed(s), owed)))), step_false(Nil{}, Main.Numbered{Main.Laid{s, it}, b, a}, Main.hunks.walk(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Main.hunks.owed(Main.laid.changed(s), owed)))) : {Main.patch.go(_, Done{Main.Patching{List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lold(Nil{}), Main.laid.side(String.eq(s, "+"), it, Main.laid.old(rest)))), w, at, nat}}) == Done{List.append(&2, Ops.Item, w, List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lnew(Nil{}), Main.laid.side(String.eq(s, "-"), it, Main.laid.new(rest)))))} : Result<&2, &2, String, List<&2, Ops.Item>>}
          %Equal.sym(Bool, String.eq(s, "+"), False{}, Equal.cong(String, Bool, z => String.eq(z, "+"), s, " ", S.eq_true(s, " ", not_false(String.eq(s, " "), ML.or_false_left(Main.laid.changed(s), Bool.or(Nat.is_gt(owed, 0n), Main.changed.near(rest, 3n)), esh))))) : {Main.patch.go(Main.hunks.close(List.append(&2, Main.Numbered, ks, Nil{}), cut_with(Nil{}, Main.hunks.walk(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Main.hunks.owed(Main.laid.changed(s), owed)))), Done{Main.Patching{List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lold(Nil{}), Main.laid.side(_, it, Main.laid.old(rest)))), w, at, nat}}) == Done{List.append(&2, Ops.Item, w, List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lnew(Nil{}), Main.laid.side(String.eq(s, "-"), it, Main.laid.new(rest)))))} : Result<&2, &2, String, List<&2, Ops.Item>>}
          %Equal.sym(Bool, String.eq(s, "-"), False{}, Equal.cong(String, Bool, z => String.eq(z, "-"), s, " ", S.eq_true(s, " ", not_false(String.eq(s, " "), ML.or_false_left(Main.laid.changed(s), Bool.or(Nat.is_gt(owed, 0n), Main.changed.near(rest, 3n)), esh))))) : {Main.patch.go(Main.hunks.close(List.append(&2, Main.Numbered, ks, Nil{}), cut_with(Nil{}, Main.hunks.walk(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Main.hunks.owed(Main.laid.changed(s), owed)))), Done{Main.Patching{List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lold(Nil{}), it <> Main.laid.old(rest))), w, at, nat}}) == Done{List.append(&2, Ops.Item, w, List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lnew(Nil{}), Main.laid.side(_, it, Main.laid.new(rest)))))} : Result<&2, &2, String, List<&2, Ops.Item>>}
          %LaidL.app_assoc(g, [it], Main.laid.old(rest)) : {Main.patch.go(cut_with(Nil{}, Main.hunks.walk(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Main.hunks.owed(Main.laid.changed(s), owed))), Done{Main.Patching{_, w, at, nat}}) == Done{List.append(&2, Ops.Item, w, List.append(&2, Ops.Item, g, it <> Main.laid.new(rest)))} : Result<&2, &2, String, List<&2, Ops.Item>>}
          %LaidL.app_assoc(g, [it], Main.laid.new(rest)) : {Main.patch.go(cut_with(Nil{}, Main.hunks.walk(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Main.hunks.owed(Main.laid.changed(s), owed))), Done{Main.Patching{List.append(&2, Ops.Item, List.append(&2, Ops.Item, g, [it]), Main.laid.old(rest)), w, at, nat}}) == Done{List.append(&2, Ops.Item, w, _)} : Result<&2, &2, String, List<&2, Ops.Item>>}
          ih(Nil{}, List.append(&2, Ops.Item, g, [it]), w, at, nat, {==}, Equal.trans(Nat, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), 1n+b, Nat.add(Nat.add(List.length(&2, Ops.Item, List.append(&2, Ops.Item, g, [it])), at), 0n), Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, b, 1n+b), String.eq(s, "+"), False{}, Equal.cong(String, Bool, z => String.eq(z, "+"), s, " ", S.eq_true(s, " ", not_false(String.eq(s, " "), ML.or_false_left(Main.laid.changed(s), Bool.or(Nat.is_gt(owed, 0n), Main.changed.near(rest, 3n)), esh))))), Equal.trans(Nat, 1n+b, Nat.add(Nat.add(1n+List.length(&2, Ops.Item, g), at), 0n), Nat.add(Nat.add(List.length(&2, Ops.Item, List.append(&2, Ops.Item, g, [it])), at), 0n), Equal.cong(Nat, Nat, v => 1n+v, b, Nat.add(Nat.add(List.length(&2, Ops.Item, g), at), 0n), h1), Equal.cong(Nat, Nat, v => Nat.add(Nat.add(v, at), 0n), 1n+List.length(&2, Ops.Item, g), List.length(&2, Ops.Item, List.append(&2, Ops.Item, g, [it])), Equal.sym(Nat, List.length(&2, Ops.Item, List.append(&2, Ops.Item, g, [it])), 1n+List.length(&2, Ops.Item, g), len_snoc(g, it))))), Equal.trans(Nat, Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), 1n+a, Nat.add(Nat.add(List.length(&2, Ops.Item, List.append(&2, Ops.Item, g, [it])), nat), 0n), Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, a, 1n+a), String.eq(s, "-"), False{}, Equal.cong(String, Bool, z => String.eq(z, "-"), s, " ", S.eq_true(s, " ", not_false(String.eq(s, " "), ML.or_false_left(Main.laid.changed(s), Bool.or(Nat.is_gt(owed, 0n), Main.changed.near(rest, 3n)), esh))))), Equal.trans(Nat, 1n+a, Nat.add(Nat.add(1n+List.length(&2, Ops.Item, g), nat), 0n), Nat.add(Nat.add(List.length(&2, Ops.Item, List.append(&2, Ops.Item, g, [it])), nat), 0n), Equal.cong(Nat, Nat, v => 1n+v, a, Nat.add(Nat.add(List.length(&2, Ops.Item, g), nat), 0n), h2), Equal.cong(Nat, Nat, v => Nat.add(Nat.add(v, nat), 0n), 1n+List.length(&2, Ops.Item, g), List.length(&2, Ops.Item, List.append(&2, Ops.Item, g, [it])), Equal.sym(Nat, List.length(&2, Ops.Item, List.append(&2, Ops.Item, g, [it])), 1n+List.length(&2, Ops.Item, g), len_snoc(g, it))))), near_fresh(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), ML.or_false_right(Nat.is_gt(owed, 0n), Main.changed.near(rest, 3n), ML.or_false_right(Main.laid.changed(s), Bool.or(Nat.is_gt(owed, 0n), Main.changed.near(rest, 3n)), esh))))
        case Main.Numbered{Main.Laid{+sk, +itk}, +bk, +ak} <> +kr:
          %Equal.sym(List<&2, Main.Hunk>, cut_with(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, Main.cut.step(Main.Numbered{Main.Laid{s, it}, b, a}, False{}, Main.hunks.walk(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Main.hunks.owed(Main.laid.changed(s), owed)))), Main.hunks.close(List.append(&2, Main.Numbered, ks, Nil{}), cut_with(Nil{}, Main.hunks.walk(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Main.hunks.owed(Main.laid.changed(s), owed)))), step_false(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, Main.Numbered{Main.Laid{s, it}, b, a}, Main.hunks.walk(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Main.hunks.owed(Main.laid.changed(s), owed)))) : {Main.patch.go(_, Done{Main.Patching{List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lold(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr), Main.laid.side(String.eq(s, "+"), it, Main.laid.old(rest)))), w, at, nat}}) == Done{List.append(&2, Ops.Item, w, List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lnew(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr), Main.laid.side(String.eq(s, "-"), it, Main.laid.new(rest)))))} : Result<&2, &2, String, List<&2, Ops.Item>>}
          %Equal.sym(Bool, String.eq(s, "+"), False{}, Equal.cong(String, Bool, z => String.eq(z, "+"), s, " ", S.eq_true(s, " ", not_false(String.eq(s, " "), ML.or_false_left(Main.laid.changed(s), Bool.or(Nat.is_gt(owed, 0n), Main.changed.near(rest, 3n)), esh))))) : {Main.patch.go(Main.hunks.close(List.append(&2, Main.Numbered, ks, Nil{}), cut_with(Nil{}, Main.hunks.walk(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Main.hunks.owed(Main.laid.changed(s), owed)))), Done{Main.Patching{List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lold(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr), Main.laid.side(_, it, Main.laid.old(rest)))), w, at, nat}}) == Done{List.append(&2, Ops.Item, w, List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lnew(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr), Main.laid.side(String.eq(s, "-"), it, Main.laid.new(rest)))))} : Result<&2, &2, String, List<&2, Ops.Item>>}
          %Equal.sym(Bool, String.eq(s, "-"), False{}, Equal.cong(String, Bool, z => String.eq(z, "-"), s, " ", S.eq_true(s, " ", not_false(String.eq(s, " "), ML.or_false_left(Main.laid.changed(s), Bool.or(Nat.is_gt(owed, 0n), Main.changed.near(rest, 3n)), esh))))) : {Main.patch.go(Main.hunks.close(List.append(&2, Main.Numbered, ks, Nil{}), cut_with(Nil{}, Main.hunks.walk(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Main.hunks.owed(Main.laid.changed(s), owed)))), Done{Main.Patching{List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lold(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr), it <> Main.laid.old(rest))), w, at, nat}}) == Done{List.append(&2, Ops.Item, w, List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lnew(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr), Main.laid.side(_, it, Main.laid.new(rest)))))} : Result<&2, &2, String, List<&2, Ops.Item>>}
          %Equal.sym(List<&2, Main.Numbered>, List.append(&2, Main.Numbered, kr, Nil{}), kr, nlapp_nil(kr)) : {Main.patch.go(Main.hunk.of(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> _) <> cut_with(Nil{}, Main.hunks.walk(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Main.hunks.owed(Main.laid.changed(s), owed))), Done{Main.Patching{List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lold(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr), it <> Main.laid.old(rest))), w, at, nat}}) == Done{List.append(&2, Ops.Item, w, List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lnew(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr), it <> Main.laid.new(rest))))} : Result<&2, &2, String, List<&2, Ops.Item>>}
          close_ok(sk, itk, bk, ak, kr, g, it <> Main.laid.old(rest), it <> Main.laid.new(rest), w, at, nat, cut_with(Nil{}, Main.hunks.walk(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Main.hunks.owed(Main.laid.changed(s), owed))), hk, h3,
            ih(Nil{}, [it], List.append(&2, Ops.Item, List.append(&2, Ops.Item, w, g), lnew(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr)), Nat.add(bk, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "+")), Nat.add(ak, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "-")), {==}, Equal.trans(Nat, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), 1n+b, 1n+Nat.add(Nat.add(bk, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "+")), 0n), Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, b, 1n+b), String.eq(s, "+"), False{}, Equal.cong(String, Bool, z => String.eq(z, "+"), s, " ", S.eq_true(s, " ", not_false(String.eq(s, " "), ML.or_false_left(Main.laid.changed(s), Bool.or(Nat.is_gt(owed, 0n), Main.changed.near(rest, 3n)), esh))))), Equal.cong(Nat, Nat, v => 1n+v, b, Nat.add(Nat.add(bk, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "+")), 0n), Equal.trans(Nat, b, Nat.add(bk, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "+")), Nat.add(Nat.add(bk, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "+")), 0n), Equal.trans(Nat, b, Nat.add(Nat.add(List.length(&2, Ops.Item, g), at), Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "+")), Nat.add(bk, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "+")), h1, Equal.cong(Nat, Nat, v => Nat.add(v, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "+")), Nat.add(List.length(&2, Ops.Item, g), at), bk, ML.nat_eq(Nat.add(List.length(&2, Ops.Item, g), at), bk, Comp.and_left(Nat.is_eq(Nat.add(List.length(&2, Ops.Item, g), at), bk), Bool.and(Nat.is_eq(Nat.add(List.length(&2, Ops.Item, g), nat), ak), Bool.or(String.eq(sk, " "), Bool.and(Nat.is_eq(bk, 1n), Nat.is_eq(ak, 1n)))), h3)))), Equal.sym(Nat, Nat.add(Nat.add(bk, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "+")), 0n), Nat.add(bk, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "+")), Comp.add_zero(Nat.add(bk, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "+"))))))), Equal.trans(Nat, Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), 1n+a, 1n+Nat.add(Nat.add(ak, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "-")), 0n), Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, a, 1n+a), String.eq(s, "-"), False{}, Equal.cong(String, Bool, z => String.eq(z, "-"), s, " ", S.eq_true(s, " ", not_false(String.eq(s, " "), ML.or_false_left(Main.laid.changed(s), Bool.or(Nat.is_gt(owed, 0n), Main.changed.near(rest, 3n)), esh))))), Equal.cong(Nat, Nat, v => 1n+v, a, Nat.add(Nat.add(ak, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "-")), 0n), Equal.trans(Nat, a, Nat.add(ak, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "-")), Nat.add(Nat.add(ak, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "-")), 0n), Equal.trans(Nat, a, Nat.add(Nat.add(List.length(&2, Ops.Item, g), nat), Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "-")), Nat.add(ak, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "-")), h2, Equal.cong(Nat, Nat, v => Nat.add(v, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "-")), Nat.add(List.length(&2, Ops.Item, g), nat), ak, ML.nat_eq(Nat.add(List.length(&2, Ops.Item, g), nat), ak, Comp.and_left(Nat.is_eq(Nat.add(List.length(&2, Ops.Item, g), nat), ak), Bool.or(String.eq(sk, " "), Bool.and(Nat.is_eq(bk, 1n), Nat.is_eq(ak, 1n))), Comp.and_right(Nat.is_eq(Nat.add(List.length(&2, Ops.Item, g), at), bk), Bool.and(Nat.is_eq(Nat.add(List.length(&2, Ops.Item, g), nat), ak), Bool.or(String.eq(sk, " "), Bool.and(Nat.is_eq(bk, 1n), Nat.is_eq(ak, 1n)))), h3))))), Equal.sym(Nat, Nat.add(Nat.add(ak, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "-")), 0n), Nat.add(ak, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "-")), Comp.add_zero(Nat.add(ak, Main.hunk.count(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr, "-"))))))), near_fresh(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), ML.or_false_right(Nat.is_gt(owed, 0n), Main.changed.near(rest, 3n), ML.or_false_right(Main.laid.changed(s), Bool.or(Nat.is_gt(owed, 0n), Main.changed.near(rest, 3n)), esh)))))

# The whole walk, by induction on its lines.
def walk_ok(ls: List<&2, Main.Laid>, +b: Nat, +a: Nat, +owed: Nat, ks: List<&2, Main.Numbered>, +g: List<&2, Ops.Item>, +w: List<&2, Ops.Item>, +at: Nat, +nat: Nat, +hl: {lsigns(ls) == True{} : Bool}, +hk: {nsigns(ks) == True{} : Bool}, +h1: {b == Nat.add(Nat.add(List.length(&2, Ops.Item, g), at), Main.hunk.count(ks, "+")) : Nat}, +h2: {a == Nat.add(Nat.add(List.length(&2, Ops.Item, g), nat), Main.hunk.count(ks, "-")) : Nat}, +h3: {start_ok(ks, ls, b, a, Nat.add(List.length(&2, Ops.Item, g), at), Nat.add(List.length(&2, Ops.Item, g), nat)) == True{} : Bool}) -> {Main.patch.go(cut_with(ks, Main.hunks.walk(ls, b, a, owed)), Done{Main.Patching{List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lold(ks), Main.laid.old(ls))), w, at, nat}}) == Done{List.append(&2, Ops.Item, w, List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lnew(ks), Main.laid.new(ls))))} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match ls:
    case Nil{}:
      match ks:
        case Nil{}:
          {==}
        case Main.Numbered{Main.Laid{+sk, +itk}, +bk, +ak} <> +kr:
          %Equal.sym(List<&2, Main.Numbered>, List.append(&2, Main.Numbered, kr, Nil{}), kr, nlapp_nil(kr)) : {Main.patch.go(Main.hunk.of(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> _) <> Nil{}, Done{Main.Patching{List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lold(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr), Nil{})), w, at, nat}}) == Done{List.append(&2, Ops.Item, w, List.append(&2, Ops.Item, g, List.append(&2, Ops.Item, lnew(Main.Numbered{Main.Laid{sk, itk}, bk, ak} <> kr), Nil{})))} : Result<&2, &2, String, List<&2, Ops.Item>>}
          close_ok(sk, itk, bk, ak, kr, g, Nil{}, Nil{}, w, at, nat, Nil{}, hk, h3, {==})
    case Main.Laid{+s, +it} <> +rest:
      walk_cons(Main.hunks.showing(Main.laid.changed(s), owed, Main.changed.near(rest, 3n)), s, it, rest, b, a, owed, ks, g, w, at, nat, {==}, Comp.and_left(sign_ok(s), lsigns(rest), hl), hk, h1, h2, h3,
        ks2 => g2 => w2 => at2 => nat2 => k2 => e1 => e2 => e3 => walk_ok(rest, Bool.pick(Nat, String.eq(s, "+"), b, 1n+b), Bool.pick(Nat, String.eq(s, "-"), a, 1n+a), Main.hunks.owed(Main.laid.changed(s), owed), ks2, g2, w2, at2, nat2, Comp.and_right(sign_ok(s), lsigns(rest), hl), k2, e1, e2, e3))

# The hunks of any laid lines whose marks are ' ', '-' and '+', read as
# `patch` reads them, take the lines that are not arrivals to the lines that
# are not removals.
def hunks_apply(+ls: List<&2, Main.Laid>, +hl: {lsigns(ls) == True{} : Bool}) -> {Main.patch(Main.laid.old(ls), Main.hunks.made(ls)) == Done{Main.laid.new(ls)} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  %with_nil(Main.hunks.walk(ls, 1n, 1n, 0n)) : {Main.patch.go(_, Done{Main.Patching{Main.laid.old(ls), Nil{}, 1n, 1n}}) == Done{Main.laid.new(ls)} : Result<&2, &2, String, List<&2, Ops.Item>>}
  walk_ok(ls, 1n, 1n, 0n, Nil{}, Nil{}, Nil{}, 1n, 1n, hl, {==}, {==}, {==}, fresh_one(ls))

# What is laid is marked ' ', '-' or '+', line by line.
def lsigns_app(xs: List<&2, Main.Laid>, +ys: List<&2, Main.Laid>, +hx: {lsigns(xs) == True{} : Bool}, hy: {lsigns(ys) == True{} : Bool}) -> {lsigns(List.append(&2, Main.Laid, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Main.Laid{+s, it} <> +rest:
      ML.and_intro(sign_ok(s), lsigns(List.append(&2, Main.Laid, rest, ys)), Comp.and_left(sign_ok(s), lsigns(rest), hx), lsigns_app(rest, ys, Comp.and_right(sign_ok(s), lsigns(rest), hx), hy))

def lsigns_all(+sign: String, items: List<&2, Ops.Item>, +hs: {sign_ok(sign) == True{} : Bool}) -> {lsigns(Main.laid.all(sign, items)) == True{} : Bool}:
  match items:
    case Nil{}:
      {==}
    case it <> rest:
      ML.and_intro(sign_ok(sign), lsigns(Main.laid.all(sign, rest)), hs, lsigns_all(sign, rest, hs))

def lsigns_walk(ops: List<&2, Ops.Op>, +pos: Nat, +state: List<&2, Ops.Item>) -> {lsigns(Main.laid.walk(ops, pos, state)) == True{} : Bool}:
  match ops:
    case Nil{}:
      lsigns_all(" ", state, {==})
    case Ops.Op{Ops.Insert{}, +at, +items} <> +rest:
      lsigns_app(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))), List.append(&2, Main.Laid, Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))), lsigns_all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)), {==}),
        lsigns_app(Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos))), lsigns_all("+", items, {==}), lsigns_walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))
    case Ops.Op{Ops.Delete{}, +at, +items} <> +rest:
      lsigns_app(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))), List.append(&2, Main.Laid, Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))), lsigns_all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)), {==}),
        lsigns_app(Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), lsigns_all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)), {==}), lsigns_walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))

def lsigns_laid(+parent: List<&2, Ops.Item>, doc: Ops.Doc) -> {lsigns(Main.laid(parent, doc)) == True{} : Bool}:
  match doc:
    case Ops.Doc{f, r, ops}:
      lsigns_walk(ops, 0n, parent)

# The hunks diff draws for a document, read back as `patch` reads them,
# take the parent to whatever the document's lines say the child is.
def hunks_patch(+parent: List<&2, Ops.Item>, +doc: Ops.Doc, +child: List<&2, Ops.Item>, eo: {Main.laid.old(Main.laid(parent, doc)) == parent : List<&2, Ops.Item>}, en: {Main.laid.new(Main.laid(parent, doc)) == child : List<&2, Ops.Item>}) -> {Main.patch(parent, Main.hunks.made(Main.laid(parent, doc))) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  %eo : {Main.patch(_, Main.hunks.made(Main.laid(parent, doc))) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %en : {Main.patch(Main.laid.old(Main.laid(parent, doc)), Main.hunks.made(Main.laid(parent, doc))) == Done{_} : Result<&2, &2, String, List<&2, Ops.Item>>}
  hunks_apply(Main.laid(parent, doc), lsigns_laid(parent, doc))
