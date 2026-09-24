# Emphasis marks each line with its own words. Where colour draws a run of
# removals replaced one for one by as many arrivals, each pair is compared
# and marked; every mark falls on its own line — the runs it draws read as
# that line, and only a removal or an arrival is marked.
import Base
import ./ops.bend as Ops
import ./main.bend as Main
import ./emphasis_lemmas.bend as Emph
import ./composition_lemmas.bend as Comp
import ./merge_lemmas.bend as ML
import ./string_lemmas.bend as S

def all_changed(ns: List<&2, Main.Numbered>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case n <> rest:
      Bool.and(Main.laid.changed(Main.numbered.sign(n)), all_changed(rest))

def fit_nil(ns: List<&2, Main.Numbered>) -> {Main.marks.fit(ns, Nil{}) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case n <> rest:
      {==}

def mapp_assoc(xs: List<&2, Maybe<&2, List<&2, Main.Piece>>>, -ys: List<&2, Maybe<&2, List<&2, Main.Piece>>>, -zs: List<&2, Maybe<&2, List<&2, Main.Piece>>>) -> {List.append(&2, Maybe<&2, List<&2, Main.Piece>>, List.append(&2, Maybe<&2, List<&2, Main.Piece>>, xs, ys), zs) == List.append(&2, Maybe<&2, List<&2, Main.Piece>>, xs, List.append(&2, Maybe<&2, List<&2, Main.Piece>>, ys, zs)) : List<&2, Maybe<&2, List<&2, Main.Piece>>>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Equal.cong(List<&2, Maybe<&2, List<&2, Main.Piece>>>, List<&2, Maybe<&2, List<&2, Main.Piece>>>, l => x <> l, List.append(&2, Maybe<&2, List<&2, Main.Piece>>, List.append(&2, Maybe<&2, List<&2, Main.Piece>>, rest, ys), zs), List.append(&2, Maybe<&2, List<&2, Main.Piece>>, rest, List.append(&2, Maybe<&2, List<&2, Main.Piece>>, ys, zs)), mapp_assoc(rest, ys, zs))

def nlapp_assoc(xs: List<&2, Main.Numbered>, -ys: List<&2, Main.Numbered>, -zs: List<&2, Main.Numbered>) -> {List.append(&2, Main.Numbered, List.append(&2, Main.Numbered, xs, ys), zs) == List.append(&2, Main.Numbered, xs, List.append(&2, Main.Numbered, ys, zs)) : List<&2, Main.Numbered>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Equal.cong(List<&2, Main.Numbered>, List<&2, Main.Numbered>, l => x <> l, List.append(&2, Main.Numbered, List.append(&2, Main.Numbered, rest, ys), zs), List.append(&2, Main.Numbered, rest, List.append(&2, Main.Numbered, ys, zs)), nlapp_assoc(rest, ys, zs))

# One pair's marks
# ----------------

def was_one(m: Maybe<&2, Main.Marked>, +r: Main.Numbered, +a: Main.Numbered, em: {Main.apart(Main.numbered.shown(r), Main.numbered.shown(a)) == m : Maybe<&2, Main.Marked>}, hr: {Main.laid.changed(Main.numbered.sign(r)) == True{} : Bool}) -> {Main.mark.fits(r, Main.mark.was(m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{Main.Marked{+w, n}}:
      %Equal.sym(String, Main.pieces.text(w), Main.numbered.shown(r), Emph.apart_was(Main.numbered.shown(r), Main.numbered.shown(a), w, n, em)) : {Bool.and(String.eq(_, Main.numbered.shown(r)), Main.laid.changed(Main.numbered.sign(r))) == True{} : Bool}
      %Equal.sym(Bool, String.eq(Main.numbered.shown(r), Main.numbered.shown(r)), True{}, S.eq_refl(Main.numbered.shown(r))) : {Bool.and(_, Main.laid.changed(Main.numbered.sign(r))) == True{} : Bool}
      hr

def now_one(m: Maybe<&2, Main.Marked>, +r: Main.Numbered, +a: Main.Numbered, em: {Main.apart(Main.numbered.shown(r), Main.numbered.shown(a)) == m : Maybe<&2, Main.Marked>}, ha: {Main.laid.changed(Main.numbered.sign(a)) == True{} : Bool}) -> {Main.mark.fits(a, Main.mark.now(m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{Main.Marked{w, +n}}:
      %Equal.sym(String, Main.pieces.text(n), Main.numbered.shown(a), Emph.apart_now(Main.numbered.shown(r), Main.numbered.shown(a), w, n, em)) : {Bool.and(String.eq(_, Main.numbered.shown(a)), Main.laid.changed(Main.numbered.sign(a))) == True{} : Bool}
      %Equal.sym(Bool, String.eq(Main.numbered.shown(a), Main.numbered.shown(a)), True{}, S.eq_refl(Main.numbered.shown(a))) : {Bool.and(_, Main.laid.changed(Main.numbered.sign(a))) == True{} : Bool}
      ha

# A run's marks
# -------------

# The removals' marks fall on the removals, each pair's on its removal, and
# the arrivals' on the arrivals, when the two runs are as long.
def was_fit(rem: List<&2, Main.Numbered>, arr: List<&2, Main.Numbered>, +y: List<&2, Main.Numbered>, +z: List<&2, Maybe<&2, List<&2, Main.Piece>>>, hlen: {Nat.is_eq(List.length(&2, Main.Numbered, rem), List.length(&2, Main.Numbered, arr)) == True{} : Bool}, +hrem: {all_changed(rem) == True{} : Bool}, h: {Main.marks.fit(y, z) == True{} : Bool}) -> {Main.marks.fit(List.append(&2, Main.Numbered, rem, y), List.append(&2, Maybe<&2, List<&2, Main.Piece>>, Main.marks.was(Main.pairs(rem, arr)), z)) == True{} : Bool}:
  match rem arr:
    case Nil{} Nil{}:
      h
    case Nil{} a <> as:
      Empty.absurd({Main.marks.fit(y, z) == True{} : Bool}, S.false_true(hlen))
    case r <> rs Nil{}:
      Empty.absurd({Main.marks.fit(List.append(&2, Main.Numbered, r <> rs, y), z) == True{} : Bool}, S.false_true(hlen))
    case +r <> +rs +a <> +as:
      ML.and_intro(Main.mark.fits(r, Main.mark.was(Main.apart(Main.numbered.shown(r), Main.numbered.shown(a)))), Main.marks.fit(List.append(&2, Main.Numbered, rs, y), List.append(&2, Maybe<&2, List<&2, Main.Piece>>, Main.marks.was(Main.pairs(rs, as)), z)),
        was_one(Main.apart(Main.numbered.shown(r), Main.numbered.shown(a)), r, a, {==}, Comp.and_left(Main.laid.changed(Main.numbered.sign(r)), all_changed(rs), hrem)),
        was_fit(rs, as, y, z, hlen, Comp.and_right(Main.laid.changed(Main.numbered.sign(r)), all_changed(rs), hrem), h))

def now_fit(rem: List<&2, Main.Numbered>, arr: List<&2, Main.Numbered>, +y: List<&2, Main.Numbered>, +z: List<&2, Maybe<&2, List<&2, Main.Piece>>>, hlen: {Nat.is_eq(List.length(&2, Main.Numbered, rem), List.length(&2, Main.Numbered, arr)) == True{} : Bool}, +harr: {all_changed(arr) == True{} : Bool}, h: {Main.marks.fit(y, z) == True{} : Bool}) -> {Main.marks.fit(List.append(&2, Main.Numbered, arr, y), List.append(&2, Maybe<&2, List<&2, Main.Piece>>, Main.marks.now(Main.pairs(rem, arr)), z)) == True{} : Bool}:
  match rem arr:
    case Nil{} Nil{}:
      h
    case Nil{} a <> as:
      Empty.absurd({Main.marks.fit(List.append(&2, Main.Numbered, a <> as, y), z) == True{} : Bool}, S.false_true(hlen))
    case r <> rs Nil{}:
      Empty.absurd({Main.marks.fit(y, z) == True{} : Bool}, S.false_true(hlen))
    case +r <> +rs +a <> +as:
      ML.and_intro(Main.mark.fits(a, Main.mark.now(Main.apart(Main.numbered.shown(r), Main.numbered.shown(a)))), Main.marks.fit(List.append(&2, Main.Numbered, as, y), List.append(&2, Maybe<&2, List<&2, Main.Piece>>, Main.marks.now(Main.pairs(rs, as)), z)),
        now_one(Main.apart(Main.numbered.shown(r), Main.numbered.shown(a)), r, a, {==}, Comp.and_left(Main.laid.changed(Main.numbered.sign(a)), all_changed(as), harr)),
        now_fit(rs, as, y, z, hlen, Comp.and_right(Main.laid.changed(Main.numbered.sign(a)), all_changed(as), harr), h))

# An unpaired run is left plain.
def none_fit(xs: List<&2, Main.Numbered>, +y: List<&2, Main.Numbered>, +z: List<&2, Maybe<&2, List<&2, Main.Piece>>>, h: {Main.marks.fit(y, z) == True{} : Bool}) -> {Main.marks.fit(List.append(&2, Main.Numbered, xs, y), List.append(&2, Maybe<&2, List<&2, Main.Piece>>, Main.marks.none(xs), z)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case x <> rest:
      none_fit(rest, y, z, h)

def changed_of(+n: Main.Numbered, +sign: String, eh: {String.eq(Main.numbered.sign(n), sign) == True{} : Bool}, hs: {String.eq(sign, " ") == False{} : Bool}) -> {Main.laid.changed(Main.numbered.sign(n)) == True{} : Bool}:
  %Equal.sym(String, Main.numbered.sign(n), sign, S.eq_true(Main.numbered.sign(n), sign, eh)) : {Bool.not(String.eq(_, " ")) == True{} : Bool}
  %Equal.sym(Bool, String.eq(sign, " "), False{}, hs) : {Bool.not(_) == True{} : Bool}
  {==}

# Splitting a run
# ---------------

def run_lines(r: Main.Run) -> List<&2, Main.Numbered>:
  match r:
    case Main.Run{ls, rest}:
      ls

def run_rest(r: Main.Run) -> List<&2, Main.Numbered>:
  match r:
    case Main.Run{ls, rest}:
      rest

def cons_app(+n: Main.Numbered, r: Main.Run) -> {List.append(&2, Main.Numbered, run_lines(Main.run.cons(n, r)), run_rest(Main.run.cons(n, r))) == n <> List.append(&2, Main.Numbered, run_lines(r), run_rest(r)) : List<&2, Main.Numbered>}:
  match r:
    case Main.Run{ls, rest}:
      {==}

def cons_lines(+n: Main.Numbered, r: Main.Run) -> {run_lines(Main.run.cons(n, r)) == n <> run_lines(r) : List<&2, Main.Numbered>}:
  match r:
    case Main.Run{ls, rest}:
      {==}

# A run and the lines after it are the lines split.
def split_app(ns: List<&2, Main.Numbered>, +sign: String, hit: Bool) -> {List.append(&2, Main.Numbered, run_lines(Main.run.split(ns, sign, hit)), run_rest(Main.run.split(ns, sign, hit))) == ns : List<&2, Main.Numbered>}:
  match ns:
    case Nil{}:
      {==}
    case +n <> +rest:
      match hit:
        case False{}:
          {==}
        case True{}:
          Equal.trans(List<&2, Main.Numbered>, List.append(&2, Main.Numbered, run_lines(Main.run.cons(n, Main.run.split(rest, sign, Main.head_is(rest, sign)))), run_rest(Main.run.cons(n, Main.run.split(rest, sign, Main.head_is(rest, sign))))), n <> List.append(&2, Main.Numbered, run_lines(Main.run.split(rest, sign, Main.head_is(rest, sign))), run_rest(Main.run.split(rest, sign, Main.head_is(rest, sign)))), n <> rest,
            cons_app(n, Main.run.split(rest, sign, Main.head_is(rest, sign))),
            Equal.cong(List<&2, Main.Numbered>, List<&2, Main.Numbered>, l => n <> l, List.append(&2, Main.Numbered, run_lines(Main.run.split(rest, sign, Main.head_is(rest, sign))), run_rest(Main.run.split(rest, sign, Main.head_is(rest, sign)))), rest, split_app(rest, sign, Main.head_is(rest, sign))))

# A run of removals, or of arrivals, is changed lines.
def split_changed(ns: List<&2, Main.Numbered>, +sign: String, hit: Bool, eh: {Main.head_is(ns, sign) == hit : Bool}, +hs: {String.eq(sign, " ") == False{} : Bool}) -> {all_changed(run_lines(Main.run.split(ns, sign, hit))) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +n <> +rest:
      match hit:
        case False{}:
          {==}
        case True{}:
          %Equal.sym(List<&2, Main.Numbered>, run_lines(Main.run.cons(n, Main.run.split(rest, sign, Main.head_is(rest, sign)))), n <> run_lines(Main.run.split(rest, sign, Main.head_is(rest, sign))), cons_lines(n, Main.run.split(rest, sign, Main.head_is(rest, sign)))) : {all_changed(_) == True{} : Bool}
          ML.and_intro(Main.laid.changed(Main.numbered.sign(n)), all_changed(run_lines(Main.run.split(rest, sign, Main.head_is(rest, sign)))),
            changed_of(n, sign, eh, hs),
            split_changed(rest, sign, Main.head_is(rest, sign), {==}, hs))

# A chunk's marks
# ---------------

def pair_fit(paired: Bool, +rem: List<&2, Main.Numbered>, +arr: List<&2, Main.Numbered>, +rest2: List<&2, Main.Numbered>, +q: Nat, +ep: {Bool.and(Nat.is_gt(List.length(&2, Main.Numbered, rem), 0n), Nat.is_eq(List.length(&2, Main.Numbered, rem), List.length(&2, Main.Numbered, arr))) == paired : Bool}, hrem: {all_changed(rem) == True{} : Bool}, harr: {all_changed(arr) == True{} : Bool}, ih: @xs: List<&2, Main.Numbered> -> {Main.marks.fit(xs, Main.emph.go(q, xs)) == True{} : Bool}) -> {Main.marks.fit(List.append(&2, Main.Numbered, rem, List.append(&2, Main.Numbered, arr, rest2)), List.append(&2, Maybe<&2, List<&2, Main.Piece>>, Main.chunked.marks(Main.emph.pair(paired, rem, arr, rest2)), Main.emph.go(q, Main.chunked.after(Main.emph.pair(paired, rem, arr, rest2))))) == True{} : Bool}:
  match paired:
    case True{}:
      %Equal.sym(List<&2, Maybe<&2, List<&2, Main.Piece>>>, List.append(&2, Maybe<&2, List<&2, Main.Piece>>, List.append(&2, Maybe<&2, List<&2, Main.Piece>>, Main.marks.was(Main.pairs(rem, arr)), Main.marks.now(Main.pairs(rem, arr))), Main.emph.go(q, rest2)), List.append(&2, Maybe<&2, List<&2, Main.Piece>>, Main.marks.was(Main.pairs(rem, arr)), List.append(&2, Maybe<&2, List<&2, Main.Piece>>, Main.marks.now(Main.pairs(rem, arr)), Main.emph.go(q, rest2))), mapp_assoc(Main.marks.was(Main.pairs(rem, arr)), Main.marks.now(Main.pairs(rem, arr)), Main.emph.go(q, rest2))) : {Main.marks.fit(List.append(&2, Main.Numbered, rem, List.append(&2, Main.Numbered, arr, rest2)), _) == True{} : Bool}
      was_fit(rem, arr, List.append(&2, Main.Numbered, arr, rest2), List.append(&2, Maybe<&2, List<&2, Main.Piece>>, Main.marks.now(Main.pairs(rem, arr)), Main.emph.go(q, rest2)), Comp.and_right(Nat.is_gt(List.length(&2, Main.Numbered, rem), 0n), Nat.is_eq(List.length(&2, Main.Numbered, rem), List.length(&2, Main.Numbered, arr)), ep), hrem, now_fit(rem, arr, rest2, Main.emph.go(q, rest2), Comp.and_right(Nat.is_gt(List.length(&2, Main.Numbered, rem), 0n), Nat.is_eq(List.length(&2, Main.Numbered, rem), List.length(&2, Main.Numbered, arr)), ep), harr, ih(rest2)))
    case False{}:
      %nlapp_assoc(rem, arr, rest2) : {Main.marks.fit(_, List.append(&2, Maybe<&2, List<&2, Main.Piece>>, Main.marks.none(List.append(&2, Main.Numbered, rem, arr)), Main.emph.go(q, rest2))) == True{} : Bool}
      none_fit(List.append(&2, Main.Numbered, rem, arr), rest2, Main.emph.go(q, rest2), ih(rest2))

def step_r2(r2: Main.Run, +rem: List<&2, Main.Numbered>, +after1: List<&2, Main.Numbered>, +n: Main.Numbered, +rest: List<&2, Main.Numbered>, +q: Nat, +er1: {Main.run.split(n <> rest, "-", Main.head_is(n <> rest, "-")) == Main.Run{rem, after1} : Main.Run}, +er2: {Main.run.split(after1, "+", Main.head_is(after1, "+")) == r2 : Main.Run}, ih: @xs: List<&2, Main.Numbered> -> {Main.marks.fit(xs, Main.emph.go(q, xs)) == True{} : Bool}) -> {Main.marks.fit(n <> rest, List.append(&2, Maybe<&2, List<&2, Main.Piece>>, Main.chunked.marks(Main.emph.arrivals(rem, r2)), Main.emph.go(q, Main.chunked.after(Main.emph.arrivals(rem, r2))))) == True{} : Bool}:
  match r2:
    case Main.Run{+arr, +rest2}:
      %Equal.trans(List<&2, Main.Numbered>, List.append(&2, Main.Numbered, rem, List.append(&2, Main.Numbered, arr, rest2)), List.append(&2, Main.Numbered, rem, after1), n <> rest,
        Equal.cong(List<&2, Main.Numbered>, List<&2, Main.Numbered>, v => List.append(&2, Main.Numbered, rem, v), List.append(&2, Main.Numbered, arr, rest2), after1,
          Equal.trans(List<&2, Main.Numbered>, List.append(&2, Main.Numbered, arr, rest2), List.append(&2, Main.Numbered, run_lines(Main.run.split(after1, "+", Main.head_is(after1, "+"))), run_rest(Main.run.split(after1, "+", Main.head_is(after1, "+")))), after1,
            Equal.cong(Main.Run, List<&2, Main.Numbered>, v => List.append(&2, Main.Numbered, run_lines(v), run_rest(v)), Main.Run{arr, rest2}, Main.run.split(after1, "+", Main.head_is(after1, "+")), Equal.sym(Main.Run, Main.run.split(after1, "+", Main.head_is(after1, "+")), Main.Run{arr, rest2}, er2)),
            split_app(after1, "+", Main.head_is(after1, "+")))),
        Equal.trans(List<&2, Main.Numbered>, List.append(&2, Main.Numbered, rem, after1), List.append(&2, Main.Numbered, run_lines(Main.run.split(n <> rest, "-", Main.head_is(n <> rest, "-"))), run_rest(Main.run.split(n <> rest, "-", Main.head_is(n <> rest, "-")))), n <> rest,
          Equal.cong(Main.Run, List<&2, Main.Numbered>, v => List.append(&2, Main.Numbered, run_lines(v), run_rest(v)), Main.Run{rem, after1}, Main.run.split(n <> rest, "-", Main.head_is(n <> rest, "-")), Equal.sym(Main.Run, Main.run.split(n <> rest, "-", Main.head_is(n <> rest, "-")), Main.Run{rem, after1}, er1)),
          split_app(n <> rest, "-", Main.head_is(n <> rest, "-")))) : {Main.marks.fit(_, List.append(&2, Maybe<&2, List<&2, Main.Piece>>, Main.chunked.marks(Main.emph.pair(Bool.and(Nat.is_gt(List.length(&2, Main.Numbered, rem), 0n), Nat.is_eq(List.length(&2, Main.Numbered, rem), List.length(&2, Main.Numbered, arr))), rem, arr, rest2)), Main.emph.go(q, Main.chunked.after(Main.emph.pair(Bool.and(Nat.is_gt(List.length(&2, Main.Numbered, rem), 0n), Nat.is_eq(List.length(&2, Main.Numbered, rem), List.length(&2, Main.Numbered, arr))), rem, arr, rest2))))) == True{} : Bool}
      pair_fit(Bool.and(Nat.is_gt(List.length(&2, Main.Numbered, rem), 0n), Nat.is_eq(List.length(&2, Main.Numbered, rem), List.length(&2, Main.Numbered, arr))), rem, arr, rest2, q, {==},
        Equal.trans(Bool, all_changed(rem), all_changed(run_lines(Main.run.split(n <> rest, "-", Main.head_is(n <> rest, "-")))), True{}, Equal.cong(Main.Run, Bool, v => all_changed(run_lines(v)), Main.Run{rem, after1}, Main.run.split(n <> rest, "-", Main.head_is(n <> rest, "-")), Equal.sym(Main.Run, Main.run.split(n <> rest, "-", Main.head_is(n <> rest, "-")), Main.Run{rem, after1}, er1)), split_changed(n <> rest, "-", Main.head_is(n <> rest, "-"), {==}, {==})),
        Equal.trans(Bool, all_changed(arr), all_changed(run_lines(Main.run.split(after1, "+", Main.head_is(after1, "+")))), True{}, Equal.cong(Main.Run, Bool, v => all_changed(run_lines(v)), Main.Run{arr, rest2}, Main.run.split(after1, "+", Main.head_is(after1, "+")), Equal.sym(Main.Run, Main.run.split(after1, "+", Main.head_is(after1, "+")), Main.Run{arr, rest2}, er2)), split_changed(after1, "+", Main.head_is(after1, "+"), {==}, {==})),
        ih)

def step_r1(r1: Main.Run, +n: Main.Numbered, +rest: List<&2, Main.Numbered>, +q: Nat, er1: {Main.run.split(n <> rest, "-", Main.head_is(n <> rest, "-")) == r1 : Main.Run}, ih: @xs: List<&2, Main.Numbered> -> {Main.marks.fit(xs, Main.emph.go(q, xs)) == True{} : Bool}) -> {Main.marks.fit(n <> rest, List.append(&2, Maybe<&2, List<&2, Main.Piece>>, Main.chunked.marks(Main.emph.removals(r1)), Main.emph.go(q, Main.chunked.after(Main.emph.removals(r1))))) == True{} : Bool}:
  match r1:
    case Main.Run{+rem, +after1}:
      step_r2(Main.run.split(after1, "+", Main.head_is(after1, "+")), rem, after1, n, rest, q, er1, {==}, ih)

def step_fit(ch: Bool, +n: Main.Numbered, +rest: List<&2, Main.Numbered>, +q: Nat, ih: @xs: List<&2, Main.Numbered> -> {Main.marks.fit(xs, Main.emph.go(q, xs)) == True{} : Bool}) -> {Main.marks.fit(n <> rest, List.append(&2, Maybe<&2, List<&2, Main.Piece>>, Main.chunked.marks(Main.emph.step(ch, n, rest)), Main.emph.go(q, Main.chunked.after(Main.emph.step(ch, n, rest))))) == True{} : Bool}:
  match ch:
    case True{}:
      step_r1(Main.run.split(n <> rest, "-", Main.head_is(n <> rest, "-")), n, rest, q, {==}, ih)
    case False{}:
      ih(rest)

# Every mark emphasis computes falls on its own line.
def go_fit(fuel: Nat, ns: List<&2, Main.Numbered>) -> {Main.marks.fit(ns, Main.emph.go(fuel, ns)) == True{} : Bool}:
  match fuel ns:
    case 0n Nil{}:
      {==}
    case 0n n <> rest:
      {==}
    case 1n+q Nil{}:
      {==}
    case 1n++q +n <> +rest:
      step_fit(Main.laid.changed(Main.numbered.sign(n)), n, rest, q, xs => go_fit(q, xs))

def emph_fit(+ns: List<&2, Main.Numbered>, paint: Bool) -> {Main.marks.fit(ns, Main.emph(ns, paint)) == True{} : Bool}:
  match paint:
    case True{}:
      go_fit(1n+List.length(&2, Main.Numbered, ns), ns)
    case False{}:
      fit_nil(ns)
