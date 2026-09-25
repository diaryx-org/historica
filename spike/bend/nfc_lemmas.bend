# Normal form C's laws: a string of ASCII is its own normal form; canonical
# ordering puts every run of marks in order of class; the class lookup,
# which stops early, misses nothing over the crate's table; `/` and `.` are
# walls the algorithm composes nothing across. And the walk's: it yields a path
# once, and opens a file only where the folder spells it.
import Base
import ./nfc.bend as N
import ./nfc_tables.bend as Tab
import ./string_lemmas.bend as S
import ./sort_lemmas.bend as SortL
import ./equality_lemmas.bend as EqL
import ./folder.bend as F
import ./text.bend as T
import ./position_lemmas.bend as Pos
import ./composition_lemmas.bend as Comp

def and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(e))

def and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, S.false_true(e))

def and_i(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

# ASCII
# -----

# Every character of an ASCII string passes the quick check, as each is
# below 128.
def quick_ascii(s: String, +e: {N.ascii(s) == True{} : Bool}) -> {N.quick(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, t}:
      +lt = and_l(U32.is_lt(x, 128), N.ascii(t), e)
      %Equal.sym(Bool, U32.is_lt(x, 128), True{}, lt) : {Bool.and(Bool.or(_, U32.is_lt(x, Tab.inert_below())), N.quick(t)) == True{} : Bool}
      quick_ascii(t, and_r(U32.is_lt(x, 128), N.ascii(t), e))

def leaves_ascii(+s: String, e: {N.ascii(s) == True{} : Bool}) -> {N.nfc(s) == s : String}:
  %Equal.sym(Bool, N.quick(s), True{}, quick_ascii(s, e)) : {N.nfc.of(s, _) == s : String}
  {==}

# Canonical ordering
# ------------------

# A run of marks in order of class, each no lower than `lo`.
def sorted.from(ms: List<&2, N.Mark>, +lo: U32) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case m <> rest:
      +k = N.mark.class(m)
      Bool.and(U32.is_le(lo, k), sorted.from(rest, k))

def sorted.run(ms: List<&2, N.Mark>) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case m <> rest:
      sorted.from(rest, N.mark.class(m))

# Two classes are in one order or the other.
def le_flip.cmp(c: Cmp, e: {Cmp.is_le(c) == False{} : Bool}) -> {Cmp.is_le(SortL.cflip(c)) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Cmp.is_le(SortL.cflip(LT{})) == True{} : Bool}, S.true_false(e))
    case EQ{}:
      Empty.absurd({Cmp.is_le(SortL.cflip(EQ{})) == True{} : Bool}, S.true_false(e))
    case GT{}:
      {==}

def le_flip(a: U32, b: U32, e: {U32.is_le(a, b) == False{} : Bool}) -> {U32.is_le(b, a) == True{} : Bool}:
  match a b:
    case U32{+x} U32{+y}:
      %Equal.sym(Cmp, Word.cmp(32n, y, x), SortL.cflip(Word.cmp(32n, x, y)), SortL.word_flip(32n, x, y)) : {Cmp.is_le(_) == True{} : Bool}
      le_flip.cmp(Word.cmp(32n, x, y), e)

# One mark into a run in order, above `lo`, leaves it in order above `lo`:
# it goes after every mark of its class or lower, and before the first
# higher one.
def insert_sorted(run: List<&2, N.Mark>, +m: N.Mark, after: Bool, +ea: {N.goes_after(run, m) == after : Bool}, +lo: U32, +hl: {U32.is_le(lo, N.mark.class(m)) == True{} : Bool}, +hs: {sorted.from(run, lo) == True{} : Bool}) -> {sorted.from(N.insert.go(run, m, after), lo) == True{} : Bool}:
  match run after:
    case Nil{} _:
      and_i(U32.is_le(lo, N.mark.class(m)), True{}, hl, {==})
    case +r <> +rest True{}:
      and_i(U32.is_le(lo, N.mark.class(r)), sorted.from(N.insert.go(rest, m, N.goes_after(rest, m)), N.mark.class(r)),
        and_l(U32.is_le(lo, N.mark.class(r)), sorted.from(rest, N.mark.class(r)), hs),
        insert_sorted(rest, m, N.goes_after(rest, m), {==}, N.mark.class(r), ea, and_r(U32.is_le(lo, N.mark.class(r)), sorted.from(rest, N.mark.class(r)), hs)))
    case +r <> +rest False{}:
      and_i(U32.is_le(lo, N.mark.class(m)), Bool.and(U32.is_le(N.mark.class(m), N.mark.class(r)), sorted.from(rest, N.mark.class(r))), hl,
        and_i(U32.is_le(N.mark.class(m), N.mark.class(r)), sorted.from(rest, N.mark.class(r)),
          le_flip(N.mark.class(r), N.mark.class(m), ea),
          and_r(U32.is_le(lo, N.mark.class(r)), sorted.from(rest, N.mark.class(r)), hs)))

def insert_run.of(+r: N.Mark, +rest: List<&2, N.Mark>, +m: N.Mark, after: Bool, +ea: {N.goes_after(r <> rest, m) == after : Bool}, +hs: {sorted.from(rest, N.mark.class(r)) == True{} : Bool}) -> {sorted.run(N.insert.go(r <> rest, m, after)) == True{} : Bool}:
  match after:
    case True{}:
      insert_sorted(rest, m, N.goes_after(rest, m), {==}, N.mark.class(r), ea, hs)
    case False{}:
      and_i(U32.is_le(N.mark.class(m), N.mark.class(r)), sorted.from(rest, N.mark.class(r)), le_flip(N.mark.class(r), N.mark.class(m), ea), hs)

def insert_run(run: List<&2, N.Mark>, +m: N.Mark, +hs: {sorted.run(run) == True{} : Bool}) -> {sorted.run(N.insert(run, m)) == True{} : Bool}:
  match run:
    case Nil{}:
      {==}
    case +r <> +rest:
      insert_run.of(r, rest, m, N.goes_after(r <> rest, m), {==}, hs)

# What canonical order asks of a mark is met where the last class is no
# higher than its own, and at once where either is a starter.
def or_second(a: Bool, b: Bool, -c: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, Bool.or(b, c)) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, b, True{}, e) : {Bool.or(_, c) == True{} : Bool}
      {==}

def or_third(a: Bool, b: Bool, c: Bool, e: {c == True{} : Bool}) -> {Bool.or(a, Bool.or(b, c)) == True{} : Bool}:
  match a b:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      e

# A run in order above the last class is in canonical order after it.
def sorted_canonical(ms: List<&2, N.Mark>, +c: U32, +hs: {sorted.from(ms, c) == True{} : Bool}) -> {N.canonical.go(ms, c) == True{} : Bool}:
  match ms:
    case Nil{}:
      {==}
    case +m <> +rest:
      and_i(Bool.or(U32.is_eq(c, 0), Bool.or(U32.is_eq(N.mark.class(m), 0), U32.is_le(c, N.mark.class(m)))), N.canonical.go(rest, N.mark.class(m)),
        or_third(U32.is_eq(c, 0), U32.is_eq(N.mark.class(m), 0), U32.is_le(c, N.mark.class(m)), and_l(U32.is_le(c, N.mark.class(m)), sorted.from(rest, N.mark.class(m)), hs)),
        sorted_canonical(rest, N.mark.class(m), and_r(U32.is_le(c, N.mark.class(m)), sorted.from(rest, N.mark.class(m)), hs)))

# What follows a starter is read after class 0.
def after_starter(+m: N.Mark, o: List<&2, N.Mark>, +c: U32, +hm: {U32.is_eq(N.mark.class(m), 0) == True{} : Bool}, ho: {N.canonical.go(o, 0) == True{} : Bool}) -> {N.canonical.go(m <> o, c) == True{} : Bool}:
  and_i(Bool.or(U32.is_eq(c, 0), Bool.or(U32.is_eq(N.mark.class(m), 0), U32.is_le(c, N.mark.class(m)))), N.canonical.go(o, N.mark.class(m)),
    or_second(U32.is_eq(c, 0), U32.is_eq(N.mark.class(m), 0), U32.is_le(c, N.mark.class(m)), hm),
    (%Equal.sym(U32, N.mark.class(m), 0, EqL.u32_eq(N.mark.class(m), 0, hm)) : {N.canonical.go(o, _) == True{} : Bool}
     ho))

# A run in order, then a starter and what is canonical after it.
def joined_canonical(ms: List<&2, N.Mark>, +c: U32, +m: N.Mark, +o: List<&2, N.Mark>, +hs: {sorted.from(ms, c) == True{} : Bool}, +hm: {U32.is_eq(N.mark.class(m), 0) == True{} : Bool}, +ho: {N.canonical.go(o, 0) == True{} : Bool}) -> {N.canonical.go(List.append(&2, N.Mark, ms, m <> o), c) == True{} : Bool}:
  match ms:
    case Nil{}:
      after_starter(m, o, c, hm, ho)
    case +r <> +rest:
      and_i(Bool.or(U32.is_eq(c, 0), Bool.or(U32.is_eq(N.mark.class(r), 0), U32.is_le(c, N.mark.class(r)))), N.canonical.go(List.append(&2, N.Mark, rest, m <> o), N.mark.class(r)),
        or_third(U32.is_eq(c, 0), U32.is_eq(N.mark.class(r), 0), U32.is_le(c, N.mark.class(r)), and_l(U32.is_le(c, N.mark.class(r)), sorted.from(rest, N.mark.class(r)), hs)),
        joined_canonical(rest, N.mark.class(r), m, o, and_r(U32.is_le(c, N.mark.class(r)), sorted.from(rest, N.mark.class(r)), hs), hm, ho))

def run_canonical(run: List<&2, N.Mark>, +hr: {sorted.run(run) == True{} : Bool}) -> {N.canonical.go(run, 0) == True{} : Bool}:
  match run:
    case Nil{}:
      {==}
    case +r <> +rest:
      sorted_canonical(rest, N.mark.class(r), hr)

def run_joined(run: List<&2, N.Mark>, +m: N.Mark, +o: List<&2, N.Mark>, +hr: {sorted.run(run) == True{} : Bool}, +hm: {U32.is_eq(N.mark.class(m), 0) == True{} : Bool}, +ho: {N.canonical.go(o, 0) == True{} : Bool}) -> {N.canonical.go(List.append(&2, N.Mark, run, m <> o), 0) == True{} : Bool}:
  match run:
    case Nil{}:
      after_starter(m, o, 0, hm, ho)
    case +r <> +rest:
      joined_canonical(rest, N.mark.class(r), m, o, hr, hm, ho)

# What `order` returns is in canonical order: each run of marks is sorted
# as it closes, at a starter or at the end, and a starter resets the class.
def order_canonical(ms: List<&2, N.Mark>, +run: List<&2, N.Mark>, st: Bool, +est: {N.starts(ms) == st : Bool}, +hr: {sorted.run(run) == True{} : Bool}) -> {N.canonical.go(N.order.go(ms, run, st), 0) == True{} : Bool}:
  match ms st:
    case Nil{} _:
      run_canonical(run, hr)
    case +m <> +rest True{}:
      run_joined(run, m, N.order.go(rest, Nil{}, N.starts(rest)), hr, est, order_canonical(rest, Nil{}, N.starts(rest), {==}, {==}))
    case +m <> +rest False{}:
      order_canonical(rest, N.insert(run, m), N.starts(rest), {==}, insert_run(run, m, hr))

# `order` from the start, with no run yet: the law's statement.
def orders_by_class(+ms: List<&2, N.Mark>) -> {N.canonical.go(N.order(ms), 0) == True{} : Bool}:
  order_canonical(ms, Nil{}, N.starts(ms), {==}, {==})

# Order of code points
# --------------------

def lt_cmp(c: Cmp, e: {Cmp.is_lt(c) == True{} : Bool}) -> {c == LT{} : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({EQ{} == LT{} : Cmp}, S.false_true(e))
    case GT{}:
      Empty.absurd({GT{} == LT{} : Cmp}, S.false_true(e))

# Below one, not at or above it.
def lt_not_le.cmp(c: Cmp, e: {c == LT{} : Cmp}) -> {Cmp.is_le(SortL.cflip(c)) == False{} : Bool}:
  %Equal.sym(Cmp, c, LT{}, e) : {Cmp.is_le(SortL.cflip(_)) == False{} : Bool}
  {==}

def lt_not_le(x: U32, y: U32, e: {U32.is_lt(x, y) == True{} : Bool}) -> {U32.is_le(y, x) == False{} : Bool}:
  match x y:
    case U32{+a} U32{+b}:
      %Equal.sym(Cmp, Word.cmp(32n, b, a), SortL.cflip(Word.cmp(32n, a, b)), SortL.word_flip(32n, a, b)) : {Cmp.is_le(_) == False{} : Bool}
      lt_not_le.cmp(Word.cmp(32n, a, b), lt_cmp(Word.cmp(32n, a, b), e))

# Not below one is at or above it.
def not_lt_le.cmp(c: Cmp, e: {Cmp.is_lt(c) == False{} : Bool}) -> {Cmp.is_le(SortL.cflip(c)) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Cmp.is_le(SortL.cflip(LT{})) == True{} : Bool}, S.true_false(e))
    case EQ{}:
      {==}
    case GT{}:
      {==}

def not_lt_le(x: U32, y: U32, e: {U32.is_lt(x, y) == False{} : Bool}) -> {U32.is_le(y, x) == True{} : Bool}:
  match x y:
    case U32{+a} U32{+b}:
      %Equal.sym(Cmp, Word.cmp(32n, b, a), SortL.cflip(Word.cmp(32n, a, b)), SortL.word_flip(32n, a, b)) : {Cmp.is_le(_) == True{} : Bool}
      not_lt_le.cmp(Word.cmp(32n, a, b), e)

def lt_le.w(+a: Word(32n), +b: Word(32n), +d: Word(32n), c2: Cmp, +e2: {Word.cmp(32n, b, d) == c2 : Cmp}, +e1: {Word.cmp(32n, a, b) == LT{} : Cmp}, h2: {Cmp.is_le(c2) == True{} : Bool}) -> {Word.cmp(32n, a, d) == LT{} : Cmp}:
  match c2:
    case LT{}:
      SortL.word_lt(32n, a, b, d, e1, e2)
    case EQ{}:
      %S.word_eq(32n, b, d, e2) : {Word.cmp(32n, a, _) == LT{} : Cmp}
      e1
    case GT{}:
      Empty.absurd({Word.cmp(32n, a, d) == LT{} : Cmp}, S.false_true(h2))

# Below one no higher than another is below that.
def lt_le(x: U32, y: U32, z: U32, e1: {U32.is_lt(x, y) == True{} : Bool}, e2: {U32.is_le(y, z) == True{} : Bool}) -> {U32.is_lt(x, z) == True{} : Bool}:
  match x y z:
    case U32{+a} U32{+b} U32{+d}:
      %Equal.sym(Cmp, Word.cmp(32n, a, d), LT{}, lt_le.w(a, b, d, Word.cmp(32n, b, d), {==}, lt_cmp(Word.cmp(32n, a, b), e1), e2)) : {Cmp.is_lt(_) == True{} : Bool}
      {==}

def lt_lt(x: U32, y: U32, z: U32, e1: {U32.is_lt(x, y) == True{} : Bool}, e2: {U32.is_lt(y, z) == True{} : Bool}) -> {U32.is_lt(x, z) == True{} : Bool}:
  match x y z:
    case U32{+a} U32{+b} U32{+d}:
      %Equal.sym(Cmp, Word.cmp(32n, a, d), LT{}, SortL.word_lt(32n, a, b, d, lt_cmp(Word.cmp(32n, a, b), e1), lt_cmp(Word.cmp(32n, b, d), e2))) : {Cmp.is_lt(_) == True{} : Bool}
      {==}

# Classes
# -------

# Below every run of a table in order after `hi`, a character is in none.
def scan_none(rs: List<&2, U32>, +c: U32, +hi: U32, +hc: {U32.is_lt(c, hi) == True{} : Bool}, +ho: {N.runs.after(rs, hi) == True{} : Bool}) -> {N.class.scan(rs, c) == 0 : U32}:
  match rs:
    case Nil{}:
      {==}
    case +a <> +b <> +k <> +rest:
      +ha = and_l(U32.is_lt(hi, a), U32.is_le(a, b), and_l(Bool.and(U32.is_lt(hi, a), U32.is_le(a, b)), N.runs.after(rest, b), ho))
      +hab = and_r(U32.is_lt(hi, a), U32.is_le(a, b), and_l(Bool.and(U32.is_lt(hi, a), U32.is_le(a, b)), N.runs.after(rest, b), ho))
      +hca = lt_lt(c, hi, a, hc, ha)
      %Equal.sym(Bool, U32.is_le(a, c), False{}, lt_not_le(c, a, hca)) : {N.class.hit(Bool.and(_, U32.is_le(c, b)), k, N.class.scan(rest, c)) == 0 : U32}
      scan_none(rest, c, b, lt_le(c, a, b, hca, hab), and_r(Bool.and(U32.is_lt(hi, a), U32.is_le(a, b)), N.runs.after(rest, b), ho))
    case a <> b <> Nil{}:
      Empty.absurd({N.class.scan([a, b], c) == 0 : U32}, S.false_true(ho))
    case a <> Nil{}:
      Empty.absurd({N.class.scan([a], c) == 0 : U32}, S.false_true(ho))

def class_scan.at(+a: U32, +b: U32, +k: U32, +rest: List<&2, U32>, +c: U32, before: Bool, +eb: {U32.is_lt(c, a) == before : Bool}, within: Bool, +ew: {U32.is_le(c, b) == within : Bool}, +hab: {U32.is_le(a, b) == True{} : Bool}, +hr: {N.runs.after(rest, b) == True{} : Bool}, ih: {N.class.go(rest, c, N.run.after(rest, c), N.run.holds(rest, c)) == N.class.scan(rest, c) : U32}) -> {N.class.go(a <> b <> k <> rest, c, before, Bool.pick(Maybe<&2, U32>, within, Some{k}, None{})) == N.class.scan(a <> b <> k <> rest, c) : U32}:
  match before within:
    case True{} _:
      %Equal.sym(Bool, U32.is_le(a, c), False{}, lt_not_le(c, a, eb)) : {0 == N.class.hit(Bool.and(_, U32.is_le(c, b)), k, N.class.scan(rest, c)) : U32}
      Equal.sym(U32, N.class.scan(rest, c), 0, scan_none(rest, c, b, lt_le(c, a, b, eb, hab), hr))
    case False{} True{}:
      %Equal.sym(Bool, U32.is_le(a, c), True{}, not_lt_le(c, a, eb)) : {k == N.class.hit(Bool.and(_, U32.is_le(c, b)), k, N.class.scan(rest, c)) : U32}
      %Equal.sym(Bool, U32.is_le(c, b), True{}, ew) : {k == N.class.hit(Bool.and(True{}, _), k, N.class.scan(rest, c)) : U32}
      {==}
    case False{} False{}:
      %Equal.sym(Bool, U32.is_le(a, c), True{}, not_lt_le(c, a, eb)) : {N.class.go(rest, c, N.run.after(rest, c), N.run.holds(rest, c)) == N.class.hit(Bool.and(_, U32.is_le(c, b)), k, N.class.scan(rest, c)) : U32}
      %Equal.sym(Bool, U32.is_le(c, b), False{}, ew) : {N.class.go(rest, c, N.run.after(rest, c), N.run.holds(rest, c)) == N.class.hit(Bool.and(True{}, _), k, N.class.scan(rest, c)) : U32}
      ih

# Over a table in order, the lookup that stops at the first run past a
# character finds what the search of every run finds.
def class_scan(rs: List<&2, U32>, +c: U32, +hi: U32, +ho: {N.runs.after(rs, hi) == True{} : Bool}) -> {N.class.go(rs, c, N.run.after(rs, c), N.run.holds(rs, c)) == N.class.scan(rs, c) : U32}:
  match rs:
    case Nil{}:
      {==}
    case +a <> +b <> +k <> +rest:
      +hab = and_r(U32.is_lt(hi, a), U32.is_le(a, b), and_l(Bool.and(U32.is_lt(hi, a), U32.is_le(a, b)), N.runs.after(rest, b), ho))
      +hr = and_r(Bool.and(U32.is_lt(hi, a), U32.is_le(a, b)), N.runs.after(rest, b), ho)
      class_scan.at(a, b, k, rest, c, U32.is_lt(c, a), {==}, U32.is_le(c, b), {==}, hab, hr, class_scan(rest, c, b, hr))
    case a <> b <> Nil{}:
      Empty.absurd({N.class.go([a, b], c, N.run.after([a, b], c), N.run.holds([a, b], c)) == N.class.scan([a, b], c) : U32}, S.false_true(ho))
    case a <> Nil{}:
      Empty.absurd({N.class.go([a], c, N.run.after([a], c), N.run.holds([a], c)) == N.class.scan([a], c) : U32}, S.false_true(ho))

# The crate's table is in order: its runs apart and each ascending.
def classes_in_order() -> {N.runs.after(Tab.classes(), 0) == True{} : Bool}:
  {==}

def class_misses_nothing(+c: U32) -> {N.class(Tab.classes(), c) == N.class.scan(Tab.classes(), c) : U32}:
  class_scan(Tab.classes(), c, 0, classes_in_order())

# Separators are walls
# --------------------

# Over the crate's tables a `/` or a `.` decomposes to itself, is a
# starter, and is neither half of any pair, so each step of normal form C
# goes through it: decomposition and marking are maps, ordering closes its
# run of marks at a starter, and composition, meeting a starter nothing
# joins, puts out what came before whole and walks what comes after as if
# from the start.

# Lists of code points and of marks, joined and reversed.
def lapp_assoc(-A: Data, xs: List<&2, A>, -ys: List<&2, A>, -zs: List<&2, A>) -> {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Equal.sym(List<&2, A>, List.append(&2, A, List.append(&2, A, t, ys), zs), List.append(&2, A, t, List.append(&2, A, ys, zs)), lapp_assoc(A, t, ys, zs)) : {h <> _ == h <> List.append(&2, A, t, List.append(&2, A, ys, zs)) : List<&2, A>}
      {==}

def lrev_go_app(-A: Data, xs: List<&2, A>, acc: List<&2, A>, -tl: List<&2, A>) -> {List.reverse.go(&2, A, xs, List.append(&2, A, acc, tl)) == List.append(&2, A, List.reverse.go(&2, A, xs, acc), tl) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      lrev_go_app(A, t, h <> acc, tl)

def lrev_go_cat(-A: Data, xs: List<&2, A>, -ys: List<&2, A>, acc: List<&2, A>) -> {List.reverse.go(&2, A, List.append(&2, A, xs, ys), acc) == List.reverse.go(&2, A, ys, List.reverse.go(&2, A, xs, acc)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      lrev_go_cat(A, t, ys, h <> acc)

def lrev_cat(-A: Data, +xs: List<&2, A>, +ys: List<&2, A>) -> {List.reverse(&2, A, List.append(&2, A, xs, ys)) == List.append(&2, A, List.reverse(&2, A, ys), List.reverse(&2, A, xs)) : List<&2, A>}:
  Equal.trans(List<&2, A>, List.reverse(&2, A, List.append(&2, A, xs, ys)), List.reverse.go(&2, A, ys, List.reverse(&2, A, xs)), List.append(&2, A, List.reverse(&2, A, ys), List.reverse(&2, A, xs)),
    lrev_go_cat(A, xs, ys, Nil{}), lrev_go_app(A, ys, Nil{}, List.reverse(&2, A, xs)))

# `c` in front of what reverses `p`, and `p` reversed, then `c`.
def lrev_cons(+c: U32, +p: List<&2, U32>, +r: List<&2, U32>) -> {List.append(&2, U32, List.reverse(&2, U32, c <> p), r) == List.append(&2, U32, List.reverse(&2, U32, p), c <> r) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, List.append(&2, U32, List.reverse(&2, U32, c <> p), r), List.append(&2, U32, List.append(&2, U32, List.reverse(&2, U32, p), [c]), r), List.append(&2, U32, List.reverse(&2, U32, p), c <> r),
    Equal.cong(List<&2, U32>, List<&2, U32>, x => List.append(&2, U32, x, r), List.reverse(&2, U32, c <> p), List.append(&2, U32, List.reverse(&2, U32, p), [c]), lrev_go_app(U32, p, Nil{}, [c])),
    lapp_assoc(U32, List.reverse(&2, U32, p), [c], r))

# Decomposition, marking and ordering each go through a separator: it
# decomposes to itself, is a starter, and a starter closes a run of marks.
def decompose_wall(+es: List<&2, List<&2, U32>>, xs: List<&2, U32>, +c: U32, +ys: List<&2, U32>, hd: {N.decompose.one(es, c) == [c] : List<&2, U32>}) -> {N.decompose(es, List.append(&2, U32, xs, c <> ys)) == List.append(&2, U32, N.decompose(es, xs), c <> N.decompose(es, ys)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      %Equal.sym(List<&2, U32>, N.decompose.one(es, c), [c], hd) : {List.append(&2, U32, _, N.decompose(es, ys)) == c <> N.decompose(es, ys) : List<&2, U32>}
      {==}
    case +x <> rest:
      %Equal.sym(List<&2, U32>, N.decompose(es, List.append(&2, U32, rest, c <> ys)), List.append(&2, U32, N.decompose(es, rest), c <> N.decompose(es, ys)), decompose_wall(es, rest, c, ys, hd)) : {List.append(&2, U32, N.decompose.one(es, x), _) == List.append(&2, U32, List.append(&2, U32, N.decompose.one(es, x), N.decompose(es, rest)), c <> N.decompose(es, ys)) : List<&2, U32>}
      Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, N.decompose.one(es, x), N.decompose(es, rest)), c <> N.decompose(es, ys)), List.append(&2, U32, N.decompose.one(es, x), List.append(&2, U32, N.decompose(es, rest), c <> N.decompose(es, ys))), lapp_assoc(U32, N.decompose.one(es, x), N.decompose(es, rest), c <> N.decompose(es, ys)))

def marked_wall(+rs: List<&2, U32>, xs: List<&2, U32>, +c: U32, +ys: List<&2, U32>) -> {N.marked(rs, List.append(&2, U32, xs, c <> ys)) == List.append(&2, N.Mark, N.marked(rs, xs), N.Mark{c, N.class(rs, c)} <> N.marked(rs, ys)) : List<&2, N.Mark>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      %Equal.sym(List<&2, N.Mark>, N.marked(rs, List.append(&2, U32, rest, c <> ys)), List.append(&2, N.Mark, N.marked(rs, rest), N.Mark{c, N.class(rs, c)} <> N.marked(rs, ys)), marked_wall(rs, rest, c, ys)) : {N.Mark{x, N.class(rs, x)} <> _ == N.Mark{x, N.class(rs, x)} <> List.append(&2, N.Mark, N.marked(rs, rest), N.Mark{c, N.class(rs, c)} <> N.marked(rs, ys)) : List<&2, N.Mark>}
      {==}

def starts_cat(xs: List<&2, N.Mark>, -c: U32, -ys: List<&2, N.Mark>) -> {N.starts(List.append(&2, N.Mark, xs, N.Mark{c, 0} <> ys)) == N.starts(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case m <> rest:
      {==}

def order_wall(xs: List<&2, N.Mark>, +run: List<&2, N.Mark>, st: Bool, +est: {N.starts(xs) == st : Bool}, +c: U32, +ys: List<&2, N.Mark>) -> {N.order.go(List.append(&2, N.Mark, xs, N.Mark{c, 0} <> ys), run, st) == List.append(&2, N.Mark, N.order.go(xs, run, st), N.Mark{c, 0} <> N.order(ys)) : List<&2, N.Mark>}:
  match xs st:
    case Nil{} True{}:
      {==}
    case Nil{} False{}:
      Empty.absurd({N.order.go(N.Mark{c, 0} <> ys, run, False{}) == List.append(&2, N.Mark, run, N.Mark{c, 0} <> N.order(ys)) : List<&2, N.Mark>}, S.true_false(est))
    case +m <> +rest True{}:
      %Equal.sym(Bool, N.starts(List.append(&2, N.Mark, rest, N.Mark{c, 0} <> ys)), N.starts(rest), starts_cat(rest, c, ys)) : {List.append(&2, N.Mark, run, m <> N.order.go(List.append(&2, N.Mark, rest, N.Mark{c, 0} <> ys), Nil{}, _)) == List.append(&2, N.Mark, List.append(&2, N.Mark, run, m <> N.order.go(rest, Nil{}, N.starts(rest))), N.Mark{c, 0} <> N.order(ys)) : List<&2, N.Mark>}
      %Equal.sym(List<&2, N.Mark>, N.order.go(List.append(&2, N.Mark, rest, N.Mark{c, 0} <> ys), Nil{}, N.starts(rest)), List.append(&2, N.Mark, N.order.go(rest, Nil{}, N.starts(rest)), N.Mark{c, 0} <> N.order(ys)), order_wall(rest, Nil{}, N.starts(rest), {==}, c, ys)) : {List.append(&2, N.Mark, run, m <> _) == List.append(&2, N.Mark, List.append(&2, N.Mark, run, m <> N.order.go(rest, Nil{}, N.starts(rest))), N.Mark{c, 0} <> N.order(ys)) : List<&2, N.Mark>}
      Equal.sym(List<&2, N.Mark>, List.append(&2, N.Mark, List.append(&2, N.Mark, run, m <> N.order.go(rest, Nil{}, N.starts(rest))), N.Mark{c, 0} <> N.order(ys)), List.append(&2, N.Mark, run, List.append(&2, N.Mark, m <> N.order.go(rest, Nil{}, N.starts(rest)), N.Mark{c, 0} <> N.order(ys))), lapp_assoc(N.Mark, run, m <> N.order.go(rest, Nil{}, N.starts(rest)), N.Mark{c, 0} <> N.order(ys)))
    case +m <> +rest False{}:
      %Equal.sym(Bool, N.starts(List.append(&2, N.Mark, rest, N.Mark{c, 0} <> ys)), N.starts(rest), starts_cat(rest, c, ys)) : {N.order.go(List.append(&2, N.Mark, rest, N.Mark{c, 0} <> ys), N.insert(run, m), _) == List.append(&2, N.Mark, N.order.go(rest, N.insert(run, m), N.starts(rest)), N.Mark{c, 0} <> N.order(ys)) : List<&2, N.Mark>}
      order_wall(rest, N.insert(run, m), N.starts(rest), {==}, c, ys)

def order_cat(+xs: List<&2, N.Mark>, +c: U32, +ys: List<&2, N.Mark>) -> {N.order(List.append(&2, N.Mark, xs, N.Mark{c, 0} <> ys)) == List.append(&2, N.Mark, N.order(xs), N.Mark{c, 0} <> N.order(ys)) : List<&2, N.Mark>}:
  %Equal.sym(Bool, N.starts(List.append(&2, N.Mark, xs, N.Mark{c, 0} <> ys)), N.starts(xs), starts_cat(xs, c, ys)) : {N.order.go(List.append(&2, N.Mark, xs, N.Mark{c, 0} <> ys), Nil{}, _) == List.append(&2, N.Mark, N.order(xs), N.Mark{c, 0} <> N.order(ys)) : List<&2, N.Mark>}
  order_wall(xs, Nil{}, N.starts(xs), {==}, c, ys)

# Composition. A walk with more already out behind it is the same walk,
# step for step: `shift` puts `q` behind what a walk has put out.
def shift(w: N.Walk, +q: List<&2, U32>) -> N.Walk:
  match w:
    case N.Walk{o, s, l, h}:
      N.Walk{List.append(&2, U32, o, q), s, l, h}

def lone_shift(b: Bool, +o: List<&2, U32>, +q: List<&2, U32>, +c: U32) -> {Bool.pick(N.Walk, b, N.Walk{List.append(&2, U32, o, q), Some{c}, None{}, Nil{}}, N.Walk{c <> List.append(&2, U32, o, q), None{}, None{}, Nil{}}) == shift(Bool.pick(N.Walk, b, N.Walk{o, Some{c}, None{}, Nil{}}, N.Walk{c <> o, None{}, None{}, Nil{}}), q) : N.Walk}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def kept_shift(b: Bool, +o: List<&2, U32>, +q: List<&2, U32>, +s: U32, +h: List<&2, U32>, +c: U32, +k: U32) -> {Bool.pick(N.Walk, b, N.Walk{List.append(&2, U32, h, s <> List.append(&2, U32, o, q)), Some{c}, None{}, Nil{}}, N.Walk{List.append(&2, U32, o, q), Some{s}, Some{k}, c <> h}) == shift(Bool.pick(N.Walk, b, N.Walk{List.append(&2, U32, h, s <> o), Some{c}, None{}, Nil{}}, N.Walk{o, Some{s}, Some{k}, c <> h}), q) : N.Walk}:
  match b:
    case True{}:
      %Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, h, s <> o), q), List.append(&2, U32, h, s <> List.append(&2, U32, o, q)), lapp_assoc(U32, h, s <> o, q)) : {N.Walk{List.append(&2, U32, h, s <> List.append(&2, U32, o, q)), Some{c}, None{}, Nil{}} == N.Walk{_, Some{c}, None{}, Nil{}} : N.Walk}
      {==}
    case False{}:
      {==}

def joined_shift(j: Maybe<&2, U32>, +o: List<&2, U32>, +q: List<&2, U32>, +last: Maybe<&2, U32>, +h: List<&2, U32>, +s: U32, +c: U32, +k: U32) -> {N.step.joined(List.append(&2, U32, o, q), last, h, j, s, c, k) == shift(N.step.joined(o, last, h, j, s, c, k), q) : N.Walk}:
  match j:
    case Some{r}:
      {==}
    case None{}:
      kept_shift(U32.is_eq(k, 0), o, q, s, h, c, k)

def behind_shift(+ps: List<&2, U32>, +o: List<&2, U32>, +q: List<&2, U32>, +s: U32, +l: U32, +h: List<&2, U32>, +c: U32, +k: U32, b: Bool) -> {N.step.behind(ps, List.append(&2, U32, o, q), s, l, h, c, k, b) == shift(N.step.behind(ps, o, s, l, h, c, k, b), q) : N.Walk}:
  match b:
    case True{}:
      joined_shift(N.compose(ps, s, c), o, q, Some{l}, h, s, c, k)
    case False{}:
      kept_shift(U32.is_eq(k, 0), o, q, s, h, c, k)

def at_shift(+ps: List<&2, U32>, +o: List<&2, U32>, +q: List<&2, U32>, +s: U32, last: Maybe<&2, U32>, +h: List<&2, U32>, +c: U32, +k: U32) -> {N.step.at(ps, List.append(&2, U32, o, q), s, last, h, c, k) == shift(N.step.at(ps, o, s, last, h, c, k), q) : N.Walk}:
  match last:
    case None{}:
      joined_shift(N.compose(ps, s, c), o, q, None{}, h, s, c, k)
    case Some{+l}:
      behind_shift(ps, o, q, s, l, h, c, k, U32.is_lt(l, k))

def step_shift(+ps: List<&2, U32>, w: N.Walk, m: N.Mark, +q: List<&2, U32>) -> {N.step(ps, shift(w, q), m) == shift(N.step(ps, w, m), q) : N.Walk}:
  match w m:
    case N.Walk{+o, None{}, l, h} N.Mark{+c, +k}:
      lone_shift(U32.is_eq(k, 0), o, q, c)
    case N.Walk{+o, Some{+s}, +l, +h} N.Mark{+c, +k}:
      at_shift(ps, o, q, s, l, h, c, k)

def walk_shift(+ps: List<&2, U32>, ms: List<&2, N.Mark>, +w: N.Walk, +q: List<&2, U32>) -> {N.walk.go(ps, ms, shift(w, q)) == shift(N.walk.go(ps, ms, w), q) : N.Walk}:
  match ms:
    case Nil{}:
      {==}
    case +m <> rest:
      Equal.trans(N.Walk, N.walk.go(ps, rest, N.step(ps, shift(w, q), m)), N.walk.go(ps, rest, shift(N.step(ps, w, m), q)), shift(N.walk.go(ps, rest, N.step(ps, w, m)), q),
        Equal.cong(N.Walk, N.Walk, x => N.walk.go(ps, rest, x), N.step(ps, shift(w, q), m), shift(N.step(ps, w, m), q), step_shift(ps, w, m, q)),
        walk_shift(ps, rest, N.step(ps, w, m), q))

def rev_behind(+h: List<&2, U32>, +p: List<&2, U32>, +q: List<&2, U32>) -> {List.reverse(&2, U32, List.append(&2, U32, h, List.append(&2, U32, p, q))) == List.append(&2, U32, List.reverse(&2, U32, q), List.reverse(&2, U32, List.append(&2, U32, h, p))) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, List.append(&2, U32, h, List.append(&2, U32, p, q)), List.append(&2, U32, List.append(&2, U32, h, p), q), Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, h, p), q), List.append(&2, U32, h, List.append(&2, U32, p, q)), lapp_assoc(U32, h, p, q))) : {List.reverse(&2, U32, _) == List.append(&2, U32, List.reverse(&2, U32, q), List.reverse(&2, U32, List.append(&2, U32, h, p))) : List<&2, U32>}
  lrev_cat(U32, List.append(&2, U32, h, p), q)

def done_shift(w: N.Walk, +q: List<&2, U32>) -> {N.walk.done(shift(w, q)) == List.append(&2, U32, List.reverse(&2, U32, q), N.walk.done(w)) : List<&2, U32>}:
  match w:
    case N.Walk{+o, None{}, l, +h}:
      rev_behind(h, o, q)
    case N.Walk{+o, Some{+s}, l, +h}:
      rev_behind(h, s <> o, q)

# A step blocked from composing is one that keeps what came.
def behind_blocked(+ps: List<&2, U32>, +o: List<&2, U32>, +s: U32, +l: U32, +h: List<&2, U32>, +x: U32, +k: U32, b: Bool, hc: {N.compose(ps, s, x) == None{} : Maybe<&2, U32>}) -> {N.step.behind(ps, o, s, l, h, x, k, b) == N.step.kept(o, s, h, x, k) : N.Walk}:
  match b:
    case True{}:
      %Equal.sym(Maybe<&2, U32>, N.compose(ps, s, x), None{}, hc) : {N.step.joined(o, Some{l}, h, _, s, x, k) == N.step.kept(o, s, h, x, k) : N.Walk}
      {==}
    case False{}:
      {==}

def at_blocked(+ps: List<&2, U32>, +o: List<&2, U32>, +s: U32, last: Maybe<&2, U32>, +h: List<&2, U32>, +x: U32, +k: U32, hc: {N.compose(ps, s, x) == None{} : Maybe<&2, U32>}) -> {N.step.at(ps, o, s, last, h, x, k) == N.step.kept(o, s, h, x, k) : N.Walk}:
  match last:
    case None{}:
      %Equal.sym(Maybe<&2, U32>, N.compose(ps, s, x), None{}, hc) : {N.step.joined(o, None{}, h, _, s, x, k) == N.step.kept(o, s, h, x, k) : N.Walk}
      {==}
    case Some{+l}:
      behind_blocked(ps, o, s, l, h, x, k, U32.is_lt(l, k), hc)

def and_false(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def and_ff(a: Bool, b: Bool, -d: Bool, e: {b == False{} : Bool}) -> {Bool.and(a, Bool.and(b, d)) == False{} : Bool}:
  %Equal.sym(Bool, b, False{}, e) : {Bool.and(a, Bool.and(_, d)) == False{} : Bool}
  and_false(a)

def compose_of_none(+ps: List<&2, U32>, +a: U32, +b: U32, lv: Bool, elv: {lv == False{} : Bool}, lvt: Bool, elvt: {lvt == False{} : Bool}, hp: {N.pair.go(ps, a, b, N.pair.cmp(ps, a, b)) == None{} : Maybe<&2, U32>}) -> {N.compose.of(ps, a, b, lv, lvt) == None{} : Maybe<&2, U32>}:
  %Equal.sym(Bool, lv, False{}, elv) : {N.compose.of(ps, a, b, _, lvt) == None{} : Maybe<&2, U32>}
  %Equal.sym(Bool, lvt, False{}, elvt) : {N.compose.of(ps, a, b, False{}, _) == None{} : Maybe<&2, U32>}
  hp

# What joins nothing after it: a character below the jamo and the
# syllables, and below the first character of every pair.
def firsts.above(ps: List<&2, U32>, +c: U32) -> Bool:
  match ps:
    case x <> y <> z <> rest:
      U32.is_lt(c, x)
    case _:
      True{}

def pair_below(ps: List<&2, U32>, +a: U32, +b: U32, hf: {firsts.above(ps, a) == True{} : Bool}) -> {N.pair.go(ps, a, b, N.pair.cmp(ps, a, b)) == None{} : Maybe<&2, U32>}:
  match ps:
    case Nil{}:
      {==}
    case x <> Nil{}:
      {==}
    case x <> y <> Nil{}:
      {==}
    case +x <> +y <> z <> rest:
      %Equal.sym(Cmp, U32.cmp(a, x), LT{}, lt_cmp(U32.cmp(a, x), hf)) : {N.pair.go(x <> y <> z <> rest, a, b, N.lex(_, U32.cmp(b, y))) == None{} : Maybe<&2, U32>}
      {==}

def lv_left(+c: U32, +x: U32, e1: {U32.is_ge(c, 4352) == False{} : Bool}) -> {N.hangul.lv(c, x) == False{} : Bool}:
  %Equal.sym(Bool, U32.is_ge(c, 4352), False{}, e1) : {Bool.and(Bool.and(_, U32.is_le(c, 4370)), Bool.and(U32.is_ge(x, 4449), U32.is_le(x, 4469))) == False{} : Bool}
  {==}

def lvt_left(+c: U32, +x: U32, e2: {U32.is_ge(c, 44032) == False{} : Bool}) -> {N.hangul.lvt(c, x) == False{} : Bool}:
  %Equal.sym(Bool, U32.is_ge(c, 44032), False{}, e2) : {Bool.and(Bool.and(Bool.and(_, U32.is_le(c, 55203)), U32.is_eq(((c - 44032 : U32) % 28 : U32), 0)), Bool.and(U32.is_ge(x, 4520), U32.is_le(x, 4546))) == False{} : Bool}
  {==}

def right_none(+ps: List<&2, U32>, +c: U32, +x: U32, hf: {firsts.above(ps, c) == True{} : Bool}, e1: {U32.is_ge(c, 4352) == False{} : Bool}, e2: {U32.is_ge(c, 44032) == False{} : Bool}) -> {N.compose(ps, c, x) == None{} : Maybe<&2, U32>}:
  compose_of_none(ps, c, x, N.hangul.lv(c, x), lv_left(c, x, e1), N.hangul.lvt(c, x), lvt_left(c, x, e2), pair_below(ps, c, x, hf))

# Behind a starter nothing joins, the marks that come wait as they would
# have gone out with no starter at all, and the next starter puts them
# out after it.
def lone_wall.at(b: Bool, +ps: List<&2, U32>, +rest: List<&2, N.Mark>, +p: List<&2, U32>, +c: U32, +h: List<&2, U32>, +x: U32, +k: U32, ih: {N.walk.done(N.walk.go(ps, rest, N.Walk{p, Some{c}, Some{k}, x <> h})) == List.append(&2, U32, List.reverse(&2, U32, p), c <> N.walk.done(N.walk.go(ps, rest, N.Walk{x <> h, None{}, None{}, Nil{}}))) : List<&2, U32>}) -> {N.walk.done(N.walk.go(ps, rest, Bool.pick(N.Walk, b, N.Walk{List.append(&2, U32, h, c <> p), Some{x}, None{}, Nil{}}, N.Walk{p, Some{c}, Some{k}, x <> h}))) == List.append(&2, U32, List.reverse(&2, U32, p), c <> N.walk.done(N.walk.go(ps, rest, Bool.pick(N.Walk, b, N.Walk{h, Some{x}, None{}, Nil{}}, N.Walk{x <> h, None{}, None{}, Nil{}})))) : List<&2, U32>}:
  match b:
    case True{}:
      +w : N.Walk = N.Walk{h, Some{x}, None{}, Nil{}}
      %Equal.sym(N.Walk, N.walk.go(ps, rest, shift(w, c <> p)), shift(N.walk.go(ps, rest, w), c <> p), walk_shift(ps, rest, w, c <> p)) : {N.walk.done(_) == List.append(&2, U32, List.reverse(&2, U32, p), c <> N.walk.done(N.walk.go(ps, rest, w))) : List<&2, U32>}
      Equal.trans(List<&2, U32>, N.walk.done(shift(N.walk.go(ps, rest, w), c <> p)), List.append(&2, U32, List.reverse(&2, U32, c <> p), N.walk.done(N.walk.go(ps, rest, w))), List.append(&2, U32, List.reverse(&2, U32, p), c <> N.walk.done(N.walk.go(ps, rest, w))),
        done_shift(N.walk.go(ps, rest, w), c <> p), lrev_cons(c, p, N.walk.done(N.walk.go(ps, rest, w))))
    case False{}:
      ih

def lone_wall(+ps: List<&2, U32>, ys: List<&2, N.Mark>, +p: List<&2, U32>, +c: U32, +l: Maybe<&2, U32>, +h: List<&2, U32>, +hf: {firsts.above(ps, c) == True{} : Bool}, +e1: {U32.is_ge(c, 4352) == False{} : Bool}, +e2: {U32.is_ge(c, 44032) == False{} : Bool}) -> {N.walk.done(N.walk.go(ps, ys, N.Walk{p, Some{c}, l, h})) == List.append(&2, U32, List.reverse(&2, U32, p), c <> N.walk.done(N.walk.go(ps, ys, N.Walk{h, None{}, None{}, Nil{}}))) : List<&2, U32>}:
  match ys:
    case Nil{}:
      Equal.trans(List<&2, U32>, List.reverse(&2, U32, List.append(&2, U32, h, c <> p)), List.append(&2, U32, List.reverse(&2, U32, c <> p), List.reverse(&2, U32, h)), List.append(&2, U32, List.reverse(&2, U32, p), c <> List.reverse(&2, U32, h)),
        lrev_cat(U32, h, c <> p), lrev_cons(c, p, List.reverse(&2, U32, h)))
    case N.Mark{+x, +k} <> +rest:
      %Equal.sym(N.Walk, N.step.at(ps, p, c, l, h, x, k), N.step.kept(p, c, h, x, k), at_blocked(ps, p, c, l, h, x, k, right_none(ps, c, x, hf, e1, e2))) : {N.walk.done(N.walk.go(ps, rest, _)) == List.append(&2, U32, List.reverse(&2, U32, p), c <> N.walk.done(N.walk.go(ps, rest, N.step.lone(h, x, k)))) : List<&2, U32>}
      lone_wall.at(U32.is_eq(k, 0), ps, rest, p, c, h, x, k, lone_wall(ps, rest, p, c, Some{k}, x <> h, hf, e1, e2))

# A walk with no starter has nothing waiting.
def ok(w: N.Walk) -> Bool:
  match w:
    case N.Walk{o, None{}, l, h}:
      List.is_empty(&2, U32, h)
    case N.Walk{o, Some{s}, l, h}:
      True{}

def kept_ok(b: Bool, +o: List<&2, U32>, +s: U32, +h: List<&2, U32>, +c: U32, +k: U32) -> {ok(Bool.pick(N.Walk, b, N.Walk{List.append(&2, U32, h, s <> o), Some{c}, None{}, Nil{}}, N.Walk{o, Some{s}, Some{k}, c <> h})) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def joined_ok(j: Maybe<&2, U32>, +o: List<&2, U32>, +last: Maybe<&2, U32>, +h: List<&2, U32>, +s: U32, +c: U32, +k: U32) -> {ok(N.step.joined(o, last, h, j, s, c, k)) == True{} : Bool}:
  match j:
    case Some{r}:
      {==}
    case None{}:
      kept_ok(U32.is_eq(k, 0), o, s, h, c, k)

def behind_ok(+ps: List<&2, U32>, +o: List<&2, U32>, +s: U32, +l: U32, +h: List<&2, U32>, +c: U32, +k: U32, b: Bool) -> {ok(N.step.behind(ps, o, s, l, h, c, k, b)) == True{} : Bool}:
  match b:
    case True{}:
      joined_ok(N.compose(ps, s, c), o, Some{l}, h, s, c, k)
    case False{}:
      kept_ok(U32.is_eq(k, 0), o, s, h, c, k)

def at_ok(+ps: List<&2, U32>, +o: List<&2, U32>, +s: U32, last: Maybe<&2, U32>, +h: List<&2, U32>, +c: U32, +k: U32) -> {ok(N.step.at(ps, o, s, last, h, c, k)) == True{} : Bool}:
  match last:
    case None{}:
      joined_ok(N.compose(ps, s, c), o, None{}, h, s, c, k)
    case Some{+l}:
      behind_ok(ps, o, s, l, h, c, k, U32.is_lt(l, k))

def lone_ok(b: Bool, +o: List<&2, U32>, +c: U32) -> {ok(Bool.pick(N.Walk, b, N.Walk{o, Some{c}, None{}, Nil{}}, N.Walk{c <> o, None{}, None{}, Nil{}})) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def step_ok(+ps: List<&2, U32>, w: N.Walk, m: N.Mark) -> {ok(N.step(ps, w, m)) == True{} : Bool}:
  match w m:
    case N.Walk{+o, None{}, l, h} N.Mark{+c, +k}:
      lone_ok(U32.is_eq(k, 0), o, c)
    case N.Walk{+o, Some{+s}, +last, +h} N.Mark{+c, +k}:
      at_ok(ps, o, s, last, h, c, k)

def go_ok(+ps: List<&2, U32>, ms: List<&2, N.Mark>, +w: N.Walk, hw: {ok(w) == True{} : Bool}) -> {ok(N.walk.go(ps, ms, w)) == True{} : Bool}:
  match ms:
    case Nil{}:
      hw
    case +m <> rest:
      go_ok(ps, rest, N.step(ps, w, m), step_ok(ps, w, m))

def walk_cat(+ps: List<&2, U32>, xs: List<&2, N.Mark>, +zs: List<&2, N.Mark>, +w: N.Walk) -> {N.walk.go(ps, List.append(&2, N.Mark, xs, zs), w) == N.walk.go(ps, zs, N.walk.go(ps, xs, w)) : N.Walk}:
  match xs:
    case Nil{}:
      {==}
    case +m <> rest:
      walk_cat(ps, rest, zs, N.step(ps, w, m))

# A starter nothing composes with, on either side, closes what came
# before it whole and opens what comes after as a walk of its own.
def wall_at.lone(+ps: List<&2, U32>, +o: List<&2, U32>, +l: Maybe<&2, U32>, h: List<&2, U32>, +c: U32, hw: {List.is_empty(&2, U32, h) == True{} : Bool}, +ys: List<&2, N.Mark>, +hf: {firsts.above(ps, c) == True{} : Bool}, +e1: {U32.is_ge(c, 4352) == False{} : Bool}, +e2: {U32.is_ge(c, 44032) == False{} : Bool}) -> {N.walk.done(N.walk.go(ps, ys, N.step(ps, N.Walk{o, None{}, l, h}, N.Mark{c, 0}))) == List.append(&2, U32, N.walk.done(N.Walk{o, None{}, l, h}), c <> N.recompose(ps, ys)) : List<&2, U32>}:
  match h:
    case Nil{}:
      lone_wall(ps, ys, o, c, None{}, Nil{}, hf, e1, e2)
    case y <> t:
      Empty.absurd({N.walk.done(N.walk.go(ps, ys, N.step(ps, N.Walk{o, None{}, l, y <> t}, N.Mark{c, 0}))) == List.append(&2, U32, N.walk.done(N.Walk{o, None{}, l, y <> t}), c <> N.recompose(ps, ys)) : List<&2, U32>}, S.false_true(hw))

def wall_at(+ps: List<&2, U32>, w: N.Walk, +c: U32, hw: {ok(w) == True{} : Bool}, +ys: List<&2, N.Mark>, hl: @s: U32 -> {N.compose(ps, s, c) == None{} : Maybe<&2, U32>}, +hf: {firsts.above(ps, c) == True{} : Bool}, +e1: {U32.is_ge(c, 4352) == False{} : Bool}, +e2: {U32.is_ge(c, 44032) == False{} : Bool}) -> {N.walk.done(N.walk.go(ps, ys, N.step(ps, w, N.Mark{c, 0}))) == List.append(&2, U32, N.walk.done(w), c <> N.recompose(ps, ys)) : List<&2, U32>}:
  match w:
    case N.Walk{+o, None{}, +l, +h}:
      wall_at.lone(ps, o, l, h, c, hw, ys, hf, e1, e2)
    case N.Walk{+o, Some{+s}, +l, +h}:
      %Equal.sym(N.Walk, N.step.at(ps, o, s, l, h, c, 0), N.step.kept(o, s, h, c, 0), at_blocked(ps, o, s, l, h, c, 0, hl(s))) : {N.walk.done(N.walk.go(ps, ys, _)) == List.append(&2, U32, N.walk.done(N.Walk{o, Some{s}, l, h}), c <> N.recompose(ps, ys)) : List<&2, U32>}
      lone_wall(ps, ys, List.append(&2, U32, h, s <> o), c, None{}, Nil{}, hf, e1, e2)

def recompose_wall(+ps: List<&2, U32>, +xs: List<&2, N.Mark>, +c: U32, +ys: List<&2, N.Mark>, hl: @s: U32 -> {N.compose(ps, s, c) == None{} : Maybe<&2, U32>}, +hf: {firsts.above(ps, c) == True{} : Bool}, +e1: {U32.is_ge(c, 4352) == False{} : Bool}, +e2: {U32.is_ge(c, 44032) == False{} : Bool}) -> {N.recompose(ps, List.append(&2, N.Mark, xs, N.Mark{c, 0} <> ys)) == List.append(&2, U32, N.recompose(ps, xs), c <> N.recompose(ps, ys)) : List<&2, U32>}:
  +w0 : N.Walk = N.Walk{Nil{}, None{}, None{}, Nil{}}
  %Equal.sym(N.Walk, N.walk.go(ps, List.append(&2, N.Mark, xs, N.Mark{c, 0} <> ys), w0), N.walk.go(ps, N.Mark{c, 0} <> ys, N.walk.go(ps, xs, w0)), walk_cat(ps, xs, N.Mark{c, 0} <> ys, w0)) : {N.walk.done(_) == List.append(&2, U32, N.recompose(ps, xs), c <> N.recompose(ps, ys)) : List<&2, U32>}
  wall_at(ps, N.walk.go(ps, xs, w0), c, go_ok(ps, xs, w0, {==}), ys, hl, hf, e1, e2)

# The whole of normal form C's algorithm, over any tables where `c`
# decomposes to itself, is a starter, and composes with nothing.
def points_wall(+rs: List<&2, U32>, +es: List<&2, List<&2, U32>>, +ps: List<&2, U32>, +xs: List<&2, U32>, +c: U32, +ys: List<&2, U32>, hd: {N.decompose.one(es, c) == [c] : List<&2, U32>}, hk: {N.class(rs, c) == 0 : U32}, hl: @s: U32 -> {N.compose(ps, s, c) == None{} : Maybe<&2, U32>}, +hf: {firsts.above(ps, c) == True{} : Bool}, +e1: {U32.is_ge(c, 4352) == False{} : Bool}, +e2: {U32.is_ge(c, 44032) == False{} : Bool}) -> {N.nfc.points(N.Tabs{rs, es, ps}, List.append(&2, U32, xs, c <> ys)) == List.append(&2, U32, N.nfc.points(N.Tabs{rs, es, ps}, xs), c <> N.nfc.points(N.Tabs{rs, es, ps}, ys)) : List<&2, U32>}:
  +dx : List<&2, U32> = N.decompose(es, xs)
  +dy : List<&2, U32> = N.decompose(es, ys)
  %Equal.sym(List<&2, U32>, N.decompose(es, List.append(&2, U32, xs, c <> ys)), List.append(&2, U32, dx, c <> dy), decompose_wall(es, xs, c, ys, hd)) : {N.recompose(ps, N.order(N.marked(rs, _))) == List.append(&2, U32, N.nfc.points(N.Tabs{rs, es, ps}, xs), c <> N.nfc.points(N.Tabs{rs, es, ps}, ys)) : List<&2, U32>}
  %Equal.sym(List<&2, N.Mark>, N.marked(rs, List.append(&2, U32, dx, c <> dy)), List.append(&2, N.Mark, N.marked(rs, dx), N.Mark{c, N.class(rs, c)} <> N.marked(rs, dy)), marked_wall(rs, dx, c, dy)) : {N.recompose(ps, N.order(_)) == List.append(&2, U32, N.nfc.points(N.Tabs{rs, es, ps}, xs), c <> N.nfc.points(N.Tabs{rs, es, ps}, ys)) : List<&2, U32>}
  %Equal.sym(U32, N.class(rs, c), 0, hk) : {N.recompose(ps, N.order(List.append(&2, N.Mark, N.marked(rs, dx), N.Mark{c, _} <> N.marked(rs, dy)))) == List.append(&2, U32, N.nfc.points(N.Tabs{rs, es, ps}, xs), c <> N.nfc.points(N.Tabs{rs, es, ps}, ys)) : List<&2, U32>}
  %Equal.sym(List<&2, N.Mark>, N.order(List.append(&2, N.Mark, N.marked(rs, dx), N.Mark{c, 0} <> N.marked(rs, dy))), List.append(&2, N.Mark, N.order(N.marked(rs, dx)), N.Mark{c, 0} <> N.order(N.marked(rs, dy))), order_cat(N.marked(rs, dx), c, N.marked(rs, dy))) : {N.recompose(ps, _) == List.append(&2, U32, N.nfc.points(N.Tabs{rs, es, ps}, xs), c <> N.nfc.points(N.Tabs{rs, es, ps}, ys)) : List<&2, U32>}
  recompose_wall(ps, N.order(N.marked(rs, dx)), c, N.order(N.marked(rs, dy)), hl, hf, e1, e2)

# The crate's tables: no pair has `/` or `.` as the character that joins.
def seconds.miss(ps: List<&2, U32>, +b: U32) -> Bool:
  match ps:
    case x <> y <> z <> rest:
      Bool.and(Bool.not(U32.is_eq(b, y)), seconds.miss(rest, b))
    case _:
      True{}

def lex_eq(f: Cmp, -t: Cmp, e: {N.lex(f, t) == EQ{} : Cmp}) -> {t == EQ{} : Cmp}:
  match f:
    case LT{}:
      Empty.absurd({t == EQ{} : Cmp}, EqL.lt_eq(e))
    case EQ{}:
      e
    case GT{}:
      Empty.absurd({t == EQ{} : Cmp}, EqL.gt_eq(e))

def pair_none(ps: List<&2, U32>, +a: U32, +b: U32, o: Cmp, +eo: {N.pair.cmp(ps, a, b) == o : Cmp}, +h: {seconds.miss(ps, b) == True{} : Bool}) -> {N.pair.go(ps, a, b, o) == None{} : Maybe<&2, U32>}:
  match ps o:
    case Nil{} LT{}:
      {==}
    case x <> Nil{} LT{}:
      {==}
    case x <> y <> Nil{} LT{}:
      {==}
    case x <> y <> z <> rest LT{}:
      {==}
    case x <> y <> z <> rest EQ{}:
      +same = lex_eq(U32.cmp(a, x), U32.cmp(b, y), eo)
      +met = Equal.cong(Cmp, Bool, t => Bool.and(Bool.not(Cmp.is_eq(t)), seconds.miss(rest, b)), EQ{}, U32.cmp(b, y), Equal.sym(Cmp, U32.cmp(b, y), EQ{}, same))
      Empty.absurd({N.pair.go(x <> y <> z <> rest, a, b, EQ{}) == None{} : Maybe<&2, U32>}, S.false_true(Equal.trans(Bool, False{}, Bool.and(Bool.not(Cmp.is_eq(U32.cmp(b, y))), seconds.miss(rest, b)), True{}, met, h)))
    case x <> y <> z <> +rest GT{}:
      pair_none(rest, a, b, N.pair.cmp(rest, a, b), {==}, and_r(Bool.not(U32.is_eq(b, y)), seconds.miss(rest, b), h))
    case Nil{} EQ{}:
      {==}
    case Nil{} GT{}:
      {==}
    case x <> Nil{} EQ{}:
      {==}
    case x <> Nil{} GT{}:
      {==}
    case x <> y <> Nil{} EQ{}:
      {==}
    case x <> y <> Nil{} GT{}:
      {==}

# A character the crate's pairs never join, below the jamo, joins nothing
# before it.
def tables_miss(+c: U32, hm: {seconds.miss(Tab.pairs(), c) == True{} : Bool}, e1: {U32.is_ge(c, 4449) == False{} : Bool}, e2: {U32.is_ge(c, 4520) == False{} : Bool}, +s: U32) -> {N.compose(Tab.pairs(), s, c) == None{} : Maybe<&2, U32>}:
  compose_of_none(Tab.pairs(), s, c,
    N.hangul.lv(s, c), and_ff(Bool.and(U32.is_ge(s, 4352), U32.is_le(s, 4370)), U32.is_ge(c, 4449), U32.is_le(c, 4469), e1),
    N.hangul.lvt(s, c), and_ff(Bool.and(N.hangul.is(s), U32.is_eq(((s - 44032 : U32) % 28 : U32), 0)), U32.is_ge(c, 4520), U32.is_le(c, 4546), e2),
    pair_none(Tab.pairs(), s, c, N.pair.cmp(Tab.pairs(), s, c), {==}, hm))

# `/` and `.` in normal form C's algorithm over the crate's tables.
def slash_wall(+xs: List<&2, U32>, +ys: List<&2, U32>) -> {N.nfc.points(N.tabs(), List.append(&2, U32, xs, 47 <> ys)) == List.append(&2, U32, N.nfc.points(N.tabs(), xs), 47 <> N.nfc.points(N.tabs(), ys)) : List<&2, U32>}:
  points_wall(Tab.classes(), Tab.decompositions(), Tab.pairs(), xs, 47, ys, {==}, {==}, s => tables_miss(47, {==}, {==}, {==}, s), {==}, {==}, {==})

def dot_wall(+xs: List<&2, U32>, +ys: List<&2, U32>) -> {N.nfc.points(N.tabs(), List.append(&2, U32, xs, 46 <> ys)) == List.append(&2, U32, N.nfc.points(N.tabs(), xs), 46 <> N.nfc.points(N.tabs(), ys)) : List<&2, U32>}:
  points_wall(Tab.classes(), Tab.decompositions(), Tab.pairs(), xs, 46, ys, {==}, {==}, s => tables_miss(46, {==}, {==}, {==}, s), {==}, {==}, {==})

# `/` or `.`: whichever the separator is, the algorithm takes it as a wall.
def sep_wall.of(b: Bool, +c: U32, eb: {U32.is_eq(c, 47) == b : Bool}, h: {Bool.or(b, U32.is_eq(c, 46)) == True{} : Bool}, +xs: List<&2, U32>, +ys: List<&2, U32>) -> {N.nfc.points(N.tabs(), List.append(&2, U32, xs, c <> ys)) == List.append(&2, U32, N.nfc.points(N.tabs(), xs), c <> N.nfc.points(N.tabs(), ys)) : List<&2, U32>}:
  match b:
    case True{}:
      %Equal.sym(U32, c, 47, EqL.u32_eq(c, 47, eb)) : {N.nfc.points(N.tabs(), List.append(&2, U32, xs, _ <> ys)) == List.append(&2, U32, N.nfc.points(N.tabs(), xs), _ <> N.nfc.points(N.tabs(), ys)) : List<&2, U32>}
      slash_wall(xs, ys)
    case False{}:
      %Equal.sym(U32, c, 46, EqL.u32_eq(c, 46, h)) : {N.nfc.points(N.tabs(), List.append(&2, U32, xs, _ <> ys)) == List.append(&2, U32, N.nfc.points(N.tabs(), xs), _ <> N.nfc.points(N.tabs(), ys)) : List<&2, U32>}
      dot_wall(xs, ys)

def separators_wall(+xs: List<&2, U32>, +c: U32, +ys: List<&2, U32>, h: {Bool.or(U32.is_eq(c, 47), U32.is_eq(c, 46)) == True{} : Bool}) -> {N.nfc.points(N.tabs(), List.append(&2, U32, xs, c <> ys)) == List.append(&2, U32, N.nfc.points(N.tabs(), xs), c <> N.nfc.points(N.tabs(), ys)) : List<&2, U32>}:
  sep_wall.of(U32.is_eq(c, 47), c, {==}, h, xs, ys)

# The walk
# --------

def go_apart(fs: List<&2, F.Found>, +last: String, same: Bool, +es: {F.distinct.same(fs, last) == same : Bool}) -> {F.apart.go(F.distinct.go(fs, last, same), last) == True{} : Bool}:
  match fs same:
    case Nil{} _:
      {==}
    case f <> +rest True{}:
      go_apart(rest, last, F.distinct.same(rest, last), {==})
    case +f <> +rest False{}:
      %Equal.sym(Bool, String.eq(F.found.path(f), last), False{}, es) : {Bool.and(Bool.not(_), F.apart.go(F.distinct.go(rest, F.found.path(f), F.distinct.same(rest, F.found.path(f))), F.found.path(f))) == True{} : Bool}
      go_apart(rest, F.found.path(f), F.distinct.same(rest, F.found.path(f)), {==})

def walk_apart(fs: List<&2, F.Found>) -> {F.apart(F.distinct(fs)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +rest:
      go_apart(rest, F.found.path(f), F.distinct.same(rest, F.found.path(f)), {==})

# What a listing may spell a path with: nothing yet, or a name whose normal
# form is the path.
def spelt_ok(got: Maybe<&2, String>, +want: String) -> Bool:
  match got:
    case None{}:
      True{}
    case Some{n}:
      String.eq(N.nfc(n), want)

def take_ok.of(+line: String, +want: String, got: Maybe<&2, String>, c: Bool, +ec: {Bool.and(Bool.not(String.starts_with(line, "u ")), String.eq(N.nfc(F.entry.name(line)), want)) == c : Bool}, +hg: {spelt_ok(got, want) == True{} : Bool}) -> {spelt_ok(Bool.pick(Maybe<&2, String>, c, Some{F.entry.name(line)}, got), want) == True{} : Bool}:
  match c:
    case True{}:
      and_r(Bool.not(String.starts_with(line, "u ")), String.eq(N.nfc(F.entry.name(line)), want), ec)
    case False{}:
      hg

def take_ok(+line: String, +want: String, +got: Maybe<&2, String>, +hg: {spelt_ok(got, want) == True{} : Bool}) -> {spelt_ok(F.spelling.take(line, want, got), want) == True{} : Bool}:
  take_ok.of(line, want, got, Bool.and(Bool.not(String.starts_with(line, "u ")), String.eq(N.nfc(F.entry.name(line)), want)), {==}, hg)

def spelling_ok(ls: List<&2, String>, +want: String, +got: Maybe<&2, String>, after: Bool, +hg: {spelt_ok(got, want) == True{} : Bool}) -> {spelt_ok(F.spelling.go(ls, want, got, after), want) == True{} : Bool}:
  match ls after:
    case Nil{} _:
      hg
    case line <> rest True{}:
      spelling_ok(rest, want, got, False{}, hg)
    case +line <> rest False{}:
      spelling_ok(rest, want, F.spelling.take(line, want, got), String.starts_with(line, "l "), take_ok(line, want, got, hg))

def or_true(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def spelt_or(m: Maybe<&2, String>, +want: String, +h: {spelt_ok(m, want) == True{} : Bool}) -> {Bool.or(String.eq(Maybe.default(&2, String, m, want), want), String.eq(N.nfc(Maybe.default(&2, String, m, want)), want)) == True{} : Bool}:
  match m:
    case None{}:
      %Equal.sym(Bool, String.eq(want, want), True{}, S.eq_refl(want)) : {Bool.or(_, String.eq(N.nfc(want), want)) == True{} : Bool}
      {==}
    case Some{+n}:
      %Equal.sym(Bool, String.eq(N.nfc(n), want), True{}, h) : {Bool.or(String.eq(n, want), _) == True{} : Bool}
      or_true(String.eq(n, want))

def spelled_there(+ls: List<&2, String>, +want: String) -> {Bool.or(String.eq(F.spelling(ls, want), want), String.eq(N.nfc(F.spelling(ls, want)), want)) == True{} : Bool}:
  spelt_or(F.spelling.go(ls, want, None{}, False{}), want, spelling_ok(ls, want, None{}, False{}, {==}))

# A listing, as the host means it
# -------------------------------

# One directory's entries as `Store.folder` knows them, before they are
# lines: what `a_name_that_cannot_be_spelled_is_refused` reads back.
type Listed is Data:
  Listed.Dir{name: String}
  Listed.File{runs: String, size: String, name: String}
  Listed.Link{name: String, target: String}
  Listed.Unreadable{name: String}
  Listed.Other{name: String}
  Listed.Unspelled{lossy: String}

# The lines the host writes for them: a kind and a name, a link's target on
# the line after it, and a name that is not UTF-8 as its lossy spelling.
def listed.lines(es: List<&2, Listed>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Listed.Dir{n} <> rest:
      ("d " ++ n) <> listed.lines(rest)
    case Listed.File{r, z, n} <> rest:
      ("f " ++ r ++ " " ++ z ++ " " ++ n) <> listed.lines(rest)
    case Listed.Link{n, t} <> rest:
      ("l " ++ n) <> t <> listed.lines(rest)
    case Listed.Unreadable{n} <> rest:
      ("L " ++ n) <> listed.lines(rest)
    case Listed.Other{n} <> rest:
      ("o " ++ n) <> listed.lines(rest)
    case Listed.Unspelled{x} <> rest:
      ("u " ++ x) <> listed.lines(rest)

# What the Rust tool refuses of them: each name that is not UTF-8, where it
# is on disk under `dir`, with `WorkingError::NotUtf8`'s words.
def listed.refused(es: List<&2, Listed>, +dir: String) -> List<&2, T.Split>:
  match es:
    case Nil{}:
      Nil{}
    case Listed.Unspelled{x} <> rest:
      T.Split{dir ++ "/" ++ x, "not a name this format can hold"} <> listed.refused(rest, dir)
    case e <> rest:
      listed.refused(rest, dir)

def sw_empty(t: String) -> {String.starts_with(t, SNil{}) == True{} : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{h, r}:
      {==}

def drop_zero(t: String) -> {String.drop(t, 0n) == t : String}:
  match t:
    case SNil{}:
      {==}
    case SCon{h, r}:
      {==}

# Reading the lines back refuses each name that cannot be spelled, onto
# what was refused before, whatever the entry before it and the count.
def read_back(es: List<&2, Listed>, +prefix: String, +dir: String, +before: String, +k: U32, +acc: List<&2, F.Keyed>) -> {F.unkeyed(F.unspelled.go(listed.lines(es), prefix, dir, before, k, False{}, F.unspelled.is(listed.lines(es)), acc)) == List.reverse.go(&2, T.Split, listed.refused(es, dir), F.unkeyed(acc)) : List<&2, T.Split>}:
  match es:
    case Nil{}:
      {==}
    case Listed.Dir{+n} <> +rest:
      read_back(rest, prefix, dir, F.joined(prefix, F.entry.name("d " ++ n)), 0, acc)
    case Listed.File{+r, +z, +n} <> +rest:
      read_back(rest, prefix, dir, F.joined(prefix, F.entry.name("f " ++ r ++ " " ++ z ++ " " ++ n)), 0, acc)
    case Listed.Link{+n, +t} <> +rest:
      %Equal.sym(Bool, String.starts_with(n, SNil{}), True{}, sw_empty(n)) : {F.unkeyed(F.unspelled.go(t <> listed.lines(rest), prefix, dir, F.joined(prefix, F.entry.name("l " ++ n)), 0, _, F.unspelled.is(t <> listed.lines(rest)), acc)) == List.reverse.go(&2, T.Split, listed.refused(rest, dir), F.unkeyed(acc)) : List<&2, T.Split>}
      read_back(rest, prefix, dir, F.joined(prefix, F.entry.name("l " ++ n)), 0, acc)
    case Listed.Unreadable{+n} <> +rest:
      read_back(rest, prefix, dir, F.joined(prefix, F.entry.name("L " ++ n)), 0, acc)
    case Listed.Other{+n} <> +rest:
      read_back(rest, prefix, dir, F.joined(prefix, F.entry.name("o " ++ n)), 0, acc)
    case Listed.Unspelled{+x} <> +rest:
      %Equal.sym(Bool, String.starts_with(x, SNil{}), True{}, sw_empty(x)) : {F.unkeyed(F.unspelled.go(("u " ++ x) <> listed.lines(rest), prefix, dir, before, k, False{}, _, acc)) == List.reverse.go(&2, T.Split, listed.refused(rest, dir), T.Split{dir ++ "/" ++ x, "not a name this format can hold"} <> F.unkeyed(acc)) : List<&2, T.Split>}
      %drop_zero(x) : {F.unkeyed(F.unspelled.go(listed.lines(rest), prefix, dir, before, (k + 1 : U32), False{}, F.unspelled.is(listed.lines(rest)), F.Keyed{F.unspelled.key(before, k), T.Split{dir ++ "/" ++ String.drop(x, 0n), F.unspelled.because()}} <> acc)) == List.reverse.go(&2, T.Split, listed.refused(rest, dir), T.Split{dir ++ "/" ++ _, "not a name this format can hold"} <> F.unkeyed(acc)) : List<&2, T.Split>}
      read_back(rest, prefix, dir, before, (k + 1 : U32), F.Keyed{F.unspelled.key(before, k), T.Split{dir ++ "/" ++ String.drop(x, 0n), F.unspelled.because()}} <> acc)

# A name that cannot be spelled, read back from the host's lines, is
# refused once, where it is on disk, in the Rust tool's words; nothing
# else in the listing is.
def all_refused(es: List<&2, Listed>, +prefix: String, +dir: String) -> {F.unkeyed(F.unspelled(listed.lines(es), prefix, dir)) == List.reverse(&2, T.Split, listed.refused(es, dir)) : List<&2, T.Split>}:
  read_back(es, prefix, dir, Bool.pick(String, String.is_empty(prefix), SNil{}, prefix ++ "/"), 0, Nil{})

# Nothing lost
# ------------

# Whether some file of `ds` is at `p`.
def held(ds: List<&2, F.Found>, +p: String) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case d <> rest:
      Bool.or(String.eq(p, F.found.path(d)), held(rest, p))

# Every path a file of `fs` is at, some file of `ds` is at.
def paths_held(fs: List<&2, F.Found>, +ds: List<&2, F.Found>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case g <> rest:
      Bool.and(held(ds, F.found.path(g)), paths_held(rest, ds))

def held_or(fs: List<&2, F.Found>, +last: String, +ds: List<&2, F.Found>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case +g <> rest:
      Bool.and(Bool.or(String.eq(F.found.path(g), last), held(ds, F.found.path(g))), held_or(rest, last, ds))

def or_widen(a: Bool, b: Bool, -c: Bool, e: {Bool.or(b, c) == True{} : Bool}) -> {Bool.or(a, Bool.or(b, c)) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

# What was held beside `f` is held with `f` in front, whatever came first.
def held_or_widen(fs: List<&2, F.Found>, +x: String, +last: String, +f: F.Found, +ds: List<&2, F.Found>, +ex: {F.found.path(f) == x : String}, +h: {held_or(fs, x, ds) == True{} : Bool}) -> {held_or(fs, last, f <> ds) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case +g <> +rest:
      %Equal.sym(String, F.found.path(f), x, ex) : {Bool.and(Bool.or(String.eq(F.found.path(g), last), Bool.or(String.eq(F.found.path(g), _), held(ds, F.found.path(g)))), held_or(rest, last, f <> ds)) == True{} : Bool}
      and_i(Bool.or(String.eq(F.found.path(g), last), Bool.or(String.eq(F.found.path(g), x), held(ds, F.found.path(g)))), held_or(rest, last, f <> ds),
        or_widen(String.eq(F.found.path(g), last), String.eq(F.found.path(g), x), held(ds, F.found.path(g)), and_l(Bool.or(String.eq(F.found.path(g), x), held(ds, F.found.path(g))), held_or(rest, x, ds), h)),
        held_or_widen(rest, x, last, f, ds, ex, and_r(Bool.or(String.eq(F.found.path(g), x), held(ds, F.found.path(g))), held_or(rest, x, ds), h)))

def or_true_l(-b: Bool) -> {Bool.or(True{}, b) == True{} : Bool}:
  {==}

# Every file `distinct.go` passes over is at `last` or at a path it keeps.
def go_held(fs: List<&2, F.Found>, +last: String, same: Bool, +es: {F.distinct.same(fs, last) == same : Bool}) -> {held_or(fs, last, F.distinct.go(fs, last, same)) == True{} : Bool}:
  match fs same:
    case Nil{} _:
      {==}
    case +g <> +rest True{}:
      and_i(Bool.or(String.eq(F.found.path(g), last), held(F.distinct.go(rest, last, F.distinct.same(rest, last)), F.found.path(g))), held_or(rest, last, F.distinct.go(rest, last, F.distinct.same(rest, last))),
        (%Equal.sym(Bool, String.eq(F.found.path(g), last), True{}, es) : {Bool.or(_, held(F.distinct.go(rest, last, F.distinct.same(rest, last)), F.found.path(g))) == True{} : Bool}
         {==}),
        go_held(rest, last, F.distinct.same(rest, last), {==}))
    case +g <> +rest False{}:
      +ds = F.distinct.go(rest, F.found.path(g), F.distinct.same(rest, F.found.path(g)))
      and_i(Bool.or(String.eq(F.found.path(g), last), held(g <> ds, F.found.path(g))), held_or(rest, last, g <> ds),
        or_widen(String.eq(F.found.path(g), last), String.eq(F.found.path(g), F.found.path(g)), held(ds, F.found.path(g)),
          (%Equal.sym(Bool, String.eq(F.found.path(g), F.found.path(g)), True{}, S.eq_refl(F.found.path(g))) : {Bool.or(_, held(ds, F.found.path(g))) == True{} : Bool}
           {==})),
        held_or_widen(rest, F.found.path(g), last, g, ds, {==}, go_held(rest, F.found.path(g), F.distinct.same(rest, F.found.path(g)), {==})))

# Held beside `f`, with `f` itself in front, is held.
def held_of(fs: List<&2, F.Found>, +f: F.Found, +ds: List<&2, F.Found>, +h: {held_or(fs, F.found.path(f), ds) == True{} : Bool}) -> {paths_held(fs, f <> ds) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case +g <> +rest:
      and_i(held(f <> ds, F.found.path(g)), paths_held(rest, f <> ds),
        and_l(Bool.or(String.eq(F.found.path(g), F.found.path(f)), held(ds, F.found.path(g))), held_or(rest, F.found.path(f), ds), h),
        held_of(rest, f, ds, and_r(Bool.or(String.eq(F.found.path(g), F.found.path(f)), held(ds, F.found.path(g))), held_or(rest, F.found.path(f), ds), h)))

# No path the walk found is lost by keeping one file for it.
def walk_keeps(fs: List<&2, F.Found>) -> {paths_held(fs, F.distinct(fs)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +rest:
      +ds = F.distinct.go(rest, F.found.path(f), F.distinct.same(rest, F.found.path(f)))
      and_i(held(f <> ds, F.found.path(f)), paths_held(rest, f <> ds),
        (%Equal.sym(Bool, String.eq(F.found.path(f), F.found.path(f)), True{}, S.eq_refl(F.found.path(f))) : {Bool.or(_, held(ds, F.found.path(f))) == True{} : Bool}
         {==}),
        held_of(rest, f, ds, go_held(rest, F.found.path(f), F.distinct.same(rest, F.found.path(f)), {==})))

def walk_once(+fs: List<&2, F.Found>) -> {Bool.and(F.apart(F.distinct(fs)), paths_held(fs, F.distinct(fs))) == True{} : Bool}:
  and_i(F.apart(F.distinct(fs)), paths_held(fs, F.distinct(fs)), walk_apart(fs), walk_keeps(fs))

# Ordering moves no mark past its class
# -------------------------------------

# The marks of class `k`, in order.
def of_class(ms: List<&2, N.Mark>, +k: U32) -> List<&2, N.Mark>:
  match ms:
    case Nil{}:
      Nil{}
    case +m <> +rest:
      Bool.pick(List<&2, N.Mark>, U32.is_eq(N.mark.class(m), k), m <> of_class(rest, k), of_class(rest, k))

def app_nil(xs: List<&2, N.Mark>) -> {List.append(&2, N.Mark, xs, Nil{}) == xs : List<&2, N.Mark>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %app_nil(rest) : {x <> List.append(&2, N.Mark, rest, Nil{}) == x <> _ : List<&2, N.Mark>}
      {==}

def app_assoc(xs: List<&2, N.Mark>, +ys: List<&2, N.Mark>, +zs: List<&2, N.Mark>) -> {List.append(&2, N.Mark, List.append(&2, N.Mark, xs, ys), zs) == List.append(&2, N.Mark, xs, List.append(&2, N.Mark, ys, zs)) : List<&2, N.Mark>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %app_assoc(rest, ys, zs) : {x <> List.append(&2, N.Mark, List.append(&2, N.Mark, rest, ys), zs) == x <> _ : List<&2, N.Mark>}
      {==}

def app_pick(c: Bool, +x: N.Mark, +a: List<&2, N.Mark>, +b: List<&2, N.Mark>) -> {Bool.pick(List<&2, N.Mark>, c, x <> List.append(&2, N.Mark, a, b), List.append(&2, N.Mark, a, b)) == List.append(&2, N.Mark, Bool.pick(List<&2, N.Mark>, c, x <> a, a), b) : List<&2, N.Mark>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def of_app(xs: List<&2, N.Mark>, +ys: List<&2, N.Mark>, +k: U32) -> {of_class(List.append(&2, N.Mark, xs, ys), k) == List.append(&2, N.Mark, of_class(xs, k), of_class(ys, k)) : List<&2, N.Mark>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(List<&2, N.Mark>, of_class(List.append(&2, N.Mark, rest, ys), k), List.append(&2, N.Mark, of_class(rest, k), of_class(ys, k)), of_app(rest, ys, k)) : {Bool.pick(List<&2, N.Mark>, U32.is_eq(N.mark.class(x), k), x <> _, _) == List.append(&2, N.Mark, Bool.pick(List<&2, N.Mark>, U32.is_eq(N.mark.class(x), k), x <> of_class(rest, k), of_class(rest, k)), of_class(ys, k)) : List<&2, N.Mark>}
      app_pick(U32.is_eq(N.mark.class(x), k), x, of_class(rest, k), of_class(ys, k))

# Above `lo`, nothing is of a class below it.
def lt_ne.cmp(c: Cmp, e: {c == LT{} : Cmp}) -> {Cmp.is_eq(SortL.cflip(c)) == False{} : Bool}:
  %Equal.sym(Cmp, c, LT{}, e) : {Cmp.is_eq(SortL.cflip(_)) == False{} : Bool}
  {==}

def lt_ne(x: U32, y: U32, e: {U32.is_lt(x, y) == True{} : Bool}) -> {U32.is_eq(y, x) == False{} : Bool}:
  match x y:
    case U32{+a} U32{+b}:
      %Equal.sym(Cmp, Word.cmp(32n, b, a), SortL.cflip(Word.cmp(32n, a, b)), SortL.word_flip(32n, a, b)) : {Cmp.is_eq(_) == False{} : Bool}
      lt_ne.cmp(Word.cmp(32n, a, b), lt_cmp(Word.cmp(32n, a, b), e))

def none_of_class(xs: List<&2, N.Mark>, +lo: U32, +k: U32, +hs: {sorted.from(xs, lo) == True{} : Bool}, +hk: {U32.is_lt(k, lo) == True{} : Bool}) -> {of_class(xs, k) == Nil{} : List<&2, N.Mark>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      +hx = lt_le(k, lo, N.mark.class(x), hk, and_l(U32.is_le(lo, N.mark.class(x)), sorted.from(rest, N.mark.class(x)), hs))
      %Equal.sym(Bool, U32.is_eq(N.mark.class(x), k), False{}, lt_ne(k, N.mark.class(x), hx)) : {Bool.pick(List<&2, N.Mark>, _, x <> of_class(rest, k), of_class(rest, k)) == Nil{} : List<&2, N.Mark>}
      none_of_class(rest, N.mark.class(x), k, and_r(U32.is_le(lo, N.mark.class(x)), sorted.from(rest, N.mark.class(x)), hs), hx)

# Not at or below, above.
def not_le_lt.cmp(c: Cmp, e: {Cmp.is_le(c) == False{} : Bool}) -> {Cmp.is_lt(SortL.cflip(c)) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Cmp.is_lt(SortL.cflip(LT{})) == True{} : Bool}, S.true_false(e))
    case EQ{}:
      Empty.absurd({Cmp.is_lt(SortL.cflip(EQ{})) == True{} : Bool}, S.true_false(e))
    case GT{}:
      {==}

def not_le_lt(x: U32, y: U32, e: {U32.is_le(x, y) == False{} : Bool}) -> {U32.is_lt(y, x) == True{} : Bool}:
  match x y:
    case U32{+a} U32{+b}:
      %Equal.sym(Cmp, Word.cmp(32n, b, a), SortL.cflip(Word.cmp(32n, a, b)), SortL.word_flip(32n, a, b)) : {Cmp.is_lt(_) == True{} : Bool}
      not_le_lt.cmp(Word.cmp(32n, a, b), e)

def le_refl(x: U32) -> {U32.is_le(x, x) == True{} : Bool}:
  match x:
    case U32{+a}:
      %Equal.sym(Cmp, Word.cmp(32n, a, a), EQ{}, S.word_refl(32n, a)) : {Cmp.is_le(_) == True{} : Bool}
      {==}

# A mark of class `k` goes in after every mark of its class.
def before_higher(c: Bool, +m: N.Mark, +r: N.Mark, +rest: List<&2, N.Mark>, +k: U32, +ec: {U32.is_eq(N.mark.class(m), k) == c : Bool}, +hlt: {U32.is_lt(N.mark.class(m), N.mark.class(r)) == True{} : Bool}, +hs: {sorted.from(rest, N.mark.class(r)) == True{} : Bool}) -> {Bool.pick(List<&2, N.Mark>, c, m <> of_class(r <> rest, k), of_class(r <> rest, k)) == List.append(&2, N.Mark, of_class(r <> rest, k), Bool.pick(List<&2, N.Mark>, c, [m], Nil{})) : List<&2, N.Mark>}:
  match c:
    case False{}:
      Equal.sym(List<&2, N.Mark>, List.append(&2, N.Mark, of_class(r <> rest, k), Nil{}), of_class(r <> rest, k), app_nil(of_class(r <> rest, k)))
    case True{}:
      +emk = EqL.u32_eq(N.mark.class(m), k, ec)
      +hk : {U32.is_lt(k, N.mark.class(r)) == True{} : Bool} = (%emk : {U32.is_lt(_, N.mark.class(r)) == True{} : Bool}; hlt)
      +e1 = none_of_class(r <> rest, N.mark.class(r), k, and_i(U32.is_le(N.mark.class(r), N.mark.class(r)), sorted.from(rest, N.mark.class(r)), le_refl(N.mark.class(r)), hs), hk)
      %Equal.sym(List<&2, N.Mark>, of_class(r <> rest, k), Nil{}, e1) : {m <> _ == List.append(&2, N.Mark, _, [m]) : List<&2, N.Mark>}
      {==}

def after_pick(c: Bool, +r: N.Mark, +a: List<&2, N.Mark>, +b: List<&2, N.Mark>, +m1: List<&2, N.Mark>, +e: {a == List.append(&2, N.Mark, b, m1) : List<&2, N.Mark>}) -> {Bool.pick(List<&2, N.Mark>, c, r <> a, a) == List.append(&2, N.Mark, Bool.pick(List<&2, N.Mark>, c, r <> b, b), m1) : List<&2, N.Mark>}:
  match c:
    case True{}:
      %Equal.sym(List<&2, N.Mark>, a, List.append(&2, N.Mark, b, m1), e) : {r <> _ == r <> List.append(&2, N.Mark, b, m1) : List<&2, N.Mark>}
      {==}
    case False{}:
      e

# Inserting a mark into a run in order adds it to its class's marks, last.
def insert_class(run: List<&2, N.Mark>, +m: N.Mark, after: Bool, +ea: {N.goes_after(run, m) == after : Bool}, +lo: U32, +hs: {sorted.from(run, lo) == True{} : Bool}, +k: U32) -> {of_class(N.insert.go(run, m, after), k) == List.append(&2, N.Mark, of_class(run, k), of_class([m], k)) : List<&2, N.Mark>}:
  match run after:
    case Nil{} _:
      {==}
    case +r <> +rest True{}:
      after_pick(U32.is_eq(N.mark.class(r), k), r, of_class(N.insert.go(rest, m, N.goes_after(rest, m)), k), of_class(rest, k), of_class([m], k),
        insert_class(rest, m, N.goes_after(rest, m), {==}, N.mark.class(r), and_r(U32.is_le(lo, N.mark.class(r)), sorted.from(rest, N.mark.class(r)), hs), k))
    case +r <> +rest False{}:
      before_higher(U32.is_eq(N.mark.class(m), k), m, r, rest, k, {==}, not_le_lt(N.mark.class(r), N.mark.class(m), ea), and_r(U32.is_le(lo, N.mark.class(r)), sorted.from(rest, N.mark.class(r)), hs))

def insert_run_class(run: List<&2, N.Mark>, +m: N.Mark, +hr: {sorted.run(run) == True{} : Bool}, +k: U32) -> {of_class(N.insert(run, m), k) == List.append(&2, N.Mark, of_class(run, k), of_class([m], k)) : List<&2, N.Mark>}:
  match run:
    case Nil{}:
      {==}
    case +r <> +rest:
      insert_class(r <> rest, m, N.goes_after(r <> rest, m), {==}, N.mark.class(r), and_i(U32.is_le(N.mark.class(r), N.mark.class(r)), sorted.from(rest, N.mark.class(r)), le_refl(N.mark.class(r)), hr), k)

def single_app(c: Bool, +m: N.Mark, +r: List<&2, N.Mark>) -> {List.append(&2, N.Mark, Bool.pick(List<&2, N.Mark>, c, [m], Nil{}), r) == Bool.pick(List<&2, N.Mark>, c, m <> r, r) : List<&2, N.Mark>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def cons_class(+m: N.Mark, +x: List<&2, N.Mark>, +y: List<&2, N.Mark>, +k: U32, +e: {of_class(x, k) == of_class(y, k) : List<&2, N.Mark>}) -> {of_class(m <> x, k) == of_class(m <> y, k) : List<&2, N.Mark>}:
  %e : {Bool.pick(List<&2, N.Mark>, U32.is_eq(N.mark.class(m), k), m <> of_class(x, k), of_class(x, k)) == Bool.pick(List<&2, N.Mark>, U32.is_eq(N.mark.class(m), k), m <> _, _) : List<&2, N.Mark>}
  {==}

# What `order` returns holds each class's marks as it was given them: the
# run so far, then what is left, class by class.
def order_class(ms: List<&2, N.Mark>, +run: List<&2, N.Mark>, st: Bool, +est: {N.starts(ms) == st : Bool}, +hr: {sorted.run(run) == True{} : Bool}, +k: U32) -> {of_class(N.order.go(ms, run, st), k) == List.append(&2, N.Mark, of_class(run, k), of_class(ms, k)) : List<&2, N.Mark>}:
  match ms st:
    case Nil{} _:
      Equal.sym(List<&2, N.Mark>, List.append(&2, N.Mark, of_class(run, k), Nil{}), of_class(run, k), app_nil(of_class(run, k)))
    case +m <> +rest True{}:
      +x = N.order.go(rest, Nil{}, N.starts(rest))
      Equal.trans(List<&2, N.Mark>, of_class(List.append(&2, N.Mark, run, m <> x), k), List.append(&2, N.Mark, of_class(run, k), of_class(m <> x, k)), List.append(&2, N.Mark, of_class(run, k), of_class(m <> rest, k)),
        of_app(run, m <> x, k),
        Equal.cong(List<&2, N.Mark>, List<&2, N.Mark>, t => List.append(&2, N.Mark, of_class(run, k), t), of_class(m <> x, k), of_class(m <> rest, k),
          cons_class(m, x, rest, k, order_class(rest, Nil{}, N.starts(rest), {==}, {==}, k))))
    case +m <> +rest False{}:
      +ir = N.insert(run, m)
      Equal.trans(List<&2, N.Mark>, of_class(N.order.go(rest, ir, N.starts(rest)), k), List.append(&2, N.Mark, of_class(ir, k), of_class(rest, k)), List.append(&2, N.Mark, of_class(run, k), of_class(m <> rest, k)),
        order_class(rest, ir, N.starts(rest), {==}, insert_run(run, m, hr), k),
        Equal.trans(List<&2, N.Mark>, List.append(&2, N.Mark, of_class(ir, k), of_class(rest, k)), List.append(&2, N.Mark, List.append(&2, N.Mark, of_class(run, k), of_class([m], k)), of_class(rest, k)), List.append(&2, N.Mark, of_class(run, k), of_class(m <> rest, k)),
          Equal.cong(List<&2, N.Mark>, List<&2, N.Mark>, t => List.append(&2, N.Mark, t, of_class(rest, k)), of_class(ir, k), List.append(&2, N.Mark, of_class(run, k), of_class([m], k)), insert_run_class(run, m, hr, k)),
          Equal.trans(List<&2, N.Mark>, List.append(&2, N.Mark, List.append(&2, N.Mark, of_class(run, k), of_class([m], k)), of_class(rest, k)), List.append(&2, N.Mark, of_class(run, k), List.append(&2, N.Mark, of_class([m], k), of_class(rest, k))), List.append(&2, N.Mark, of_class(run, k), of_class(m <> rest, k)),
            app_assoc(of_class(run, k), of_class([m], k), of_class(rest, k)),
            Equal.cong(List<&2, N.Mark>, List<&2, N.Mark>, t => List.append(&2, N.Mark, of_class(run, k), t), List.append(&2, N.Mark, of_class([m], k), of_class(rest, k)), of_class(m <> rest, k), single_app(U32.is_eq(N.mark.class(m), k), m, of_class(rest, k))))))

# Canonical ordering moves no mark past another of its class, and loses or
# adds none: the marks of every class are the ones given, in order.
def keeps_each_class(+ms: List<&2, N.Mark>, +k: U32) -> {of_class(N.order(ms), k) == of_class(ms, k) : List<&2, N.Mark>}:
  order_class(ms, Nil{}, N.starts(ms), {==}, {==}, k)
