# Normal form C's laws: a string of ASCII is its own normal form; canonical
# ordering puts every run of marks in order of class; the class lookup,
# which stops early, misses nothing over the crate's table; `/` and `.` are
# characters normalising leaves alone. And the walk's: it yields a path
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

# Neither `/` nor `.` has a class, is in a pair, or is in a decomposition.
def separators_inert() -> {Bool.and(N.inert(47), N.inert(46)) == True{} : Bool}:
  {==}

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

# One refusal for every name a listing holds that cannot be spelled.
def count_go(ls: List<&2, String>, +prefix: String, +dir: String, +before: String, +k: U32, after: Bool, odd: Bool, +acc: List<&2, F.Keyed>) -> {List.length(&2, F.Keyed, F.unspelled.go(ls, prefix, dir, before, k, after, odd, acc)) == Nat.add(F.unspelled.count(ls, after, odd), List.length(&2, F.Keyed, acc)) : Nat}:
  match ls after odd:
    case Nil{} _ _:
      {==}
    case line <> +rest True{} _:
      count_go(rest, prefix, dir, before, k, False{}, F.unspelled.is(rest), acc)
    case +line <> +rest False{} True{}:
      +r : F.Keyed = F.Keyed{F.unspelled.key(before, k), T.Split{dir ++ "/" ++ String.drop(line, 2n), F.unspelled.because()}}
      Equal.trans(Nat, List.length(&2, F.Keyed, F.unspelled.go(rest, prefix, dir, before, (k + 1 : U32), False{}, F.unspelled.is(rest), r <> acc)), Nat.add(F.unspelled.count(rest, False{}, F.unspelled.is(rest)), 1n+List.length(&2, F.Keyed, acc)), 1n+Nat.add(F.unspelled.count(rest, False{}, F.unspelled.is(rest)), List.length(&2, F.Keyed, acc)),
        count_go(rest, prefix, dir, before, (k + 1 : U32), False{}, F.unspelled.is(rest), r <> acc),
        Pos.add_succ(F.unspelled.count(rest, False{}, F.unspelled.is(rest)), List.length(&2, F.Keyed, acc)))
    case +line <> +rest False{} False{}:
      count_go(rest, prefix, dir, F.joined(prefix, F.entry.name(line)), 0, String.starts_with(line, "l "), F.unspelled.is(rest), acc)

def all_refused(+ls: List<&2, String>, +prefix: String, +dir: String) -> {List.length(&2, F.Keyed, F.unspelled(ls, prefix, dir)) == F.unspelled.count(ls, False{}, F.unspelled.is(ls)) : Nat}:
  Equal.trans(Nat, List.length(&2, F.Keyed, F.unspelled(ls, prefix, dir)), Nat.add(F.unspelled.count(ls, False{}, F.unspelled.is(ls)), 0n), F.unspelled.count(ls, False{}, F.unspelled.is(ls)),
    count_go(ls, prefix, dir, Bool.pick(String, String.is_empty(prefix), SNil{}, prefix ++ "/"), 0, False{}, F.unspelled.is(ls), Nil{}),
    Comp.add_zero(F.unspelled.count(ls, False{}, F.unspelled.is(ls))))
