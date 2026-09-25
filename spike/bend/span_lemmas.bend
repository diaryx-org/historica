# `log` lists only what its span names: with a target, revisions the target
# reaches; with `a..b`, revisions `b` reaches and `a` does not — every one a
# revision the store holds.
import Base
import ./revision.bend as Rev
import ./commands.bend as Main
import ./string_lemmas.bend as S
import ./anchor_lemmas.bend as AL
import ./composition_lemmas.bend as Comp
import ./graph_lemmas.bend as GL

# Every revision of a list has its digest among `ids`.
def inids(+ids: List<&2, String>, xs: List<&2, Main.Full>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      Bool.and(Rev.member(ids, Main.id_of(x)), inids(ids, rest))

def inids_weak(+y: String, +ids: List<&2, String>, xs: List<&2, Main.Full>, +h: {inids(ids, xs) == True{} : Bool}) -> {inids(y <> ids, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Rev.member(y <> ids, Main.id_of(x)), inids(y <> ids, rest),
        GL.member_tail(y, ids, Main.id_of(x), Comp.and_left(Rev.member(ids, Main.id_of(x)), inids(ids, rest), h)),
        inids_weak(y, ids, rest, Comp.and_right(Rev.member(ids, Main.id_of(x)), inids(ids, rest), h)))

# Each revision of the store is one of the store's.
def inids_self(fs: List<&2, Main.Full>) -> {inids(Main.ids(fs), fs) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +rest:
      AL.and_intro(Rev.member(Main.id_of(f) <> Main.ids(rest), Main.id_of(f)), inids(Main.id_of(f) <> Main.ids(rest), rest),
        GL.member_head(Main.id_of(f), Main.ids(rest)), inids_weak(Main.id_of(f), Main.ids(rest), rest, inids_self(rest)))

def all_case(+fs: List<&2, Main.Full>, xs: List<&2, Main.Full>, +h: {inids(Main.ids(fs), xs) == True{} : Bool}) -> {Main.span.all_in(fs, Main.Span.All{}, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Rev.member(Main.ids(fs), Main.id_of(x)), Main.span.all_in(fs, Main.Span.All{}, rest), Comp.and_left(Rev.member(Main.ids(fs), Main.id_of(x)), inids(Main.ids(fs), rest), h),
        all_case(fs, rest, Comp.and_right(Rev.member(Main.ids(fs), Main.id_of(x)), inids(Main.ids(fs), rest), h)))

# Every revision of a list is one of `ids` and in `R`.
def amongst(+ids: List<&2, String>, +R: List<&2, String>, xs: List<&2, Main.Full>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      Bool.and(Bool.and(Rev.member(ids, Main.id_of(x)), Rev.member(R, Main.id_of(x))), amongst(ids, R, rest))

def keep_case(b: Bool, +ids: List<&2, String>, +R: List<&2, String>, +x: Main.Full, +rest: List<&2, Main.Full>, +eb: {Rev.member(R, Main.id_of(x)) == b : Bool}, +hx: {Rev.member(ids, Main.id_of(x)) == True{} : Bool}, ih: {amongst(ids, R, Main.among(rest, R)) == True{} : Bool}) -> {amongst(ids, R, Main.keep_full(b, x, Main.among(rest, R))) == True{} : Bool}:
  match b:
    case True{}:
      AL.and_intro(Bool.and(Rev.member(ids, Main.id_of(x)), Rev.member(R, Main.id_of(x))), amongst(ids, R, Main.among(rest, R)), AL.and_intro(Rev.member(ids, Main.id_of(x)), Rev.member(R, Main.id_of(x)), hx, eb), ih)
    case False{}:
      ih

# What `among` keeps of revisions among `ids` is among `ids`, and in `R`.
def among_ok(+ids: List<&2, String>, +R: List<&2, String>, xs: List<&2, Main.Full>, +hs: {inids(ids, xs) == True{} : Bool}) -> {amongst(ids, R, Main.among(xs, R)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      keep_case(Rev.member(R, Main.id_of(x)), ids, R, x, rest, {==}, Comp.and_left(Rev.member(ids, Main.id_of(x)), inids(ids, rest), hs),
        among_ok(ids, R, rest, Comp.and_right(Rev.member(ids, Main.id_of(x)), inids(ids, rest), hs)))

def from_case(+fs: List<&2, Main.Full>, +a: String, xs: List<&2, Main.Full>, +h: {amongst(Main.ids(fs), Main.reached(fs, a), xs) == True{} : Bool}) -> {Main.span.all_in(fs, Main.Span.From{a}, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Main.span.has(fs, Main.Span.From{a}, Main.id_of(x)), Main.span.all_in(fs, Main.Span.From{a}, rest),
        Comp.and_left(Bool.and(Rev.member(Main.ids(fs), Main.id_of(x)), Rev.member(Main.reached(fs, a), Main.id_of(x))), amongst(Main.ids(fs), Main.reached(fs, a), rest), h),
        from_case(fs, a, rest, Comp.and_right(Bool.and(Rev.member(Main.ids(fs), Main.id_of(x)), Rev.member(Main.reached(fs, a), Main.id_of(x))), amongst(Main.ids(fs), Main.reached(fs, a), rest), h)))

# What `without` keeps is not in what it takes away.
def without_out.of(b: Bool, +y: String, +rest: List<&2, String>, +ys: List<&2, String>, +x: String, +eb: {Rev.member(ys, y) == b : Bool}, m: {Rev.member(Rev.keep(Bool.not(b), y, Rev.without(rest, ys)), x) == True{} : Bool}, ih: {Rev.member(Rev.without(rest, ys), x) == True{} : Bool} -> {Rev.member(ys, x) == False{} : Bool}) -> {Rev.member(ys, x) == False{} : Bool}:
  match b:
    case True{}:
      ih(m)
    case False{}:
      GL.member_cons({Rev.member(ys, x) == False{} : Bool}, y, Rev.without(rest, ys), x, m, h => (%h : {Rev.member(ys, _) == False{} : Bool}; eb), ih)

def without_out(xs: List<&2, String>, +ys: List<&2, String>, +x: String, m: {Rev.member(Rev.without(xs, ys), x) == True{} : Bool}) -> {Rev.member(ys, x) == False{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Rev.member(ys, x) == False{} : Bool}, S.false_true(m))
    case +y <> +rest:
      without_out.of(Rev.member(ys, y), y, rest, ys, x, {==}, m, w => without_out(rest, ys, x, w))

def not_true(-b: Bool, e: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  %Equal.sym(Bool, b, False{}, e) : {Bool.not(_) == True{} : Bool}
  {==}

def between_case(+fs: List<&2, Main.Full>, +from: String, +to: String, xs: List<&2, Main.Full>, +h: {amongst(Main.ids(fs), Rev.without(Main.reached(fs, to), Main.reached(fs, from)), xs) == True{} : Bool}) -> {Main.span.all_in(fs, Main.Span.Between{from, to}, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      +hx = Comp.and_left(Bool.and(Rev.member(Main.ids(fs), Main.id_of(x)), Rev.member(Rev.without(Main.reached(fs, to), Main.reached(fs, from)), Main.id_of(x))), amongst(Main.ids(fs), Rev.without(Main.reached(fs, to), Main.reached(fs, from)), rest), h)
      +mw = Comp.and_right(Rev.member(Main.ids(fs), Main.id_of(x)), Rev.member(Rev.without(Main.reached(fs, to), Main.reached(fs, from)), Main.id_of(x)), hx)
      AL.and_intro(Main.span.has(fs, Main.Span.Between{from, to}, Main.id_of(x)), Main.span.all_in(fs, Main.Span.Between{from, to}, rest),
        AL.and_intro(Rev.member(Main.ids(fs), Main.id_of(x)), Bool.and(Rev.member(Main.reached(fs, to), Main.id_of(x)), Bool.not(Rev.member(Main.reached(fs, from), Main.id_of(x)))),
          Comp.and_left(Rev.member(Main.ids(fs), Main.id_of(x)), Rev.member(Rev.without(Main.reached(fs, to), Main.reached(fs, from)), Main.id_of(x)), hx),
          AL.and_intro(Rev.member(Main.reached(fs, to), Main.id_of(x)), Bool.not(Rev.member(Main.reached(fs, from), Main.id_of(x))),
            GL.without_sub(Main.reached(fs, to), Main.reached(fs, from), Main.id_of(x), mw),
            not_true(Rev.member(Main.reached(fs, from), Main.id_of(x)), without_out(Main.reached(fs, to), Main.reached(fs, from), Main.id_of(x), mw)))),
        between_case(fs, from, to, rest, Comp.and_right(Bool.and(Rev.member(Main.ids(fs), Main.id_of(x)), Rev.member(Rev.without(Main.reached(fs, to), Main.reached(fs, from)), Main.id_of(x))), amongst(Main.ids(fs), Rev.without(Main.reached(fs, to), Main.reached(fs, from)), rest), h)))

# `log` lists only what its span names.
def span_listed(+fs: List<&2, Main.Full>, sp: Main.Span) -> {Main.span.all_in(fs, sp, Main.span.shown(fs, sp)) == True{} : Bool}:
  match sp:
    case Main.Span.All{}:
      all_case(fs, fs, inids_self(fs))
    case Main.Span.From{+a}:
      from_case(fs, a, Main.among(fs, Main.reached(fs, a)), among_ok(Main.ids(fs), Main.reached(fs, a), fs, inids_self(fs)))
    case Main.Span.Between{+from, +to}:
      between_case(fs, from, to, Main.among(fs, Rev.without(Main.reached(fs, to), Main.reached(fs, from))), among_ok(Main.ids(fs), Rev.without(Main.reached(fs, to), Main.reached(fs, from)), fs, inids_self(fs)))
