# What a reading command asks the store and the host for, held to what it
# reads. `diff` over the folder plans every path from the `edit` documents
# it asks for and from nothing else the store holds; a reader that asks,
# after the documents it fetched, for what the resolutions among them keep
# finds every `keep` of theirs; and `diff` asks the host about exactly the
# payloads it shows, each once, and the stat of each only where the host
# located it.
import Base
import ./text.bend as T
import ./tree.bend as Tree
import ./revision.bend as Rev
import ./store.bend as Store
import ./resolution.bend as Res
import ./standin.bend as Stand
import ./commands.bend as Main
import ./anchor_lemmas.bend as AL
import ./composition_lemmas.bend as Comp
import ./graph_lemmas.bend as GL
import ./status_lemmas.bend as StatusL
import ./sort_lemmas.bend as SortL
import ./string_lemmas.bend as S
import ./abbrev_lemmas.bend as AbL

# Where the laws look
# -------------------

# Whether a side is a file of bytes whose payload is `d`.
def side.holds(s: Maybe<&2, Main.Side>, +d: String) -> Bool:
  match s:
    case Some{Main.Side.Whole{e, n}}:
      String.eq(e, d)
    case _:
      False{}

# Whether a comparison among these has a side that is a file of bytes whose
# payload is `d`.
def shows.bytes(cs: List<&2, Main.Compared>, +d: String) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Main.Compared{f, t, b, a, m, g} <> rest:
      Bool.or(Bool.or(side.holds(b, d), side.holds(a, d)), shows.bytes(rest, d))

# No item twice.
def each_once(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> +rest:
      Bool.and(Bool.not(Rev.member(rest, x)), each_once(rest))

# Whether two lists of documents answer each of these digests alike: the
# same text for the first document whose digest begins with it, as
# `doc_by_id` reads one, or none in both.
def agree(+eds: List<&2, Store.Doc>, +all: List<&2, Store.Doc>, ds: List<&2, String>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case +d <> rest:
      Bool.and(Main.maybe_eq(Main.doc_by_id(eds, d), Main.doc_by_id(all, d)), agree(eds, all, rest))

# The digest of each document.
def doc_ids(ds: List<&2, Store.Doc>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Store.Doc{path, id, size, text} <> rest:
      id <> doc_ids(rest)

# Every `keep` among these pieces finds a document under the digest it
# names, as assembling the resolution looks for one.
def pieces.found(+all: List<&2, Store.Doc>, ps: List<&2, Res.Piece>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Res.Piece.Keep{+d, first, count} <> rest:
      Bool.and(Maybe.is_some(&2, String, Stand.text(all, d)), pieces.found(all, rest))
    case Res.Piece.Insert{items} <> rest:
      pieces.found(all, rest)

def parsed.found(+all: List<&2, Store.Doc>, r: Result<&2, &2, String, Res.Doc>) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{Res.Doc{forgets, result, ps}}:
      pieces.found(all, ps)

# Every document among `ds` that reads as a resolution, and parses, has
# every `keep` of it found among `all`.
def kept.found(+all: List<&2, Store.Doc>, ds: List<&2, Store.Doc>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Store.Doc{path, id, size, +text} <> rest:
      Bool.and(Bool.or(Bool.not(Res.is_resolution(text)), parsed.found(all, Res.parse(text))), kept.found(all, rest))

# Whether the host located payload `d` at path `p`: the answer for it,
# among those the host gave for the payloads asked about, in order.
def located.at(ds: List<&2, String>, at: List<&2, String>, +d: String, +p: String) -> Bool:
  match ds at:
    case +x <> xr +y <> yr:
      Bool.or(Bool.and(String.eq(x, d), String.eq(y, p)), located.at(xr, yr, d, p))
    case _ _:
      False{}

# Every payload asked the stat of is paired with a path the host located it
# at, and none with `-`, the answer for a payload it could not find.
def located.each(+ds: List<&2, String>, +at: List<&2, String>, found: List<&2, T.Split>) -> Bool:
  match found:
    case Nil{}:
      True{}
    case T.Split{+d, +p} <> rest:
      Bool.and(Bool.and(located.at(ds, at, d, p), Bool.not(String.eq(p, "-"))), located.each(ds, at, rest))

# Lists
# -----

def ah_left(+docs: List<&2, String>, xs: List<&2, String>, +ys: List<&2, String>, +h: {Main.all_held(docs, List.append(&2, String, xs, ys)) == True{} : Bool}) -> {Main.all_held(docs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Rev.member(docs, x), Main.all_held(docs, rest), Comp.and_left(Rev.member(docs, x), Main.all_held(docs, List.append(&2, String, rest, ys)), h),
        ah_left(docs, rest, ys, Comp.and_right(Rev.member(docs, x), Main.all_held(docs, List.append(&2, String, rest, ys)), h)))

def ah_right(+docs: List<&2, String>, xs: List<&2, String>, +ys: List<&2, String>, +h: {Main.all_held(docs, List.append(&2, String, xs, ys)) == True{} : Bool}) -> {Main.all_held(docs, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +x <> +rest:
      ah_right(docs, rest, ys, Comp.and_right(Rev.member(docs, x), Main.all_held(docs, List.append(&2, String, rest, ys)), h))

def ah_refl(xs: List<&2, String>) -> {Main.all_held(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Rev.member(x <> rest, x), Main.all_held(x <> rest, rest), GL.member_head(x, rest), StatusL.ah_weak(x, rest, rest, ah_refl(rest)))

def held_mem(+ids: List<&2, String>, xs: List<&2, String>, +p: String, +h: {Main.all_held(ids, xs) == True{} : Bool}, m: {Rev.member(xs, p) == True{} : Bool}) -> {Rev.member(ids, p) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Rev.member(ids, p) == True{} : Bool}, S.false_true(m))
    case +x <> +rest:
      GL.member_cons({Rev.member(ids, p) == True{} : Bool}, x, rest, p, m,
        e => GL.member_at(ids, x, p, e, Comp.and_left(Rev.member(ids, x), Main.all_held(ids, rest), h)),
        t => held_mem(ids, rest, p, Comp.and_right(Rev.member(ids, x), Main.all_held(ids, rest), h), t))

def mem_app(xs: List<&2, String>, +ys: List<&2, String>, +d: String) -> {Rev.member(List.append(&2, String, xs, ys), d) == Bool.or(Rev.member(xs, d), Rev.member(ys, d)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, Rev.member(List.append(&2, String, rest, ys), d), Bool.or(Rev.member(rest, d), Rev.member(ys, d)), mem_app(rest, ys, d)) : {Bool.or(String.eq(x, d), _) == Bool.or(Bool.or(String.eq(x, d), Rev.member(rest, d)), Rev.member(ys, d)) : Bool}
      AL.or_assoc(String.eq(x, d), Rev.member(rest, d), Rev.member(ys, d))

def or_false(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# Sorted and each once
# --------------------

def mem_keyed.of(b: Bool, +x: String, +rest: List<&2, String>, +d: String, eb: {String.eq(x, d) == b : Bool}, m: {Bool.or(b, Rev.member(rest, d)) == True{} : Bool}, ih: {Rev.member(rest, d) == True{} : Bool} -> {List.is_empty(&2, String, SortL.keyed(~String, ~(s => s), d, rest)) == False{} : Bool}) -> {List.is_empty(&2, String, Bool.pick(List<&2, String>, b, x <> SortL.keyed(~String, ~(s => s), d, rest), SortL.keyed(~String, ~(s => s), d, rest))) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(m)

# What a list holds, the items it keys under that name hold.
def mem_keyed(xs: List<&2, String>, +d: String, m: {Rev.member(xs, d) == True{} : Bool}) -> {List.is_empty(&2, String, SortL.keyed(~String, ~(s => s), d, xs)) == False{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({List.is_empty(&2, String, Nil{}) == False{} : Bool}, S.false_true(m))
    case +x <> +rest:
      mem_keyed.of(String.eq(x, d), x, rest, d, {==}, m, h => mem_keyed(rest, d, h))

def keyed_mem.of(b: Bool, +x: String, +rest: List<&2, String>, +d: String, h: {List.is_empty(&2, String, Bool.pick(List<&2, String>, b, x <> SortL.keyed(~String, ~(s => s), d, rest), SortL.keyed(~String, ~(s => s), d, rest))) == False{} : Bool}, ih: {List.is_empty(&2, String, SortL.keyed(~String, ~(s => s), d, rest)) == False{} : Bool} -> {Rev.member(rest, d) == True{} : Bool}) -> {Bool.or(b, Rev.member(rest, d)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(h)

def keyed_mem(ys: List<&2, String>, +d: String, h: {List.is_empty(&2, String, SortL.keyed(~String, ~(s => s), d, ys)) == False{} : Bool}) -> {Rev.member(ys, d) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({Rev.member(Nil{}, d) == True{} : Bool}, S.true_false(h))
    case +y <> +rest:
      keyed_mem.of(String.eq(y, d), y, rest, d, h, t => keyed_mem(rest, d, t))

# Sorting keeps every item.
def sort_mem(+xs: List<&2, String>, +d: String, m: {Rev.member(xs, d) == True{} : Bool}) -> {Rev.member(List.sort(~String, ~(a => b => String.is_le(a, b)), xs), d) == True{} : Bool}:
  keyed_mem(List.sort(~String, ~(a => b => String.is_le(a, b)), xs), d,
    (%Equal.sym(List<&2, String>, SortL.keyed(~String, ~(s => s), d, List.sort(~String, ~(a => b => String.is_le(a, b)), xs)), SortL.keyed(~String, ~(s => s), d, xs), SortL.sort_keyed(~String, ~(s => s), xs, d)) : {List.is_empty(&2, String, _) == False{} : Bool}; mem_keyed(xs, d, m)))

# Sorting adds nothing.
def mem_sort(+xs: List<&2, String>, +d: String, m: {Rev.member(List.sort(~String, ~(a => b => String.is_le(a, b)), xs), d) == True{} : Bool}) -> {Rev.member(xs, d) == True{} : Bool}:
  keyed_mem(xs, d,
    (%SortL.sort_keyed(~String, ~(s => s), xs, d) : {List.is_empty(&2, String, _) == False{} : Bool}; mem_keyed(List.sort(~String, ~(a => b => String.is_le(a, b)), xs), d, m)))

def distinct_head(c: Bool, +a: String, +b: String, +rest: List<&2, String>, +d: String, +ec: {String.eq(a, b) == c : Bool}, +ad: {a == d : String}, ih: {Rev.member(b <> rest, b) == True{} : Bool} -> {Rev.member(Main.distinct(b <> rest), b) == True{} : Bool}) -> {Rev.member(Main.distinct.keep(a, Main.distinct(b <> rest), c), d) == True{} : Bool}:
  match c:
    case True{}:
      +ab = S.eq_true(a, b, ec)
      %Equal.trans(String, b, a, d, Equal.sym(String, a, b, ab), ad) : {Rev.member(Main.distinct(b <> rest), _) == True{} : Bool}
      ih(GL.member_head(b, rest))
    case False{}:
      %Equal.sym(String, a, d, ad) : {Rev.member(_ <> Main.distinct(b <> rest), d) == True{} : Bool}
      GL.member_head(d, Main.distinct(b <> rest))

def distinct_rest(c: Bool, +a: String, +b: String, +rest: List<&2, String>, +d: String, m: {Rev.member(Main.distinct(b <> rest), d) == True{} : Bool}) -> {Rev.member(Main.distinct.keep(a, Main.distinct(b <> rest), c), d) == True{} : Bool}:
  match c:
    case True{}:
      m
    case False{}:
      GL.member_tail(a, Main.distinct(b <> rest), d, m)

# Leaving each item once keeps every item.
def distinct_mem(xs: List<&2, String>, +d: String, m: {Rev.member(xs, d) == True{} : Bool}) -> {Rev.member(Main.distinct(xs), d) == True{} : Bool}:
  match xs:
    case Nil{}:
      m
    case +a <> Nil{}:
      m
    case +a <> +b <> +rest:
      GL.member_cons({Rev.member(Main.distinct.keep(a, Main.distinct(b <> rest), String.eq(a, b)), d) == True{} : Bool}, a, b <> rest, d, m,
        h => distinct_head(String.eq(a, b), a, b, rest, d, {==}, h, t => distinct_mem(b <> rest, b, t)),
        t => distinct_rest(String.eq(a, b), a, b, rest, d, distinct_mem(b <> rest, d, t)))

def mem_distinct.keep(c: Bool, +a: String, +b: String, +rest: List<&2, String>, +d: String, m: {Rev.member(Main.distinct.keep(a, Main.distinct(b <> rest), c), d) == True{} : Bool}, ih: {Rev.member(Main.distinct(b <> rest), d) == True{} : Bool} -> {Rev.member(b <> rest, d) == True{} : Bool}) -> {Rev.member(a <> b <> rest, d) == True{} : Bool}:
  match c:
    case True{}:
      GL.member_tail(a, b <> rest, d, ih(m))
    case False{}:
      GL.member_cons({Rev.member(a <> b <> rest, d) == True{} : Bool}, a, Main.distinct(b <> rest), d, m,
        e => GL.member_at(a <> b <> rest, a, d, e, GL.member_head(a, b <> rest)),
        t => GL.member_tail(a, b <> rest, d, ih(t)))

# Leaving each item once adds nothing.
def mem_distinct(xs: List<&2, String>, +d: String, m: {Rev.member(Main.distinct(xs), d) == True{} : Bool}) -> {Rev.member(xs, d) == True{} : Bool}:
  match xs:
    case Nil{}:
      m
    case +a <> Nil{}:
      m
    case +a <> +b <> +rest:
      mem_distinct.keep(String.eq(a, b), a, b, rest, d, m, t => mem_distinct(b <> rest, d, t))

# What a list sorted and each once holds is what the list holds.
def ds_mem(+xs: List<&2, String>, +d: String) -> {Rev.member(Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs)), d) == Rev.member(xs, d) : Bool}:
  GL.bool_iff(Rev.member(Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs)), d), Rev.member(xs, d),
    m => mem_sort(xs, d, mem_distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs), d, m)),
    m => distinct_mem(List.sort(~String, ~(a => b => String.is_le(a, b)), xs), d, sort_mem(xs, d, m)))

# Everything a list holds, the list sorted and each once holds.
def ah_ds(+ys: List<&2, String>, xs: List<&2, String>, +h: {Main.all_held(ys, xs) == True{} : Bool}) -> {Main.all_held(Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), ys)), xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Rev.member(Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), ys)), x), Main.all_held(Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), ys)), rest),
        distinct_mem(List.sort(~String, ~(a => b => String.is_le(a, b)), ys), x, sort_mem(ys, x, Comp.and_left(Rev.member(ys, x), Main.all_held(ys, rest), h))),
        ah_ds(ys, rest, Comp.and_right(Rev.member(ys, x), Main.all_held(ys, rest), h)))

# In a list sorted above `k`, every item is no smaller than `k`.
def sorted_le(ys: List<&2, String>, +k: String, +y: String, +hs: {SortL.sorted.from(~String, ~(s => s), ys, k) == True{} : Bool}, m: {Rev.member(ys, y) == True{} : Bool}) -> {String.is_le(k, y) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({String.is_le(k, y) == True{} : Bool}, S.false_true(m))
    case +z <> +rest:
      +hz = Comp.and_left(String.is_le(k, z), SortL.sorted.from(~String, ~(s => s), rest, z), hs)
      GL.member_cons({String.is_le(k, y) == True{} : Bool}, z, rest, y, m,
        e => (%e : {String.is_le(k, _) == True{} : Bool}; hz),
        t => SortL.str_le(k, z, y, hz, sorted_le(rest, z, y, Comp.and_right(String.is_le(k, z), SortL.sorted.from(~String, ~(s => s), rest, z), hs), t)))

def le_both(c: Cmp, h1: {Cmp.is_le(c) == True{} : Bool}, h2: {Cmp.is_le(SortL.cflip(c)) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, S.false_true(h2))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, S.false_true(h1))

# Two strings each no larger than the other are one.
def le_antisym(+a: String, +b: String, h1: {String.is_le(a, b) == True{} : Bool}, h2: {String.is_le(b, a) == True{} : Bool}) -> {a == b : String}:
  S.order_eq(a, b, le_both(String.order(a, b), h1, (%SortL.str_flip(a, b) : {Cmp.is_le(_) == True{} : Bool}; h2)))

def eq_clash(+a: String, +b: String, e: {a == b : String}, ec: {String.eq(a, b) == False{} : Bool}) -> Empty:
  S.true_false(Equal.trans(Bool, True{}, String.eq(a, b), False{}, (%e : {True{} == String.eq(a, _) : Bool}; Equal.sym(Bool, String.eq(a, a), True{}, S.eq_refl(a))), ec))

def false_of(x: Bool, k: {x == True{} : Bool} -> Empty) -> {x == False{} : Bool}:
  match x:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, k({==}))
    case False{}:
      {==}

# Where a sorted list goes on past `a` to a larger `b`, `a` is not among
# what it keeps of the rest.
def not_after(+a: String, +b: String, +rest: List<&2, String>, +ec: {String.eq(a, b) == False{} : Bool}, +hab: {String.is_le(a, b) == True{} : Bool}, +hs: {SortL.sorted.from(~String, ~(s => s), rest, b) == True{} : Bool}) -> {Bool.not(Rev.member(Main.distinct(b <> rest), a)) == True{} : Bool}:
  AL.not_true(Rev.member(Main.distinct(b <> rest), a), false_of(Rev.member(Main.distinct(b <> rest), a),
    m => GL.member_cons(Empty, b, rest, a, mem_distinct(b <> rest, a, m),
      e => eq_clash(a, b, Equal.sym(String, b, a, e), ec),
      t => eq_clash(a, b, le_antisym(a, b, hab, sorted_le(rest, b, a, hs, t)), ec))))

def once_keep(c: Bool, +a: String, +b: String, +rest: List<&2, String>, ec: {String.eq(a, b) == c : Bool}, hab: {String.is_le(a, b) == True{} : Bool}, hs: {SortL.sorted.from(~String, ~(s => s), rest, b) == True{} : Bool}, ih: {each_once(Main.distinct(b <> rest)) == True{} : Bool}) -> {each_once(Main.distinct.keep(a, Main.distinct(b <> rest), c)) == True{} : Bool}:
  match c:
    case True{}:
      ih
    case False{}:
      AL.and_intro(Bool.not(Rev.member(Main.distinct(b <> rest), a)), each_once(Main.distinct(b <> rest)), not_after(a, b, rest, ec, hab, hs), ih)

# A sorted list, each once, holds no item twice.
def once_sorted(xs: List<&2, String>, +k: String, h: {SortL.sorted.from(~String, ~(s => s), xs, k) == True{} : Bool}) -> {each_once(Main.distinct(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +a <> Nil{}:
      {==}
    case +a <> +b <> +rest:
      +hb = Comp.and_right(String.is_le(k, a), SortL.sorted.from(~String, ~(s => s), b <> rest, a), h)
      once_keep(String.eq(a, b), a, b, rest, {==},
        Comp.and_left(String.is_le(a, b), SortL.sorted.from(~String, ~(s => s), rest, b), hb),
        Comp.and_right(String.is_le(a, b), SortL.sorted.from(~String, ~(s => s), rest, b), hb),
        once_sorted(b <> rest, a, hb))

# The payloads asked about
# ------------------------

def side_mem(s: Maybe<&2, Main.Side>, +d: String) -> {Rev.member(Main.side.payload(s), d) == side.holds(s, d) : Bool}:
  match s:
    case None{}:
      {==}
    case Some{Main.Side.Lines{items}}:
      {==}
    case Some{Main.Side.Whole{+e, n}}:
      or_false(String.eq(e, d))

# A payload is among those `diff` collects exactly where a comparison shows
# it.
def payloads_mem(cs: List<&2, Main.Compared>, +d: String) -> {Rev.member(Main.payloads_of(cs), d) == shows.bytes(cs, d) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Main.Compared{+f, +t, +b, +a, +m, +g} <> +rest:
      +pb = Main.side.payload(b)
      +pa = Main.side.payload(a)
      +pr = Main.payloads_of(rest)
      %Equal.sym(Bool, Rev.member(List.append(&2, String, pb, List.append(&2, String, pa, pr)), d), Bool.or(Rev.member(pb, d), Rev.member(List.append(&2, String, pa, pr), d)), mem_app(pb, List.append(&2, String, pa, pr), d)) : {_ == shows.bytes(Main.Compared{f, t, b, a, m, g} <> rest, d) : Bool}
      %Equal.sym(Bool, Rev.member(List.append(&2, String, pa, pr), d), Bool.or(Rev.member(pa, d), Rev.member(pr, d)), mem_app(pa, pr, d)) : {Bool.or(Rev.member(pb, d), _) == shows.bytes(Main.Compared{f, t, b, a, m, g} <> rest, d) : Bool}
      %Equal.sym(Bool, Rev.member(pb, d), side.holds(b, d), side_mem(b, d)) : {Bool.or(_, Bool.or(Rev.member(pa, d), Rev.member(pr, d))) == shows.bytes(Main.Compared{f, t, b, a, m, g} <> rest, d) : Bool}
      %Equal.sym(Bool, Rev.member(pa, d), side.holds(a, d), side_mem(a, d)) : {Bool.or(side.holds(b, d), Bool.or(_, Rev.member(pr, d))) == shows.bytes(Main.Compared{f, t, b, a, m, g} <> rest, d) : Bool}
      %Equal.sym(Bool, Rev.member(pr, d), shows.bytes(rest, d), payloads_mem(rest, d)) : {Bool.or(side.holds(b, d), Bool.or(side.holds(a, d), _)) == shows.bytes(Main.Compared{f, t, b, a, m, g} <> rest, d) : Bool}
      AL.or_assoc(side.holds(b, d), side.holds(a, d), shows.bytes(rest, d))

# `diff` asks the host about no payload twice.
def payloads_once(+cs: List<&2, Main.Compared>) -> {each_once(Main.payloads.asked(cs)) == True{} : Bool}:
  once_sorted(List.sort(~String, ~(a => b => String.is_le(a, b)), Main.payloads_of(cs)), SNil{}, SortL.sort_sorted(~String, ~(s => s), Main.payloads_of(cs)))

# `diff` asks the host about a payload exactly where a comparison it shows
# has a side that is a file of bytes with that payload.
def payloads_shown(+cs: List<&2, Main.Compared>, +d: String) -> {Rev.member(Main.payloads.asked(cs), d) == shows.bytes(cs, d) : Bool}:
  Equal.trans(Bool, Rev.member(Main.payloads.asked(cs), d), Rev.member(Main.payloads_of(cs), d), shows.bytes(cs, d), ds_mem(Main.payloads_of(cs), d), payloads_mem(cs, d))

# The paths asked about
# ---------------------

def located_weak(+x: String, +y: String, +xr: List<&2, String>, +yr: List<&2, String>, found: List<&2, T.Split>, +h: {located.each(xr, yr, found) == True{} : Bool}) -> {located.each(x <> xr, y <> yr, found) == True{} : Bool}:
  match found:
    case Nil{}:
      {==}
    case T.Split{+d, +p} <> +rest:
      +hd = Comp.and_left(Bool.and(located.at(xr, yr, d, p), Bool.not(String.eq(p, "-"))), located.each(xr, yr, rest), h)
      AL.and_intro(Bool.and(located.at(x <> xr, y <> yr, d, p), Bool.not(String.eq(p, "-"))), located.each(x <> xr, y <> yr, rest),
        AL.and_intro(located.at(x <> xr, y <> yr, d, p), Bool.not(String.eq(p, "-")),
          AL.or_right(Bool.and(String.eq(x, d), String.eq(y, p)), located.at(xr, yr, d, p), Comp.and_left(located.at(xr, yr, d, p), Bool.not(String.eq(p, "-")), hd)),
          Comp.and_right(located.at(xr, yr, d, p), Bool.not(String.eq(p, "-")), hd)),
        located_weak(x, y, xr, yr, rest, Comp.and_right(Bool.and(located.at(xr, yr, d, p), Bool.not(String.eq(p, "-"))), located.each(xr, yr, rest), h)))

def keep_located(missing: Bool, +d: String, +p: String, +rest: List<&2, String>, +more: List<&2, String>, +found: List<&2, T.Split>, +em: {String.eq(p, "-") == missing : Bool}, +h: {located.each(rest, more, found) == True{} : Bool}) -> {located.each(d <> rest, p <> more, Main.sizes.keep(d, p, found, missing)) == True{} : Bool}:
  match missing:
    case True{}:
      located_weak(d, p, rest, more, found, h)
    case False{}:
      AL.and_intro(Bool.and(located.at(d <> rest, p <> more, d, p), Bool.not(String.eq(p, "-"))), located.each(d <> rest, p <> more, found),
        AL.and_intro(located.at(d <> rest, p <> more, d, p), Bool.not(String.eq(p, "-")),
          AL.or_left(Bool.and(String.eq(d, d), String.eq(p, p)), located.at(rest, more, d, p), AL.and_intro(String.eq(d, d), String.eq(p, p), S.eq_refl(d), S.eq_refl(p))),
          (%Equal.sym(Bool, String.eq(p, "-"), False{}, em) : {Bool.not(_) == True{} : Bool}; {==})),
        located_weak(d, p, rest, more, found, h))

# `diff` asks the stat only of paths the host located a payload at, each
# with the payload it located there, and never of a payload it could not
# find.
def sizes_located(+root: String, ds: List<&2, String>, at: List<&2, String>) -> {located.each(ds, at, Main.sizes.of(root, ds, at)) == True{} : Bool}:
  match ds at:
    case +d <> +rest +p <> +more:
      keep_located(String.eq(p, "-"), d, p, rest, more, Main.sizes.of(root, rest, more), {==}, sizes_located(root, rest, more))
    case Nil{} y:
      {==}
    case x <> xr Nil{}:
      {==}

# The plan over the folder
# ------------------------

def meq(a: Maybe<&2, String>, b: Maybe<&2, String>, e: {Main.maybe_eq(a, b) == True{} : Bool}) -> {a == b : Maybe<&2, String>}:
  match a b:
    case None{} None{}:
      {==}
    case Some{+x} Some{+y}:
      %S.eq_true(x, y, e) : {Some{x} == Some{_} : Maybe<&2, String>}
      {==}
    case None{} Some{y}:
      Empty.absurd({None{} == Some{y} : Maybe<&2, String>}, S.false_true(e))
    case Some{x} None{}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, String>}, S.false_true(e))

# A digest the two answer alike is answered alike.
def agree_at(+eds: List<&2, Store.Doc>, +all: List<&2, Store.Doc>, ds: List<&2, String>, +d: String, +h: {agree(eds, all, ds) == True{} : Bool}, m: {Rev.member(ds, d) == True{} : Bool}) -> {Main.doc_by_id(eds, d) == Main.doc_by_id(all, d) : Maybe<&2, String>}:
  match ds:
    case Nil{}:
      Empty.absurd({Main.doc_by_id(eds, d) == Main.doc_by_id(all, d) : Maybe<&2, String>}, S.false_true(m))
    case +x <> +rest:
      GL.member_cons({Main.doc_by_id(eds, d) == Main.doc_by_id(all, d) : Maybe<&2, String>}, x, rest, d, m,
        e => (%e : {Main.doc_by_id(eds, _) == Main.doc_by_id(all, _) : Maybe<&2, String>}; meq(Main.doc_by_id(eds, x), Main.doc_by_id(all, x), Comp.and_left(Main.maybe_eq(Main.doc_by_id(eds, x), Main.doc_by_id(all, x)), agree(eds, all, rest), h))),
        t => agree_at(eds, all, rest, d, Comp.and_right(Main.maybe_eq(Main.doc_by_id(eds, x), Main.doc_by_id(all, x)), agree(eds, all, rest), h), t))

# Where a path is not a file of lines the folder holds a regular file for,
# whether its statement settles it decides nothing.
def plan_of_eq(+h: Main.Here, +digest: String, l: Bool, r: Bool, +s1: Bool, +s2: Bool, same: {Bool.and(l, r) == True{} : Bool} -> {s1 == s2 : Bool}) -> {Main.plan.of(h, digest, l, r, s1) == Main.plan.of(h, digest, l, r, s2) : Main.Planned}:
  match l r:
    case True{} True{}:
      %same({==}) : {Main.plan.of(h, digest, True{}, True{}, s1) == Main.plan.of(h, digest, True{}, True{}, _) : Main.Planned}
      {==}
    case True{} False{}:
      {==}
    case False{} r2:
      {==}

def stated_same.edit(+eds: List<&2, Store.Doc>, +all: List<&2, Store.Doc>, +asked: List<&2, String>, +d: String, e: Bool, +ha: {agree(eds, all, asked) == True{} : Bool}, +sub: {Main.all_held(asked, Main.edit_of.is(d, e)) == True{} : Bool}) -> {Main.stated.edit(eds, d, e) == Main.stated.edit(all, d, e) : Maybe<&2, String>}:
  match e:
    case True{}:
      %agree_at(eds, all, asked, d, ha, held_mem(asked, [d], d, sub, GL.member_head(d, Nil{}))) : {Main.result.doc(Main.doc_by_id(eds, d)) == Main.result.doc(_) : Maybe<&2, String>}
      {==}
    case False{}:
      {==}

def stated_same.by(+eds: List<&2, Store.Doc>, +all: List<&2, Store.Doc>, +asked: List<&2, String>, +k: String, +d: String, t: Bool, +ha: {agree(eds, all, asked) == True{} : Bool}, +sub: {Main.all_held(asked, Main.edit_of.is(d, String.eq(k, "edit"))) == True{} : Bool}) -> {Main.stated.by(eds, k, d, t) == Main.stated.by(all, k, d, t) : Maybe<&2, String>}:
  match t:
    case True{}:
      {==}
    case False{}:
      stated_same.edit(eds, all, asked, d, String.eq(k, "edit"), ha, sub)

# The digest a statement leaves is read from nothing but the `edit`
# document it names, if any.
def stated_same(+eds: List<&2, Store.Doc>, +all: List<&2, Store.Doc>, +asked: List<&2, String>, o: T.Split, +ha: {agree(eds, all, asked) == True{} : Bool}, +sub: {Main.all_held(asked, Main.edit_of.split(o)) == True{} : Bool}) -> {Main.stated_digest(eds, o) == Main.stated_digest(all, o) : Maybe<&2, String>}:
  match o:
    case T.Split{+k, +d}:
      stated_same.by(eds, all, asked, k, d, String.eq(k, "text"), ha, sub)

def edit_at(+os: Map<&2, T.Split>, +h: Main.Here, +asked: List<&2, String>, +e: {Bool.and(Main.here.lines(h), Main.here.regular(h)) == True{} : Bool}, +sub: {Main.all_held(asked, Main.edit_of(os, h, Bool.and(Main.here.lines(h), Main.here.regular(h)))) == True{} : Bool}) -> {Main.all_held(asked, Main.edit_of.split(Main.origin(os, Main.here.file(h)))) == True{} : Bool}:
  %e : {Main.all_held(asked, Main.edit_of(os, h, _)) == True{} : Bool}
  sub

# One path is planned alike from any documents that answer its `edit`
# alike.
def plan_same(+dg: Map<&2, String>, +os: Map<&2, T.Split>, +eds: List<&2, Store.Doc>, +all: List<&2, Store.Doc>, +asked: List<&2, String>, +h: Main.Here, +ha: {agree(eds, all, asked) == True{} : Bool}, +sub: {Main.all_held(asked, Main.edit_of(os, h, Bool.and(Main.here.lines(h), Main.here.regular(h)))) == True{} : Bool}) -> {Main.plan(dg, os, eds, h) == Main.plan(dg, os, all, h) : Main.Planned}:
  +dgst = Main.here.digest(dg, h)
  +o = Main.origin(os, Main.here.file(h))
  plan_of_eq(h, dgst, Main.here.lines(h), Main.here.regular(h), Main.here.same(eds, os, h, dgst), Main.here.same(all, os, h, dgst),
    e => (%stated_same(eds, all, asked, o, ha, edit_at(os, h, asked, e, sub)) : {Main.maybe_eq(Main.stated_digest(eds, o), Some{dgst}) == Main.maybe_eq(_, Some{dgst}) : Bool}; {==}))

def plans_same(+dg: Map<&2, String>, +os: Map<&2, T.Split>, +eds: List<&2, Store.Doc>, +all: List<&2, Store.Doc>, +asked: List<&2, String>, hs: List<&2, Main.Here>, +ha: {agree(eds, all, asked) == True{} : Bool}, +sub: {Main.all_held(asked, Main.edits_of(os, hs)) == True{} : Bool}) -> {Main.plans(dg, os, eds, hs) == Main.plans(dg, os, all, hs) : List<&2, Main.Planned>}:
  match hs:
    case Nil{}:
      {==}
    case +h <> +rest:
      +x = Main.edit_of(os, h, Bool.and(Main.here.lines(h), Main.here.regular(h)))
      +eh = plan_same(dg, os, eds, all, asked, h, ha, ah_left(asked, x, Main.edits_of(os, rest), sub))
      +er = plans_same(dg, os, eds, all, asked, rest, ha, ah_right(asked, x, Main.edits_of(os, rest), sub))
      %eh : {Main.plan(dg, os, eds, h) <> Main.plans(dg, os, eds, rest) == _ <> Main.plans(dg, os, all, rest) : List<&2, Main.Planned>}
      %er : {Main.plan(dg, os, eds, h) <> Main.plans(dg, os, eds, rest) == Main.plan(dg, os, eds, h) <> _ : List<&2, Main.Planned>}
      {==}

# `diff` over the folder plans every path from the store's documents only
# through the `edit` documents it asks for.
def plans_fetched(+dg: Map<&2, String>, +os: Map<&2, T.Split>, +eds: List<&2, Store.Doc>, +all: List<&2, Store.Doc>, +hs: List<&2, Main.Here>, +ha: {agree(eds, all, Main.edits.asked(os, hs)) == True{} : Bool}) -> {Main.plans(dg, os, eds, hs) == Main.plans(dg, os, all, hs) : List<&2, Main.Planned>}:
  plans_same(dg, os, eds, all, Main.edits.asked(os, hs), hs, ha, ah_ds(Main.edits_of(os, hs), Main.edits_of(os, hs), ah_refl(Main.edits_of(os, hs))))

# What resolutions keep
# ---------------------

def sw_refl(s: String) -> {String.starts_with(s, s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      %Equal.sym(Bool, Char.is_eq(c, c), True{}, AbL.char_refl(c)) : {String.starts_with.if(t, t, _) == True{} : Bool}
      sw_refl(t)

def pick_some(b: Bool, +t: String, +rest: Maybe<&2, String>, ih: {Maybe.is_some(&2, String, rest) == True{} : Bool}) -> {Maybe.is_some(&2, String, Bool.pick(Maybe<&2, String>, b, Some{t}, rest)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def pick_hit(b: Bool, +t: String, +rest: Maybe<&2, String>, e: {b == True{} : Bool}) -> {Maybe.is_some(&2, String, Bool.pick(Maybe<&2, String>, b, Some{t}, rest)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Maybe.is_some(&2, String, rest) == True{} : Bool}, S.false_true(e))

# A document under the very digest asked for is found.
def held_in(more: List<&2, Store.Doc>, +d: String, m: {Rev.member(doc_ids(more), d) == True{} : Bool}) -> {Maybe.is_some(&2, String, Stand.held(more, d)) == True{} : Bool}:
  match more:
    case Nil{}:
      Empty.absurd({Maybe.is_some(&2, String, Stand.held(Nil{}, d)) == True{} : Bool}, S.false_true(m))
    case Store.Doc{+path, +i, +size, +text} <> +rest:
      GL.member_cons({Maybe.is_some(&2, String, Bool.pick(Maybe<&2, String>, String.starts_with(i, d), Some{text}, Stand.held(rest, d))) == True{} : Bool}, i, doc_ids(rest), d, m,
        e => pick_hit(String.starts_with(i, d), text, Stand.held(rest, d), (%e : {String.starts_with(i, _) == True{} : Bool}; sw_refl(i))),
        t => pick_some(String.starts_with(i, d), text, Stand.held(rest, d), held_in(rest, d, t)))

# And still found with other documents before it.
def held_app(ds: List<&2, Store.Doc>, +more: List<&2, Store.Doc>, +d: String, +e: {Maybe.is_some(&2, String, Stand.held(more, d)) == True{} : Bool}) -> {Maybe.is_some(&2, String, Stand.held(List.append(&2, Store.Doc, ds, more), d)) == True{} : Bool}:
  match ds:
    case Nil{}:
      e
    case Store.Doc{+path, +i, +size, +text} <> +rest:
      pick_some(String.starts_with(i, d), text, Stand.held(List.append(&2, Store.Doc, rest, more), d), held_app(rest, more, d, e))

# What is held under a digest is what a reader of a `keep` reads there.
def text_held(m: Maybe<&2, String>, +all: List<&2, Store.Doc>, +d: String, em: {Stand.held(all, d) == m : Maybe<&2, String>}, e: {Maybe.is_some(&2, String, m) == True{} : Bool}) -> {Maybe.is_some(&2, String, Stand.text(all, d)) == True{} : Bool}:
  match m:
    case Some{t}:
      %Equal.sym(Maybe<&2, String>, Stand.held(all, d), Some{t}, em) : {Maybe.is_some(&2, String, Stand.text.of(Stand.found.of(all, d, _))) == True{} : Bool}
      {==}
    case None{}:
      Empty.absurd({Maybe.is_some(&2, String, Stand.text(all, d)) == True{} : Bool}, S.false_true(e))

# A document fetched after the first ones is found by a reader of all of
# them.
def found_of(+ds0: List<&2, Store.Doc>, +more: List<&2, Store.Doc>, +d: String, m: {Rev.member(doc_ids(more), d) == True{} : Bool}) -> {Maybe.is_some(&2, String, Stand.text(List.append(&2, Store.Doc, ds0, more), d)) == True{} : Bool}:
  text_held(Stand.held(List.append(&2, Store.Doc, ds0, more), d), List.append(&2, Store.Doc, ds0, more), d, {==}, held_app(ds0, more, d, held_in(more, d, m)))

def pieces_ok(+ds0: List<&2, Store.Doc>, +more: List<&2, Store.Doc>, ps: List<&2, Res.Piece>, +hk: {Main.all_held(doc_ids(more), Res.keeps.of(ps)) == True{} : Bool}) -> {pieces.found(List.append(&2, Store.Doc, ds0, more), ps) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case Res.Piece.Keep{+d, +first, +count} <> +rest:
      AL.and_intro(Maybe.is_some(&2, String, Stand.text(List.append(&2, Store.Doc, ds0, more), d)), pieces.found(List.append(&2, Store.Doc, ds0, more), rest),
        found_of(ds0, more, d, Comp.and_left(Rev.member(doc_ids(more), d), Main.all_held(doc_ids(more), Res.keeps.of(rest)), hk)),
        pieces_ok(ds0, more, rest, Comp.and_right(Rev.member(doc_ids(more), d), Main.all_held(doc_ids(more), Res.keeps.of(rest)), hk)))
    case Res.Piece.Insert{+items} <> +rest:
      pieces_ok(ds0, more, rest, hk)

def parsed_ok(+ds0: List<&2, Store.Doc>, +more: List<&2, Store.Doc>, r: Result<&2, &2, String, Res.Doc>, +hk: {Main.all_held(doc_ids(more), Res.keeps(r)) == True{} : Bool}) -> {parsed.found(List.append(&2, Store.Doc, ds0, more), r) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{Res.Doc{+forgets, +result, +ps}}:
      pieces_ok(ds0, more, ps, hk)

def kept_one(r: Bool, +ds0: List<&2, Store.Doc>, +more: List<&2, Store.Doc>, +text: String, +hk: {Main.all_held(doc_ids(more), Main.kept_digests.of(text, r)) == True{} : Bool}) -> {Bool.or(Bool.not(r), parsed.found(List.append(&2, Store.Doc, ds0, more), Res.parse(text))) == True{} : Bool}:
  match r:
    case True{}:
      parsed_ok(ds0, more, Res.parse(text), hk)
    case False{}:
      {==}

def kept_ok(+ds0: List<&2, Store.Doc>, +more: List<&2, Store.Doc>, ds: List<&2, Store.Doc>, +h: {Main.all_held(doc_ids(more), Main.kept_digests(ds)) == True{} : Bool}) -> {kept.found(List.append(&2, Store.Doc, ds0, more), ds) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Store.Doc{+path, +id, +size, +text} <> +rest:
      +k = Main.kept_digests.of(text, Res.is_resolution(text))
      AL.and_intro(Bool.or(Bool.not(Res.is_resolution(text)), parsed.found(List.append(&2, Store.Doc, ds0, more), Res.parse(text))), kept.found(List.append(&2, Store.Doc, ds0, more), rest),
        kept_one(Res.is_resolution(text), ds0, more, text, ah_left(doc_ids(more), k, Main.kept_digests(rest), h)),
        kept_ok(ds0, more, rest, ah_right(doc_ids(more), k, Main.kept_digests(rest), h)))

# Where the store answers every digest a reader asks for after the
# documents it first fetched with a document under that digest, every
# `keep` of every resolution among those documents finds one.
def kept_found(+ds: List<&2, Store.Doc>, +more: List<&2, Store.Doc>, +h: {Main.all_held(doc_ids(more), Main.kept_digests(ds)) == True{} : Bool}) -> {kept.found(List.append(&2, Store.Doc, ds, more), ds) == True{} : Bool}:
  kept_ok(ds, more, ds, h)
