# What `merge` joins: every revision it joins is one the store holds, and
# every current head is among them.
import Base
import ./text.bend as T
import ./revision.bend as Rev
import ./bookmark.bend as Bm
import ./commands.bend as Main
import ./update.bend as Upd
import ./merging.bend as M
import ./tree.bend as Tree
import ./conflict.bend as Conflict
import ./sort_lemmas.bend as SortL
import ./status_lemmas.bend as StatusL
import ./blamed_lemmas.bend as B
import ./anchor_lemmas.bend as AL
import ./composition_lemmas.bend as Comp
import ./string_lemmas.bend as S

# Lists of heads
# --------------

def ids_app(xs: List<&2, T.Split>, +ys: List<&2, T.Split>) -> {M.typed.ids(List.append(&2, T.Split, xs, ys)) == List.append(&2, String, M.typed.ids(xs), M.typed.ids(ys)) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case T.Split{+h, +s} <> +rest:
      %Equal.sym(List<&2, String>, M.typed.ids(List.append(&2, T.Split, rest, ys)), List.append(&2, String, M.typed.ids(rest), M.typed.ids(ys)), ids_app(rest, ys)) : {h <> _ == h <> List.append(&2, String, M.typed.ids(rest), M.typed.ids(ys)) : List<&2, String>}
      {==}

# A head is among the digests joined exactly where it is among the heads.
def mem_ids(ys: List<&2, T.Split>, +h: String) -> {Rev.member(M.typed.ids(ys), h) == M.typed.has(ys, h) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case T.Split{+k, +s} <> +rest:
      %Equal.sym(Bool, Rev.member(M.typed.ids(rest), h), M.typed.has(rest, h), mem_ids(rest, h)) : {Bool.or(String.eq(k, h), _) == Bool.or(String.eq(k, h), M.typed.has(rest, h)) : Bool}
      {==}

# Every current head is joined
# ----------------------------

# A head added is there, and so is every head there before.
def has_last(xs: List<&2, T.Split>, +id: String, +s: String) -> {M.typed.has(List.append(&2, T.Split, xs, [T.Split{id, s}]), id) == True{} : Bool}:
  match xs:
    case Nil{}:
      AL.or_left(String.eq(id, id), False{}, S.eq_refl(id))
    case T.Split{+h, +k} <> +rest:
      AL.or_right(String.eq(h, id), M.typed.has(List.append(&2, T.Split, rest, [T.Split{id, s}]), id), has_last(rest, id, s))

def has_app(xs: List<&2, T.Split>, +ys: List<&2, T.Split>, +y: String, +h: {M.typed.has(xs, y) == True{} : Bool}) -> {M.typed.has(List.append(&2, T.Split, xs, ys), y) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({M.typed.has(ys, y) == True{} : Bool}, Comp.false_true(h))
    case T.Split{+k, +s} <> +rest:
      AL.or_cases({M.typed.has(List.append(&2, T.Split, T.Split{k, s} <> rest, ys), y) == True{} : Bool}, String.eq(k, y), M.typed.has(rest, y), h,
        l => AL.or_left(String.eq(k, y), M.typed.has(List.append(&2, T.Split, rest, ys), y), l),
        r => AL.or_right(String.eq(k, y), M.typed.has(List.append(&2, T.Split, rest, ys), y), has_app(rest, ys, y, r)))

def add_has.pick(b: Bool, +xs: List<&2, T.Split>, +id: String, +s: String, +eb: {M.typed.has(xs, id) == b : Bool}) -> {M.typed.has(Bool.pick(List<&2, T.Split>, b, xs, List.append(&2, T.Split, xs, [T.Split{id, s}])), id) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      has_last(xs, id, s)

def add_has(+xs: List<&2, T.Split>, +id: String, +s: String) -> {M.typed.has(M.typed.add(xs, id, s), id) == True{} : Bool}:
  add_has.pick(M.typed.has(xs, id), xs, id, s, {==})

def add_keeps.pick(b: Bool, +xs: List<&2, T.Split>, +id: String, +s: String, +y: String, +h: {M.typed.has(xs, y) == True{} : Bool}) -> {M.typed.has(Bool.pick(List<&2, T.Split>, b, xs, List.append(&2, T.Split, xs, [T.Split{id, s}])), y) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      has_app(xs, [T.Split{id, s}], y, h)

def add_keeps(+xs: List<&2, T.Split>, +id: String, +s: String, +y: String, +h: {M.typed.has(xs, y) == True{} : Bool}) -> {M.typed.has(M.typed.add(xs, id, s), y) == True{} : Bool}:
  add_keeps.pick(M.typed.has(xs, id), xs, id, s, y, h)

def standing_keeps(hs: List<&2, String>, +acc: List<&2, T.Split>, +y: String, +h: {M.typed.has(acc, y) == True{} : Bool}) -> {M.typed.has(M.typed.standing(hs, acc), y) == True{} : Bool}:
  match hs:
    case Nil{}:
      h
    case +x <> +rest:
      standing_keeps(rest, M.typed.add(acc, x, String.take(x, 12n)), y, add_keeps(acc, x, String.take(x, 12n), y, h))

def has_mem(+ys: List<&2, T.Split>, +h: String, +e: {M.typed.has(ys, h) == True{} : Bool}) -> {Rev.member(M.typed.ids(ys), h) == True{} : Bool}:
  %Equal.sym(Bool, Rev.member(M.typed.ids(ys), h), M.typed.has(ys, h), mem_ids(ys, h)) : {_ == True{} : Bool}
  e

# Every head a merge stands among joins it.
def standing_all(hs: List<&2, String>, +acc: List<&2, T.Split>) -> {Main.all_held(M.typed.ids(M.typed.standing(hs, acc)), hs) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Rev.member(M.typed.ids(M.typed.standing(rest, M.typed.add(acc, x, String.take(x, 12n)))), x), Main.all_held(M.typed.ids(M.typed.standing(rest, M.typed.add(acc, x, String.take(x, 12n)))), rest),
        has_mem(M.typed.standing(rest, M.typed.add(acc, x, String.take(x, 12n))), x, standing_keeps(rest, M.typed.add(acc, x, String.take(x, 12n)), x, add_has(acc, x, String.take(x, 12n)))),
        standing_all(rest, M.typed.add(acc, x, String.take(x, 12n))))

# A sort by digest keeps every head: what is under each digest is what was.
def keyed_pick(b: Bool, +k: String, +s: String, +rest: List<&2, T.Split>, +h: String, +eb: {String.eq(k, h) == b : Bool}, ih: {M.typed.has(rest, h) == Bool.not(List.is_empty(&2, T.Split, SortL.keyed(~T.Split, ~(a => M.typed.key(a)), h, rest))) : Bool}) -> {Bool.or(String.eq(k, h), M.typed.has(rest, h)) == Bool.not(List.is_empty(&2, T.Split, Bool.pick(List<&2, T.Split>, String.eq(k, h), T.Split{k, s} <> SortL.keyed(~T.Split, ~(a => M.typed.key(a)), h, rest), SortL.keyed(~T.Split, ~(a => M.typed.key(a)), h, rest)))) : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, String.eq(k, h), True{}, eb) : {Bool.or(_, M.typed.has(rest, h)) == Bool.not(List.is_empty(&2, T.Split, Bool.pick(List<&2, T.Split>, _, T.Split{k, s} <> SortL.keyed(~T.Split, ~(a => M.typed.key(a)), h, rest), SortL.keyed(~T.Split, ~(a => M.typed.key(a)), h, rest)))) : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, String.eq(k, h), False{}, eb) : {Bool.or(_, M.typed.has(rest, h)) == Bool.not(List.is_empty(&2, T.Split, Bool.pick(List<&2, T.Split>, _, T.Split{k, s} <> SortL.keyed(~T.Split, ~(a => M.typed.key(a)), h, rest), SortL.keyed(~T.Split, ~(a => M.typed.key(a)), h, rest)))) : Bool}
      ih

def has_keyed(zs: List<&2, T.Split>, +h: String) -> {M.typed.has(zs, h) == Bool.not(List.is_empty(&2, T.Split, SortL.keyed(~T.Split, ~(a => M.typed.key(a)), h, zs))) : Bool}:
  match zs:
    case Nil{}:
      {==}
    case T.Split{+k, +s} <> +rest:
      keyed_pick(String.eq(k, h), k, s, rest, h, {==}, has_keyed(rest, h))

def sort_has(+xs: List<&2, T.Split>, +h: String) -> {M.typed.has(List.sort(~T.Split, ~(a => b => String.is_le(M.typed.key(a), M.typed.key(b))), xs), h) == M.typed.has(xs, h) : Bool}:
  %Equal.sym(Bool, M.typed.has(List.sort(~T.Split, ~(a => b => String.is_le(M.typed.key(a), M.typed.key(b))), xs), h), Bool.not(List.is_empty(&2, T.Split, SortL.keyed(~T.Split, ~(a => M.typed.key(a)), h, List.sort(~T.Split, ~(a => b => String.is_le(M.typed.key(a), M.typed.key(b))), xs)))), has_keyed(List.sort(~T.Split, ~(a => b => String.is_le(M.typed.key(a), M.typed.key(b))), xs), h)) : {_ == M.typed.has(xs, h) : Bool}
  %Equal.sym(List<&2, T.Split>, SortL.keyed(~T.Split, ~(a => M.typed.key(a)), h, List.sort(~T.Split, ~(a => b => String.is_le(M.typed.key(a), M.typed.key(b))), xs)), SortL.keyed(~T.Split, ~(a => M.typed.key(a)), h, xs), SortL.sort_keyed(~T.Split, ~(a => M.typed.key(a)), xs, h)) : {Bool.not(List.is_empty(&2, T.Split, _)) == M.typed.has(xs, h) : Bool}
  %Equal.sym(Bool, M.typed.has(xs, h), Bool.not(List.is_empty(&2, T.Split, SortL.keyed(~T.Split, ~(a => M.typed.key(a)), h, xs))), has_keyed(xs, h)) : {Bool.not(List.is_empty(&2, T.Split, SortL.keyed(~T.Split, ~(a => M.typed.key(a)), h, xs))) == _ : Bool}
  {==}

def mem_has(+xs: List<&2, T.Split>, +x: String, +h: {Rev.member(M.typed.ids(xs), x) == True{} : Bool}) -> {M.typed.has(xs, x) == True{} : Bool}:
  %mem_ids(xs, x) : {_ == True{} : Bool}
  h

def sorted_has(+xs: List<&2, T.Split>, +x: String, +e: {M.typed.has(xs, x) == True{} : Bool}) -> {M.typed.has(List.sort(~T.Split, ~(a => b => String.is_le(M.typed.key(a), M.typed.key(b))), xs), x) == True{} : Bool}:
  %Equal.sym(Bool, M.typed.has(List.sort(~T.Split, ~(a => b => String.is_le(M.typed.key(a), M.typed.key(b))), xs), x), M.typed.has(xs, x), sort_has(xs, x)) : {_ == True{} : Bool}
  e

def sort_all(hs: List<&2, String>, +xs: List<&2, T.Split>, +h: {Main.all_held(M.typed.ids(xs), hs) == True{} : Bool}) -> {Main.all_held(M.typed.ids(List.sort(~T.Split, ~(a => b => String.is_le(M.typed.key(a), M.typed.key(b))), xs)), hs) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Rev.member(M.typed.ids(List.sort(~T.Split, ~(a => b => String.is_le(M.typed.key(a), M.typed.key(b))), xs)), x), Main.all_held(M.typed.ids(List.sort(~T.Split, ~(a => b => String.is_le(M.typed.key(a), M.typed.key(b))), xs)), rest),
        has_mem(List.sort(~T.Split, ~(a => b => String.is_le(M.typed.key(a), M.typed.key(b))), xs), x, sorted_has(xs, x, mem_has(xs, x, Comp.and_left(Rev.member(M.typed.ids(xs), x), Main.all_held(M.typed.ids(xs), rest), h)))),
        sort_all(rest, xs, Comp.and_right(Rev.member(M.typed.ids(xs), x), Main.all_held(M.typed.ids(xs), rest), h)))

def enough_all(b: Bool, +hs: List<&2, String>, +ys: List<&2, T.Split>, +xs: List<&2, T.Split>, +h: {Main.all_held(M.typed.ids(ys), hs) == True{} : Bool}, e: {Bool.pick(Result<&2, &2, Main.Refused, List<&2, T.Split>>, b, Fail{Main.Refused{1, "merging is joining two lines of work, and this store has one; name the other, or record on both sides first"}}, Done{List.sort(~T.Split, ~(a => b => String.is_le(M.typed.key(a), M.typed.key(b))), ys)}) == Done{xs} : Result<&2, &2, Main.Refused, List<&2, T.Split>>}) -> {Main.all_held(M.typed.ids(xs), hs) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Main.all_held(M.typed.ids(xs), hs) == True{} : Bool}, B.fail_done(List<&2, T.Split>, Main.Refused{1, "merging is joining two lines of work, and this store has one; name the other, or record on both sides first"}, xs, e))
    case False{}:
      %B.done_eq(List<&2, T.Split>, List.sort(~T.Split, ~(a => b => String.is_le(M.typed.key(a), M.typed.key(b))), ys), xs, e) : {Main.all_held(M.typed.ids(_), hs) == True{} : Bool}
      sort_all(hs, ys, h)

def joined_all.bind(+fs: List<&2, Main.Full>, r: Result<&2, &2, Main.Refused, List<&2, T.Split>>, +xs: List<&2, T.Split>, e: {Result.bind(&2, &2, Main.Refused, List<&2, T.Split>, List<&2, T.Split>, r, named => M.typed.enough(M.typed.standing(Upd.heads.sorted(fs), named))) == Done{xs} : Result<&2, &2, Main.Refused, List<&2, T.Split>>}) -> {Main.all_held(M.typed.ids(xs), Upd.heads.sorted(fs)) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.all_held(M.typed.ids(xs), Upd.heads.sorted(fs)) == True{} : Bool}, B.fail_done(List<&2, T.Split>, x, xs, e))
    case Done{+named}:
      enough_all(Nat.is_lt(List.length(&2, T.Split, M.typed.standing(Upd.heads.sorted(fs), named)), 2n), Upd.heads.sorted(fs), M.typed.standing(Upd.heads.sorted(fs), named), xs, standing_all(Upd.heads.sorted(fs), named), e)

# `merge` joins every current head, named or not.
def joined_all(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +ss: List<&2, String>, +xs: List<&2, T.Split>, e: {M.joined.r(fs, bs, ss) == Done{xs} : Result<&2, &2, Main.Refused, List<&2, T.Split>>}) -> {Main.all_held(M.typed.ids(xs), Upd.heads.sorted(fs)) == True{} : Bool}:
  joined_all.bind(fs, M.typed.named(fs, bs, ss, Nil{}), xs, e)

# Every revision it joins is held
# -------------------------------

def add_pick(b: Bool, +ids: List<&2, String>, +xs: List<&2, T.Split>, +id: String, +s: String, +hx: {Main.all_held(ids, M.typed.ids(xs)) == True{} : Bool}, +hid: {Rev.member(ids, id) == True{} : Bool}) -> {Main.all_held(ids, M.typed.ids(Bool.pick(List<&2, T.Split>, b, xs, List.append(&2, T.Split, xs, [T.Split{id, s}])))) == True{} : Bool}:
  match b:
    case True{}:
      hx
    case False{}:
      %Equal.sym(List<&2, String>, M.typed.ids(List.append(&2, T.Split, xs, [T.Split{id, s}])), List.append(&2, String, M.typed.ids(xs), [id]), ids_app(xs, [T.Split{id, s}])) : {Main.all_held(ids, _) == True{} : Bool}
      StatusL.ah_app(ids, M.typed.ids(xs), [id], hx, StatusL.one_held(ids, id, hid))

def add_held(+ids: List<&2, String>, +xs: List<&2, T.Split>, +id: String, +s: String, +hx: {Main.all_held(ids, M.typed.ids(xs)) == True{} : Bool}, +hid: {Rev.member(ids, id) == True{} : Bool}) -> {Main.all_held(ids, M.typed.ids(M.typed.add(xs, id, s))) == True{} : Bool}:
  add_pick(M.typed.has(xs, id), ids, xs, id, s, hx, hid)

def named_bind(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +s: String, +rest: List<&2, String>, +acc: List<&2, T.Split>, +hacc: {Main.all_held(Main.ids(fs), M.typed.ids(acc)) == True{} : Bool}, r: Result<&2, &2, Main.Refused, Main.Full>, +er: {Main.resolved.r(fs, bs, s) == r : Result<&2, &2, Main.Refused, Main.Full>}, +xs: List<&2, T.Split>, e: {Result.bind(&2, &2, Main.Refused, Main.Full, List<&2, T.Split>, r, f => M.typed.named(fs, bs, rest, M.typed.add(acc, Main.id_of(f), s))) == Done{xs} : Result<&2, &2, Main.Refused, List<&2, T.Split>>}, ih: @acc2: List<&2, T.Split> -> {Main.all_held(Main.ids(fs), M.typed.ids(acc2)) == True{} : Bool} -> {M.typed.named(fs, bs, rest, acc2) == Done{xs} : Result<&2, &2, Main.Refused, List<&2, T.Split>>} -> {Main.all_held(Main.ids(fs), M.typed.ids(xs)) == True{} : Bool}) -> {Main.all_held(Main.ids(fs), M.typed.ids(xs)) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.all_held(Main.ids(fs), M.typed.ids(xs)) == True{} : Bool}, B.fail_done(List<&2, T.Split>, x, xs, e))
    case Done{+f}:
      ih(M.typed.add(acc, Main.id_of(f), s), add_held(Main.ids(fs), acc, Main.id_of(f), s, hacc, B.resolved_mem(fs, bs, s, f, er)), e)

# What is named resolves to revisions the store holds.
def named_held(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, ss: List<&2, String>, +acc: List<&2, T.Split>, +hacc: {Main.all_held(Main.ids(fs), M.typed.ids(acc)) == True{} : Bool}, +xs: List<&2, T.Split>, e: {M.typed.named(fs, bs, ss, acc) == Done{xs} : Result<&2, &2, Main.Refused, List<&2, T.Split>>}) -> {Main.all_held(Main.ids(fs), M.typed.ids(xs)) == True{} : Bool}:
  match ss:
    case Nil{}:
      %B.done_eq(List<&2, T.Split>, acc, xs, e) : {Main.all_held(Main.ids(fs), M.typed.ids(_)) == True{} : Bool}
      hacc
    case +s <> +rest:
      named_bind(fs, bs, s, rest, acc, hacc, Main.resolved.r(fs, bs, s), {==}, xs, e, a2 => h2 => e2 => named_held(fs, bs, rest, a2, h2, xs, e2))

# Every current head is held.
def weaken(xs: List<&2, String>, +y: String, +l: List<&2, String>, +h: {Main.all_held(l, xs) == True{} : Bool}) -> {Main.all_held(y <> l, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Rev.member(y <> l, x), Main.all_held(y <> l, rest),
        AL.or_right(String.eq(y, x), Rev.member(l, x), Comp.and_left(Rev.member(l, x), Main.all_held(l, rest), h)),
        weaken(rest, y, l, Comp.and_right(Rev.member(l, x), Main.all_held(l, rest), h)))

def held_self(l: List<&2, String>) -> {Main.all_held(l, l) == True{} : Bool}:
  match l:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Rev.member(x <> rest, x), Main.all_held(x <> rest, rest),
        AL.or_left(String.eq(x, x), Rev.member(rest, x), S.eq_refl(x)),
        weaken(rest, x, rest, held_self(rest)))

def held_cur(xs: List<&2, String>, +fs: List<&2, Main.Full>, +hx: {Main.all_held(Main.current_heads(Main.history(fs)), xs) == True{} : Bool}) -> {Main.all_held(Main.ids(fs), xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Rev.member(Main.ids(fs), x), Main.all_held(Main.ids(fs), rest),
        B.cur_held(fs, x, Comp.and_left(Rev.member(Main.current_heads(Main.history(fs)), x), Main.all_held(Main.current_heads(Main.history(fs)), rest), hx)),
        held_cur(rest, fs, Comp.and_right(Rev.member(Main.current_heads(Main.history(fs)), x), Main.all_held(Main.current_heads(Main.history(fs)), rest), hx)))

def heads_held(+fs: List<&2, Main.Full>) -> {Main.all_held(Main.ids(fs), Upd.heads.sorted(fs)) == True{} : Bool}:
  StatusL.ah_sort(~(a => b => String.is_le(a, b)), Main.ids(fs), Main.current_heads(Main.history(fs)),
    held_cur(Main.current_heads(Main.history(fs)), fs, held_self(Main.current_heads(Main.history(fs)))))

def standing_held(hs: List<&2, String>, +ids: List<&2, String>, +acc: List<&2, T.Split>, +hh: {Main.all_held(ids, hs) == True{} : Bool}, +hacc: {Main.all_held(ids, M.typed.ids(acc)) == True{} : Bool}) -> {Main.all_held(ids, M.typed.ids(M.typed.standing(hs, acc))) == True{} : Bool}:
  match hs:
    case Nil{}:
      hacc
    case +h <> +rest:
      standing_held(rest, ids, M.typed.add(acc, h, String.take(h, 12n)), Comp.and_right(Rev.member(ids, h), Main.all_held(ids, rest), hh),
        add_held(ids, acc, h, String.take(h, 12n), hacc, Comp.and_left(Rev.member(ids, h), Main.all_held(ids, rest), hh)))

# A sort by digest keeps every head held.
def at_held(+ids: List<&2, String>, xs: List<&2, T.Split>) -> {SortL.all_at(~T.Split, ~List<&2, String>, ~(c => a => Rev.member(c, M.typed.key(a))), ids, xs) == Main.all_held(ids, M.typed.ids(xs)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case T.Split{+h, +s} <> +rest:
      %Equal.sym(Bool, SortL.all_at(~T.Split, ~List<&2, String>, ~(c => a => Rev.member(c, M.typed.key(a))), ids, rest), Main.all_held(ids, M.typed.ids(rest)), at_held(ids, rest)) : {Bool.and(Rev.member(ids, h), _) == Bool.and(Rev.member(ids, h), Main.all_held(ids, M.typed.ids(rest))) : Bool}
      {==}

def at_of(+ids: List<&2, String>, +xs: List<&2, T.Split>, +hx: {Main.all_held(ids, M.typed.ids(xs)) == True{} : Bool}) -> {SortL.all_at(~T.Split, ~List<&2, String>, ~(c => a => Rev.member(c, M.typed.key(a))), ids, xs) == True{} : Bool}:
  %Equal.sym(Bool, SortL.all_at(~T.Split, ~List<&2, String>, ~(c => a => Rev.member(c, M.typed.key(a))), ids, xs), Main.all_held(ids, M.typed.ids(xs)), at_held(ids, xs)) : {_ == True{} : Bool}
  hx

def sorted_held(+ids: List<&2, String>, +xs: List<&2, T.Split>, +hx: {Main.all_held(ids, M.typed.ids(xs)) == True{} : Bool}) -> {Main.all_held(ids, M.typed.ids(List.sort(~T.Split, ~(a => b => String.is_le(M.typed.key(a), M.typed.key(b))), xs))) == True{} : Bool}:
  %at_held(ids, List.sort(~T.Split, ~(a => b => String.is_le(M.typed.key(a), M.typed.key(b))), xs)) : {_ == True{} : Bool}
  SortL.all_sort_at(~T.Split, ~(a => b => String.is_le(M.typed.key(a), M.typed.key(b))), ~List<&2, String>, ~(c => a => Rev.member(c, M.typed.key(a))), ids, xs, at_of(ids, xs, hx))

def enough_pick(b: Bool, +ids: List<&2, String>, +xs: List<&2, T.Split>, +ys: List<&2, T.Split>, +hx: {Main.all_held(ids, M.typed.ids(xs)) == True{} : Bool}, e: {Bool.pick(Result<&2, &2, Main.Refused, List<&2, T.Split>>, b, Fail{Main.Refused{1, "merging is joining two lines of work, and this store has one; name the other, or record on both sides first"}}, Done{List.sort(~T.Split, ~(a => b => String.is_le(M.typed.key(a), M.typed.key(b))), xs)}) == Done{ys} : Result<&2, &2, Main.Refused, List<&2, T.Split>>}) -> {Main.all_held(ids, M.typed.ids(ys)) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Main.all_held(ids, M.typed.ids(ys)) == True{} : Bool}, B.fail_done(List<&2, T.Split>, Main.Refused{1, "merging is joining two lines of work, and this store has one; name the other, or record on both sides first"}, ys, e))
    case False{}:
      %B.done_eq(List<&2, T.Split>, List.sort(~T.Split, ~(a => b => String.is_le(M.typed.key(a), M.typed.key(b))), xs), ys, e) : {Main.all_held(ids, M.typed.ids(_)) == True{} : Bool}
      sorted_held(ids, xs, hx)

def joined_bind(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +ss: List<&2, String>, r: Result<&2, &2, Main.Refused, List<&2, T.Split>>, +er: {M.typed.named(fs, bs, ss, Nil{}) == r : Result<&2, &2, Main.Refused, List<&2, T.Split>>}, +xs: List<&2, T.Split>, e: {Result.bind(&2, &2, Main.Refused, List<&2, T.Split>, List<&2, T.Split>, r, named => M.typed.enough(M.typed.standing(Upd.heads.sorted(fs), named))) == Done{xs} : Result<&2, &2, Main.Refused, List<&2, T.Split>>}) -> {Main.all_held(Main.ids(fs), M.typed.ids(xs)) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.all_held(Main.ids(fs), M.typed.ids(xs)) == True{} : Bool}, B.fail_done(List<&2, T.Split>, x, xs, e))
    case Done{+named}:
      enough_pick(Nat.is_lt(List.length(&2, T.Split, M.typed.standing(Upd.heads.sorted(fs), named)), 2n), Main.ids(fs), M.typed.standing(Upd.heads.sorted(fs), named), xs,
        standing_held(Upd.heads.sorted(fs), Main.ids(fs), named, heads_held(fs), named_held(fs, bs, ss, Nil{}, {==}, named, er)), e)

# `merge` joins only revisions the store holds.
def joined_held(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +ss: List<&2, String>, +xs: List<&2, T.Split>, e: {M.joined.r(fs, bs, ss) == Done{xs} : Result<&2, &2, Main.Refused, List<&2, T.Split>>}) -> {Main.all_held(Main.ids(fs), M.typed.ids(xs)) == True{} : Bool}:
  joined_bind(fs, bs, ss, M.typed.named(fs, bs, ss, Nil{}), {==}, xs, e)

# What it writes over
# -------------------

# A decision to write that is not a refusal to: what stood there is one of
# the versions the decision was made against, or nothing.
def nand(a: Bool, b: Bool, e: {Bool.and(Bool.not(a), Bool.not(b)) == False{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a b:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(Equal.sym(Bool, True{}, False{}, e)))

def lines_ok(text: Bool, a: Bool, b: Bool, e: {Bool.and(text, Bool.and(Bool.not(a), Bool.not(b))) == False{} : Bool}) -> {Bool.or(Bool.not(text), Bool.or(a, b)) == True{} : Bool}:
  match text:
    case False{}:
      {==}
    case True{}:
      nand(a, b, e)

# What a place says nothing about: a line said, or where the Rust tool stops.
def cat_ok(+p: M.Place, +at: String, cs: List<&2, Tree.Claim>) -> {M.laid.all(p, M.claims.cat(at, cs)) == True{} : Bool}:
  match p cs:
    case M.Place{+e, +pat, +held, +h, +heads, +text, +r} Nil{}:
      {==}
    case M.Place{+e, +pat, +held, +h, +heads, +text, +r} Tree.Claim{by, w} <> rest:
      cat_ok(M.Place{e, pat, held, h, heads, text, r}, at, rest)

def link_pick(c: Bool, +p: M.Place, +at: String, +s: String) -> {M.laid.all(p, Bool.pick(List<&2, M.Act>, c, Nil{}, [M.Act.Link{at, s}])) == True{} : Bool}:
  match c p:
    case True{} _:
      {==}
    case False{} M.Place{e, pat, held, h, heads, text, r}:
      {==}

def link_ok(+p: M.Place, +at: String, h: Upd.Held, want: Maybe<&2, String>) -> {M.laid.all(p, M.laid.acts(M.lay.link(at, h, want))) == True{} : Bool}:
  match p want:
    case M.Place{e, pat, held, hh, heads, text, r} None{}:
      {==}
    case M.Place{+e, +pat, +held, +hh, +heads, +text, +r} Some{+s}:
      link_pick(Upd.lands.link(s, h), M.Place{e, pat, held, hh, heads, text, r}, at, s)

def whole_written(c: Bool, +f: String, +p2: String, +y: Maybe<&2, String>, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, +at: String, +held: String, +h: Upd.Held, +hs: List<&2, String>, +x: Bool, +r: Result<&2, &2, String, Conflict.Joined>, +from: String, +pay: String, +ec: {M.unrecorded(held, pay <> hs) == c : Bool}) -> {M.laid.all(M.Place{Tree.Entry{f, p2, Tree.Whole{}, y, g, m}, at, held, h, hs, x, r}, Bool.pick(List<&2, M.Act>, c, [M.Act.Said{M.UNRECORDED(at)}], [M.Act.Whole{at, from, pay, m}])) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, String.eq(at, at), True{}, S.eq_refl(at)) : {Bool.and(Bool.and(_, Bool.or(String.eq(held, "-"), Rev.member(pay <> hs, held))), True{}) == True{} : Bool}
      %Equal.sym(Bool, Bool.or(String.eq(held, "-"), Rev.member(pay <> hs, held)), True{}, nand(String.eq(held, "-"), Rev.member(pay <> hs, held), ec)) : {Bool.and(Bool.and(True{}, _), True{}) == True{} : Bool}
      {==}

def whole_found(c: Bool, +f: String, +p2: String, +y: Maybe<&2, String>, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, +at: String, +held: String, +h: Upd.Held, +hs: List<&2, String>, +x: Bool, +r: Result<&2, &2, String, Conflict.Joined>, +from: String, +pay: String) -> {M.laid.all(M.Place{Tree.Entry{f, p2, Tree.Whole{}, y, g, m}, at, held, h, hs, x, r}, Bool.pick(List<&2, M.Act>, c, [M.Act.Stop{"this store does not hold the content " ++ pay}], Bool.pick(List<&2, M.Act>, M.unrecorded(held, pay <> hs), [M.Act.Said{M.UNRECORDED(at)}], [M.Act.Whole{at, from, pay, m}]))) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      whole_written(M.unrecorded(held, pay <> hs), f, p2, y, g, m, at, held, h, hs, x, r, from, pay, {==})

def whole_ok(+cs: List<&2, Tree.Contest>, +located: Map<&2, String>, +f: String, +p2: String, y: Maybe<&2, String>, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, +at: String, +held: String, +h: Upd.Held, +hs: List<&2, String>, +x: Bool, +r: Result<&2, &2, String, Conflict.Joined>) -> {M.laid.all(M.Place{Tree.Entry{f, p2, Tree.Whole{}, y, g, m}, at, held, h, hs, x, r}, M.laid.acts(M.lay.whole(at, f, cs, located, held, hs, m, y))) == True{} : Bool}:
  match y:
    case None{}:
      cat_ok(M.Place{Tree.Entry{f, p2, Tree.Whole{}, None{}, g, m}, at, held, h, hs, x, r}, at, M.payload.claims(cs, f))
    case Some{+pay}:
      whole_found(String.is_empty(Main.stat_of(pay, Map.get(String, SNil{}, located, pay))), f, p2, Some{pay}, g, m, at, held, h, hs, x, r, Main.stat_of(pay, Map.get(String, SNil{}, located, pay)), pay)

def lines_written(c: Bool, +f: String, +p2: String, +y: Maybe<&2, String>, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, +at: String, +held: String, +h: Upd.Held, +hs: List<&2, String>, +x: Bool, +j: Conflict.Joined, +ec: {Bool.and(x, M.unrecorded(held, Upd.text_digest(Conflict.render(j)) <> Upd.text_digest(Conflict.plain(j)) <> hs)) == c : Bool}) -> {M.laid.all(M.Place{Tree.Entry{f, p2, Tree.Lines{}, y, g, m}, at, held, h, hs, x, Done{j}}, Bool.pick(List<&2, M.Act>, c, [M.Act.Said{M.UNRECORDED(at)}], [M.Act.Lines{at, Conflict.render(j), m}])) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, String.eq(at, at), True{}, S.eq_refl(at)) : {Bool.and(Bool.and(_, M.spared.lines(held, hs, x, Conflict.render(j), Done{j})), True{}) == True{} : Bool}
      %Equal.sym(Bool, String.eq(Conflict.render(j), Conflict.render(j)), True{}, S.eq_refl(Conflict.render(j))) : {Bool.and(Bool.and(True{}, Bool.and(_, Bool.or(Bool.not(x), Bool.or(String.eq(held, "-"), Rev.member(Upd.text_digest(Conflict.render(j)) <> Upd.text_digest(Conflict.plain(j)) <> hs, held))))), True{}) == True{} : Bool}
      %Equal.sym(Bool, Bool.or(Bool.not(x), Bool.or(String.eq(held, "-"), Rev.member(Upd.text_digest(Conflict.render(j)) <> Upd.text_digest(Conflict.plain(j)) <> hs, held))), True{}, lines_ok(x, String.eq(held, "-"), Rev.member(Upd.text_digest(Conflict.render(j)) <> Upd.text_digest(Conflict.plain(j)) <> hs, held), ec)) : {Bool.and(Bool.and(True{}, Bool.and(True{}, _)), True{}) == True{} : Bool}
      {==}

# Wherever `merge` writes, it writes at the place's own path — the walk's
# rendering for a file of lines — and only over nothing, over no text, or
# over a version of the file the merge was decided against.
def spares(+t: Tree.Tree(), +cs: List<&2, Tree.Contest>, +located: Map<&2, String>, p: M.Place) -> {M.laid.all(p, M.laid.acts(M.lay(t, cs, located, p))) == True{} : Bool}:
  match p:
    case M.Place{Tree.Entry{+f, +p2, Tree.Link{}, +y, +g, +m}, +at, +held, +h, +hs, +x, +r}:
      link_ok(M.Place{Tree.Entry{f, p2, Tree.Link{}, y, g, m}, at, held, h, hs, x, r}, at, h, Maybe.bind(&2, Tree.Target, String, g, x2 => Upd.materialise(t, at, x2)))
    case M.Place{Tree.Entry{+f, +p2, Tree.Whole{}, +y, +g, +m}, +at, +held, +h, +hs, +x, +r}:
      whole_ok(cs, located, f, p2, y, g, m, at, held, h, hs, x, r)
    case M.Place{Tree.Entry{+f, +p2, Tree.Lines{}, +y, +g, +m}, +at, +held, +h, +hs, +x, r}:
      match r:
        case Fail{e}:
          {==}
        case Done{+j}:
          lines_written(Bool.and(x, M.unrecorded(held, Upd.text_digest(Conflict.render(j)) <> Upd.text_digest(Conflict.plain(j)) <> hs)), f, p2, y, g, m, at, held, h, hs, x, j, {==})
