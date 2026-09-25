# What `merge` joins: every revision it joins is one the store holds, and
# every current head is among them; and what it writes into the folder is
# what the store says the merged tree holds, over nothing the store does
# not account for.
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
import ./store.bend as Store
import ./update_lemmas.bend as UpdL

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

# Where one of a choice holds, so does it with the rest made weaker.
def or_tail(a: Bool, -m: Bool, -r: Bool, h: {Bool.or(a, m) == True{} : Bool}, f: {m == True{} : Bool} -> {r == True{} : Bool}) -> {Bool.or(a, r) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      f(h)

def same_mode(m: Tree.Mode) -> {M.same.mode(m, m) == True{} : Bool}:
  match m:
    case Tree.Executable{}:
      {==}
    case Tree.Plain{}:
      {==}

# Where it writes: the file's path, or the name `beside` gave it.
def get_pick(c: Bool, +a: String, +b: String, +rest: List<&2, T.Split>, +k: String, +v: String, +eb: {String.eq(a, k) == c : Bool}, h: {Bool.pick(Maybe<&2, String>, c, Some{b}, M.split.get(rest, k)) == Some{v} : Maybe<&2, String>}, ih: {M.split.get(rest, k) == Some{v} : Maybe<&2, String>} -> {M.split.has(rest, k, v) == True{} : Bool}) -> {Bool.or(Bool.and(String.eq(a, k), String.eq(b, v)), M.split.has(rest, k, v)) == True{} : Bool}:
  match c:
    case True{}:
      AL.or_left(Bool.and(String.eq(a, k), String.eq(b, v)), M.split.has(rest, k, v), AL.and_intro(String.eq(a, k), String.eq(b, v), eb,
        (%UpdL.some_eq(b, v, h) : {String.eq(b, _) == True{} : Bool}
          S.eq_refl(b))))
    case False{}:
      AL.or_right(Bool.and(String.eq(a, k), String.eq(b, v)), M.split.has(rest, k, v), ih(h))

def get_has(xs: List<&2, T.Split>, +k: String, +v: String, h: {M.split.get(xs, k) == Some{v} : Maybe<&2, String>}) -> {M.split.has(xs, k, v) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({M.split.has(Nil{}, k, v) == True{} : Bool}, UpdL.none_some(v, h))
    case T.Split{+a, +b} <> +rest:
      get_pick(String.eq(a, k), a, b, rest, k, v, {==}, h, h2 => get_has(rest, k, v, h2))

def at_pick(mm: Maybe<&2, String>, +bs: List<&2, T.Split>, +f: String, +p: String, +em: {M.split.get(bs, f) == mm : Maybe<&2, String>}) -> {M.at.is(bs, f, p, Maybe.default(&2, String, mm, p)) == True{} : Bool}:
  match mm:
    case None{}:
      AL.or_left(String.eq(p, p), M.split.has(bs, f, p), S.eq_refl(p))
    case Some{+b}:
      AL.or_right(String.eq(b, p), M.split.has(bs, f, b), get_has(bs, f, b, em))

# What a head leaves a file of lines as is what the head reads for it.
def reads_pick(mm: Maybe<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +f: String, +h: String, +rest: List<&2, String>, +em: {Upd.recorded.lines(Main.walked(fs, ds, h, f)) == mm : Maybe<&2, String>}, +d: String, hm: {Rev.member(Upd.push(mm, M.head.lines(fs, ds, f, rest)), d) == True{} : Bool}, ih: {Rev.member(M.head.lines(fs, ds, f, rest), d) == True{} : Bool} -> {M.heads.read(fs, ds, f, d, rest) == True{} : Bool}) -> {M.heads.read(fs, ds, f, d, h <> rest) == True{} : Bool}:
  match mm:
    case None{}:
      AL.or_right(Upd.records.lines(d, Main.walked(fs, ds, h, f)), M.heads.read(fs, ds, f, d, rest), ih(hm))
    case Some{+v}:
      AL.or_cases({M.heads.read(fs, ds, f, d, h <> rest) == True{} : Bool}, String.eq(v, d), Rev.member(M.head.lines(fs, ds, f, rest), d), hm,
        l => AL.or_left(Upd.records.lines(d, Main.walked(fs, ds, h, f)), M.heads.read(fs, ds, f, d, rest),
          (%S.eq_true(v, d, l) : {Upd.records.lines(_, Main.walked(fs, ds, h, f)) == True{} : Bool}
            UpdL.lines_rec(v, Main.walked(fs, ds, h, f), em))),
        r => AL.or_right(Upd.records.lines(d, Main.walked(fs, ds, h, f)), M.heads.read(fs, ds, f, d, rest), ih(r)))

def lines_read(hs: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +f: String, +d: String, h: {Rev.member(M.head.lines(fs, ds, f, hs), d) == True{} : Bool}) -> {M.heads.read(fs, ds, f, d, hs) == True{} : Bool}:
  match hs:
    case Nil{}:
      Empty.absurd({M.heads.read(fs, ds, f, d, Nil{}) == True{} : Bool}, Comp.false_true(h))
    case +x <> +rest:
      reads_pick(Upd.recorded.lines(Main.walked(fs, ds, x, f)), fs, ds, f, x, rest, {==}, d, h, h2 => lines_read(rest, fs, ds, f, d, h2))

# What a head leaves a file of bytes as is what the head's tree names.
def bind_names(lm: Maybe<&2, Tree.Entry>, +v: String, em: {Maybe.bind(&2, Tree.Entry, String, lm, e => Tree.entry_payload(e)) == Some{v} : Maybe<&2, String>}) -> {M.entry.names(v, lm) == True{} : Bool}:
  match lm:
    case None{}:
      Empty.absurd({M.entry.names(v, None{}) == True{} : Bool}, UpdL.none_some(v, em))
    case Some{+e}:
      %Equal.sym(Maybe<&2, String>, Tree.entry_payload(e), Some{v}, em) : {Upd.records.payload(v, _) == True{} : Bool}
      S.eq_refl(v)

def payload_names(+f: String, r: Result<&2, &2, Main.Refused, Tree.Tree()>, +v: String, em: {M.head.payload(f, r) == Some{v} : Maybe<&2, String>}) -> {M.tree.names(f, v, r) == True{} : Bool}:
  match r:
    case Done{+t2}:
      bind_names(Tree.lookup(t2, f), v, em)
    case Fail{e}:
      Empty.absurd({M.tree.names(f, v, Fail{e}) == True{} : Bool}, UpdL.none_some(v, em))

def names_pick(mm: Maybe<&2, String>, +fs: List<&2, Main.Full>, +f: String, +h: String, +rest: List<&2, String>, +em: {M.head.payload(f, Main.tree.r(fs, h)) == mm : Maybe<&2, String>}, +d: String, hm: {Rev.member(Upd.push(mm, M.head.wholes(fs, f, rest)), d) == True{} : Bool}, ih: {Rev.member(M.head.wholes(fs, f, rest), d) == True{} : Bool} -> {M.heads.name(fs, f, d, rest) == True{} : Bool}) -> {M.heads.name(fs, f, d, h <> rest) == True{} : Bool}:
  match mm:
    case None{}:
      AL.or_right(M.tree.names(f, d, Main.tree.r(fs, h)), M.heads.name(fs, f, d, rest), ih(hm))
    case Some{+v}:
      AL.or_cases({M.heads.name(fs, f, d, h <> rest) == True{} : Bool}, String.eq(v, d), Rev.member(M.head.wholes(fs, f, rest), d), hm,
        l => AL.or_left(M.tree.names(f, d, Main.tree.r(fs, h)), M.heads.name(fs, f, d, rest),
          (%S.eq_true(v, d, l) : {M.tree.names(f, _, Main.tree.r(fs, h)) == True{} : Bool}
            payload_names(f, Main.tree.r(fs, h), v, em))),
        r => AL.or_right(M.tree.names(f, d, Main.tree.r(fs, h)), M.heads.name(fs, f, d, rest), ih(r)))

def wholes_name(hs: List<&2, String>, +fs: List<&2, Main.Full>, +f: String, +d: String, h: {Rev.member(M.head.wholes(fs, f, hs), d) == True{} : Bool}) -> {M.heads.name(fs, f, d, hs) == True{} : Bool}:
  match hs:
    case Nil{}:
      Empty.absurd({M.heads.name(fs, f, d, Nil{}) == True{} : Bool}, Comp.false_true(h))
    case +x <> +rest:
      names_pick(M.head.payload(f, Main.tree.r(fs, x)), fs, f, x, rest, {==}, d, h, h2 => wholes_name(rest, fs, f, d, h2))

# Each act at one file of the merged tree, as the store and the folder
# read it.
def laid.each(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +e: Tree.Entry, acts: List<&2, M.Act>) -> Bool:
  match acts:
    case Nil{}:
      True{}
    case +a <> rest:
      Bool.and(M.laid.reads(fs, ds, heads, bs, t, dg, texts, e, a), laid.each(fs, ds, heads, bs, t, dg, texts, e, rest))

# A file of lines: written as the walk of the heads renders it, and only
# over nothing, no text, what it writes, the walk unfenced, or what a head
# reads.
def lines_written(c: Bool, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +f: String, +p: String, +y: Maybe<&2, String>, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, +at: String, +hat: {M.at.is(bs, f, p, at) == True{} : Bool}, +j: Conflict.Joined, +er: {Main.joined(fs, ds, heads, f) == Done{j} : Result<&2, &2, String, Conflict.Joined>}, +ec: {Bool.and(M.text.at(texts, at), M.unrecorded(Main.status.folder_digest(dg, at), Upd.text_digest(Conflict.render(j)) <> Upd.text_digest(Conflict.plain(j)) <> M.head.lines(fs, ds, f, heads))) == c : Bool}) -> {laid.each(fs, ds, heads, bs, t, dg, texts, Tree.Entry{f, p, Tree.Lines{}, y, g, m}, Bool.pick(List<&2, M.Act>, c, [M.Act.Said{M.LEFT_UNRECORDED(at)}], [M.Act.Lines{at, Conflict.render(j), m}])) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Result<&2, &2, String, Conflict.Joined>, Main.joined(fs, ds, heads, f), Done{j}, er) : {Bool.and(Bool.and(Bool.and(M.at.is(bs, f, p, at), M.same.mode(m, m)), M.lines.over(fs, ds, heads, f, Main.status.folder_digest(dg, at), M.text.at(texts, at), Conflict.render(j), _)), True{}) == True{} : Bool}
      AL.and_intro(Bool.and(Bool.and(M.at.is(bs, f, p, at), M.same.mode(m, m)), M.lines.over(fs, ds, heads, f, Main.status.folder_digest(dg, at), M.text.at(texts, at), Conflict.render(j), Done{j})), True{},
        AL.and_intro(Bool.and(M.at.is(bs, f, p, at), M.same.mode(m, m)), M.lines.over(fs, ds, heads, f, Main.status.folder_digest(dg, at), M.text.at(texts, at), Conflict.render(j), Done{j}),
          AL.and_intro(M.at.is(bs, f, p, at), M.same.mode(m, m), hat, same_mode(m)),
          AL.and_intro(String.eq(Conflict.render(j), Conflict.render(j)), Bool.or(Bool.not(M.text.at(texts, at)), Bool.or(String.eq(Main.status.folder_digest(dg, at), "-"), Bool.or(String.eq(Upd.text_digest(Conflict.render(j)), Main.status.folder_digest(dg, at)), Bool.or(String.eq(Upd.text_digest(Conflict.plain(j)), Main.status.folder_digest(dg, at)), M.heads.read(fs, ds, f, Main.status.folder_digest(dg, at), heads))))),
            S.eq_refl(Conflict.render(j)),
            or_tail(Bool.not(M.text.at(texts, at)), Bool.or(String.eq(Main.status.folder_digest(dg, at), "-"), Rev.member(Upd.text_digest(Conflict.render(j)) <> Upd.text_digest(Conflict.plain(j)) <> M.head.lines(fs, ds, f, heads), Main.status.folder_digest(dg, at))), Bool.or(String.eq(Main.status.folder_digest(dg, at), "-"), Bool.or(String.eq(Upd.text_digest(Conflict.render(j)), Main.status.folder_digest(dg, at)), Bool.or(String.eq(Upd.text_digest(Conflict.plain(j)), Main.status.folder_digest(dg, at)), M.heads.read(fs, ds, f, Main.status.folder_digest(dg, at), heads)))),
              lines_ok(M.text.at(texts, at), String.eq(Main.status.folder_digest(dg, at), "-"), Rev.member(Upd.text_digest(Conflict.render(j)) <> Upd.text_digest(Conflict.plain(j)) <> M.head.lines(fs, ds, f, heads), Main.status.folder_digest(dg, at)), ec),
              h1 => or_tail(String.eq(Main.status.folder_digest(dg, at), "-"), Rev.member(Upd.text_digest(Conflict.render(j)) <> Upd.text_digest(Conflict.plain(j)) <> M.head.lines(fs, ds, f, heads), Main.status.folder_digest(dg, at)), Bool.or(String.eq(Upd.text_digest(Conflict.render(j)), Main.status.folder_digest(dg, at)), Bool.or(String.eq(Upd.text_digest(Conflict.plain(j)), Main.status.folder_digest(dg, at)), M.heads.read(fs, ds, f, Main.status.folder_digest(dg, at), heads))), h1,
                h2 => or_tail(String.eq(Upd.text_digest(Conflict.render(j)), Main.status.folder_digest(dg, at)), Rev.member(Upd.text_digest(Conflict.plain(j)) <> M.head.lines(fs, ds, f, heads), Main.status.folder_digest(dg, at)), Bool.or(String.eq(Upd.text_digest(Conflict.plain(j)), Main.status.folder_digest(dg, at)), M.heads.read(fs, ds, f, Main.status.folder_digest(dg, at), heads)), h2,
                  h3 => or_tail(String.eq(Upd.text_digest(Conflict.plain(j)), Main.status.folder_digest(dg, at)), Rev.member(M.head.lines(fs, ds, f, heads), Main.status.folder_digest(dg, at)), M.heads.read(fs, ds, f, Main.status.folder_digest(dg, at), heads), h3,
                    h4 => lines_read(heads, fs, ds, f, Main.status.folder_digest(dg, at), h4))))))),
        {==})

def lines_each(r: Result<&2, &2, String, Conflict.Joined>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +f: String, +p: String, +y: Maybe<&2, String>, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, +at: String, +hat: {M.at.is(bs, f, p, at) == True{} : Bool}, +er: {Main.joined(fs, ds, heads, f) == r : Result<&2, &2, String, Conflict.Joined>}) -> {laid.each(fs, ds, heads, bs, t, dg, texts, Tree.Entry{f, p, Tree.Lines{}, y, g, m}, M.laid.acts(M.lay.lines(at, Main.status.folder_digest(dg, at), M.head.lines(fs, ds, f, heads), M.text.at(texts, at), m, r))) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+j}:
      lines_written(Bool.and(M.text.at(texts, at), M.unrecorded(Main.status.folder_digest(dg, at), Upd.text_digest(Conflict.render(j)) <> Upd.text_digest(Conflict.plain(j)) <> M.head.lines(fs, ds, f, heads))), fs, ds, heads, bs, t, dg, texts, f, p, y, g, m, at, hat, j, er, {==})

# A file of bytes: the payload its tree names, laid only over nothing, the
# payload, or what a head's tree names.
def cat_each(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +f: String, +p: String, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, +at: String, cs: List<&2, Tree.Claim>) -> {laid.each(fs, ds, heads, bs, t, dg, texts, Tree.Entry{f, p, Tree.Whole{}, None{}, g, m}, M.claims.cat(at, cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Tree.Claim{by, w} <> rest:
      cat_each(fs, ds, heads, bs, t, dg, texts, f, p, g, m, at, rest)

def whole_written(c: Bool, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +f: String, +p: String, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, +at: String, +hat: {M.at.is(bs, f, p, at) == True{} : Bool}, +pay: String, +from: String, +ec: {M.unrecorded(Main.status.folder_digest(dg, at), pay <> M.head.wholes(fs, f, heads)) == c : Bool}) -> {laid.each(fs, ds, heads, bs, t, dg, texts, Tree.Entry{f, p, Tree.Whole{}, Some{pay}, g, m}, Bool.pick(List<&2, M.Act>, c, [M.Act.Said{M.LEFT_UNRECORDED(at)}], [M.Act.Whole{at, from, pay, m}])) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      AL.and_intro(Bool.and(Bool.and(M.at.is(bs, f, p, at), M.same.mode(m, m)), Bool.and(String.eq(pay, pay), Bool.or(String.eq(Main.status.folder_digest(dg, at), "-"), Bool.or(String.eq(pay, Main.status.folder_digest(dg, at)), M.heads.name(fs, f, Main.status.folder_digest(dg, at), heads))))), True{},
        AL.and_intro(Bool.and(M.at.is(bs, f, p, at), M.same.mode(m, m)), Bool.and(String.eq(pay, pay), Bool.or(String.eq(Main.status.folder_digest(dg, at), "-"), Bool.or(String.eq(pay, Main.status.folder_digest(dg, at)), M.heads.name(fs, f, Main.status.folder_digest(dg, at), heads)))),
          AL.and_intro(M.at.is(bs, f, p, at), M.same.mode(m, m), hat, same_mode(m)),
          AL.and_intro(String.eq(pay, pay), Bool.or(String.eq(Main.status.folder_digest(dg, at), "-"), Bool.or(String.eq(pay, Main.status.folder_digest(dg, at)), M.heads.name(fs, f, Main.status.folder_digest(dg, at), heads))), S.eq_refl(pay),
            or_tail(String.eq(Main.status.folder_digest(dg, at), "-"), Rev.member(pay <> M.head.wholes(fs, f, heads), Main.status.folder_digest(dg, at)), Bool.or(String.eq(pay, Main.status.folder_digest(dg, at)), M.heads.name(fs, f, Main.status.folder_digest(dg, at), heads)),
              nand(String.eq(Main.status.folder_digest(dg, at), "-"), Rev.member(pay <> M.head.wholes(fs, f, heads), Main.status.folder_digest(dg, at)), ec),
              h1 => or_tail(String.eq(pay, Main.status.folder_digest(dg, at)), Rev.member(M.head.wholes(fs, f, heads), Main.status.folder_digest(dg, at)), M.heads.name(fs, f, Main.status.folder_digest(dg, at), heads), h1,
                h2 => wholes_name(heads, fs, f, Main.status.folder_digest(dg, at), h2))))),
        {==})

def whole_found(c: Bool, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +f: String, +p: String, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, +at: String, +hat: {M.at.is(bs, f, p, at) == True{} : Bool}, +pay: String, +from: String) -> {laid.each(fs, ds, heads, bs, t, dg, texts, Tree.Entry{f, p, Tree.Whole{}, Some{pay}, g, m}, Bool.pick(List<&2, M.Act>, c, [M.Act.Stop{"this store does not hold the content " ++ pay}], Bool.pick(List<&2, M.Act>, M.unrecorded(Main.status.folder_digest(dg, at), pay <> M.head.wholes(fs, f, heads)), [M.Act.Said{M.LEFT_UNRECORDED(at)}], [M.Act.Whole{at, from, pay, m}]))) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      whole_written(M.unrecorded(Main.status.folder_digest(dg, at), pay <> M.head.wholes(fs, f, heads)), fs, ds, heads, bs, t, dg, texts, f, p, g, m, at, hat, pay, from, {==})

def whole_each(y: Maybe<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +f: String, +p: String, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, +at: String, +hat: {M.at.is(bs, f, p, at) == True{} : Bool}, +cs: List<&2, Tree.Contest>, +located: Map<&2, String>) -> {laid.each(fs, ds, heads, bs, t, dg, texts, Tree.Entry{f, p, Tree.Whole{}, y, g, m}, M.laid.acts(M.lay.whole(at, f, cs, located, Main.status.folder_digest(dg, at), M.head.wholes(fs, f, heads), m, y))) == True{} : Bool}:
  match y:
    case None{}:
      cat_each(fs, ds, heads, bs, t, dg, texts, f, p, g, m, at, M.payload.claims(cs, f))
    case Some{+pay}:
      whole_found(String.is_empty(Main.stat_of(pay, Map.get(String, SNil{}, located, pay))), fs, ds, heads, bs, t, dg, texts, f, p, g, m, at, hat, pay, Main.stat_of(pay, Map.get(String, SNil{}, located, pay)))

# A link: pointed where `cat` says it points.
def link_pick(c: Bool, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +f: String, +p: String, +y: Maybe<&2, String>, +v: Tree.Target, +m: Tree.Mode, +at: String, +hat: {M.at.is(bs, f, p, at) == True{} : Bool}, +s: String, +es: {Main.materialise(t, at, v) == s : String}) -> {laid.each(fs, ds, heads, bs, t, dg, texts, Tree.Entry{f, p, Tree.Link{}, y, Some{v}, m}, Bool.pick(List<&2, M.Act>, c, Nil{}, [M.Act.Link{at, s}])) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      AL.and_intro(Bool.and(M.at.is(bs, f, p, at), String.eq(s, Main.materialise(t, at, v))), True{},
        AL.and_intro(M.at.is(bs, f, p, at), String.eq(s, Main.materialise(t, at, v)), hat,
          (%Equal.sym(String, Main.materialise(t, at, v), s, es) : {String.eq(s, _) == True{} : Bool}
            S.eq_refl(s))),
        {==})

def link_some(mm: Maybe<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +f: String, +p: String, +y: Maybe<&2, String>, +v: Tree.Target, +m: Tree.Mode, +at: String, +hat: {M.at.is(bs, f, p, at) == True{} : Bool}, +em: {Upd.materialise(t, at, v) == mm : Maybe<&2, String>}, +h: Upd.Held) -> {laid.each(fs, ds, heads, bs, t, dg, texts, Tree.Entry{f, p, Tree.Link{}, y, Some{v}, m}, M.laid.acts(M.lay.link(at, h, mm))) == True{} : Bool}:
  match mm:
    case None{}:
      {==}
    case Some{+s}:
      link_pick(Upd.lands.link(s, h), fs, ds, heads, bs, t, dg, texts, f, p, y, v, m, at, hat, s, UpdL.spelled_same(t, at, v, s, em))

def link_each(g: Maybe<&2, Tree.Target>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +f: String, +p: String, +y: Maybe<&2, String>, +m: Tree.Mode, +at: String, +hat: {M.at.is(bs, f, p, at) == True{} : Bool}, +h: Upd.Held) -> {laid.each(fs, ds, heads, bs, t, dg, texts, Tree.Entry{f, p, Tree.Link{}, y, g, m}, M.laid.acts(M.lay.link(at, h, Maybe.bind(&2, Tree.Target, String, g, x2 => Upd.materialise(t, at, x2))))) == True{} : Bool}:
  match g:
    case None{}:
      {==}
    case Some{+v}:
      link_some(Upd.materialise(t, at, v), fs, ds, heads, bs, t, dg, texts, f, p, y, v, m, at, hat, {==}, h)

# Whatever `merge` does at one file of the merged tree is what the store
# and the folder say it may.
def lay_each(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +ls: Map<&2, String>, +cs: List<&2, Tree.Contest>, +located: Map<&2, String>, e: Tree.Entry) -> {laid.each(fs, ds, heads, bs, t, dg, texts, e, M.laid.acts(M.lay(t, cs, located, M.place(fs, ds, heads, bs, dg, ls, texts, e)))) == True{} : Bool}:
  match e:
    case Tree.Entry{+f, +p, Tree.Lines{}, +y, +g, +m}:
      lines_each(Main.joined(fs, ds, heads, f), fs, ds, heads, bs, t, dg, texts, f, p, y, g, m, Maybe.default(&2, String, M.split.get(bs, f), p), at_pick(M.split.get(bs, f), bs, f, p, {==}), {==})
    case Tree.Entry{+f, +p, Tree.Whole{}, +y, +g, +m}:
      whole_each(y, fs, ds, heads, bs, t, dg, texts, f, p, g, m, Maybe.default(&2, String, M.split.get(bs, f), p), at_pick(M.split.get(bs, f), bs, f, p, {==}), cs, located)
    case Tree.Entry{+f, +p, Tree.Link{}, +y, +g, +m}:
      link_each(g, fs, ds, heads, bs, t, dg, texts, f, p, y, m, Maybe.default(&2, String, M.split.get(bs, f), p), at_pick(M.split.get(bs, f), bs, f, p, {==}), Upd.held.of(ls, Maybe.default(&2, String, M.split.get(bs, f), p), None{}))

# Every act, over the whole tree
# ------------------------------

def each_every(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +e: Tree.Entry, +rest: List<&2, Tree.Entry>, acts: List<&2, M.Act>, +h: {laid.each(fs, ds, heads, bs, t, dg, texts, e, acts) == True{} : Bool}) -> {M.laid.every(fs, ds, heads, bs, t, dg, texts, e <> rest, acts) == True{} : Bool}:
  match acts:
    case Nil{}:
      {==}
    case +a <> +more:
      AL.and_intro(M.laid.some(fs, ds, heads, bs, t, dg, texts, e <> rest, a), M.laid.every(fs, ds, heads, bs, t, dg, texts, e <> rest, more),
        AL.or_left(M.laid.reads(fs, ds, heads, bs, t, dg, texts, e, a), M.laid.some(fs, ds, heads, bs, t, dg, texts, rest, a), Comp.and_left(M.laid.reads(fs, ds, heads, bs, t, dg, texts, e, a), laid.each(fs, ds, heads, bs, t, dg, texts, e, more), h)),
        each_every(fs, ds, heads, bs, t, dg, texts, e, rest, more, Comp.and_right(M.laid.reads(fs, ds, heads, bs, t, dg, texts, e, a), laid.each(fs, ds, heads, bs, t, dg, texts, e, more), h)))

def every_weaken(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +e: Tree.Entry, +rest: List<&2, Tree.Entry>, acts: List<&2, M.Act>, +h: {M.laid.every(fs, ds, heads, bs, t, dg, texts, rest, acts) == True{} : Bool}) -> {M.laid.every(fs, ds, heads, bs, t, dg, texts, e <> rest, acts) == True{} : Bool}:
  match acts:
    case Nil{}:
      {==}
    case +a <> +more:
      AL.and_intro(M.laid.some(fs, ds, heads, bs, t, dg, texts, e <> rest, a), M.laid.every(fs, ds, heads, bs, t, dg, texts, e <> rest, more),
        AL.or_right(M.laid.reads(fs, ds, heads, bs, t, dg, texts, e, a), M.laid.some(fs, ds, heads, bs, t, dg, texts, rest, a), Comp.and_left(M.laid.some(fs, ds, heads, bs, t, dg, texts, rest, a), M.laid.every(fs, ds, heads, bs, t, dg, texts, rest, more), h)),
        every_weaken(fs, ds, heads, bs, t, dg, texts, e, rest, more, Comp.and_right(M.laid.some(fs, ds, heads, bs, t, dg, texts, rest, a), M.laid.every(fs, ds, heads, bs, t, dg, texts, rest, more), h)))

def every_app(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +es: List<&2, Tree.Entry>, xs: List<&2, M.Act>, +ys: List<&2, M.Act>, +hx: {M.laid.every(fs, ds, heads, bs, t, dg, texts, es, xs) == True{} : Bool}, +hy: {M.laid.every(fs, ds, heads, bs, t, dg, texts, es, ys) == True{} : Bool}) -> {M.laid.every(fs, ds, heads, bs, t, dg, texts, es, List.append(&2, M.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +a <> +more:
      AL.and_intro(M.laid.some(fs, ds, heads, bs, t, dg, texts, es, a), M.laid.every(fs, ds, heads, bs, t, dg, texts, es, List.append(&2, M.Act, more, ys)),
        Comp.and_left(M.laid.some(fs, ds, heads, bs, t, dg, texts, es, a), M.laid.every(fs, ds, heads, bs, t, dg, texts, es, more), hx),
        every_app(fs, ds, heads, bs, t, dg, texts, es, more, ys, Comp.and_right(M.laid.some(fs, ds, heads, bs, t, dg, texts, es, a), M.laid.every(fs, ds, heads, bs, t, dg, texts, es, more), hx), hy))

def join_acts(l: M.Laid, r: M.Lay) -> {List.append(&2, M.Act, M.laid.acts(l), M.lay.acts(r)) == M.lay.acts(M.lay.join(l, r)) : List<&2, M.Act>}:
  match l r:
    case M.Laid{x, a} M.Lay{y, n}:
      {==}

# Whatever `merge` does, over every file of the merged tree, one of them
# accounts for as the store and the folder read it.
def spares(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +ls: Map<&2, String>, +cs: List<&2, Tree.Contest>, +located: Map<&2, String>, es: List<&2, Tree.Entry>) -> {M.laid.every(fs, ds, heads, bs, t, dg, texts, es, M.lay.acts(M.lay.all(t, cs, located, M.places(fs, ds, heads, bs, dg, ls, texts, es)))) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      %join_acts(M.lay(t, cs, located, M.place(fs, ds, heads, bs, dg, ls, texts, e)), M.lay.all(t, cs, located, M.places(fs, ds, heads, bs, dg, ls, texts, rest))) : {M.laid.every(fs, ds, heads, bs, t, dg, texts, e <> rest, _) == True{} : Bool}
      every_app(fs, ds, heads, bs, t, dg, texts, e <> rest, M.laid.acts(M.lay(t, cs, located, M.place(fs, ds, heads, bs, dg, ls, texts, e))), M.lay.acts(M.lay.all(t, cs, located, M.places(fs, ds, heads, bs, dg, ls, texts, rest))),
        each_every(fs, ds, heads, bs, t, dg, texts, e, rest, M.laid.acts(M.lay(t, cs, located, M.place(fs, ds, heads, bs, dg, ls, texts, e))), lay_each(fs, ds, heads, bs, t, dg, texts, ls, cs, located, e)),
        every_weaken(fs, ds, heads, bs, t, dg, texts, e, rest, M.lay.acts(M.lay.all(t, cs, located, M.places(fs, ds, heads, bs, dg, ls, texts, rest))), spares(fs, ds, heads, bs, t, dg, texts, ls, cs, located, rest)))

# What is set aside
# -----------------

def files_ids(+p: String, zs: List<&2, String>) -> {M.typed.ids(M.beside.files(p, zs)) == zs : List<&2, String>}:
  match zs:
    case Nil{}:
      {==}
    case +z <> +zr:
      %Equal.sym(List<&2, String>, M.typed.ids(M.beside.files(p, zr)), zr, files_ids(p, zr)) : {z <> _ == z <> zr : List<&2, String>}
      {==}

def mem_left(xs: List<&2, String>, +ys: List<&2, String>, +x: String, h: {Rev.member(xs, x) == True{} : Bool}) -> {Rev.member(List.append(&2, String, xs, ys), x) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Rev.member(ys, x) == True{} : Bool}, Comp.false_true(h))
    case +a <> +rest:
      AL.or_cases({Rev.member(List.append(&2, String, a <> rest, ys), x) == True{} : Bool}, String.eq(a, x), Rev.member(rest, x), h,
        l => AL.or_left(String.eq(a, x), Rev.member(List.append(&2, String, rest, ys), x), l),
        r => AL.or_right(String.eq(a, x), Rev.member(List.append(&2, String, rest, ys), x), mem_left(rest, ys, x, r)))

def mem_right(xs: List<&2, String>, +ys: List<&2, String>, +x: String, +h: {Rev.member(ys, x) == True{} : Bool}) -> {Rev.member(List.append(&2, String, xs, ys), x) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +a <> +rest:
      AL.or_right(String.eq(a, x), Rev.member(List.append(&2, String, rest, ys), x), mem_right(rest, ys, x, h))

def held_left(+xs: List<&2, String>, +ys: List<&2, String>, ps: List<&2, String>, +h: {Main.all_held(xs, ps) == True{} : Bool}) -> {Main.all_held(List.append(&2, String, xs, ys), ps) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +q <> +rest:
      AL.and_intro(Rev.member(List.append(&2, String, xs, ys), q), Main.all_held(List.append(&2, String, xs, ys), rest),
        mem_left(xs, ys, q, Comp.and_left(Rev.member(xs, q), Main.all_held(xs, rest), h)),
        held_left(xs, ys, rest, Comp.and_right(Rev.member(xs, q), Main.all_held(xs, rest), h)))

def held_right(+xs: List<&2, String>, +ys: List<&2, String>, ps: List<&2, String>, +h: {Main.all_held(ys, ps) == True{} : Bool}) -> {Main.all_held(List.append(&2, String, xs, ys), ps) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +q <> +rest:
      AL.and_intro(Rev.member(List.append(&2, String, xs, ys), q), Main.all_held(List.append(&2, String, xs, ys), rest),
        mem_right(xs, ys, q, Comp.and_left(Rev.member(ys, q), Main.all_held(ys, rest), h)),
        held_right(xs, ys, rest, Comp.and_right(Rev.member(ys, q), Main.all_held(ys, rest), h)))

# Every file after the first a contest names is written beside its path.
def claims_right(fs: List<&2, String>, +xs: List<&2, String>, +ys: List<&2, String>, h: {M.claims.written(fs, ys) == True{} : Bool}) -> {M.claims.written(fs, List.append(&2, String, xs, ys)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case x <> +rest:
      held_right(xs, ys, rest, h)

def contest_right(c: Tree.Contest, +xs: List<&2, String>, +ys: List<&2, String>, h: {M.contest.written(c, ys) == True{} : Bool}) -> {M.contest.written(c, List.append(&2, String, xs, ys)) == True{} : Bool}:
  match c:
    case Tree.Path{p, +fs}:
      claims_right(fs, xs, ys, h)
    case Tree.Dropped{f, b}:
      {==}
    case Tree.Moved{f, b}:
      {==}
    case Tree.Content{f, b}:
      {==}
    case Tree.ModeOf{f, b}:
      {==}
    case Tree.TargetOf{f, b}:
      {==}
    case Tree.Referenced{f, b, l}:
      {==}

def written_right(cs: List<&2, Tree.Contest>, +xs: List<&2, String>, +ys: List<&2, String>, +h: {M.contests.written(cs, ys) == True{} : Bool}) -> {M.contests.written(cs, List.append(&2, String, xs, ys)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +rest:
      AL.and_intro(M.contest.written(c, List.append(&2, String, xs, ys)), M.contests.written(rest, List.append(&2, String, xs, ys)),
        contest_right(c, xs, ys, Comp.and_left(M.contest.written(c, ys), M.contests.written(rest, ys), h)),
        written_right(rest, xs, ys, Comp.and_right(M.contest.written(c, ys), M.contests.written(rest, ys), h)))

def contest_written(c: Tree.Contest, +more: List<&2, Tree.Contest>) -> {M.contest.written(c, M.typed.ids(List.append(&2, T.Split, M.beside.of(c), M.beside(more)))) == True{} : Bool}:
  match c:
    case Tree.Path{+p, fs}:
      match fs:
        case Nil{}:
          {==}
        case +x <> +rest:
          %Equal.sym(List<&2, String>, M.typed.ids(List.append(&2, T.Split, M.beside.files(p, rest), M.beside(more))), List.append(&2, String, M.typed.ids(M.beside.files(p, rest)), M.typed.ids(M.beside(more))), ids_app(M.beside.files(p, rest), M.beside(more))) : {Main.all_held(_, rest) == True{} : Bool}
          %Equal.sym(List<&2, String>, M.typed.ids(M.beside.files(p, rest)), rest, files_ids(p, rest)) : {Main.all_held(List.append(&2, String, _, M.typed.ids(M.beside(more))), rest) == True{} : Bool}
          held_left(rest, M.typed.ids(M.beside(more)), rest, held_self(rest))
    case Tree.Dropped{f, b}:
      {==}
    case Tree.Moved{f, b}:
      {==}
    case Tree.Content{f, b}:
      {==}
    case Tree.ModeOf{f, b}:
      {==}
    case Tree.TargetOf{f, b}:
      {==}
    case Tree.Referenced{f, b, l}:
      {==}

def written_all(cs: List<&2, Tree.Contest>) -> {M.contests.written(cs, M.typed.ids(M.beside(cs))) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +more:
      AL.and_intro(M.contest.written(c, M.typed.ids(List.append(&2, T.Split, M.beside.of(c), M.beside(more)))), M.contests.written(more, M.typed.ids(List.append(&2, T.Split, M.beside.of(c), M.beside(more)))),
        contest_written(c, more),
        (%Equal.sym(List<&2, String>, M.typed.ids(List.append(&2, T.Split, M.beside.of(c), M.beside(more))), List.append(&2, String, M.typed.ids(M.beside.of(c)), M.typed.ids(M.beside(more))), ids_app(M.beside.of(c), M.beside(more))) : {M.contests.written(more, _) == True{} : Bool}
          written_right(more, M.typed.ids(M.beside.of(c)), M.typed.ids(M.beside(more)), written_all(more))))

# And every file written beside a path is one a contest names after the
# first.
def claimed_app(+cs: List<&2, Tree.Contest>, xs: List<&2, String>, +ys: List<&2, String>, +hx: {M.besides.claimed(cs, xs) == True{} : Bool}, +hy: {M.besides.claimed(cs, ys) == True{} : Bool}) -> {M.besides.claimed(cs, List.append(&2, String, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +k <> +rest:
      AL.and_intro(M.contests.beside(cs, k), M.besides.claimed(cs, List.append(&2, String, rest, ys)),
        Comp.and_left(M.contests.beside(cs, k), M.besides.claimed(cs, rest), hx),
        claimed_app(cs, rest, ys, Comp.and_right(M.contests.beside(cs, k), M.besides.claimed(cs, rest), hx), hy))

def claimed_weaken(+c: Tree.Contest, +cs: List<&2, Tree.Contest>, ks: List<&2, String>, +h: {M.besides.claimed(cs, ks) == True{} : Bool}) -> {M.besides.claimed(c <> cs, ks) == True{} : Bool}:
  match ks:
    case Nil{}:
      {==}
    case +k <> +rest:
      AL.and_intro(M.contests.beside(c <> cs, k), M.besides.claimed(c <> cs, rest),
        AL.or_right(M.contest.beside(c, k), M.contests.beside(cs, k), Comp.and_left(M.contests.beside(cs, k), M.besides.claimed(cs, rest), h)),
        claimed_weaken(c, cs, rest, Comp.and_right(M.contests.beside(cs, k), M.besides.claimed(cs, rest), h)))

def claimed_tail(+p: String, +x: String, +rest: List<&2, String>, +more: List<&2, Tree.Contest>, zs: List<&2, String>, +h: {Main.all_held(rest, zs) == True{} : Bool}) -> {M.besides.claimed(Tree.Path{p, x <> rest} <> more, zs) == True{} : Bool}:
  match zs:
    case Nil{}:
      {==}
    case +z <> +zr:
      AL.and_intro(M.contests.beside(Tree.Path{p, x <> rest} <> more, z), M.besides.claimed(Tree.Path{p, x <> rest} <> more, zr),
        AL.or_left(Rev.member(rest, z), M.contests.beside(more, z), Comp.and_left(Rev.member(rest, z), Main.all_held(rest, zr), h)),
        claimed_tail(p, x, rest, more, zr, Comp.and_right(Rev.member(rest, z), Main.all_held(rest, zr), h)))

def claimed_of(c: Tree.Contest, +more: List<&2, Tree.Contest>) -> {M.besides.claimed(c <> more, M.typed.ids(M.beside.of(c))) == True{} : Bool}:
  match c:
    case Tree.Path{+p, fs}:
      match fs:
        case Nil{}:
          {==}
        case +x <> +rest:
          %Equal.sym(List<&2, String>, M.typed.ids(M.beside.files(p, rest)), rest, files_ids(p, rest)) : {M.besides.claimed(Tree.Path{p, x <> rest} <> more, _) == True{} : Bool}
          claimed_tail(p, x, rest, more, rest, held_self(rest))
    case Tree.Dropped{f, b}:
      {==}
    case Tree.Moved{f, b}:
      {==}
    case Tree.Content{f, b}:
      {==}
    case Tree.ModeOf{f, b}:
      {==}
    case Tree.TargetOf{f, b}:
      {==}
    case Tree.Referenced{f, b, l}:
      {==}

def claimed_all(cs: List<&2, Tree.Contest>) -> {M.besides.claimed(cs, M.typed.ids(M.beside(cs))) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +more:
      %Equal.sym(List<&2, String>, M.typed.ids(List.append(&2, T.Split, M.beside.of(c), M.beside(more))), List.append(&2, String, M.typed.ids(M.beside.of(c)), M.typed.ids(M.beside(more))), ids_app(M.beside.of(c), M.beside(more))) : {M.besides.claimed(c <> more, _) == True{} : Bool}
      claimed_app(c <> more, M.typed.ids(M.beside.of(c)), M.typed.ids(M.beside(more)), claimed_of(c, more), claimed_weaken(c, more, M.typed.ids(M.beside(more)), claimed_all(more)))

# The files `merge` writes beside a path are exactly those a contest names
# after the first.
def aside(+cs: List<&2, Tree.Contest>) -> {Bool.and(M.besides.claimed(cs, M.typed.ids(M.beside(cs))), M.contests.written(cs, M.typed.ids(M.beside(cs)))) == True{} : Bool}:
  AL.and_intro(M.besides.claimed(cs, M.typed.ids(M.beside(cs))), M.contests.written(cs, M.typed.ids(M.beside(cs))), claimed_all(cs), written_all(cs))
