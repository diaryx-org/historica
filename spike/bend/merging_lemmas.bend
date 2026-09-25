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
import ./map_lemmas.bend as ML
import ./conflict_lemmas.bend as ConflictL
import ./rewrite_lemmas.bend as RewriteL
import ./spelling_lemmas.bend as Spell
import ./equality_lemmas.bend as Eq

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

# Where the folder already holds the merge
# ----------------------------------------
#
# Where the merged trees contest nothing and the folder already holds, at
# each file's path, what the merge reads there, every file `merge` writes
# it writes with the bytes already there, and it points no link.

def same_app(+dg: Map<&2, String>, xs: List<&2, M.Act>, +ys: List<&2, M.Act>, +hx: {M.rewrites.same(dg, xs) == True{} : Bool}, +hy: {M.rewrites.same(dg, ys) == True{} : Bool}) -> {M.rewrites.same(dg, List.append(&2, M.Act, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case M.Act.Lines{+at, +text, m} <> +rest:
      AL.and_intro(String.eq(Upd.text_digest(text), Main.status.folder_digest(dg, at)), M.rewrites.same(dg, List.append(&2, M.Act, rest, ys)),
        Comp.and_left(String.eq(Upd.text_digest(text), Main.status.folder_digest(dg, at)), M.rewrites.same(dg, rest), hx),
        same_app(dg, rest, ys, Comp.and_right(String.eq(Upd.text_digest(text), Main.status.folder_digest(dg, at)), M.rewrites.same(dg, rest), hx), hy))
    case M.Act.Whole{+at, from, +q, m} <> +rest:
      AL.and_intro(String.eq(q, Main.status.folder_digest(dg, at)), M.rewrites.same(dg, List.append(&2, M.Act, rest, ys)),
        Comp.and_left(String.eq(q, Main.status.folder_digest(dg, at)), M.rewrites.same(dg, rest), hx),
        same_app(dg, rest, ys, Comp.and_right(String.eq(q, Main.status.folder_digest(dg, at)), M.rewrites.same(dg, rest), hx), hy))
    case M.Act.Link{at, target} <> rest:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(hx))
    case M.Act.Said{l} <> +rest:
      same_app(dg, rest, ys, hx, hy)
    case M.Act.Stop{e} <> +rest:
      same_app(dg, rest, ys, hx, hy)

def acts_cons(l: M.Laid, -rest: List<&2, M.Laid>) -> {M.lay.acts(l <> rest) == List.append(&2, M.Act, M.laid.acts(l), M.lay.acts(rest)) : List<&2, M.Act>}:
  match l:
    case M.Laid{a, m}:
      {==}

def lines_same.pick(c: Bool, +dg: Map<&2, String>, +p: String, +j: Conflict.Joined, +m: Tree.Mode, +hj: {String.eq(Upd.text_digest(Conflict.render(j)), Main.status.folder_digest(dg, p)) == True{} : Bool}) -> {M.rewrites.same(dg, Bool.pick(List<&2, M.Act>, c, [M.Act.Said{M.LEFT_UNRECORDED(p)}], [M.Act.Lines{p, Conflict.render(j), m}])) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      AL.and_intro(String.eq(Upd.text_digest(Conflict.render(j)), Main.status.folder_digest(dg, p)), True{}, hj, {==})

# A file of lines where nothing met is written as the walk reads it, which
# is what the folder holds.
def lines_same(r: Result<&2, &2, String, Conflict.Joined>, +dg: Map<&2, String>, +p: String, +hs: List<&2, String>, +x: Bool, +m: Tree.Mode, +h: {M.already.lines(dg, p, r) == True{} : Bool}) -> {M.rewrites.same(dg, M.laid.acts(M.lay.lines(p, Main.status.folder_digest(dg, p), hs, x, m, r))) == True{} : Bool}:
  match r:
    case Fail{e}:
      Empty.absurd({M.rewrites.same(dg, M.laid.acts(M.lay.lines(p, Main.status.folder_digest(dg, p), hs, x, m, Fail{e}))) == True{} : Bool}, Comp.false_true(h))
    case Done{+j}:
      lines_same.pick(Bool.and(x, M.unrecorded(Main.status.folder_digest(dg, p), Upd.text_digest(Conflict.render(j)) <> Upd.text_digest(Conflict.plain(j)) <> hs)), dg, p, j, m,
        (%Equal.sym(String, Conflict.render(j), Conflict.plain(j), ConflictL.render_plain(j, UpdL.not_true(Conflict.met(j), Comp.and_left(Bool.not(Conflict.met(j)), String.eq(Main.status.folder_digest(dg, p), Upd.text_digest(Conflict.plain(j))), h)))) : {String.eq(Upd.text_digest(_), Main.status.folder_digest(dg, p)) == True{} : Bool}
          %ML.eq_sym(Main.status.folder_digest(dg, p), Upd.text_digest(Conflict.plain(j))) : {_ == True{} : Bool}
          Comp.and_right(Bool.not(Conflict.met(j)), String.eq(Main.status.folder_digest(dg, p), Upd.text_digest(Conflict.plain(j))), h)))

def whole_same.pick(a: Bool, b: Bool, +dg: Map<&2, String>, +p: String, +from: String, +d: String, +m: Tree.Mode, +hd: {String.eq(d, Main.status.folder_digest(dg, p)) == True{} : Bool}) -> {M.rewrites.same(dg, Bool.pick(List<&2, M.Act>, a, [M.Act.Stop{"this store does not hold the content " ++ d}], Bool.pick(List<&2, M.Act>, b, [M.Act.Said{M.LEFT_UNRECORDED(p)}], [M.Act.Whole{p, from, d, m}]))) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          AL.and_intro(String.eq(d, Main.status.folder_digest(dg, p)), True{}, hd, {==})

# A file of bytes holding the payload already has it laid again, and
# nothing else.
def whole_same(y: Maybe<&2, String>, +f: String, +located: Map<&2, String>, +dg: Map<&2, String>, +p: String, +hs: List<&2, String>, +m: Tree.Mode, h: {Upd.records.payload(Main.status.folder_digest(dg, p), y) == True{} : Bool}) -> {M.rewrites.same(dg, M.laid.acts(M.lay.whole(p, f, Nil{}, located, Main.status.folder_digest(dg, p), hs, m, y))) == True{} : Bool}:
  match y:
    case None{}:
      Empty.absurd({M.rewrites.same(dg, M.laid.acts(M.lay.whole(p, f, Nil{}, located, Main.status.folder_digest(dg, p), hs, m, None{}))) == True{} : Bool}, Comp.false_true(h))
    case Some{+d}:
      whole_same.pick(String.is_empty(Main.stat_of(d, Map.get(String, SNil{}, located, d))), M.unrecorded(Main.status.folder_digest(dg, p), d <> hs), dg, p, Main.stat_of(d, Map.get(String, SNil{}, located, d)), d, m, h)

def lands_of(h: Upd.Held, +s: String, -S: String, eS: {S == s : String}, hy: {Upd.holds.link(h, S) == True{} : Bool}) -> {Upd.lands.link(s, h) == True{} : Bool}:
  match h:
    case Upd.Held.Link{w}:
      %eS : {String.eq(w, _) == True{} : Bool}
      hy
    case Upd.Held.File{d, r}:
      Empty.absurd({Upd.lands.link(s, Upd.Held.File{d, r}) == True{} : Bool}, Comp.false_true(hy))
    case Upd.Held.Dir{}:
      Empty.absurd({Upd.lands.link(s, Upd.Held.Dir{}) == True{} : Bool}, Comp.false_true(hy))
    case Upd.Held.Unread{}:
      Empty.absurd({Upd.lands.link(s, Upd.Held.Unread{}) == True{} : Bool}, Comp.false_true(hy))
    case Upd.Held.Other{}:
      Empty.absurd({Upd.lands.link(s, Upd.Held.Other{}) == True{} : Bool}, Comp.false_true(hy))
    case Upd.Held.Nothing{}:
      Empty.absurd({Upd.lands.link(s, Upd.Held.Nothing{}) == True{} : Bool}, Comp.false_true(hy))

def link_same.some(mm: Maybe<&2, String>, +t: Tree.Tree(), +dg: Map<&2, String>, +p: String, +v: Tree.Target, +h: Upd.Held, +em: {Upd.materialise(t, p, v) == mm : Maybe<&2, String>}, hy: {Upd.holds.link(h, Main.materialise(t, p, v)) == True{} : Bool}) -> {M.rewrites.same(dg, M.laid.acts(M.lay.link(p, h, mm))) == True{} : Bool}:
  match mm:
    case None{}:
      {==}
    case Some{+s}:
      %Equal.sym(Bool, Upd.lands.link(s, h), True{}, lands_of(h, s, Main.materialise(t, p, v), UpdL.spelled_same(t, p, v, s, em), hy)) : {M.rewrites.same(dg, Bool.pick(List<&2, M.Act>, _, Nil{}, [M.Act.Link{p, s}])) == True{} : Bool}
      {==}

# A link already pointing where `cat` says is not pointed again.
def link_same(g: Maybe<&2, Tree.Target>, +t: Tree.Tree(), +dg: Map<&2, String>, +p: String, +h: Upd.Held, hy: {Upd.holds.target(h, t, p, g) == True{} : Bool}) -> {M.rewrites.same(dg, M.laid.acts(M.lay.link(p, h, Maybe.bind(&2, Tree.Target, String, g, x2 => Upd.materialise(t, p, x2))))) == True{} : Bool}:
  match g:
    case None{}:
      Empty.absurd({M.rewrites.same(dg, M.laid.acts(M.lay.link(p, h, None{}))) == True{} : Bool}, Comp.false_true(hy))
    case Some{+v}:
      link_same.some(Upd.materialise(t, p, v), t, dg, p, v, h, {==}, hy)

def merged_one(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +ls: Map<&2, String>, +located: Map<&2, String>, e: Tree.Entry, h: {M.already.one(fs, ds, heads, t, dg, ls, e) == True{} : Bool}) -> {M.rewrites.same(dg, M.laid.acts(M.lay(t, Nil{}, located, M.place(fs, ds, heads, Nil{}, dg, ls, texts, e)))) == True{} : Bool}:
  match e:
    case Tree.Entry{+f, +p, Tree.Lines{}, y, g, +m}:
      lines_same(Main.joined(fs, ds, heads, f), dg, p, M.head.lines(fs, ds, f, heads), M.text.at(texts, p), m, h)
    case Tree.Entry{+f, +p, Tree.Whole{}, +y, g, +m}:
      whole_same(y, f, located, dg, p, M.head.wholes(fs, f, heads), m, h)
    case Tree.Entry{f, +p, Tree.Link{}, y, +g, m}:
      link_same(g, t, dg, p, Upd.held.of(ls, p, None{}), h)

# Over every file of the merged tree.
def merged_all(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +ls: Map<&2, String>, +located: Map<&2, String>, es: List<&2, Tree.Entry>, +h: {M.already(fs, ds, heads, t, dg, ls, es) == True{} : Bool}) -> {M.rewrites.same(dg, M.lay.acts(M.lay.all(t, Nil{}, located, M.places(fs, ds, heads, Nil{}, dg, ls, texts, es)))) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      %Equal.sym(List<&2, M.Act>, M.lay.acts(M.lay(t, Nil{}, located, M.place(fs, ds, heads, Nil{}, dg, ls, texts, e)) <> M.lay.all(t, Nil{}, located, M.places(fs, ds, heads, Nil{}, dg, ls, texts, rest))), List.append(&2, M.Act, M.laid.acts(M.lay(t, Nil{}, located, M.place(fs, ds, heads, Nil{}, dg, ls, texts, e))), M.lay.acts(M.lay.all(t, Nil{}, located, M.places(fs, ds, heads, Nil{}, dg, ls, texts, rest)))), acts_cons(M.lay(t, Nil{}, located, M.place(fs, ds, heads, Nil{}, dg, ls, texts, e)), M.lay.all(t, Nil{}, located, M.places(fs, ds, heads, Nil{}, dg, ls, texts, rest)))) : {M.rewrites.same(dg, _) == True{} : Bool}
      same_app(dg, M.laid.acts(M.lay(t, Nil{}, located, M.place(fs, ds, heads, Nil{}, dg, ls, texts, e))), M.lay.acts(M.lay.all(t, Nil{}, located, M.places(fs, ds, heads, Nil{}, dg, ls, texts, rest))),
        merged_one(fs, ds, heads, t, dg, texts, ls, located, e, Comp.and_left(M.already.one(fs, ds, heads, t, dg, ls, e), M.already(fs, ds, heads, t, dg, ls, rest), h)),
        merged_all(fs, ds, heads, t, dg, texts, ls, located, rest, Comp.and_right(M.already.one(fs, ds, heads, t, dg, ls, e), M.already(fs, ds, heads, t, dg, ls, rest), h)))

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

def named_pick(c: Bool, +a: String, +b: String, +rest: List<&2, T.Split>, +k: String, +v: String, +eb: {String.eq(a, k) == c : Bool}, h: {Bool.pick(Maybe<&2, String>, c, Some{b}, M.split.get(rest, k)) == Some{v} : Maybe<&2, String>}, ih: {M.split.get(rest, k) == Some{v} : Maybe<&2, String>} -> {M.split.named(rest, k) == True{} : Bool}) -> {Bool.or(String.eq(a, k), M.split.named(rest, k)) == True{} : Bool}:
  match c:
    case True{}:
      AL.or_left(String.eq(a, k), M.split.named(rest, k), eb)
    case False{}:
      AL.or_right(String.eq(a, k), M.split.named(rest, k), ih(h))

# A file `beside` gives a name is one it names.
def get_named(xs: List<&2, T.Split>, +k: String, +v: String, h: {M.split.get(xs, k) == Some{v} : Maybe<&2, String>}) -> {M.split.named(xs, k) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({M.split.named(Nil{}, k) == True{} : Bool}, UpdL.none_some(v, h))
    case T.Split{+a, +b} <> +rest:
      named_pick(String.eq(a, k), a, b, rest, k, v, {==}, h, h2 => get_named(rest, k, v, h2))

def none_pick(c: Bool, +a: String, +b: String, +rest: List<&2, T.Split>, +k: String, h: {Bool.pick(Maybe<&2, String>, c, Some{b}, M.split.get(rest, k)) == None{} : Maybe<&2, String>}, ih: {M.split.get(rest, k) == None{} : Maybe<&2, String>} -> {M.split.named(rest, k) == False{} : Bool}) -> {Bool.or(c, M.split.named(rest, k)) == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, UpdL.none_some(b, Equal.sym(Maybe<&2, String>, Some{b}, None{}, h)))
    case False{}:
      ih(h)

# And one it gives none is not.
def get_none(xs: List<&2, T.Split>, +k: String, h: {M.split.get(xs, k) == None{} : Maybe<&2, String>}) -> {M.split.named(xs, k) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case T.Split{+a, +b} <> +rest:
      none_pick(String.eq(a, k), a, b, rest, k, h, h2 => get_none(rest, k, h2))

def at_pick(mm: Maybe<&2, String>, +bs: List<&2, T.Split>, +f: String, +p: String, +em: {M.split.get(bs, f) == mm : Maybe<&2, String>}) -> {M.at.is(bs, f, p, Maybe.default(&2, String, mm, p)) == True{} : Bool}:
  match mm:
    case None{}:
      %Equal.sym(Bool, M.split.named(bs, f), False{}, get_none(bs, f, em)) : {Bool.pick(Bool, _, M.split.has(bs, f, p), String.eq(p, p)) == True{} : Bool}
      S.eq_refl(p)
    case Some{+b}:
      %Equal.sym(Bool, M.split.named(bs, f), True{}, get_named(bs, f, b, em)) : {Bool.pick(Bool, _, M.split.has(bs, f, b), String.eq(b, p)) == True{} : Bool}
      get_has(bs, f, b, em)

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

# A file of lines: written as the walk of the heads renders it, and only
# over nothing, no text, what it writes, the walk unfenced, or what a head
# reads.
def lines_written(c: Bool, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +f: String, +p: String, +y: Maybe<&2, String>, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, +at: String, +hat: {M.at.is(bs, f, p, at) == True{} : Bool}, +j: Conflict.Joined, +er: {Main.joined(fs, ds, heads, f) == Done{j} : Result<&2, &2, String, Conflict.Joined>}, +ec: {Bool.and(M.text.at(texts, at), M.unrecorded(Main.status.folder_digest(dg, at), Upd.text_digest(Conflict.render(j)) <> Upd.text_digest(Conflict.plain(j)) <> M.head.lines(fs, ds, f, heads))) == c : Bool}) -> {M.laid.by(fs, ds, heads, bs, t, dg, texts, Tree.Entry{f, p, Tree.Lines{}, y, g, m}, Bool.pick(List<&2, M.Act>, c, [M.Act.Said{M.LEFT_UNRECORDED(at)}], [M.Act.Lines{at, Conflict.render(j), m}])) == True{} : Bool}:
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

def lines_each(r: Result<&2, &2, String, Conflict.Joined>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +f: String, +p: String, +y: Maybe<&2, String>, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, +at: String, +hat: {M.at.is(bs, f, p, at) == True{} : Bool}, +er: {Main.joined(fs, ds, heads, f) == r : Result<&2, &2, String, Conflict.Joined>}) -> {M.laid.by(fs, ds, heads, bs, t, dg, texts, Tree.Entry{f, p, Tree.Lines{}, y, g, m}, M.laid.acts(M.lay.lines(at, Main.status.folder_digest(dg, at), M.head.lines(fs, ds, f, heads), M.text.at(texts, at), m, r))) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+j}:
      lines_written(Bool.and(M.text.at(texts, at), M.unrecorded(Main.status.folder_digest(dg, at), Upd.text_digest(Conflict.render(j)) <> Upd.text_digest(Conflict.plain(j)) <> M.head.lines(fs, ds, f, heads))), fs, ds, heads, bs, t, dg, texts, f, p, y, g, m, at, hat, j, er, {==})

# A file of bytes: the payload its tree names, laid only over nothing, the
# payload, or what a head's tree names.
def cat_each(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +f: String, +p: String, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, +at: String, cs: List<&2, Tree.Claim>) -> {M.laid.by(fs, ds, heads, bs, t, dg, texts, Tree.Entry{f, p, Tree.Whole{}, None{}, g, m}, M.claims.cat(at, cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Tree.Claim{by, w} <> rest:
      cat_each(fs, ds, heads, bs, t, dg, texts, f, p, g, m, at, rest)

def whole_written(c: Bool, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +f: String, +p: String, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, +at: String, +hat: {M.at.is(bs, f, p, at) == True{} : Bool}, +pay: String, +from: String, +ec: {M.unrecorded(Main.status.folder_digest(dg, at), pay <> M.head.wholes(fs, f, heads)) == c : Bool}) -> {M.laid.by(fs, ds, heads, bs, t, dg, texts, Tree.Entry{f, p, Tree.Whole{}, Some{pay}, g, m}, Bool.pick(List<&2, M.Act>, c, [M.Act.Said{M.LEFT_UNRECORDED(at)}], [M.Act.Whole{at, from, pay, m}])) == True{} : Bool}:
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

def whole_found(c: Bool, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +f: String, +p: String, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, +at: String, +hat: {M.at.is(bs, f, p, at) == True{} : Bool}, +pay: String, +from: String) -> {M.laid.by(fs, ds, heads, bs, t, dg, texts, Tree.Entry{f, p, Tree.Whole{}, Some{pay}, g, m}, Bool.pick(List<&2, M.Act>, c, [M.Act.Stop{"this store does not hold the content " ++ pay}], Bool.pick(List<&2, M.Act>, M.unrecorded(Main.status.folder_digest(dg, at), pay <> M.head.wholes(fs, f, heads)), [M.Act.Said{M.LEFT_UNRECORDED(at)}], [M.Act.Whole{at, from, pay, m}]))) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      whole_written(M.unrecorded(Main.status.folder_digest(dg, at), pay <> M.head.wholes(fs, f, heads)), fs, ds, heads, bs, t, dg, texts, f, p, g, m, at, hat, pay, from, {==})

def whole_each(y: Maybe<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +f: String, +p: String, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, +at: String, +hat: {M.at.is(bs, f, p, at) == True{} : Bool}, +cs: List<&2, Tree.Contest>, +located: Map<&2, String>) -> {M.laid.by(fs, ds, heads, bs, t, dg, texts, Tree.Entry{f, p, Tree.Whole{}, y, g, m}, M.laid.acts(M.lay.whole(at, f, cs, located, Main.status.folder_digest(dg, at), M.head.wholes(fs, f, heads), m, y))) == True{} : Bool}:
  match y:
    case None{}:
      cat_each(fs, ds, heads, bs, t, dg, texts, f, p, g, m, at, M.payload.claims(cs, f))
    case Some{+pay}:
      whole_found(String.is_empty(Main.stat_of(pay, Map.get(String, SNil{}, located, pay))), fs, ds, heads, bs, t, dg, texts, f, p, g, m, at, hat, pay, Main.stat_of(pay, Map.get(String, SNil{}, located, pay)))

# A link: pointed where `cat` says it points.
def link_pick(c: Bool, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +f: String, +p: String, +y: Maybe<&2, String>, +v: Tree.Target, +m: Tree.Mode, +at: String, +hat: {M.at.is(bs, f, p, at) == True{} : Bool}, +s: String, +es: {Main.materialise(t, at, v) == s : String}) -> {M.laid.by(fs, ds, heads, bs, t, dg, texts, Tree.Entry{f, p, Tree.Link{}, y, Some{v}, m}, Bool.pick(List<&2, M.Act>, c, Nil{}, [M.Act.Link{at, s}])) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      AL.and_intro(Bool.and(M.at.is(bs, f, p, at), String.eq(s, Main.materialise(t, at, v))), True{},
        AL.and_intro(M.at.is(bs, f, p, at), String.eq(s, Main.materialise(t, at, v)), hat,
          (%Equal.sym(String, Main.materialise(t, at, v), s, es) : {String.eq(s, _) == True{} : Bool}
            S.eq_refl(s))),
        {==})

def link_some(mm: Maybe<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +f: String, +p: String, +y: Maybe<&2, String>, +v: Tree.Target, +m: Tree.Mode, +at: String, +hat: {M.at.is(bs, f, p, at) == True{} : Bool}, +em: {Upd.materialise(t, at, v) == mm : Maybe<&2, String>}, +h: Upd.Held) -> {M.laid.by(fs, ds, heads, bs, t, dg, texts, Tree.Entry{f, p, Tree.Link{}, y, Some{v}, m}, M.laid.acts(M.lay.link(at, h, mm))) == True{} : Bool}:
  match mm:
    case None{}:
      {==}
    case Some{+s}:
      link_pick(Upd.lands.link(s, h), fs, ds, heads, bs, t, dg, texts, f, p, y, v, m, at, hat, s, UpdL.spelled_same(t, at, v, s, em))

def link_each(g: Maybe<&2, Tree.Target>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +f: String, +p: String, +y: Maybe<&2, String>, +m: Tree.Mode, +at: String, +hat: {M.at.is(bs, f, p, at) == True{} : Bool}, +h: Upd.Held) -> {M.laid.by(fs, ds, heads, bs, t, dg, texts, Tree.Entry{f, p, Tree.Link{}, y, g, m}, M.laid.acts(M.lay.link(at, h, Maybe.bind(&2, Tree.Target, String, g, x2 => Upd.materialise(t, at, x2))))) == True{} : Bool}:
  match g:
    case None{}:
      {==}
    case Some{+v}:
      link_some(Upd.materialise(t, at, v), fs, ds, heads, bs, t, dg, texts, f, p, y, v, m, at, hat, {==}, h)

# Whatever `merge` does at one file of the merged tree is what the store
# and the folder say it may.
def lay_each(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +ls: Map<&2, String>, +cs: List<&2, Tree.Contest>, +located: Map<&2, String>, e: Tree.Entry) -> {M.laid.by(fs, ds, heads, bs, t, dg, texts, e, M.laid.acts(M.lay(t, cs, located, M.place(fs, ds, heads, bs, dg, ls, texts, e)))) == True{} : Bool}:
  match e:
    case Tree.Entry{+f, +p, Tree.Lines{}, +y, +g, +m}:
      lines_each(Main.joined(fs, ds, heads, f), fs, ds, heads, bs, t, dg, texts, f, p, y, g, m, Maybe.default(&2, String, M.split.get(bs, f), p), at_pick(M.split.get(bs, f), bs, f, p, {==}), {==})
    case Tree.Entry{+f, +p, Tree.Whole{}, +y, +g, +m}:
      whole_each(y, fs, ds, heads, bs, t, dg, texts, f, p, g, m, Maybe.default(&2, String, M.split.get(bs, f), p), at_pick(M.split.get(bs, f), bs, f, p, {==}), cs, located)
    case Tree.Entry{+f, +p, Tree.Link{}, +y, +g, +m}:
      link_each(g, fs, ds, heads, bs, t, dg, texts, f, p, y, m, Maybe.default(&2, String, M.split.get(bs, f), p), at_pick(M.split.get(bs, f), bs, f, p, {==}), Upd.held.of(ls, Maybe.default(&2, String, M.split.get(bs, f), p), None{}))

# Every act, file by file
# -----------------------

# Whatever `merge` does, file by file over the merged tree, the file it is
# done for accounts for as the store and the folder read it.
def spares(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +t: Tree.Tree(), +dg: Map<&2, String>, +texts: Map<&2, String>, +ls: Map<&2, String>, +cs: List<&2, Tree.Contest>, +located: Map<&2, String>, es: List<&2, Tree.Entry>) -> {M.laid.files(fs, ds, heads, bs, t, dg, texts, es, M.lay.all(t, cs, located, M.places(fs, ds, heads, bs, dg, ls, texts, es))) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      AL.and_intro(M.laid.by(fs, ds, heads, bs, t, dg, texts, e, M.laid.acts(M.lay(t, cs, located, M.place(fs, ds, heads, bs, dg, ls, texts, e)))), M.laid.files(fs, ds, heads, bs, t, dg, texts, rest, M.lay.all(t, cs, located, M.places(fs, ds, heads, bs, dg, ls, texts, rest))),
        lay_each(fs, ds, heads, bs, t, dg, texts, ls, cs, located, e),
        spares(fs, ds, heads, bs, t, dg, texts, ls, cs, located, rest))

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


# The markers `merge` writes are the ones counted
# -----------------------------------------------

# The marker search and a list's own membership read a line the same way.
def any_member(xs: List<&2, String>, +x: String) -> {Conflict.any_eq(xs, x) == Rev.member(xs, x) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +rest:
      %any_member(rest, x) : {Bool.or(String.eq(y, x), Conflict.any_eq(rest, x)) == Bool.or(String.eq(y, x), _) : Bool}
      {==}

def not_pick.eq(e: Bool, +k: String, +l: String, +pl: List<&2, String>, +later: List<&2, String>, +ee: {String.eq(k, l) == e : Bool}, +ec: {Bool.and(Conflict.is_marker(k), Bool.not(Conflict.any_eq(pl, k))) == True{} : Bool}, +hl: {Conflict.any_eq(pl, l) == True{} : Bool}, ih: {Conflict.any_eq(later, l) == False{} : Bool}) -> {Bool.or(e, Conflict.any_eq(later, l)) == False{} : Bool}:
  match e:
    case True{}:
      Empty.absurd({True{} == False{} : Bool},
        Comp.false_true(
          (%hl : {Bool.not(_) == True{} : Bool}
            %S.eq_true(k, l, ee) : {Bool.not(Conflict.any_eq(pl, _)) == True{} : Bool}
            Comp.and_right(Conflict.is_marker(k), Bool.not(Conflict.any_eq(pl, k)), ec))))
    case False{}:
      ih

def not_pick.hit(c: Bool, +k: String, +l: String, +pl: List<&2, String>, +later: List<&2, String>, +ec: {Bool.and(Conflict.is_marker(k), Bool.not(Conflict.any_eq(pl, k))) == c : Bool}, +hl: {Conflict.any_eq(pl, l) == True{} : Bool}, ih: {Conflict.any_eq(later, l) == False{} : Bool}) -> {Conflict.any_eq(Bool.pick(List<&2, String>, c, k <> later, later), l) == False{} : Bool}:
  match c:
    case True{}:
      not_pick.eq(String.eq(k, l), k, l, pl, later, {==}, ec, hl, ih)
    case False{}:
      ih

# A line the walk's reading holds is no marker of this merge.
def not_marker(ls: List<&2, String>, +pl: List<&2, String>, +l: String, +hl: {Conflict.any_eq(pl, l) == True{} : Bool}) -> {Conflict.any_eq(Conflict.markers.go(ls, pl), l) == False{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case +k <> +rest:
      not_pick.hit(Bool.and(Conflict.is_marker(k), Bool.not(Conflict.any_eq(pl, k))), k, l, pl, Conflict.markers.go(rest, pl), {==}, hl, not_marker(rest, pl, l, hl))

def zero_standing(ls: List<&2, String>, +rl: List<&2, String>, +pl: List<&2, String>, +hall: {Main.all_held(pl, ls) == True{} : Bool}) -> {Conflict.standing.go(ls, Conflict.markers.go(rl, pl)) == Nil{} : List<&2, String>}:
  match ls:
    case Nil{}:
      {==}
    case +l <> +rest:
      %Equal.sym(Bool, Conflict.any_eq(Conflict.markers.go(rl, pl), l), False{}, not_marker(rl, pl, l, (%Equal.sym(Bool, Conflict.any_eq(pl, l), Rev.member(pl, l), any_member(pl, l)) : {_ == True{} : Bool} Comp.and_left(Rev.member(pl, l), Main.all_held(pl, rest), hall)))) : {Bool.pick(List<&2, String>, _, l <> Conflict.standing.go(rest, Conflict.markers.go(rl, pl)), Conflict.standing.go(rest, Conflict.markers.go(rl, pl))) == Nil{} : List<&2, String>}
      zero_standing(rest, rl, pl, Comp.and_right(Rev.member(pl, l), Main.all_held(pl, rest), hall))

# The walk's reading unfenced is counted as holding no marker at all.
def plain_unmarked(+j: Conflict.Joined) -> {Main.status.marked.of(Conflict.plain(j), Some{Done{j}}) == 0n : Nat}:
  %Equal.sym(List<&2, String>, Conflict.standing.go(Conflict.lines(Conflict.plain(j)), Conflict.markers.go(Conflict.lines(Conflict.render(j)), Conflict.lines(Conflict.plain(j)))), Nil{}, zero_standing(Conflict.lines(Conflict.plain(j)), Conflict.lines(Conflict.render(j)), Conflict.lines(Conflict.plain(j)), RewriteL.held_refl(Conflict.lines(Conflict.plain(j))))) : {List.length(&2, String, _) == 0n : Nat}
  {==}

# The label the renderer writes, and the line closing a fence, are lines
# the marker search takes for its own.
def label_marks(+names: List<&2, String>, +a: Nat) -> {Conflict.is_marker(Conflict.label.line(names, a)) == True{} : Bool}:
  AL.or_left(Bool.and(String.starts_with(Conflict.label.line(names, a), "vvv historica: "), Bool.or(String.ends_with(Conflict.label.line(names, a), "vvv"), String.ends_with(Conflict.label.line(names, a), "^^^"))), String.starts_with(Conflict.label.line(names, a), "^^^ historica: "),
    AL.and_intro(String.starts_with(Conflict.label.line(names, a), "vvv historica: "), Bool.or(String.ends_with(Conflict.label.line(names, a), "vvv"), String.ends_with(Conflict.label.line(names, a), "^^^")),
      UpdL.starts_nil(String.take(Conflict.name_at(names, a), 8n) ++ " wrote vvv"),
      AL.or_left(String.ends_with(Conflict.label.line(names, a), "vvv"), String.ends_with(Conflict.label.line(names, a), "^^^"),
        B.ends_pre("vvv historica: ", String.take(Conflict.name_at(names, a), 8n) ++ " wrote vvv", "vvv", B.ends_pre(String.take(Conflict.name_at(names, a), 8n), " wrote vvv", "vvv", {==})))))

def closing_marks() -> {Conflict.is_marker(Conflict.closing.line()) == True{} : Bool}:
  {==}

def fence_marks(+j: Conflict.Joined, +x: String, +a: Nat, h: {Bool.or(String.eq(x, Conflict.closing.line()), String.eq(x, Conflict.label.line(Conflict.joined.names(j), a))) == True{} : Bool}) -> {Conflict.is_marker(x) == True{} : Bool}:
  AL.or_cases({Conflict.is_marker(x) == True{} : Bool}, String.eq(x, Conflict.closing.line()), String.eq(x, Conflict.label.line(Conflict.joined.names(j), a)), h,
    l => (%Equal.sym(String, x, Conflict.closing.line(), S.eq_true(x, Conflict.closing.line(), l)) : {Conflict.is_marker(_) == True{} : Bool}
      closing_marks()),
    r => (%Equal.sym(String, x, Conflict.label.line(Conflict.joined.names(j), a), S.eq_true(x, Conflict.label.line(Conflict.joined.names(j), a), r)) : {Conflict.is_marker(_) == True{} : Bool}
      label_marks(Conflict.joined.names(j), a)))

def has_pick(c: Bool, +l: String, +x: String, +later: List<&2, String>, ih: {Conflict.any_eq(later, x) == True{} : Bool}) -> {Conflict.any_eq(Bool.pick(List<&2, String>, c, l <> later, later), x) == True{} : Bool}:
  match c:
    case True{}:
      AL.or_right(String.eq(l, x), Conflict.any_eq(later, x), ih)
    case False{}:
      ih

# A marker standing in the rendering, and no line of the walk's reading, is
# among the lines the renderer wrote on its own account.
def markers_has(ls: List<&2, String>, +pl: List<&2, String>, +x: String, h1: {Rev.member(ls, x) == True{} : Bool}, +hm: {Conflict.is_marker(x) == True{} : Bool}, +hp: {Conflict.any_eq(pl, x) == False{} : Bool}) -> {Conflict.any_eq(Conflict.markers.go(ls, pl), x) == True{} : Bool}:
  match ls:
    case Nil{}:
      Empty.absurd({Conflict.any_eq(Nil{}, x) == True{} : Bool}, Comp.false_true(h1))
    case +l <> +rest:
      AL.or_cases({Conflict.any_eq(Bool.pick(List<&2, String>, Bool.and(Conflict.is_marker(l), Bool.not(Conflict.any_eq(pl, l))), l <> Conflict.markers.go(rest, pl), Conflict.markers.go(rest, pl)), x) == True{} : Bool}, String.eq(l, x), Rev.member(rest, x), h1,
        e => (%Equal.sym(String, l, x, S.eq_true(l, x, e)) : {Conflict.any_eq(Bool.pick(List<&2, String>, Bool.and(Conflict.is_marker(_), Bool.not(Conflict.any_eq(pl, _))), _ <> Conflict.markers.go(rest, pl), Conflict.markers.go(rest, pl)), x) == True{} : Bool}
          %Equal.sym(Bool, Conflict.is_marker(x), True{}, hm) : {Conflict.any_eq(Bool.pick(List<&2, String>, Bool.and(_, Bool.not(Conflict.any_eq(pl, x))), x <> Conflict.markers.go(rest, pl), Conflict.markers.go(rest, pl)), x) == True{} : Bool}
          %Equal.sym(Bool, Conflict.any_eq(pl, x), False{}, hp) : {Conflict.any_eq(Bool.pick(List<&2, String>, Bool.and(True{}, Bool.not(_)), x <> Conflict.markers.go(rest, pl), Conflict.markers.go(rest, pl)), x) == True{} : Bool}
          AL.or_left(String.eq(x, x), Conflict.any_eq(Conflict.markers.go(rest, pl), x), S.eq_refl(x))),
        r => has_pick(Bool.and(Conflict.is_marker(l), Bool.not(Conflict.any_eq(pl, l))), l, x, Conflict.markers.go(rest, pl), markers_has(rest, pl, x, r, hm, hp)))

def pos_pick(c: Bool, +l: String, +later: List<&2, String>, ih: {Nat.is_gt(List.length(&2, String, later), 0n) == True{} : Bool}) -> {Nat.is_gt(List.length(&2, String, Bool.pick(List<&2, String>, c, l <> later, later)), 0n) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      ih

# A line of a file among the markers is counted.
def standing_pos(ls: List<&2, String>, +ms: List<&2, String>, +x: String, h1: {Rev.member(ls, x) == True{} : Bool}, +h2: {Conflict.any_eq(ms, x) == True{} : Bool}) -> {Nat.is_gt(List.length(&2, String, Conflict.standing.go(ls, ms)), 0n) == True{} : Bool}:
  match ls:
    case Nil{}:
      Empty.absurd({Nat.is_gt(0n, 0n) == True{} : Bool}, Comp.false_true(h1))
    case +l <> +rest:
      AL.or_cases({Nat.is_gt(List.length(&2, String, Bool.pick(List<&2, String>, Conflict.any_eq(ms, l), l <> Conflict.standing.go(rest, ms), Conflict.standing.go(rest, ms))), 0n) == True{} : Bool}, String.eq(l, x), Rev.member(rest, x), h1,
        e => (%Equal.sym(String, l, x, S.eq_true(l, x, e)) : {Nat.is_gt(List.length(&2, String, Bool.pick(List<&2, String>, Conflict.any_eq(ms, _), l <> Conflict.standing.go(rest, ms), Conflict.standing.go(rest, ms))), 0n) == True{} : Bool}
          %Equal.sym(Bool, Conflict.any_eq(ms, x), True{}, h2) : {Nat.is_gt(List.length(&2, String, Bool.pick(List<&2, String>, _, l <> Conflict.standing.go(rest, ms), Conflict.standing.go(rest, ms))), 0n) == True{} : Bool}
          {==}),
        r => pos_pick(Conflict.any_eq(ms, l), l, Conflict.standing.go(rest, ms), standing_pos(rest, ms, x, r, h2)))

# In the file `merge` renders, a fence line standing on its own that the
# walk's reading does not hold is counted as marked.
def fences_counted(+j: Conflict.Joined, +x: String, +a: Nat, +h1: {Rev.member(Conflict.lines(Conflict.render(j)), x) == True{} : Bool}, h2: {Rev.member(Conflict.lines(Conflict.plain(j)), x) == False{} : Bool}, h3: {Bool.or(String.eq(x, Conflict.closing.line()), String.eq(x, Conflict.label.line(Conflict.joined.names(j), a))) == True{} : Bool}) -> {Nat.is_gt(Main.status.marked.of(Conflict.render(j), Some{Done{j}}), 0n) == True{} : Bool}:
  standing_pos(Conflict.lines(Conflict.render(j)), Conflict.markers(j), x, h1,
    markers_has(Conflict.lines(Conflict.render(j)), Conflict.lines(Conflict.plain(j)), x, h1, fence_marks(j, x, a, h3),
      (%Equal.sym(Bool, Conflict.any_eq(Conflict.lines(Conflict.plain(j)), x), Rev.member(Conflict.lines(Conflict.plain(j)), x), any_member(Conflict.lines(Conflict.plain(j)), x)) : {_ == False{} : Bool}
        h2)))

# The `record` line reads back
# ----------------------------

def join_cons(p: String, r: List<&2, String>, ne: {Spell.nonempty(String, r) == True{} : Bool}) -> {String.join(p <> r, "=") == p ++ ("=" ++ String.join(r, "=")) : String}:
  match r:
    case Nil{}:
      Empty.absurd({String.join([p], "=") == p ++ ("=" ++ String.join(Nil{}, "=")) : String}, Comp.false_true(ne))
    case q <> more:
      {==}

def join_push(c: Char, r: List<&2, String>, ne: {Spell.nonempty(String, r) == True{} : Bool}) -> {String.join(String.split.push(c, r), "=") == SCon{c, String.join(r, "=")} : String}:
  match r:
    case Nil{}:
      Empty.absurd({String.join(String.split.push(c, Nil{}), "=") == SCon{c, String.join(Nil{}, "=")} : String}, Comp.false_true(ne))
    case p <> Nil{}:
      {==}
    case p <> q <> more:
      {==}

def join_split.fin(h: Char, +t: String, cut: Bool, eq: {Char.is_eq(h, '=') == cut : Bool}, ih: {String.join(String.split(t, '='), "=") == t : String}) -> {String.join(String.split.fin(h, String.split(t, '='), cut), "=") == SCon{h, t} : String}:
  match cut:
    case True{}:
      %Equal.sym(String, String.join(SNil{} <> String.split(t, '='), "="), SNil{} ++ ("=" ++ String.join(String.split(t, '='), "=")), join_cons(SNil{}, String.split(t, '='), Spell.split_nonempty(t, '='))) : {_ == SCon{h, t} : String}
      %Equal.sym(String, String.join(String.split(t, '='), "="), t, ih) : {SCon{'=', _} == SCon{h, t} : String}
      %Eq.char_eq(h, '=', eq) : {SCon{_, t} == SCon{h, t} : String}
      {==}
    case False{}:
      %Equal.sym(String, String.join(String.split.push(h, String.split(t, '=')), "="), SCon{h, String.join(String.split(t, '='), "=")}, join_push(h, String.split(t, '='), Spell.split_nonempty(t, '='))) : {_ == SCon{h, t} : String}
      %Equal.sym(String, String.join(String.split(t, '='), "="), t, ih) : {SCon{h, _} == SCon{h, t} : String}
      {==}

# Cut at every `=` and joined again with one, a string is itself.
def join_split(s: String) -> {String.join(String.split(s, '='), "=") == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      join_split.fin(h, t, Char.is_eq(h, '='), {==}, join_split(t))

# A name with no `=` in it, then one: the name, then the rest cut.
def split_pre(f: String, -r: String, +h: {M.no.equals(f) == True{} : Bool}) -> {String.split(f ++ SCon{'=', r}, '=') == f <> String.split(r, '=') : List<&2, String>}:
  match f:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Equal.trans(List<&2, String>, String.split.fin(c, String.split(t ++ SCon{'=', r}, '='), Char.is_eq(c, '=')), String.split.fin(c, String.split(t ++ SCon{'=', r}, '='), False{}), SCon{c, t} <> String.split(r, '='),
        Equal.cong(Bool, List<&2, String>, b => String.split.fin(c, String.split(t ++ SCon{'=', r}, '='), b), Char.is_eq(c, '='), False{}, AL.not_of_true(Char.is_eq(c, '='), Comp.and_left(Bool.not(Char.is_eq(c, '=')), M.no.equals(t), h))),
        Equal.cong(List<&2, String>, List<&2, String>, l => String.split.push(c, l), String.split(t ++ SCon{'=', r}, '='), t <> String.split(r, '='), split_pre(t, r, Comp.and_right(Bool.not(Char.is_eq(c, '=')), M.no.equals(t), h))))

def at_split.of(r: List<&2, String>, +f: String, +p: String, +msg: String, +er: {String.split(p, '=') == r : List<&2, String>}, ne: {Spell.nonempty(String, r) == True{} : Bool}) -> {Main.record.split.of(msg, f <> r) == Done{T.Split{f, p}} : Result<&2, &2, Main.Refused, T.Split>}:
  match r:
    case Nil{}:
      Empty.absurd({Main.record.split.of(msg, [f]) == Done{T.Split{f, p}} : Result<&2, &2, Main.Refused, T.Split>}, Comp.false_true(ne))
    case +b <> +rest:
      %er : {Done{T.Split{f, String.join(_, "=")}} == Done{T.Split{f, p}} : Result<&2, &2, Main.Refused, T.Split>}
      %Equal.sym(String, String.join(String.split(p, '='), "="), p, join_split(p)) : {Done{T.Split{f, _}} == Done{T.Split{f, p}} : Result<&2, &2, Main.Refused, T.Split>}
      {==}

# `record` cuts `<file>=<path>` back into the file and the path.
def at_split(+f: String, +p: String, +msg: String, +h: {M.no.equals(f) == True{} : Bool}) -> {Main.record.split(f ++ ("=" ++ p), msg) == Done{T.Split{f, p}} : Result<&2, &2, Main.Refused, T.Split>}:
  %Equal.sym(List<&2, String>, String.split(f ++ SCon{'=', p}, '='), f <> String.split(p, '='), split_pre(f, p, h)) : {Main.record.split.of(msg, _) == Done{T.Split{f, p}} : Result<&2, &2, Main.Refused, T.Split>}
  at_split.of(String.split(p, '='), f, p, msg, {==}, Spell.split_nonempty(p, '='))

# Each `--merge` and its head, read back.
def merges_back(xs: List<&2, T.Split>, +rest: List<&2, String>, +o: Maybe<&2, String>, +ms: List<&2, String>, +ac: List<&2, String>, +at: List<&2, T.Split>, +mv: List<&2, T.Split>, +ks: List<&2, T.Split>, +ns: List<&2, String>, +d: Bool, +f: Bool, +mg: Maybe<&2, String>) -> {Main.record.args.go(List.append(&2, String, M.merges.words(xs), rest), Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, Main.rword(List.append(&2, String, M.merges.words(xs), rest))) == Main.record.args.go(rest, Main.RecordCmd{o, List.append(&2, String, ms, M.typed.spellings(xs)), ac, at, mv, ks, ns, d, f, mg}, Main.rword(rest)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}:
  match xs:
    case Nil{}:
      %Equal.sym(List<&2, String>, List.append(&2, String, ms, Nil{}), ms, SortL.lapp_nil(String, ms)) : {Main.record.args.go(rest, Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, Main.rword(rest)) == Main.record.args.go(rest, Main.RecordCmd{o, _, ac, at, mv, ks, ns, d, f, mg}, Main.rword(rest)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}
      {==}
    case T.Split{h, +s} <> +more:
      %SortL.app_assoc(String, ms, [s], M.typed.spellings(more)) : {Main.record.args.go(List.append(&2, String, M.merges.words(more), rest), Main.RecordCmd{o, List.append(&2, String, ms, [s]), ac, at, mv, ks, ns, d, f, mg}, Main.rword(List.append(&2, String, M.merges.words(more), rest))) == Main.record.args.go(rest, Main.RecordCmd{o, _, ac, at, mv, ks, ns, d, f, mg}, Main.rword(rest)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}
      merges_back(more, rest, o, List.append(&2, String, ms, [s]), ac, at, mv, ks, ns, d, f, mg)

# Each `--at` and its file and path, read back as the pair itself.
def ats_back(xs: List<&2, T.Split>, +rest: List<&2, String>, +o: Maybe<&2, String>, +ms: List<&2, String>, +ac: List<&2, String>, +at: List<&2, T.Split>, +mv: List<&2, T.Split>, +ks: List<&2, T.Split>, +ns: List<&2, String>, +d: Bool, +f: Bool, +mg: Maybe<&2, String>, +h: {SortL.all_ok(~T.Split, ~(x => M.id.plain(x)), xs) == True{} : Bool}) -> {Main.record.args.go(List.append(&2, String, M.ats.words(xs), rest), Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, Main.rword(List.append(&2, String, M.ats.words(xs), rest))) == Main.record.args.go(rest, Main.RecordCmd{o, ms, ac, List.append(&2, T.Split, at, xs), mv, ks, ns, d, f, mg}, Main.rword(rest)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}:
  match xs:
    case Nil{}:
      %Equal.sym(List<&2, T.Split>, List.append(&2, T.Split, at, Nil{}), at, SortL.lapp_nil(T.Split, at)) : {Main.record.args.go(rest, Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, Main.rword(rest)) == Main.record.args.go(rest, Main.RecordCmd{o, ms, ac, _, mv, ks, ns, d, f, mg}, Main.rword(rest)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}
      {==}
    case T.Split{+fi, +p} <> +more:
      %Equal.sym(Result<&2, &2, Main.Refused, T.Split>, Main.record.split(fi ++ ("=" ++ p), "`--at` is spelled `--at <file>=<path>`"), Done{T.Split{fi, p}}, at_split(fi, p, "`--at` is spelled `--at <file>=<path>`", Comp.and_left(M.id.plain(T.Split{fi, p}), SortL.all_ok(~T.Split, ~(x => M.id.plain(x)), more), h))) : {Result.bind(&2, &2, Main.Refused, T.Split, Main.RecordCmd, _, s2 => Main.record.args.go(List.append(&2, String, M.ats.words(more), rest), Main.rc.at(Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, s2), Main.rword(List.append(&2, String, M.ats.words(more), rest)))) == Main.record.args.go(rest, Main.RecordCmd{o, ms, ac, List.append(&2, T.Split, at, T.Split{fi, p} <> more), mv, ks, ns, d, f, mg}, Main.rword(rest)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}
      %SortL.app_assoc(T.Split, at, [T.Split{fi, p}], more) : {Main.record.args.go(List.append(&2, String, M.ats.words(more), rest), Main.RecordCmd{o, ms, ac, List.append(&2, T.Split, at, [T.Split{fi, p}]), mv, ks, ns, d, f, mg}, Main.rword(List.append(&2, String, M.ats.words(more), rest))) == Main.record.args.go(rest, Main.RecordCmd{o, ms, ac, _, mv, ks, ns, d, f, mg}, Main.rword(rest)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}
      ats_back(more, rest, o, ms, ac, List.append(&2, T.Split, at, [T.Split{fi, p}]), mv, ks, ns, d, f, mg, Comp.and_right(M.id.plain(T.Split{fi, p}), SortL.all_ok(~T.Split, ~(x => M.id.plain(x)), more), h))

# The words `merge` prints `record` reads as the merge it laid out.
def record_back(+typed: List<&2, T.Split>, +bs: List<&2, T.Split>, +h: {SortL.all_ok(~T.Split, ~(x => M.id.plain(x)), bs) == True{} : Bool}) -> {Main.record.args.r(M.record.words(typed, bs)) == Done{Main.RecordCmd{None{}, M.typed.spellings(typed), Nil{}, List.sort(~T.Split, ~(a => b => M.typed.le(a, b)), bs), Nil{}, Nil{}, Nil{}, False{}, False{}, Some{"<message>"}}} : Result<&2, &2, Main.Refused, Main.RecordCmd>}:
  %Equal.sym(Result<&2, &2, Main.Refused, Main.RecordCmd>, Main.record.args.go(List.append(&2, String, M.merges.words(typed), List.append(&2, String, M.ats.words(List.sort(~T.Split, ~(a => b => M.typed.le(a, b)), bs)), ["-m", "<message>"])), Main.RecordCmd{None{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, False{}, False{}, None{}}, Main.rword(List.append(&2, String, M.merges.words(typed), List.append(&2, String, M.ats.words(List.sort(~T.Split, ~(a => b => M.typed.le(a, b)), bs)), ["-m", "<message>"])))), Main.record.args.go(List.append(&2, String, M.ats.words(List.sort(~T.Split, ~(a => b => M.typed.le(a, b)), bs)), ["-m", "<message>"]), Main.RecordCmd{None{}, List.append(&2, String, Nil{}, M.typed.spellings(typed)), Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, False{}, False{}, None{}}, Main.rword(List.append(&2, String, M.ats.words(List.sort(~T.Split, ~(a => b => M.typed.le(a, b)), bs)), ["-m", "<message>"]))), merges_back(typed, List.append(&2, String, M.ats.words(List.sort(~T.Split, ~(a => b => M.typed.le(a, b)), bs)), ["-m", "<message>"]), None{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, False{}, False{}, None{})) : {_ == Done{Main.RecordCmd{None{}, M.typed.spellings(typed), Nil{}, List.sort(~T.Split, ~(a => b => M.typed.le(a, b)), bs), Nil{}, Nil{}, Nil{}, False{}, False{}, Some{"<message>"}}} : Result<&2, &2, Main.Refused, Main.RecordCmd>}
  %Equal.sym(Result<&2, &2, Main.Refused, Main.RecordCmd>, Main.record.args.go(List.append(&2, String, M.ats.words(List.sort(~T.Split, ~(a => b => M.typed.le(a, b)), bs)), ["-m", "<message>"]), Main.RecordCmd{None{}, M.typed.spellings(typed), Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, False{}, False{}, None{}}, Main.rword(List.append(&2, String, M.ats.words(List.sort(~T.Split, ~(a => b => M.typed.le(a, b)), bs)), ["-m", "<message>"]))), Main.record.args.go(["-m", "<message>"], Main.RecordCmd{None{}, M.typed.spellings(typed), Nil{}, List.append(&2, T.Split, Nil{}, List.sort(~T.Split, ~(a => b => M.typed.le(a, b)), bs)), Nil{}, Nil{}, Nil{}, False{}, False{}, None{}}, Main.rword(["-m", "<message>"])), ats_back(List.sort(~T.Split, ~(a => b => M.typed.le(a, b)), bs), ["-m", "<message>"], None{}, M.typed.spellings(typed), Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, False{}, False{}, None{}, SortL.all_sort(~T.Split, ~(a => b => M.typed.le(a, b)), ~(x => M.id.plain(x)), bs, h))) : {_ == Done{Main.RecordCmd{None{}, M.typed.spellings(typed), Nil{}, List.sort(~T.Split, ~(a => b => M.typed.le(a, b)), bs), Nil{}, Nil{}, Nil{}, False{}, False{}, Some{"<message>"}}} : Result<&2, &2, Main.Refused, Main.RecordCmd>}
  {==}
