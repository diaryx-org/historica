# What `receive` plans. It takes only what this store lacks, and only what
# the source holds: a revision no revision document here has the digest of,
# and documents and payloads this store has nothing under the digest of and
# neither store forgets. It moves no bookmark this store has. The
# originals it destroys are ones a forgetting document stands in for. And
# it plans nothing from a store holding a revision document whose text
# does not parse, on either side.
import Base
import ./receive.bend as Receive
import ./arrange.bend as Arrange
import ./commands.bend as Main
import ./bookmark.bend as Bm
import ./revision.bend as Rev
import ./store.bend as Store
import ./text.bend as T
import ./tree.bend as Tree
import ./blamed_lemmas.bend as B
import ./string_lemmas.bend as S
import ./prune_lemmas.bend as PruneL
import ./prune.bend as Prune
import ./status_lemmas.bend as StatusL
import ./forget_lemmas.bend as ForgetL
import ./arrange_lemmas.bend as ArrangeL
import ./sort_lemmas.bend as SortL
import ./map_lemmas.bend as ML

# Bookmarks
# ---------

def join_names(a: Receive.Marked, b: Receive.Marked) -> {Receive.marked.names(Receive.marked.join(a, b)) == List.append(&2, Bm.Bookmark, Receive.marked.names(a), Receive.marked.names(b)) : List<&2, Bm.Bookmark>}:
  match a b:
    case Receive.Marked{an, ac} Receive.Marked{bn, bc}:
      {==}

def kept_app(xs: List<&2, Bm.Bookmark>, +ys: List<&2, Bm.Bookmark>, +hm: List<&2, Bm.Bookmark>, +hx: {Receive.names_kept(xs, hm) == True{} : Bool}, hy: {Receive.names_kept(ys, hm) == True{} : Bool}) -> {Receive.names_kept(List.append(&2, Bm.Bookmark, xs, ys), hm) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +x <> +rest:
      B.and_tt(Receive.keeps(hm, x), Receive.names_kept(List.append(&2, Bm.Bookmark, rest, ys), hm),
        PruneL.and_l(Receive.keeps(hm, x), Receive.names_kept(rest, hm), hx),
        kept_app(rest, ys, hm, PruneL.and_r(Receive.keeps(hm, x), Receive.names_kept(rest, hm), hx), hy))

def same_refl(+t: Bm.Target) -> {Receive.same_target(t, t) == True{} : Bool}:
  S.eq_refl(Bm.show_target(t))

def joined_kept(c: Bool, +hm: List<&2, Bm.Bookmark>, +n: String, +hn: String, +ht: Bm.Target, +hp: Bool, ef: {Main.found_of(hm, n) == Some{Bm.Bookmark{hn, ht, hp}} : Maybe<&2, Bm.Bookmark>}) -> {Receive.names_kept(Receive.marked.names(Bool.pick(Receive.Marked, c, Receive.Marked{[Bm.Bookmark{n, ht, True{}}], Nil{}}, Receive.Marked{Nil{}, Nil{}})), hm) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Maybe<&2, Bm.Bookmark>, Main.found_of(hm, n), Some{Bm.Bookmark{hn, ht, hp}}, ef) : {Bool.and(Receive.keeps.of(ht, _), True{}) == True{} : Bool}
      B.and_tt(Receive.same_target(ht, ht), True{}, same_refl(ht), {==})
    case False{}:
      {==}

def target_kept(c: Bool, +hm: List<&2, Bm.Bookmark>, +n: String, +tt: Bm.Target, +tp: Bool, +hn: String, +ht: Bm.Target, +hp: Bool, ef: {Main.found_of(hm, n) == Some{Bm.Bookmark{hn, ht, hp}} : Maybe<&2, Bm.Bookmark>}) -> {Receive.names_kept(Receive.marked.names(Bool.pick(Receive.Marked, c, Receive.marked.joined(n, ht, hp, tp), Receive.Marked{Nil{}, [Receive.Conflict{n, Bm.Bookmark{hn, ht, hp}, Bm.Bookmark{n, tt, tp}}]})), hm) == True{} : Bool}:
  match c:
    case True{}:
      joined_kept(Bool.and(tp, Bool.not(hp)), hm, n, hn, ht, hp, ef)
    case False{}:
      {==}

def one_kept(t: Bm.Bookmark, found: Maybe<&2, Bm.Bookmark>, +hm: List<&2, Bm.Bookmark>, ef: {Main.found_of(hm, Bm.name_of(t)) == found : Maybe<&2, Bm.Bookmark>}) -> {Receive.names_kept(Receive.marked.names(Receive.marked.one(t, found)), hm) == True{} : Bool}:
  match t found:
    case Bm.Bookmark{+n, +tt, +tp} None{}:
      %Equal.sym(Maybe<&2, Bm.Bookmark>, Main.found_of(hm, n), None{}, ef) : {Bool.and(Receive.keeps.of(tt, _), True{}) == True{} : Bool}
      {==}
    case Bm.Bookmark{+n, +tt, +tp} Some{Bm.Bookmark{+hn, +ht, +hp}}:
      target_kept(Receive.same_target(tt, ht), hm, n, tt, tp, hn, ht, hp, ef)

def all_kept(ts: List<&2, Bm.Bookmark>, +hm: List<&2, Bm.Bookmark>) -> {Receive.names_kept(Receive.marked.names(Receive.marked.all(ts, hm)), hm) == True{} : Bool}:
  match ts:
    case Nil{}:
      {==}
    case +t <> +rest:
      %Equal.sym(List<&2, Bm.Bookmark>, Receive.marked.names(Receive.marked.join(Receive.marked.one(t, Main.found_of(hm, Bm.name_of(t))), Receive.marked.all(rest, hm))), List.append(&2, Bm.Bookmark, Receive.marked.names(Receive.marked.one(t, Main.found_of(hm, Bm.name_of(t)))), Receive.marked.names(Receive.marked.all(rest, hm))), join_names(Receive.marked.one(t, Main.found_of(hm, Bm.name_of(t))), Receive.marked.all(rest, hm))) : {Receive.names_kept(_, hm) == True{} : Bool}
      kept_app(Receive.marked.names(Receive.marked.one(t, Main.found_of(hm, Bm.name_of(t)))), Receive.marked.names(Receive.marked.all(rest, hm)), hm,
        one_kept(t, Main.found_of(hm, Bm.name_of(t)), hm, {==}), all_kept(rest, hm))

# `receive` moves no bookmark this store has.
def names(+here: Receive.Side, +there: Receive.Side) -> {Receive.names_kept(Receive.rplan.names(Receive.plan.of(here, there)), Receive.side.marks(here)) == True{} : Bool}:
  all_kept(Receive.side.marks(there), Receive.side.marks(here))

# Destroying
# ----------

def or_r(a: Bool, -b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def held_cons(+y: String, +ys: List<&2, String>, zs: List<&2, String>, +h: {Main.all_held(ys, zs) == True{} : Bool}) -> {Main.all_held(y <> ys, zs) == True{} : Bool}:
  match zs:
    case Nil{}:
      {==}
    case +z <> +rest:
      B.and_tt(Rev.member(y <> ys, z), Main.all_held(y <> ys, rest),
        or_r(String.eq(y, z), Rev.member(ys, z), PruneL.and_l(Rev.member(ys, z), Main.all_held(ys, rest), h)),
        held_cons(y, ys, rest, PruneL.and_r(Rev.member(ys, z), Main.all_held(ys, rest), h)))

def held_refl(xs: List<&2, String>) -> {Main.all_held(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      B.and_tt(Rev.member(x <> rest, x), Main.all_held(x <> rest, rest),
        %Equal.sym(Bool, String.eq(x, x), True{}, S.eq_refl(x)) : {Bool.or(_, Rev.member(rest, x)) == True{} : Bool}
        {==},
        held_cons(x, rest, rest, held_refl(rest)))

def keep_held(b: Bool, +x: String, +r: List<&2, String>, +ys: List<&2, String>, hx: {Rev.member(ys, x) == True{} : Bool}, hr: {Main.all_held(ys, r) == True{} : Bool}) -> {Main.all_held(ys, Rev.keep(b, x, r)) == True{} : Bool}:
  match b:
    case True{}:
      B.and_tt(Rev.member(ys, x), Main.all_held(ys, r), hx, hr)
    case False{}:
      hr

def among_held(xs: List<&2, String>, +s: Set(), +ys: List<&2, String>, +h: {Main.all_held(ys, xs) == True{} : Bool}) -> {Main.all_held(ys, Receive.among(xs, s)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      keep_held(Arrange.has(s, x), x, Receive.among(rest, s), ys,
        PruneL.and_l(Rev.member(ys, x), Main.all_held(ys, rest), h),
        among_held(rest, s, ys, PruneL.and_r(Rev.member(ys, x), Main.all_held(ys, rest), h)))

# `receive` destroys only what a forgetting document of either store
# stands in for.
def destroys(+here: Receive.Side, +there: Receive.Side) -> {Main.all_held(Receive.forgotten(here, there), Receive.rplan.destroys(Receive.plan.of(here, there))) == True{} : Bool}:
  StatusL.ah_distinct(Receive.forgotten(here, there), List.sort(~String, ~(a => b => String.is_le(a, b)), Receive.among(Receive.forgotten(here, there), Set.from_list(List.append(&2, String, Receive.body.ids(Receive.stored.bodies(Receive.stored.of(here))), Receive.payload.ids(Receive.stored.payloads(Receive.stored.of(here))))))),
    StatusL.ah_sort(~(a => b => String.is_le(a, b)), Receive.forgotten(here, there), Receive.among(Receive.forgotten(here, there), Set.from_list(List.append(&2, String, Receive.body.ids(Receive.stored.bodies(Receive.stored.of(here))), Receive.payload.ids(Receive.stored.payloads(Receive.stored.of(here)))))),
      among_held(Receive.forgotten(here, there), Set.from_list(List.append(&2, String, Receive.body.ids(Receive.stored.bodies(Receive.stored.of(here))), Receive.payload.ids(Receive.stored.payloads(Receive.stored.of(here))))), Receive.forgotten(here, there), held_refl(Receive.forgotten(here, there)))))

# Every digest `receive` destroys is one a forgetting document of this
# store or of the source stands in for: said of the documents themselves,
# not of the list of digests the plan draws up from them.

def or_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def member_app(xs: List<&2, String>, +ys: List<&2, String>, +d: String) -> {Rev.member(List.append(&2, String, xs, ys), d) == Bool.or(Rev.member(xs, d), Rev.member(ys, d)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, Rev.member(List.append(&2, String, rest, ys), d), Bool.or(Rev.member(rest, d), Rev.member(ys, d)), member_app(rest, ys, d)) : {Bool.or(String.eq(x, d), _) == Bool.or(Rev.member(x <> rest, d), Rev.member(ys, d)) : Bool}
      or_assoc(String.eq(x, d), Rev.member(rest, d), Rev.member(ys, d))

def forgets_push(f: Maybe<&2, String>, +d: String, -rest: List<&2, Prune.Body>, ih: {Rev.member(Receive.body.forgets(rest), d) == Receive.forgot.by(rest, d) : Bool}) -> {Rev.member(Receive.forgets.push(f, Receive.body.forgets(rest)), d) == Bool.or(Receive.stands.for(f, d), Receive.forgot.by(rest, d)) : Bool}:
  match f:
    case None{}:
      ih
    case Some{t}:
      Equal.cong(Bool, Bool, x => Bool.or(String.eq(t, d), x), Rev.member(Receive.body.forgets(rest), d), Receive.forgot.by(rest, d), ih)

# A digest is among those these documents forget exactly where one of them
# stands in for it.
def forgets_member(bs: List<&2, Prune.Body>, +d: String) -> {Rev.member(Receive.body.forgets(bs), d) == Receive.forgot.by(bs, d) : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Prune.Body{p, i, ok, f} <> +rest:
      forgets_push(f, d, rest, forgets_member(rest, d))

def destroyed(+here: Receive.Side, +there: Receive.Side, +d: String, h: {Rev.member(Receive.rplan.destroys(Receive.plan.of(here, there)), d) == True{} : Bool}) -> {Bool.or(Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(here)), d), Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(there)), d)) == True{} : Bool}:
  %forgets_member(Receive.stored.bodies(Receive.stored.of(here)), d) : {Bool.or(_, Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(there)), d)) == True{} : Bool}
  %forgets_member(Receive.stored.bodies(Receive.stored.of(there)), d) : {Bool.or(Rev.member(Receive.body.forgets(Receive.stored.bodies(Receive.stored.of(here))), d), _) == True{} : Bool}
  %member_app(Receive.body.forgets(Receive.stored.bodies(Receive.stored.of(here))), Receive.body.forgets(Receive.stored.bodies(Receive.stored.of(there))), d) : {_ == True{} : Bool}
  ForgetL.held_member(Receive.forgotten(here, there), Receive.rplan.destroys(Receive.plan.of(here, there)), d, destroys(here, there), h)

# What it plans from
# ------------------

def and_false_r(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def gate(a: Bool, -b: Bool, -c: Bool, -e: Bool, ha: {a == False{} : Bool}) -> {Bool.and(Bool.and(Bool.and(a, b), c), e) == False{} : Bool}:
  %Equal.sym(Bool, a, False{}, ha) : {Bool.and(Bool.and(Bool.and(_, b), c), e) == False{} : Bool}
  {==}

# A store holding a revision document whose text does not parse fails the
# part of `check` the port reads, whatever else it holds.
def sound_bad(+pre: List<&2, Store.Doc>, +path: String, +id: String, +size: Nat, +text: String, +post: List<&2, Store.Doc>, +revs: List<&2, T.Split>, +od: List<&2, Store.Doc>, +bs: List<&2, Prune.Body>, +ps: List<&2, T.Split>, +names: List<&2, String>, +rules: List<&2, T.Split>, +msg: String, hp: {String.ends_with(path, ".rev.txt") == True{} : Bool}, hf: {Rev.parse(text) == Fail{msg} : Result<&2, &2, String, Rev.Rev>}) -> {Prune.sound(Prune.Stored{List.append(&2, Store.Doc, pre, Store.Doc{path, id, size, text} <> post), revs, od, bs, ps, names, rules}) == False{} : Bool}:
  gate(Arrange.all_parse(Arrange.revision_docs(List.append(&2, Store.Doc, pre, Store.Doc{path, id, size, text} <> post))), Prune.revs.sound(revs), Bool.and(Prune.bodies.sound(bs), Prune.revs.sound(ps)), Bool.and(Bool.and(Prune.texts.bookmarks(names), Prune.texts.rules(rules)), Prune.heads.sound(Rev.heads(Main.history(Arrange.distinct(Prune.fulls(Arrange.revision_docs(List.append(&2, Store.Doc, pre, Store.Doc{path, id, size, text} <> post)))))), Arrange.distinct(Prune.fulls(Arrange.revision_docs(List.append(&2, Store.Doc, pre, Store.Doc{path, id, size, text} <> post)))))),
    ArrangeL.bad_parse(pre, path, id, size, text, post, msg, hp, hf))

def gate_there(c: Bool, +here: Receive.Side, +there: Receive.Side, +join: Bool, hs: {Prune.sound(Receive.stored.of(there)) == False{} : Bool}) -> {Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.here(c, here, there, join)) == False{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, Prune.sound(Receive.stored.of(there)), False{}, hs) : {Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.source(_, here, there, join)) == False{} : Bool}
      {==}
    case False{}:
      {==}

# `receive` plans nothing from a store holding a revision document whose
# text does not parse, on either side.
def trusts(+other: Receive.Side, +root: String, +pre: List<&2, Store.Doc>, +path: String, +id: String, +size: Nat, +text: String, +post: List<&2, Store.Doc>, +revs: List<&2, T.Split>, +od: List<&2, Store.Doc>, +bs: List<&2, Prune.Body>, +ps: List<&2, T.Split>, +names: List<&2, String>, +rules: List<&2, T.Split>, +marks: List<&2, Bm.Bookmark>, +claims: List<&2, T.Split>, +join: Bool, +msg: String, +hp: {String.ends_with(path, ".rev.txt") == True{} : Bool}, +hf: {Rev.parse(text) == Fail{msg} : Result<&2, &2, String, Rev.Rev>}) -> {Bool.or(Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.r(Receive.Side{root, Prune.Stored{List.append(&2, Store.Doc, pre, Store.Doc{path, id, size, text} <> post), revs, od, bs, ps, names, rules}, marks, claims}, other, join)), Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.r(other, Receive.Side{root, Prune.Stored{List.append(&2, Store.Doc, pre, Store.Doc{path, id, size, text} <> post), revs, od, bs, ps, names, rules}, marks, claims}, join))) == False{} : Bool}:
  %Equal.sym(Bool, Prune.sound(Prune.Stored{List.append(&2, Store.Doc, pre, Store.Doc{path, id, size, text} <> post), revs, od, bs, ps, names, rules}), False{}, sound_bad(pre, path, id, size, text, post, revs, od, bs, ps, names, rules, msg, hp, hf)) : {Bool.or(Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.here(_, Receive.Side{root, Prune.Stored{List.append(&2, Store.Doc, pre, Store.Doc{path, id, size, text} <> post), revs, od, bs, ps, names, rules}, marks, claims}, other, join)), Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.r(other, Receive.Side{root, Prune.Stored{List.append(&2, Store.Doc, pre, Store.Doc{path, id, size, text} <> post), revs, od, bs, ps, names, rules}, marks, claims}, join))) == False{} : Bool}
  gate_there(Prune.sound(Receive.stored.of(other)), other, Receive.Side{root, Prune.Stored{List.append(&2, Store.Doc, pre, Store.Doc{path, id, size, text} <> post), revs, od, bs, ps, names, rules}, marks, claims}, join, sound_bad(pre, path, id, size, text, post, revs, od, bs, ps, names, rules, msg, hp, hf))

# Taking what is lacking, said of the files
# -----------------------------------------

def text_of(d: Store.Doc) -> String:
  match d:
    case Store.Doc{p, i, n, t}:
      t

# Whether one of these documents has this digest and this text.
def holds(ds: List<&2, Store.Doc>, +id: String, +text: String) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Store.Doc{p, +i, n, +t} <> rest:
      Bool.or(Bool.and(String.eq(i, id), String.eq(t, text)), holds(rest, id, text))

# Whether one of these files is at this path with this digest.
def lists(ss: List<&2, T.Split>, +path: String, +d: String) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case T.Split{+q, +x} <> rest:
      Bool.or(Bool.and(String.eq(q, path), String.eq(x, d)), lists(rest, path, d))

def rplan.documents(p: Receive.RPlan) -> List<&2, Store.Doc>:
  match p:
    case Receive.RPlan{rs, ds, ps, ns, rules, res, des, cs}:
      ds

def rplan.payloads(p: Receive.RPlan) -> List<&2, T.Split>:
  match p:
    case Receive.RPlan{rs, ds, ps, ns, rules, res, des, cs}:
      ps

# What `docs.lacking` keeps has a digest the set lacks.
def lacking_hit(c: Bool, +i: String, +t: String, +r: List<&2, Store.Doc>, +have: Set(), +id: String, +text: String, +hb: {Bool.not(Arrange.has(have, i)) == True{} : Bool}, +ec: {Bool.and(String.eq(i, id), String.eq(t, text)) == c : Bool}, h: {Bool.or(c, holds(r, id, text)) == True{} : Bool}, ih: {holds(r, id, text) == True{} : Bool} -> {Arrange.has(have, id) == False{} : Bool}) -> {Arrange.has(have, id) == False{} : Bool}:
  match c:
    case True{}:
      %S.eq_true(i, id, ArrangeL.and_tl(String.eq(i, id), String.eq(t, text), ec)) : {Arrange.has(have, _) == False{} : Bool}
      ArrangeL.not_tt(Arrange.has(have, i), hb)
    case False{}:
      ih(h)

def lacking_keep(b: Bool, +p: String, +i: String, +n: Nat, +t: String, +r: List<&2, Store.Doc>, +have: Set(), +id: String, +text: String, +eb: {Bool.not(Arrange.has(have, i)) == b : Bool}, h: {holds(Receive.doc.keep(b, Store.Doc{p, i, n, t}, r), id, text) == True{} : Bool}, ih: {holds(r, id, text) == True{} : Bool} -> {Arrange.has(have, id) == False{} : Bool}) -> {Arrange.has(have, id) == False{} : Bool}:
  match b:
    case True{}:
      lacking_hit(Bool.and(String.eq(i, id), String.eq(t, text)), i, t, r, have, id, text, eb, {==}, h, ih)
    case False{}:
      ih(h)

def lacking_fresh(xs: List<&2, Store.Doc>, +have: Set(), +id: String, +text: String, h: {holds(Receive.docs.lacking(xs, have), id, text) == True{} : Bool}) -> {Arrange.has(have, id) == False{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Arrange.has(have, id) == False{} : Bool}, S.false_true(h))
    case Store.Doc{+p, +i, +n, +t} <> +rest:
      lacking_keep(Bool.not(Arrange.has(have, i)), p, i, n, t, Receive.docs.lacking(rest, have), have, id, text, {==}, h, hr => lacking_fresh(rest, have, id, text, hr))

def slacking_hit(c: Bool, +q: String, +x: String, +r: List<&2, T.Split>, +have: Set(), +path: String, +d: String, +hb: {Bool.not(Arrange.has(have, x)) == True{} : Bool}, +ec: {Bool.and(String.eq(q, path), String.eq(x, d)) == c : Bool}, h: {Bool.or(c, lists(r, path, d)) == True{} : Bool}, ih: {lists(r, path, d) == True{} : Bool} -> {Arrange.has(have, d) == False{} : Bool}) -> {Arrange.has(have, d) == False{} : Bool}:
  match c:
    case True{}:
      %S.eq_true(x, d, ArrangeL.and_tr(String.eq(q, path), String.eq(x, d), ec)) : {Arrange.has(have, _) == False{} : Bool}
      ArrangeL.not_tt(Arrange.has(have, x), hb)
    case False{}:
      ih(h)

def slacking_keep(b: Bool, +q: String, +x: String, +r: List<&2, T.Split>, +have: Set(), +path: String, +d: String, +eb: {Bool.not(Arrange.has(have, x)) == b : Bool}, h: {lists(Tree.keep(~T.Split, b, T.Split{q, x}, r), path, d) == True{} : Bool}, ih: {lists(r, path, d) == True{} : Bool} -> {Arrange.has(have, d) == False{} : Bool}) -> {Arrange.has(have, d) == False{} : Bool}:
  match b:
    case True{}:
      slacking_hit(Bool.and(String.eq(q, path), String.eq(x, d)), q, x, r, have, path, d, eb, {==}, h, ih)
    case False{}:
      ih(h)

def slacking_fresh(xs: List<&2, T.Split>, +have: Set(), +path: String, +d: String, h: {lists(Receive.splits.lacking(xs, have), path, d) == True{} : Bool}) -> {Arrange.has(have, d) == False{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Arrange.has(have, d) == False{} : Bool}, S.false_true(h))
    case T.Split{+q, +x} <> +rest:
      slacking_keep(Bool.not(Arrange.has(have, x)), q, x, Receive.splits.lacking(rest, have), have, path, d, {==}, h, hr => slacking_fresh(rest, have, path, d, hr))

# A filter keeps only what it was given.
def keep_holds(b: Bool, +p: String, +i: String, +n: Nat, +t: String, +r: List<&2, Store.Doc>, +rest: List<&2, Store.Doc>, +id: String, +text: String, h: {holds(Receive.doc.keep(b, Store.Doc{p, i, n, t}, r), id, text) == True{} : Bool}, ih: {holds(r, id, text) == True{} : Bool} -> {holds(rest, id, text) == True{} : Bool}) -> {holds(Store.Doc{p, i, n, t} <> rest, id, text) == True{} : Bool}:
  match b:
    case True{}:
      PruneL.or_tt(Bool.and(String.eq(i, id), String.eq(t, text)), holds(r, id, text), holds(rest, id, text), h, ih)
    case False{}:
      PruneL.or_rt(Bool.and(String.eq(i, id), String.eq(t, text)), holds(rest, id, text), ih(h))

def lacking_holds(xs: List<&2, Store.Doc>, +have: Set(), +id: String, +text: String, h: {holds(Receive.docs.lacking(xs, have), id, text) == True{} : Bool}) -> {holds(xs, id, text) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Store.Doc{+p, +i, +n, +t} <> +rest:
      keep_holds(Bool.not(Arrange.has(have, i)), p, i, n, t, Receive.docs.lacking(rest, have), rest, id, text, h, hr => lacking_holds(rest, have, id, text, hr))

def dedup_holds(ys: List<&2, Store.Doc>, +prev: String, +id: String, +text: String, h: {holds(Receive.docs.dedup(ys, prev), id, text) == True{} : Bool}) -> {holds(ys, id, text) == True{} : Bool}:
  match ys:
    case Nil{}:
      h
    case Store.Doc{+p, +i, +n, +t} <> +rest:
      keep_holds(Bool.not(String.eq(i, prev)), p, i, n, t, Receive.docs.dedup(rest, i), rest, id, text, h, hr => dedup_holds(rest, i, id, text, hr))

def parsing_holds(ys: List<&2, Store.Doc>, +id: String, +text: String, h: {holds(Receive.docs.parsing(ys), id, text) == True{} : Bool}) -> {holds(ys, id, text) == True{} : Bool}:
  match ys:
    case Nil{}:
      h
    case Store.Doc{+p, +i, +n, +t} <> +rest:
      keep_holds(Arrange.parses(Store.Doc{p, i, n, t}), p, i, n, t, Receive.docs.parsing(rest), rest, id, text, h, hr => parsing_holds(rest, id, text, hr))

# Whether a list of documents holds this one's digest and text.
def held.by(c: List<&2, Store.Doc>, +d: Store.Doc) -> Bool:
  holds(c, Store.id_of(d), text_of(d))

def weak_all(+c: List<&2, Store.Doc>, +dp: String, +di: String, +dn: Nat, +dt: String, ys: List<&2, Store.Doc>, +h: {SortL.all_at(~Store.Doc, ~List<&2, Store.Doc>, ~(c => a => held.by(c, a)), c, ys) == True{} : Bool}) -> {SortL.all_at(~Store.Doc, ~List<&2, Store.Doc>, ~(c => a => held.by(c, a)), Store.Doc{dp, di, dn, dt} <> c, ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Store.Doc{+p, +i, +n, +t} <> +rest:
      B.and_tt(holds(Store.Doc{dp, di, dn, dt} <> c, i, t), SortL.all_at(~Store.Doc, ~List<&2, Store.Doc>, ~(c => a => held.by(c, a)), Store.Doc{dp, di, dn, dt} <> c, rest),
        PruneL.or_rt(Bool.and(String.eq(di, i), String.eq(dt, t)), holds(c, i, t), PruneL.and_l(holds(c, i, t), SortL.all_at(~Store.Doc, ~List<&2, Store.Doc>, ~(c => a => held.by(c, a)), c, rest), h)),
        weak_all(c, dp, di, dn, dt, rest, PruneL.and_r(holds(c, i, t), SortL.all_at(~Store.Doc, ~List<&2, Store.Doc>, ~(c => a => held.by(c, a)), c, rest), h)))

# Every document of a list, the list holds.
def self_all(xs: List<&2, Store.Doc>) -> {SortL.all_at(~Store.Doc, ~List<&2, Store.Doc>, ~(c => a => held.by(c, a)), xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Store.Doc{+p, +i, +n, +t} <> +rest:
      B.and_tt(holds(Store.Doc{p, i, n, t} <> rest, i, t), SortL.all_at(~Store.Doc, ~List<&2, Store.Doc>, ~(c => a => held.by(c, a)), Store.Doc{p, i, n, t} <> rest, rest),
        PruneL.or_lt(Bool.and(String.eq(i, i), String.eq(t, t)), holds(rest, i, t), B.and_tt(String.eq(i, i), String.eq(t, t), S.eq_refl(i), S.eq_refl(t))),
        weak_all(rest, p, i, n, t, rest, self_all(rest)))

def from_hit(c: Bool, +i: String, +t: String, +rest: List<&2, Store.Doc>, +cs: List<&2, Store.Doc>, +id: String, +text: String, +ec: {Bool.and(String.eq(i, id), String.eq(t, text)) == c : Bool}, +hc: {holds(cs, i, t) == True{} : Bool}, h: {Bool.or(c, holds(rest, id, text)) == True{} : Bool}, ih: {holds(rest, id, text) == True{} : Bool} -> {holds(cs, id, text) == True{} : Bool}) -> {holds(cs, id, text) == True{} : Bool}:
  match c:
    case True{}:
      %S.eq_true(i, id, ArrangeL.and_tl(String.eq(i, id), String.eq(t, text), ec)) : {holds(cs, _, text) == True{} : Bool}
      %S.eq_true(t, text, ArrangeL.and_tr(String.eq(i, id), String.eq(t, text), ec)) : {holds(cs, i, _) == True{} : Bool}
      hc
    case False{}:
      ih(h)

# What a list whose every document another holds holds, that one holds.
def from_all(ys: List<&2, Store.Doc>, +cs: List<&2, Store.Doc>, +id: String, +text: String, +ha: {SortL.all_at(~Store.Doc, ~List<&2, Store.Doc>, ~(c => a => held.by(c, a)), cs, ys) == True{} : Bool}, h: {holds(ys, id, text) == True{} : Bool}) -> {holds(cs, id, text) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({holds(cs, id, text) == True{} : Bool}, S.false_true(h))
    case Store.Doc{+p, +i, +n, +t} <> +rest:
      from_hit(Bool.and(String.eq(i, id), String.eq(t, text)), i, t, rest, cs, id, text, {==},
        PruneL.and_l(holds(cs, i, t), SortL.all_at(~Store.Doc, ~List<&2, Store.Doc>, ~(c => a => held.by(c, a)), cs, rest), ha), h,
        hr => from_all(rest, cs, id, text, PruneL.and_r(holds(cs, i, t), SortL.all_at(~Store.Doc, ~List<&2, Store.Doc>, ~(c => a => held.by(c, a)), cs, rest), ha), hr))

# A sort keeps only what it was given.
def sort_holds(+xs: List<&2, Store.Doc>, +id: String, +text: String, h: {holds(List.sort(~Store.Doc, ~(a => b => Receive.doc.id_le(a, b)), xs), id, text) == True{} : Bool}) -> {holds(xs, id, text) == True{} : Bool}:
  from_all(List.sort(~Store.Doc, ~(a => b => Receive.doc.id_le(a, b)), xs), xs, id, text,
    SortL.all_sort_at(~Store.Doc, ~(a => b => Receive.doc.id_le(a, b)), ~List<&2, Store.Doc>, ~(c => a => held.by(c, a)), xs, xs, self_all(xs)), h)

# Each document once keeps only documents it was given.
def distinct_holds(+xs: List<&2, Store.Doc>, +id: String, +text: String, h: {holds(Receive.docs.distinct(xs), id, text) == True{} : Bool}) -> {holds(xs, id, text) == True{} : Bool}:
  sort_holds(xs, id, text, dedup_holds(List.sort(~Store.Doc, ~(a => b => Receive.doc.id_le(a, b)), xs), SNil{}, id, text, h))

def tkeep_lists(b: Bool, +q: String, +x: String, +r: List<&2, T.Split>, +rest: List<&2, T.Split>, +path: String, +d: String, h: {lists(Tree.keep(~T.Split, b, T.Split{q, x}, r), path, d) == True{} : Bool}, ih: {lists(r, path, d) == True{} : Bool} -> {lists(rest, path, d) == True{} : Bool}) -> {lists(T.Split{q, x} <> rest, path, d) == True{} : Bool}:
  match b:
    case True{}:
      PruneL.or_tt(Bool.and(String.eq(q, path), String.eq(x, d)), lists(r, path, d), lists(rest, path, d), h, ih)
    case False{}:
      PruneL.or_rt(Bool.and(String.eq(q, path), String.eq(x, d)), lists(rest, path, d), ih(h))

def slacking_lists(xs: List<&2, T.Split>, +have: Set(), +path: String, +d: String, h: {lists(Receive.splits.lacking(xs, have), path, d) == True{} : Bool}) -> {lists(xs, path, d) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case T.Split{+q, +x} <> +rest:
      tkeep_lists(Bool.not(Arrange.has(have, x)), q, x, Receive.splits.lacking(rest, have), rest, path, d, h, hr => slacking_lists(rest, have, path, d, hr))

def sdedup_lists(ys: List<&2, T.Split>, +prev: String, +path: String, +d: String, h: {lists(Receive.splits.dedup(ys, prev), path, d) == True{} : Bool}) -> {lists(ys, path, d) == True{} : Bool}:
  match ys:
    case Nil{}:
      h
    case T.Split{+q, +x} <> +rest:
      tkeep_lists(Bool.not(String.eq(x, prev)), q, x, Receive.splits.dedup(rest, x), rest, path, d, h, hr => sdedup_lists(rest, x, path, d, hr))

def listed.by(c: List<&2, T.Split>, +s: T.Split) -> Bool:
  match s:
    case T.Split{+q, +x}:
      lists(c, q, x)

def sweak_all(+c: List<&2, T.Split>, +dq: String, +dx: String, ys: List<&2, T.Split>, +h: {SortL.all_at(~T.Split, ~List<&2, T.Split>, ~(c => a => listed.by(c, a)), c, ys) == True{} : Bool}) -> {SortL.all_at(~T.Split, ~List<&2, T.Split>, ~(c => a => listed.by(c, a)), T.Split{dq, dx} <> c, ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case T.Split{+q, +x} <> +rest:
      B.and_tt(lists(T.Split{dq, dx} <> c, q, x), SortL.all_at(~T.Split, ~List<&2, T.Split>, ~(c => a => listed.by(c, a)), T.Split{dq, dx} <> c, rest),
        PruneL.or_rt(Bool.and(String.eq(dq, q), String.eq(dx, x)), lists(c, q, x), PruneL.and_l(lists(c, q, x), SortL.all_at(~T.Split, ~List<&2, T.Split>, ~(c => a => listed.by(c, a)), c, rest), h)),
        sweak_all(c, dq, dx, rest, PruneL.and_r(lists(c, q, x), SortL.all_at(~T.Split, ~List<&2, T.Split>, ~(c => a => listed.by(c, a)), c, rest), h)))

def sself_all(xs: List<&2, T.Split>) -> {SortL.all_at(~T.Split, ~List<&2, T.Split>, ~(c => a => listed.by(c, a)), xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case T.Split{+q, +x} <> +rest:
      B.and_tt(lists(T.Split{q, x} <> rest, q, x), SortL.all_at(~T.Split, ~List<&2, T.Split>, ~(c => a => listed.by(c, a)), T.Split{q, x} <> rest, rest),
        PruneL.or_lt(Bool.and(String.eq(q, q), String.eq(x, x)), lists(rest, q, x), B.and_tt(String.eq(q, q), String.eq(x, x), S.eq_refl(q), S.eq_refl(x))),
        sweak_all(rest, q, x, rest, sself_all(rest)))

def sfrom_hit(c: Bool, +q: String, +x: String, +rest: List<&2, T.Split>, +cs: List<&2, T.Split>, +path: String, +d: String, +ec: {Bool.and(String.eq(q, path), String.eq(x, d)) == c : Bool}, +hc: {lists(cs, q, x) == True{} : Bool}, h: {Bool.or(c, lists(rest, path, d)) == True{} : Bool}, ih: {lists(rest, path, d) == True{} : Bool} -> {lists(cs, path, d) == True{} : Bool}) -> {lists(cs, path, d) == True{} : Bool}:
  match c:
    case True{}:
      %S.eq_true(q, path, ArrangeL.and_tl(String.eq(q, path), String.eq(x, d), ec)) : {lists(cs, _, d) == True{} : Bool}
      %S.eq_true(x, d, ArrangeL.and_tr(String.eq(q, path), String.eq(x, d), ec)) : {lists(cs, q, _) == True{} : Bool}
      hc
    case False{}:
      ih(h)

def sfrom_all(ys: List<&2, T.Split>, +cs: List<&2, T.Split>, +path: String, +d: String, +ha: {SortL.all_at(~T.Split, ~List<&2, T.Split>, ~(c => a => listed.by(c, a)), cs, ys) == True{} : Bool}, h: {lists(ys, path, d) == True{} : Bool}) -> {lists(cs, path, d) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({lists(cs, path, d) == True{} : Bool}, S.false_true(h))
    case T.Split{+q, +x} <> +rest:
      sfrom_hit(Bool.and(String.eq(q, path), String.eq(x, d)), q, x, rest, cs, path, d, {==},
        PruneL.and_l(lists(cs, q, x), SortL.all_at(~T.Split, ~List<&2, T.Split>, ~(c => a => listed.by(c, a)), cs, rest), ha), h,
        hr => sfrom_all(rest, cs, path, d, PruneL.and_r(lists(cs, q, x), SortL.all_at(~T.Split, ~List<&2, T.Split>, ~(c => a => listed.by(c, a)), cs, rest), ha), hr))

# Each payload once keeps only payloads it was given, where it found them.
def sdistinct_lists(+xs: List<&2, T.Split>, +path: String, +d: String, h: {lists(Receive.splits.distinct(xs), path, d) == True{} : Bool}) -> {lists(xs, path, d) == True{} : Bool}:
  sfrom_all(List.sort(~T.Split, ~(a => b => Receive.split.le(a, b)), xs), xs, path, d,
    SortL.all_sort_at(~T.Split, ~(a => b => Receive.split.le(a, b)), ~List<&2, T.Split>, ~(c => a => listed.by(c, a)), xs, xs, sself_all(xs)),
    sdedup_lists(List.sort(~T.Split, ~(a => b => Receive.split.le(a, b)), xs), SNil{}, path, d, h))

# Documents and payloads
# ----------------------

def forgot_false(+bs: List<&2, Prune.Body>, +d: String, h: {Rev.member(Receive.body.forgets(bs), d) == False{} : Bool}) -> {Receive.forgot.by(bs, d) == False{} : Bool}:
  Equal.trans(Bool, Receive.forgot.by(bs, d), Rev.member(Receive.body.forgets(bs), d), False{}, Equal.sym(Bool, Rev.member(Receive.body.forgets(bs), d), Receive.forgot.by(bs, d), forgets_member(bs, d)), h)

# A digest a set built from what this store holds and what either store
# forgets lacks is one neither holds nor forgets.
def fresh_of(+held: List<&2, String>, +here: Receive.Side, +there: Receive.Side, +d: String, h: {Arrange.has(Set.from_list(List.append(&2, String, held, Receive.forgotten(here, there))), d) == False{} : Bool}) -> {Bool.not(Bool.or(Rev.member(held, d), Bool.or(Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(here)), d), Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(there)), d)))) == True{} : Bool}:
  +bh = Receive.stored.bodies(Receive.stored.of(here))
  +bt = Receive.stored.bodies(Receive.stored.of(there))
  +m1 = ArrangeL.app_false(held, Receive.forgotten(here, there), d, ArrangeL.has_false(List.append(&2, String, held, Receive.forgotten(here, there)), d, h))
  +m2 = ArrangeL.app_false(Receive.body.forgets(bh), Receive.body.forgets(bt), d, ArrangeL.or_ff_r(Rev.member(held, d), Rev.member(Receive.forgotten(here, there), d), m1))
  ArrangeL.not_ff(Bool.or(Rev.member(held, d), Bool.or(Receive.forgot.by(bh, d), Receive.forgot.by(bt, d))),
    ArrangeL.or_ff(Rev.member(held, d), Bool.or(Receive.forgot.by(bh, d), Receive.forgot.by(bt, d)), ArrangeL.or_ff_l(Rev.member(held, d), Rev.member(Receive.forgotten(here, there), d), m1),
      ArrangeL.or_ff(Receive.forgot.by(bh, d), Receive.forgot.by(bt, d),
        forgot_false(bh, d, ArrangeL.or_ff_l(Rev.member(Receive.body.forgets(bh), d), Rev.member(Receive.body.forgets(bt), d), m2)),
        forgot_false(bt, d, ArrangeL.or_ff_r(Rev.member(Receive.body.forgets(bh), d), Rev.member(Receive.body.forgets(bt), d), m2)))))

# Every operation document `receive` files is one of the source's, by its
# digest and its text, under a digest this store holds no document under
# and neither store forgets.
def documents(+here: Receive.Side, +there: Receive.Side, +id: String, +text: String, +h: {holds(rplan.documents(Receive.plan.of(here, there)), id, text) == True{} : Bool}) -> {Bool.and(Bool.not(Bool.or(Rev.member(T.map(~Prune.Body, ~String, ~(b => Prune.body.id(b)), Receive.stored.bodies(Receive.stored.of(here))), id), Bool.or(Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(here)), id), Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(there)), id)))), holds(Receive.stored.odocs(Receive.stored.of(there)), id, text)) == True{} : Bool}:
  +ds = Receive.docs.distinct(Receive.stored.odocs(Receive.stored.of(there)))
  B.and_tt(Bool.not(Bool.or(Rev.member(T.map(~Prune.Body, ~String, ~(b => Prune.body.id(b)), Receive.stored.bodies(Receive.stored.of(here))), id), Bool.or(Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(here)), id), Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(there)), id)))), holds(Receive.stored.odocs(Receive.stored.of(there)), id, text),
    fresh_of(Receive.body.ids(Receive.stored.bodies(Receive.stored.of(here))), here, there, id, lacking_fresh(ds, Receive.have.documents(here, there), id, text, h)),
    distinct_holds(Receive.stored.odocs(Receive.stored.of(there)), id, text, lacking_holds(ds, Receive.have.documents(here, there), id, text, h)))

# Every payload `receive` copies is one of the source's, at the path the
# source has it, under a digest this store holds no payload under and
# neither store forgets.
def payloads(+here: Receive.Side, +there: Receive.Side, +path: String, +d: String, +h: {lists(rplan.payloads(Receive.plan.of(here, there)), path, d) == True{} : Bool}) -> {Bool.and(Bool.not(Bool.or(Rev.member(T.map(~T.Split, ~String, ~(s => Receive.split.digest(s)), Receive.stored.payloads(Receive.stored.of(here))), d), Bool.or(Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(here)), d), Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(there)), d)))), lists(Receive.stored.payloads(Receive.stored.of(there)), path, d)) == True{} : Bool}:
  +ss = Receive.splits.distinct(Receive.stored.payloads(Receive.stored.of(there)))
  B.and_tt(Bool.not(Bool.or(Rev.member(T.map(~T.Split, ~String, ~(s => Receive.split.digest(s)), Receive.stored.payloads(Receive.stored.of(here))), d), Bool.or(Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(here)), d), Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(there)), d)))), lists(Receive.stored.payloads(Receive.stored.of(there)), path, d),
    fresh_of(Receive.payload.ids(Receive.stored.payloads(Receive.stored.of(here))), here, there, d, slacking_fresh(ss, Receive.have.payloads(here, there), path, d, h)),
    sdistinct_lists(Receive.stored.payloads(Receive.stored.of(there)), path, d, slacking_lists(ss, Receive.have.payloads(here, there), path, d, h)))

# Revisions
# ---------

def related_done(r: Bool, +here: Receive.Side, +there: Receive.Side, +p: Receive.RPlan, e: {Receive.plan.related(r, here, there) == Done{p} : Result<&2, &2, Main.Refused, Receive.RPlan>}) -> {Receive.plan.of(here, there) == p : Receive.RPlan}:
  match r:
    case True{}:
      B.done_eq(Receive.RPlan, Receive.plan.of(here, there), p, e)
    case False{}:
      Empty.absurd({Receive.plan.of(here, there) == p : Receive.RPlan}, B.fail_done(Receive.RPlan, Main.Refused{1, "these nonempty stores share no revision or graph edge; use `--join-unrelated` only if combining two histories is intended"}, p, e))

def source_done(c: Bool, +here: Receive.Side, +there: Receive.Side, +join: Bool, +p: Receive.RPlan, e: {Receive.plan.source(c, here, there, join) == Done{p} : Result<&2, &2, Main.Refused, Receive.RPlan>}) -> {Receive.plan.of(here, there) == p : Receive.RPlan}:
  match c:
    case True{}:
      related_done(Bool.or(join, Receive.related(Receive.side.fulls(here), Receive.side.fulls(there))), here, there, p, e)
    case False{}:
      Empty.absurd({Receive.plan.of(here, there) == p : Receive.RPlan}, B.fail_done(Receive.RPlan, Main.Refused{1, "the source store does not pass `check`; receive writes nothing until its errors are repaired"}, p, e))

def here_done(c: Bool, +here: Receive.Side, +there: Receive.Side, +join: Bool, +p: Receive.RPlan, e: {Receive.plan.here(c, here, there, join) == Done{p} : Result<&2, &2, Main.Refused, Receive.RPlan>}) -> {Receive.plan.of(here, there) == p : Receive.RPlan}:
  match c:
    case True{}:
      source_done(Prune.sound(Receive.stored.of(there)), here, there, join, p, e)
    case False{}:
      Empty.absurd({Receive.plan.of(here, there) == p : Receive.RPlan}, B.fail_done(Receive.RPlan, Main.Refused{1, "the receiving store does not pass `check`; receive writes nothing until its errors are repaired"}, p, e))

def here_sound(c: Bool, +here: Receive.Side, +there: Receive.Side, +join: Bool, +p: Receive.RPlan, +ec: {Prune.sound(Receive.stored.of(here)) == c : Bool}, e: {Receive.plan.here(c, here, there, join) == Done{p} : Result<&2, &2, Main.Refused, Receive.RPlan>}) -> {Prune.sound(Receive.stored.of(here)) == True{} : Bool}:
  match c:
    case True{}:
      ec
    case False{}:
      Empty.absurd({Prune.sound(Receive.stored.of(here)) == True{} : Bool}, B.fail_done(Receive.RPlan, Main.Refused{1, "the receiving store does not pass `check`; receive writes nothing until its errors are repaired"}, p, e))

# A plan `plan.r` gives is `plan.of`'s, of a store that passes the check.
def planned(+here: Receive.Side, +there: Receive.Side, +join: Bool, +p: Receive.RPlan, e: {Receive.plan.r(here, there, join) == Done{p} : Result<&2, &2, Main.Refused, Receive.RPlan>}) -> {Receive.plan.of(here, there) == p : Receive.RPlan}:
  here_done(Prune.sound(Receive.stored.of(here)), here, there, join, p, e)

def planned_sound(+here: Receive.Side, +there: Receive.Side, +join: Bool, +p: Receive.RPlan, e: {Receive.plan.r(here, there, join) == Done{p} : Result<&2, &2, Main.Refused, Receive.RPlan>}) -> {Prune.sound(Receive.stored.of(here)) == True{} : Bool}:
  here_sound(Prune.sound(Receive.stored.of(here)), here, there, join, p, {==}, e)

def first4(a: Bool, -b: Bool, -c: Bool, -d: Bool, e: {Bool.and(Bool.and(Bool.and(a, b), c), d) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(e))

# A store the check passes holds no revision document that does not parse.
def sound_parse(s: Prune.Stored, h: {Prune.sound(s) == True{} : Bool}) -> {Arrange.all_parse(Arrange.revision_docs(Receive.stored.docs(s))) == True{} : Bool}:
  match s:
    case Prune.Stored{+docs, +revs, +od, +bs, +ps, +names, +rules}:
      first4(Arrange.all_parse(Arrange.revision_docs(docs)), Prune.revs.sound(revs), Bool.and(Prune.bodies.sound(bs), Prune.revs.sound(ps)), Bool.and(Bool.and(Prune.texts.bookmarks(names), Prune.texts.rules(rules)), Prune.heads.sound(Rev.heads(Main.history(Arrange.distinct(Prune.fulls(Arrange.revision_docs(docs))))), Arrange.distinct(Prune.fulls(Arrange.revision_docs(docs))))), h)

def doc_ids(ds: List<&2, Store.Doc>) -> List<&2, String>:
  T.map(~Store.Doc, ~String, ~(d => Store.id_of(d)), ds)

def full_step(r: Result<&2, &2, String, Rev.Rev>, +i: String, +rest: List<&2, Store.Doc>, hp: {Bool.not(Arrange.rev.fails(r)) == True{} : Bool}, ih: {Main.ids(Prune.fulls(rest)) == doc_ids(rest) : List<&2, String>}) -> {Main.ids(Main.push_full(Main.full(i, r), Prune.fulls(rest))) == i <> doc_ids(rest) : List<&2, String>}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.ids(Main.push_full(Main.full(i, Fail{x}), Prune.fulls(rest))) == i <> doc_ids(rest) : List<&2, String>}, S.false_true(hp))
    case Done{Rev.Rev{+c, +pa, +su, +au, +wh, +rb, +rv, +fa, +me}}:
      Equal.cong(List<&2, String>, List<&2, String>, l => i <> l, Main.ids(Prune.fulls(rest)), doc_ids(rest), ih)

# Where every document parses, the revisions read from them are one each,
# under their documents' digests.
def fulls_ids(ds: List<&2, Store.Doc>, +h: {Arrange.all_parse(ds) == True{} : Bool}) -> {Main.ids(Prune.fulls(ds)) == doc_ids(ds) : List<&2, String>}:
  match ds:
    case Nil{}:
      {==}
    case Store.Doc{+p, +i, +n, +t} <> +rest:
      full_step(Rev.parse(t), i, rest, ArrangeL.and_tl(Arrange.parses(Store.Doc{p, i, n, t}), Arrange.all_parse(rest), h), fulls_ids(rest, ArrangeL.and_tr(Arrange.parses(Store.Doc{p, i, n, t}), Arrange.all_parse(rest), h)))

def fmem_keyed.of(b: Bool, +f: Main.Full, +rest: List<&2, Main.Full>, +d: String, m: {Bool.or(b, Rev.member(Main.ids(rest), d)) == True{} : Bool}, ih: {Rev.member(Main.ids(rest), d) == True{} : Bool} -> {List.is_empty(&2, Main.Full, SortL.keyed(~Main.Full, ~(g => Main.id_of(g)), d, rest)) == False{} : Bool}) -> {List.is_empty(&2, Main.Full, Bool.pick(List<&2, Main.Full>, b, f <> SortL.keyed(~Main.Full, ~(g => Main.id_of(g)), d, rest), SortL.keyed(~Main.Full, ~(g => Main.id_of(g)), d, rest))) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(m)

def fmem_keyed(xs: List<&2, Main.Full>, +d: String, m: {Rev.member(Main.ids(xs), d) == True{} : Bool}) -> {List.is_empty(&2, Main.Full, SortL.keyed(~Main.Full, ~(g => Main.id_of(g)), d, xs)) == False{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({List.is_empty(&2, Main.Full, Nil{}) == False{} : Bool}, S.false_true(m))
    case +x <> +rest:
      fmem_keyed.of(String.eq(Main.id_of(x), d), x, rest, d, m, h => fmem_keyed(rest, d, h))

def fkeyed_mem.of(b: Bool, +f: Main.Full, +rest: List<&2, Main.Full>, +d: String, h: {List.is_empty(&2, Main.Full, Bool.pick(List<&2, Main.Full>, b, f <> SortL.keyed(~Main.Full, ~(g => Main.id_of(g)), d, rest), SortL.keyed(~Main.Full, ~(g => Main.id_of(g)), d, rest))) == False{} : Bool}, ih: {List.is_empty(&2, Main.Full, SortL.keyed(~Main.Full, ~(g => Main.id_of(g)), d, rest)) == False{} : Bool} -> {Rev.member(Main.ids(rest), d) == True{} : Bool}) -> {Bool.or(b, Rev.member(Main.ids(rest), d)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(h)

def fkeyed_mem(ys: List<&2, Main.Full>, +d: String, h: {List.is_empty(&2, Main.Full, SortL.keyed(~Main.Full, ~(g => Main.id_of(g)), d, ys)) == False{} : Bool}) -> {Rev.member(Main.ids(ys), d) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({Rev.member(Main.ids(Nil{}), d) == True{} : Bool}, S.true_false(h))
    case +y <> +rest:
      fkeyed_mem.of(String.eq(Main.id_of(y), d), y, rest, d, h, t => fkeyed_mem(rest, d, t))

# Sorting revisions by digest keeps every one.
def fsort_mem(+fs: List<&2, Main.Full>, +d: String, m: {Rev.member(Main.ids(fs), d) == True{} : Bool}) -> {Rev.member(Main.ids(List.sort(~Main.Full, ~(a => b => Arrange.full_le(a, b)), fs)), d) == True{} : Bool}:
  fkeyed_mem(List.sort(~Main.Full, ~(a => b => Arrange.full_le(a, b)), fs), d,
    (%Equal.sym(List<&2, Main.Full>, SortL.keyed(~Main.Full, ~(g => Main.id_of(g)), d, List.sort(~Main.Full, ~(a => b => Arrange.full_le(a, b)), fs)), SortL.keyed(~Main.Full, ~(g => Main.id_of(g)), d, fs), SortL.sort_keyed(~Main.Full, ~(g => Main.id_of(g)), fs, d)) : {List.is_empty(&2, Main.Full, _) == False{} : Bool}; fmem_keyed(fs, d, m)))

def same_prev(+i: String, +prev: String, +x: String, ep: {String.eq(i, prev) == True{} : Bool}, ex: {String.eq(i, x) == True{} : Bool}, hx: {String.eq(x, prev) == False{} : Bool}) -> Empty:
  +a = S.eq_true(i, prev, ep)
  +b = S.eq_true(i, x, ex)
  +xp = Equal.trans(String, x, i, prev, Equal.sym(String, i, x, b), a)
  +eq = Equal.trans(Bool, String.eq(x, prev), String.eq(prev, prev), True{}, Equal.cong(String, Bool, z => String.eq(z, prev), x, prev, xp), S.eq_refl(prev))
  S.true_false(Equal.trans(Bool, True{}, String.eq(x, prev), False{}, Equal.sym(Bool, String.eq(x, prev), True{}, eq), hx))

def dedup_step(c: Bool, a: Bool, +f: Main.Full, +rest: List<&2, Main.Full>, +r: List<&2, Main.Full>, +prev: String, +x: String, +ec: {Bool.not(String.eq(Main.id_of(f), prev)) == c : Bool}, +ea: {String.eq(Main.id_of(f), x) == a : Bool}, +hx: {String.eq(x, prev) == False{} : Bool}, m: {Bool.or(a, Rev.member(Main.ids(rest), x)) == True{} : Bool}, ih: {String.eq(x, Main.id_of(f)) == False{} : Bool} -> {Rev.member(Main.ids(rest), x) == True{} : Bool} -> {Rev.member(Main.ids(r), x) == True{} : Bool}) -> {Rev.member(Main.ids(Main.keep_full(c, f, r)), x) == True{} : Bool}:
  match c a:
    case True{} True{}:
      PruneL.or_lt(String.eq(Main.id_of(f), x), Rev.member(Main.ids(r), x), ea)
    case True{} False{}:
      PruneL.or_rt(String.eq(Main.id_of(f), x), Rev.member(Main.ids(r), x), ih(ML.eq_flip(Main.id_of(f), x, ea), m))
    case False{} True{}:
      Empty.absurd({Rev.member(Main.ids(r), x) == True{} : Bool}, same_prev(Main.id_of(f), prev, x, PruneL.not_false_true(String.eq(Main.id_of(f), prev), ec), ea, hx))
    case False{} False{}:
      ih(ML.eq_flip(Main.id_of(f), x, ea), m)

# Each revision once keeps every digest but the one it starts past.
def dedup_mem(fs: List<&2, Main.Full>, +prev: String, +x: String, +hx: {String.eq(x, prev) == False{} : Bool}, m: {Rev.member(Main.ids(fs), x) == True{} : Bool}) -> {Rev.member(Main.ids(Arrange.dedup(fs, prev)), x) == True{} : Bool}:
  match fs:
    case Nil{}:
      m
    case +f <> +rest:
      dedup_step(Bool.not(String.eq(Main.id_of(f), prev)), String.eq(Main.id_of(f), x), f, rest, Arrange.dedup(rest, Main.id_of(f)), prev, x, {==}, {==}, hx, m,
        hf => hm => dedup_mem(rest, Main.id_of(f), x, hf, hm))

def le_nil(s: String, h: {String.is_le(s, SNil{}) == True{} : Bool}) -> {s == SNil{} : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      Empty.absurd({SCon{c, t} == SNil{} : String}, S.false_true(h))

def nil_kept(e: Bool, +i: String, +prev: String, +eb: {Bool.not(String.eq(i, prev)) == True{} : Bool}, +hl: {String.is_le(prev, i) == True{} : Bool}, +ee: {String.eq(i, SNil{}) == e : Bool}) -> {String.eq(i, SNil{}) == False{} : Bool}:
  match e:
    case True{}:
      +ei = S.eq_true(i, SNil{}, ee)
      +hp = le_nil(prev, (%ei : {String.is_le(prev, _) == True{} : Bool}; hl))
      +ne = ArrangeL.not_tt(String.eq(i, prev), eb)
      Empty.absurd({String.eq(i, SNil{}) == False{} : Bool}, S.true_false(Equal.trans(Bool, True{}, String.eq(i, prev), False{}, Equal.sym(Bool, String.eq(i, prev), True{}, (%Equal.sym(String, i, SNil{}, ei) : {String.eq(_, prev) == True{} : Bool}; %Equal.sym(String, prev, SNil{}, hp) : {String.eq(SNil{}, _) == True{} : Bool}; {==})), ne)))
    case False{}:
      ee

def dedup_ne.hit(c: Bool, +i: String, +t: String, +r: List<&2, Store.Doc>, +prev: String, +id: String, +text: String, +eb: {Bool.not(String.eq(i, prev)) == True{} : Bool}, +hl: {String.is_le(prev, i) == True{} : Bool}, +ec: {Bool.and(String.eq(i, id), String.eq(t, text)) == c : Bool}, h: {Bool.or(c, holds(r, id, text)) == True{} : Bool}, ih: {holds(r, id, text) == True{} : Bool} -> {String.eq(id, SNil{}) == False{} : Bool}) -> {String.eq(id, SNil{}) == False{} : Bool}:
  match c:
    case True{}:
      %S.eq_true(i, id, ArrangeL.and_tl(String.eq(i, id), String.eq(t, text), ec)) : {String.eq(_, SNil{}) == False{} : Bool}
      nil_kept(String.eq(i, SNil{}), i, prev, eb, hl, {==})
    case False{}:
      ih(h)

def dedup_ne.keep(b: Bool, +p: String, +i: String, +n: Nat, +t: String, +r: List<&2, Store.Doc>, +prev: String, +id: String, +text: String, +eb: {Bool.not(String.eq(i, prev)) == b : Bool}, +hl: {String.is_le(prev, i) == True{} : Bool}, h: {holds(Receive.doc.keep(b, Store.Doc{p, i, n, t}, r), id, text) == True{} : Bool}, ih: {holds(r, id, text) == True{} : Bool} -> {String.eq(id, SNil{}) == False{} : Bool}) -> {String.eq(id, SNil{}) == False{} : Bool}:
  match b:
    case True{}:
      dedup_ne.hit(Bool.and(String.eq(i, id), String.eq(t, text)), i, t, r, prev, id, text, eb, hl, {==}, h, ih)
    case False{}:
      ih(h)

# Each document once, of documents in digest order, keeps none under the
# empty digest: the first of them is the one it starts past.
def dedup_ne(ys: List<&2, Store.Doc>, +prev: String, +id: String, +text: String, +hs: {SortL.sorted.from(~Store.Doc, ~(d => Store.id_of(d)), ys, prev) == True{} : Bool}, h: {holds(Receive.docs.dedup(ys, prev), id, text) == True{} : Bool}) -> {String.eq(id, SNil{}) == False{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({String.eq(id, SNil{}) == False{} : Bool}, S.false_true(h))
    case Store.Doc{+p, +i, +n, +t} <> +rest:
      dedup_ne.keep(Bool.not(String.eq(i, prev)), p, i, n, t, Receive.docs.dedup(rest, i), prev, id, text, {==},
        ArrangeL.and_tl(String.is_le(prev, i), SortL.sorted.from(~Store.Doc, ~(d => Store.id_of(d)), rest, i), hs), h,
        hr => dedup_ne(rest, i, id, text, ArrangeL.and_tr(String.is_le(prev, i), SortL.sorted.from(~Store.Doc, ~(d => Store.id_of(d)), rest, i), hs), hr))

def ne_distinct(+xs: List<&2, Store.Doc>, +id: String, +text: String, h: {holds(Receive.docs.distinct(xs), id, text) == True{} : Bool}) -> {String.eq(id, SNil{}) == False{} : Bool}:
  dedup_ne(List.sort(~Store.Doc, ~(a => b => Receive.doc.id_le(a, b)), xs), SNil{}, id, text, SortL.sort_sorted(~Store.Doc, ~(d => Store.id_of(d)), xs), h)

def here_lacks(m: Bool, +ds: List<&2, Store.Doc>, +id: String, +em: {Rev.member(doc_ids(ds), id) == m : Bool}, +hp: {Arrange.all_parse(ds) == True{} : Bool}, +hne: {String.eq(id, SNil{}) == False{} : Bool}, +hn: {Rev.member(Main.ids(Arrange.distinct(Prune.fulls(ds))), id) == False{} : Bool}) -> {Bool.not(m) == True{} : Bool}:
  match m:
    case True{}:
      +mf = Equal.trans(Bool, Rev.member(Main.ids(Prune.fulls(ds)), id), Rev.member(doc_ids(ds), id), True{}, Equal.cong(List<&2, String>, Bool, l => Rev.member(l, id), Main.ids(Prune.fulls(ds)), doc_ids(ds), fulls_ids(ds, hp)), em)
      +md = dedup_mem(List.sort(~Main.Full, ~(a => b => Arrange.full_le(a, b)), Prune.fulls(ds)), SNil{}, id, hne, fsort_mem(Prune.fulls(ds), id, mf))
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, S.true_false(Equal.trans(Bool, True{}, Rev.member(Main.ids(Arrange.distinct(Prune.fulls(ds))), id), False{}, Equal.sym(Bool, Rev.member(Main.ids(Arrange.distinct(Prune.fulls(ds))), id), True{}, md), hn)))
    case False{}:
      {==}

# Every revision `receive` files is one of the source's revision
# documents, by its digest and its text, under a digest no revision
# document of this store has.
def revisions(+here: Receive.Side, +there: Receive.Side, +join: Bool, +p: Receive.RPlan, +e: {Receive.plan.r(here, there, join) == Done{p} : Result<&2, &2, Main.Refused, Receive.RPlan>}, +id: String, +text: String, h: {holds(Receive.rplan.revisions(p), id, text) == True{} : Bool}) -> {Bool.and(Bool.not(Rev.member(doc_ids(Arrange.revision_docs(Receive.stored.docs(Receive.stored.of(here)))), id)), holds(Arrange.revision_docs(Receive.stored.docs(Receive.stored.of(there))), id, text)) == True{} : Bool}:
  +ep = planned(here, there, join, p, e)
  +hs = planned_sound(here, there, join, p, e)
  +rh = Arrange.revision_docs(Receive.stored.docs(Receive.stored.of(here)))
  +rt = Arrange.revision_docs(Receive.stored.docs(Receive.stored.of(there)))
  +hp = Equal.trans(Bool, holds(Receive.rplan.revisions(Receive.plan.of(here, there)), id, text), holds(Receive.rplan.revisions(p), id, text), True{}, Equal.cong(Receive.RPlan, Bool, q => holds(Receive.rplan.revisions(q), id, text), Receive.plan.of(here, there), p, ep), h)
  +hl = lacking_holds(Receive.side.revisions(there), Receive.have.revisions(here), id, text, hp)
  +hf = lacking_fresh(Receive.side.revisions(there), Receive.have.revisions(here), id, text, hp)
  +hne = ne_distinct(Receive.docs.parsing(rt), id, text, hl)
  B.and_tt(Bool.not(Rev.member(doc_ids(rh), id)), holds(rt, id, text),
    here_lacks(Rev.member(doc_ids(rh), id), rh, id, {==}, sound_parse(Receive.stored.of(here), hs), hne, ArrangeL.has_false(Main.ids(Receive.side.fulls(here)), id, hf)),
    parsing_holds(rt, id, text, distinct_holds(Receive.docs.parsing(rt), id, text, hl)))

# Related histories
# -----------------

# Whether some string of `xs` is among `ys`.
def any_member(xs: List<&2, String>, +ys: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +x <> rest:
      Bool.or(Rev.member(ys, x), any_member(rest, ys))

# Whether some revision of `fs` names one of `ys` as a parent, or as what
# it supersedes.
def names_one(+ys: List<&2, String>, fs: List<&2, Main.Full>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Main.Full{i, c, +parents, +supersedes, a, w, rb, rv, fa, m} <> rest:
      Bool.or(Bool.or(any_member(parents, ys), any_member(supersedes, ys)), names_one(ys, rest))

# Decision 0029's evidence that two histories are one, read from the
# revisions themselves: one side is empty; or they share a revision; or a
# revision of either names one of the other's as a parent or as what it
# supersedes.
def related(+ours: List<&2, Main.Full>, +theirs: List<&2, Main.Full>) -> Bool:
  Bool.or(Bool.or(List.is_empty(&2, Main.Full, ours), List.is_empty(&2, Main.Full, theirs)),
    Bool.or(any_member(Main.ids(theirs), Main.ids(ours)), Bool.or(names_one(Main.ids(ours), theirs), names_one(Main.ids(theirs), ours))))

def any_in_is(xs: List<&2, String>, +ys: List<&2, String>) -> {Receive.any_in(xs, Set.from_list(ys)) == any_member(xs, ys) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, Arrange.has(Set.from_list(ys), x), Rev.member(ys, x), ArrangeL.has_list(ys, x)) : {Bool.or(_, Receive.any_in(rest, Set.from_list(ys))) == Bool.or(Rev.member(ys, x), any_member(rest, ys)) : Bool}
      Equal.cong(Bool, Bool, z => Bool.or(Rev.member(ys, x), z), Receive.any_in(rest, Set.from_list(ys)), any_member(rest, ys), any_in_is(rest, ys))

def am_app(xs: List<&2, String>, +zs: List<&2, String>, +ys: List<&2, String>) -> {any_member(List.append(&2, String, xs, zs), ys) == Bool.or(any_member(xs, ys), any_member(zs, ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, any_member(List.append(&2, String, rest, zs), ys), Bool.or(any_member(rest, ys), any_member(zs, ys)), am_app(rest, zs, ys)) : {Bool.or(Rev.member(ys, x), _) == Bool.or(any_member(x <> rest, ys), any_member(zs, ys)) : Bool}
      ArrangeL.or_assoc(Rev.member(ys, x), any_member(rest, ys), any_member(zs, ys))

def edges_is(fs: List<&2, Main.Full>, +ys: List<&2, String>) -> {any_member(Receive.edges(fs), ys) == names_one(ys, fs) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Main.Full{+i, +c, +parents, +supersedes, +a, +w, +rb, +rv, +fa, +m} <> +rest:
      %Equal.sym(Bool, any_member(List.append(&2, String, List.append(&2, String, parents, supersedes), Receive.edges(rest)), ys), Bool.or(any_member(List.append(&2, String, parents, supersedes), ys), any_member(Receive.edges(rest), ys)), am_app(List.append(&2, String, parents, supersedes), Receive.edges(rest), ys)) : {_ == names_one(ys, Main.Full{i, c, parents, supersedes, a, w, rb, rv, fa, m} <> rest) : Bool}
      %Equal.sym(Bool, any_member(List.append(&2, String, parents, supersedes), ys), Bool.or(any_member(parents, ys), any_member(supersedes, ys)), am_app(parents, supersedes, ys)) : {Bool.or(_, any_member(Receive.edges(rest), ys)) == names_one(ys, Main.Full{i, c, parents, supersedes, a, w, rb, rv, fa, m} <> rest) : Bool}
      Equal.cong(Bool, Bool, z => Bool.or(Bool.or(any_member(parents, ys), any_member(supersedes, ys)), z), any_member(Receive.edges(rest), ys), names_one(ys, rest), edges_is(rest, ys))

def related_is(+ours: List<&2, Main.Full>, +theirs: List<&2, Main.Full>) -> {Receive.related(ours, theirs) == related(ours, theirs) : Bool}:
  %Equal.sym(Bool, Receive.any_in(Main.ids(theirs), Set.from_list(Main.ids(ours))), any_member(Main.ids(theirs), Main.ids(ours)), any_in_is(Main.ids(theirs), Main.ids(ours))) : {Bool.or(Bool.or(List.is_empty(&2, Main.Full, ours), List.is_empty(&2, Main.Full, theirs)), Bool.or(_, Bool.or(Receive.any_in(Receive.edges(theirs), Set.from_list(Main.ids(ours))), Receive.any_in(Receive.edges(ours), Set.from_list(Main.ids(theirs)))))) == related(ours, theirs) : Bool}
  %Equal.sym(Bool, Receive.any_in(Receive.edges(theirs), Set.from_list(Main.ids(ours))), any_member(Receive.edges(theirs), Main.ids(ours)), any_in_is(Receive.edges(theirs), Main.ids(ours))) : {Bool.or(Bool.or(List.is_empty(&2, Main.Full, ours), List.is_empty(&2, Main.Full, theirs)), Bool.or(any_member(Main.ids(theirs), Main.ids(ours)), Bool.or(_, Receive.any_in(Receive.edges(ours), Set.from_list(Main.ids(theirs)))))) == related(ours, theirs) : Bool}
  %Equal.sym(Bool, Receive.any_in(Receive.edges(ours), Set.from_list(Main.ids(theirs))), any_member(Receive.edges(ours), Main.ids(theirs)), any_in_is(Receive.edges(ours), Main.ids(theirs))) : {Bool.or(Bool.or(List.is_empty(&2, Main.Full, ours), List.is_empty(&2, Main.Full, theirs)), Bool.or(any_member(Main.ids(theirs), Main.ids(ours)), Bool.or(any_member(Receive.edges(theirs), Main.ids(ours)), _))) == related(ours, theirs) : Bool}
  %Equal.sym(Bool, any_member(Receive.edges(theirs), Main.ids(ours)), names_one(Main.ids(ours), theirs), edges_is(theirs, Main.ids(ours))) : {Bool.or(Bool.or(List.is_empty(&2, Main.Full, ours), List.is_empty(&2, Main.Full, theirs)), Bool.or(any_member(Main.ids(theirs), Main.ids(ours)), Bool.or(_, any_member(Receive.edges(ours), Main.ids(theirs))))) == related(ours, theirs) : Bool}
  %Equal.sym(Bool, any_member(Receive.edges(ours), Main.ids(theirs)), names_one(Main.ids(theirs), ours), edges_is(ours, Main.ids(theirs))) : {Bool.or(Bool.or(List.is_empty(&2, Main.Full, ours), List.is_empty(&2, Main.Full, theirs)), Bool.or(any_member(Main.ids(theirs), Main.ids(ours)), Bool.or(names_one(Main.ids(ours), theirs), _))) == related(ours, theirs) : Bool}
  {==}

def related_done.of(c: Bool, +here: Receive.Side, +there: Receive.Side) -> {Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.related(c, here, there)) == c : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# Between two stores the check passes, `receive` plans exactly where the
# histories are related or it was asked to join them.
def joins(+here: Receive.Side, +there: Receive.Side, +join: Bool, hh: {Prune.sound(Receive.stored.of(here)) == True{} : Bool}, ht: {Prune.sound(Receive.stored.of(there)) == True{} : Bool}) -> {Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.r(here, there, join)) == Bool.or(join, related(Receive.side.fulls(here), Receive.side.fulls(there))) : Bool}:
  %Equal.sym(Bool, Prune.sound(Receive.stored.of(here)), True{}, hh) : {Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.here(_, here, there, join)) == Bool.or(join, related(Receive.side.fulls(here), Receive.side.fulls(there))) : Bool}
  %Equal.sym(Bool, Prune.sound(Receive.stored.of(there)), True{}, ht) : {Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.source(_, here, there, join)) == Bool.or(join, related(Receive.side.fulls(here), Receive.side.fulls(there))) : Bool}
  %related_is(Receive.side.fulls(here), Receive.side.fulls(there)) : {Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.source(True{}, here, there, join)) == Bool.or(join, _) : Bool}
  related_done.of(Bool.or(join, Receive.related(Receive.side.fulls(here), Receive.side.fulls(there))), here, there)

# Bookmarks, said of the stores' own
# ----------------------------------

# Whether one of these bookmarks has this name.
def named(bs: List<&2, Bm.Bookmark>, +n: String) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Bm.Bookmark{+bn, bt, bp} <> rest:
      Bool.or(String.eq(bn, n), named(rest, n))

# Whether one of these bookmarks has this name and points where `at`
# spells a target.
def marks_at(bs: List<&2, Bm.Bookmark>, +n: String, +at: String) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Bm.Bookmark{+bn, +bt, bp} <> rest:
      Bool.or(Bool.and(String.eq(bn, n), String.eq(Bm.show_target(bt), at)), marks_at(rest, n, at))

def mb_none(m: Maybe<&2, Bm.Bookmark>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some(-x: Bm.Bookmark, e: {None{} == Some{x} : Maybe<&2, Bm.Bookmark>}) -> Empty:
  %e : {mb_none(_) : Type}
  Unit{}

def mtarget(m: Maybe<&2, Bm.Bookmark>, +d: Bm.Target) -> Bm.Target:
  match m:
    case None{}:
      d
    case Some{Bm.Bookmark{n, t, p}}:
      t

def found_none.of(c: Bool, +bn: String, +bt: Bm.Target, +bp: Bool, +rest: List<&2, Bm.Bookmark>, +n: String, e: {Bool.pick(Maybe<&2, Bm.Bookmark>, c, Some{Bm.Bookmark{bn, bt, bp}}, Main.found_of(rest, n)) == None{} : Maybe<&2, Bm.Bookmark>}, ih: {Main.found_of(rest, n) == None{} : Maybe<&2, Bm.Bookmark>} -> {named(rest, n) == False{} : Bool}) -> {Bool.or(c, named(rest, n)) == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, none_some(Bm.Bookmark{bn, bt, bp}, Equal.sym(Maybe<&2, Bm.Bookmark>, Some{Bm.Bookmark{bn, bt, bp}}, None{}, e)))
    case False{}:
      ih(e)

# Where the store's lookup finds no bookmark of a name, it has none.
def found_none(hm: List<&2, Bm.Bookmark>, +n: String, e: {Main.found_of(hm, n) == None{} : Maybe<&2, Bm.Bookmark>}) -> {named(hm, n) == False{} : Bool}:
  match hm:
    case Nil{}:
      {==}
    case Bm.Bookmark{+bn, +bt, +bp} <> +rest:
      found_none.of(String.eq(bn, n), bn, bt, bp, rest, n, e, h => found_none(rest, n, h))

def found_marks.of(c: Bool, +bn: String, +bt: Bm.Target, +bp: Bool, +rest: List<&2, Bm.Bookmark>, +n: String, +hn: String, +ht: Bm.Target, +hp: Bool, +ec: {String.eq(bn, n) == c : Bool}, e: {Bool.pick(Maybe<&2, Bm.Bookmark>, c, Some{Bm.Bookmark{bn, bt, bp}}, Main.found_of(rest, n)) == Some{Bm.Bookmark{hn, ht, hp}} : Maybe<&2, Bm.Bookmark>}, ih: {Main.found_of(rest, n) == Some{Bm.Bookmark{hn, ht, hp}} : Maybe<&2, Bm.Bookmark>} -> {marks_at(rest, n, Bm.show_target(ht)) == True{} : Bool}) -> {Bool.or(Bool.and(c, String.eq(Bm.show_target(bt), Bm.show_target(ht))), marks_at(rest, n, Bm.show_target(ht))) == True{} : Bool}:
  match c:
    case True{}:
      +et = Equal.cong(Maybe<&2, Bm.Bookmark>, Bm.Target, m => mtarget(m, bt), Some{Bm.Bookmark{bn, bt, bp}}, Some{Bm.Bookmark{hn, ht, hp}}, e)
      %et : {Bool.or(String.eq(Bm.show_target(bt), Bm.show_target(_)), marks_at(rest, n, Bm.show_target(_))) == True{} : Bool}
      PruneL.or_lt(String.eq(Bm.show_target(bt), Bm.show_target(bt)), marks_at(rest, n, Bm.show_target(bt)), S.eq_refl(Bm.show_target(bt)))
    case False{}:
      PruneL.or_rt(False{}, marks_at(rest, n, Bm.show_target(ht)), ih(e))

# The bookmark the store's lookup finds is one it has, by that name.
def found_marks(hm: List<&2, Bm.Bookmark>, +n: String, +hn: String, +ht: Bm.Target, +hp: Bool, e: {Main.found_of(hm, n) == Some{Bm.Bookmark{hn, ht, hp}} : Maybe<&2, Bm.Bookmark>}) -> {marks_at(hm, n, Bm.show_target(ht)) == True{} : Bool}:
  match hm:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, none_some(Bm.Bookmark{hn, ht, hp}, e))
    case Bm.Bookmark{+bn, +bt, +bp} <> +rest:
      found_marks.of(String.eq(bn, n), bn, bt, bp, rest, n, hn, ht, hp, {==}, e, h => found_marks(rest, n, hn, ht, hp, h))

def keeps_spec(found: Maybe<&2, Bm.Bookmark>, +hm: List<&2, Bm.Bookmark>, +n: String, +t: Bm.Target, +ef: {Main.found_of(hm, n) == found : Maybe<&2, Bm.Bookmark>}, h: {Receive.keeps.of(t, found) == True{} : Bool}) -> {Bool.or(Bool.not(named(hm, n)), marks_at(hm, n, Bm.show_target(t))) == True{} : Bool}:
  match found:
    case None{}:
      %Equal.sym(Bool, named(hm, n), False{}, found_none(hm, n, ef)) : {Bool.or(Bool.not(_), marks_at(hm, n, Bm.show_target(t))) == True{} : Bool}
      {==}
    case Some{Bm.Bookmark{+hn, +ht, +hp}}:
      +es = S.eq_true(Bm.show_target(ht), Bm.show_target(t), h)
      PruneL.or_rt(Bool.not(named(hm, n)), marks_at(hm, n, Bm.show_target(t)), (%es : {marks_at(hm, n, _) == True{} : Bool}; found_marks(hm, n, hn, ht, hp, ef)))

def kept_hit(c: Bool, +bn: String, +bt: Bm.Target, +bp: Bool, +rest: List<&2, Bm.Bookmark>, +hm: List<&2, Bm.Bookmark>, +n: String, +at: String, +ec: {Bool.and(String.eq(bn, n), String.eq(Bm.show_target(bt), at)) == c : Bool}, +hk: {Receive.keeps(hm, Bm.Bookmark{bn, bt, bp}) == True{} : Bool}, h: {Bool.or(c, marks_at(rest, n, at)) == True{} : Bool}, ih: {marks_at(rest, n, at) == True{} : Bool} -> {Bool.or(Bool.not(named(hm, n)), marks_at(hm, n, at)) == True{} : Bool}) -> {Bool.or(Bool.not(named(hm, n)), marks_at(hm, n, at)) == True{} : Bool}:
  match c:
    case True{}:
      %S.eq_true(bn, n, ArrangeL.and_tl(String.eq(bn, n), String.eq(Bm.show_target(bt), at), ec)) : {Bool.or(Bool.not(named(hm, _)), marks_at(hm, _, at)) == True{} : Bool}
      %S.eq_true(Bm.show_target(bt), at, ArrangeL.and_tr(String.eq(bn, n), String.eq(Bm.show_target(bt), at), ec)) : {Bool.or(Bool.not(named(hm, bn)), marks_at(hm, bn, _)) == True{} : Bool}
      keeps_spec(Main.found_of(hm, bn), hm, bn, bt, {==}, hk)
    case False{}:
      ih(h)

# Of bookmarks each of which leaves this store's pointing where it did:
# each names none of this store's, or one of this store's at its target.
def kept_marks(bs: List<&2, Bm.Bookmark>, +hm: List<&2, Bm.Bookmark>, +n: String, +at: String, +hk: {Receive.names_kept(bs, hm) == True{} : Bool}, h: {marks_at(bs, n, at) == True{} : Bool}) -> {Bool.or(Bool.not(named(hm, n)), marks_at(hm, n, at)) == True{} : Bool}:
  match bs:
    case Nil{}:
      Empty.absurd({Bool.or(Bool.not(named(hm, n)), marks_at(hm, n, at)) == True{} : Bool}, S.false_true(h))
    case Bm.Bookmark{+bn, +bt, +bp} <> +rest:
      kept_hit(Bool.and(String.eq(bn, n), String.eq(Bm.show_target(bt), at)), bn, bt, bp, rest, hm, n, at, {==},
        ArrangeL.and_tl(Receive.keeps(hm, Bm.Bookmark{bn, bt, bp}), Receive.names_kept(rest, hm), hk), h,
        hr => kept_marks(rest, hm, n, at, ArrangeL.and_tr(Receive.keeps(hm, Bm.Bookmark{bn, bt, bp}), Receive.names_kept(rest, hm), hk), hr))

# `receive` moves no bookmark this store has: every one it writes is one
# this store has none of by that name, or has at that very target.
def moves_none(+here: Receive.Side, +there: Receive.Side, +n: String, +at: String, h: {marks_at(Receive.rplan.names(Receive.plan.of(here, there)), n, at) == True{} : Bool}) -> {Bool.or(Bool.not(named(Receive.side.marks(here), n)), marks_at(Receive.side.marks(here), n, at)) == True{} : Bool}:
  kept_marks(Receive.rplan.names(Receive.plan.of(here, there)), Receive.side.marks(here), n, at, names(here, there), h)

# The files it removes
# --------------------

# Whether one of these files is at `x` and holds one of `des`.
def gone_at(ss: List<&2, T.Split>, +x: String, +des: List<&2, String>) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case T.Split{+q, +d} <> rest:
      Bool.or(Bool.and(String.eq(q, x), Rev.member(des, d)), gone_at(rest, x, des))

def gone_hit(c: Bool, e: Bool, +q: String, +d: String, +r: List<&2, T.Split>, +rest: List<&2, T.Split>, +x: String, +des: List<&2, String>, +ec: {Arrange.has(Set.from_list(des), d) == c : Bool}, +ee: {String.eq(q, x) == e : Bool}, h: {Rev.member(T.map(~T.Split, ~String, ~(s => Prune.split.path(s)), Tree.keep(~T.Split, c, T.Split{q, d}, r)), x) == True{} : Bool}, ih: {Rev.member(T.map(~T.Split, ~String, ~(s => Prune.split.path(s)), r), x) == True{} : Bool} -> {gone_at(rest, x, des) == True{} : Bool}) -> {gone_at(T.Split{q, d} <> rest, x, des) == True{} : Bool}:
  match c e:
    case True{} True{}:
      PruneL.or_lt(Bool.and(String.eq(q, x), Rev.member(des, d)), gone_at(rest, x, des),
        B.and_tt(String.eq(q, x), Rev.member(des, d), ee, Equal.trans(Bool, Rev.member(des, d), Arrange.has(Set.from_list(des), d), True{}, Equal.sym(Bool, Arrange.has(Set.from_list(des), d), Rev.member(des, d), ArrangeL.has_list(des, d)), ec)))
    case True{} False{}:
      PruneL.or_rt(Bool.and(String.eq(q, x), Rev.member(des, d)), gone_at(rest, x, des), ih(ArrangeL.or_tt_r(String.eq(q, x), Rev.member(T.map(~T.Split, ~String, ~(s => Prune.split.path(s)), r), x), h, ee)))
    case False{} _:
      PruneL.or_rt(Bool.and(String.eq(q, x), Rev.member(des, d)), gone_at(rest, x, des), ih(h))

# What `kept.in` keeps of a list of files holds one of the digests asked
# about.
def kept_gone(ss: List<&2, T.Split>, +des: List<&2, String>, +x: String, h: {Rev.member(T.map(~T.Split, ~String, ~(s => Prune.split.path(s)), Receive.kept.in(ss, Set.from_list(des))), x) == True{} : Bool}) -> {gone_at(ss, x, des) == True{} : Bool}:
  match ss:
    case Nil{}:
      h
    case T.Split{+q, +d} <> +rest:
      gone_hit(Arrange.has(Set.from_list(des), d), String.eq(q, x), q, d, Receive.kept.in(rest, Set.from_list(des)), rest, x, des, {==}, {==}, h, hr => kept_gone(rest, des, x, hr))

def tkeep_gone(b: Bool, +q: String, +d: String, +r: List<&2, T.Split>, +rest: List<&2, T.Split>, +x: String, +des: List<&2, String>, h: {gone_at(Tree.keep(~T.Split, b, T.Split{q, d}, r), x, des) == True{} : Bool}, ih: {gone_at(r, x, des) == True{} : Bool} -> {gone_at(rest, x, des) == True{} : Bool}) -> {gone_at(T.Split{q, d} <> rest, x, des) == True{} : Bool}:
  match b:
    case True{}:
      PruneL.or_tt(Bool.and(String.eq(q, x), Rev.member(des, d)), gone_at(r, x, des), gone_at(rest, x, des), h, ih)
    case False{}:
      PruneL.or_rt(Bool.and(String.eq(q, x), Rev.member(des, d)), gone_at(rest, x, des), ih(h))

def sdedup_gone(ys: List<&2, T.Split>, +prev: String, +x: String, +des: List<&2, String>, h: {gone_at(Receive.splits.dedup(ys, prev), x, des) == True{} : Bool}) -> {gone_at(ys, x, des) == True{} : Bool}:
  match ys:
    case Nil{}:
      h
    case T.Split{+q, +d} <> +rest:
      tkeep_gone(Bool.not(String.eq(d, prev)), q, d, Receive.splits.dedup(rest, d), rest, x, des, h, hr => sdedup_gone(rest, d, x, des, hr))

def lists_hit(c: Bool, +q: String, +d: String, +rest: List<&2, T.Split>, +path: String, +dd: String, +x: String, +des: List<&2, String>, +ec: {Bool.and(String.eq(q, path), String.eq(d, dd)) == c : Bool}, +hx: {String.eq(path, x) == True{} : Bool}, +hd: {Rev.member(des, dd) == True{} : Bool}, h: {Bool.or(c, lists(rest, path, dd)) == True{} : Bool}, ih: {lists(rest, path, dd) == True{} : Bool} -> {gone_at(rest, x, des) == True{} : Bool}) -> {gone_at(T.Split{q, d} <> rest, x, des) == True{} : Bool}:
  match c:
    case True{}:
      +eq = S.eq_true(q, path, ArrangeL.and_tl(String.eq(q, path), String.eq(d, dd), ec))
      +ed = S.eq_true(d, dd, ArrangeL.and_tr(String.eq(q, path), String.eq(d, dd), ec))
      PruneL.or_lt(Bool.and(String.eq(q, x), Rev.member(des, d)), gone_at(rest, x, des),
        (%Equal.sym(String, q, path, eq) : {Bool.and(String.eq(_, x), Rev.member(des, d)) == True{} : Bool}; %Equal.sym(String, d, dd, ed) : {Bool.and(String.eq(path, x), Rev.member(des, _)) == True{} : Bool}; B.and_tt(String.eq(path, x), Rev.member(des, dd), hx, hd)))
    case False{}:
      PruneL.or_rt(Bool.and(String.eq(q, x), Rev.member(des, d)), gone_at(rest, x, des), ih(h))

# A file a list lists, at `x` and holding one of `des`, is one of them.
def lists_gone(cs: List<&2, T.Split>, +path: String, +dd: String, +x: String, +des: List<&2, String>, +hx: {String.eq(path, x) == True{} : Bool}, +hd: {Rev.member(des, dd) == True{} : Bool}, h: {lists(cs, path, dd) == True{} : Bool}) -> {gone_at(cs, x, des) == True{} : Bool}:
  match cs:
    case Nil{}:
      h
    case T.Split{+q, +d} <> +rest:
      lists_hit(Bool.and(String.eq(q, path), String.eq(d, dd)), q, d, rest, path, dd, x, des, {==}, hx, hd, h, hr => lists_gone(rest, path, dd, x, des, hx, hd, hr))

def from_gone.hit(c: Bool, +q: String, +d: String, +rest: List<&2, T.Split>, +cs: List<&2, T.Split>, +x: String, +des: List<&2, String>, +ec: {Bool.and(String.eq(q, x), Rev.member(des, d)) == c : Bool}, +hc: {lists(cs, q, d) == True{} : Bool}, h: {Bool.or(c, gone_at(rest, x, des)) == True{} : Bool}, ih: {gone_at(rest, x, des) == True{} : Bool} -> {gone_at(cs, x, des) == True{} : Bool}) -> {gone_at(cs, x, des) == True{} : Bool}:
  match c:
    case True{}:
      lists_gone(cs, q, d, x, des, ArrangeL.and_tl(String.eq(q, x), Rev.member(des, d), ec), ArrangeL.and_tr(String.eq(q, x), Rev.member(des, d), ec), hc)
    case False{}:
      ih(h)

def from_gone(ys: List<&2, T.Split>, +cs: List<&2, T.Split>, +x: String, +des: List<&2, String>, +ha: {SortL.all_at(~T.Split, ~List<&2, T.Split>, ~(c => a => listed.by(c, a)), cs, ys) == True{} : Bool}, h: {gone_at(ys, x, des) == True{} : Bool}) -> {gone_at(cs, x, des) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({gone_at(cs, x, des) == True{} : Bool}, S.false_true(h))
    case T.Split{+q, +d} <> +rest:
      from_gone.hit(Bool.and(String.eq(q, x), Rev.member(des, d)), q, d, rest, cs, x, des, {==},
        PruneL.and_l(lists(cs, q, d), SortL.all_at(~T.Split, ~List<&2, T.Split>, ~(c => a => listed.by(c, a)), cs, rest), ha), h,
        hr => from_gone(rest, cs, x, des, PruneL.and_r(lists(cs, q, d), SortL.all_at(~T.Split, ~List<&2, T.Split>, ~(c => a => listed.by(c, a)), cs, rest), ha), hr))

def sdistinct_gone(+ps: List<&2, T.Split>, +x: String, +des: List<&2, String>, h: {gone_at(Receive.splits.distinct(ps), x, des) == True{} : Bool}) -> {gone_at(ps, x, des) == True{} : Bool}:
  from_gone(List.sort(~T.Split, ~(a => b => Receive.split.le(a, b)), ps), ps, x, des,
    SortL.all_sort_at(~T.Split, ~(a => b => Receive.split.le(a, b)), ~List<&2, T.Split>, ~(c => a => listed.by(c, a)), ps, ps, sself_all(ps)),
    sdedup_gone(List.sort(~T.Split, ~(a => b => Receive.split.le(a, b)), ps), SNil{}, x, des, h))

def removed_of(m: Bool, +a: List<&2, String>, +b: List<&2, String>, +x: String, +bs: List<&2, T.Split>, +ps: List<&2, T.Split>, +des: List<&2, String>, +em: {Rev.member(a, x) == m : Bool}, h: {Bool.or(m, Rev.member(b, x)) == True{} : Bool}, ha: {Rev.member(a, x) == True{} : Bool} -> {gone_at(bs, x, des) == True{} : Bool}, hb: {Rev.member(b, x) == True{} : Bool} -> {gone_at(ps, x, des) == True{} : Bool}) -> {Bool.or(gone_at(bs, x, des), gone_at(ps, x, des)) == True{} : Bool}:
  match m:
    case True{}:
      PruneL.or_lt(gone_at(bs, x, des), gone_at(ps, x, des), ha(em))
    case False{}:
      PruneL.or_rt(gone_at(bs, x, des), gone_at(ps, x, des), hb(h))

# Every file `receive` removes for the originals it destroys is an
# operation document or a payload file of this store, at that path,
# holding one of the digests destroyed.
def removes_only(+bs: List<&2, Prune.Body>, +ps: List<&2, T.Split>, +des: List<&2, String>, +x: String, h: {Rev.member(Receive.destroyed(bs, ps, des), x) == True{} : Bool}) -> {Bool.or(gone_at(T.map(~Prune.Body, ~T.Split, ~(b => Prune.body.split(b)), bs), x, des), gone_at(ps, x, des)) == True{} : Bool}:
  +a = T.map(~T.Split, ~String, ~(s => Prune.split.path(s)), Receive.kept.in(T.map(~Prune.Body, ~T.Split, ~(b => Receive.body.split.of(b)), bs), Set.from_list(des)))
  +b = T.map(~T.Split, ~String, ~(s => Prune.split.path(s)), Receive.kept.in(Receive.splits.distinct(ps), Set.from_list(des)))
  +l = List.append(&2, String, a, b)
  +hl = ForgetL.held_member(l, Main.sorted_distinct(l), x, StatusL.ah_distinct(l, List.sort(~String, ~(a => b => String.is_le(a, b)), l), StatusL.ah_sort(~(a => b => String.is_le(a, b)), l, l, held_refl(l))), h)
  removed_of(Rev.member(a, x), a, b, x, T.map(~Prune.Body, ~T.Split, ~(b => Prune.body.split(b)), bs), ps, des, {==},
    Equal.trans(Bool, Bool.or(Rev.member(a, x), Rev.member(b, x)), Rev.member(l, x), True{}, Equal.sym(Bool, Rev.member(l, x), Bool.or(Rev.member(a, x), Rev.member(b, x)), ArrangeL.member_app(a, b, x)), hl),
    ha => kept_gone(T.map(~Prune.Body, ~T.Split, ~(b => Receive.body.split.of(b)), bs), des, x, ha),
    hb => sdistinct_gone(ps, x, des, kept_gone(Receive.splits.distinct(ps), des, x, hb)))

# Related histories, read from each side
# --------------------------------------

def or_comm(a: Bool, b: Bool) -> {Bool.or(a, b) == Bool.or(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def mix4(a: Bool, b: Bool, c: Bool, -d: Bool) -> {Bool.or(Bool.or(a, b), Bool.or(c, d)) == Bool.or(Bool.or(a, c), Bool.or(b, d)) : Bool}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def eq_sym.of(q: Bool, +x: String, +y: String, +eq: {String.eq(y, x) == q : Bool}, e: {String.eq(x, y) == False{} : Bool}) -> {False{} == q : Bool}:
  match q:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({False{} == True{} : Bool}, S.true_false(Equal.trans(Bool, True{}, String.eq(x, y), False{}, Equal.sym(Bool, String.eq(x, y), True{}, (%Equal.sym(String, y, x, S.eq_true(y, x, eq)) : {String.eq(x, _) == True{} : Bool}
        S.eq_refl(x))), e)))

def eq_sym.at(p: Bool, +x: String, +y: String, +ep: {String.eq(x, y) == p : Bool}) -> {p == String.eq(y, x) : Bool}:
  match p:
    case True{}:
      Equal.sym(Bool, String.eq(y, x), True{}, (%Equal.sym(String, x, y, S.eq_true(x, y, ep)) : {String.eq(y, _) == True{} : Bool}
        S.eq_refl(y)))
    case False{}:
      eq_sym.of(String.eq(y, x), x, y, {==}, ep)

def eq_sym(+x: String, +y: String) -> {String.eq(x, y) == String.eq(y, x) : Bool}:
  eq_sym.at(String.eq(x, y), x, y, {==})

def am_cons_r(ys: List<&2, String>, +x: String, +xs: List<&2, String>) -> {any_member(ys, x <> xs) == Bool.or(Rev.member(ys, x), any_member(ys, xs)) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +rest:
      %Equal.sym(Bool, any_member(rest, x <> xs), Bool.or(Rev.member(rest, x), any_member(rest, xs)), am_cons_r(rest, x, xs)) : {Bool.or(Bool.or(String.eq(x, y), Rev.member(xs, y)), _) == Bool.or(Rev.member(y <> rest, x), any_member(y <> rest, xs)) : Bool}
      %eq_sym(y, x) : {Bool.or(Bool.or(_, Rev.member(xs, y)), Bool.or(Rev.member(rest, x), any_member(rest, xs))) == Bool.or(Rev.member(y <> rest, x), any_member(y <> rest, xs)) : Bool}
      mix4(String.eq(y, x), Rev.member(xs, y), Rev.member(rest, x), any_member(rest, xs))

def am_nil(ys: List<&2, String>) -> {False{} == any_member(ys, Nil{}) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +rest:
      am_nil(rest)

# Two lists share a string whichever is asked of the other.
def am_sym(xs: List<&2, String>, +ys: List<&2, String>) -> {any_member(xs, ys) == any_member(ys, xs) : Bool}:
  match xs:
    case Nil{}:
      am_nil(ys)
    case +x <> +rest:
      %Equal.sym(Bool, any_member(rest, ys), any_member(ys, rest), am_sym(rest, ys)) : {Bool.or(Rev.member(ys, x), _) == any_member(ys, x <> rest) : Bool}
      Equal.sym(Bool, any_member(ys, x <> rest), Bool.or(Rev.member(ys, x), any_member(ys, rest)), am_cons_r(ys, x, rest))

# What one revision names of others: its parents, then what it says it
# supersedes.
def named_by(+f: Main.Full) -> List<&2, String>:
  List.append(&2, String, Main.parents_of(f), Prune.supersedes_of(f))

# Relatedness reads both histories alike.
def rel_sym(+ours: List<&2, Main.Full>, +theirs: List<&2, Main.Full>) -> {related(ours, theirs) == related(theirs, ours) : Bool}:
  %or_comm(List.is_empty(&2, Main.Full, theirs), List.is_empty(&2, Main.Full, ours)) : {Bool.or(_, Bool.or(any_member(Main.ids(theirs), Main.ids(ours)), Bool.or(names_one(Main.ids(ours), theirs), names_one(Main.ids(theirs), ours)))) == related(theirs, ours) : Bool}
  %am_sym(Main.ids(ours), Main.ids(theirs)) : {Bool.or(Bool.or(List.is_empty(&2, Main.Full, theirs), List.is_empty(&2, Main.Full, ours)), Bool.or(_, Bool.or(names_one(Main.ids(ours), theirs), names_one(Main.ids(theirs), ours)))) == related(theirs, ours) : Bool}
  %or_comm(names_one(Main.ids(theirs), ours), names_one(Main.ids(ours), theirs)) : {Bool.or(Bool.or(List.is_empty(&2, Main.Full, theirs), List.is_empty(&2, Main.Full, ours)), Bool.or(any_member(Main.ids(ours), Main.ids(theirs)), _)) == related(theirs, ours) : Bool}
  {==}

# Whether `receive` plans between two stores the check passes does not
# depend on which receives from which.
def either_way(+here: Receive.Side, +there: Receive.Side, +join: Bool, +hh: {Prune.sound(Receive.stored.of(here)) == True{} : Bool}, +ht: {Prune.sound(Receive.stored.of(there)) == True{} : Bool}) -> {Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.r(here, there, join)) == Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.r(there, here, join)) : Bool}:
  Equal.trans(Bool, Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.r(here, there, join)), Bool.or(join, related(Receive.side.fulls(here), Receive.side.fulls(there))), Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.r(there, here, join)),
    joins(here, there, join, hh, ht),
    Equal.trans(Bool, Bool.or(join, related(Receive.side.fulls(here), Receive.side.fulls(there))), Bool.or(join, related(Receive.side.fulls(there), Receive.side.fulls(here))), Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.r(there, here, join)),
      Equal.cong(Bool, Bool, z => Bool.or(join, z), related(Receive.side.fulls(here), Receive.side.fulls(there)), related(Receive.side.fulls(there), Receive.side.fulls(here)), rel_sym(Receive.side.fulls(here), Receive.side.fulls(there))),
      Equal.sym(Bool, Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.r(there, here, join)), Bool.or(join, related(Receive.side.fulls(there), Receive.side.fulls(here))), joins(there, here, join, ht, hh))))

def or_cases(a: Bool, -b: Bool, -X: Bool, h: {Bool.or(a, b) == True{} : Bool}, ha: {a == True{} : Bool} -> {X == True{} : Bool}, hb: {b == True{} : Bool} -> {X == True{} : Bool}) -> {X == True{} : Bool}:
  match a:
    case True{}:
      ha({==})
    case False{}:
      hb(h)

def am_hit.of(e: Bool, +x: String, +rest: List<&2, String>, +ys: List<&2, String>, +id: String, +ee: {String.eq(x, id) == e : Bool}, hy: {Rev.member(ys, id) == True{} : Bool}, hx: {Bool.or(e, Rev.member(rest, id)) == True{} : Bool}, ih: {Rev.member(rest, id) == True{} : Bool} -> {any_member(rest, ys) == True{} : Bool}) -> {Bool.or(Rev.member(ys, x), any_member(rest, ys)) == True{} : Bool}:
  match e:
    case True{}:
      %Equal.sym(String, x, id, S.eq_true(x, id, ee)) : {Bool.or(Rev.member(ys, _), any_member(rest, ys)) == True{} : Bool}
      PruneL.or_lt(Rev.member(ys, id), any_member(rest, ys), hy)
    case False{}:
      PruneL.or_rt(Rev.member(ys, x), any_member(rest, ys), ih(hx))

# A string in both lists is one they share.
def am_hit(xs: List<&2, String>, +ys: List<&2, String>, +id: String, hx: {Rev.member(xs, id) == True{} : Bool}, +hy: {Rev.member(ys, id) == True{} : Bool}) -> {any_member(xs, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(hx))
    case +x <> +rest:
      am_hit.of(String.eq(x, id), x, rest, ys, id, {==}, hy, hx, h => am_hit(rest, ys, id, h, hy))

# A revision among these whose parents or supersedes hold a string of
# `ys` is one that names one of them.
def no_hit(fs: List<&2, Main.Full>, +ys: List<&2, String>, +id: String, hc: {Rev.member(List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named_by(f)), fs)), id) == True{} : Bool}, +hy: {Rev.member(ys, id) == True{} : Bool}) -> {names_one(ys, fs) == True{} : Bool}:
  match fs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(hc))
    case Main.Full{i, c, +parents, +supersedes, a, w, rb, rv, fa, m} <> +rest:
      or_cases(Rev.member(List.append(&2, String, parents, supersedes), id), Rev.member(List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named_by(f)), rest)), id), Bool.or(Bool.or(any_member(parents, ys), any_member(supersedes, ys)), names_one(ys, rest)),
        Equal.trans(Bool, Bool.or(Rev.member(List.append(&2, String, parents, supersedes), id), Rev.member(List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named_by(f)), rest)), id)), Rev.member(List.append(&2, String, List.append(&2, String, parents, supersedes), List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named_by(f)), rest))), id), True{},
          Equal.sym(Bool, Rev.member(List.append(&2, String, List.append(&2, String, parents, supersedes), List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named_by(f)), rest))), id), Bool.or(Rev.member(List.append(&2, String, parents, supersedes), id), Rev.member(List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named_by(f)), rest)), id)), ArrangeL.member_app(List.append(&2, String, parents, supersedes), List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named_by(f)), rest)), id)), hc),
        h1 => PruneL.or_lt(Bool.or(any_member(parents, ys), any_member(supersedes, ys)), names_one(ys, rest),
          or_cases(Rev.member(parents, id), Rev.member(supersedes, id), Bool.or(any_member(parents, ys), any_member(supersedes, ys)),
            Equal.trans(Bool, Bool.or(Rev.member(parents, id), Rev.member(supersedes, id)), Rev.member(List.append(&2, String, parents, supersedes), id), True{}, Equal.sym(Bool, Rev.member(List.append(&2, String, parents, supersedes), id), Bool.or(Rev.member(parents, id), Rev.member(supersedes, id)), ArrangeL.member_app(parents, supersedes, id)), h1),
            hp => PruneL.or_lt(any_member(parents, ys), any_member(supersedes, ys), am_hit(parents, ys, id, hp, hy)),
            hs => PruneL.or_rt(any_member(parents, ys), any_member(supersedes, ys), am_hit(supersedes, ys, id, hs, hy)))),
        h2 => PruneL.or_rt(Bool.or(any_member(parents, ys), any_member(supersedes, ys)), names_one(ys, rest), no_hit(rest, ys, id, h2, hy)))

# Two histories meet where one of ours is one of theirs, or one a revision
# of theirs names as a parent or as what it supersedes.
def related_meets(+ours: List<&2, Main.Full>, +theirs: List<&2, Main.Full>, +id: String, +hi: {Rev.member(Main.ids(ours), id) == True{} : Bool}, hm: {Rev.member(List.append(&2, String, Main.ids(theirs), List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named_by(f)), theirs))), id) == True{} : Bool}) -> {related(ours, theirs) == True{} : Bool}:
  or_cases(Rev.member(Main.ids(theirs), id), Rev.member(List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named_by(f)), theirs)), id), related(ours, theirs),
    Equal.trans(Bool, Bool.or(Rev.member(Main.ids(theirs), id), Rev.member(List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named_by(f)), theirs)), id)), Rev.member(List.append(&2, String, Main.ids(theirs), List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named_by(f)), theirs))), id), True{}, Equal.sym(Bool, Rev.member(List.append(&2, String, Main.ids(theirs), List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named_by(f)), theirs))), id), Bool.or(Rev.member(Main.ids(theirs), id), Rev.member(List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named_by(f)), theirs)), id)), ArrangeL.member_app(Main.ids(theirs), List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named_by(f)), theirs)), id)), hm),
    h1 => PruneL.or_rt(Bool.or(List.is_empty(&2, Main.Full, ours), List.is_empty(&2, Main.Full, theirs)), Bool.or(any_member(Main.ids(theirs), Main.ids(ours)), Bool.or(names_one(Main.ids(ours), theirs), names_one(Main.ids(theirs), ours))),
      PruneL.or_lt(any_member(Main.ids(theirs), Main.ids(ours)), Bool.or(names_one(Main.ids(ours), theirs), names_one(Main.ids(theirs), ours)), am_hit(Main.ids(theirs), Main.ids(ours), id, h1, hi))),
    h2 => PruneL.or_rt(Bool.or(List.is_empty(&2, Main.Full, ours), List.is_empty(&2, Main.Full, theirs)), Bool.or(any_member(Main.ids(theirs), Main.ids(ours)), Bool.or(names_one(Main.ids(ours), theirs), names_one(Main.ids(theirs), ours))),
      PruneL.or_rt(any_member(Main.ids(theirs), Main.ids(ours)), Bool.or(names_one(Main.ids(ours), theirs), names_one(Main.ids(theirs), ours)),
        PruneL.or_lt(names_one(Main.ids(ours), theirs), names_one(Main.ids(theirs), ours), no_hit(theirs, Main.ids(ours), id, h2, hi)))))

# Between two stores the check passes, `receive` plans without being asked
# to join where a revision here is one the source holds or names.
def meets(+here: Receive.Side, +there: Receive.Side, hh: {Prune.sound(Receive.stored.of(here)) == True{} : Bool}, ht: {Prune.sound(Receive.stored.of(there)) == True{} : Bool}, +id: String, hi: {Rev.member(Main.ids(Receive.side.fulls(here)), id) == True{} : Bool}, hm: {Rev.member(List.append(&2, String, Main.ids(Receive.side.fulls(there)), List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named_by(f)), Receive.side.fulls(there)))), id) == True{} : Bool}) -> {Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.r(here, there, False{})) == True{} : Bool}:
  %Equal.sym(Bool, Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.r(here, there, False{})), Bool.or(False{}, related(Receive.side.fulls(here), Receive.side.fulls(there))), joins(here, there, False{}, hh, ht)) : {_ == True{} : Bool}
  related_meets(Receive.side.fulls(here), Receive.side.fulls(there), id, hi, hm)

# A string no member of `ys` matches is one they do not share.
def am_none(xs: List<&2, String>, +ys: List<&2, String>, +h: {List.all(~&2, ~String, ~(i => Bool.not(Rev.member(ys, i))), xs) == True{} : Bool}) -> {any_member(xs, ys) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      ArrangeL.or_ff(Rev.member(ys, x), any_member(rest, ys),
        ArrangeL.not_tt(Rev.member(ys, x), ArrangeL.and_tl(Bool.not(Rev.member(ys, x)), List.all(~&2, ~String, ~(i => Bool.not(Rev.member(ys, i))), rest), h)),
        am_none(rest, ys, ArrangeL.and_tr(Bool.not(Rev.member(ys, x)), List.all(~&2, ~String, ~(i => Bool.not(Rev.member(ys, i))), rest), h)))

def all_app_l(xs: List<&2, String>, +zs: List<&2, String>, +ys: List<&2, String>, +h: {List.all(~&2, ~String, ~(i => Bool.not(Rev.member(ys, i))), List.append(&2, String, xs, zs)) == True{} : Bool}) -> {List.all(~&2, ~String, ~(i => Bool.not(Rev.member(ys, i))), xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      B.and_tt(Bool.not(Rev.member(ys, x)), List.all(~&2, ~String, ~(i => Bool.not(Rev.member(ys, i))), rest), ArrangeL.and_tl(Bool.not(Rev.member(ys, x)), List.all(~&2, ~String, ~(i => Bool.not(Rev.member(ys, i))), List.append(&2, String, rest, zs)), h), all_app_l(rest, zs, ys, ArrangeL.and_tr(Bool.not(Rev.member(ys, x)), List.all(~&2, ~String, ~(i => Bool.not(Rev.member(ys, i))), List.append(&2, String, rest, zs)), h)))

def all_app_r(xs: List<&2, String>, +zs: List<&2, String>, +ys: List<&2, String>, +h: {List.all(~&2, ~String, ~(i => Bool.not(Rev.member(ys, i))), List.append(&2, String, xs, zs)) == True{} : Bool}) -> {List.all(~&2, ~String, ~(i => Bool.not(Rev.member(ys, i))), zs) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +x <> +rest:
      all_app_r(rest, zs, ys, ArrangeL.and_tr(Bool.not(Rev.member(ys, x)), List.all(~&2, ~String, ~(i => Bool.not(Rev.member(ys, i))), List.append(&2, String, rest, zs)), h))

# Revisions none of whose parents or supersedes is among `ys` name none.
def no_none(fs: List<&2, Main.Full>, +ys: List<&2, String>, +h: {List.all(~&2, ~String, ~(i => Bool.not(Rev.member(ys, i))), List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named_by(f)), fs))) == True{} : Bool}) -> {names_one(ys, fs) == False{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Main.Full{i, c, +parents, +supersedes, a, w, rb, rv, fa, m} <> +rest:
      +hl = all_app_l(List.append(&2, String, parents, supersedes), List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named_by(f)), rest)), ys, h)
      ArrangeL.or_ff(Bool.or(any_member(parents, ys), any_member(supersedes, ys)), names_one(ys, rest),
        ArrangeL.or_ff(any_member(parents, ys), any_member(supersedes, ys), am_none(parents, ys, all_app_l(parents, supersedes, ys, hl)), am_none(supersedes, ys, all_app_r(parents, supersedes, ys, hl))),
        no_none(rest, ys, all_app_r(List.append(&2, String, parents, supersedes), List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named_by(f)), rest)), ys, h)))

# Two nonempty histories sharing no revision, where no revision of either
# names one of the other's, are unrelated.
def unrelated(+ours: List<&2, Main.Full>, +theirs: List<&2, Main.Full>, no: {List.is_empty(&2, Main.Full, ours) == False{} : Bool}, nt: {List.is_empty(&2, Main.Full, theirs) == False{} : Bool}, hs: {List.all(~&2, ~String, ~(i => Bool.not(Rev.member(Main.ids(ours), i))), Main.ids(theirs)) == True{} : Bool}, eo: {List.all(~&2, ~String, ~(i => Bool.not(Rev.member(Main.ids(theirs), i))), List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named_by(f)), ours))) == True{} : Bool}, et: {List.all(~&2, ~String, ~(i => Bool.not(Rev.member(Main.ids(ours), i))), List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named_by(f)), theirs))) == True{} : Bool}) -> {related(ours, theirs) == False{} : Bool}:
  ArrangeL.or_ff(Bool.or(List.is_empty(&2, Main.Full, ours), List.is_empty(&2, Main.Full, theirs)), Bool.or(any_member(Main.ids(theirs), Main.ids(ours)), Bool.or(names_one(Main.ids(ours), theirs), names_one(Main.ids(theirs), ours))),
    ArrangeL.or_ff(List.is_empty(&2, Main.Full, ours), List.is_empty(&2, Main.Full, theirs), no, nt),
    ArrangeL.or_ff(any_member(Main.ids(theirs), Main.ids(ours)), Bool.or(names_one(Main.ids(ours), theirs), names_one(Main.ids(theirs), ours)), am_none(Main.ids(theirs), Main.ids(ours), hs),
      ArrangeL.or_ff(names_one(Main.ids(ours), theirs), names_one(Main.ids(theirs), ours), no_none(theirs, Main.ids(ours), et), no_none(ours, Main.ids(theirs), eo))))

# `receive` refuses two such stores, and plans between them when asked to
# join them.
def refuses(+here: Receive.Side, +there: Receive.Side, +hh: {Prune.sound(Receive.stored.of(here)) == True{} : Bool}, +ht: {Prune.sound(Receive.stored.of(there)) == True{} : Bool}, nh: {List.is_empty(&2, Main.Full, Receive.side.fulls(here)) == False{} : Bool}, nt: {List.is_empty(&2, Main.Full, Receive.side.fulls(there)) == False{} : Bool}, hs: {List.all(~&2, ~String, ~(i => Bool.not(Rev.member(Main.ids(Receive.side.fulls(here)), i))), Main.ids(Receive.side.fulls(there))) == True{} : Bool}, eh: {List.all(~&2, ~String, ~(i => Bool.not(Rev.member(Main.ids(Receive.side.fulls(there)), i))), List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named_by(f)), Receive.side.fulls(here)))) == True{} : Bool}, et: {List.all(~&2, ~String, ~(i => Bool.not(Rev.member(Main.ids(Receive.side.fulls(here)), i))), List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named_by(f)), Receive.side.fulls(there)))) == True{} : Bool}) -> {(Receive.plan.r(here, there, False{}), Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.r(here, there, True{}))) == (Fail{Main.Refused{1, "these nonempty stores share no revision or graph edge; use `--join-unrelated` only if combining two histories is intended"}}, True{}) : Result<&2, &2, Main.Refused, Receive.RPlan> & Bool}:
  %Equal.sym(Bool, Result.is_done(&2, &2, Main.Refused, Receive.RPlan, Receive.plan.r(here, there, True{})), Bool.or(True{}, related(Receive.side.fulls(here), Receive.side.fulls(there))), joins(here, there, True{}, hh, ht)) : {(Receive.plan.r(here, there, False{}), _) == (Fail{Main.Refused{1, "these nonempty stores share no revision or graph edge; use `--join-unrelated` only if combining two histories is intended"}}, True{}) : Result<&2, &2, Main.Refused, Receive.RPlan> & Bool}
  %Equal.sym(Bool, Prune.sound(Receive.stored.of(here)), True{}, hh) : {(Receive.plan.here(_, here, there, False{}), True{}) == (Fail{Main.Refused{1, "these nonempty stores share no revision or graph edge; use `--join-unrelated` only if combining two histories is intended"}}, True{}) : Result<&2, &2, Main.Refused, Receive.RPlan> & Bool}
  %Equal.sym(Bool, Prune.sound(Receive.stored.of(there)), True{}, ht) : {(Receive.plan.source(_, here, there, False{}), True{}) == (Fail{Main.Refused{1, "these nonempty stores share no revision or graph edge; use `--join-unrelated` only if combining two histories is intended"}}, True{}) : Result<&2, &2, Main.Refused, Receive.RPlan> & Bool}
  %Equal.sym(Bool, Receive.related(Receive.side.fulls(here), Receive.side.fulls(there)), related(Receive.side.fulls(here), Receive.side.fulls(there)), related_is(Receive.side.fulls(here), Receive.side.fulls(there))) : {(Receive.plan.related(_, here, there), True{}) == (Fail{Main.Refused{1, "these nonempty stores share no revision or graph edge; use `--join-unrelated` only if combining two histories is intended"}}, True{}) : Result<&2, &2, Main.Refused, Receive.RPlan> & Bool}
  %Equal.sym(Bool, related(Receive.side.fulls(here), Receive.side.fulls(there)), False{}, unrelated(Receive.side.fulls(here), Receive.side.fulls(there), nh, nt, hs, eh, et)) : {(Receive.plan.related(_, here, there), True{}) == (Fail{Main.Refused{1, "these nonempty stores share no revision or graph edge; use `--join-unrelated` only if combining two histories is intended"}}, True{}) : Result<&2, &2, Main.Refused, Receive.RPlan> & Bool}
  {==}
