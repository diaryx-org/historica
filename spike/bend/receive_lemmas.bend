# What `receive` plans. It takes only what this store lacks: revisions it
# does not hold, and documents and payloads it has nothing under the digest
# of and neither store forgets. It moves no bookmark this store has. The
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

# Taking what is lacking
# ----------------------

def keep_doc(c: Bool, +d: Store.Doc, +rest: List<&2, Store.Doc>, +have: Set(), ec: {Bool.not(Arrange.has(have, Store.id_of(d))) == c : Bool}, hr: {Receive.docs.fresh(rest, have) == True{} : Bool}) -> {Receive.docs.fresh(Receive.doc.keep(c, d, rest), have) == True{} : Bool}:
  match c:
    case True{}:
      B.and_tt(Bool.not(Arrange.has(have, Store.id_of(d))), Receive.docs.fresh(rest, have), ec, hr)
    case False{}:
      hr

# What `docs.lacking` keeps, this store has nothing under the digest of.
def docs_lacking(ds: List<&2, Store.Doc>, +have: Set()) -> {Receive.docs.fresh(Receive.docs.lacking(ds, have), have) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case +d <> +rest:
      keep_doc(Bool.not(Arrange.has(have, Store.id_of(d))), d, Receive.docs.lacking(rest, have), have, {==}, docs_lacking(rest, have))

def keep_split(c: Bool, +s: T.Split, +rest: List<&2, T.Split>, +have: Set(), ec: {Bool.not(Arrange.has(have, Receive.split.digest(s))) == c : Bool}, hr: {Receive.splits.fresh(rest, have) == True{} : Bool}) -> {Receive.splits.fresh(Tree.keep(~T.Split, c, s, rest), have) == True{} : Bool}:
  match c:
    case True{}:
      B.and_tt(Bool.not(Arrange.has(have, Receive.split.digest(s))), Receive.splits.fresh(rest, have), ec, hr)
    case False{}:
      hr

def splits_lacking(ss: List<&2, T.Split>, +have: Set()) -> {Receive.splits.fresh(Receive.splits.lacking(ss, have), have) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +rest:
      keep_split(Bool.not(Arrange.has(have, Receive.split.digest(s))), s, Receive.splits.lacking(rest, have), have, {==}, splits_lacking(rest, have))

# `receive` plans only what this store lacks.
def fresh(+here: Receive.Side, +there: Receive.Side) -> {Receive.fresh(here, there, Receive.plan.of(here, there)) == True{} : Bool}:
  B.and_tt(Receive.docs.fresh(Receive.docs.lacking(Receive.side.revisions(there), Receive.have.revisions(here)), Receive.have.revisions(here)),
    Bool.and(Receive.docs.fresh(Receive.docs.lacking(Receive.docs.distinct(Receive.stored.odocs(Receive.stored.of(there))), Receive.have.documents(here, there)), Receive.have.documents(here, there)), Receive.splits.fresh(Receive.splits.lacking(Receive.splits.distinct(Receive.stored.payloads(Receive.stored.of(there))), Receive.have.payloads(here, there)), Receive.have.payloads(here, there))),
    docs_lacking(Receive.side.revisions(there), Receive.have.revisions(here)),
    B.and_tt(Receive.docs.fresh(Receive.docs.lacking(Receive.docs.distinct(Receive.stored.odocs(Receive.stored.of(there))), Receive.have.documents(here, there)), Receive.have.documents(here, there)), Receive.splits.fresh(Receive.splits.lacking(Receive.splits.distinct(Receive.stored.payloads(Receive.stored.of(there))), Receive.have.payloads(here, there)), Receive.have.payloads(here, there)),
      docs_lacking(Receive.docs.distinct(Receive.stored.odocs(Receive.stored.of(there))), Receive.have.documents(here, there)),
      splits_lacking(Receive.splits.distinct(Receive.stored.payloads(Receive.stored.of(there))), Receive.have.payloads(here, there))))

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
