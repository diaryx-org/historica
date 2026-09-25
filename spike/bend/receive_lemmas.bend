# What `receive` plans. It takes only what this store lacks: revisions it
# does not hold, and documents and payloads it has nothing under the digest
# of and neither store forgets. It moves no bookmark this store has. And
# the originals it destroys are ones a forgetting document stands in for.
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

# What it plans from
# ------------------

def related_ok(c: Bool, +here: Receive.Side, +there: Receive.Side, +join: Bool, ea: {Prune.sound(Receive.stored.of(here)) == True{} : Bool}, eb: {Prune.sound(Receive.stored.of(there)) == True{} : Bool}, ec: {Bool.or(join, Receive.related(Receive.side.fulls(here), Receive.side.fulls(there))) == c : Bool}) -> {Receive.plan.ok(here, there, join, Receive.plan.related(c, here, there)) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, Prune.sound(Receive.stored.of(here)), True{}, ea) : {Bool.and(_, Bool.and(Prune.sound(Receive.stored.of(there)), Bool.or(join, Receive.related(Receive.side.fulls(here), Receive.side.fulls(there))))) == True{} : Bool}
      %Equal.sym(Bool, Prune.sound(Receive.stored.of(there)), True{}, eb) : {Bool.and(True{}, Bool.and(_, Bool.or(join, Receive.related(Receive.side.fulls(here), Receive.side.fulls(there))))) == True{} : Bool}
      ec
    case False{}:
      {==}

def source_ok(b: Bool, +here: Receive.Side, +there: Receive.Side, +join: Bool, ea: {Prune.sound(Receive.stored.of(here)) == True{} : Bool}, eb: {Prune.sound(Receive.stored.of(there)) == b : Bool}) -> {Receive.plan.ok(here, there, join, Receive.plan.source(b, here, there, join)) == True{} : Bool}:
  match b:
    case True{}:
      related_ok(Bool.or(join, Receive.related(Receive.side.fulls(here), Receive.side.fulls(there))), here, there, join, ea, eb, {==})
    case False{}:
      {==}

def here_ok(a: Bool, +here: Receive.Side, +there: Receive.Side, +join: Bool, ea: {Prune.sound(Receive.stored.of(here)) == a : Bool}) -> {Receive.plan.ok(here, there, join, Receive.plan.here(a, here, there, join)) == True{} : Bool}:
  match a:
    case True{}:
      source_ok(Prune.sound(Receive.stored.of(there)), here, there, join, ea, {==})
    case False{}:
      {==}

# Nothing is planned from a store the check calls broken, on either side,
# nor between two histories that share nothing, unless joining was asked.
def plan_ok(+here: Receive.Side, +there: Receive.Side, +join: Bool) -> {Receive.plan.ok(here, there, join, Receive.plan.r(here, there, join)) == True{} : Bool}:
  here_ok(Prune.sound(Receive.stored.of(here)), here, there, join, {==})

# The words
# ---------

def end_of(both: Bool, +dry: Bool, +fields: Bool, +join: Bool, source: Maybe<&2, String>, eb: {Bool.and(dry, fields) == both : Bool}) -> {Receive.args.ok(Receive.args.end.of(both, dry, fields, join, source)) == True{} : Bool}:
  match both:
    case True{}:
      {==}
    case False{}:
      match source:
        case None{}:
          {==}
        case Some{s}:
          %Equal.sym(Bool, Bool.and(dry, fields), False{}, eb) : {Bool.not(_) == True{} : Bool}
          {==}

def go_ok(ws: List<&2, String>, k: Receive.RWord, +dry: Bool, +fields: Bool, +join: Bool, +source: Maybe<&2, String>) -> {Receive.args.ok(Receive.args.go(ws, k, dry, fields, join, source)) == True{} : Bool}:
  match ws:
    case Nil{}:
      end_of(Bool.and(dry, fields), dry, fields, join, source, {==})
    case +w <> +rest:
      match k:
        case Receive.RWord.Dry{}:
          go_ok(rest, Receive.rword.of(rest), True{}, fields, join, source)
        case Receive.RWord.Fields{}:
          go_ok(rest, Receive.rword.of(rest), dry, True{}, join, source)
        case Receive.RWord.Join{}:
          go_ok(rest, Receive.rword.of(rest), dry, fields, True{}, source)
        case Receive.RWord.Flag{}:
          {==}
        case Receive.RWord.End{}:
          end_of(Bool.and(dry, fields), dry, fields, join, source, {==})
        case Receive.RWord.Plain{}:
          match source:
            case None{}:
              go_ok(rest, Receive.rword.of(rest), dry, fields, join, Some{w})
            case Some{s}:
              {==}

# `receive` never reads a command line as a plan and a statement at once.
def words(+ws: List<&2, String>) -> {Receive.args.ok(Receive.args.r(ws)) == True{} : Bool}:
  go_ok(ws, Receive.rword.of(ws), False{}, False{}, False{}, None{})
