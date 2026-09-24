# `cat` and `show` read what the store holds: `cat` a file the target's tree
# holds that is not a link, `show` a document held under the digest named.
import Base
import ./main.bend as Main
import ./tree.bend as Tree
import ./revision.bend as Rev
import ./bookmark.bend as Bm
import ./store.bend as Store
import ./string_lemmas.bend as S
import ./fileat_lemmas.bend as FileAt
import ./blamed_lemmas.bend as B

# `cat`
# -----

def tdisc(m: Maybe<&2, Tree.Target>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def link_ok(+t: Tree.Tree(), +path: String, +file: String, m: Maybe<&2, Tree.Target>, +u: Unit, e: {Main.not_a_link.r(t, path, file, m) == Done{u} : Result<&2, &2, Main.Refused, Unit>}) -> {Maybe.is_none(&2, Tree.Target, m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{g}:
      Empty.absurd({Maybe.is_none(&2, Tree.Target, Some{g}) == True{} : Bool}, B.refuse(Unit, Main.not_a_link.r(t, path, file, Some{g}), u, {==}, e))

def ck_file(+fs: List<&2, Main.Full>, +id: String, +hm: {Rev.member(Main.ids(fs), id) == True{} : Bool}, +t: Tree.Tree(), +path: String, +file: String, +et: {Main.tree.r(fs, id) == Done{t} : Result<&2, &2, Main.Refused, Tree.Tree()>}, +hh: {Tree.holds(t, file) == True{} : Bool}, r: Result<&2, &2, Main.Refused, Unit>, +er: {Main.not_a_link.r(t, path, file, Tree.entry_target_of(Tree.lookup(t, file))) == r : Result<&2, &2, Main.Refused, Unit>}, +p: Main.Picked, e: {Result.bind(&2, &2, Main.Refused, Unit, Main.Picked, r, u => Done{Main.Picked{id, file}}) == Done{p} : Result<&2, &2, Main.Refused, Main.Picked>}) -> {Main.cat.ok(fs, p) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.cat.ok(fs, p) == True{} : Bool}, B.fail_done(Main.Picked, x, p, e))
    case Done{+u}:
      +d = B.done_eq(Main.Picked, Main.Picked{id, file}, p, e)
      %d : {Main.cat.ok(fs, _) == True{} : Bool}
      +es = Equal.sym(Result<&2, &2, Main.Refused, Tree.Tree()>, Main.tree.r(fs, id), Done{t}, et)
      %es : {Bool.and(Rev.member(Main.ids(fs), id), Main.tree.cat_ok(_, file)) == True{} : Bool}
      B.and_tt(Rev.member(Main.ids(fs), id), Bool.and(Tree.holds(t, file), Maybe.is_none(&2, Tree.Target, Tree.entry_target_of(Tree.lookup(t, file)))), hm,
        B.and_tt(Tree.holds(t, file), Maybe.is_none(&2, Tree.Target, Tree.entry_target_of(Tree.lookup(t, file))), hh, link_ok(t, path, file, Tree.entry_target_of(Tree.lookup(t, file)), u, er)))

def ck_tree(+fs: List<&2, Main.Full>, +id: String, +hm: {Rev.member(Main.ids(fs), id) == True{} : Bool}, +bs: List<&2, Bm.Bookmark>, +path: String, +t: Tree.Tree(), +et: {Main.tree.r(fs, id) == Done{t} : Result<&2, &2, Main.Refused, Tree.Tree()>}, r: Result<&2, &2, Main.Refused, String>, +er: {Main.file_in.r(id, bs, path, t) == r : Result<&2, &2, Main.Refused, String>}, +p: Main.Picked, e: {Result.bind(&2, &2, Main.Refused, String, Main.Picked, r, file => Main.cat.picked.file(t, path, id, file)) == Done{p} : Result<&2, &2, Main.Refused, Main.Picked>}) -> {Main.cat.ok(fs, p) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.cat.ok(fs, p) == True{} : Bool}, B.fail_done(Main.Picked, x, p, e))
    case Done{+file}:
      ck_file(fs, id, hm, t, path, file, et, FileAt.file_ok(id, bs, path, t, file, er), Main.not_a_link.r(t, path, file, Tree.entry_target_of(Tree.lookup(t, file))), {==}, p, e)

def ck_full(+fs: List<&2, Main.Full>, +id: String, +hm: {Rev.member(Main.ids(fs), id) == True{} : Bool}, +bs: List<&2, Bm.Bookmark>, +path: String, r: Result<&2, &2, Main.Refused, Tree.Tree()>, +er: {Main.tree.r(fs, id) == r : Result<&2, &2, Main.Refused, Tree.Tree()>}, +p: Main.Picked, e: {Result.bind(&2, &2, Main.Refused, Tree.Tree(), Main.Picked, r, t => Main.cat.picked.tree(bs, path, id, t)) == Done{p} : Result<&2, &2, Main.Refused, Main.Picked>}) -> {Main.cat.ok(fs, p) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.cat.ok(fs, p) == True{} : Bool}, B.fail_done(Main.Picked, x, p, e))
    case Done{+t}:
      ck_tree(fs, id, hm, bs, path, t, er, Main.file_in.r(id, bs, path, t), {==}, p, e)

def ck_r(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +target: String, +path: String, r: Result<&2, &2, Main.Refused, Main.Full>, +er: {Main.resolved.r(fs, bs, target) == r : Result<&2, &2, Main.Refused, Main.Full>}, +p: Main.Picked, e: {Result.bind(&2, &2, Main.Refused, Main.Full, Main.Picked, r, f => Main.cat.picked.full(fs, bs, path, Main.id_of(f))) == Done{p} : Result<&2, &2, Main.Refused, Main.Picked>}) -> {Main.cat.ok(fs, p) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.cat.ok(fs, p) == True{} : Bool}, B.fail_done(Main.Picked, x, p, e))
    case Done{+f}:
      ck_full(fs, Main.id_of(f), B.resolved_mem(fs, bs, target, f, er), bs, path, Main.tree.r(fs, Main.id_of(f)), {==}, p, e)

# `cat <target> <path>` reads a revision the store holds, and a file its tree
# holds that is not a link.
def cat_ok(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +target: String, +path: String, +p: Main.Picked, e: {Main.cat.picked.r(fs, bs, target, path) == Done{p} : Result<&2, &2, Main.Refused, Main.Picked>}) -> {Main.cat.ok(fs, p) == True{} : Bool}:
  ck_r(fs, bs, target, path, Main.resolved.r(fs, bs, target), {==}, p, e)

# `show`
# ------

def sdisc(m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def some_eq_s(-a: String, -b: String, h: {Some{a} == Some{b} : Maybe<&2, String>}) -> {a == b : String}:
  Equal.cong(Maybe<&2, String>, String, m => Maybe.default(&2, String, m, a), Some{a}, Some{b}, h)

def or_true(-x: Bool) -> {Bool.or(True{}, x) == True{} : Bool}:
  {==}

def by_id_at(b: Bool, +i: String, +d: String, +t: String, rest: List<&2, Store.Doc>, +text: String, e: {Bool.pick(Maybe<&2, String>, b, Some{t}, Main.doc_by_id(rest, d)) == Some{text} : Maybe<&2, String>}, ih: {Main.doc_by_id(rest, d) == Some{text} : Maybe<&2, String>} -> {Main.doc.holds(rest, d, text) == True{} : Bool}) -> {Bool.or(Bool.and(b, String.eq(t, text)), Main.doc.holds(rest, d, text)) == True{} : Bool}:
  match b:
    case True{}:
      +te = some_eq_s(t, text, e)
      %te : {Bool.or(String.eq(t, _), Main.doc.holds(rest, d, text)) == True{} : Bool}
      +r = Equal.sym(Bool, String.eq(t, t), True{}, S.eq_refl(t))
      %r : {Bool.or(_, Main.doc.holds(rest, d, text)) == True{} : Bool}
      {==}
    case False{}:
      ih(e)

# What `doc_by_id` finds is a document the store holds under that digest.
def by_id(ds: List<&2, Store.Doc>, +d: String, +text: String, e: {Main.doc_by_id(ds, d) == Some{text} : Maybe<&2, String>}) -> {Main.doc.holds(ds, d, text) == True{} : Bool}:
  match ds:
    case Nil{}:
      Empty.absurd({Main.doc.holds(Nil{}, d, text) == True{} : Bool}, (%e : {sdisc(_) : Type} Unit{}))
    case Store.Doc{p, +i, n, +t} <> +rest:
      by_id_at(String.starts_with(i, d), i, d, t, rest, text, e, h => by_id(rest, d, text, h))

def doc_r(+id: String, +d: String, m: Maybe<&2, String>, +ds: List<&2, Store.Doc>, +em: {Main.doc_by_id(ds, d) == m : Maybe<&2, String>}, +text: String, e: {Main.show.doc.r(id, d, m) == Done{text} : Result<&2, &2, Main.Refused, String>}) -> {Main.doc.holds(ds, d, text) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Main.doc.holds(ds, d, text) == True{} : Bool}, B.refuse(String, Main.show.doc.r(id, d, None{}), text, {==}, e))
    case Some{x}:
      +dx = B.done_eq(String, x, text, e)
      %dx : {Main.doc.holds(ds, d, _) == True{} : Bool}
      by_id(ds, d, x, em)

# `show` prints a document the store holds under the digest named.
def doc_ok(+id: String, +d: String, +ds: List<&2, Store.Doc>, +text: String, e: {Main.show.doc.r(id, d, Main.doc_by_id(ds, d)) == Done{text} : Result<&2, &2, Main.Refused, String>}) -> {Main.doc.holds(ds, d, text) == True{} : Bool}:
  doc_r(id, d, Main.doc_by_id(ds, d), ds, {==}, text, e)

def said_ok(+id: String, +file: String, +ds: List<&2, Store.Doc>, s: Main.Said, +text: String, e: {Main.show.said.r(id, file, ds, s) == Done{text} : Result<&2, &2, Main.Refused, String>}) -> {Main.doc.holds(ds, Main.said.digest(s), text) == True{} : Bool}:
  match s:
    case Main.Nothing{}:
      Empty.absurd({Main.doc.holds(ds, SNil{}, text) == True{} : Bool}, B.refuse(String, Main.show.said.r(id, file, ds, Main.Nothing{}), text, {==}, e))
    case Main.Whole{+d}:
      doc_ok(id, d, ds, text, e)
    case Main.Edited{+d}:
      doc_ok(id, d, ds, text, e)

def sf_bind(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +p: String, r: Result<&2, &2, Main.Refused, Tree.Tree()>, +er: {Main.tree.r(fs, id) == r : Result<&2, &2, Main.Refused, Tree.Tree()>}, +file: String, e: {Result.bind(&2, &2, Main.Refused, Tree.Tree(), String, r, t => Main.file_in.r(id, bs, p, t)) == Done{file} : Result<&2, &2, Main.Refused, String>}) -> {Main.tree.holds.r(Main.tree.r(fs, id), file) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.tree.holds.r(Main.tree.r(fs, id), file) == True{} : Bool}, B.fail_done(String, x, file, e))
    case Done{+t}:
      +es = Equal.sym(Result<&2, &2, Main.Refused, Tree.Tree()>, Main.tree.r(fs, id), Done{t}, er)
      %es : {Main.tree.holds.r(_, file) == True{} : Bool}
      FileAt.file_ok(id, bs, p, t, file, e)

# `show <target> <path>` names a file the target's tree holds.
def file_ok(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +p: String, +file: String, e: {Main.show.file.r(fs, bs, id, p) == Done{file} : Result<&2, &2, Main.Refused, String>}) -> {Main.tree.holds.r(Main.tree.r(fs, id), file) == True{} : Bool}:
  sf_bind(fs, bs, id, p, Main.tree.r(fs, id), {==}, file, e)
