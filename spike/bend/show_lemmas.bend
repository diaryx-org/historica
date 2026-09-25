# `cat` and `show` read what the store holds: `cat` a file the target's tree
# holds that is not a link, `show` a document held under the digest named.
import Base
import ./commands.bend as Main
import ./tree.bend as Tree
import ./revision.bend as Rev
import ./bookmark.bend as Bm
import ./store.bend as Store
import ./string_lemmas.bend as S
import ./fileat_lemmas.bend as FileAt
import ./blamed_lemmas.bend as B
import ./standin.bend as Stand
import ./ops.bend as Ops
import ./resolution.bend as Res

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

def rdisc2(r: Result<&2, &2, Main.Refused, String>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{t}:
      Empty

def fail_done2(-e: Main.Refused, -t: String, h: {Fail{e} == Done{t} : Result<&2, &2, Main.Refused, String>}) -> Empty:
  %h : {rdisc2(_) : Type}
  Unit{}

# Reading a document before printing it only refuses more: what `show`
# prints, the lookup under it found.
def read_done(bad: Maybe<&2, String>, r: Result<&2, &2, Main.Refused, String>, -text: String, e: {Main.show.read(bad, r) == Done{text} : Result<&2, &2, Main.Refused, String>}) -> {r == Done{text} : Result<&2, &2, Main.Refused, String>}:
  match bad r:
    case _ Fail{x}:
      e
    case None{} Done{t}:
      e
    case Some{m} Done{t}:
      Empty.absurd({Done{t} == Done{text} : Result<&2, &2, Main.Refused, String>}, fail_done2(Main.Refused{1, m}, text, e))

# What stands in for a destroyed document
# ----------------------------------------

def char_refl(h: Char) -> {Char.is_eq(h, h) == True{} : Bool}:
  match h:
    case Chr{U32{w}}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, S.word_refl(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# A string begins with itself, whatever follows it.
def starts_app(t: String, +x: String) -> {String.starts_with(t ++ x, t) == True{} : Bool}:
  match t:
    case SNil{}:
      match x:
        case SNil{}:
          {==}
        case SCon{h, r}:
          {==}
    case SCon{+h, tt}:
      %Equal.sym(Bool, Char.is_eq(h, h), True{}, char_refl(h)) : {String.starts_with.if(tt ++ x, tt, _) == True{} : Bool}
      starts_app(tt, x)

# And dropping as many characters as it has leaves what followed.
def drop_app(t: String, +x: String) -> {String.drop(t ++ x, String.length(t)) == x : String}:
  match t:
    case SNil{}:
      match x:
        case SNil{}:
          {==}
        case SCon{h, r}:
          {==}
    case SCon{h, tt}:
      drop_app(tt, x)

def or_r(a: Bool, -b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

# A document is only ever taken where its first header says it forgets the
# digest named.
def taken_says(says: Bool, stands: Bool, payload: Bool, seen: Bool, e: {Stand.kind.taken(Stand.kind.of(says, stands, payload), seen) == True{} : Bool}) -> {says == True{} : Bool}:
  match says:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(e))

def made_took(+t: String, +d: String, +y: String, rest: List<&2, Store.Doc>, hs: {Store.stands_for(t, [d]) == True{} : Bool}, ih: {Stand.made_of(rest, d, y) == True{} : Bool}) -> {Bool.and(Bool.and(Store.stands_for(t, [d]), String.starts_with(t ++ y, t)), Stand.made_of(rest, d, String.drop(t ++ y, String.length(t)))) == True{} : Bool}:
  %Equal.sym(Bool, Store.stands_for(t, [d]), True{}, hs) : {Bool.and(Bool.and(_, String.starts_with(t ++ y, t)), Stand.made_of(rest, d, String.drop(t ++ y, String.length(t)))) == True{} : Bool}
  %Equal.sym(Bool, String.starts_with(t ++ y, t), True{}, starts_app(t, y)) : {Bool.and(Bool.and(True{}, _), Stand.made_of(rest, d, String.drop(t ++ y, String.length(t)))) == True{} : Bool}
  %Equal.sym(String, String.drop(t ++ y, String.length(t)), y, drop_app(t, y)) : {Bool.and(True{}, Stand.made_of(rest, d, _)) == True{} : Bool}
  ih

def made_step(taken: Bool, +t: String, +d: String, +y: String, rest: List<&2, Store.Doc>, ht: {taken == True{} : Bool} -> {Store.stands_for(t, [d]) == True{} : Bool}, ih: {Stand.made_of(rest, d, y) == True{} : Bool}) -> {Stand.made_of(Store.Doc{SNil{}, SNil{}, 0n, t} <> rest, d, Bool.pick(String, taken, t, SNil{}) ++ y) == True{} : Bool}:
  match taken:
    case True{}:
      +h = made_took(t, d, y, rest, ht({==}), ih)
      %Equal.sym(Bool, Bool.and(Bool.and(Store.stands_for(t, [d]), String.starts_with(t ++ y, t)), Stand.made_of(rest, d, String.drop(t ++ y, String.length(t)))), True{}, h) : {Bool.or(_, Stand.made_of(rest, d, t ++ y)) == True{} : Bool}
      {==}
    case False{}:
      or_r(Bool.and(Bool.and(Store.stands_for(t, [d]), String.starts_with(y, t)), Stand.made_of(rest, d, String.drop(y, String.length(t)))), Stand.made_of(rest, d, y), ih)

def kind_says(+t: String, +d: String, +seen: Bool, e: {Stand.kind.taken(Stand.kind(t, d), seen) == True{} : Bool}) -> {Store.stands_for(t, [d]) == True{} : Bool}:
  taken_says(Store.stands_for(t, [d]), Bool.or(Stand.forgets.is(Stand.ops.forgets(Ops.parse(t)), d), Stand.forgets.is(Stand.res.forgets(Stand.res.parsed(t, Res.is_resolution(t))), d)), Stand.forgets.is(Stand.payload.forgets(Stand.payload.parse(t)), d), seen, e)

# Every document `show` prints for a digest it does not hold says it
# forgets that digest, and is printed whole, in the store's order.
def made_go(ds: List<&2, Store.Doc>, +d: String, +seen: Bool) -> {Stand.made_of(ds, d, Stand.shown.go(ds, d, seen)) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Store.Doc{p, i, n, +t} <> +rest:
      made_step(Stand.kind.taken(Stand.kind(t, d), seen), t, d, Stand.shown.go(rest, d, Stand.kind.seen(Stand.kind(t, d), seen)), rest, h => kind_says(t, d, seen, h), made_go(rest, d, Stand.kind.seen(Stand.kind(t, d), seen)))

def nonempty_some(s: String, -y: String, e: {Stand.nonempty(s) == Some{y} : Maybe<&2, String>}) -> {s == y : String}:
  match s:
    case SNil{}:
      Empty.absurd({SNil{} == y : String}, (%e : {sdisc(_) : Type} Unit{}))
    case SCon{c, r}:
      some_eq_s(SCon{c, r}, y, e)

def shown_none(+id: String, +d: String, +ds: List<&2, Store.Doc>, m: Maybe<&2, String>, +em: {Stand.nonempty(Stand.shown.go(ds, d, False{})) == m : Maybe<&2, String>}, +text: String, e: {Main.show.doc.r(id, d, m) == Done{text} : Result<&2, &2, Main.Refused, String>}) -> {Bool.or(Main.doc.holds(ds, d, text), Stand.made_of(ds, d, text)) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Bool.or(Main.doc.holds(ds, d, text), Stand.made_of(ds, d, text)) == True{} : Bool}, B.refuse(String, Main.show.doc.r(id, d, None{}), text, {==}, e))
    case Some{x}:
      +dx = B.done_eq(String, x, text, e)
      %dx : {Bool.or(Main.doc.holds(ds, d, _), Stand.made_of(ds, d, _)) == True{} : Bool}
      +hs = nonempty_some(Stand.shown.go(ds, d, False{}), x, em)
      %hs : {Bool.or(Main.doc.holds(ds, d, _), Stand.made_of(ds, d, _)) == True{} : Bool}
      or_r(Main.doc.holds(ds, d, Stand.shown.go(ds, d, False{})), Stand.made_of(ds, d, Stand.shown.go(ds, d, False{})), made_go(ds, d, False{}))

def shown_r(+id: String, +d: String, +ds: List<&2, Store.Doc>, m: Maybe<&2, String>, +em: {Stand.held(ds, d) == m : Maybe<&2, String>}, +text: String, e: {Main.show.doc.r(id, d, Stand.shown.of(ds, d, m)) == Done{text} : Result<&2, &2, Main.Refused, String>}) -> {Bool.or(Main.doc.holds(ds, d, text), Stand.made_of(ds, d, text)) == True{} : Bool}:
  match m:
    case Some{x}:
      +dx = B.done_eq(String, x, text, e)
      %dx : {Bool.or(Main.doc.holds(ds, d, _), Stand.made_of(ds, d, _)) == True{} : Bool}
      +h = by_id(ds, d, x, em)
      %Equal.sym(Bool, Main.doc.holds(ds, d, x), True{}, h) : {Bool.or(_, Stand.made_of(ds, d, x)) == True{} : Bool}
      {==}
    case None{}:
      shown_none(id, d, ds, Stand.nonempty(Stand.shown.go(ds, d, False{})), {==}, text, e)

def said_ok(+id: String, +file: String, +ds: List<&2, Store.Doc>, s: Main.Said, +text: String, e: {Main.show.said.r(id, file, ds, s) == Done{text} : Result<&2, &2, Main.Refused, String>}) -> {Bool.or(Main.doc.holds(ds, Main.said.digest(s), text), Stand.made_of(ds, Main.said.digest(s), text)) == True{} : Bool}:
  match s:
    case Main.Nothing{}:
      Empty.absurd({Bool.or(Main.doc.holds(ds, SNil{}, text), Stand.made_of(ds, SNil{}, text)) == True{} : Bool}, B.refuse(String, Main.show.said.r(id, file, ds, Main.Nothing{}), text, {==}, e))
    case Main.Whole{+d}:
      shown_r(id, d, ds, Stand.held(ds, d), {==}, text, e)
    case Main.Edited{+d}:
      shown_r(id, d, ds, Stand.held(ds, d), {==}, text, read_done(Main.unparsable.of(ds, d), Main.show.doc.r(id, d, Stand.shown(ds, d)), text, e))

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
