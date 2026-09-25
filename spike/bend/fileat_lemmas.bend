# A file argument names a file the revision holds. A path, `path:` and a
# path, `file:` and a file bookmark, or `file:` and an identifier's prefix:
# whichever an argument is read as, the file it names is one the tree holds.
import Base
import ./commands.bend as Main
import ./tree.bend as Tree
import ./revision.bend as Rev
import ./bookmark.bend as Bm
import ./text.bend as T
import ./ident.bend as Id
import ./string_lemmas.bend as S
import ./graph_lemmas.bend as GL
import ./target_lemmas.bend as TG

def rdisc(r: Result<&2, &2, Main.Refused, String>) -> Type:
  match r:
    case Done{x}:
      Empty
    case Fail{e}:
      Unit

def fail_done(-e: Main.Refused, -x: String, h: {Fail{e} == Done{x} : Result<&2, &2, Main.Refused, String>}) -> Empty:
  %h : {rdisc(_) : Type}
  Unit{}

def done_eq(-a: String, -b: String, h: {Done{a} == Done{b} : Result<&2, &2, Main.Refused, String>}) -> {a == b : String}:
  Equal.cong(Result<&2, &2, Main.Refused, String>, String, r => Result.default(&2, &2, Main.Refused, String, r, a), Done{a}, Done{b}, h)

def one_mem(+only: String, +f: String, e: {Done{only} == Done{f} : Result<&2, &2, Main.Refused, String>}) -> {Rev.member([only], f) == True{} : Bool}:
  GL.member_at([only], only, f, done_eq(only, f, e), GL.member_head(only, Nil{}))

# The tree
# --------

def mdisc(m: Maybe<&2, Tree.Entry>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def holds_of(m: Maybe<&2, Tree.Entry>, +p: String, e: {Maybe.map(&2, Tree.Entry, String, x => Tree.entry_path(x), m) == Some{p} : Maybe<&2, String>}) -> {Maybe.is_some(&2, Tree.Entry, m) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Maybe.is_some(&2, Tree.Entry, None{}) == True{} : Bool}, TG.none_some_s(p, e))
    case Some{x}:
      {==}

def lookup_hit(b: Bool, +en: Tree.Entry, rest: Tree.Tree(), +f: String, ih: {Maybe.is_some(&2, Tree.Entry, Tree.lookup(rest, f)) == True{} : Bool}) -> {Maybe.is_some(&2, Tree.Entry, Bool.pick(Maybe<&2, Tree.Entry>, b, Some{en}, Tree.lookup(rest, f))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def lookup_self(b: Bool, eb: {b == True{} : Bool}, +en: Tree.Entry, -rest: Maybe<&2, Tree.Entry>) -> {Maybe.is_some(&2, Tree.Entry, Bool.pick(Maybe<&2, Tree.Entry>, b, Some{en}, rest)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Maybe.is_some(&2, Tree.Entry, rest) == True{} : Bool}, S.false_true(eb))

# Every file the tree lists, it holds.
def files_holds(t: Tree.Tree(), +f: String, m: {Rev.member(Tree.files(t), f) == True{} : Bool}) -> {Tree.holds(t, f) == True{} : Bool}:
  match t:
    case Nil{}:
      Empty.absurd({Tree.holds(Nil{}, f) == True{} : Bool}, S.false_true(m))
    case Tree.Entry{+g, +p, +k, +y, +tg, +md} <> +rest:
      GL.member_cons({Tree.holds(Tree.Entry{g, p, k, y, tg, md} <> rest, f) == True{} : Bool}, g, Tree.files(rest), f, m,
        h => (%h : {Maybe.is_some(&2, Tree.Entry, Bool.pick(Maybe<&2, Tree.Entry>, String.eq(g, _), Some{Tree.Entry{g, p, k, y, tg, md}}, Tree.lookup(rest, _))) == True{} : Bool}
          lookup_self(String.eq(g, g), S.eq_refl(g), Tree.Entry{g, p, k, y, tg, md}, Tree.lookup(rest, g))),
        r => lookup_hit(String.eq(g, f), Tree.Entry{g, p, k, y, tg, md}, rest, f, files_holds(rest, f, r)))

# Every file at a path is one the tree lists.
def at_files(t: Tree.Tree(), +p: String, +f: String, m: {Rev.member(Tree.at(t, p), f) == True{} : Bool}) -> {Rev.member(Tree.files(t), f) == True{} : Bool}:
  match t:
    case Nil{}:
      m
    case Tree.Entry{+g, +q, k, y, tg, md} <> +rest:
      TG.keep_sub(String.eq(q, p), g, Tree.at(rest, p), Tree.files(rest), f, m, x => at_files(rest, p, f, x))

# The argument
# ------------

def is_fail(r: Result<&2, &2, Main.Refused, String>) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{x}:
      False{}

# A refusal is not an answer: computing that `r` fails refutes it.
def refuse(r: Result<&2, &2, Main.Refused, String>, -x: String, bad: {is_fail(r) == True{} : Bool}, e: {r == Done{x} : Result<&2, &2, Main.Refused, String>}) -> Empty:
  match r:
    case Fail{er}:
      fail_done(er, x, e)
    case Done{y}:
      S.false_true(bad)


def of_mem(+id: String, +path: String, found: List<&2, String>, +f: String, e: {Main.file_in.of.r(id, path, found) == Done{f} : Result<&2, &2, Main.Refused, String>}) -> {Rev.member(found, f) == True{} : Bool}:
  match found:
    case Nil{}:
      Empty.absurd({Rev.member(Nil{}, f) == True{} : Bool}, refuse(Main.file_in.of.r(id, path, Nil{}), f, {==}, e))
    case +only <> Nil{}:
      one_mem(only, f, e)
    case +x <> +y <> +r:
      Empty.absurd({Rev.member(x <> y <> r, f) == True{} : Bool}, refuse(Main.file_in.of.r(id, path, x <> y <> r), f, {==}, e))

def matched_mem(+id: String, +sp: String, +t: Tree.Tree(), found: List<&2, String>, +f: String, e: {Main.file_named.matched.r(id, sp, t, found) == Done{f} : Result<&2, &2, Main.Refused, String>}) -> {Rev.member(found, f) == True{} : Bool}:
  match found:
    case Nil{}:
      Empty.absurd({Rev.member(Nil{}, f) == True{} : Bool}, refuse(Main.file_named.matched.r(id, sp, t, Nil{}), f, {==}, e))
    case +only <> Nil{}:
      one_mem(only, f, e)
    case +x <> +y <> +r:
      Empty.absurd({Rev.member(x <> y <> r, f) == True{} : Bool}, refuse(Main.file_named.matched.r(id, sp, t, x <> y <> r), f, {==}, e))

def prefix_ok(+id: String, +sp: String, +t: Tree.Tree(), letters: Bool, +f: String, e: {Main.file_named.prefix.r(id, sp, t, letters) == Done{f} : Result<&2, &2, Main.Refused, String>}) -> {Tree.holds(t, f) == True{} : Bool}:
  match letters:
    case False{}:
      Empty.absurd({Tree.holds(t, f) == True{} : Bool}, refuse(Main.file_named.prefix.r(id, sp, t, False{}), f, {==}, e))
    case True{}:
      files_holds(t, f, TG.prefix_mem(Tree.files(t), sp, f, matched_mem(id, sp, t, Main.with_prefix(Tree.files(t), sp), f, e)))

def held_ok(+id: String, +sp: String, +file: String, +t: Tree.Tree(), at: Maybe<&2, String>, +f: String, ea: {Tree.path(t, file) == at : Maybe<&2, String>}, e: {Main.file_named.held.r(id, sp, file, at) == Done{f} : Result<&2, &2, Main.Refused, String>}) -> {Tree.holds(t, f) == True{} : Bool}:
  match at:
    case None{}:
      Empty.absurd({Tree.holds(t, f) == True{} : Bool}, refuse(Main.file_named.held.r(id, sp, file, None{}), f, {==}, e))
    case Some{+p}:
      (%done_eq(file, f, e) : {Tree.holds(t, _) == True{} : Bool}
        holds_of(Tree.lookup(t, file), p, ea))

def bookmark_ok(+id: String, +sp: String, +t: Tree.Tree(), target: Bm.Target, +f: String, e: {Main.file_named.bookmark.r(id, sp, t, target) == Done{f} : Result<&2, &2, Main.Refused, String>}) -> {Tree.holds(t, f) == True{} : Bool}:
  match target:
    case Bm.Target.File{+g}:
      held_ok(id, sp, g, t, Tree.path(t, g), f, {==}, e)
    case Bm.Target.Change{+c}:
      Empty.absurd({Tree.holds(t, f) == True{} : Bool}, refuse(Main.file_named.bookmark.r(id, sp, t, Bm.Target.Change{c}), f, {==}, e))
    case Bm.Target.Revision{+r}:
      Empty.absurd({Tree.holds(t, f) == True{} : Bool}, refuse(Main.file_named.bookmark.r(id, sp, t, Bm.Target.Revision{r}), f, {==}, e))

def found_ok(+id: String, +sp: String, +t: Tree.Tree(), found: Maybe<&2, Bm.Target>, +f: String, e: {Main.file_named.found.r(id, sp, t, found) == Done{f} : Result<&2, &2, Main.Refused, String>}) -> {Tree.holds(t, f) == True{} : Bool}:
  match found:
    case Some{target}:
      bookmark_ok(id, sp, t, target, f, e)
    case None{}:
      prefix_ok(id, sp, t, Main.all_chars(~(c => Id.is_letter(c)), sp), f, e)

def named_ok(+id: String, +bs: List<&2, Bm.Bookmark>, sp: String, +t: Tree.Tree(), +f: String, e: {Main.file_named.r(id, bs, sp, t) == Done{f} : Result<&2, &2, Main.Refused, String>}) -> {Tree.holds(t, f) == True{} : Bool}:
  match sp:
    case SNil{}:
      Empty.absurd({Tree.holds(t, f) == True{} : Bool}, refuse(Main.file_named.r(id, bs, SNil{}, t), f, {==}, e))
    case SCon{+c, +rest}:
      found_ok(id, SCon{c, rest}, t, Bm.find(bs, SCon{c, rest}), f, e)

def spelled_ok(+id: String, +bs: List<&2, Bm.Bookmark>, +path: String, +t: Tree.Tree(), named: Maybe<&2, String>, +f: String, e: {Main.file_in.spelled.r(id, bs, path, t, named) == Done{f} : Result<&2, &2, Main.Refused, String>}) -> {Tree.holds(t, f) == True{} : Bool}:
  match named:
    case Some{n}:
      named_ok(id, bs, n, t, f, e)
    case None{}:
      files_holds(t, f, at_files(t, Main.path.spelled(path), f, of_mem(id, Main.path.spelled(path), Tree.at(t, Main.path.spelled(path)), f, e)))

# Whatever an argument is read as, the file it names is one the tree holds.
def file_ok(+id: String, +bs: List<&2, Bm.Bookmark>, +path: String, +t: Tree.Tree(), +f: String, e: {Main.file_in.r(id, bs, path, t) == Done{f} : Result<&2, &2, Main.Refused, String>}) -> {Tree.holds(t, f) == True{} : Bool}:
  spelled_ok(id, bs, path, t, T.strip_prefix(path, "file:"), f, e)
