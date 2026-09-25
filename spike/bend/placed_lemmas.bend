# What a folder an export lays out holds. The tree is taken path by path,
# each path once however many files claim it, in path order; so a folder
# laid out without a refusal holds every path the tree places, once each
# and in path order, and no other.
import Base
import ./export.bend as Export
import ./commands.bend as Main
import ./tree.bend as Tree
import ./revision.bend as Rev
import ./text.bend as T
import ./store.bend as Store
import ./prune.bend as Prune
import ./folder.bend as Folder
import ./ops.bend as Ops
import ./export_lemmas.bend as ExportL
import ./catchup_lemmas.bend as CatchL
import ./sort_lemmas.bend as SortL
import ./rewrite_lemmas.bend as RewriteL
import ./string_lemmas.bend as SL
import ./map_lemmas.bend as ML
import ./composition_lemmas.bend as Comp
import ./listed_lemmas.bend as ListedL

# The paths, each once
# --------------------

# Whether a list begins with a string.
def head.is(m: Maybe<&2, String>, +p: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      String.eq(x, p)

def push_step(b: Bool, +e: Tree.Entry, +path: String, +es: List<&2, Tree.Entry>, +rest: List<&2, Export.Placed>) -> {Export.placed.paths(Bool.pick(List<&2, Export.Placed>, b, Export.Placed{path, e <> es} <> rest, Export.Placed{Tree.entry_path(e), [e]} <> Export.Placed{path, es} <> rest)) == Main.distinct.keep(Tree.entry_path(e), path <> Export.placed.paths(rest), b) : List<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# A file joins the path in front where it is that path, and goes in front
# of it otherwise.
def pp_push(+e: Tree.Entry, ps: List<&2, Export.Placed>) -> {Export.placed.paths(Export.placed.push(e, ps)) == Main.distinct.keep(Tree.entry_path(e), Export.placed.paths(ps), head.is(List.head(&2, String, Export.placed.paths(ps)), Tree.entry_path(e))) : List<&2, String>}:
  match ps:
    case Export.Placed{+path, +es} <> +rest:
      push_step(String.eq(path, Tree.entry_path(e)), e, path, es, rest)
    case Nil{}:
      {==}

# `distinct` drops a string where the one after it is the same.
def dist_cons(+a: String, xs: List<&2, String>) -> {Main.distinct(a <> xs) == Main.distinct.keep(a, Main.distinct(xs), head.is(List.head(&2, String, Main.distinct(xs)), a)) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case +b <> +rest:
      %Equal.sym(Maybe<&2, String>, List.head(&2, String, Main.distinct(b <> rest)), List.head(&2, String, b <> rest), RewriteL.dist_head(b <> rest)) : {Main.distinct.keep(a, Main.distinct(b <> rest), String.eq(a, b)) == Main.distinct.keep(a, Main.distinct(b <> rest), head.is(_, a)) : List<&2, String>}
      %ML.eq_sym(a, b) : {Main.distinct.keep(a, Main.distinct(b <> rest), String.eq(a, b)) == Main.distinct.keep(a, Main.distinct(b <> rest), _) : List<&2, String>}
      {==}

# The tree by path is its paths, a run of one path taken once.
def pp_go(es: List<&2, Tree.Entry>) -> {Export.placed.paths(Export.placed.go(es)) == Main.distinct(Export.entry.paths(es)) : List<&2, String>}:
  match es:
    case Nil{}:
      {==}
    case Tree.Entry{+f, +p, +k, +y, +g, +m} <> +rest:
      Equal.trans(List<&2, String>, Export.placed.paths(Export.placed.push(Tree.Entry{f, p, k, y, g, m}, Export.placed.go(rest))), Main.distinct.keep(p, Export.placed.paths(Export.placed.go(rest)), head.is(List.head(&2, String, Export.placed.paths(Export.placed.go(rest))), p)), Main.distinct(p <> Export.entry.paths(rest)),
        pp_push(Tree.Entry{f, p, k, y, g, m}, Export.placed.go(rest)),
        (%Equal.sym(List<&2, String>, Export.placed.paths(Export.placed.go(rest)), Main.distinct(Export.entry.paths(rest)), pp_go(rest)) : {Main.distinct.keep(p, _, head.is(List.head(&2, String, _), p)) == Main.distinct(p <> Export.entry.paths(rest)) : List<&2, String>}
        Equal.sym(List<&2, String>, Main.distinct(p <> Export.entry.paths(rest)), Main.distinct.keep(p, Main.distinct(Export.entry.paths(rest)), head.is(List.head(&2, String, Main.distinct(Export.entry.paths(rest))), p)), dist_cons(p, Export.entry.paths(rest)))))

# In path order
# -------------

def entries_sorted(es: List<&2, Tree.Entry>, +k: String, +h: {SortL.sorted.from(~Tree.Entry, ~(e => Tree.entry_path(e)), es, k) == True{} : Bool}) -> {SortL.sorted.from(~String, ~(x => x), Export.entry.paths(es), k) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case Tree.Entry{+f, +p, +kd, +y, +g, +m} <> +rest:
      SortL.band_i(String.is_le(k, p), SortL.sorted.from(~String, ~(x => x), Export.entry.paths(rest), p),
        SortL.band_l(String.is_le(k, p), SortL.sorted.from(~Tree.Entry, ~(e => Tree.entry_path(e)), rest, p), h),
        entries_sorted(rest, p, SortL.band_r(String.is_le(k, p), SortL.sorted.from(~Tree.Entry, ~(e => Tree.entry_path(e)), rest, p), h)))

# The tree's paths, by path: each once, in path order.
def placed_rising(+t: Tree.Tree()) -> {Main.rising(Export.placed.paths(Export.placed(t))) == True{} : Bool}:
  +es = List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t)
  %Equal.sym(List<&2, String>, Export.placed.paths(Export.placed.go(es)), Main.distinct(Export.entry.paths(es)), pp_go(es)) : {Main.rising(_) == True{} : Bool}
  RewriteL.dist_rising(Export.entry.paths(es), SNil{}, entries_sorted(es, SNil{}, SortL.sort_sorted(~Tree.Entry, ~(e => Tree.entry_path(e)), t)))

# Every path the tree holds
# -------------------------

def or_dup(a: Bool, -b: Bool) -> {Bool.or(a, Bool.or(a, b)) == Bool.or(a, b) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def dm_keep(e: Bool, +a: String, +b: String, +rest: List<&2, String>, +x: String, ee: {String.eq(a, b) == e : Bool}, ih: {Rev.member(Main.distinct(b <> rest), x) == Rev.member(b <> rest, x) : Bool}) -> {Rev.member(Main.distinct.keep(a, Main.distinct(b <> rest), e), x) == Rev.member(a <> b <> rest, x) : Bool}:
  match e:
    case True{}:
      %Equal.sym(String, a, b, SL.eq_true(a, b, ee)) : {Rev.member(Main.distinct(b <> rest), x) == Bool.or(String.eq(_, x), Bool.or(String.eq(b, x), Rev.member(rest, x))) : Bool}
      Equal.trans(Bool, Rev.member(Main.distinct(b <> rest), x), Bool.or(String.eq(b, x), Rev.member(rest, x)), Bool.or(String.eq(b, x), Bool.or(String.eq(b, x), Rev.member(rest, x))), ih,
        Equal.sym(Bool, Bool.or(String.eq(b, x), Bool.or(String.eq(b, x), Rev.member(rest, x))), Bool.or(String.eq(b, x), Rev.member(rest, x)), or_dup(String.eq(b, x), Rev.member(rest, x))))
    case False{}:
      Equal.cong(Bool, Bool, v => Bool.or(String.eq(a, x), v), Rev.member(Main.distinct(b <> rest), x), Rev.member(b <> rest, x), ih)

# Dropping a string the same as the one after it keeps every string.
def dist_member(ys: List<&2, String>, +x: String) -> {Rev.member(Main.distinct(ys), x) == Rev.member(ys, x) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case a <> Nil{}:
      {==}
    case +a <> +b <> +rest:
      dm_keep(String.eq(a, b), a, b, rest, x, {==}, dist_member(b <> rest, x))

def paths_holds(t: Tree.Tree(), +x: String) -> {Rev.member(Export.entry.paths(t), x) == Export.tree.holds(t, x) : Bool}:
  match t:
    case Nil{}:
      {==}
    case Tree.Entry{+f, +p, +k, +y, +g, +m} <> +rest:
      %Equal.sym(Bool, Rev.member(Export.entry.paths(rest), x), Export.tree.holds(rest, x), paths_holds(rest, x)) : {Bool.or(String.eq(p, x), _) == Bool.or(String.eq(p, x), Export.tree.holds(rest, x)) : Bool}
      {==}

def some(es: List<&2, Tree.Entry>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case e <> rest:
      True{}

def hk_step(b: Bool, +e: Tree.Entry, +rest: List<&2, Tree.Entry>, +x: String, -h: Bool, ih: {h == some(SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), x, rest)) : Bool}) -> {Bool.or(b, h) == some(Bool.pick(List<&2, Tree.Entry>, b, e <> SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), x, rest), SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), x, rest))) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# A tree holds a path exactly where some of its files are at it.
def holds_keyed(es: List<&2, Tree.Entry>, +x: String) -> {Export.tree.holds(es, x) == some(SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), x, es)) : Bool}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      hk_step(String.eq(Tree.entry_path(e), x), e, rest, x, Export.tree.holds(rest, x), holds_keyed(rest, x))

# Sorted, a tree holds the paths it held.
def holds_sorted(+t: Tree.Tree(), +x: String) -> {Export.tree.holds(List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t), x) == Export.tree.holds(t, x) : Bool}:
  +es = List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t)
  Equal.trans(Bool, Export.tree.holds(es, x), some(SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), x, es)), Export.tree.holds(t, x), holds_keyed(es, x),
    (%Equal.sym(List<&2, Tree.Entry>, SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), x, es), SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), x, t), SortL.sort_keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), t, x)) : {some(_) == Export.tree.holds(t, x) : Bool}
    Equal.sym(Bool, Export.tree.holds(t, x), some(SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), x, t)), holds_keyed(t, x))))

# The tree by path names each path the tree holds, and no other.
def placed_member(+t: Tree.Tree(), +x: String) -> {Rev.member(Export.placed.paths(Export.placed(t)), x) == Export.tree.holds(t, x) : Bool}:
  +es = List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t)
  %Equal.sym(List<&2, String>, Export.placed.paths(Export.placed.go(es)), Main.distinct(Export.entry.paths(es)), pp_go(es)) : {Rev.member(_, x) == Export.tree.holds(t, x) : Bool}
  %Equal.sym(Bool, Rev.member(Main.distinct(Export.entry.paths(es)), x), Rev.member(Export.entry.paths(es), x), dist_member(Export.entry.paths(es), x)) : {_ == Export.tree.holds(t, x) : Bool}
  %Equal.sym(Bool, Rev.member(Export.entry.paths(es), x), Export.tree.holds(es, x), paths_holds(es, x)) : {_ == Export.tree.holds(t, x) : Bool}
  holds_sorted(t, x)

# The folder laid out
# -------------------

def app_nil_r(-A: Data, xs: List<&2, A>, -ys: List<&2, A>, e: {List.append(&2, A, xs, ys) == Nil{} : List<&2, A>}) -> {ys == Nil{} : List<&2, A>}:
  match xs:
    case Nil{}:
      e
    case x <> r:
      Empty.absurd({ys == Nil{} : List<&2, A>}, ExportL.cons_nil(A, x, List.append(&2, A, r, ys), e))

def done_or(r: Result<&2, &2, Main.Refused, List<&2, Export.Put>>, +d: List<&2, Export.Put>) -> List<&2, Export.Put>:
  match r:
    case Done{x}:
      x
    case Fail{e}:
      d

# A folder is laid out only where nothing is refused.
def laid_refused(+os: List<&2, Export.Outcome>, refused: List<&2, T.Split>, +qs: List<&2, Export.Put>, h: {Export.laid.r(os, refused) == Done{qs} : Result<&2, &2, Main.Refused, List<&2, Export.Put>>}) -> {refused == Nil{} : List<&2, T.Split>}:
  match refused:
    case Nil{}:
      {==}
    case +r <> +rest:
      Empty.absurd({r <> rest == Nil{} : List<&2, T.Split>}, Comp.false_true(Equal.cong(Result<&2, &2, Main.Refused, List<&2, Export.Put>>, Bool, x => Result.is_done(&2, &2, Main.Refused, List<&2, Export.Put>, x), Export.laid.r(os, r <> rest), Done{qs}, h)))

# And what it lays out is every file laid.
def laid_puts(+os: List<&2, Export.Outcome>, refused: List<&2, T.Split>, +qs: List<&2, Export.Put>, h: {Export.laid.r(os, refused) == Done{qs} : Result<&2, &2, Main.Refused, List<&2, Export.Put>>}) -> {Export.puts(os) == qs : List<&2, Export.Put>}:
  match refused:
    case Nil{}:
      Equal.cong(Result<&2, &2, Main.Refused, List<&2, Export.Put>>, List<&2, Export.Put>, x => done_or(x, qs), Export.laid.r(os, Nil{}), Done{qs}, h)
    case +r <> +rest:
      Empty.absurd({Export.puts(os) == qs : List<&2, Export.Put>}, Comp.false_true(Equal.cong(Result<&2, &2, Main.Refused, List<&2, Export.Put>>, Bool, x => Result.is_done(&2, &2, Main.Refused, List<&2, Export.Put>, x), Export.laid.r(os, r <> rest), Done{qs}, h)))

# A folder laid out holds the tree by path.
def done_paths(+t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>, +bs: List<&2, Prune.Body>, +rules: List<&2, Folder.Scope>, +qs: List<&2, Export.Put>, +h: {Export.folder.r(t, fs, ds, id, pays, bs, rules) == Done{qs} : Result<&2, &2, Main.Refused, List<&2, Export.Put>>}) -> {Export.put.paths(qs) == Export.placed.paths(Export.placed(t)) : List<&2, String>}:
  +ps = Export.placed(t)
  +os = Export.lay(ps, t, fs, ds, id, pays, bs)
  +rt = Export.refused.tree(ps, Set.from_list(Export.directories(ps)), rules)
  +refused = List.append(&2, T.Split, rt, Export.refused.laid(os))
  Equal.trans(List<&2, String>, Export.put.paths(qs), Export.put.paths(Export.puts(os)), Export.placed.paths(ps),
    Equal.cong(List<&2, Export.Put>, List<&2, String>, q => Export.put.paths(q), qs, Export.puts(os), Equal.sym(List<&2, Export.Put>, Export.puts(os), qs, laid_puts(os, refused, qs, h))),
    Equal.trans(List<&2, String>, Export.put.paths(Export.puts(os)), Export.outcome.paths(os), Export.placed.paths(ps),
      CatchL.puts_paths(os, app_nil_r(T.Split, rt, Export.refused.laid(os), laid_refused(os, refused, qs, h))),
      ExportL.laid(ps, t, fs, ds, id, pays, bs)))

# A folder laid out holds every path the tree places, once each, in path
# order, and no other.
def laid_out(+t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>, +bs: List<&2, Prune.Body>, +rules: List<&2, Folder.Scope>, +qs: List<&2, Export.Put>, +x: String, +h: {Export.folder.r(t, fs, ds, id, pays, bs, rules) == Done{qs} : Result<&2, &2, Main.Refused, List<&2, Export.Put>>}) -> {Bool.and(Main.rising(Export.put.paths(qs)), Export.bool.same(Rev.member(Export.put.paths(qs), x), Export.tree.holds(t, x))) == True{} : Bool}:
  +pp = Export.placed.paths(Export.placed(t))
  %Equal.sym(List<&2, String>, Export.put.paths(qs), pp, done_paths(t, fs, ds, id, pays, bs, rules, qs, h)) : {Bool.and(Main.rising(_), Export.bool.same(Rev.member(_, x), Export.tree.holds(t, x))) == True{} : Bool}
  ExportL.and_tt(Main.rising(pp), Export.bool.same(Rev.member(pp, x), Export.tree.holds(t, x)), placed_rising(t),
    (%Equal.sym(Bool, Rev.member(pp, x), Export.tree.holds(t, x), placed_member(t, x)) : {Export.bool.same(_, Export.tree.holds(t, x)) == True{} : Bool}
    ExportL.same_refl(Export.tree.holds(t, x))))

# Which paths are files
# ---------------------

def any.file(es: List<&2, Tree.Entry>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case Tree.Entry{f, p, k, y, g, m} <> rest:
      Bool.or(Bool.not(Tree.kind_eq(k, Tree.Link{})), any.file(rest))

def pl.file(p: Export.Placed, +x: String) -> Bool:
  match p:
    case Export.Placed{path, es}:
      Bool.and(String.eq(path, x), any.file(es))

def placed.file(ps: List<&2, Export.Placed>, +x: String) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> rest:
      Bool.or(pl.file(p, x), placed.file(rest, x))

def o.file(o: Export.Outcome, +x: String) -> Bool:
  match o:
    case Export.Outcome.Laid{+p}:
      Bool.and(String.eq(Export.put.path(p), x), Bool.not(Export.is.link(p)))
    case Export.Outcome.Refused{p, b}:
      False{}

def out.file(os: List<&2, Export.Outcome>, +x: String) -> Bool:
  match os:
    case Nil{}:
      False{}
    case o <> rest:
      Bool.or(o.file(o, x), out.file(rest, x))

def o.ok(o: Export.Outcome) -> Bool:
  match o:
    case Export.Outcome.Laid{p}:
      True{}
    case Export.Outcome.Refused{p, b}:
      False{}

def and_true(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def and_false(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# The paths of the files among what is laid, less its links.
def file_paths(os: List<&2, Export.Outcome>, +x: String) -> {Rev.member(Export.put.paths(Export.file.puts(Export.puts(os))), x) == out.file(os, x) : Bool}:
  match os:
    case Nil{}:
      {==}
    case o <> +rest:
      match o:
        case Export.Outcome.Refused{p, b}:
          file_paths(rest, x)
        case Export.Outcome.Laid{q}:
          match q:
            case Export.Put.Text{+path, tx, r}:
              %Equal.sym(Bool, Rev.member(Export.put.paths(Export.file.puts(Export.puts(rest))), x), out.file(rest, x), file_paths(rest, x)) : {Bool.or(String.eq(path, x), _) == Bool.or(Bool.and(String.eq(path, x), True{}), out.file(rest, x)) : Bool}
              %Equal.sym(Bool, Bool.and(String.eq(path, x), True{}), String.eq(path, x), and_true(String.eq(path, x))) : {Bool.or(String.eq(path, x), out.file(rest, x)) == Bool.or(_, out.file(rest, x)) : Bool}
              {==}
            case Export.Put.Bytes{+path, fr, d, r}:
              %Equal.sym(Bool, Rev.member(Export.put.paths(Export.file.puts(Export.puts(rest))), x), out.file(rest, x), file_paths(rest, x)) : {Bool.or(String.eq(path, x), _) == Bool.or(Bool.and(String.eq(path, x), True{}), out.file(rest, x)) : Bool}
              %Equal.sym(Bool, Bool.and(String.eq(path, x), True{}), String.eq(path, x), and_true(String.eq(path, x))) : {Bool.or(String.eq(path, x), out.file(rest, x)) == Bool.or(_, out.file(rest, x)) : Bool}
              {==}
            case Export.Put.Link{+path, g}:
              %Equal.sym(Bool, Bool.and(String.eq(path, x), False{}), False{}, and_false(String.eq(path, x))) : {Rev.member(Export.put.paths(Export.file.puts(Export.puts(rest))), x) == Bool.or(_, out.file(rest, x)) : Bool}
              file_paths(rest, x)

def not_ok(-g: Bool, h: {False{} == True{} : Bool}) -> {g == True{} : Bool}:
  Empty.absurd({g == True{} : Bool}, Comp.false_true(h))

def ref_file(+path: String, found: Maybe<&2, String>, +x: String, h: {o.ok(Export.lay.reference(path, found)) == True{} : Bool}) -> {o.file(Export.lay.reference(path, found), x) == Bool.and(String.eq(path, x), False{}) : Bool}:
  match found:
    case None{}:
      Empty.absurd({o.file(Export.lay.reference(path, None{}), x) == Bool.and(String.eq(path, x), False{}) : Bool}, Comp.false_true(h))
    case Some{to}:
      {==}

def link_file(+path: String, +t: Tree.Tree(), target: Maybe<&2, Tree.Target>, +x: String, h: {o.ok(Export.lay.link(path, t, target)) == True{} : Bool}) -> {o.file(Export.lay.link(path, t, target), x) == Bool.and(String.eq(path, x), False{}) : Bool}:
  match target:
    case None{}:
      Empty.absurd({o.file(Export.lay.link(path, t, None{}), x) == Bool.and(String.eq(path, x), False{}) : Bool}, Comp.false_true(h))
    case Some{Tree.Verbatim{s}}:
      {==}
    case Some{Tree.Reference{+f}}:
      ref_file(path, Tree.path(t, f), x, h)

def absent_file(+path: String, +d: String, forgotten: Bool, +x: String, h: {o.ok(Export.lay.absent(path, d, forgotten)) == True{} : Bool}) -> {o.file(Export.lay.absent(path, d, forgotten), x) == Bool.and(String.eq(path, x), True{}) : Bool}:
  match forgotten:
    case True{}:
      Empty.absurd({o.file(Export.lay.absent(path, d, True{}), x) == Bool.and(String.eq(path, x), True{}) : Bool}, Comp.false_true(h))
    case False{}:
      Empty.absurd({o.file(Export.lay.absent(path, d, False{}), x) == Bool.and(String.eq(path, x), True{}) : Bool}, Comp.false_true(h))

def held_file(+path: String, +d: String, found: Maybe<&2, String>, forgotten: Bool, r: Bool, +x: String, h: {o.ok(Export.lay.held(path, d, found, forgotten, r)) == True{} : Bool}) -> {o.file(Export.lay.held(path, d, found, forgotten, r), x) == Bool.and(String.eq(path, x), True{}) : Bool}:
  match found:
    case Some{from}:
      {==}
    case None{}:
      absent_file(path, d, forgotten, x, h)

def whole_file(+path: String, payload: Maybe<&2, String>, +ps: List<&2, T.Split>, +bs: List<&2, Prune.Body>, r: Bool, +x: String, h: {o.ok(Export.lay.whole(path, payload, ps, bs, r)) == True{} : Bool}) -> {o.file(Export.lay.whole(path, payload, ps, bs, r), x) == Bool.and(String.eq(path, x), True{}) : Bool}:
  match payload:
    case None{}:
      Empty.absurd({o.file(Export.lay.whole(path, None{}, ps, bs, r), x) == Bool.and(String.eq(path, x), True{}) : Bool}, Comp.false_true(h))
    case Some{+d}:
      held_file(path, d, Export.split.find(ps, d), Export.forgets(bs, d), r, x, h)

def lines_file(+path: String, content: Result<&2, &2, String, List<&2, Ops.Item>>, r: Bool, +x: String, h: {o.ok(Export.lay.lines(path, content, r)) == True{} : Bool}) -> {o.file(Export.lay.lines(path, content, r), x) == Bool.and(String.eq(path, x), True{}) : Bool}:
  match content:
    case Fail{e}:
      Empty.absurd({o.file(Export.lay.lines(path, Fail{e}, r), x) == Bool.and(String.eq(path, x), True{}) : Bool}, Comp.false_true(h))
    case Done{items}:
      {==}

def entry_file(+path: String, e: Tree.Entry, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>, +bs: List<&2, Prune.Body>, +x: String, h: {o.ok(Export.lay.entry(path, e, t, fs, ds, id, pays, bs)) == True{} : Bool}) -> {o.file(Export.lay.entry(path, e, t, fs, ds, id, pays, bs), x) == pl.file(Export.Placed{path, [e]}, x) : Bool}:
  match e:
    case Tree.Entry{+file, ep, kind, payload, target, mode}:
      match kind:
        case Tree.Link{}:
          link_file(path, t, target, x, h)
        case Tree.Whole{}:
          whole_file(path, payload, pays, bs, Export.runs(mode), x, h)
        case Tree.Lines{}:
          lines_file(path, Main.content(fs, ds, id, file), Export.runs(mode), x, h)

# A path laid out is a file exactly where the file claiming it is no link.
def one_file(p: Export.Placed, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>, +bs: List<&2, Prune.Body>, +x: String, h: {o.ok(Export.lay.one(p, t, fs, ds, id, pays, bs)) == True{} : Bool}) -> {o.file(Export.lay.one(p, t, fs, ds, id, pays, bs), x) == pl.file(p, x) : Bool}:
  match p:
    case Export.Placed{+path, es}:
      match es:
        case Nil{}:
          Empty.absurd({o.file(Export.lay.one(Export.Placed{path, Nil{}}, t, fs, ds, id, pays, bs), x) == pl.file(Export.Placed{path, Nil{}}, x) : Bool}, Comp.false_true(h))
        case e <> Nil{}:
          entry_file(path, e, t, fs, ds, id, pays, bs, x, h)
        case e <> f <> more:
          Empty.absurd({o.file(Export.lay.one(Export.Placed{path, e <> f <> more}, t, fs, ds, id, pays, bs), x) == pl.file(Export.Placed{path, e <> f <> more}, x) : Bool}, Comp.false_true(h))

def head_ok(o: Export.Outcome, -rest: List<&2, Export.Outcome>, h: {Export.refused.laid(o <> rest) == Nil{} : List<&2, T.Split>}) -> {o.ok(o) == True{} : Bool}:
  match o:
    case Export.Outcome.Laid{p}:
      {==}
    case Export.Outcome.Refused{p, b}:
      Empty.absurd({False{} == True{} : Bool}, ExportL.cons_nil(T.Split, T.Split{p, b}, Export.refused.laid(rest), h))

def tail_ok(o: Export.Outcome, -rest: List<&2, Export.Outcome>, h: {Export.refused.laid(o <> rest) == Nil{} : List<&2, T.Split>}) -> {Export.refused.laid(rest) == Nil{} : List<&2, T.Split>}:
  match o:
    case Export.Outcome.Laid{p}:
      h
    case Export.Outcome.Refused{p, b}:
      Empty.absurd({Export.refused.laid(rest) == Nil{} : List<&2, T.Split>}, ExportL.cons_nil(T.Split, T.Split{p, b}, Export.refused.laid(rest), h))

# Where nothing is refused, what is laid out is a file exactly where the
# file claiming the path is no link.
def laid_file(ps: List<&2, Export.Placed>, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>, +bs: List<&2, Prune.Body>, +x: String, +h: {Export.refused.laid(Export.lay(ps, t, fs, ds, id, pays, bs)) == Nil{} : List<&2, T.Split>}) -> {out.file(Export.lay(ps, t, fs, ds, id, pays, bs), x) == placed.file(ps, x) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +rest:
      +o = Export.lay.one(p, t, fs, ds, id, pays, bs)
      +os = Export.lay(rest, t, fs, ds, id, pays, bs)
      %Equal.sym(Bool, o.file(o, x), pl.file(p, x), one_file(p, t, fs, ds, id, pays, bs, x, head_ok(o, os, h))) : {Bool.or(_, out.file(os, x)) == Bool.or(pl.file(p, x), placed.file(rest, x)) : Bool}
      %Equal.sym(Bool, out.file(os, x), placed.file(rest, x), laid_file(rest, t, fs, ds, id, pays, bs, x, tail_ok(o, os, h))) : {Bool.or(pl.file(p, x), _) == Bool.or(pl.file(p, x), placed.file(rest, x)) : Bool}
      {==}

def or_nil_file(fe: Bool, +c: Bool, -z: Bool) -> {Bool.or(Bool.and(c, Bool.or(fe, False{})), z) == Bool.or(Bool.and(c, fe), z) : Bool}:
  match fe:
    case True{}:
      {==}
    case False{}:
      {==}

def or_join_file(c: Bool, fe: Bool, -a: Bool, -r: Bool) -> {Bool.or(Bool.and(c, Bool.or(fe, a)), r) == Bool.or(Bool.and(c, fe), Bool.or(Bool.and(c, a), r)) : Bool}:
  match c:
    case True{}:
      match fe:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

def push_file_step(b: Bool, +f: String, +p: String, +k: Tree.FileKind, +y: Maybe<&2, String>, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, +path: String, +es: List<&2, Tree.Entry>, +rest: List<&2, Export.Placed>, +x: String, eb: {String.eq(path, p) == b : Bool}) -> {placed.file(Bool.pick(List<&2, Export.Placed>, b, Export.Placed{path, Tree.Entry{f, p, k, y, g, m} <> es} <> rest, Export.Placed{p, [Tree.Entry{f, p, k, y, g, m}]} <> Export.Placed{path, es} <> rest), x) == Bool.or(Bool.and(String.eq(p, x), Bool.not(Tree.kind_eq(k, Tree.Link{}))), placed.file(Export.Placed{path, es} <> rest, x)) : Bool}:
  match b:
    case True{}:
      %SL.eq_true(path, p, eb) : {Bool.or(Bool.and(String.eq(path, x), Bool.or(Bool.not(Tree.kind_eq(k, Tree.Link{})), any.file(es))), placed.file(rest, x)) == Bool.or(Bool.and(String.eq(_, x), Bool.not(Tree.kind_eq(k, Tree.Link{}))), Bool.or(Bool.and(String.eq(path, x), any.file(es)), placed.file(rest, x))) : Bool}
      or_join_file(String.eq(path, x), Bool.not(Tree.kind_eq(k, Tree.Link{})), any.file(es), placed.file(rest, x))
    case False{}:
      or_nil_file(Bool.not(Tree.kind_eq(k, Tree.Link{})), String.eq(p, x), placed.file(Export.Placed{path, es} <> rest, x))

# A file joining the tree by path is a file there where it is no link.
def push_file(+f: String, +p: String, +k: Tree.FileKind, +y: Maybe<&2, String>, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, ps: List<&2, Export.Placed>, +x: String) -> {placed.file(Export.placed.push(Tree.Entry{f, p, k, y, g, m}, ps), x) == Bool.or(Bool.and(String.eq(p, x), Bool.not(Tree.kind_eq(k, Tree.Link{}))), placed.file(ps, x)) : Bool}:
  match ps:
    case Export.Placed{+path, +es} <> +rest:
      push_file_step(String.eq(path, p), f, p, k, y, g, m, path, es, rest, x, {==})
    case Nil{}:
      or_nil_file(Bool.not(Tree.kind_eq(k, Tree.Link{})), String.eq(p, x), False{})

# The tree by path has a file at a path exactly where the tree does.
def go_file(es: List<&2, Tree.Entry>, +x: String) -> {placed.file(Export.placed.go(es), x) == Export.tree.file(es, x) : Bool}:
  match es:
    case Nil{}:
      {==}
    case Tree.Entry{+f, +p, +k, +y, +g, +m} <> +rest:
      Equal.trans(Bool, placed.file(Export.placed.push(Tree.Entry{f, p, k, y, g, m}, Export.placed.go(rest)), x), Bool.or(Bool.and(String.eq(p, x), Bool.not(Tree.kind_eq(k, Tree.Link{}))), placed.file(Export.placed.go(rest), x)), Export.tree.file(Tree.Entry{f, p, k, y, g, m} <> rest, x),
        push_file(f, p, k, y, g, m, Export.placed.go(rest), x),
        Equal.cong(Bool, Bool, v => Bool.or(Bool.and(String.eq(p, x), Bool.not(Tree.kind_eq(k, Tree.Link{}))), v), placed.file(Export.placed.go(rest), x), Export.tree.file(rest, x), go_file(rest, x)))

def kf_step(b: Bool, +f: String, +p: String, +k: Tree.FileKind, +y: Maybe<&2, String>, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, +rest: List<&2, Tree.Entry>, +x: String, -h: Bool, ih: {h == any.file(SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), x, rest)) : Bool}) -> {Bool.or(Bool.and(b, Bool.not(Tree.kind_eq(k, Tree.Link{}))), h) == any.file(Bool.pick(List<&2, Tree.Entry>, b, Tree.Entry{f, p, k, y, g, m} <> SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), x, rest), SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), x, rest))) : Bool}:
  match b:
    case True{}:
      Equal.cong(Bool, Bool, v => Bool.or(Bool.not(Tree.kind_eq(k, Tree.Link{})), v), h, any.file(SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), x, rest)), ih)
    case False{}:
      ih

# A tree has a file at a path exactly where one of the files at it is no
# link.
def file_keyed(es: List<&2, Tree.Entry>, +x: String) -> {Export.tree.file(es, x) == any.file(SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), x, es)) : Bool}:
  match es:
    case Nil{}:
      {==}
    case Tree.Entry{+f, +p, +k, +y, +g, +m} <> +rest:
      kf_step(String.eq(p, x), f, p, k, y, g, m, rest, x, Export.tree.file(rest, x), file_keyed(rest, x))

# Sorted, a tree has the files it had.
def file_sorted(+t: Tree.Tree(), +x: String) -> {Export.tree.file(List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t), x) == Export.tree.file(t, x) : Bool}:
  +es = List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t)
  Equal.trans(Bool, Export.tree.file(es, x), any.file(SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), x, es)), Export.tree.file(t, x), file_keyed(es, x),
    (%Equal.sym(List<&2, Tree.Entry>, SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), x, es), SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), x, t), SortL.sort_keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), t, x)) : {any.file(_) == Export.tree.file(t, x) : Bool}
    Equal.sym(Bool, Export.tree.file(t, x), any.file(SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), x, t)), file_keyed(t, x))))

# The files, less the links, in path order
# ----------------------------------------

def ne_of(b: Bool, +k: String, +m: String, +y: String, eb: {String.eq(k, y) == b : Bool}, hkm: {String.is_le(k, m) == True{} : Bool}, nkm: {String.eq(k, m) == False{} : Bool}, hmy: {String.is_le(m, y) == True{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, Comp.false_true(Equal.trans(Bool, False{}, String.is_le(m, k), True{},
        Equal.sym(Bool, String.is_le(m, k), False{}, ListedL.le_ne(k, m, hkm, Equal.trans(Bool, String.eq(m, k), String.eq(k, m), False{}, ML.eq_sym(m, k), nkm))),
        (%Equal.sym(String, k, y, SL.eq_true(k, y, eb)) : {String.is_le(m, _) == True{} : Bool}
        hmy))))
    case False{}:
      {==}

def not_true(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Comp.false_true(e))
    case False{}:
      {==}

# Rising above a string, a list rises above any smaller one.
def rising_weaken(xs: List<&2, String>, +k: String, +m: String, +hkm: {String.is_le(k, m) == True{} : Bool}, +nkm: {String.eq(k, m) == False{} : Bool}, +h: {Main.rising.from(xs, m) == True{} : Bool}) -> {Main.rising.from(xs, k) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +r:
      +hl = SortL.band_l(Bool.and(String.is_le(m, y), Bool.not(String.eq(m, y))), Main.rising.from(r, y), h)
      +hmy = SortL.band_l(String.is_le(m, y), Bool.not(String.eq(m, y)), hl)
      ExportL.and_tt(Bool.and(String.is_le(k, y), Bool.not(String.eq(k, y))), Main.rising.from(r, y),
        ExportL.and_tt(String.is_le(k, y), Bool.not(String.eq(k, y)), SortL.str_le(k, m, y, hkm, hmy), ne_of(String.eq(k, y), k, m, y, {==}, hkm, nkm, hmy)),
        SortL.band_r(Bool.and(String.is_le(m, y), Bool.not(String.eq(m, y))), Main.rising.from(r, y), h))

def from_rising(xs: List<&2, String>, +k: String, h: {Main.rising.from(xs, k) == True{} : Bool}) -> {Main.rising(xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +r:
      SortL.band_r(Bool.and(String.is_le(k, y), Bool.not(String.eq(k, y))), Main.rising.from(r, y), h)

def files_from(qs: List<&2, Export.Put>, +k: String, +h: {Main.rising.from(Export.put.paths(qs), k) == True{} : Bool}) -> {Main.rising.from(Export.put.paths(Export.file.puts(qs)), k) == True{} : Bool}:
  match qs:
    case Nil{}:
      {==}
    case q <> +rest:
      match q:
        case Export.Put.Text{+path, tx, r}:
          ExportL.and_tt(Bool.and(String.is_le(k, path), Bool.not(String.eq(k, path))), Main.rising.from(Export.put.paths(Export.file.puts(rest)), path),
            SortL.band_l(Bool.and(String.is_le(k, path), Bool.not(String.eq(k, path))), Main.rising.from(Export.put.paths(rest), path), h),
            files_from(rest, path, SortL.band_r(Bool.and(String.is_le(k, path), Bool.not(String.eq(k, path))), Main.rising.from(Export.put.paths(rest), path), h)))
        case Export.Put.Bytes{+path, fr, d, r}:
          ExportL.and_tt(Bool.and(String.is_le(k, path), Bool.not(String.eq(k, path))), Main.rising.from(Export.put.paths(Export.file.puts(rest)), path),
            SortL.band_l(Bool.and(String.is_le(k, path), Bool.not(String.eq(k, path))), Main.rising.from(Export.put.paths(rest), path), h),
            files_from(rest, path, SortL.band_r(Bool.and(String.is_le(k, path), Bool.not(String.eq(k, path))), Main.rising.from(Export.put.paths(rest), path), h)))
        case Export.Put.Link{+path, g}:
          +hd = SortL.band_l(Bool.and(String.is_le(k, path), Bool.not(String.eq(k, path))), Main.rising.from(Export.put.paths(rest), path), h)
          rising_weaken(Export.put.paths(Export.file.puts(rest)), k, path, SortL.band_l(String.is_le(k, path), Bool.not(String.eq(k, path)), hd), not_true(String.eq(k, path), SortL.band_r(String.is_le(k, path), Bool.not(String.eq(k, path)), hd)),
            files_from(rest, path, SortL.band_r(Bool.and(String.is_le(k, path), Bool.not(String.eq(k, path))), Main.rising.from(Export.put.paths(rest), path), h)))

# The files of a folder, less its links, rise as the folder does.
def files_rising(qs: List<&2, Export.Put>, +h: {Main.rising(Export.put.paths(qs)) == True{} : Bool}) -> {Main.rising(Export.put.paths(Export.file.puts(qs))) == True{} : Bool}:
  match qs:
    case Nil{}:
      {==}
    case q <> +rest:
      match q:
        case Export.Put.Text{+path, tx, r}:
          files_from(rest, path, h)
        case Export.Put.Bytes{+path, fr, d, r}:
          files_from(rest, path, h)
        case Export.Put.Link{+path, g}:
          from_rising(Export.put.paths(Export.file.puts(rest)), path, files_from(rest, path, h))

# A folder laid out has, less its links, a file at every path where the
# target's tree holds a file that is no link, and at no other, each once
# and in path order.
def files_laid_out(+t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>, +bs: List<&2, Prune.Body>, +rules: List<&2, Folder.Scope>, +qs: List<&2, Export.Put>, +x: String, +h: {Export.folder.r(t, fs, ds, id, pays, bs, rules) == Done{qs} : Result<&2, &2, Main.Refused, List<&2, Export.Put>>}) -> {Bool.and(Main.rising(Export.put.paths(Export.file.puts(qs))), Export.bool.same(Rev.member(Export.put.paths(Export.file.puts(qs)), x), Export.tree.file(t, x))) == True{} : Bool}:
  +es = List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t)
  +ps = Export.placed(t)
  +os = Export.lay(ps, t, fs, ds, id, pays, bs)
  +rt = Export.refused.tree(ps, Set.from_list(Export.directories(ps)), rules)
  +refused = List.append(&2, T.Split, rt, Export.refused.laid(os))
  +hr = app_nil_r(T.Split, rt, Export.refused.laid(os), laid_refused(os, refused, qs, h))
  +fp = Export.put.paths(Export.file.puts(qs))
  +mem = Equal.trans(Bool, Rev.member(fp, x), out.file(os, x), Export.tree.file(t, x),
    (%laid_puts(os, refused, qs, h) : {Rev.member(Export.put.paths(Export.file.puts(_)), x) == out.file(os, x) : Bool}
    file_paths(os, x)),
    Equal.trans(Bool, out.file(os, x), placed.file(ps, x), Export.tree.file(t, x), laid_file(ps, t, fs, ds, id, pays, bs, x, hr),
      Equal.trans(Bool, placed.file(ps, x), Export.tree.file(es, x), Export.tree.file(t, x), go_file(es, x), file_sorted(t, x))))
  +ris = files_rising(qs, (%Equal.sym(List<&2, String>, Export.put.paths(qs), Export.placed.paths(ps), done_paths(t, fs, ds, id, pays, bs, rules, qs, h)) : {Main.rising(_) == True{} : Bool}
    placed_rising(t)))
  ExportL.and_tt(Main.rising(fp), Export.bool.same(Rev.member(fp, x), Export.tree.file(t, x)), ris,
    (%Equal.sym(Bool, Rev.member(fp, x), Export.tree.file(t, x), mem) : {Export.bool.same(_, Export.tree.file(t, x)) == True{} : Bool}
    ExportL.same_refl(Export.tree.file(t, x))))
