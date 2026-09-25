# What `export` promises of a copy. Its folder has every path the target's
# tree places, each once and at its own path, whatever the file is; every
# bookmark it is given is shared and finds what it names in the copy; and
# every rule file it is given states a shared rule.
import Base
import ./export.bend as Export
import ./receive.bend as Receive
import ./prune.bend as Prune
import ./prune_lemmas.bend as PruneL
import ./arrange.bend as Arrange
import ./commands.bend as Main
import ./store.bend as Store
import ./bookmark.bend as Bm
import ./text.bend as T
import ./tree.bend as Tree
import ./revision.bend as Rev
import ./ops.bend as Ops

# The folder
# ----------

def ref_path(+path: String, found: Maybe<&2, String>) -> {Export.outcome.path(Export.lay.reference(path, found)) == path : String}:
  match found:
    case None{}:
      {==}
    case Some{to}:
      {==}

def link_path(+path: String, +t: Tree.Tree(), target: Maybe<&2, Tree.Target>) -> {Export.outcome.path(Export.lay.link(path, t, target)) == path : String}:
  match target:
    case None{}:
      {==}
    case Some{Tree.Verbatim{s}}:
      {==}
    case Some{Tree.Reference{+f}}:
      ref_path(path, Tree.path(t, f))

def absent_path(+path: String, +d: String, forgotten: Bool) -> {Export.outcome.path(Export.lay.absent(path, d, forgotten)) == path : String}:
  match forgotten:
    case True{}:
      {==}
    case False{}:
      {==}

def held_path(+path: String, +d: String, found: Maybe<&2, String>, forgotten: Bool, r: Bool) -> {Export.outcome.path(Export.lay.held(path, d, found, forgotten, r)) == path : String}:
  match found:
    case Some{from}:
      {==}
    case None{}:
      absent_path(path, d, forgotten)

def whole_path(+path: String, payload: Maybe<&2, String>, +ps: List<&2, T.Split>, +bs: List<&2, Prune.Body>, r: Bool) -> {Export.outcome.path(Export.lay.whole(path, payload, ps, bs, r)) == path : String}:
  match payload:
    case None{}:
      {==}
    case Some{+d}:
      held_path(path, d, Export.split.find(ps, d), Export.forgets(bs, d), r)

def lines_path(+path: String, content: Result<&2, &2, String, List<&2, Ops.Item>>, r: Bool) -> {Export.outcome.path(Export.lay.lines(path, content, r)) == path : String}:
  match content:
    case Fail{e}:
      {==}
    case Done{items}:
      {==}

def entry_path(+path: String, e: Tree.Entry, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +ps: List<&2, T.Split>, +bs: List<&2, Prune.Body>) -> {Export.outcome.path(Export.lay.entry(path, e, t, fs, ds, id, ps, bs)) == path : String}:
  match e:
    case Tree.Entry{+file, p, kind, payload, target, mode}:
      match kind:
        case Tree.Link{}:
          link_path(path, t, target)
        case Tree.Whole{}:
          whole_path(path, payload, ps, bs, Export.runs(mode))
        case Tree.Lines{}:
          lines_path(path, Main.content(fs, ds, id, file), Export.runs(mode))

def one_path(p: Export.Placed, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +ps: List<&2, T.Split>, +bs: List<&2, Prune.Body>) -> {Export.outcome.path(Export.lay.one(p, t, fs, ds, id, ps, bs)) == Export.placed.path(p) : String}:
  match p:
    case Export.Placed{+path, es}:
      match es:
        case Nil{}:
          {==}
        case e <> Nil{}:
          entry_path(path, e, t, fs, ds, id, ps, bs)
        case e <> f <> more:
          {==}

# Every path placed gets one outcome, at that path, in order: a folder laid
# out without a refusal holds each path the tree places, and no other.
def laid(ps: List<&2, Export.Placed>, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>, +bs: List<&2, Prune.Body>) -> {Export.outcome.paths(Export.lay(ps, t, fs, ds, id, pays, bs)) == Export.placed.paths(ps) : List<&2, String>}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +rest:
      %Equal.sym(String, Export.outcome.path(Export.lay.one(p, t, fs, ds, id, pays, bs)), Export.placed.path(p), one_path(p, t, fs, ds, id, pays, bs)) : {_ <> Export.outcome.paths(Export.lay(rest, t, fs, ds, id, pays, bs)) == Export.placed.path(p) <> Export.placed.paths(rest) : List<&2, String>}
      %Equal.sym(List<&2, String>, Export.outcome.paths(Export.lay(rest, t, fs, ds, id, pays, bs)), Export.placed.paths(rest), laid(rest, t, fs, ds, id, pays, bs)) : {Export.placed.path(p) <> _ == Export.placed.path(p) <> Export.placed.paths(rest) : List<&2, String>}
      {==}

# Bookmarks
# ---------

def withheld_travels(t: Export.Travel, +pt: Export.Pointed, ih: {Export.travels(Export.travel.names(t), pt) == True{} : Bool}) -> {Export.travels(Export.travel.names(Export.travel.withheld(t)), pt) == True{} : Bool}:
  match t:
    case Export.Travel{ns, w, y}:
      ih

def held_travels(+n: String, +g: Bm.Target, +pt: Export.Pointed, h: Bool, e: {Export.pointed.holds(pt, g) == h : Bool}, t: Export.Travel, ih: {Export.travels(Export.travel.names(t), pt) == True{} : Bool}) -> {Export.travels(Export.travel.names(Export.travel.held(Bm.Bookmark{n, g, False{}}, h, t)), pt) == True{} : Bool}:
  match h:
    case True{}:
      match t:
        case Export.Travel{+ns, w, y}:
          %Equal.sym(Bool, Export.pointed.holds(pt, g), True{}, e) : {Bool.and(Bool.and(Bool.not(False{}), _), Export.travels(ns, pt)) == True{} : Bool}
          %Equal.sym(Bool, Export.travels(ns, pt), True{}, ih) : {Bool.and(Bool.and(Bool.not(False{}), True{}), _) == True{} : Bool}
          {==}
    case False{}:
      match t:
        case Export.Travel{ns, w, y}:
          ih

def push_travels(b: Bm.Bookmark, +pt: Export.Pointed, t: Export.Travel, ih: {Export.travels(Export.travel.names(t), pt) == True{} : Bool}) -> {Export.travels(Export.travel.names(Export.travel.push(b, pt, t)), pt) == True{} : Bool}:
  match b:
    case Bm.Bookmark{+n, +g, p}:
      match p:
        case True{}:
          withheld_travels(t, pt, ih)
        case False{}:
          held_travels(n, g, pt, Export.pointed.holds(pt, g), {==}, t, ih)

# Every bookmark the copy is given is shared, and finds what it names.
def names(bs: List<&2, Bm.Bookmark>, +pt: Export.Pointed) -> {Export.travels(Export.travel.names(Export.travel.of(bs, pt)), pt) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case b <> +rest:
      push_travels(b, pt, Export.travel.of(rest, pt), names(rest, pt))

# Rules
# -----

def all_shared(rs: List<&2, Receive.Ruled>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Receive.Ruled{f, +line, l} <> rest:
      Bool.and(Bool.not(String.starts_with(line, "private")), all_shared(rest))

def keep_shared(c: Bool, +f: String, +line: String, +l: String, rest: List<&2, Receive.Ruled>, ec: {String.starts_with(line, "private") == c : Bool}, ih: {all_shared(Export.rules.shared(rest)) == True{} : Bool}) -> {all_shared(Tree.keep(~Receive.Ruled, Bool.not(c), Receive.Ruled{f, line, l}, Export.rules.shared(rest))) == True{} : Bool}:
  match c:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, String.starts_with(line, "private"), False{}, ec) : {Bool.and(Bool.not(_), all_shared(Export.rules.shared(rest))) == True{} : Bool}
      ih

def shared_all(rs: List<&2, Receive.Ruled>) -> {all_shared(Export.rules.shared(rs)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Receive.Ruled{+f, +line, +l} <> +rest:
      keep_shared(String.starts_with(line, "private"), f, line, l, rest, {==}, shared_all(rest))

def written_step(dup: Bool, +chosen: String, +line: String, rest: List<&2, Receive.Ruled>, +existing: Set(), +done: List<&2, String>, +taken: List<&2, String>, hl: {Bool.not(String.starts_with(line, "private")) == True{} : Bool}, ih: {Export.lines.shared(Receive.rules.written(rest, existing, line <> done, Bool.pick(List<&2, String>, dup, taken, chosen <> taken))) == True{} : Bool}) -> {Export.lines.shared(Tree.keep(~T.Split, Bool.not(dup), T.Split{chosen, line}, Receive.rules.written(rest, existing, line <> done, Bool.pick(List<&2, String>, dup, taken, chosen <> taken)))) == True{} : Bool}:
  match dup:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, Bool.not(String.starts_with(line, "private")), True{}, hl) : {Bool.and(_, Export.lines.shared(Receive.rules.written(rest, existing, line <> done, chosen <> taken))) == True{} : Bool}
      ih

# What `rules.written` files states only what it was given: a list of
# shared rules comes out as files of shared rules, whatever labels it takes.
def written_shared(rs: List<&2, Receive.Ruled>, +existing: Set(), +done: List<&2, String>, +taken: List<&2, String>, +h: {all_shared(rs) == True{} : Bool}) -> {Export.lines.shared(Receive.rules.written(rs, existing, done, taken)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Receive.Ruled{f, +line, +label} <> +rest:
      +chosen = Bool.pick(String, Bool.or(Arrange.has(existing, label), Rev.member(taken, label)), Receive.rule.digest_label(line), label)
      written_step(Rev.member(done, line), chosen, line, rest, existing, done, taken,
        PruneL.and_l(Bool.not(String.starts_with(line, "private")), all_shared(rest), h),
        written_shared(rest, existing, line <> done, Bool.pick(List<&2, String>, Rev.member(done, line), taken, chosen <> taken), PruneL.and_r(Bool.not(String.starts_with(line, "private")), all_shared(rest), h)))

# Every rule file the copy is given states a shared rule.
def rules(+rs: List<&2, Receive.Ruled>) -> {Export.lines.shared(Export.rules.files(rs)) == True{} : Bool}:
  written_shared(Export.rules.shared(rs), Set.from_list(["README.txt"]), Nil{}, Nil{}, shared_all(rs))
