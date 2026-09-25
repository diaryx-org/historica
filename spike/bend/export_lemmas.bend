# What `export` promises of a copy. Its folder has every path the target's
# tree places, each once and at its own path, whatever the file is; every
# bookmark it is given is shared and finds what it names in the copy;
# every rule file it is given states a shared rule; and brought up to date,
# it writes over, removes and destroys only what some revision or
# forgetting document accounts for.
import Base
import ./export.bend as Export
import ./receive.bend as Receive
import ./composition_lemmas.bend as Comp
import ./offer.bend as Offer
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
import ./string_lemmas.bend as S
import ./folder.bend as Folder
import ./naming.bend as Naming
import ./receive_lemmas.bend as ReceiveL
import ./status_lemmas.bend as StatusL
import ./forget_lemmas.bend as ForgetL

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

def names_withheld(t: Export.Travel) -> {Export.travel.names(Export.travel.withheld(t)) == Export.travel.names(t) : List<&2, Bm.Bookmark>}:
  match t:
    case Export.Travel{ns, w, y}:
      {==}

def names_held(b: Bm.Bookmark, h: Bool, t: Export.Travel) -> {Export.travel.names(Export.travel.held(b, h, t)) == Tree.keep(~Bm.Bookmark, h, b, Export.travel.names(t)) : List<&2, Bm.Bookmark>}:
  match h t:
    case True{} Export.Travel{ns, w, y}:
      {==}
    case False{} Export.Travel{ns, w, y}:
      {==}

def or_false(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# A revision bookmark finds what the copy's revisions list.
def finds_revision(held: List<&2, Main.Full>, +r: String) -> {Rev.member(Main.ids(held), r) == Export.target.found(held, Bm.Target.Revision{r}) : Bool}:
  match held:
    case Nil{}:
      {==}
    case +f <> rest:
      Equal.cong(Bool, Bool, m => Bool.or(String.eq(Main.id_of(f), r), m), Rev.member(Main.ids(rest), r), Export.target.found(rest, Bm.Target.Revision{r}), finds_revision(rest, r))

# A change bookmark finds what the copy's changes list.
def finds_change(held: List<&2, Main.Full>, +c: String) -> {Rev.member(T.map(~Main.Full, ~String, ~(f => Main.change_of(f)), held), c) == Export.target.found(held, Bm.Target.Change{c}) : Bool}:
  match held:
    case Nil{}:
      {==}
    case +f <> rest:
      Equal.cong(Bool, Bool, m => Bool.or(String.eq(Main.change_of(f), c), m), Rev.member(T.map(~Main.Full, ~String, ~(f => Main.change_of(f)), rest), c), Export.target.found(rest, Bm.Target.Change{c}), finds_change(rest, c))

def says_one(c: Bool, fa: Tree.Fact, +l: List<&2, Tree.Fact>, +s: Bool, +x: String, ih: {Rev.member(Export.fact.files(l), x) == s : Bool}) -> {Rev.member(Export.fact.files(Tree.keep(~Tree.Fact, c, fa, l)), x) == Bool.or(Bool.and(c, Export.fact.names(fa, x)), s) : Bool}:
  match c fa:
    case True{} Tree.Fact{+f, r}:
      Equal.cong(Bool, Bool, m => Bool.or(String.eq(f, x), m), Rev.member(Export.fact.files(l), x), s, ih)
    case False{} Tree.Fact{f, r}:
      ih

# The files the facts of one kind name are the files a header of that kind
# says something of.
def says(hs: List<&2, Rev.Header>, +k: String, +x: String) -> {Rev.member(Export.fact.files(Tree.facts_of(hs, k)), x) == Export.fact.says(hs, k, x) : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Rev.Header{+key, +v} <> +rest:
      says_one(String.eq(key, k), Tree.fact_of(v, T.split_once(v)), Tree.facts_of(rest, k), Export.fact.says(rest, k, x), x, says(rest, k, x))

# One kind of fact in front of the rest of `touched`.
def said_step(+a: List<&2, String>, +z: List<&2, String>, +s: Bool, +cs: Bool, +fr: Bool, +x: String, ea: {Rev.member(a, x) == s : Bool}, ez: {Rev.member(z, x) == Bool.or(cs, fr) : Bool}) -> {Rev.member(List.append(&2, String, a, z), x) == Bool.or(Bool.or(s, cs), fr) : Bool}:
  Equal.trans(Bool, Rev.member(List.append(&2, String, a, z), x), Bool.or(s, Bool.or(cs, fr)), Bool.or(Bool.or(s, cs), fr),
    Equal.trans(Bool, Rev.member(List.append(&2, String, a, z), x), Bool.or(Rev.member(a, x), Rev.member(z, x)), Bool.or(s, Bool.or(cs, fr)), ReceiveL.member_app(a, z, x),
      Equal.trans(Bool, Bool.or(Rev.member(a, x), Rev.member(z, x)), Bool.or(s, Rev.member(z, x)), Bool.or(s, Bool.or(cs, fr)),
        Equal.cong(Bool, Bool, m => Bool.or(m, Rev.member(z, x)), Rev.member(a, x), s, ea),
        Equal.cong(Bool, Bool, m => Bool.or(s, m), Rev.member(z, x), Bool.or(cs, fr), ez))),
    ReceiveL.or_assoc(s, cs, fr))

# A file bookmark finds what some revision of the copy says anything of.
def finds_file(held: List<&2, Main.Full>, +x: String) -> {Rev.member(Export.touched(held), x) == Export.target.found(held, Bm.Target.File{x}) : Bool}:
  match held:
    case Nil{}:
      {==}
    case +f <> +rest:
      +hs = Main.facts_of(f)
      +fr = Export.target.found(rest, Bm.Target.File{x})
      +tail = List.append(&2, String, Export.touched(rest), Nil{})
      +et = Equal.trans(Bool, Rev.member(tail, x), Rev.member(Export.touched(rest), x), fr,
        Equal.trans(Bool, Rev.member(tail, x), Bool.or(Rev.member(Export.touched(rest), x), False{}), Rev.member(Export.touched(rest), x), ReceiveL.member_app(Export.touched(rest), Nil{}, x), or_false(Rev.member(Export.touched(rest), x))),
        finds_file(rest, x))
      +z6 = said_step(Export.fact.files(Tree.facts_of(hs, "bytes")), tail, Export.fact.says(hs, "bytes", x), False{}, fr, x, says(hs, "bytes", x), et)
      +z5 = said_step(Export.fact.files(Tree.facts_of(hs, "text")), List.append(&2, String, Export.fact.files(Tree.facts_of(hs, "bytes")), tail), Export.fact.says(hs, "text", x), Export.fact.said(["bytes"], hs, x), fr, x, says(hs, "text", x), z6)
      +z4 = said_step(Export.fact.files(Tree.facts_of(hs, "edit")), List.append(&2, String, Export.fact.files(Tree.facts_of(hs, "text")), List.append(&2, String, Export.fact.files(Tree.facts_of(hs, "bytes")), tail)), Export.fact.says(hs, "edit", x), Export.fact.said(["text", "bytes"], hs, x), fr, x, says(hs, "edit", x), z5)
      +z3 = said_step(Export.fact.files(Tree.facts_of(hs, "drop")), List.append(&2, String, Export.fact.files(Tree.facts_of(hs, "edit")), List.append(&2, String, Export.fact.files(Tree.facts_of(hs, "text")), List.append(&2, String, Export.fact.files(Tree.facts_of(hs, "bytes")), tail))), Export.fact.says(hs, "drop", x), Export.fact.said(["edit", "text", "bytes"], hs, x), fr, x, says(hs, "drop", x), z4)
      +z2 = said_step(Export.fact.files(Tree.facts_of(hs, "move")), List.append(&2, String, Export.fact.files(Tree.facts_of(hs, "drop")), List.append(&2, String, Export.fact.files(Tree.facts_of(hs, "edit")), List.append(&2, String, Export.fact.files(Tree.facts_of(hs, "text")), List.append(&2, String, Export.fact.files(Tree.facts_of(hs, "bytes")), tail)))), Export.fact.says(hs, "move", x), Export.fact.said(["drop", "edit", "text", "bytes"], hs, x), fr, x, says(hs, "move", x), z3)
      said_step(Export.fact.files(Tree.facts_of(hs, "add")), List.append(&2, String, Export.fact.files(Tree.facts_of(hs, "move")), List.append(&2, String, Export.fact.files(Tree.facts_of(hs, "drop")), List.append(&2, String, Export.fact.files(Tree.facts_of(hs, "edit")), List.append(&2, String, Export.fact.files(Tree.facts_of(hs, "text")), List.append(&2, String, Export.fact.files(Tree.facts_of(hs, "bytes")), tail))))), Export.fact.says(hs, "add", x), Export.fact.said(["move", "drop", "edit", "text", "bytes"], hs, x), fr, x, says(hs, "add", x), z2)

# The export's hold test, over the revisions the copy is given, is what
# those revisions find.
def holds_over(+held: List<&2, Main.Full>, g: Bm.Target) -> {Export.pointed.holds(Export.pointed.over(held), g) == Export.target.found(held, g) : Bool}:
  match g:
    case Bm.Target.Revision{+r}:
      finds_revision(held, r)
    case Bm.Target.Change{+c}:
      finds_change(held, c)
    case Bm.Target.File{+x}:
      finds_file(held, x)

# The bookmarks the copy is given are the shared ones, as `offer` lists
# them, that find something among the revisions it is given, in order.
def names(bs: List<&2, Bm.Bookmark>, +held: List<&2, Main.Full>) -> {Export.travel.names(Export.travel.of(bs, Export.pointed.over(held))) == Export.marks.found(Offer.shared(bs), held) : List<&2, Bm.Bookmark>}:
  match bs:
    case Nil{}:
      {==}
    case Bm.Bookmark{+n, +g, p} <> +rest:
      match p:
        case True{}:
          +pt = Export.pointed.over(held)
          Equal.trans(List<&2, Bm.Bookmark>, Export.travel.names(Export.travel.withheld(Export.travel.of(rest, pt))), Export.travel.names(Export.travel.of(rest, pt)), Export.marks.found(Offer.shared(rest), held), names_withheld(Export.travel.of(rest, pt)), names(rest, held))
        case False{}:
          +pt = Export.pointed.over(held)
          Equal.trans(List<&2, Bm.Bookmark>, Export.travel.names(Export.travel.held(Bm.Bookmark{n, g, False{}}, Export.pointed.holds(pt, g), Export.travel.of(rest, pt))), Tree.keep(~Bm.Bookmark, Export.pointed.holds(pt, g), Bm.Bookmark{n, g, False{}}, Export.travel.names(Export.travel.of(rest, pt))), Tree.keep(~Bm.Bookmark, Export.target.found(held, g), Bm.Bookmark{n, g, False{}}, Export.marks.found(Offer.shared(rest), held)),
            names_held(Bm.Bookmark{n, g, False{}}, Export.pointed.holds(pt, g), Export.travel.of(rest, pt)),
            Equal.trans(List<&2, Bm.Bookmark>, Tree.keep(~Bm.Bookmark, Export.pointed.holds(pt, g), Bm.Bookmark{n, g, False{}}, Export.travel.names(Export.travel.of(rest, pt))), Tree.keep(~Bm.Bookmark, Export.target.found(held, g), Bm.Bookmark{n, g, False{}}, Export.travel.names(Export.travel.of(rest, pt))), Tree.keep(~Bm.Bookmark, Export.target.found(held, g), Bm.Bookmark{n, g, False{}}, Export.marks.found(Offer.shared(rest), held)),
              Equal.cong(Bool, List<&2, Bm.Bookmark>, c => Tree.keep(~Bm.Bookmark, c, Bm.Bookmark{n, g, False{}}, Export.travel.names(Export.travel.of(rest, pt))), Export.pointed.holds(pt, g), Export.target.found(held, g), holds_over(held, g)),
              Equal.cong(List<&2, Bm.Bookmark>, List<&2, Bm.Bookmark>, l => Tree.keep(~Bm.Bookmark, Export.target.found(held, g), Bm.Bookmark{n, g, False{}}, l), Export.travel.names(Export.travel.of(rest, pt)), Export.marks.found(Offer.shared(rest), held), names(rest, held))))

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

# Catching a folder up
# --------------------

def and_tt(a: Bool, b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, S.false_true(ea))

def or_r(a: Bool, -b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

# What `recorded` finds by looking the path up is held by some record of
# that path.
def rec_step(c: Bool, +p: String, +ds: List<&2, String>, +ls: List<&2, String>, -rest: List<&2, Export.Rec>, +path: String, +d: String, h: {Rev.member(Export.rec.digests(Bool.pick(Maybe<&2, Export.Rec>, c, Some{Export.Rec{p, ds, ls}}, Export.rec.find(rest, path))), d) == True{} : Bool}, ih: {Rev.member(Export.rec.digests(Export.rec.find(rest, path)), d) == True{} : Bool} -> {Export.recs.hold(rest, path, d) == True{} : Bool}) -> {Bool.or(Bool.and(c, Rev.member(ds, d)), Export.recs.hold(rest, path, d)) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, Rev.member(ds, d), True{}, h) : {Bool.or(_, Export.recs.hold(rest, path, d)) == True{} : Bool}
      {==}
    case False{}:
      or_r(False{}, Export.recs.hold(rest, path, d), ih(h))

def rec_find(rs: List<&2, Export.Rec>, +path: String, +d: String, h: {Rev.member(Export.rec.digests(Export.rec.find(rs, path)), d) == True{} : Bool}) -> {Export.recs.hold(rs, path, d) == True{} : Bool}:
  match rs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(h))
    case Export.Rec{+p, +ds, +ls} <> +rest:
      rec_step(String.eq(p, path), p, ds, ls, rest, path, d, h, x => rec_find(rest, path, d, x))

def rec_hold(whole: Bool, +rs: List<&2, Export.Rec>, +path: String, +d: String, h: {Export.recorded(whole, rs, path, d) == True{} : Bool}) -> {Bool.or(whole, Export.recs.hold(rs, path, d)) == True{} : Bool}:
  match whole:
    case True{}:
      {==}
    case False{}:
      rec_find(rs, path, d, h)

def lnk_step(c: Bool, +p: String, +ds: List<&2, String>, +ls: List<&2, String>, -rest: List<&2, Export.Rec>, +path: String, +t: String, h: {Rev.member(Export.rec.links(Bool.pick(Maybe<&2, Export.Rec>, c, Some{Export.Rec{p, ds, ls}}, Export.rec.find(rest, path))), t) == True{} : Bool}, ih: {Rev.member(Export.rec.links(Export.rec.find(rest, path)), t) == True{} : Bool} -> {Export.recs.link(rest, path, t) == True{} : Bool}) -> {Bool.or(Bool.and(c, Rev.member(ls, t)), Export.recs.link(rest, path, t)) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, Rev.member(ls, t), True{}, h) : {Bool.or(_, Export.recs.link(rest, path, t)) == True{} : Bool}
      {==}
    case False{}:
      or_r(False{}, Export.recs.link(rest, path, t), ih(h))

def lnk_find(rs: List<&2, Export.Rec>, +path: String, +t: String, h: {Rev.member(Export.rec.links(Export.rec.find(rs, path)), t) == True{} : Bool}) -> {Export.recs.link(rs, path, t) == True{} : Bool}:
  match rs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(h))
    case Export.Rec{+p, +ds, +ls} <> +rest:
      lnk_step(String.eq(p, path), p, ds, ls, rest, path, t, h, x => lnk_find(rest, path, t, x))

def lnk_hold(whole: Bool, +rs: List<&2, Export.Rec>, +path: String, +t: String, h: {Export.recorded.link(whole, rs, path, t) == True{} : Bool}) -> {Bool.or(whole, Export.recs.link(rs, path, t)) == True{} : Bool}:
  match whole:
    case True{}:
      {==}
    case False{}:
      lnk_find(rs, path, t, h)

# What the walk found that `removes` counts as gone is what a record holds.
def gone_recorded(s: Export.Seen, +whole: Bool, +rs: List<&2, Export.Rec>, h: {Export.seen.gone(s, whole, rs) == True{} : Bool}) -> {Export.seen.recorded(s, whole, rs) == True{} : Bool}:
  match s:
    case Export.Seen.File{+p, +d, r}:
      rec_hold(whole, rs, p, d, h)
    case Export.Seen.Link{+p, +t}:
      lnk_hold(whole, rs, p, t, h)

# A write or a link at a path lands where what the walk found there is
# what `s` is.
def over_at(+put: Export.Put, +path: String, -s: Maybe<&2, Export.Seen>, +ss: List<&2, Export.Seen>, +whole: Bool, +rs: List<&2, Export.Rec>, ep: {Export.put.path(put) == path : String}, es: {Export.seen.find(ss, path) == s : Maybe<&2, Export.Seen>}, h: {Export.over.ok(whole, rs, path, Export.held.digest(s)) == True{} : Bool}) -> {Export.over.ok(whole, rs, Export.put.path(put), Export.held.digest(Export.seen.find(ss, Export.put.path(put)))) == True{} : Bool}:
  %Equal.sym(String, Export.put.path(put), path, ep) : {Export.over.ok(whole, rs, _, Export.held.digest(Export.seen.find(ss, _))) == True{} : Bool}
  %Equal.sym(Maybe<&2, Export.Seen>, Export.seen.find(ss, path), s, es) : {Export.over.ok(whole, rs, path, Export.held.digest(_)) == True{} : Bool}
  h

# Over a file whose bytes some revision records, and nowhere else.
def over_file(r: Bool, link: Bool, +put: Export.Put, +path: String, +p: String, +d: String, +runs: Bool, +ss: List<&2, Export.Seen>, +whole: Bool, +rs: List<&2, Export.Rec>, er: {Export.recorded(whole, rs, path, d) == r : Bool}, ep: {Export.put.path(put) == path : String}, es: {Export.seen.find(ss, path) == Some{Export.Seen.File{p, d, runs}} : Maybe<&2, Export.Seen>}) -> {Export.step.safe(Bool.pick(Export.Step, r, Bool.pick(Export.Step, link, Export.Step.Link{put}, Export.Step.Write{put, True{}}), Export.Step.Refuse{path, Export.UNRECORDED()}), ss, whole, rs) == True{} : Bool}:
  match r:
    case True{}:
      match link:
        case True{}:
          over_at(put, path, Some{Export.Seen.File{p, d, runs}}, ss, whole, rs, ep, es, rec_hold(whole, rs, path, d, er))
        case False{}:
          over_at(put, path, Some{Export.Seen.File{p, d, runs}}, ss, whole, rs, ep, es, rec_hold(whole, rs, path, d, er))
    case False{}:
      {==}

# Keeping, or setting a mode, writes nothing over.
def same_safe(eq: Bool, runs: Bool, wanted: Bool, +path: String, +over: Export.Step, +ss: List<&2, Export.Seen>, +whole: Bool, +rs: List<&2, Export.Rec>, ho: {Export.step.safe(over, ss, whole, rs) == True{} : Bool}) -> {Export.step.safe(Export.step.same(path, eq, runs, wanted, over), ss, whole, rs) == True{} : Bool}:
  match eq:
    case True{}:
      match runs wanted:
        case True{} True{}:
          {==}
        case True{} False{}:
          {==}
        case False{} True{}:
          {==}
        case False{} False{}:
          {==}
    case False{}:
      ho

def link_same(q: Bool, +put: Export.Put, +path: String, +p: String, +t: String, +ss: List<&2, Export.Seen>, +whole: Bool, +rs: List<&2, Export.Rec>, ep: {Export.put.path(put) == path : String}, es: {Export.seen.find(ss, path) == Some{Export.Seen.Link{p, t}} : Maybe<&2, Export.Seen>}) -> {Export.step.safe(Bool.pick(Export.Step, q, Export.Step.Keep{}, Export.Step.Link{put}), ss, whole, rs) == True{} : Bool}:
  match q:
    case True{}:
      {==}
    case False{}:
      over_at(put, path, Some{Export.Seen.Link{p, t}}, ss, whole, rs, ep, es, {==})

def absent_safe(pr: Export.Probe, link: Bool, +put: Export.Put, +path: String, +ss: List<&2, Export.Seen>, +whole: Bool, +rs: List<&2, Export.Rec>, ep: {Export.put.path(put) == path : String}, es: {Export.seen.find(ss, path) == None{} : Maybe<&2, Export.Seen>}) -> {Export.step.safe(Export.step.absent(put, path, pr, link), ss, whole, rs) == True{} : Bool}:
  match pr link:
    case Export.Probe.Nothing{} True{}:
      over_at(put, path, None{}, ss, whole, rs, ep, es, {==})
    case Export.Probe.Nothing{} False{}:
      over_at(put, path, None{}, ss, whole, rs, ep, es, {==})
    case Export.Probe.Dir{} _:
      {==}
    case Export.Probe.Other{} True{}:
      {==}
    case Export.Probe.Other{} False{}:
      {==}

def seen_link(lk: Bool, +put: Export.Put, +path: String, +p: String, +t: String, +ss: List<&2, Export.Seen>, +whole: Bool, +rs: List<&2, Export.Rec>, ep: {Export.put.path(put) == path : String}, es: {Export.seen.find(ss, path) == Some{Export.Seen.Link{p, t}} : Maybe<&2, Export.Seen>}) -> {Export.step.safe(Bool.pick(Export.Step, lk, Bool.pick(Export.Step, String.eq(t, Export.put.target(put)), Export.Step.Keep{}, Export.Step.Link{put}), Export.Step.Refuse{path, "a symbolic link stands there"}), ss, whole, rs) == True{} : Bool}:
  match lk:
    case True{}:
      link_same(String.eq(t, Export.put.target(put)), put, path, p, t, ss, whole, rs, ep, es)
    case False{}:
      {==}

def seen_file(lk: Bool, +put: Export.Put, +path: String, +p: String, +d: String, +runs: Bool, +ss: List<&2, Export.Seen>, +whole: Bool, +rs: List<&2, Export.Rec>, ep: {Export.put.path(put) == path : String}, es: {Export.seen.find(ss, path) == Some{Export.Seen.File{p, d, runs}} : Maybe<&2, Export.Seen>}) -> {Export.step.safe(Bool.pick(Export.Step, lk, Bool.pick(Export.Step, Export.recorded(whole, rs, path, d), Bool.pick(Export.Step, lk, Export.Step.Link{put}, Export.Step.Write{put, True{}}), Export.Step.Refuse{path, Export.UNRECORDED()}), Export.step.same(path, String.eq(d, Export.put.digest(put)), runs, Export.put.runs(put), Bool.pick(Export.Step, Export.recorded(whole, rs, path, d), Bool.pick(Export.Step, lk, Export.Step.Link{put}, Export.Step.Write{put, True{}}), Export.Step.Refuse{path, Export.UNRECORDED()}))), ss, whole, rs) == True{} : Bool}:
  match lk:
    case True{}:
      over_file(Export.recorded(whole, rs, path, d), True{}, put, path, p, d, runs, ss, whole, rs, {==}, ep, es)
    case False{}:
      same_safe(String.eq(d, Export.put.digest(put)), runs, Export.put.runs(put), path, Bool.pick(Export.Step, Export.recorded(whole, rs, path, d), Bool.pick(Export.Step, False{}, Export.Step.Link{put}, Export.Step.Write{put, True{}}), Export.Step.Refuse{path, Export.UNRECORDED()}), ss, whole, rs,
        over_file(Export.recorded(whole, rs, path, d), False{}, put, path, p, d, runs, ss, whole, rs, {==}, ep, es))

# One path the tree places: whatever stands there, the step writes over a
# regular file only where some revision records its bytes.
def held_safe(+put: Export.Put, +path: String, +lk: Bool, s: Maybe<&2, Export.Seen>, pr: Export.Probe, +ss: List<&2, Export.Seen>, +whole: Bool, +rs: List<&2, Export.Rec>, ep: {Export.put.path(put) == path : String}, es: {Export.seen.find(ss, path) == s : Maybe<&2, Export.Seen>}) -> {Export.step.safe(Export.step.held(put, path, lk, s, pr, whole, rs), ss, whole, rs) == True{} : Bool}:
  match s:
    case None{}:
      absent_safe(pr, lk, put, path, ss, whole, rs, ep, es)
    case Some{Export.Seen.Link{+p, +t}}:
      seen_link(lk, put, path, p, t, ss, whole, rs, ep, es)
    case Some{Export.Seen.File{+p, +d, +runs}}:
      seen_file(lk, put, path, p, d, runs, ss, whole, rs, ep, es)

def step_safe(o: Export.Outcome, +ss: List<&2, Export.Seen>, +dirs: Set(), +others: Set(), +whole: Bool, +rs: List<&2, Export.Rec>) -> {Export.step.safe(Export.step.of(o, ss, dirs, others, whole, rs), ss, whole, rs) == True{} : Bool}:
  match o:
    case Export.Outcome.Refused{p, b}:
      {==}
    case Export.Outcome.Laid{+put}:
      held_safe(put, Export.put.path(put), Export.is.link(put), Export.seen.find(ss, Export.put.path(put)), Export.probe.of(Arrange.has(dirs, Export.put.path(put)), Arrange.has(others, Export.put.path(put))), ss, whole, rs, {==}, {==})

# The folder's plan writes over no work nothing has recorded.
def steps_safe(os: List<&2, Export.Outcome>, +ss: List<&2, Export.Seen>, +dirs: Set(), +others: Set(), +whole: Bool, +rs: List<&2, Export.Rec>) -> {Export.steps.safe(Export.steps(os, ss, dirs, others, whole, rs), ss, whole, rs) == True{} : Bool}:
  match os:
    case Nil{}:
      {==}
    case +o <> +rest:
      and_tt(Export.step.safe(Export.step.of(o, ss, dirs, others, whole, rs), ss, whole, rs), Export.steps.safe(Export.steps(rest, ss, dirs, others, whole, rs), ss, whole, rs),
        step_safe(o, ss, dirs, others, whole, rs), steps_safe(rest, ss, dirs, others, whole, rs))

# Removing
# --------

def and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, S.false_true(e))

def and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(e))

# A path with something to remove at it among the walk's entries still has
# it with one more entry in front.
def removed_more(ps: List<&2, String>, +s: Export.Seen, +rest: List<&2, Export.Seen>, +whole: Bool, +rs: List<&2, Export.Rec>, +h: {Export.removed.ok(ps, rest, whole, rs) == True{} : Bool}) -> {Export.removed.ok(ps, s <> rest, whole, rs) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +more:
      and_tt(Export.witness(s <> rest, p, whole, rs), Export.removed.ok(more, s <> rest, whole, rs),
        or_r(Bool.and(String.eq(Export.seen.path(s), p), Export.seen.recorded(s, whole, rs)), Export.witness(rest, p, whole, rs), and_l(Export.witness(rest, p, whole, rs), Export.removed.ok(more, rest, whole, rs), h)),
        removed_more(more, s, rest, whole, rs, and_r(Export.witness(rest, p, whole, rs), Export.removed.ok(more, rest, whole, rs), h)))

def removed_step(c: Bool, +s: Export.Seen, +rest: List<&2, Export.Seen>, +placed: Set(), +whole: Bool, +rs: List<&2, Export.Rec>, +ec: {Bool.and(Bool.not(Arrange.has(placed, Export.seen.path(s))), Export.seen.gone(s, whole, rs)) == c : Bool}, +ih: {Export.removed.ok(Export.removes(rest, placed, whole, rs), rest, whole, rs) == True{} : Bool}) -> {Export.removed.ok(Tree.keep(~String, c, Export.seen.path(s), Export.removes(rest, placed, whole, rs)), s <> rest, whole, rs) == True{} : Bool}:
  match c:
    case True{}:
      +gone = and_r(Bool.not(Arrange.has(placed, Export.seen.path(s))), Export.seen.gone(s, whole, rs), ec)
      and_tt(Export.witness(s <> rest, Export.seen.path(s), whole, rs), Export.removed.ok(Export.removes(rest, placed, whole, rs), s <> rest, whole, rs),
        %Equal.sym(Bool, String.eq(Export.seen.path(s), Export.seen.path(s)), True{}, S.eq_refl(Export.seen.path(s))) : {Bool.or(Bool.and(_, Export.seen.recorded(s, whole, rs)), Export.witness(rest, Export.seen.path(s), whole, rs)) == True{} : Bool}
        %Equal.sym(Bool, Export.seen.recorded(s, whole, rs), True{}, gone_recorded(s, whole, rs, gone)) : {Bool.or(Bool.and(True{}, _), Export.witness(rest, Export.seen.path(s), whole, rs)) == True{} : Bool}
        {==},
        removed_more(Export.removes(rest, placed, whole, rs), s, rest, whole, rs, ih))
    case False{}:
      removed_more(Export.removes(rest, placed, whole, rs), s, rest, whole, rs, ih)

# Everything the folder's plan removes is something the walk found that
# some revision records, or that the export's own output is.
def removes_safe(ss: List<&2, Export.Seen>, +placed: Set(), +whole: Bool, +rs: List<&2, Export.Rec>) -> {Export.removed.ok(Export.removes(ss, placed, whole, rs), ss, whole, rs) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +rest:
      removed_step(Bool.and(Bool.not(Arrange.has(placed, Export.seen.path(s))), Export.seen.gone(s, whole, rs)), s, rest, placed, whole, rs, {==}, removes_safe(rest, placed, whole, rs))

# Words
# -----

def m_none(-A: Data, m: Maybe<&2, A>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def m_some(-A: Data, m: Maybe<&2, A>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{x}:
      Unit

def none_some(-A: Data, -x: A, e: {None{} == Some{x} : Maybe<&2, A>}) -> Empty:
  %e : {m_none(A, _) : Type}
  Unit{}

def some_none(-A: Data, -x: A, e: {Some{x} == None{} : Maybe<&2, A>}) -> Empty:
  %e : {m_some(A, _) : Type}
  Unit{}

# Where it writes
# ---------------

def held_dest(e: Bool, s: Bool, +into: String, +tx: String, ee: {String.is_empty(tx) == e : Bool}) -> {Export.dest.ok(Export.Lst.Listed{tx}, s, Export.dest.held(into, e, s)) == True{} : Bool}:
  match e s:
    case True{} _:
      ee
    case False{} True{}:
      %Equal.sym(Bool, String.is_empty(tx), False{}, ee) : {Bool.and(True{}, Bool.not(_)) == True{} : Bool}
      {==}
    case False{} False{}:
      {==}

# An export makes a fresh copy only where nothing is, or nothing is held,
# and updates only a directory holding something that is a store.
def dest(+into: String, l: Export.Lst, s: Bool) -> {Export.dest.ok(l, s, Export.dest.decide(into, l, s)) == True{} : Bool}:
  match l:
    case Export.Lst.Absent{}:
      {==}
    case Export.Lst.Unreadable{m}:
      {==}
    case Export.Lst.Listed{+tx}:
      held_dest(String.is_empty(tx), s, into, tx, {==})

# The folder, file by file
# ------------------------

def some_inj(+a: String, -b: String, e: {Some{a} == Some{b} : Maybe<&2, String>}) -> {a == b : String}:
  Equal.cong(Maybe<&2, String>, String, m => Maybe.default(&2, String, m, a), Some{a}, Some{b}, e)

def or_l(a: Bool, -b: Bool, e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Bool.or(False{}, b) == True{} : Bool}, S.false_true(e))

def find_step(c: Bool, +p: String, +d: String, +rest: List<&2, T.Split>, +digest: String, +from: String, ec: {String.eq(d, digest) == c : Bool}, e: {Bool.pick(Maybe<&2, String>, c, Some{p}, Export.split.find(rest, digest)) == Some{from} : Maybe<&2, String>}, ih: {Export.split.find(rest, digest) == Some{from} : Maybe<&2, String>} -> {Export.split.held(rest, from, digest) == True{} : Bool}) -> {Bool.or(Bool.and(String.eq(p, from), String.eq(d, digest)), Export.split.held(rest, from, digest)) == True{} : Bool}:
  match c:
    case True{}:
      %some_inj(p, from, e) : {Bool.or(Bool.and(String.eq(p, _), String.eq(d, digest)), Export.split.held(rest, _, digest)) == True{} : Bool}
      %Equal.sym(Bool, String.eq(p, p), True{}, S.eq_refl(p)) : {Bool.or(Bool.and(_, String.eq(d, digest)), Export.split.held(rest, p, digest)) == True{} : Bool}
      %Equal.sym(Bool, String.eq(d, digest), True{}, ec) : {Bool.or(Bool.and(True{}, _), Export.split.held(rest, p, digest)) == True{} : Bool}
      {==}
    case False{}:
      or_r(Bool.and(String.eq(p, from), String.eq(d, digest)), Export.split.held(rest, from, digest), ih(e))

# The file a payload is found in is a file of the store holding it.
def find_held(ss: List<&2, T.Split>, +digest: String, +from: String, e: {Export.split.find(ss, digest) == Some{from} : Maybe<&2, String>}) -> {Export.split.held(ss, from, digest) == True{} : Bool}:
  match ss:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, none_some(String, from, e))
    case T.Split{+p, +d} <> +rest:
      find_step(String.eq(d, digest), p, d, rest, digest, from, {==}, e, x => find_held(rest, digest, from, x))




def same_refl(b: Bool) -> {Export.bool.same(b, b) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def lines_as(c: Result<&2, &2, String, List<&2, Ops.Item>>, +path: String, +file: String, +ep: String, +payload: Maybe<&2, String>, +target: Maybe<&2, Tree.Target>, +mode: Tree.Mode, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>, ec: {Main.content(fs, ds, id, file) == c : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Export.laid.as(Export.lay.lines(path, c, Export.runs(mode)), path, Tree.Entry{file, ep, Tree.Lines{}, payload, target, mode}, t, fs, ds, id, pays) == True{} : Bool}:
  match c:
    case Fail{m}:
      {==}
    case Done{+items}:
      %Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Main.content(fs, ds, id, file), Done{items}, ec) : {Bool.and(True{}, Bool.and(Export.maybe.is(Export.cat.of(_), Ops.text(items)), Export.bool.same(Export.runs(mode), Export.runs(mode)))) == True{} : Bool}
      %Equal.sym(Bool, String.eq(Ops.text(items), Ops.text(items)), True{}, S.eq_refl(Ops.text(items))) : {Bool.and(True{}, Bool.and(_, Export.bool.same(Export.runs(mode), Export.runs(mode)))) == True{} : Bool}
      same_refl(Export.runs(mode))

def held_as(found: Maybe<&2, String>, +path: String, +d: String, +forgot: Bool, +file: String, +ep: String, +target: Maybe<&2, Tree.Target>, +mode: Tree.Mode, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>, ef: {Export.split.find(pays, d) == found : Maybe<&2, String>}) -> {Export.laid.as(Export.lay.held(path, d, found, forgot, Export.runs(mode)), path, Tree.Entry{file, ep, Tree.Whole{}, Some{d}, target, mode}, t, fs, ds, id, pays) == True{} : Bool}:
  match found:
    case None{}:
      match forgot:
        case True{}:
          {==}
        case False{}:
          {==}
    case Some{+from}:
      %Equal.sym(Bool, String.eq(d, d), True{}, S.eq_refl(d)) : {Bool.and(True{}, Bool.and(_, Bool.and(Export.split.held(pays, from, d), Export.bool.same(Export.runs(mode), Export.runs(mode))))) == True{} : Bool}
      %Equal.sym(Bool, Export.split.held(pays, from, d), True{}, find_held(pays, d, from, ef)) : {Bool.and(True{}, Bool.and(True{}, Bool.and(_, Export.bool.same(Export.runs(mode), Export.runs(mode))))) == True{} : Bool}
      same_refl(Export.runs(mode))

def whole_as(payload: Maybe<&2, String>, +path: String, +file: String, +ep: String, +target: Maybe<&2, Tree.Target>, +mode: Tree.Mode, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>, +bs: List<&2, Prune.Body>) -> {Export.laid.as(Export.lay.whole(path, payload, pays, bs, Export.runs(mode)), path, Tree.Entry{file, ep, Tree.Whole{}, payload, target, mode}, t, fs, ds, id, pays) == True{} : Bool}:
  match payload:
    case None{}:
      {==}
    case Some{+d}:
      held_as(Export.split.find(pays, d), path, d, Export.forgets(bs, d), file, ep, target, mode, t, fs, ds, id, pays, {==})

def ref_as(found: Maybe<&2, String>, +f: String, +path: String, +file: String, +ep: String, +payload: Maybe<&2, String>, +mode: Tree.Mode, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>, ef: {Tree.path(t, f) == found : Maybe<&2, String>}) -> {Export.laid.as(Export.lay.reference(path, found), path, Tree.Entry{file, ep, Tree.Link{}, payload, Some{Tree.Reference{f}}, mode}, t, fs, ds, id, pays) == True{} : Bool}:
  match found:
    case None{}:
      {==}
    case Some{+to}:
      %Equal.sym(Maybe<&2, String>, Tree.path(t, f), Some{to}, ef) : {Bool.and(True{}, String.eq(Main.materialise.of(path, _, "file:" ++ f), Main.relative_path(Main.directory_of(path), to))) == True{} : Bool}
      S.eq_refl(Main.relative_path(Main.directory_of(path), to))

def link_as(target: Maybe<&2, Tree.Target>, +path: String, +file: String, +ep: String, +payload: Maybe<&2, String>, +mode: Tree.Mode, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>) -> {Export.laid.as(Export.lay.link(path, t, target), path, Tree.Entry{file, ep, Tree.Link{}, payload, target, mode}, t, fs, ds, id, pays) == True{} : Bool}:
  match target:
    case None{}:
      {==}
    case Some{Tree.Verbatim{+v}}:
      S.eq_refl(v)
    case Some{Tree.Reference{+f}}:
      ref_as(Tree.path(t, f), f, path, file, ep, payload, mode, t, fs, ds, id, pays, {==})

def entry_as(+path: String, e: Tree.Entry, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>, +bs: List<&2, Prune.Body>) -> {Export.laid.as(Export.lay.entry(path, e, t, fs, ds, id, pays, bs), path, e, t, fs, ds, id, pays) == True{} : Bool}:
  match e:
    case Tree.Entry{+file, +ep, kind, +payload, +target, +mode}:
      match kind:
        case Tree.Link{}:
          link_as(target, path, file, ep, payload, mode, t, fs, ds, id, pays)
        case Tree.Whole{}:
          whole_as(payload, path, file, ep, target, mode, t, fs, ds, id, pays, bs)
        case Tree.Lines{}:
          lines_as(Main.content(fs, ds, id, file), path, file, ep, payload, target, mode, t, fs, ds, id, pays, {==})

def one_as(p: Export.Placed, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>, +bs: List<&2, Prune.Body>) -> {Export.placed.as(p, Export.lay.one(p, t, fs, ds, id, pays, bs), t, fs, ds, id, pays) == True{} : Bool}:
  match p:
    case Export.Placed{+path, es}:
      match es:
        case Nil{}:
          {==}
        case +e <> Nil{}:
          entry_as(path, e, t, fs, ds, id, pays, bs)
        case e <> f <> more:
          {==}

# Every file the folder is given is as the target's tree has it.
def laid_all(ps: List<&2, Export.Placed>, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>, +bs: List<&2, Prune.Body>) -> {Export.laid.all(ps, Export.lay(ps, t, fs, ds, id, pays, bs), t, fs, ds, id, pays) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +rest:
      and_tt(Export.placed.as(p, Export.lay.one(p, t, fs, ds, id, pays, bs), t, fs, ds, id, pays), Export.laid.all(rest, Export.lay(rest, t, fs, ds, id, pays, bs), t, fs, ds, id, pays),
        one_as(p, t, fs, ds, id, pays, bs), laid_all(rest, t, fs, ds, id, pays, bs))

# What a copy carries
# -------------------

def some_doc(+a: Store.Doc, -b: Store.Doc, e: {Some{a} == Some{b} : Maybe<&2, Store.Doc>}) -> {a == b : Store.Doc}:
  Equal.cong(Maybe<&2, Store.Doc>, Store.Doc, m => Maybe.default(&2, Store.Doc, m, a), Some{a}, Some{b}, e)

def doc_refl(d: Store.Doc) -> {Export.doc.same(d, d) == True{} : Bool}:
  match d:
    case Store.Doc{+p, +i, +n, +t}:
      and_tt(String.eq(p, p), Bool.and(String.eq(i, i), Bool.and(Nat.is_eq(n, n), String.eq(t, t))), S.eq_refl(p),
        and_tt(String.eq(i, i), Bool.and(Nat.is_eq(n, n), String.eq(t, t)), S.eq_refl(i),
          and_tt(Nat.is_eq(n, n), String.eq(t, t), Comp.eq_refl(n), S.eq_refl(t))))

def found_step(c: Bool, +x: Store.Doc, +rest: List<&2, Store.Doc>, +id: String, +d: Store.Doc, e: {Bool.pick(Maybe<&2, Store.Doc>, c, Some{x}, Export.doc.find(rest, id)) == Some{d} : Maybe<&2, Store.Doc>}, ih: {Export.doc.find(rest, id) == Some{d} : Maybe<&2, Store.Doc>} -> {Export.doc.among(rest, d) == True{} : Bool}) -> {Bool.or(Export.doc.same(x, d), Export.doc.among(rest, d)) == True{} : Bool}:
  match c:
    case True{}:
      %some_doc(x, d, e) : {Bool.or(Export.doc.same(x, _), Export.doc.among(rest, _)) == True{} : Bool}
      or_l(Export.doc.same(x, x), Export.doc.among(rest, x), doc_refl(x))
    case False{}:
      or_r(Export.doc.same(x, d), Export.doc.among(rest, d), ih(e))

# A document found by its digest is, whole, one of the documents it was
# found among.
def found_among(ds: List<&2, Store.Doc>, +id: String, +d: Store.Doc, e: {Export.doc.find(ds, id) == Some{d} : Maybe<&2, Store.Doc>}) -> {Export.doc.among(ds, d) == True{} : Bool}:
  match ds:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, none_some(Store.Doc, d, e))
    case Store.Doc{+p0, +i0, +n0, +t0} <> +rest:
      found_step(String.eq(i0, id), Store.Doc{p0, i0, n0, t0}, rest, id, d, e, x => found_among(rest, id, d, x))

def push_from(m: Maybe<&2, Store.Doc>, +ds: List<&2, Store.Doc>, +id: String, +rest: List<&2, Store.Doc>, em: {Export.doc.find(ds, id) == m : Maybe<&2, Store.Doc>}, ih: {Export.docs.from(rest, ds) == True{} : Bool}) -> {Export.docs.from(Export.doc.push(m, rest), ds) == True{} : Bool}:
  match m:
    case None{}:
      ih
    case Some{+x}:
      and_tt(Export.doc.among(ds, x), Export.docs.from(rest, ds), found_among(ds, id, x, em), ih)

def among_from(ids: List<&2, String>, +ds: List<&2, Store.Doc>) -> {Export.docs.from(Export.docs.among(ids, ds), ds) == True{} : Bool}:
  match ids:
    case Nil{}:
      {==}
    case +id <> +rest:
      push_from(Export.doc.find(ds, id), ds, id, Export.docs.among(rest, ds), {==}, among_from(rest, ds))

def pays_found(fm: Maybe<&2, String>, +id: String, +later: List<&2, T.Split>, +ps: List<&2, T.Split>, ef: {Export.split.find(ps, id) == fm : Maybe<&2, String>}, ih: {Export.pays.from(later, ps) == True{} : Bool}) -> {Export.pays.from(Export.payload.push(id, fm, later), ps) == True{} : Bool}:
  match fm:
    case None{}:
      ih
    case Some{+from}:
      and_tt(Export.split.held(ps, from, id), Export.pays.from(later, ps), find_held(ps, id, from, ef), ih)

def pays_step(h: Bool, +id: String, +later: List<&2, T.Split>, +ps: List<&2, T.Split>, +ih: {Export.pays.from(later, ps) == True{} : Bool}) -> {Export.pays.from(Bool.pick(List<&2, T.Split>, h, later, Export.payload.push(id, Export.split.find(ps, id), later)), ps) == True{} : Bool}:
  match h:
    case True{}:
      ih
    case False{}:
      pays_found(Export.split.find(ps, id), id, later, ps, {==}, ih)

def pays_among(ids: List<&2, String>, +dset: Set(), +ps: List<&2, T.Split>) -> {Export.pays.from(Export.payloads.among(ids, dset, ps), ps) == True{} : Bool}:
  match ids:
    case Nil{}:
      {==}
    case +id <> +rest:
      pays_step(Arrange.has(dset, id), id, Export.payloads.among(rest, dset, ps), ps, pays_among(rest, dset, ps))

def plan_named(+held: List<&2, Main.Full>, +t: Tree.Tree(), +ds: List<&2, Store.Doc>, +ps: List<&2, T.Split>, +bodies: List<&2, Prune.Body>, +rs: List<&2, Receive.Ruled>, +bs: List<&2, Bm.Bookmark>, +claims: List<&2, T.Split>, +named: List<&2, String>) -> {Export.plan.from(Export.plan.named(held, t, ds, ps, bodies, rs, bs, claims, named), ds, ps) == True{} : Bool}:
  +ns = Main.sorted_distinct(named)
  +dset = Set.from_list(Export.doc.ids(Export.docs.among(ns, ds)))
  +forg = Main.sorted_distinct(Export.forgetting.of(bodies, Set.from_list(ns), dset))
  and_tt(Export.docs.from(Export.docs.among(ns, ds), ds), Bool.and(Export.pays.from(Export.payloads.among(ns, dset, ps), ps), Export.docs.from(Export.docs.among(forg, ds), ds)),
    among_from(ns, ds),
    and_tt(Export.pays.from(Export.payloads.among(ns, dset, ps), ps), Export.docs.from(Export.docs.among(forg, ds), ds), pays_among(ns, dset, ps), among_from(forg, ds)))

# A copy is assembled from this store's own files: every document it
# carries is, whole, one of this store's.
def plan_from(+held: List<&2, Main.Full>, +t: Tree.Tree(), +ds: List<&2, Store.Doc>, +ps: List<&2, T.Split>, +bodies: List<&2, Prune.Body>, +rs: List<&2, Receive.Ruled>, +bs: List<&2, Bm.Bookmark>, +claims: List<&2, T.Split>) -> {Export.plan.from(Export.plan.of(held, t, ds, ps, bodies, rs, bs, claims), ds, ps) == True{} : Bool}:
  plan_named(held, t, ds, ps, bodies, rs, bs, claims, Export.closure(Nat.mul(2n, 1n+Nat.add(List.length(&2, String, Export.named.by(held)), Export.keeps.all(ds))), ds, Export.named.by(held), Nil{}))

# Onto a copy
# -----------

def or_left_false(a: Bool, -b: Bool, e: {Bool.or(a, b) == True{} : Bool}, ea: {a == False{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      e
    case True{}:
      Empty.absurd({b == True{} : Bool}, S.true_false(ea))

def kept_head(c: Bool, +i: String, +id: String, +s: String, +held: List<&2, T.Split>, +dflt: String, +tail: List<&2, T.Split>, ec: {String.eq(i, id) == c : Bool}, +e: {Arrange.lookup(held, id) == Some{s} : Maybe<&2, String>}, ih: {c == False{} : Bool} -> {Arrange.lookup(tail, id) == Some{s} : Maybe<&2, String>}) -> {Bool.pick(Maybe<&2, String>, c, Some{Maybe.default(&2, String, Arrange.lookup(held, i), dflt)}, Arrange.lookup(tail, id)) == Some{s} : Maybe<&2, String>}:
  match c:
    case True{}:
      %Equal.sym(String, i, id, S.eq_true(i, id, ec)) : {Some{Maybe.default(&2, String, Arrange.lookup(held, _), dflt)} == Some{s} : Maybe<&2, String>}
      %Equal.sym(Maybe<&2, String>, Arrange.lookup(held, id), Some{s}, e) : {Some{Maybe.default(&2, String, _, dflt)} == Some{s} : Maybe<&2, String>}
      {==}
    case False{}:
      ih({==})

# An update renames no revision the copy holds: each keeps the stem it has.
def stems_kept(fs: List<&2, Main.Full>, +held: List<&2, T.Split>, +ex: List<&2, Naming.Named>, +id: String, +s: String, +e: {Arrange.lookup(held, id) == Some{s} : Maybe<&2, String>}, m: {Rev.member(Main.ids(fs), id) == True{} : Bool}) -> {Arrange.lookup(Export.stems.around(fs, held, ex), id) == Some{s} : Maybe<&2, String>}:
  match fs:
    case Nil{}:
      Empty.absurd({Arrange.lookup(Nil{}, id) == Some{s} : Maybe<&2, String>}, S.false_true(m))
    case Main.Full{+i, +c, parents, supersedes, a, +w, rb, rv, facts, +msg} <> +rest:
      kept_head(String.eq(i, id), i, id, s, held, Naming.stem(w, msg, c, i, ex), Export.stems.around(rest, held, Bool.pick(List<&2, Naming.Named>, Maybe.is_some(&2, String, Arrange.lookup(held, i)), ex, Naming.Named{w, msg, c} <> ex)), {==}, e,
        x => stems_kept(rest, held, Bool.pick(List<&2, Naming.Named>, Maybe.is_some(&2, String, Arrange.lookup(held, i)), ex, Naming.Named{w, msg, c} <> ex), id, s, e, or_left_false(String.eq(i, id), Rev.member(Main.ids(rest), id), m, x)))

# What an update destroys
# -----------------------

# An update destroys only originals a forgetting document of either side
# stands in for.
def destroys_of(+f: List<&2, String>, +cst: Prune.Stored) -> {Main.all_held(f, Export.onto.destroys.of(f, cst)) == True{} : Bool}:
  +held = Set.from_list(List.append(&2, String, Export.body.digests(Receive.stored.bodies(cst)), Export.split.digests(Receive.stored.payloads(cst))))
  StatusL.ah_distinct(f, List.sort(~String, ~(a => b => String.is_le(a, b)), Receive.among(f, held)),
    StatusL.ah_sort(~(a => b => String.is_le(a, b)), f, Receive.among(f, held),
      ReceiveL.among_held(f, held, f, ReceiveL.held_refl(f))))

def destroys(+p: Export.Plan, +here: List<&2, Prune.Body>, +cst: Prune.Stored, +marks: List<&2, Bm.Bookmark>) -> {Main.all_held(Export.onto.forgotten(Export.onto.of(p, here, cst, marks)), Export.onto.destroys(Export.onto.of(p, here, cst, marks))) == True{} : Bool}:
  destroys_of(Export.onto.forgotten.of(p, here, cst), cst)

# Said of the documents themselves: every original an update destroys is
# one a forgetting document of this store, or of the copy, stands in for.

def fa_push(f: Maybe<&2, String>, +d: String, -rest: List<&2, Prune.Body>, ih: {Rev.member(Export.forgets.all(rest), d) == Receive.forgot.by(rest, d) : Bool}) -> {Rev.member(Export.maybe.push(f, Export.forgets.all(rest)), d) == Bool.or(Receive.stands.for(f, d), Receive.forgot.by(rest, d)) : Bool}:
  match f:
    case None{}:
      ih
    case Some{t}:
      Equal.cong(Bool, Bool, x => Bool.or(String.eq(t, d), x), Rev.member(Export.forgets.all(rest), d), Receive.forgot.by(rest, d), ih)

def forgets_all(bs: List<&2, Prune.Body>, +d: String) -> {Rev.member(Export.forgets.all(bs), d) == Receive.forgot.by(bs, d) : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Prune.Body{p, id, ok, f} <> +rest:
      fa_push(f, d, rest, forgets_all(rest, d))

def member_head(+t: String, +xs: List<&2, String>) -> {Rev.member(t <> xs, t) == True{} : Bool}:
  %Equal.sym(Bool, String.eq(t, t), True{}, S.eq_refl(t)) : {Bool.or(_, Rev.member(xs, t)) == True{} : Bool}
  {==}

def here_all.none(c: Bool, -fa: List<&2, String>, -fh: List<&2, String>, ih: {Main.all_held(fa, fh) == True{} : Bool}) -> {Main.all_held(fa, Bool.pick(List<&2, String>, c, fh, fh)) == True{} : Bool}:
  match c:
    case True{}:
      ih
    case False{}:
      ih

def here_all.some(c: Bool, +t: String, +fa: List<&2, String>, +fh: List<&2, String>, +ih: {Main.all_held(fa, fh) == True{} : Bool}) -> {Main.all_held(t <> fa, Bool.pick(List<&2, String>, c, t <> fh, fh)) == True{} : Bool}:
  match c:
    case True{}:
      and_tt(Rev.member(t <> fa, t), Main.all_held(t <> fa, fh), member_head(t, fa), ReceiveL.held_cons(t, fa, fh, ih))
    case False{}:
      ReceiveL.held_cons(t, fa, fh, ih)

def here_all.step(c: Bool, f: Maybe<&2, String>, +fa: List<&2, String>, +fh: List<&2, String>, +ih: {Main.all_held(fa, fh) == True{} : Bool}) -> {Main.all_held(Export.maybe.push(f, fa), Bool.pick(List<&2, String>, c, Export.maybe.push(f, fh), fh)) == True{} : Bool}:
  match f:
    case None{}:
      here_all.none(c, fa, fh, ih)
    case Some{t}:
      here_all.some(c, t, fa, fh, ih)

# What the documents that travel forget is among what all of them forget.
def here_all(bs: List<&2, Prune.Body>, +docs: Set()) -> {Main.all_held(Export.forgets.all(bs), Export.forgets.here(bs, docs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Prune.Body{p, +id, ok, f} <> +rest:
      here_all.step(Arrange.has(docs, id), f, Export.forgets.all(rest), Export.forgets.here(rest, docs), here_all(rest, docs))

def ex_or(a: Bool, +bs: List<&2, Prune.Body>, +cb: List<&2, Prune.Body>, +docs: Set(), +d: String, ea: {Rev.member(Export.forgets.here(bs, docs), d) == a : Bool}, h: {Bool.or(a, Rev.member(Export.forgets.all(cb), d)) == True{} : Bool}) -> {Bool.or(Receive.forgot.by(bs, d), Receive.forgot.by(cb, d)) == True{} : Bool}:
  match a:
    case True{}:
      %Equal.sym(Bool, Receive.forgot.by(bs, d), True{}, Equal.trans(Bool, Receive.forgot.by(bs, d), Rev.member(Export.forgets.all(bs), d), True{}, Equal.sym(Bool, Rev.member(Export.forgets.all(bs), d), Receive.forgot.by(bs, d), forgets_all(bs, d)), ForgetL.held_member(Export.forgets.all(bs), Export.forgets.here(bs, docs), d, here_all(bs, docs), ea))) : {Bool.or(_, Receive.forgot.by(cb, d)) == True{} : Bool}
      {==}
    case False{}:
      or_r(Receive.forgot.by(bs, d), Receive.forgot.by(cb, d), Equal.trans(Bool, Receive.forgot.by(cb, d), Rev.member(Export.forgets.all(cb), d), True{}, Equal.sym(Bool, Rev.member(Export.forgets.all(cb), d), Receive.forgot.by(cb, d), forgets_all(cb, d)), h))

def destroyed(+p: Export.Plan, +here: List<&2, Prune.Body>, +cst: Prune.Stored, +marks: List<&2, Bm.Bookmark>, +d: String, h: {Rev.member(Export.onto.destroys(Export.onto.of(p, here, cst, marks)), d) == True{} : Bool}) -> {Bool.or(Receive.forgot.by(here, d), Receive.forgot.by(Receive.stored.bodies(cst), d)) == True{} : Bool}:
  ex_or(Rev.member(Export.forgets.here(here, Export.plan.docset(p)), d), here, Receive.stored.bodies(cst), Export.plan.docset(p), d, {==},
    Equal.trans(Bool, Bool.or(Rev.member(Export.forgets.here(here, Export.plan.docset(p)), d), Rev.member(Export.forgets.all(Receive.stored.bodies(cst)), d)), Rev.member(List.append(&2, String, Export.forgets.here(here, Export.plan.docset(p)), Export.forgets.all(Receive.stored.bodies(cst))), d), True{}, Equal.sym(Bool, Rev.member(List.append(&2, String, Export.forgets.here(here, Export.plan.docset(p)), Export.forgets.all(Receive.stored.bodies(cst))), d), Bool.or(Rev.member(Export.forgets.here(here, Export.plan.docset(p)), d), Rev.member(Export.forgets.all(Receive.stored.bodies(cst)), d)), ReceiveL.member_app(Export.forgets.here(here, Export.plan.docset(p)), Export.forgets.all(Receive.stored.bodies(cst)), d)),
      ForgetL.held_member(List.append(&2, String, Export.forgets.here(here, Export.plan.docset(p)), Export.forgets.all(Receive.stored.bodies(cst))), Main.sorted_distinct(List.append(&2, String, Export.forgets.here(here, Export.plan.docset(p)), Export.forgets.all(Receive.stored.bodies(cst)))), d, StatusL.ah_distinct(List.append(&2, String, Export.forgets.here(here, Export.plan.docset(p)), Export.forgets.all(Receive.stored.bodies(cst))), List.sort(~String, ~(a => b => String.is_le(a, b)), List.append(&2, String, Export.forgets.here(here, Export.plan.docset(p)), Export.forgets.all(Receive.stored.bodies(cst)))), StatusL.ah_sort(~(a => b => String.is_le(a, b)), List.append(&2, String, Export.forgets.here(here, Export.plan.docset(p)), Export.forgets.all(Receive.stored.bodies(cst))), List.append(&2, String, Export.forgets.here(here, Export.plan.docset(p)), Export.forgets.all(Receive.stored.bodies(cst))), ReceiveL.held_refl(List.append(&2, String, Export.forgets.here(here, Export.plan.docset(p)), Export.forgets.all(Receive.stored.bodies(cst)))))),
        ForgetL.held_member(Export.onto.forgotten(Export.onto.of(p, here, cst, marks)), Export.onto.destroys(Export.onto.of(p, here, cst, marks)), d, destroys(p, here, cst, marks), h))))

# Where the folder's files go
# ---------------------------

def l_cons(-A: Data, l: List<&2, A>) -> Type:
  match l:
    case Nil{}:
      Empty
    case x <> r:
      Unit

def cons_nil(-A: Data, -x: A, -r: List<&2, A>, e: {x <> r == Nil{} : List<&2, A>}) -> Empty:
  %e : {l_cons(A, _) : Type}
  Unit{}

def app_nil(-A: Data, xs: List<&2, A>, -ys: List<&2, A>, e: {List.append(&2, A, xs, ys) == Nil{} : List<&2, A>}) -> {xs == Nil{} : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case x <> r:
      Empty.absurd({x <> r == Nil{} : List<&2, A>}, cons_nil(A, x, List.append(&2, A, r, ys), e))
