# What `export` promises of a copy's folder it catches up. Every file its
# plan writes over or takes away holds bytes the copy's own history can
# give back.
import Base
import ./export.bend as Export
import ./update.bend as U
import ./update_lemmas.bend as UpdL
import ./export_lemmas.bend as ExportL
import ./commands.bend as Main
import ./store.bend as Store
import ./tree.bend as Tree
import ./revision.bend as Rev
import ./text.bend as T
import ./ops.bend as Ops
import ./prune.bend as Prune
import ./folder.bend as Folder
import ./string_lemmas.bend as SL
import ./anchor_lemmas.bend as AL
import ./graph_lemmas.bend as GL
import ./composition_lemmas.bend as Comp
import ./map_lemmas.bend as ML
import ./sha256.bend as Sha
import ./utf8.bend as Utf8
import ./arrange.bend as Arrange

# What the copy's revisions record
# --------------------------------

def rds(r: Export.Rec) -> List<&2, String>:
  match r:
    case Export.Rec{p, ds, ls}:
      ds

def member_merge(a: Export.Rec, b: Export.Rec, +d: String, h: {Rev.member(rds(Export.rec.merge(a, b)), d) == True{} : Bool}) -> {Bool.or(Rev.member(rds(a), d), Rev.member(rds(b), d)) == True{} : Bool}:
  match a b:
    case Export.Rec{p, ds, ls} Export.Rec{q, +es, ms}:
      GL.append_mem(ds, es, d, h)

def member_join(dm: Maybe<&2, String>, l: Maybe<&2, String>, r: Export.Rec, +d: String, h: {Rev.member(rds(Export.rec.join(dm, l, r)), d) == True{} : Bool}) -> {Rev.member(Export.maybe.push(dm, rds(r)), d) == True{} : Bool}:
  match r:
    case Export.Rec{p, ds, ls}:
      h

def items_same(r: Result<&2, &2, String, List<&2, Ops.Item>>) -> {Export.rec.items(r) == U.recorded.lines(r) : Maybe<&2, String>}:
  match r:
    case Fail{e}:
      {==}
    case Done{items}:
      {==}

# What the copy records of one file of a tree is what `update` would.
def entry_same(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +cs: List<&2, Main.Contents>, +file: String, +id: String, e: Maybe<&2, Tree.Entry>) -> {Export.rec.entry(fs, ds, cs, file, id, e) == U.recorded.entry(fs, ds, cs, id, file, e) : Maybe<&2, String>}:
  match e:
    case None{}:
      {==}
    case Some{Tree.Entry{f, p, kind, payload, target, mode}}:
      match kind:
        case Tree.Whole{}:
          {==}
        case Tree.Lines{}:
          items_same(Main.content.found(fs, ds, id, file, Main.content_of(cs, id)))
        case Tree.Link{}:
          {==}

def push_back(mm: Maybe<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +x: String, +f: Main.Full, +rest: List<&2, Main.Full>, +tree: Tree.Tree(), +later: List<&2, String>, +d: String, em: {Export.rec.entry(fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x, Main.id_of(f), Tree.lookup(tree, x)) == mm : Maybe<&2, String>}, et: {Main.tree.r(fs, Main.id_of(f)) == Done{tree} : Result<&2, &2, Main.Refused, Tree.Tree()>}, h: {Rev.member(Export.maybe.push(mm, later), d) == True{} : Bool}, ih: {Rev.member(later, d) == True{} : Bool} -> {U.recoverable.go(rest, fs, ds, d) == True{} : Bool}) -> {U.recoverable.go(f <> rest, fs, ds, d) == True{} : Bool}:
  match mm:
    case None{}:
      AL.or_right(U.rev.records(fs, ds, Main.id_of(f), Main.tree.r(fs, Main.id_of(f)), d), U.recoverable.go(rest, fs, ds, d), ih(h))
    case Some{+v}:
      AL.or_cases({U.recoverable.go(f <> rest, fs, ds, d) == True{} : Bool}, String.eq(v, d), Rev.member(later, d), h,
        l => AL.or_left(U.rev.records(fs, ds, Main.id_of(f), Main.tree.r(fs, Main.id_of(f)), d), U.recoverable.go(rest, fs, ds, d),
          (%Equal.sym(Result<&2, &2, Main.Refused, Tree.Tree()>, Main.tree.r(fs, Main.id_of(f)), Done{tree}, et) : {U.rev.records(fs, ds, Main.id_of(f), _, d) == True{} : Bool}
            %SL.eq_true(v, d, l) : {U.tree.records(fs, ds, Main.id_of(f), tree, _) == True{} : Bool}
            UpdL.lookup_rec(tree, fs, ds, Main.id_of(f), x, v,
              Equal.trans(Maybe<&2, String>, U.recorded.entry(fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), Main.id_of(f), x, Tree.lookup(tree, x)), Export.rec.entry(fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x, Main.id_of(f), Tree.lookup(tree, x)), Some{v},
                Equal.sym(Maybe<&2, String>, Export.rec.entry(fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x, Main.id_of(f), Tree.lookup(tree, x)), U.recorded.entry(fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), Main.id_of(f), x, Tree.lookup(tree, x)), entry_same(fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x, Main.id_of(f), Tree.lookup(tree, x))),
                em)))),
        r => AL.or_right(U.rev.records(fs, ds, Main.id_of(f), Main.tree.r(fs, Main.id_of(f)), d), U.recoverable.go(rest, fs, ds, d), ih(r)))

def content_back(touch: Bool, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +x: String, +f: Main.Full, +rest: List<&2, Main.Full>, +tree: Tree.Tree(), +later: List<&2, String>, +d: String, et: {Main.tree.r(fs, Main.id_of(f)) == Done{tree} : Result<&2, &2, Main.Refused, Tree.Tree()>}, h: {Rev.member(Export.maybe.push(Export.rec.content(touch, fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x, Main.id_of(f), tree), later), d) == True{} : Bool}, ih: {Rev.member(later, d) == True{} : Bool} -> {U.recoverable.go(rest, fs, ds, d) == True{} : Bool}) -> {U.recoverable.go(f <> rest, fs, ds, d) == True{} : Bool}:
  match touch:
    case False{}:
      AL.or_right(U.rev.records(fs, ds, Main.id_of(f), Main.tree.r(fs, Main.id_of(f)), d), U.recoverable.go(rest, fs, ds, d), ih(h))
    case True{}:
      push_back(Export.rec.entry(fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x, Main.id_of(f), Tree.lookup(tree, x)), fs, ds, x, f, rest, tree, later, d, {==}, et, h, ih)

def at_back(t: Result<&2, &2, Main.Refused, Tree.Tree()>, +touch: Bool, +link: Bool, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +x: String, +f: Main.Full, +rest: List<&2, Main.Full>, +d: String, et: {Main.tree.r(fs, Main.id_of(f)) == t : Result<&2, &2, Main.Refused, Tree.Tree()>}, h: {Rev.member(rds(Export.rec.at(t, touch, link, fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x, Main.id_of(f), Export.rec.file(rest, fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x))), d) == True{} : Bool}, ih: {Rev.member(rds(Export.rec.file(rest, fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x)), d) == True{} : Bool} -> {U.recoverable.go(rest, fs, ds, d) == True{} : Bool}) -> {U.recoverable.go(f <> rest, fs, ds, d) == True{} : Bool}:
  match t:
    case Fail{e}:
      AL.or_right(U.rev.records(fs, ds, Main.id_of(f), Main.tree.r(fs, Main.id_of(f)), d), U.recoverable.go(rest, fs, ds, d), ih(h))
    case Done{+tree}:
      content_back(touch, fs, ds, x, f, rest, tree, rds(Export.rec.file(rest, fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x)), d, et,
        member_join(Export.rec.content(touch, fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x, Main.id_of(f), tree), Export.rec.laid(link, x, tree), Export.rec.file(rest, fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x), d, h),
        ih)

def when_back(any: Bool, +touch: Bool, +link: Bool, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +x: String, +f: Main.Full, +rest: List<&2, Main.Full>, +d: String, h: {Rev.member(rds(Export.rec.when(any, touch, link, fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x, Main.id_of(f), Export.rec.file(rest, fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x))), d) == True{} : Bool}, ih: {Rev.member(rds(Export.rec.file(rest, fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x)), d) == True{} : Bool} -> {U.recoverable.go(rest, fs, ds, d) == True{} : Bool}) -> {U.recoverable.go(f <> rest, fs, ds, d) == True{} : Bool}:
  match any:
    case False{}:
      AL.or_right(U.rev.records(fs, ds, Main.id_of(f), Main.tree.r(fs, Main.id_of(f)), d), U.recoverable.go(rest, fs, ds, d), ih(h))
    case True{}:
      at_back(Main.tree.r(fs, Main.id_of(f)), touch, link, fs, ds, x, f, rest, d, {==}, h, ih)

# A digest the copy's revisions record for one file is one `cat` of some
# revision among them reads, or a payload its tree names.
def file_back(revs: List<&2, Main.Full>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +x: String, +d: String, h: {Rev.member(rds(Export.rec.file(revs, fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x)), d) == True{} : Bool}) -> {U.recoverable.go(revs, fs, ds, d) == True{} : Bool}:
  match revs:
    case Nil{}:
      Empty.absurd({U.recoverable.go(Nil{}, fs, ds, d) == True{} : Bool}, Comp.false_true(h))
    case +f <> +rest:
      when_back(Bool.or(Export.touches(f, x), Export.links.stated(f, x)), Export.touches(f, x), Export.links.stated(f, x), fs, ds, x, f, rest, d, h, h2 => file_back(rest, fs, ds, x, d, h2))

def files_back(files: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +path: String, +d: String, h: {Rev.member(rds(Export.rec.files(files, fs, ds, path)), d) == True{} : Bool}) -> {U.recoverable(fs, ds, d) == True{} : Bool}:
  match files:
    case Nil{}:
      Empty.absurd({U.recoverable(fs, ds, d) == True{} : Bool}, Comp.false_true(h))
    case +file <> +rest:
      AL.or_cases({U.recoverable(fs, ds, d) == True{} : Bool}, Rev.member(rds(Export.rec.files(rest, fs, ds, path)), d), Rev.member(rds(Export.rec.file(fs, fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, file, Nil{}), file)), d),
        member_merge(Export.rec.files(rest, fs, ds, path), Export.rec.file(fs, fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, file, Nil{}), file), d, h),
        l => files_back(rest, fs, ds, path, d, l),
        r => file_back(fs, fs, ds, file, d, r))

def hold_cons(r: Export.Rec, +rest: List<&2, Export.Rec>, +path: String, +d: String, h: {Export.recs.hold(r <> rest, path, d) == True{} : Bool}) -> {Bool.or(Rev.member(rds(r), d), Export.recs.hold(rest, path, d)) == True{} : Bool}:
  match r:
    case Export.Rec{+p, +ds, ls}:
      AL.or_cases({Bool.or(Rev.member(ds, d), Export.recs.hold(rest, path, d)) == True{} : Bool}, Bool.and(String.eq(p, path), Rev.member(ds, d)), Export.recs.hold(rest, path, d), h,
        l => AL.or_left(Rev.member(ds, d), Export.recs.hold(rest, path, d), ExportL.and_r(String.eq(p, path), Rev.member(ds, d), l)),
        r => AL.or_right(Rev.member(ds, d), Export.recs.hold(rest, path, d), r))

# Every digest the copy's revisions are said to record at a path the walk
# found is one `cat` of some revision of the copy reads, or a payload its
# tree names.
def recs_back(ps: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +path: String, +d: String, h: {Export.recs.hold(Export.recs(ps, fs, ds), path, d) == True{} : Bool}) -> {U.recoverable(fs, ds, d) == True{} : Bool}:
  match ps:
    case Nil{}:
      Empty.absurd({U.recoverable(fs, ds, d) == True{} : Bool}, Comp.false_true(h))
    case +p <> +rest:
      AL.or_cases({U.recoverable(fs, ds, d) == True{} : Bool}, Rev.member(rds(Export.rec.files(Main.sorted_distinct(Export.ever.at(fs, p)), fs, ds, p)), d), Export.recs.hold(Export.recs(rest, fs, ds), path, d),
        hold_cons(Export.rec.files(Main.sorted_distinct(Export.ever.at(fs, p)), fs, ds, p), Export.recs(rest, fs, ds), path, d, h),
        l => files_back(Main.sorted_distinct(Export.ever.at(fs, p)), fs, ds, p, d, l),
        r => recs_back(rest, fs, ds, path, d, r))

# What the folder's plan writes over and takes away
# -------------------------------------------------

def over_back(hm: Maybe<&2, String>, +path: String, +ps: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, h: {Export.over.ok(False{}, Export.recs(ps, fs, ds), path, hm) == True{} : Bool}) -> {Export.given.back(fs, ds, hm) == True{} : Bool}:
  match hm:
    case None{}:
      {==}
    case Some{+d}:
      recs_back(ps, fs, ds, path, d, h)

def step_spare(x: Export.Step, +ss: List<&2, Export.Seen>, +ps: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, h: {Export.step.safe(x, ss, False{}, Export.recs(ps, fs, ds)) == True{} : Bool}) -> {Export.step.spares(x, ss, fs, ds) == True{} : Bool}:
  match x:
    case Export.Step.Write{+put, r}:
      over_back(Export.held.digest(Export.seen.find(ss, Export.put.path(put))), Export.put.path(put), ps, fs, ds, h)
    case Export.Step.Link{+put}:
      over_back(Export.held.digest(Export.seen.find(ss, Export.put.path(put))), Export.put.path(put), ps, fs, ds, h)
    case Export.Step.Keep{}:
      {==}
    case Export.Step.Mode{p, r}:
      {==}
    case Export.Step.Refuse{p, b}:
      {==}

# Every step that writes or links over a file is over bytes the copy's
# history can give back.
def steps_spare(xs: List<&2, Export.Step>, +ss: List<&2, Export.Seen>, +ps: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +h: {Export.steps.safe(xs, ss, False{}, Export.recs(ps, fs, ds)) == True{} : Bool}) -> {Export.steps.spare(xs, ss, fs, ds) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      ExportL.and_tt(Export.step.spares(x, ss, fs, ds), Export.steps.spare(rest, ss, fs, ds),
        step_spare(x, ss, ps, fs, ds, ExportL.and_l(Export.step.safe(x, ss, False{}, Export.recs(ps, fs, ds)), Export.steps.safe(rest, ss, False{}, Export.recs(ps, fs, ds)), h)),
        steps_spare(rest, ss, ps, fs, ds, ExportL.and_r(Export.step.safe(x, ss, False{}, Export.recs(ps, fs, ds)), Export.steps.safe(rest, ss, False{}, Export.recs(ps, fs, ds)), h)))

def seen_spared(s: Export.Seen, +ps: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, h: {Export.seen.recorded(s, False{}, Export.recs(ps, fs, ds)) == True{} : Bool}) -> {Export.seen.spared(s, fs, ds) == True{} : Bool}:
  match s:
    case Export.Seen.File{+p, +d, r}:
      recs_back(ps, fs, ds, p, d, h)
    case Export.Seen.Link{p, t}:
      {==}

def witness_spared(ss: List<&2, Export.Seen>, +p: String, +ps: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, h: {Export.witness(ss, p, False{}, Export.recs(ps, fs, ds)) == True{} : Bool}) -> {Export.spared.at(ss, p, fs, ds) == True{} : Bool}:
  match ss:
    case Nil{}:
      h
    case +s <> +rest:
      AL.or_cases({Export.spared.at(s <> rest, p, fs, ds) == True{} : Bool}, Bool.and(String.eq(Export.seen.path(s), p), Export.seen.recorded(s, False{}, Export.recs(ps, fs, ds))), Export.witness(rest, p, False{}, Export.recs(ps, fs, ds)), h,
        +l => AL.or_left(Bool.and(String.eq(Export.seen.path(s), p), Export.seen.spared(s, fs, ds)), Export.spared.at(rest, p, fs, ds),
          ExportL.and_tt(String.eq(Export.seen.path(s), p), Export.seen.spared(s, fs, ds),
            ExportL.and_l(String.eq(Export.seen.path(s), p), Export.seen.recorded(s, False{}, Export.recs(ps, fs, ds)), l),
            seen_spared(s, ps, fs, ds, ExportL.and_r(String.eq(Export.seen.path(s), p), Export.seen.recorded(s, False{}, Export.recs(ps, fs, ds)), l)))),
        r => AL.or_right(Bool.and(String.eq(Export.seen.path(s), p), Export.seen.spared(s, fs, ds)), Export.spared.at(rest, p, fs, ds), witness_spared(rest, p, ps, fs, ds, r)))

# Every file the folder's plan removes holds bytes the copy's history can
# give back, or is a link.
def removed_spare(rm: List<&2, String>, +ss: List<&2, Export.Seen>, +ps: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +h: {Export.removed.ok(rm, ss, False{}, Export.recs(ps, fs, ds)) == True{} : Bool}) -> {Export.removed.spare(rm, ss, fs, ds) == True{} : Bool}:
  match rm:
    case Nil{}:
      {==}
    case +p <> +rest:
      ExportL.and_tt(Export.spared.at(ss, p, fs, ds), Export.removed.spare(rest, ss, fs, ds),
        witness_spared(ss, p, ps, fs, ds, ExportL.and_l(Export.witness(ss, p, False{}, Export.recs(ps, fs, ds)), Export.removed.ok(rest, ss, False{}, Export.recs(ps, fs, ds)), h)),
        removed_spare(rest, ss, ps, fs, ds, ExportL.and_r(Export.witness(ss, p, False{}, Export.recs(ps, fs, ds)), Export.removed.ok(rest, ss, False{}, Export.recs(ps, fs, ds)), h)))

def of_spares(+xs: List<&2, Export.Step>, +rm: List<&2, String>, refused: List<&2, T.Split>, +ss: List<&2, Export.Seen>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, hs: {Export.steps.spare(xs, ss, fs, ds) == True{} : Bool}, hr: {Export.removed.spare(rm, ss, fs, ds) == True{} : Bool}) -> {Export.caught.spares(ss, fs, ds, Export.caught.of(xs, rm, refused)) == True{} : Bool}:
  match refused:
    case Nil{}:
      ExportL.and_tt(Export.steps.spare(xs, ss, fs, ds), Export.removed.spare(rm, ss, fs, ds), hs, hr)
    case x <> more:
      {==}

# Catching a copy's folder up writes over and takes away only bytes the
# copy's own history can give back.
def spares(+t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>, +bs: List<&2, Prune.Body>, +rules: List<&2, Folder.Scope>, +seen: List<&2, Export.Seen>, +walk: List<&2, T.Split>, +dirs: Set(), +others: Set(), +cfs: List<&2, Main.Full>, +cds: List<&2, Store.Doc>) -> {Export.caught.spares(seen, cfs, cds, Export.caught.r(t, fs, ds, id, pays, bs, rules, seen, walk, dirs, others, False{}, Export.recs(Export.seen.paths(seen), cfs, cds))) == True{} : Bool}:
  +ps = Export.placed(t)
  +rs = Export.recs(Export.seen.paths(seen), cfs, cds)
  +xs = Export.steps(Export.lay(ps, t, fs, ds, id, pays, bs), seen, dirs, others, False{}, rs)
  +rm = Export.removes(seen, Set.from_list(Export.placed.paths(ps)), False{}, rs)
  of_spares(xs, rm, List.concat(&2, T.Split, [Export.refused.tree(ps, Set.from_list(Export.directories(ps)), rules), Export.refused.walk(Export.placed.paths(ps), walk), Export.steps.refused(xs)]), seen, cfs, cds,
    steps_spare(xs, seen, Export.seen.paths(seen), cfs, cds, ExportL.steps_safe(Export.lay(ps, t, fs, ds, id, pays, bs), seen, dirs, others, False{}, rs)),
    removed_spare(rm, seen, Export.seen.paths(seen), cfs, cds, ExportL.removes_safe(seen, Set.from_list(Export.placed.paths(ps)), False{}, rs)))

# Where the folder's plan is made, a fresh export's folder is too
# ---------------------------------------------------------------

def not_refuse(x: Export.Step) -> Bool:
  match x:
    case Export.Step.Refuse{p, b}:
      False{}
    case _:
      True{}

def sr_head(x: Export.Step, -xs: List<&2, Export.Step>, h: {Export.steps.refused(x <> xs) == Nil{} : List<&2, T.Split>}) -> {not_refuse(x) == True{} : Bool}:
  match x:
    case Export.Step.Refuse{p, b}:
      Empty.absurd({False{} == True{} : Bool}, ExportL.cons_nil(T.Split, T.Split{p, b}, Export.steps.refused(xs), h))
    case Export.Step.Keep{}:
      {==}
    case Export.Step.Write{put, r}:
      {==}
    case Export.Step.Link{put}:
      {==}
    case Export.Step.Mode{p, r}:
      {==}

def sr_tail(x: Export.Step, -xs: List<&2, Export.Step>, h: {Export.steps.refused(x <> xs) == Nil{} : List<&2, T.Split>}) -> {Export.steps.refused(xs) == Nil{} : List<&2, T.Split>}:
  match x:
    case Export.Step.Refuse{p, b}:
      Empty.absurd({Export.steps.refused(xs) == Nil{} : List<&2, T.Split>}, ExportL.cons_nil(T.Split, T.Split{p, b}, Export.steps.refused(xs), h))
    case Export.Step.Keep{}:
      h
    case Export.Step.Write{put, r}:
      h
    case Export.Step.Link{put}:
      h
    case Export.Step.Mode{p, r}:
      h

# A plan none of whose steps refuses lays every path out.
def laid_clear(os: List<&2, Export.Outcome>, +ss: List<&2, Export.Seen>, +dirs: Set(), +others: Set(), +whole: Bool, +rs: List<&2, Export.Rec>, h: {Export.steps.refused(Export.steps(os, ss, dirs, others, whole, rs)) == Nil{} : List<&2, T.Split>}) -> {Export.refused.laid(os) == Nil{} : List<&2, T.Split>}:
  match os:
    case Nil{}:
      {==}
    case o <> +rest:
      match o:
        case Export.Outcome.Refused{+p, +b}:
          Empty.absurd({T.Split{p, b} <> Export.refused.laid(rest) == Nil{} : List<&2, T.Split>}, ExportL.cons_nil(T.Split, T.Split{p, b}, Export.steps.refused(Export.steps(rest, ss, dirs, others, whole, rs)), h))
        case Export.Outcome.Laid{+put}:
          laid_clear(rest, ss, dirs, others, whole, rs, sr_tail(Export.step.of(Export.Outcome.Laid{put}, ss, dirs, others, whole, rs), Export.steps(rest, ss, dirs, others, whole, rs), h))

def puts_paths(os: List<&2, Export.Outcome>, h: {Export.refused.laid(os) == Nil{} : List<&2, T.Split>}) -> {Export.put.paths(Export.puts(os)) == Export.outcome.paths(os) : List<&2, String>}:
  match os:
    case Nil{}:
      {==}
    case o <> +rest:
      match o:
        case Export.Outcome.Refused{+p, +b}:
          Empty.absurd({Export.put.paths(Export.puts(rest)) == Export.outcome.path(Export.Outcome.Refused{p, b}) <> Export.outcome.paths(rest) : List<&2, String>}, ExportL.cons_nil(T.Split, T.Split{p, b}, Export.refused.laid(rest), h))
        case Export.Outcome.Laid{+put}:
          %puts_paths(rest, h) : {Export.put.path(put) <> Export.put.paths(Export.puts(rest)) == Export.put.path(put) <> _ : List<&2, String>}
          {==}

# Each step lands
# ---------------

def seen_inj(+a: Export.Seen, -b: Export.Seen, e: {Some{a} == Some{b} : Maybe<&2, Export.Seen>}) -> {a == b : Export.Seen}:
  Equal.cong(Maybe<&2, Export.Seen>, Export.Seen, m => Maybe.default(&2, Export.Seen, m, a), Some{a}, Some{b}, e)

def find_step(c: Bool, +x: Export.Seen, +rest: List<&2, Export.Seen>, +path: String, +s: Export.Seen, ec: {String.eq(Export.seen.path(x), path) == c : Bool}, e: {Bool.pick(Maybe<&2, Export.Seen>, c, Some{x}, Export.seen.find(rest, path)) == Some{s} : Maybe<&2, Export.Seen>}, ih: {Export.seen.find(rest, path) == Some{s} : Maybe<&2, Export.Seen>} -> {String.eq(Export.seen.path(s), path) == True{} : Bool}) -> {String.eq(Export.seen.path(s), path) == True{} : Bool}:
  match c:
    case True{}:
      %seen_inj(x, s, e) : {String.eq(Export.seen.path(_), path) == True{} : Bool}
      ec
    case False{}:
      ih(e)

# What the walk is found to hold at a path is what it found there.
def find_path(ss: List<&2, Export.Seen>, +path: String, +s: Export.Seen, e: {Export.seen.find(ss, path) == Some{s} : Maybe<&2, Export.Seen>}) -> {String.eq(Export.seen.path(s), path) == True{} : Bool}:
  match ss:
    case Nil{}:
      Empty.absurd({String.eq(Export.seen.path(s), path) == True{} : Bool}, ExportL.none_some(Export.Seen, s, e))
    case +x <> +rest:
      find_step(String.eq(Export.seen.path(x), path), x, rest, path, s, {==}, e, h => find_path(rest, path, s, h))

def lays_refl(+put: Export.Put) -> {Export.seen.is(Some{Export.put.seen(put)}, Export.put.seen(put)) == True{} : Bool}:
  match put:
    case Export.Put.Text{+q, +text, +r}:
      ExportL.and_tt(String.eq(q, q), Bool.and(String.eq(Sha.digest(Utf8.encode(text)), Sha.digest(Utf8.encode(text))), Export.bool.same(r, r)), SL.eq_refl(q),
        ExportL.and_tt(String.eq(Sha.digest(Utf8.encode(text)), Sha.digest(Utf8.encode(text))), Export.bool.same(r, r), SL.eq_refl(Sha.digest(Utf8.encode(text))), ExportL.same_refl(r)))
    case Export.Put.Bytes{+q, f, +d, +r}:
      ExportL.and_tt(String.eq(q, q), Bool.and(String.eq(d, d), Export.bool.same(r, r)), SL.eq_refl(q),
        ExportL.and_tt(String.eq(d, d), Export.bool.same(r, r), SL.eq_refl(d), ExportL.same_refl(r)))
    case Export.Put.Link{+q, +t}:
      ExportL.and_tt(String.eq(q, q), String.eq(t, t), SL.eq_refl(q), SL.eq_refl(t))

# A write or a link lays its file where the file says.
def write_lands(+put: Export.Put, r: Bool, +found: Maybe<&2, Export.Seen>) -> {Export.seen.is(Export.step.after(Export.Step.Write{put, r}, Export.put.path(put), found), Export.put.seen(put)) == True{} : Bool}:
  %Equal.sym(Bool, String.eq(Export.put.path(put), Export.put.path(put)), True{}, SL.eq_refl(Export.put.path(put))) : {Export.seen.is(Bool.pick(Maybe<&2, Export.Seen>, _, Some{Export.put.seen(put)}, found), Export.put.seen(put)) == True{} : Bool}
  lays_refl(put)

def link_lands(+put: Export.Put, +found: Maybe<&2, Export.Seen>) -> {Export.seen.is(Export.step.after(Export.Step.Link{put}, Export.put.path(put), found), Export.put.seen(put)) == True{} : Bool}:
  %Equal.sym(Bool, String.eq(Export.put.path(put), Export.put.path(put)), True{}, SL.eq_refl(Export.put.path(put))) : {Export.seen.is(Bool.pick(Maybe<&2, Export.Seen>, _, Some{Export.put.seen(put)}, found), Export.put.seen(put)) == True{} : Bool}
  lays_refl(put)

def lands_goal(x: Export.Step, +q: String, +s: Maybe<&2, Export.Seen>, +want: Export.Seen) -> Type:
  {Export.seen.is(Export.step.after(x, q, s), want) == True{} : Bool}

def same_of_xor(a: Bool, b: Bool, e: {Bool.xor(a, b) == False{} : Bool}) -> {Export.bool.same(a, b) == True{} : Bool}:
  %Equal.sym(Bool, Bool.xor(a, b), False{}, e) : {Bool.not(_) == True{} : Bool}
  {==}

def mode_keep(x: Bool, +q: String, +g: String, +r: Bool, +p: String, +d: String, +runs: Bool, ex: {Bool.xor(runs, r) == x : Bool}, epq: {String.eq(p, q) == True{} : Bool}, edg: {String.eq(d, g) == True{} : Bool}) -> lands_goal(Bool.pick(Export.Step, x, Export.Step.Mode{q, r}, Export.Step.Keep{}), q, Some{Export.Seen.File{p, d, runs}}, Export.Seen.File{q, g, r}):
  match x:
    case True{}:
      %Equal.sym(Bool, String.eq(q, q), True{}, SL.eq_refl(q)) : {Export.seen.is(Bool.pick(Maybe<&2, Export.Seen>, _, Export.seen.moded(Some{Export.Seen.File{p, d, runs}}, r), Some{Export.Seen.File{p, d, runs}}), Export.Seen.File{q, g, r}) == True{} : Bool}
      ExportL.and_tt(String.eq(p, q), Bool.and(String.eq(d, g), Export.bool.same(r, r)), epq, ExportL.and_tt(String.eq(d, g), Export.bool.same(r, r), edg, ExportL.same_refl(r)))
    case False{}:
      ExportL.and_tt(String.eq(p, q), Bool.and(String.eq(d, g), Export.bool.same(runs, r)), epq, ExportL.and_tt(String.eq(d, g), Export.bool.same(runs, r), edg, same_of_xor(runs, r, ex)))

# Where the bytes there are the file's, the step keeps them or sets the
# mode; anything else is the step over them.
def same_lands(e: Bool, +q: String, +g: String, +r: Bool, +p: String, +d: String, +runs: Bool, over: Export.Step, ee: {String.eq(d, g) == e : Bool}, epq: {String.eq(p, q) == True{} : Bool}, hn: {not_refuse(Export.step.same(q, e, runs, r, over)) == True{} : Bool}, ho: {not_refuse(over) == True{} : Bool} -> lands_goal(over, q, Some{Export.Seen.File{p, d, runs}}, Export.Seen.File{q, g, r})) -> lands_goal(Export.step.same(q, e, runs, r, over), q, Some{Export.Seen.File{p, d, runs}}, Export.Seen.File{q, g, r}):
  match e:
    case True{}:
      mode_keep(Bool.xor(runs, r), q, g, r, p, d, runs, {==}, epq, ee)
    case False{}:
      ho(hn)

# Over bytes somebody may have: written or linked where recorded, refused
# otherwise.
def over_write(c: Bool, +put: Export.Put, +q: String, +want: Export.Seen, +found: Maybe<&2, Export.Seen>, +why: String, epath: {Export.put.path(put) == q : String}, eseen: {Export.put.seen(put) == want : Export.Seen}, hn: {not_refuse(Bool.pick(Export.Step, c, Export.Step.Write{put, True{}}, Export.Step.Refuse{q, why})) == True{} : Bool}) -> lands_goal(Bool.pick(Export.Step, c, Export.Step.Write{put, True{}}, Export.Step.Refuse{q, why}), q, found, want):
  match c:
    case True{}:
      %eseen : {Export.seen.is(Export.step.after(Export.Step.Write{put, True{}}, q, found), _) == True{} : Bool}
      %epath : {Export.seen.is(Export.step.after(Export.Step.Write{put, True{}}, _, found), Export.put.seen(put)) == True{} : Bool}
      write_lands(put, True{}, found)
    case False{}:
      Empty.absurd(lands_goal(Export.Step.Refuse{q, why}, q, found, want), Comp.false_true(hn))

def over_link(c: Bool, +put: Export.Put, +q: String, +want: Export.Seen, +found: Maybe<&2, Export.Seen>, +why: String, epath: {Export.put.path(put) == q : String}, eseen: {Export.put.seen(put) == want : Export.Seen}, hn: {not_refuse(Bool.pick(Export.Step, c, Export.Step.Link{put}, Export.Step.Refuse{q, why})) == True{} : Bool}) -> lands_goal(Bool.pick(Export.Step, c, Export.Step.Link{put}, Export.Step.Refuse{q, why}), q, found, want):
  match c:
    case True{}:
      %eseen : {Export.seen.is(Export.step.after(Export.Step.Link{put}, q, found), _) == True{} : Bool}
      %epath : {Export.seen.is(Export.step.after(Export.Step.Link{put}, _, found), Export.put.seen(put)) == True{} : Bool}
      link_lands(put, found)
    case False{}:
      Empty.absurd(lands_goal(Export.Step.Refuse{q, why}, q, found, want), Comp.false_true(hn))

def nr_plain(+put: Export.Put, +q: String, +g: String, +r: Bool, +d: String, +runs: Bool, +over: Export.Step, edig: {Export.put.digest(put) == g : String}, eruns: {Export.put.runs(put) == r : Bool}, hn: {not_refuse(Export.step.same(q, String.eq(d, Export.put.digest(put)), runs, Export.put.runs(put), over)) == True{} : Bool}) -> {not_refuse(Export.step.same(q, String.eq(d, g), runs, r, over)) == True{} : Bool}:
  %edig : {not_refuse(Export.step.same(q, String.eq(d, _), runs, r, over)) == True{} : Bool}
  %eruns : {not_refuse(Export.step.same(q, String.eq(d, Export.put.digest(put)), runs, _, over)) == True{} : Bool}
  hn

# A file of lines or of bytes, against whatever stands where it goes.
def plain_held(+put: Export.Put, +q: String, +g: String, +r: Bool, s: Maybe<&2, Export.Seen>, pr: Export.Probe, +ss: List<&2, Export.Seen>, +whole: Bool, +rs: List<&2, Export.Rec>, +epath: {Export.put.path(put) == q : String}, +edig: {Export.put.digest(put) == g : String}, +eruns: {Export.put.runs(put) == r : Bool}, +eseen: {Export.put.seen(put) == Export.Seen.File{q, g, r} : Export.Seen}, es: {Export.seen.find(ss, q) == s : Maybe<&2, Export.Seen>}, hn: {not_refuse(Export.step.held(put, q, False{}, s, pr, whole, rs)) == True{} : Bool}) -> lands_goal(Export.step.held(put, q, False{}, s, pr, whole, rs), q, s, Export.Seen.File{q, g, r}):
  match s:
    case None{}:
      match pr:
        case Export.Probe.Nothing{}:
          %eseen : {Export.seen.is(Export.step.after(Export.Step.Write{put, False{}}, q, None{}), _) == True{} : Bool}
          %epath : {Export.seen.is(Export.step.after(Export.Step.Write{put, False{}}, _, None{}), Export.put.seen(put)) == True{} : Bool}
          write_lands(put, False{}, None{})
        case Export.Probe.Dir{}:
          Empty.absurd(lands_goal(Export.Step.Refuse{q, "a directory stands there"}, q, None{}, Export.Seen.File{q, g, r}), Comp.false_true(hn))
        case Export.Probe.Other{}:
          Empty.absurd(lands_goal(Export.Step.Refuse{q, "something stands there the walk did not offer"}, q, None{}, Export.Seen.File{q, g, r}), Comp.false_true(hn))
    case Some{Export.Seen.Link{p, t}}:
      Empty.absurd(lands_goal(Export.Step.Refuse{q, "a symbolic link stands there"}, q, Some{Export.Seen.Link{p, t}}, Export.Seen.File{q, g, r}), Comp.false_true(hn))
    case Some{Export.Seen.File{+p, +d, +runs}}:
      %Equal.sym(String, Export.put.digest(put), g, edig) : {Export.seen.is(Export.step.after(Export.step.same(q, String.eq(d, _), runs, Export.put.runs(put), Bool.pick(Export.Step, Export.recorded(whole, rs, q, d), Export.Step.Write{put, True{}}, Export.Step.Refuse{q, Export.UNRECORDED()})), q, Some{Export.Seen.File{p, d, runs}}), Export.Seen.File{q, g, r}) == True{} : Bool}
      %Equal.sym(Bool, Export.put.runs(put), r, eruns) : {Export.seen.is(Export.step.after(Export.step.same(q, String.eq(d, g), runs, _, Bool.pick(Export.Step, Export.recorded(whole, rs, q, d), Export.Step.Write{put, True{}}, Export.Step.Refuse{q, Export.UNRECORDED()})), q, Some{Export.Seen.File{p, d, runs}}), Export.Seen.File{q, g, r}) == True{} : Bool}
      same_lands(String.eq(d, g), q, g, r, p, d, runs, Bool.pick(Export.Step, Export.recorded(whole, rs, q, d), Export.Step.Write{put, True{}}, Export.Step.Refuse{q, Export.UNRECORDED()}), {==}, find_path(ss, q, Export.Seen.File{p, d, runs}, es),
        nr_plain(put, q, g, r, d, runs, Bool.pick(Export.Step, Export.recorded(whole, rs, q, d), Export.Step.Write{put, True{}}, Export.Step.Refuse{q, Export.UNRECORDED()}), edig, eruns, hn),
        h2 => over_write(Export.recorded(whole, rs, q, d), put, q, Export.Seen.File{q, g, r}, Some{Export.Seen.File{p, d, runs}}, Export.UNRECORDED(), epath, eseen, h2))

def link_keep(c: Bool, +put: Export.Put, +q: String, +g: String, +p: String, +t: String, ec: {String.eq(t, g) == c : Bool}, epq: {String.eq(p, q) == True{} : Bool}, +epath: {Export.put.path(put) == q : String}, +eseen: {Export.put.seen(put) == Export.Seen.Link{q, g} : Export.Seen}, hn: {not_refuse(Bool.pick(Export.Step, c, Export.Step.Keep{}, Export.Step.Link{put})) == True{} : Bool}) -> lands_goal(Bool.pick(Export.Step, c, Export.Step.Keep{}, Export.Step.Link{put}), q, Some{Export.Seen.Link{p, t}}, Export.Seen.Link{q, g}):
  match c:
    case True{}:
      ExportL.and_tt(String.eq(p, q), String.eq(t, g), epq, ec)
    case False{}:
      %eseen : {Export.seen.is(Export.step.after(Export.Step.Link{put}, q, Some{Export.Seen.Link{p, t}}), _) == True{} : Bool}
      %epath : {Export.seen.is(Export.step.after(Export.Step.Link{put}, _, Some{Export.Seen.Link{p, t}}), Export.put.seen(put)) == True{} : Bool}
      link_lands(put, Some{Export.Seen.Link{p, t}})

def nr_link(+put: Export.Put, +g: String, +t: String, etarget: {Export.put.target(put) == g : String}, hn: {not_refuse(Bool.pick(Export.Step, String.eq(t, Export.put.target(put)), Export.Step.Keep{}, Export.Step.Link{put})) == True{} : Bool}) -> {not_refuse(Bool.pick(Export.Step, String.eq(t, g), Export.Step.Keep{}, Export.Step.Link{put})) == True{} : Bool}:
  %etarget : {not_refuse(Bool.pick(Export.Step, String.eq(t, _), Export.Step.Keep{}, Export.Step.Link{put})) == True{} : Bool}
  hn

def link_target(+put: Export.Put, +g: String, +t: String, +q: String, +p: String, etarget: {Export.put.target(put) == g : String}, h: lands_goal(Bool.pick(Export.Step, String.eq(t, g), Export.Step.Keep{}, Export.Step.Link{put}), q, Some{Export.Seen.Link{p, t}}, Export.Seen.Link{q, g})) -> lands_goal(Bool.pick(Export.Step, String.eq(t, Export.put.target(put)), Export.Step.Keep{}, Export.Step.Link{put}), q, Some{Export.Seen.Link{p, t}}, Export.Seen.Link{q, g}):
  %Equal.sym(String, Export.put.target(put), g, etarget) : {Export.seen.is(Export.step.after(Bool.pick(Export.Step, String.eq(t, _), Export.Step.Keep{}, Export.Step.Link{put}), q, Some{Export.Seen.Link{p, t}}), Export.Seen.Link{q, g}) == True{} : Bool}
  h

# A link, against whatever stands where it goes.
def link_held(+put: Export.Put, +q: String, +g: String, s: Maybe<&2, Export.Seen>, pr: Export.Probe, +ss: List<&2, Export.Seen>, +whole: Bool, +rs: List<&2, Export.Rec>, +epath: {Export.put.path(put) == q : String}, +etarget: {Export.put.target(put) == g : String}, +eseen: {Export.put.seen(put) == Export.Seen.Link{q, g} : Export.Seen}, es: {Export.seen.find(ss, q) == s : Maybe<&2, Export.Seen>}, hn: {not_refuse(Export.step.held(put, q, True{}, s, pr, whole, rs)) == True{} : Bool}) -> lands_goal(Export.step.held(put, q, True{}, s, pr, whole, rs), q, s, Export.Seen.Link{q, g}):
  match s:
    case None{}:
      match pr:
        case Export.Probe.Nothing{}:
          %eseen : {Export.seen.is(Export.step.after(Export.Step.Link{put}, q, None{}), _) == True{} : Bool}
          %epath : {Export.seen.is(Export.step.after(Export.Step.Link{put}, _, None{}), Export.put.seen(put)) == True{} : Bool}
          link_lands(put, None{})
        case Export.Probe.Dir{}:
          Empty.absurd(lands_goal(Export.Step.Refuse{q, "a directory stands there"}, q, None{}, Export.Seen.Link{q, g}), Comp.false_true(hn))
        case Export.Probe.Other{}:
          Empty.absurd(lands_goal(Export.Step.Refuse{q, Export.UNRECORDED()}, q, None{}, Export.Seen.Link{q, g}), Comp.false_true(hn))
    case Some{Export.Seen.Link{+p, +t}}:
      link_target(put, g, t, q, p, etarget,
        link_keep(String.eq(t, g), put, q, g, p, t, {==}, find_path(ss, q, Export.Seen.Link{p, t}, es), epath, eseen, nr_link(put, g, t, etarget, hn)))
    case Some{Export.Seen.File{+p, +d, +runs}}:
      over_link(Export.recorded(whole, rs, q, d), put, q, Export.Seen.Link{q, g}, Some{Export.Seen.File{p, d, runs}}, Export.UNRECORDED(), epath, eseen, hn)

# Whatever stands where a file goes, a step that does not refuse leaves the
# file there.
def held_lands(put: Export.Put, s: Maybe<&2, Export.Seen>, pr: Export.Probe, +ss: List<&2, Export.Seen>, +whole: Bool, +rs: List<&2, Export.Rec>, es: {Export.seen.find(ss, Export.put.path(put)) == s : Maybe<&2, Export.Seen>}, hn: {not_refuse(Export.step.held(put, Export.put.path(put), Export.is.link(put), s, pr, whole, rs)) == True{} : Bool}) -> lands_goal(Export.step.held(put, Export.put.path(put), Export.is.link(put), s, pr, whole, rs), Export.put.path(put), s, Export.put.seen(put)):
  match put:
    case Export.Put.Text{+q, +text, +r}:
      plain_held(Export.Put.Text{q, text, r}, q, Sha.digest(Utf8.encode(text)), r, s, pr, ss, whole, rs, {==}, {==}, {==}, {==}, es, hn)
    case Export.Put.Bytes{+q, +f, +d, +r}:
      plain_held(Export.Put.Bytes{q, f, d, r}, q, d, r, s, pr, ss, whole, rs, {==}, {==}, {==}, {==}, es, hn)
    case Export.Put.Link{+q, +g}:
      link_held(Export.Put.Link{q, g}, q, g, s, pr, ss, whole, rs, {==}, {==}, {==}, es, hn)

# Where no step refuses, each file a fresh export lays is where its step
# leaves it, one step a file.
def lands_all(os: List<&2, Export.Outcome>, +ss: List<&2, Export.Seen>, +dirs: Set(), +others: Set(), +whole: Bool, +rs: List<&2, Export.Rec>, +h: {Export.steps.refused(Export.steps(os, ss, dirs, others, whole, rs)) == Nil{} : List<&2, T.Split>}) -> {Export.lands(Export.puts(os), Export.steps(os, ss, dirs, others, whole, rs), ss) == True{} : Bool}:
  match os:
    case Nil{}:
      {==}
    case o <> +rest:
      match o:
        case Export.Outcome.Refused{+p, +b}:
          Empty.absurd({Export.lands(Export.puts(rest), Export.Step.Refuse{p, b} <> Export.steps(rest, ss, dirs, others, whole, rs), ss) == True{} : Bool}, ExportL.cons_nil(T.Split, T.Split{p, b}, Export.steps.refused(Export.steps(rest, ss, dirs, others, whole, rs)), h))
        case Export.Outcome.Laid{+put}:
          ExportL.and_tt(Export.seen.is(Export.step.after(Export.step.of(Export.Outcome.Laid{put}, ss, dirs, others, whole, rs), Export.put.path(put), Export.seen.find(ss, Export.put.path(put))), Export.put.seen(put)), Export.lands(Export.puts(rest), Export.steps(rest, ss, dirs, others, whole, rs), ss),
            held_lands(put, Export.seen.find(ss, Export.put.path(put)), Export.probe.of(Arrange.has(dirs, Export.put.path(put)), Arrange.has(others, Export.put.path(put))), ss, whole, rs, {==}, sr_head(Export.step.of(Export.Outcome.Laid{put}, ss, dirs, others, whole, rs), Export.steps(rest, ss, dirs, others, whole, rs), h)),
            lands_all(rest, ss, dirs, others, whole, rs, sr_tail(Export.step.of(Export.Outcome.Laid{put}, ss, dirs, others, whole, rs), Export.steps(rest, ss, dirs, others, whole, rs), h)))

# Nothing removed is a path the tree places
# -----------------------------------------

def found_hv(r: Set() & Bool) -> {Arrange.found(r) == ML.hv(Unit, r) : Bool}:
  match r:
    case (m, b):
      {==}

# A set built from a list holds exactly the list's strings.
def has_member(+xs: List<&2, String>, +k: String) -> {Arrange.has(Set.from_list(xs), k) == Rev.member(xs, k) : Bool}:
  Equal.trans(Bool, Arrange.has(Set.from_list(xs), k), ML.hv(Unit, Set.has(Set.from_list(xs), k)), Rev.member(xs, k), found_hv(Set.has(Set.from_list(xs), k)), ML.set_from_list(xs, k))

def rm_step(c: Bool, +p: String, +later: List<&2, String>, +names: List<&2, String>, -g: Bool, ec: {Bool.and(Bool.not(Arrange.has(Set.from_list(names), p)), g) == c : Bool}, ih: {Export.none.of(later, names) == True{} : Bool}) -> {Export.none.of(Tree.keep(~String, c, p, later), names) == True{} : Bool}:
  match c:
    case True{}:
      ExportL.and_tt(Bool.not(Rev.member(names, p)), Export.none.of(later, names),
        (%has_member(names, p) : {Bool.not(_) == True{} : Bool}
          ExportL.and_l(Bool.not(Arrange.has(Set.from_list(names), p)), g, ec)),
        ih)
    case False{}:
      ih

# What the plan removes is none of the paths it was told the tree places.
def removes_none(ss: List<&2, Export.Seen>, +names: List<&2, String>, +whole: Bool, +rs: List<&2, Export.Rec>) -> {Export.none.of(Export.removes(ss, Set.from_list(names), whole, rs), names) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +rest:
      rm_step(Bool.and(Bool.not(Arrange.has(Set.from_list(names), Export.seen.path(s))), Export.seen.gone(s, whole, rs)), Export.seen.path(s), Export.removes(rest, Set.from_list(names), whole, rs), names, Export.seen.gone(s, whole, rs), {==}, removes_none(rest, names, whole, rs))

# The whole plan
# --------------

def app_nil_r(-A: Data, xs: List<&2, A>, -ys: List<&2, A>, e: {List.append(&2, A, xs, ys) == Nil{} : List<&2, A>}) -> {ys == Nil{} : List<&2, A>}:
  match xs:
    case Nil{}:
      e
    case x <> r:
      Empty.absurd({ys == Nil{} : List<&2, A>}, ExportL.cons_nil(A, x, List.append(&2, A, r, ys), e))

def lands_of(refused: List<&2, T.Split>, +ps: List<&2, Export.Placed>, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>, +bs: List<&2, Prune.Body>, +rules: List<&2, Folder.Scope>, +seen: List<&2, Export.Seen>, +walk: List<&2, T.Split>, +dirs: Set(), +others: Set(), +whole: Bool, +rs: List<&2, Export.Rec>, +er: {List.concat(&2, T.Split, [Export.refused.tree(ps, Set.from_list(Export.directories(ps)), rules), Export.refused.walk(Export.placed.paths(ps), walk), Export.steps.refused(Export.steps(Export.lay(ps, t, fs, ds, id, pays, bs), seen, dirs, others, whole, rs))]) == refused : List<&2, T.Split>}) -> {Export.caught.lands(seen, Export.caught.of(Export.steps(Export.lay(ps, t, fs, ds, id, pays, bs), seen, dirs, others, whole, rs), Export.removes(seen, Set.from_list(Export.placed.paths(ps)), whole, rs), refused), Export.laid.r(Export.lay(ps, t, fs, ds, id, pays, bs), List.append(&2, T.Split, Export.refused.tree(ps, Set.from_list(Export.directories(ps)), rules), Export.refused.laid(Export.lay(ps, t, fs, ds, id, pays, bs))))) == True{} : Bool}:
  match refused:
    case x <> more:
      {==}
    case Nil{}:
      +os = Export.lay(ps, t, fs, ds, id, pays, bs)
      +a = Export.refused.tree(ps, Set.from_list(Export.directories(ps)), rules)
      +w = Export.refused.walk(Export.placed.paths(ps), walk)
      +sr = Export.steps.refused(Export.steps(os, seen, dirs, others, whole, rs))
      +ea = ExportL.app_nil(T.Split, a, List.append(&2, T.Split, w, List.append(&2, T.Split, sr, Nil{})), er)
      +e1 = app_nil_r(T.Split, a, List.append(&2, T.Split, w, List.append(&2, T.Split, sr, Nil{})), er)
      +e2 = app_nil_r(T.Split, w, List.append(&2, T.Split, sr, Nil{}), e1)
      +es = ExportL.app_nil(T.Split, sr, Nil{}, e2)
      +el = laid_clear(os, seen, dirs, others, whole, rs, es)
      %Equal.sym(List<&2, T.Split>, a, Nil{}, ea) : {Export.caught.lands(seen, Done{Export.Caught{Export.steps(os, seen, dirs, others, whole, rs), Export.removes(seen, Set.from_list(Export.placed.paths(ps)), whole, rs)}}, Export.laid.r(os, List.append(&2, T.Split, _, Export.refused.laid(os)))) == True{} : Bool}
      %Equal.sym(List<&2, T.Split>, Export.refused.laid(os), Nil{}, el) : {Export.caught.lands(seen, Done{Export.Caught{Export.steps(os, seen, dirs, others, whole, rs), Export.removes(seen, Set.from_list(Export.placed.paths(ps)), whole, rs)}}, Export.laid.r(os, List.append(&2, T.Split, Nil{}, _))) == True{} : Bool}
      %Equal.trans(List<&2, String>, Export.placed.paths(ps), Export.outcome.paths(os), Export.put.paths(Export.puts(os)), Equal.sym(List<&2, String>, Export.outcome.paths(os), Export.placed.paths(ps), ExportL.laid(ps, t, fs, ds, id, pays, bs)), Equal.sym(List<&2, String>, Export.put.paths(Export.puts(os)), Export.outcome.paths(os), puts_paths(os, el))) : {Bool.and(Export.lands(Export.puts(os), Export.steps(os, seen, dirs, others, whole, rs), seen), Export.none.of(Export.removes(seen, Set.from_list(Export.placed.paths(ps)), whole, rs), _)) == True{} : Bool}
      ExportL.and_tt(Export.lands(Export.puts(os), Export.steps(os, seen, dirs, others, whole, rs), seen), Export.none.of(Export.removes(seen, Set.from_list(Export.placed.paths(ps)), whole, rs), Export.placed.paths(ps)),
        lands_all(os, seen, dirs, others, whole, rs, es),
        removes_none(seen, Export.placed.paths(ps), whole, rs))

# Catching a copy's folder up leaves every path the target's tree places
# holding what a fresh export lays there, and removes none of them.
def catch_lands(+t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>, +bs: List<&2, Prune.Body>, +rules: List<&2, Folder.Scope>, +seen: List<&2, Export.Seen>, +walk: List<&2, T.Split>, +dirs: Set(), +others: Set(), +whole: Bool, +rs: List<&2, Export.Rec>) -> {Export.caught.lands(seen, Export.caught.r(t, fs, ds, id, pays, bs, rules, seen, walk, dirs, others, whole, rs), Export.folder.r(t, fs, ds, id, pays, bs, rules)) == True{} : Bool}:
  lands_of(List.concat(&2, T.Split, [Export.refused.tree(Export.placed(t), Set.from_list(Export.directories(Export.placed(t))), rules), Export.refused.walk(Export.placed.paths(Export.placed(t)), walk), Export.steps.refused(Export.steps(Export.lay(Export.placed(t), t, fs, ds, id, pays, bs), seen, dirs, others, whole, rs))]), Export.placed(t), t, fs, ds, id, pays, bs, rules, seen, walk, dirs, others, whole, rs, {==})
