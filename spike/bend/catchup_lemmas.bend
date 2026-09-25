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
