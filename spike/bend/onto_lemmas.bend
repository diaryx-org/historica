# What `export` promises of a copy's store it brings up to date. It writes
# only into a copy related to this store holding nothing this store has
# not heard of.
import Base
import ./export.bend as Export
import ./receive.bend as Receive
import ./receive_lemmas.bend as ReceiveL
import ./catchup_lemmas.bend as CatchL
import ./export_lemmas.bend as ExportL
import ./commands.bend as Main
import ./revision.bend as Rev
import ./text.bend as T
import ./sort_lemmas.bend as SortL
import ./anchor_lemmas.bend as AL
import ./arrange.bend as Arrange
import ./prune.bend as Prune
import ./tree.bend as Tree
import ./store.bend as Store
import ./bookmark.bend as Bm
import ./graph_lemmas.bend as GL
import ./forget_lemmas.bend as ForgetL
import ./status_lemmas.bend as StatusL
import ./string_lemmas.bend as SL
import ./composition_lemmas.bend as Comp

# Which copy an export writes into
# --------------------------------

# What a copy's revision is found among: the digests this store holds and
# those its revisions name.
def edges_named(fs: List<&2, Main.Full>, +id: String) -> {Rev.member(Export.named.edges(fs), id) == Export.named.edge(fs, id) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Main.Full{i, c, +parents, +supersedes, a, w, rb, rv, facts, m} <> +rest:
      %Equal.sym(Bool, Rev.member(List.append(&2, String, parents, List.append(&2, String, supersedes, List.append(&2, String, Export.named.edges(rest), Nil{}))), id), Bool.or(Rev.member(parents, id), Rev.member(List.append(&2, String, supersedes, List.append(&2, String, Export.named.edges(rest), Nil{})), id)), ReceiveL.member_app(parents, List.append(&2, String, supersedes, List.append(&2, String, Export.named.edges(rest), Nil{})), id)) : {_ == Bool.or(Bool.or(Rev.member(parents, id), Rev.member(supersedes, id)), Export.named.edge(rest, id)) : Bool}
      %Equal.sym(Bool, Rev.member(List.append(&2, String, supersedes, List.append(&2, String, Export.named.edges(rest), Nil{})), id), Bool.or(Rev.member(supersedes, id), Rev.member(List.append(&2, String, Export.named.edges(rest), Nil{}), id)), ReceiveL.member_app(supersedes, List.append(&2, String, Export.named.edges(rest), Nil{}), id)) : {Bool.or(Rev.member(parents, id), _) == Bool.or(Bool.or(Rev.member(parents, id), Rev.member(supersedes, id)), Export.named.edge(rest, id)) : Bool}
      %Equal.sym(List<&2, String>, List.append(&2, String, Export.named.edges(rest), Nil{}), Export.named.edges(rest), SortL.lapp_nil(String, Export.named.edges(rest))) : {Bool.or(Rev.member(parents, id), Bool.or(Rev.member(supersedes, id), Rev.member(_, id))) == Bool.or(Bool.or(Rev.member(parents, id), Rev.member(supersedes, id)), Export.named.edge(rest, id)) : Bool}
      %Equal.sym(Bool, Rev.member(Export.named.edges(rest), id), Export.named.edge(rest, id), edges_named(rest, id)) : {Bool.or(Rev.member(parents, id), Bool.or(Rev.member(supersedes, id), _)) == Bool.or(Bool.or(Rev.member(parents, id), Rev.member(supersedes, id)), Export.named.edge(rest, id)) : Bool}
      ReceiveL.or_assoc(Rev.member(parents, id), Rev.member(supersedes, id), Export.named.edge(rest, id))

def heard_is(+fs: List<&2, Main.Full>, +id: String) -> {Arrange.has(Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs))), id) == Bool.or(Rev.member(Main.ids(fs), id), Export.named.edge(fs, id)) : Bool}:
  Equal.trans(Bool, Arrange.has(Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs))), id), Rev.member(List.append(&2, String, Main.ids(fs), Export.named.edges(fs)), id), Bool.or(Rev.member(Main.ids(fs), id), Export.named.edge(fs, id)),
    CatchL.has_member(List.append(&2, String, Main.ids(fs), Export.named.edges(fs)), id),
    Equal.trans(Bool, Rev.member(List.append(&2, String, Main.ids(fs), Export.named.edges(fs)), id), Bool.or(Rev.member(Main.ids(fs), id), Rev.member(Export.named.edges(fs), id)), Bool.or(Rev.member(Main.ids(fs), id), Export.named.edge(fs, id)),
      ReceiveL.member_app(Main.ids(fs), Export.named.edges(fs), id),
      Equal.cong(Bool, Bool, x => Bool.or(Rev.member(Main.ids(fs), id), x), Rev.member(Export.named.edges(fs), id), Export.named.edge(fs, id), edges_named(fs, id))))

def stranger_step(c: Bool, +f: Main.Full, +rest: List<&2, Main.Full>, +fs: List<&2, Main.Full>, +into: String, ec: {Arrange.has(Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs))), Main.id_of(f)) == c : Bool}, ih: {Result.is_done(&2, &2, Main.Refused, Unit, Export.stranger.r(into, Export.stranger(rest, Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs)))))) == Export.heard.all(rest, fs) : Bool}) -> {Result.is_done(&2, &2, Main.Refused, Unit, Export.stranger.r(into, Bool.pick(Maybe<&2, String>, c, Export.stranger(rest, Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs)))), Some{Main.id_of(f)}))) == Bool.and(Bool.or(Rev.member(Main.ids(fs), Main.id_of(f)), Export.named.edge(fs, Main.id_of(f))), Export.heard.all(rest, fs)) : Bool}:
  match c:
    case True{}:
      %Equal.trans(Bool, True{}, Arrange.has(Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs))), Main.id_of(f)), Bool.or(Rev.member(Main.ids(fs), Main.id_of(f)), Export.named.edge(fs, Main.id_of(f))), Equal.sym(Bool, Arrange.has(Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs))), Main.id_of(f)), True{}, ec), heard_is(fs, Main.id_of(f))) : {Result.is_done(&2, &2, Main.Refused, Unit, Export.stranger.r(into, Export.stranger(rest, Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs)))))) == Bool.and(_, Export.heard.all(rest, fs)) : Bool}
      ih
    case False{}:
      %Equal.trans(Bool, False{}, Arrange.has(Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs))), Main.id_of(f)), Bool.or(Rev.member(Main.ids(fs), Main.id_of(f)), Export.named.edge(fs, Main.id_of(f))), Equal.sym(Bool, Arrange.has(Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs))), Main.id_of(f)), False{}, ec), heard_is(fs, Main.id_of(f))) : {False{} == Bool.and(_, Export.heard.all(rest, fs)) : Bool}
      {==}

# The copy holds no revision this store has not heard of exactly where no
# stranger is found in it.
def stranger_done(cfs: List<&2, Main.Full>, +fs: List<&2, Main.Full>, +into: String) -> {Result.is_done(&2, &2, Main.Refused, Unit, Export.stranger.r(into, Export.stranger(cfs, Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs)))))) == Export.heard.all(cfs, fs) : Bool}:
  match cfs:
    case Nil{}:
      {==}
    case +f <> +rest:
      stranger_step(Arrange.has(Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs))), Main.id_of(f)), f, rest, fs, into, {==}, stranger_done(rest, fs, into))

def rel_step(b: Bool, +into: String, +fs: List<&2, Main.Full>, +cfs: List<&2, Main.Full>) -> {Result.is_done(&2, &2, Main.Refused, Unit, Result.bind(&2, &2, Main.Refused, Unit, Unit, Bool.pick(Result<&2, &2, Main.Refused, Unit>, b, Done{Unit{}}, Fail{Main.Refused{1, Export.UNRELATED(into)}}), u => Export.stranger.r(into, Export.stranger(cfs, Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs))))))) == Bool.and(b, Export.heard.all(cfs, fs)) : Bool}:
  match b:
    case True{}:
      stranger_done(cfs, fs, into)
    case False{}:
      {==}

# An export writes into a copy exactly where the copy is related to this
# store and holds no revision this store has not heard of.
def copy_done(+into: String, +fs: List<&2, Main.Full>, +cfs: List<&2, Main.Full>) -> {Result.is_done(&2, &2, Main.Refused, Unit, Export.copy.r(into, fs, cfs)) == Bool.and(Receive.related(fs, cfs), Export.heard.all(cfs, fs)) : Bool}:
  rel_step(Receive.related(fs, cfs), into, fs, cfs)

# The rules an update gives a copy
# --------------------------------

def unstated_step(c: Bool, +f: String, +line: String, +l: String, +rest: List<&2, Receive.Ruled>, +stated: Set(), hl: {Bool.not(String.starts_with(line, "private")) == True{} : Bool}, ih: {ExportL.all_shared(Export.rules.unstated(rest, stated)) == True{} : Bool}) -> {ExportL.all_shared(Tree.keep(~Receive.Ruled, c, Receive.Ruled{f, line, l}, Export.rules.unstated(rest, stated))) == True{} : Bool}:
  match c:
    case True{}:
      ExportL.and_tt(Bool.not(String.starts_with(line, "private")), ExportL.all_shared(Export.rules.unstated(rest, stated)), hl, ih)
    case False{}:
      ih

# Leaving out what a copy states keeps every rule left shared.
def unstated_shared(rs: List<&2, Receive.Ruled>, +stated: Set(), +h: {ExportL.all_shared(rs) == True{} : Bool}) -> {ExportL.all_shared(Export.rules.unstated(rs, stated)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Receive.Ruled{+f, +line, +l} <> +rest:
      unstated_step(Bool.not(Arrange.has(stated, line)), f, line, l, rest, stated,
        ExportL.and_l(Bool.not(String.starts_with(line, "private")), ExportL.all_shared(rest), h),
        unstated_shared(rest, stated, ExportL.and_r(Bool.not(String.starts_with(line, "private")), ExportL.all_shared(rest), h)))

# Every rule file an update gives a copy states a shared rule.
def added_shared(+held: List<&2, Main.Full>, +t: Tree.Tree(), +ds: List<&2, Store.Doc>, +ps: List<&2, T.Split>, +bodies: List<&2, Prune.Body>, +rs: List<&2, Receive.Ruled>, +bs: List<&2, Bm.Bookmark>, +claims: List<&2, T.Split>, +cst: Prune.Stored, +retired: Set()) -> {Export.lines.shared(Export.rules.added(Export.plan.of(held, t, ds, ps, bodies, rs, bs, claims), cst, retired)) == True{} : Bool}:
  ExportL.written_shared(Export.rules.unstated(Export.rules.shared(rs), Set.from_list(Export.rules.lines(Receive.ruled(Export.keep.unretired(Receive.stored.rules(cst), retired))))), Set.from_list(Export.rule.labels(Export.keep.unretired(Receive.stored.rules(cst), retired))), Nil{}, Nil{},
    unstated_shared(Export.rules.shared(rs), Set.from_list(Export.rules.lines(Receive.ruled(Export.keep.unretired(Receive.stored.rules(cst), retired)))), ExportL.shared_all(rs)))

# What an update leaves a copy holding
# ------------------------------------

def keep_mem(c: Bool, +x: String, +rest: List<&2, String>, +d: String, h: {Rev.member(Tree.keep(~String, c, x, rest), d) == True{} : Bool}) -> {Bool.or(String.eq(x, d), Rev.member(rest, d)) == True{} : Bool}:
  match c:
    case True{}:
      h
    case False{}:
      AL.or_right(String.eq(x, d), Rev.member(rest, d), h)

def revs_has(ss: List<&2, T.Split>, +set: Set(), +d: String, h: {Rev.member(Export.revs.holds(ss, set), d) == True{} : Bool}) -> {Export.split.has(ss, d) == True{} : Bool}:
  match ss:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(h))
    case T.Split{+p, +x} <> +rest:
      AL.or_cases({Export.split.has(T.Split{p, x} <> rest, d) == True{} : Bool}, String.eq(x, d), Rev.member(Export.revs.holds(rest, set), d),
        keep_mem(Arrange.has(set, x), x, Export.revs.holds(rest, set), d, h),
        l => AL.or_left(String.eq(x, d), Export.split.has(rest, d), l),
        r => AL.or_right(String.eq(x, d), Export.split.has(rest, d), revs_has(rest, set, d, r)))

def bodies_has(bs: List<&2, Prune.Body>, +fset: Set(), +docs: Set(), +content: Set(), +d: String, h: {Rev.member(Export.bodies.holds(bs, fset, docs, content), d) == True{} : Bool}) -> {Export.body.has(bs, d) == True{} : Bool}:
  match bs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(h))
    case Prune.Body{+p, +i, +ok, +f} <> +rest:
      AL.or_cases({Export.body.has(Prune.Body{p, i, ok, f} <> rest, d) == True{} : Bool}, String.eq(i, d), Rev.member(Export.bodies.holds(rest, fset, docs, content), d),
        keep_mem(Bool.and(Bool.not(Arrange.has(fset, i)), Export.body.kept(i, f, docs, content)), i, Export.bodies.holds(rest, fset, docs, content), d, h),
        l => AL.or_left(String.eq(i, d), Export.body.has(rest, d), l),
        r => AL.or_right(String.eq(i, d), Export.body.has(rest, d), bodies_has(rest, fset, docs, content, d, r)))

def pays_has(ss: List<&2, T.Split>, +fset: Set(), +pays: Set(), +d: String, h: {Rev.member(Export.pays.holds(ss, fset, pays), d) == True{} : Bool}) -> {Export.split.has(ss, d) == True{} : Bool}:
  match ss:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(h))
    case T.Split{+p, +x} <> +rest:
      AL.or_cases({Export.split.has(T.Split{p, x} <> rest, d) == True{} : Bool}, String.eq(x, d), Rev.member(Export.pays.holds(rest, fset, pays), d),
        keep_mem(Bool.and(Bool.not(Arrange.has(fset, x)), Arrange.has(pays, x)), x, Export.pays.holds(rest, fset, pays), d, h),
        l => AL.or_left(String.eq(x, d), Export.split.has(rest, d), l),
        r => AL.or_right(String.eq(x, d), Export.split.has(rest, d), pays_has(rest, fset, pays, d, r)))

# What an update counts as held is a file the copy's store holds.
def holds_has(+cst: Prune.Stored, +revset: Set(), +fset: Set(), +docs: Set(), +content: Set(), +pays: Set(), +d: String, h: {Rev.member(List.concat(&2, String, [Export.revs.holds(Export.stored.revs(cst), revset), Export.bodies.holds(Receive.stored.bodies(cst), fset, docs, content), Export.pays.holds(Receive.stored.payloads(cst), fset, pays)]), d) == True{} : Bool}) -> {Export.copy.has(cst, d) == True{} : Bool}:
  +a = Export.revs.holds(Export.stored.revs(cst), revset)
  +b = Export.bodies.holds(Receive.stored.bodies(cst), fset, docs, content)
  +c = Export.pays.holds(Receive.stored.payloads(cst), fset, pays)
  +sr = Export.split.has(Export.stored.revs(cst), d)
  +sb = Export.body.has(Receive.stored.bodies(cst), d)
  +sp = Export.split.has(Receive.stored.payloads(cst), d)
  AL.or_cases({Bool.or(sr, Bool.or(sb, sp)) == True{} : Bool}, Rev.member(a, d), Rev.member(List.append(&2, String, b, List.append(&2, String, c, Nil{})), d),
    GL.append_mem(a, List.append(&2, String, b, List.append(&2, String, c, Nil{})), d, h),
    l => AL.or_left(sr, Bool.or(sb, sp), revs_has(Export.stored.revs(cst), revset, d, l)),
    r => AL.or_cases({Bool.or(sr, Bool.or(sb, sp)) == True{} : Bool}, Rev.member(b, d), Rev.member(List.append(&2, String, c, Nil{}), d),
      GL.append_mem(b, List.append(&2, String, c, Nil{}), d, r),
      rl => AL.or_right(sr, Bool.or(sb, sp), AL.or_left(sb, sp, bodies_has(Receive.stored.bodies(cst), fset, docs, content, d, rl))),
      rr => AL.or_cases({Bool.or(sr, Bool.or(sb, sp)) == True{} : Bool}, Rev.member(c, d), Rev.member(Nil{}, d),
        GL.append_mem(c, Nil{}, d, rr),
        cl => AL.or_right(sr, Bool.or(sb, sp), AL.or_right(sb, sp, pays_has(Receive.stored.payloads(cst), fset, pays, d, cl))),
        cr => Empty.absurd({Bool.or(sr, Bool.or(sb, sp)) == True{} : Bool}, Comp.false_true(cr)))))

# What either side forgets is what a forgetting document of this store,
# or of the copy, stands in for.
def forgot_or(+p: Export.Plan, +here: List<&2, Prune.Body>, +cst: Prune.Stored, +marks: List<&2, Bm.Bookmark>, +d: String, h: {Rev.member(Export.onto.forgotten(Export.onto.of(p, here, cst, marks)), d) == True{} : Bool}) -> {Bool.or(Receive.forgot.by(here, d), Receive.forgot.by(Receive.stored.bodies(cst), d)) == True{} : Bool}:
  ExportL.ex_or(Rev.member(Export.forgets.here(here, Export.plan.docset(p)), d), here, Receive.stored.bodies(cst), Export.plan.docset(p), d, {==},
    Equal.trans(Bool, Bool.or(Rev.member(Export.forgets.here(here, Export.plan.docset(p)), d), Rev.member(Export.forgets.all(Receive.stored.bodies(cst)), d)), Rev.member(List.append(&2, String, Export.forgets.here(here, Export.plan.docset(p)), Export.forgets.all(Receive.stored.bodies(cst))), d), True{}, Equal.sym(Bool, Rev.member(List.append(&2, String, Export.forgets.here(here, Export.plan.docset(p)), Export.forgets.all(Receive.stored.bodies(cst))), d), Bool.or(Rev.member(Export.forgets.here(here, Export.plan.docset(p)), d), Rev.member(Export.forgets.all(Receive.stored.bodies(cst)), d)), ReceiveL.member_app(Export.forgets.here(here, Export.plan.docset(p)), Export.forgets.all(Receive.stored.bodies(cst)), d)),
      ForgetL.held_member(List.append(&2, String, Export.forgets.here(here, Export.plan.docset(p)), Export.forgets.all(Receive.stored.bodies(cst))), Main.sorted_distinct(List.append(&2, String, Export.forgets.here(here, Export.plan.docset(p)), Export.forgets.all(Receive.stored.bodies(cst)))), d, StatusL.ah_distinct(List.append(&2, String, Export.forgets.here(here, Export.plan.docset(p)), Export.forgets.all(Receive.stored.bodies(cst))), List.sort(~String, ~(a => b => String.is_le(a, b)), List.append(&2, String, Export.forgets.here(here, Export.plan.docset(p)), Export.forgets.all(Receive.stored.bodies(cst)))), StatusL.ah_sort(~(a => b => String.is_le(a, b)), List.append(&2, String, Export.forgets.here(here, Export.plan.docset(p)), Export.forgets.all(Receive.stored.bodies(cst))), List.append(&2, String, Export.forgets.here(here, Export.plan.docset(p)), Export.forgets.all(Receive.stored.bodies(cst))), ReceiveL.held_refl(List.append(&2, String, Export.forgets.here(here, Export.plan.docset(p)), Export.forgets.all(Receive.stored.bodies(cst)))))),
        h)))
# What is gone from the set is held in the copy or forgotten by one side.
def gone_or(+p: Export.Plan, +here: List<&2, Prune.Body>, +cst: Prune.Stored, +marks: List<&2, Bm.Bookmark>, +d: String, h: {Arrange.has(Export.onto.gone(Export.onto.of(p, here, cst, marks)), d) == True{} : Bool}) -> {Bool.or(Export.copy.has(cst, d), Bool.or(Receive.forgot.by(here, d), Receive.forgot.by(Receive.stored.bodies(cst), d))) == True{} : Bool}:
  +hl = Export.onto.holds(Export.onto.of(p, here, cst, marks))
  +fl = Export.onto.forgotten(Export.onto.of(p, here, cst, marks))
  +fb = Bool.or(Receive.forgot.by(here, d), Receive.forgot.by(Receive.stored.bodies(cst), d))
  AL.or_cases({Bool.or(Export.copy.has(cst, d), fb) == True{} : Bool}, Rev.member(hl, d), Rev.member(fl, d),
    GL.append_mem(hl, fl, d, Equal.trans(Bool, Rev.member(List.append(&2, String, hl, fl), d), Arrange.has(Set.from_list(List.append(&2, String, hl, fl)), d), True{}, Equal.sym(Bool, Arrange.has(Set.from_list(List.append(&2, String, hl, fl)), d), Rev.member(List.append(&2, String, hl, fl), d), CatchL.has_member(List.append(&2, String, hl, fl), d)), h)),
    l => AL.or_left(Export.copy.has(cst, d), fb, holds_has(cst, Set.from_list(Main.ids(Export.plan.revisions(p))), Set.from_list(Export.onto.forgotten.of(p, here, cst)), Export.plan.docset(p), Set.from_list(List.concat(&2, String, [Export.doc.ids(Export.plan.documents(p)), Export.doc.ids(Export.plan.forgetting(p)), Export.split.digests(Export.plan.payloads(p))])), Set.from_list(Export.split.digests(Export.plan.payloads(p))), d, l)),
    r => AL.or_right(Export.copy.has(cst, d), fb, forgot_or(p, here, cst, marks, d, r)))

def not_false_true(b: Bool, e: {Bool.not(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, SL.true_false(e))

# Every revision of the set is gone or written.
def fulls_step(c: Bool, +f: Main.Full, +rest: List<&2, Main.Full>, +gone: Set(), +d: String, ec: {Bool.not(Arrange.has(gone, Main.id_of(f))) == c : Bool}, h: {Bool.or(String.eq(Main.id_of(f), d), Rev.member(Main.ids(rest), d)) == True{} : Bool}, ih: {Rev.member(Main.ids(rest), d) == True{} : Bool} -> {Bool.or(Arrange.has(gone, d), Rev.member(Main.ids(Export.fresh.fulls(rest, gone)), d)) == True{} : Bool}) -> {Bool.or(Arrange.has(gone, d), Rev.member(Main.ids(Tree.keep(~Main.Full, c, f, Export.fresh.fulls(rest, gone))), d)) == True{} : Bool}:
  match c:
    case True{}:
      +m = Rev.member(Main.ids(Export.fresh.fulls(rest, gone)), d)
      AL.or_cases({Bool.or(Arrange.has(gone, d), Bool.or(String.eq(Main.id_of(f), d), m)) == True{} : Bool}, String.eq(Main.id_of(f), d), Rev.member(Main.ids(rest), d), h,
        l => AL.or_right(Arrange.has(gone, d), Bool.or(String.eq(Main.id_of(f), d), m), AL.or_left(String.eq(Main.id_of(f), d), m, l)),
        r => AL.or_cases({Bool.or(Arrange.has(gone, d), Bool.or(String.eq(Main.id_of(f), d), m)) == True{} : Bool}, Arrange.has(gone, d), m, ih(r),
          a => AL.or_left(Arrange.has(gone, d), Bool.or(String.eq(Main.id_of(f), d), m), a),
          b => AL.or_right(Arrange.has(gone, d), Bool.or(String.eq(Main.id_of(f), d), m), AL.or_right(String.eq(Main.id_of(f), d), m, b))))
    case False{}:
      +hg = not_false_true(Arrange.has(gone, Main.id_of(f)), ec)
      AL.or_cases({Bool.or(Arrange.has(gone, d), Rev.member(Main.ids(Export.fresh.fulls(rest, gone)), d)) == True{} : Bool}, String.eq(Main.id_of(f), d), Rev.member(Main.ids(rest), d), h,
        l => AL.or_left(Arrange.has(gone, d), Rev.member(Main.ids(Export.fresh.fulls(rest, gone)), d), (%SL.eq_true(Main.id_of(f), d, l) : {Arrange.has(gone, _) == True{} : Bool}
          hg)),
        r => ih(r))

def fulls_cover(fs: List<&2, Main.Full>, +gone: Set(), +d: String, h: {Rev.member(Main.ids(fs), d) == True{} : Bool}) -> {Bool.or(Arrange.has(gone, d), Rev.member(Main.ids(Export.fresh.fulls(fs, gone)), d)) == True{} : Bool}:
  match fs:
    case Nil{}:
      Empty.absurd({Bool.or(Arrange.has(gone, d), False{}) == True{} : Bool}, Comp.false_true(h))
    case +f <> +rest:
      fulls_step(Bool.not(Arrange.has(gone, Main.id_of(f))), f, rest, gone, d, {==}, h, x => fulls_cover(rest, gone, d, x))

# Every document of the set is gone or written.
def docs_step(c: Bool, +p: String, +i: String, +n: Nat, +t: String, +rest: List<&2, Store.Doc>, +gone: Set(), +d: String, ec: {Bool.not(Arrange.has(gone, i)) == c : Bool}, h: {Bool.or(String.eq(i, d), Rev.member(Export.doc.ids(rest), d)) == True{} : Bool}, ih: {Rev.member(Export.doc.ids(rest), d) == True{} : Bool} -> {Bool.or(Arrange.has(gone, d), Export.doc.has(Export.fresh.docs(rest, gone), d)) == True{} : Bool}) -> {Bool.or(Arrange.has(gone, d), Export.doc.has(Tree.keep(~Store.Doc, c, Store.Doc{p, i, n, t}, Export.fresh.docs(rest, gone)), d)) == True{} : Bool}:
  match c:
    case True{}:
      +m = Export.doc.has(Export.fresh.docs(rest, gone), d)
      AL.or_cases({Bool.or(Arrange.has(gone, d), Bool.or(String.eq(i, d), m)) == True{} : Bool}, String.eq(i, d), Rev.member(Export.doc.ids(rest), d), h,
        l => AL.or_right(Arrange.has(gone, d), Bool.or(String.eq(i, d), m), AL.or_left(String.eq(i, d), m, l)),
        r => AL.or_cases({Bool.or(Arrange.has(gone, d), Bool.or(String.eq(i, d), m)) == True{} : Bool}, Arrange.has(gone, d), m, ih(r),
          a => AL.or_left(Arrange.has(gone, d), Bool.or(String.eq(i, d), m), a),
          b => AL.or_right(Arrange.has(gone, d), Bool.or(String.eq(i, d), m), AL.or_right(String.eq(i, d), m, b))))
    case False{}:
      +hg = not_false_true(Arrange.has(gone, i), ec)
      AL.or_cases({Bool.or(Arrange.has(gone, d), Export.doc.has(Export.fresh.docs(rest, gone), d)) == True{} : Bool}, String.eq(i, d), Rev.member(Export.doc.ids(rest), d), h,
        l => AL.or_left(Arrange.has(gone, d), Export.doc.has(Export.fresh.docs(rest, gone), d), (%SL.eq_true(i, d, l) : {Arrange.has(gone, _) == True{} : Bool}
          hg)),
        r => ih(r))

def docs_cover(ds: List<&2, Store.Doc>, +gone: Set(), +d: String, h: {Rev.member(Export.doc.ids(ds), d) == True{} : Bool}) -> {Bool.or(Arrange.has(gone, d), Export.doc.has(Export.fresh.docs(ds, gone), d)) == True{} : Bool}:
  match ds:
    case Nil{}:
      Empty.absurd({Bool.or(Arrange.has(gone, d), False{}) == True{} : Bool}, Comp.false_true(h))
    case Store.Doc{+p, +i, +n, +t} <> +rest:
      docs_step(Bool.not(Arrange.has(gone, i)), p, i, n, t, rest, gone, d, {==}, h, x => docs_cover(rest, gone, d, x))

# Every payload of the set is gone or written.
def splits_step(c: Bool, +q: String, +x: String, +rest: List<&2, T.Split>, +gone: Set(), +d: String, ec: {Bool.not(Arrange.has(gone, x)) == c : Bool}, h: {Bool.or(String.eq(x, d), Rev.member(Export.split.digests(rest), d)) == True{} : Bool}, ih: {Rev.member(Export.split.digests(rest), d) == True{} : Bool} -> {Bool.or(Arrange.has(gone, d), Export.split.has(Export.fresh.splits(rest, gone), d)) == True{} : Bool}) -> {Bool.or(Arrange.has(gone, d), Export.split.has(Tree.keep(~T.Split, c, T.Split{q, x}, Export.fresh.splits(rest, gone)), d)) == True{} : Bool}:
  match c:
    case True{}:
      +m = Export.split.has(Export.fresh.splits(rest, gone), d)
      AL.or_cases({Bool.or(Arrange.has(gone, d), Bool.or(String.eq(x, d), m)) == True{} : Bool}, String.eq(x, d), Rev.member(Export.split.digests(rest), d), h,
        l => AL.or_right(Arrange.has(gone, d), Bool.or(String.eq(x, d), m), AL.or_left(String.eq(x, d), m, l)),
        r => AL.or_cases({Bool.or(Arrange.has(gone, d), Bool.or(String.eq(x, d), m)) == True{} : Bool}, Arrange.has(gone, d), m, ih(r),
          a => AL.or_left(Arrange.has(gone, d), Bool.or(String.eq(x, d), m), a),
          b => AL.or_right(Arrange.has(gone, d), Bool.or(String.eq(x, d), m), AL.or_right(String.eq(x, d), m, b))))
    case False{}:
      +hg = not_false_true(Arrange.has(gone, x), ec)
      AL.or_cases({Bool.or(Arrange.has(gone, d), Export.split.has(Export.fresh.splits(rest, gone), d)) == True{} : Bool}, String.eq(x, d), Rev.member(Export.split.digests(rest), d), h,
        l => AL.or_left(Arrange.has(gone, d), Export.split.has(Export.fresh.splits(rest, gone), d), (%SL.eq_true(x, d, l) : {Arrange.has(gone, _) == True{} : Bool}
          hg)),
        r => ih(r))

def splits_cover(ss: List<&2, T.Split>, +gone: Set(), +d: String, h: {Rev.member(Export.split.digests(ss), d) == True{} : Bool}) -> {Bool.or(Arrange.has(gone, d), Export.split.has(Export.fresh.splits(ss, gone), d)) == True{} : Bool}:
  match ss:
    case Nil{}:
      Empty.absurd({Bool.or(Arrange.has(gone, d), False{}) == True{} : Bool}, Comp.false_true(h))
    case T.Split{+q, +x} <> +rest:
      splits_step(Bool.not(Arrange.has(gone, x)), q, x, rest, gone, d, {==}, h, y => splits_cover(rest, gone, d, y))

# Gone, or written.
def final_of(+a: Bool, +wv: Bool, +fv: Bool, +g: Bool, +m: Bool, h: {Bool.or(g, m) == True{} : Bool}, hg: {g == True{} : Bool} -> {Bool.or(a, fv) == True{} : Bool}, hm: {m == True{} : Bool} -> {wv == True{} : Bool}) -> {Bool.or(a, Bool.or(wv, fv)) == True{} : Bool}:
  AL.or_cases({Bool.or(a, Bool.or(wv, fv)) == True{} : Bool}, g, m, h,
    x => AL.or_cases({Bool.or(a, Bool.or(wv, fv)) == True{} : Bool}, a, fv, hg(x),
      y => AL.or_left(a, Bool.or(wv, fv), y),
      z => AL.or_right(a, Bool.or(wv, fv), AL.or_right(wv, fv, z))),
    x => AL.or_right(a, Bool.or(wv, fv), AL.or_left(wv, fv, hm(x))))

# Every revision, document, forgetting document and payload of the set is
# one the copy holds, one the update writes, or one either side forgets.
def whole_set(p: Export.Plan, +here: List<&2, Prune.Body>, +cst: Prune.Stored, +marks: List<&2, Bm.Bookmark>, +d: String, h: {Rev.member(Export.set.named(p), d) == True{} : Bool}) -> {Bool.or(Export.copy.has(cst, d), Bool.or(Export.writes.has(Export.onto.writes(p, Export.onto.of(p, here, cst, marks)), d), Bool.or(Receive.forgot.by(here, d), Receive.forgot.by(Receive.stored.bodies(cst), d)))) == True{} : Bool}:
  match p:
    case Export.Plan{+r, +dd, +y, +f, +paths, +rs, +w, +n, +res}:
      +pl : Export.Plan = Export.Plan{r, dd, y, f, paths, rs, w, n, res}
      +gone = Export.onto.gone(Export.onto.of(pl, here, cst, marks))
      +a = Export.copy.has(cst, d)
      +fb = Bool.or(Receive.forgot.by(here, d), Receive.forgot.by(Receive.stored.bodies(cst), d))
      +m1 = Rev.member(Main.ids(Export.fresh.fulls(r, gone)), d)
      +d1 = Export.doc.has(Export.fresh.docs(dd, gone), d)
      +f1 = Export.doc.has(Export.fresh.docs(f, gone), d)
      +s1 = Export.split.has(Export.fresh.splits(y, gone), d)
      +wv = Bool.or(m1, Bool.or(d1, Bool.or(f1, s1)))
      +rest3 = List.append(&2, String, Export.split.digests(y), Nil{})
      +rest2 = List.append(&2, String, Export.doc.ids(f), rest3)
      +rest1 = List.append(&2, String, Export.doc.ids(dd), rest2)
      AL.or_cases({Bool.or(a, Bool.or(wv, fb)) == True{} : Bool}, Rev.member(Main.ids(r), d), Rev.member(rest1, d), GL.append_mem(Main.ids(r), rest1, d, h),
        x => final_of(a, wv, fb, Arrange.has(gone, d), m1, fulls_cover(r, gone, d, x), g => gone_or(pl, here, cst, marks, d, g), mm => AL.or_left(m1, Bool.or(d1, Bool.or(f1, s1)), mm)),
        x => AL.or_cases({Bool.or(a, Bool.or(wv, fb)) == True{} : Bool}, Rev.member(Export.doc.ids(dd), d), Rev.member(rest2, d), GL.append_mem(Export.doc.ids(dd), rest2, d, x),
          y1 => final_of(a, wv, fb, Arrange.has(gone, d), d1, docs_cover(dd, gone, d, y1), g => gone_or(pl, here, cst, marks, d, g), mm => AL.or_right(m1, Bool.or(d1, Bool.or(f1, s1)), AL.or_left(d1, Bool.or(f1, s1), mm))),
          y2 => AL.or_cases({Bool.or(a, Bool.or(wv, fb)) == True{} : Bool}, Rev.member(Export.doc.ids(f), d), Rev.member(rest3, d), GL.append_mem(Export.doc.ids(f), rest3, d, y2),
            z1 => final_of(a, wv, fb, Arrange.has(gone, d), f1, docs_cover(f, gone, d, z1), g => gone_or(pl, here, cst, marks, d, g), mm => AL.or_right(m1, Bool.or(d1, Bool.or(f1, s1)), AL.or_right(d1, Bool.or(f1, s1), AL.or_left(f1, s1, mm)))),
            z2 => AL.or_cases({Bool.or(a, Bool.or(wv, fb)) == True{} : Bool}, Rev.member(Export.split.digests(y), d), Rev.member(Nil{}, d), GL.append_mem(Export.split.digests(y), Nil{}, d, z2),
              u1 => final_of(a, wv, fb, Arrange.has(gone, d), s1, splits_cover(y, gone, d, u1), g => gone_or(pl, here, cst, marks, d, g), mm => AL.or_right(m1, Bool.or(d1, Bool.or(f1, s1)), AL.or_right(d1, Bool.or(f1, s1), AL.or_right(f1, s1, mm)))),
              u2 => Empty.absurd({Bool.or(a, Bool.or(wv, fb)) == True{} : Bool}, Comp.false_true(u2))))))
