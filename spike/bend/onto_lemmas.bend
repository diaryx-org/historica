# What `export` promises of a copy's store it brings up to date. It writes
# only into a copy related to this store holding nothing this store has
# not heard of; it leaves the copy the whole set, giving up only what the
# set no longer names; it carries the files of `claims/` the copy lacks;
# and it adds no private rule.
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

# The files of `claims/` an update carries
# ----------------------------------------

def labels_named(cs: List<&2, T.Split>, +l: String) -> {Rev.member(Export.split.labels(cs), l) == Export.claim.named(cs, l) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case T.Split{+x, d} <> +rest:
      %Equal.sym(Bool, Rev.member(Export.split.labels(rest), l), Export.claim.named(rest, l), labels_named(rest, l)) : {Bool.or(String.eq(x, l), _) == Bool.or(String.eq(x, l), Export.claim.named(rest, l)) : Bool}
      {==}

def held_named(+cc: List<&2, T.Split>, +l: String) -> {Arrange.has(Set.from_list(Export.split.labels(cc)), l) == Export.claim.named(cc, l) : Bool}:
  Equal.trans(Bool, Arrange.has(Set.from_list(Export.split.labels(cc)), l), Rev.member(Export.split.labels(cc), l), Export.claim.named(cc, l), CatchL.has_member(Export.split.labels(cc), l), labels_named(cc, l))

def step_true(e: Bool, +r: Bool, n: Bool, h: {e == True{} : Bool} -> {n == False{} : Bool}) -> {Bool.or(e, Bool.and(r, Bool.not(n))) == Bool.and(Bool.or(e, r), Bool.not(n)) : Bool}:
  match e:
    case True{}:
      match n:
        case True{}:
          Empty.absurd({True{} == False{} : Bool}, SL.true_false(h({==})))
        case False{}:
          {==}
    case False{}:
      {==}

def step_false(e: Bool, n: Bool, r: Bool, h: {e == True{} : Bool} -> {n == True{} : Bool}) -> {Bool.and(r, Bool.not(n)) == Bool.and(Bool.or(e, r), Bool.not(n)) : Bool}:
  match e:
    case True{}:
      match n:
        case True{}:
          match r:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          Empty.absurd({Bool.and(r, True{}) == True{} : Bool}, Comp.false_true(h({==})))
    case False{}:
      {==}

def cc_is(+cc: List<&2, T.Split>, +x: String, +l: String, +b: Bool, hx: {Arrange.has(Set.from_list(Export.split.labels(cc)), x) == b : Bool}, el: {String.eq(x, l) == True{} : Bool}) -> {Export.claim.named(cc, l) == b : Bool}:
  %SL.eq_true(x, l, el) : {Export.claim.named(cc, _) == b : Bool}
  Equal.trans(Bool, Export.claim.named(cc, x), Arrange.has(Set.from_list(Export.split.labels(cc)), x), b, Equal.sym(Bool, Arrange.has(Set.from_list(Export.split.labels(cc)), x), Export.claim.named(cc, x), held_named(cc, x)), hx)

def fresh_step(c: Bool, +x: String, +d: String, +rest: List<&2, T.Split>, +cc: List<&2, T.Split>, +l: String, ec: {Bool.not(Arrange.has(Set.from_list(Export.split.labels(cc)), x)) == c : Bool}, ih: {Export.claim.named(Export.claims.fresh(rest, Set.from_list(Export.split.labels(cc))), l) == Bool.and(Export.claim.named(rest, l), Bool.not(Export.claim.named(cc, l))) : Bool}) -> {Export.claim.named(Tree.keep(~T.Split, c, T.Split{x, d}, Export.claims.fresh(rest, Set.from_list(Export.split.labels(cc)))), l) == Bool.and(Bool.or(String.eq(x, l), Export.claim.named(rest, l)), Bool.not(Export.claim.named(cc, l))) : Bool}:
  match c:
    case True{}:
      +hx = AL.not_of_true(Arrange.has(Set.from_list(Export.split.labels(cc)), x), ec)
      %Equal.sym(Bool, Export.claim.named(Export.claims.fresh(rest, Set.from_list(Export.split.labels(cc))), l), Bool.and(Export.claim.named(rest, l), Bool.not(Export.claim.named(cc, l))), ih) : {Bool.or(String.eq(x, l), _) == Bool.and(Bool.or(String.eq(x, l), Export.claim.named(rest, l)), Bool.not(Export.claim.named(cc, l))) : Bool}
      step_true(String.eq(x, l), Export.claim.named(rest, l), Export.claim.named(cc, l), el => cc_is(cc, x, l, False{}, hx, el))
    case False{}:
      +hx = not_false_true(Arrange.has(Set.from_list(Export.split.labels(cc)), x), ec)
      %Equal.sym(Bool, Export.claim.named(Export.claims.fresh(rest, Set.from_list(Export.split.labels(cc))), l), Bool.and(Export.claim.named(rest, l), Bool.not(Export.claim.named(cc, l))), ih) : {_ == Bool.and(Bool.or(String.eq(x, l), Export.claim.named(rest, l)), Bool.not(Export.claim.named(cc, l))) : Bool}
      step_false(String.eq(x, l), Export.claim.named(cc, l), Export.claim.named(rest, l), el => cc_is(cc, x, l, True{}, hx, el))

# An update carries a file of `claims/` exactly where the origin has it and
# the copy has none of that name.
def fresh_named(cs: List<&2, T.Split>, +cc: List<&2, T.Split>, +l: String) -> {Export.claim.named(Export.claims.fresh(cs, Set.from_list(Export.split.labels(cc))), l) == Bool.and(Export.claim.named(cs, l), Bool.not(Export.claim.named(cc, l))) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case T.Split{+x, +d} <> +rest:
      fresh_step(Bool.not(Arrange.has(Set.from_list(Export.split.labels(cc)), x)), x, d, rest, cc, l, {==}, fresh_named(rest, cc, l))

# What an update gives up
# -----------------------

def not_has(+xs: List<&2, String>, +k: String, h: {Bool.not(Arrange.has(Set.from_list(xs), k)) == True{} : Bool}) -> {Bool.not(Rev.member(xs, k)) == True{} : Bool}:
  %CatchL.has_member(xs, k) : {Bool.not(_) == True{} : Bool}
  h

def not_or_r(a: Bool, -b: Bool, h: {Bool.not(Bool.or(a, b)) == True{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({Bool.not(b) == True{} : Bool}, Comp.false_true(h))
    case False{}:
      h

def not_or_l(a: Bool, -b: Bool, h: {Bool.not(Bool.or(a, b)) == True{} : Bool}) -> {Bool.not(a) == True{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(h))
    case False{}:
      {==}

# A path kept by one of these filters, at a file whose test `ok` passed.
def gone_step(c: Bool, +p: String, +rest: List<&2, String>, +w: String, +ok: Bool, +later: Bool, ec: {c == True{} : Bool} -> {ok == True{} : Bool}, h: {Rev.member(Tree.keep(~String, c, p, rest), w) == True{} : Bool}, ih: {Rev.member(rest, w) == True{} : Bool} -> {later == True{} : Bool}) -> {Bool.or(Bool.and(String.eq(p, w), ok), later) == True{} : Bool}:
  match c:
    case True{}:
      AL.or_cases({Bool.or(Bool.and(String.eq(p, w), ok), later) == True{} : Bool}, String.eq(p, w), Rev.member(rest, w), h,
        l => AL.or_left(Bool.and(String.eq(p, w), ok), later, ExportL.and_tt(String.eq(p, w), ok, l, ec({==}))),
        r => AL.or_right(Bool.and(String.eq(p, w), ok), later, ih(r)))
    case False{}:
      AL.or_right(Bool.and(String.eq(p, w), ok), later, ih(h))

def revs_gone(ss: List<&2, T.Split>, +names: List<&2, String>, +w: String, h: {Rev.member(Export.revs.gone(ss, Set.from_list(names)), w) == True{} : Bool}) -> {Export.split.gone(ss, w, names) == True{} : Bool}:
  match ss:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(h))
    case T.Split{+p, +d} <> +rest:
      gone_step(Bool.not(Arrange.has(Set.from_list(names), d)), p, Export.revs.gone(rest, Set.from_list(names)), w, Bool.not(Rev.member(names, d)), Export.split.gone(rest, w, names),
        e => not_has(names, d, e), h, x => revs_gone(rest, names, w, x))

def pays_gone(ss: List<&2, T.Split>, +fset: Set(), +names: List<&2, String>, +w: String, h: {Rev.member(Export.pays.gone(ss, fset, Set.from_list(names)), w) == True{} : Bool}) -> {Export.split.gone(ss, w, names) == True{} : Bool}:
  match ss:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(h))
    case T.Split{+p, +d} <> +rest:
      gone_step(Bool.not(Bool.or(Arrange.has(fset, d), Arrange.has(Set.from_list(names), d))), p, Export.pays.gone(rest, fset, Set.from_list(names)), w, Bool.not(Rev.member(names, d)), Export.split.gone(rest, w, names),
        e => not_has(names, d, not_or_r(Arrange.has(fset, d), Arrange.has(Set.from_list(names), d), e)), h, x => pays_gone(rest, fset, names, w, x))

def bodies_gone(bs: List<&2, Prune.Body>, +fset: Set(), +names: List<&2, String>, +content: Set(), +w: String, h: {Rev.member(Export.bodies.gone(bs, fset, Set.from_list(names), content), w) == True{} : Bool}) -> {Export.body.gone(bs, w, names) == True{} : Bool}:
  match bs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(h))
    case Prune.Body{+p, +id, +ok, +f} <> +rest:
      gone_step(Bool.not(Bool.or(Arrange.has(fset, id), Export.body.kept(id, f, Set.from_list(names), content))), p, Export.bodies.gone(rest, fset, Set.from_list(names), content), w, Bool.not(Rev.member(names, id)), Export.body.gone(rest, w, names),
        e => not_has(names, id, not_or_l(Arrange.has(Set.from_list(names), id), Export.stands.in(f, content), not_or_r(Arrange.has(fset, id), Export.body.kept(id, f, Set.from_list(names), content), e))), h, x => bodies_gone(rest, fset, names, content, w, x))

def lines_states(rs: List<&2, Receive.Ruled>, +line: String) -> {Rev.member(Export.rules.lines(rs), line) == Export.rule.states(rs, line) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Receive.Ruled{f, +x, l} <> +rest:
      %Equal.sym(Bool, Rev.member(Export.rules.lines(rest), line), Export.rule.states(rest, line), lines_states(rest, line)) : {Bool.or(String.eq(x, line), _) == Bool.or(String.eq(x, line), Export.rule.states(rest, line)) : Bool}
      {==}

def retired_gone(rs: List<&2, Receive.Ruled>, +shared: List<&2, Receive.Ruled>, +w: String, h: {Rev.member(Export.rules.retired(rs, Set.from_list(Export.rules.lines(shared))), w) == True{} : Bool}) -> {Export.rule.gone(rs, w, shared) == True{} : Bool}:
  match rs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(h))
    case Receive.Ruled{+f, +line, +l} <> +rest:
      gone_step(Bool.not(Arrange.has(Set.from_list(Export.rules.lines(shared)), line)), "skipped/" ++ f, Export.rules.retired(rest, Set.from_list(Export.rules.lines(shared))), w, Bool.not(Export.rule.states(shared, line)), Export.rule.gone(rest, w, shared),
        e => (%lines_states(shared, line) : {Bool.not(_) == True{} : Bool}
          not_has(Export.rules.lines(shared), line, e)), h, x => retired_gone(rest, shared, w, x))

def marks_named(bs: List<&2, Bm.Bookmark>, +n: String) -> {Rev.member(Export.marks.names(bs), n) == Export.mark.named(bs, n) : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Bm.Bookmark{+x, t, pv} <> +rest:
      %Equal.sym(Bool, Rev.member(Export.marks.names(rest), n), Export.mark.named(rest, n), marks_named(rest, n)) : {Bool.or(String.eq(x, n), _) == Bool.or(String.eq(x, n), Export.mark.named(rest, n)) : Bool}
      {==}

def names_step(c: Bool, +n: String, +rest: List<&2, String>, +w: String, +ok: Bool, +later: Bool, ec: {c == True{} : Bool} -> {ok == True{} : Bool}, h: {Rev.member(Export.names.files(Tree.keep(~String, c, n, rest)), w) == True{} : Bool}, ih: {Rev.member(Export.names.files(rest), w) == True{} : Bool} -> {later == True{} : Bool}) -> {Bool.or(Bool.and(String.eq("names/" ++ n ++ ".txt", w), ok), later) == True{} : Bool}:
  match c:
    case True{}:
      AL.or_cases({Bool.or(Bool.and(String.eq("names/" ++ n ++ ".txt", w), ok), later) == True{} : Bool}, String.eq("names/" ++ n ++ ".txt", w), Rev.member(Export.names.files(rest), w), h,
        l => AL.or_left(Bool.and(String.eq("names/" ++ n ++ ".txt", w), ok), later, ExportL.and_tt(String.eq("names/" ++ n ++ ".txt", w), ok, l, ec({==}))),
        r => AL.or_right(Bool.and(String.eq("names/" ++ n ++ ".txt", w), ok), later, ih(r)))
    case False{}:
      AL.or_right(Bool.and(String.eq("names/" ++ n ++ ".txt", w), ok), later, ih(h))

def names_gone(bs: List<&2, Bm.Bookmark>, +kept: List<&2, Bm.Bookmark>, +w: String, h: {Rev.member(Export.names.files(Export.names.retired(bs, Set.from_list(Export.marks.names(kept)))), w) == True{} : Bool}) -> {Export.name.gone(bs, w, kept) == True{} : Bool}:
  match bs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(h))
    case Bm.Bookmark{+n, +t, +pv} <> +rest:
      names_step(Bool.not(Arrange.has(Set.from_list(Export.marks.names(kept)), n)), n, Export.names.retired(rest, Set.from_list(Export.marks.names(kept))), w, Bool.not(Export.mark.named(kept, n)), Export.name.gone(rest, w, kept),
        e => (%marks_named(kept, n) : {Bool.not(_) == True{} : Bool}
          not_has(Export.marks.names(kept), n, e)), h, x => names_gone(rest, kept, w, x))

# Everything an update gives up — the store files it withdraws, the rule
# files and the bookmark files it retires — is something the set no longer
# names.
def given_all(p: Export.Plan, +here: List<&2, Prune.Body>, +cst: Prune.Stored, +marks: List<&2, Bm.Bookmark>, +w: String, h: {Rev.member(Export.onto.all(Export.onto.of(p, here, cst, marks)), w) == True{} : Bool}) -> {Export.given.up(p, cst, marks, w) == True{} : Bool}:
  match p:
    case Export.Plan{+r, +d, +y, +f, +paths, +rs, +wh, +n, +res}:
      +pl : Export.Plan = Export.Plan{r, d, y, f, paths, rs, wh, n, res}
      AL.or_cases({Bool.or(Export.split.gone(Export.stored.revs(cst), w, Main.ids(r)), Bool.or(Export.body.gone(Receive.stored.bodies(cst), w, List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Bool.or(Export.split.gone(Receive.stored.payloads(cst), w, Export.split.digests(y)), Bool.or(Export.rule.gone(Receive.ruled(Receive.stored.rules(cst)), w, rs), Export.name.gone(marks, w, Export.travel.names(n)))))) == True{} : Bool}, Rev.member(List.append(&2, String, Export.revs.gone(Export.stored.revs(cst), Set.from_list(Main.ids(r))), List.append(&2, String, Export.bodies.gone(Receive.stored.bodies(cst), Set.from_list(Export.onto.forgotten.of(pl, here, cst)), Set.from_list(List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Set.from_list(List.concat(&2, String, [Export.doc.ids(d), Export.doc.ids(f), Export.split.digests(y)]))), List.append(&2, String, Export.pays.gone(Receive.stored.payloads(cst), Set.from_list(Export.onto.forgotten.of(pl, here, cst)), Set.from_list(Export.split.digests(y))), Nil{}))), w), Rev.member(List.append(&2, String, Export.rules.retired(Receive.ruled(Receive.stored.rules(cst)), Set.from_list(Export.rules.lines(rs))), List.append(&2, String, Export.names.files(Export.names.retired(marks, Set.from_list(Export.marks.names(Export.travel.names(n))))), Nil{})), w), GL.append_mem(List.append(&2, String, Export.revs.gone(Export.stored.revs(cst), Set.from_list(Main.ids(r))), List.append(&2, String, Export.bodies.gone(Receive.stored.bodies(cst), Set.from_list(Export.onto.forgotten.of(pl, here, cst)), Set.from_list(List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Set.from_list(List.concat(&2, String, [Export.doc.ids(d), Export.doc.ids(f), Export.split.digests(y)]))), List.append(&2, String, Export.pays.gone(Receive.stored.payloads(cst), Set.from_list(Export.onto.forgotten.of(pl, here, cst)), Set.from_list(Export.split.digests(y))), Nil{}))), List.append(&2, String, Export.rules.retired(Receive.ruled(Receive.stored.rules(cst)), Set.from_list(Export.rules.lines(rs))), List.append(&2, String, Export.names.files(Export.names.retired(marks, Set.from_list(Export.marks.names(Export.travel.names(n))))), Nil{})), w, h),
        x => AL.or_cases({Bool.or(Export.split.gone(Export.stored.revs(cst), w, Main.ids(r)), Bool.or(Export.body.gone(Receive.stored.bodies(cst), w, List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Bool.or(Export.split.gone(Receive.stored.payloads(cst), w, Export.split.digests(y)), Bool.or(Export.rule.gone(Receive.ruled(Receive.stored.rules(cst)), w, rs), Export.name.gone(marks, w, Export.travel.names(n)))))) == True{} : Bool}, Rev.member(Export.revs.gone(Export.stored.revs(cst), Set.from_list(Main.ids(r))), w), Rev.member(List.append(&2, String, Export.bodies.gone(Receive.stored.bodies(cst), Set.from_list(Export.onto.forgotten.of(pl, here, cst)), Set.from_list(List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Set.from_list(List.concat(&2, String, [Export.doc.ids(d), Export.doc.ids(f), Export.split.digests(y)]))), List.append(&2, String, Export.pays.gone(Receive.stored.payloads(cst), Set.from_list(Export.onto.forgotten.of(pl, here, cst)), Set.from_list(Export.split.digests(y))), Nil{})), w), GL.append_mem(Export.revs.gone(Export.stored.revs(cst), Set.from_list(Main.ids(r))), List.append(&2, String, Export.bodies.gone(Receive.stored.bodies(cst), Set.from_list(Export.onto.forgotten.of(pl, here, cst)), Set.from_list(List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Set.from_list(List.concat(&2, String, [Export.doc.ids(d), Export.doc.ids(f), Export.split.digests(y)]))), List.append(&2, String, Export.pays.gone(Receive.stored.payloads(cst), Set.from_list(Export.onto.forgotten.of(pl, here, cst)), Set.from_list(Export.split.digests(y))), Nil{})), w, x),
          a => AL.or_left(Export.split.gone(Export.stored.revs(cst), w, Main.ids(r)), Bool.or(Export.body.gone(Receive.stored.bodies(cst), w, List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Bool.or(Export.split.gone(Receive.stored.payloads(cst), w, Export.split.digests(y)), Bool.or(Export.rule.gone(Receive.ruled(Receive.stored.rules(cst)), w, rs), Export.name.gone(marks, w, Export.travel.names(n))))), revs_gone(Export.stored.revs(cst), Main.ids(r), w, a)),
          x2 => AL.or_cases({Bool.or(Export.split.gone(Export.stored.revs(cst), w, Main.ids(r)), Bool.or(Export.body.gone(Receive.stored.bodies(cst), w, List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Bool.or(Export.split.gone(Receive.stored.payloads(cst), w, Export.split.digests(y)), Bool.or(Export.rule.gone(Receive.ruled(Receive.stored.rules(cst)), w, rs), Export.name.gone(marks, w, Export.travel.names(n)))))) == True{} : Bool}, Rev.member(Export.bodies.gone(Receive.stored.bodies(cst), Set.from_list(Export.onto.forgotten.of(pl, here, cst)), Set.from_list(List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Set.from_list(List.concat(&2, String, [Export.doc.ids(d), Export.doc.ids(f), Export.split.digests(y)]))), w), Rev.member(List.append(&2, String, Export.pays.gone(Receive.stored.payloads(cst), Set.from_list(Export.onto.forgotten.of(pl, here, cst)), Set.from_list(Export.split.digests(y))), Nil{}), w), GL.append_mem(Export.bodies.gone(Receive.stored.bodies(cst), Set.from_list(Export.onto.forgotten.of(pl, here, cst)), Set.from_list(List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Set.from_list(List.concat(&2, String, [Export.doc.ids(d), Export.doc.ids(f), Export.split.digests(y)]))), List.append(&2, String, Export.pays.gone(Receive.stored.payloads(cst), Set.from_list(Export.onto.forgotten.of(pl, here, cst)), Set.from_list(Export.split.digests(y))), Nil{}), w, x2),
            b => AL.or_right(Export.split.gone(Export.stored.revs(cst), w, Main.ids(r)), Bool.or(Export.body.gone(Receive.stored.bodies(cst), w, List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Bool.or(Export.split.gone(Receive.stored.payloads(cst), w, Export.split.digests(y)), Bool.or(Export.rule.gone(Receive.ruled(Receive.stored.rules(cst)), w, rs), Export.name.gone(marks, w, Export.travel.names(n))))), AL.or_left(Export.body.gone(Receive.stored.bodies(cst), w, List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Bool.or(Export.split.gone(Receive.stored.payloads(cst), w, Export.split.digests(y)), Bool.or(Export.rule.gone(Receive.ruled(Receive.stored.rules(cst)), w, rs), Export.name.gone(marks, w, Export.travel.names(n)))), bodies_gone(Receive.stored.bodies(cst), Set.from_list(Export.onto.forgotten.of(pl, here, cst)), List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f)), Set.from_list(List.concat(&2, String, [Export.doc.ids(d), Export.doc.ids(f), Export.split.digests(y)])), w, b))),
            x3 => AL.or_cases({Bool.or(Export.split.gone(Export.stored.revs(cst), w, Main.ids(r)), Bool.or(Export.body.gone(Receive.stored.bodies(cst), w, List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Bool.or(Export.split.gone(Receive.stored.payloads(cst), w, Export.split.digests(y)), Bool.or(Export.rule.gone(Receive.ruled(Receive.stored.rules(cst)), w, rs), Export.name.gone(marks, w, Export.travel.names(n)))))) == True{} : Bool}, Rev.member(Export.pays.gone(Receive.stored.payloads(cst), Set.from_list(Export.onto.forgotten.of(pl, here, cst)), Set.from_list(Export.split.digests(y))), w), Rev.member(Nil{}, w), GL.append_mem(Export.pays.gone(Receive.stored.payloads(cst), Set.from_list(Export.onto.forgotten.of(pl, here, cst)), Set.from_list(Export.split.digests(y))), Nil{}, w, x3),
              c => AL.or_right(Export.split.gone(Export.stored.revs(cst), w, Main.ids(r)), Bool.or(Export.body.gone(Receive.stored.bodies(cst), w, List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Bool.or(Export.split.gone(Receive.stored.payloads(cst), w, Export.split.digests(y)), Bool.or(Export.rule.gone(Receive.ruled(Receive.stored.rules(cst)), w, rs), Export.name.gone(marks, w, Export.travel.names(n))))), AL.or_right(Export.body.gone(Receive.stored.bodies(cst), w, List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Bool.or(Export.split.gone(Receive.stored.payloads(cst), w, Export.split.digests(y)), Bool.or(Export.rule.gone(Receive.ruled(Receive.stored.rules(cst)), w, rs), Export.name.gone(marks, w, Export.travel.names(n)))), AL.or_left(Export.split.gone(Receive.stored.payloads(cst), w, Export.split.digests(y)), Bool.or(Export.rule.gone(Receive.ruled(Receive.stored.rules(cst)), w, rs), Export.name.gone(marks, w, Export.travel.names(n))), pays_gone(Receive.stored.payloads(cst), Set.from_list(Export.onto.forgotten.of(pl, here, cst)), Export.split.digests(y), w, c)))),
              z => Empty.absurd({Bool.or(Export.split.gone(Export.stored.revs(cst), w, Main.ids(r)), Bool.or(Export.body.gone(Receive.stored.bodies(cst), w, List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Bool.or(Export.split.gone(Receive.stored.payloads(cst), w, Export.split.digests(y)), Bool.or(Export.rule.gone(Receive.ruled(Receive.stored.rules(cst)), w, rs), Export.name.gone(marks, w, Export.travel.names(n)))))) == True{} : Bool}, Comp.false_true(z))))),
        x => AL.or_cases({Bool.or(Export.split.gone(Export.stored.revs(cst), w, Main.ids(r)), Bool.or(Export.body.gone(Receive.stored.bodies(cst), w, List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Bool.or(Export.split.gone(Receive.stored.payloads(cst), w, Export.split.digests(y)), Bool.or(Export.rule.gone(Receive.ruled(Receive.stored.rules(cst)), w, rs), Export.name.gone(marks, w, Export.travel.names(n)))))) == True{} : Bool}, Rev.member(Export.rules.retired(Receive.ruled(Receive.stored.rules(cst)), Set.from_list(Export.rules.lines(rs))), w), Rev.member(List.append(&2, String, Export.names.files(Export.names.retired(marks, Set.from_list(Export.marks.names(Export.travel.names(n))))), Nil{}), w), GL.append_mem(Export.rules.retired(Receive.ruled(Receive.stored.rules(cst)), Set.from_list(Export.rules.lines(rs))), List.append(&2, String, Export.names.files(Export.names.retired(marks, Set.from_list(Export.marks.names(Export.travel.names(n))))), Nil{}), w, x),
          rr => AL.or_right(Export.split.gone(Export.stored.revs(cst), w, Main.ids(r)), Bool.or(Export.body.gone(Receive.stored.bodies(cst), w, List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Bool.or(Export.split.gone(Receive.stored.payloads(cst), w, Export.split.digests(y)), Bool.or(Export.rule.gone(Receive.ruled(Receive.stored.rules(cst)), w, rs), Export.name.gone(marks, w, Export.travel.names(n))))), AL.or_right(Export.body.gone(Receive.stored.bodies(cst), w, List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Bool.or(Export.split.gone(Receive.stored.payloads(cst), w, Export.split.digests(y)), Bool.or(Export.rule.gone(Receive.ruled(Receive.stored.rules(cst)), w, rs), Export.name.gone(marks, w, Export.travel.names(n)))), AL.or_right(Export.split.gone(Receive.stored.payloads(cst), w, Export.split.digests(y)), Bool.or(Export.rule.gone(Receive.ruled(Receive.stored.rules(cst)), w, rs), Export.name.gone(marks, w, Export.travel.names(n))), AL.or_left(Export.rule.gone(Receive.ruled(Receive.stored.rules(cst)), w, rs), Export.name.gone(marks, w, Export.travel.names(n)), retired_gone(Receive.ruled(Receive.stored.rules(cst)), rs, w, rr))))),
          x2 => AL.or_cases({Bool.or(Export.split.gone(Export.stored.revs(cst), w, Main.ids(r)), Bool.or(Export.body.gone(Receive.stored.bodies(cst), w, List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Bool.or(Export.split.gone(Receive.stored.payloads(cst), w, Export.split.digests(y)), Bool.or(Export.rule.gone(Receive.ruled(Receive.stored.rules(cst)), w, rs), Export.name.gone(marks, w, Export.travel.names(n)))))) == True{} : Bool}, Rev.member(Export.names.files(Export.names.retired(marks, Set.from_list(Export.marks.names(Export.travel.names(n))))), w), Rev.member(Nil{}, w), GL.append_mem(Export.names.files(Export.names.retired(marks, Set.from_list(Export.marks.names(Export.travel.names(n))))), Nil{}, w, x2),
            nn => AL.or_right(Export.split.gone(Export.stored.revs(cst), w, Main.ids(r)), Bool.or(Export.body.gone(Receive.stored.bodies(cst), w, List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Bool.or(Export.split.gone(Receive.stored.payloads(cst), w, Export.split.digests(y)), Bool.or(Export.rule.gone(Receive.ruled(Receive.stored.rules(cst)), w, rs), Export.name.gone(marks, w, Export.travel.names(n))))), AL.or_right(Export.body.gone(Receive.stored.bodies(cst), w, List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Bool.or(Export.split.gone(Receive.stored.payloads(cst), w, Export.split.digests(y)), Bool.or(Export.rule.gone(Receive.ruled(Receive.stored.rules(cst)), w, rs), Export.name.gone(marks, w, Export.travel.names(n)))), AL.or_right(Export.split.gone(Receive.stored.payloads(cst), w, Export.split.digests(y)), Bool.or(Export.rule.gone(Receive.ruled(Receive.stored.rules(cst)), w, rs), Export.name.gone(marks, w, Export.travel.names(n))), AL.or_right(Export.rule.gone(Receive.ruled(Receive.stored.rules(cst)), w, rs), Export.name.gone(marks, w, Export.travel.names(n)), names_gone(marks, Export.travel.names(n), w, nn))))),
            z => Empty.absurd({Bool.or(Export.split.gone(Export.stored.revs(cst), w, Main.ids(r)), Bool.or(Export.body.gone(Receive.stored.bodies(cst), w, List.append(&2, String, Export.doc.ids(d), Export.doc.ids(f))), Bool.or(Export.split.gone(Receive.stored.payloads(cst), w, Export.split.digests(y)), Bool.or(Export.rule.gone(Receive.ruled(Receive.stored.rules(cst)), w, rs), Export.name.gone(marks, w, Export.travel.names(n)))))) == True{} : Bool}, Comp.false_true(z)))))
