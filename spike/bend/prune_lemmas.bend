# What `prune` removes. A revision it lets go of is one a revision of the
# store supersedes and that nothing it keeps stands on — however many
# passes the fixed point takes, and whichever revision went first in each.
# A file of content it removes holds a digest nothing kept still needs.
import Base
import ./prune.bend as Prune
import ./arrange.bend as Arrange
import ./commands.bend as Main
import ./revision.bend as Rev
import ./text.bend as T
import ./tree.bend as Tree
import ./blamed_lemmas.bend as B
import ./name_lemmas.bend as NameL
import ./string_lemmas.bend as S
import ./arrange_lemmas.bend as ArrangeL
import ./graph_lemmas.bend as GL
import ./span_lemmas.bend as SpanL

# Booleans
# --------

def or_false_l(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, S.true_false(e))
    case False{}:
      {==}

def or_false_r(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, S.true_false(e))
    case False{}:
      e

def or_false(a: Bool, -b: Bool, ea: {a == False{} : Bool}, eb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({Bool.or(True{}, b) == False{} : Bool}, S.true_false(ea))
    case False{}:
      eb

def and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(e))

def and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, S.false_true(e))

def not_true(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, S.false_true(e))
    case False{}:
      {==}

def not_false(b: Bool, e: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, S.true_false(e))
    case False{}:
      {==}

def not_false_true(b: Bool, e: {Bool.not(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, S.true_false(e))

# Letting one revision go
# -----------------------

def keep_stood(c: Bool, +k: Main.Full, +r: List<&2, Main.Full>, +id: String, ha: {Rev.member(Main.parents_of(k), id) == False{} : Bool}, hr: {Prune.stood_on(r, id) == False{} : Bool}) -> {Prune.stood_on(Main.keep_full(c, k, r), id) == False{} : Bool}:
  match c:
    case True{}:
      or_false(Rev.member(Main.parents_of(k), id), Prune.stood_on(r, id), ha, hr)
    case False{}:
      hr

# What nothing kept stands on, nothing kept stands on once one more goes.
def stood_without(ks: List<&2, Main.Full>, +x: String, +id: String, +h: {Prune.stood_on(ks, id) == False{} : Bool}) -> {Prune.stood_on(Prune.without(ks, x), id) == False{} : Bool}:
  match ks:
    case Nil{}:
      {==}
    case +k <> +rest:
      keep_stood(Bool.not(String.eq(Main.id_of(k), x)), k, Prune.without(rest, x), id,
        or_false_l(Rev.member(Main.parents_of(k), id), Prune.stood_on(rest, id), h),
        stood_without(rest, x, id, or_false_r(Rev.member(Main.parents_of(k), id), Prune.stood_on(rest, id), h)))

def keep_member(c: Bool, +k: Main.Full, +r: List<&2, Main.Full>, +rest: List<&2, Main.Full>, +x: String, +id: String, ec: {Bool.not(String.eq(Main.id_of(k), x)) == c : Bool}, +hx: {String.eq(x, id) == False{} : Bool}, +h: {Rev.member(Main.ids(Main.keep_full(c, k, r)), id) == False{} : Bool}, ih: {Rev.member(Main.ids(r), id) == False{} : Bool} -> {Rev.member(Main.ids(rest), id) == False{} : Bool}) -> {Rev.member(Main.ids(k <> rest), id) == False{} : Bool}:
  match c:
    case True{}:
      or_false(String.eq(Main.id_of(k), id), Rev.member(Main.ids(rest), id),
        or_false_l(String.eq(Main.id_of(k), id), Rev.member(Main.ids(r), id), h),
        ih(or_false_r(String.eq(Main.id_of(k), id), Rev.member(Main.ids(r), id), h)))
    case False{}:
      %Equal.sym(String, Main.id_of(k), x, S.eq_true(Main.id_of(k), x, not_false_true(String.eq(Main.id_of(k), x), ec))) : {Bool.or(String.eq(_, id), Rev.member(Main.ids(rest), id)) == False{} : Bool}
      or_false(String.eq(x, id), Rev.member(Main.ids(rest), id), hx, ih(h))

# A revision other than the one that went, not kept after, was not kept
# before.
def member_without(ks: List<&2, Main.Full>, +x: String, +id: String, +hx: {String.eq(x, id) == False{} : Bool}, h: {Rev.member(Main.ids(Prune.without(ks, x)), id) == False{} : Bool}) -> {Rev.member(Main.ids(ks), id) == False{} : Bool}:
  match ks:
    case Nil{}:
      {==}
    case +k <> +rest:
      keep_member(Bool.not(String.eq(Main.id_of(k), x)), k, Prune.without(rest, x), rest, x, id, {==}, hx, h, hr => member_without(rest, x, id, hx, hr))

# The invariant
# -------------

# Every revision of the store no longer kept is one nothing kept stands on.
def Inv(fs: List<&2, Main.Full>, kept: List<&2, Main.Full>) -> Type:
  @id: String -> {Rev.member(Main.ids(fs), id) == True{} : Bool} -> {Rev.member(Main.ids(kept), id) == False{} : Bool} -> {Prune.stood_on(kept, id) == False{} : Bool}

def goes_stood(+kept: List<&2, Main.Full>, +f: Main.Full, +e: {Prune.goes(kept, f) == True{} : Bool}) -> {Prune.stood_on(kept, Main.id_of(f)) == False{} : Bool}:
  not_true(Prune.stood_on(kept, Main.id_of(f)), and_l(Bool.not(Prune.stood_on(kept, Main.id_of(f))), Bool.not(Prune.evidence(Prune.supersedes_of(f), Main.ids(kept))),
    and_r(Prune.superseded(kept, Main.id_of(f)), Bool.and(Bool.not(Prune.stood_on(kept, Main.id_of(f))), Bool.not(Prune.evidence(Prune.supersedes_of(f), Main.ids(kept)))), e)))

def which(q: Bool, +fs: List<&2, Main.Full>, +kept: List<&2, Main.Full>, +f: Main.Full, +id: String, +eq: {String.eq(Main.id_of(f), id) == q : Bool}, +e: {Prune.goes(kept, f) == True{} : Bool}, inv: Inv(fs, kept), +hf: {Rev.member(Main.ids(fs), id) == True{} : Bool}, +hk: {Rev.member(Main.ids(Prune.without(kept, Main.id_of(f))), id) == False{} : Bool}) -> {Prune.stood_on(Prune.without(kept, Main.id_of(f)), id) == False{} : Bool}:
  match q:
    case True{}:
      %S.eq_true(Main.id_of(f), id, eq) : {Prune.stood_on(Prune.without(kept, Main.id_of(f)), _) == False{} : Bool}
      stood_without(kept, Main.id_of(f), Main.id_of(f), goes_stood(kept, f, e))
    case False{}:
      stood_without(kept, Main.id_of(f), id, inv(id, hf, member_without(kept, Main.id_of(f), id, eq, hk)))

def step_inv(+fs: List<&2, Main.Full>, g: Bool, +kept: List<&2, Main.Full>, +f: Main.Full, +e: {Prune.goes(kept, f) == g : Bool}, inv: Inv(fs, kept)) -> Inv(fs, Prune.drop.if(g, kept, Main.id_of(f))):
  match g:
    case True{}:
      +id => hf => hk => which(String.eq(Main.id_of(f), id), fs, kept, f, id, {==}, e, inv, hf, hk)
    case False{}:
      inv

def pass_inv(snap: List<&2, Main.Full>, +fs: List<&2, Main.Full>, +kept: List<&2, Main.Full>, inv: Inv(fs, kept)) -> Inv(fs, Prune.pass(snap, kept)):
  match snap:
    case Nil{}:
      inv
    case +f <> rest:
      pass_inv(rest, fs, Prune.drop.if(Prune.goes(kept, f), kept, Main.id_of(f)), step_inv(fs, Prune.goes(kept, f), kept, f, {==}, inv))

def fix_inv(fuel: Nat, +fs: List<&2, Main.Full>, p: Prune.Passed, inv: Inv(fs, Prune.passed.kept(p))) -> Inv(fs, Prune.fix(fuel, p)):
  match fuel:
    case 0n:
      inv
    case 1n+more:
      match p:
        case Prune.Passed{+kept, shrank}:
          match shrank:
            case False{}:
              inv
            case True{}:
              fix_inv(more, fs, Prune.passed(kept, Prune.pass(kept, kept)), pass_inv(kept, fs, kept, inv))

def start(+fs: List<&2, Main.Full>) -> Inv(fs, fs):
  +id => +hf => hk => Empty.absurd({Prune.stood_on(fs, id) == False{} : Bool}, S.true_false(Equal.trans(Bool, True{}, Rev.member(Main.ids(fs), id), False{}, Equal.sym(Bool, Rev.member(Main.ids(fs), id), True{}, hf), hk)))

# Nothing `prune` keeps stands on a revision of the store it does not keep.
def kept_inv(+fs: List<&2, Main.Full>) -> Inv(fs, Prune.kept(fs)):
  fix_inv(List.length(&2, Main.Full, fs), fs, Prune.passed(fs, Prune.pass(fs, fs)), pass_inv(fs, fs, fs, start(fs)))

def stands(+fs: List<&2, Main.Full>, +id: String, hf: {Rev.member(Main.ids(fs), id) == True{} : Bool}, hk: {Rev.member(Main.ids(Prune.kept(fs)), id) == False{} : Bool}) -> {Prune.stood_on(Prune.kept(fs), id) == False{} : Bool}:
  kept_inv(fs)(id, hf, hk)

# Content
# -------

def splits_unneeded(ds: List<&2, T.Split>, +refs: Set()) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case T.Split{p, +id} <> rest:
      Bool.and(Bool.not(Arrange.has(refs, id)), splits_unneeded(rest, refs))

def keep_split(c: Bool, +path: String, +id: String, +rest: List<&2, T.Split>, +refs: Set(), ec: {Bool.not(Arrange.has(refs, id)) == c : Bool}, hr: {splits_unneeded(rest, refs) == True{} : Bool}) -> {splits_unneeded(Tree.keep(~T.Split, c, T.Split{path, id}, rest), refs) == True{} : Bool}:
  match c:
    case True{}:
      B.and_tt(Bool.not(Arrange.has(refs, id)), splits_unneeded(rest, refs), ec, hr)
    case False{}:
      hr

# What `gone.of` keeps is what nothing needs.
def gone_unneeded(ds: List<&2, T.Split>, +refs: Set()) -> {splits_unneeded(Prune.gone.of(ds, refs), refs) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case T.Split{+path, +id} <> +rest:
      keep_split(Bool.not(Arrange.has(refs, id)), path, id, Prune.gone.of(rest, refs), refs, {==}, gone_unneeded(rest, refs))

def keep_id(b: Bool, +id: String, +r: List<&2, String>, +refs: Set(), hi: {Bool.not(Arrange.has(refs, id)) == True{} : Bool}, hr: {Prune.unneeded(r, refs) == True{} : Bool}) -> {Prune.unneeded(Rev.keep(b, id, r), refs) == True{} : Bool}:
  match b:
    case True{}:
      B.and_tt(Bool.not(Arrange.has(refs, id)), Prune.unneeded(r, refs), hi, hr)
    case False{}:
      hr

# Each digest once, of files nothing needs, is a digest nothing needs.
def unique_unneeded(ds: List<&2, T.Split>, +seen: List<&2, String>, +refs: Set(), +h: {splits_unneeded(ds, refs) == True{} : Bool}) -> {Prune.unneeded(Prune.unique.go(ds, seen), refs) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case T.Split{+p, +id} <> +rest:
      keep_id(Bool.not(Rev.member(seen, id)), id, Prune.unique.go(rest, id <> seen), refs,
        and_l(Bool.not(Arrange.has(refs, id)), splits_unneeded(rest, refs), h),
        unique_unneeded(rest, id <> seen, refs, and_r(Bool.not(Arrange.has(refs, id)), splits_unneeded(rest, refs), h)))

def app_unneeded(xs: List<&2, String>, +ys: List<&2, String>, +refs: Set(), +hx: {Prune.unneeded(xs, refs) == True{} : Bool}, hy: {Prune.unneeded(ys, refs) == True{} : Bool}) -> {Prune.unneeded(List.append(&2, String, xs, ys), refs) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +x <> +rest:
      B.and_tt(Bool.not(Arrange.has(refs, x)), Prune.unneeded(List.append(&2, String, rest, ys), refs),
        and_l(Bool.not(Arrange.has(refs, x)), Prune.unneeded(rest, refs), hx),
        app_unneeded(rest, ys, refs, and_r(Bool.not(Arrange.has(refs, x)), Prune.unneeded(rest, refs), hx), hy))

# Every file of content `prune` removes holds a digest nothing it keeps
# needs: named by no revision kept, and no forgetting document for one.
def content(+fs: List<&2, Main.Full>, +revs: List<&2, T.Split>, +bs: List<&2, Prune.Body>, +ps: List<&2, T.Split>) -> {Prune.unneeded(Prune.pruned.content(Prune.plan(fs, revs, bs, ps)), Prune.referenced(Prune.kept(fs), bs)) == True{} : Bool}:
  app_unneeded(Prune.unique(Prune.gone.of(T.map(~Prune.Body, ~T.Split, ~(b => Prune.body.split(b)), bs), Prune.referenced(Prune.kept(fs), bs))), Prune.unique(Prune.gone.of(ps, Prune.referenced(Prune.kept(fs), bs))), Prune.referenced(Prune.kept(fs), bs),
    unique_unneeded(Prune.gone.of(T.map(~Prune.Body, ~T.Split, ~(b => Prune.body.split(b)), bs), Prune.referenced(Prune.kept(fs), bs)), Nil{}, Prune.referenced(Prune.kept(fs), bs), gone_unneeded(T.map(~Prune.Body, ~T.Split, ~(b => Prune.body.split(b)), bs), Prune.referenced(Prune.kept(fs), bs))),
    unique_unneeded(Prune.gone.of(ps, Prune.referenced(Prune.kept(fs), bs)), Nil{}, Prune.referenced(Prune.kept(fs), bs), gone_unneeded(ps, Prune.referenced(Prune.kept(fs), bs))))

# What a revision names, read from its own facts
# ----------------------------------------------

# The digest a fact's value gives, past the file's name and a space.
def cut.names(cut: Maybe<&2, T.Split>, +d: String) -> Bool:
  match cut:
    case None{}:
      False{}
    case Some{T.Split{f, +r}}:
      String.eq(r, d)

# Whether a header says, under one key, that a file holds `d`.
def says(h: Rev.Header, +key: String, +d: String) -> Bool:
  match h:
    case Rev.Header{+k, +v}:
      Bool.and(String.eq(k, key), cut.names(T.split_once(v), d))

def any.says(hs: List<&2, Rev.Header>, +key: String, +d: String) -> Bool:
  match hs:
    case Nil{}:
      False{}
    case +h <> rest:
      Bool.or(says(h, key, d), any.says(rest, key, d))

# Whether a revision names content by `d`: one of its `edit`, `text` or
# `bytes` facts says a file holds it.
def names(f: Main.Full, +d: String) -> Bool:
  match f:
    case Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, +facts, message}:
      Bool.or(any.says(facts, "edit", d), Bool.or(any.says(facts, "text", d), any.says(facts, "bytes", d)))

# Whether one of these revisions names content by `d`.
def named(ks: List<&2, Main.Full>, +d: String) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case +k <> rest:
      Bool.or(names(k, d), named(rest, d))

def body.stands(+id: String, f: Maybe<&2, String>, +ks: List<&2, Main.Full>, +d: String) -> Bool:
  match f:
    case None{}:
      False{}
    case Some{+t}:
      Bool.and(String.eq(id, d), named(ks, t))

# Whether a forgetting document among these, filed under `d`, stands in
# for content one of these revisions names.
def stands_in(bs: List<&2, Prune.Body>, +ks: List<&2, Main.Full>, +d: String) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Prune.Body{p, +id, ok, f} <> rest:
      Bool.or(body.stands(id, f, ks, d), stands_in(rest, ks, d))

def cut_false(+v: String, cut: Maybe<&2, T.Split>, +d: String, +rest: List<&2, Tree.Fact>, h: {Rev.member(Prune.fact_digests(Tree.fact_of(v, cut) <> rest), d) == False{} : Bool}) -> {Bool.or(cut.names(cut, d), Rev.member(Prune.fact_digests(rest), d)) == False{} : Bool}:
  match cut:
    case None{}:
      ArrangeL.or_ff_r(String.eq(SNil{}, d), Rev.member(Prune.fact_digests(rest), d), h)
    case Some{T.Split{+f, +r}}:
      h

def says_step(c: Bool, +k: String, +v: String, +rest: List<&2, Rev.Header>, +key: String, +d: String, h: {Rev.member(Prune.fact_digests(Tree.keep(~Tree.Fact, c, Tree.fact_of(v, T.split_once(v)), Tree.facts_of(rest, key))), d) == False{} : Bool}, ih: {Rev.member(Prune.fact_digests(Tree.facts_of(rest, key)), d) == False{} : Bool} -> {any.says(rest, key, d) == False{} : Bool}) -> {Bool.or(Bool.and(c, cut.names(T.split_once(v), d)), any.says(rest, key, d)) == False{} : Bool}:
  match c:
    case True{}:
      +hc = cut_false(v, T.split_once(v), d, Tree.facts_of(rest, key), h)
      ArrangeL.or_ff(cut.names(T.split_once(v), d), any.says(rest, key, d),
        ArrangeL.or_ff_l(cut.names(T.split_once(v), d), Rev.member(Prune.fact_digests(Tree.facts_of(rest, key)), d), hc),
        ih(ArrangeL.or_ff_r(cut.names(T.split_once(v), d), Rev.member(Prune.fact_digests(Tree.facts_of(rest, key)), d), hc)))
    case False{}:
      ih(h)

# A digest none of a key's facts gives is one no header says under it.
def says_false(hs: List<&2, Rev.Header>, +key: String, +d: String, h: {Rev.member(Prune.fact_digests(Tree.facts_of(hs, key)), d) == False{} : Bool}) -> {any.says(hs, key, d) == False{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Rev.Header{+k, +v} <> +rest:
      says_step(String.eq(k, key), k, v, rest, key, d, h, hr => says_false(rest, key, d, hr))

# A digest a revision's content list lacks is one its facts do not name.
def names_false(f: Main.Full, +d: String, h: {Rev.member(Prune.named_by(f), d) == False{} : Bool}) -> {names(f, d) == False{} : Bool}:
  match f:
    case Main.Full{+id, +change, +parents, +supersedes, +author, +when, +revised_by, +revised, +facts, +message}:
      +e = Prune.fact_digests(Tree.facts_of(facts, "edit"))
      +t = Prune.fact_digests(Tree.facts_of(facts, "text"))
      +b = Prune.fact_digests(Tree.facts_of(facts, "bytes"))
      +h1 = ArrangeL.app_false(e, List.append(&2, String, t, b), d, h)
      +h2 = ArrangeL.app_false(t, b, d, ArrangeL.or_ff_r(Rev.member(e, d), Rev.member(List.append(&2, String, t, b), d), h1))
      ArrangeL.or_ff(any.says(facts, "edit", d), Bool.or(any.says(facts, "text", d), any.says(facts, "bytes", d)),
        says_false(facts, "edit", d, ArrangeL.or_ff_l(Rev.member(e, d), Rev.member(List.append(&2, String, t, b), d), h1)),
        ArrangeL.or_ff(any.says(facts, "text", d), any.says(facts, "bytes", d),
          says_false(facts, "text", d, ArrangeL.or_ff_l(Rev.member(t, d), Rev.member(b, d), h2)),
          says_false(facts, "bytes", d, ArrangeL.or_ff_r(Rev.member(t, d), Rev.member(b, d), h2))))

def named_false(ks: List<&2, Main.Full>, +d: String, h: {Rev.member(Prune.named_all(ks), d) == False{} : Bool}) -> {named(ks, d) == False{} : Bool}:
  match ks:
    case Nil{}:
      {==}
    case +k <> +rest:
      +h1 = ArrangeL.app_false(Prune.named_by(k), Prune.named_all(rest), d, h)
      ArrangeL.or_ff(names(k, d), named(rest, d),
        names_false(k, d, ArrangeL.or_ff_l(Rev.member(Prune.named_by(k), d), Rev.member(Prune.named_all(rest), d), h1)),
        named_false(rest, d, ArrangeL.or_ff_r(Rev.member(Prune.named_by(k), d), Rev.member(Prune.named_all(rest), d), h1)))

def kept_false(c: Bool, +id: String, +t: String, +rest: List<&2, String>, +ks: List<&2, Main.Full>, +d: String, +ec: {Arrange.has(Set.from_list(Prune.named_all(ks)), t) == c : Bool}, h: {Rev.member(Rev.keep(c, id, rest), d) == False{} : Bool}) -> {Bool.and(String.eq(id, d), named(ks, t)) == False{} : Bool}:
  match c:
    case True{}:
      ArrangeL.and_ff_l(String.eq(id, d), named(ks, t), ArrangeL.or_ff_l(String.eq(id, d), Rev.member(rest, d), h))
    case False{}:
      ArrangeL.and_ff_r(String.eq(id, d), named(ks, t), named_false(ks, t, ArrangeL.has_false(Prune.named_all(ks), t, ec)))

def rest_false(c: Bool, +id: String, +rest: List<&2, String>, +d: String, h: {Rev.member(Rev.keep(c, id, rest), d) == False{} : Bool}) -> {Rev.member(rest, d) == False{} : Bool}:
  match c:
    case True{}:
      ArrangeL.or_ff_r(String.eq(id, d), Rev.member(rest, d), h)
    case False{}:
      h

def forgetting_step(f: Maybe<&2, String>, +id: String, +rest: List<&2, Prune.Body>, +ks: List<&2, Main.Full>, +d: String, +h: {Rev.member(Prune.forgetting.of(id, Set.from_list(Prune.named_all(ks)), f, Prune.forgetting(rest, Set.from_list(Prune.named_all(ks)))), d) == False{} : Bool}, ih: {Rev.member(Prune.forgetting(rest, Set.from_list(Prune.named_all(ks))), d) == False{} : Bool} -> {stands_in(rest, ks, d) == False{} : Bool}) -> {Bool.or(body.stands(id, f, ks, d), stands_in(rest, ks, d)) == False{} : Bool}:
  match f:
    case None{}:
      ih(h)
    case Some{+t}:
      +c = Arrange.has(Set.from_list(Prune.named_all(ks)), t)
      ArrangeL.or_ff(Bool.and(String.eq(id, d), named(ks, t)), stands_in(rest, ks, d),
        kept_false(c, id, t, Prune.forgetting(rest, Set.from_list(Prune.named_all(ks))), ks, d, {==}, h),
        ih(rest_false(c, id, Prune.forgetting(rest, Set.from_list(Prune.named_all(ks))), d, h)))

# A digest no forgetting document is kept for is one no forgetting
# document standing in for named content is filed under.
def stands_false(bs: List<&2, Prune.Body>, +ks: List<&2, Main.Full>, +d: String, h: {Rev.member(Prune.forgetting(bs, Set.from_list(Prune.named_all(ks))), d) == False{} : Bool}) -> {stands_in(bs, ks, d) == False{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Prune.Body{+p, +id, +ok, +f} <> +rest:
      forgetting_step(f, id, rest, ks, d, h, hr => stands_false(rest, ks, d, hr))

def unneeded_at.of(c: Bool, +x: String, +rest: List<&2, String>, +refs: Set(), +d: String, +ec: {String.eq(x, d) == c : Bool}, +hu: {Bool.and(Bool.not(Arrange.has(refs, x)), Prune.unneeded(rest, refs)) == True{} : Bool}, hm: {Bool.or(c, Rev.member(rest, d)) == True{} : Bool}, ih: {Prune.unneeded(rest, refs) == True{} : Bool} -> {Rev.member(rest, d) == True{} : Bool} -> {Arrange.has(refs, d) == False{} : Bool}) -> {Arrange.has(refs, d) == False{} : Bool}:
  match c:
    case True{}:
      %S.eq_true(x, d, ec) : {Arrange.has(refs, _) == False{} : Bool}
      ArrangeL.not_tt(Arrange.has(refs, x), ArrangeL.and_tl(Bool.not(Arrange.has(refs, x)), Prune.unneeded(rest, refs), hu))
    case False{}:
      ih(ArrangeL.and_tr(Bool.not(Arrange.has(refs, x)), Prune.unneeded(rest, refs), hu), hm)

# A digest among those nothing needs is one nothing needs.
def unneeded_at(xs: List<&2, String>, +refs: Set(), +d: String, +hu: {Prune.unneeded(xs, refs) == True{} : Bool}, hm: {Rev.member(xs, d) == True{} : Bool}) -> {Arrange.has(refs, d) == False{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Arrange.has(refs, d) == False{} : Bool}, S.false_true(hm))
    case +x <> +rest:
      unneeded_at.of(String.eq(x, d), x, rest, refs, d, {==}, hu, hm, a => b => unneeded_at(rest, refs, d, a, b))

# Every digest of content `prune` removes is one no revision it keeps names
# by its own facts, and no forgetting document standing in for named
# content is filed under.
def removes(+fs: List<&2, Main.Full>, +revs: List<&2, T.Split>, +bs: List<&2, Prune.Body>, +ps: List<&2, T.Split>, +d: String, h: {Rev.member(Prune.pruned.content(Prune.plan(fs, revs, bs, ps)), d) == True{} : Bool}) -> {Bool.or(named(Prune.kept(fs), d), stands_in(bs, Prune.kept(fs), d)) == False{} : Bool}:
  +nm = Prune.named_all(Prune.kept(fs))
  +forgot = Prune.forgetting(bs, Set.from_list(nm))
  +hr = unneeded_at(Prune.pruned.content(Prune.plan(fs, revs, bs, ps)), Prune.referenced(Prune.kept(fs), bs), d, content(fs, revs, bs, ps), h)
  +hl = ArrangeL.app_false(nm, forgot, d, ArrangeL.has_false(List.append(&2, String, nm, forgot), d, hr))
  ArrangeL.or_ff(named(Prune.kept(fs), d), stands_in(bs, Prune.kept(fs), d),
    named_false(Prune.kept(fs), d, ArrangeL.or_ff_l(Rev.member(nm, d), Rev.member(forgot, d), hl)),
    stands_false(bs, Prune.kept(fs), d, ArrangeL.or_ff_r(Rev.member(nm, d), Rev.member(forgot, d), hl)))

# Letting only what is superseded go
# ----------------------------------

# Whether a revision among these says, in its own `supersedes`, that it
# supersedes `id`.
def supersedes_any(fs: List<&2, Main.Full>, +id: String) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Main.Full{i, c, p, +sup, a, w, rb, rv, fa, m} <> rest:
      Bool.or(Rev.member(sup, id), supersedes_any(rest, id))

def superseded_is(fs: List<&2, Main.Full>, +id: String) -> {Prune.superseded(fs, id) == supersedes_any(fs, id) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Main.Full{+i, +c, +p, +sup, +a, +w, +rb, +rv, +fa, +m} <> +rest:
      Equal.cong(Bool, Bool, x => Bool.or(Rev.member(sup, id), x), Prune.superseded(rest, id), supersedes_any(rest, id), superseded_is(rest, id))

def or_tt(a: Bool, -b: Bool, +c: Bool, e: {Bool.or(a, b) == True{} : Bool}, ih: {b == True{} : Bool} -> {c == True{} : Bool}) -> {Bool.or(a, c) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      ih(e)

def or_rt(a: Bool, -c: Bool, e: {c == True{} : Bool}) -> {Bool.or(a, c) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def or_lt(a: Bool, -c: Bool, e: {a == True{} : Bool}) -> {Bool.or(a, c) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Bool.or(False{}, c) == True{} : Bool}, S.false_true(e))

def sup_keep(c: Bool, +k: Main.Full, +r: List<&2, Main.Full>, +rest: List<&2, Main.Full>, +y: String, h: {Prune.superseded(Main.keep_full(c, k, r), y) == True{} : Bool}, ih: {Prune.superseded(r, y) == True{} : Bool} -> {Prune.superseded(rest, y) == True{} : Bool}) -> {Prune.superseded(k <> rest, y) == True{} : Bool}:
  match c:
    case True{}:
      or_tt(Rev.member(Prune.supersedes_of(k), y), Prune.superseded(r, y), Prune.superseded(rest, y), h, ih)
    case False{}:
      or_rt(Rev.member(Prune.supersedes_of(k), y), Prune.superseded(rest, y), ih(h))

# What one fewer revision supersedes, all of them did.
def sup_without(ks: List<&2, Main.Full>, +x: String, +y: String, h: {Prune.superseded(Prune.without(ks, x), y) == True{} : Bool}) -> {Prune.superseded(ks, y) == True{} : Bool}:
  match ks:
    case Nil{}:
      h
    case +k <> +rest:
      sup_keep(Bool.not(String.eq(Main.id_of(k), x)), k, Prune.without(rest, x), rest, y, h, hr => sup_without(rest, x, y, hr))

# The invariant: whatever a revision kept supersedes, and every revision
# of the store no longer kept, a revision of the store supersedes.
def Sup(fs: List<&2, Main.Full>, kept: List<&2, Main.Full>) -> Type:
  @y: String -> {Bool.or(Prune.superseded(kept, y), Bool.and(Rev.member(Main.ids(fs), y), Bool.not(Rev.member(Main.ids(kept), y)))) == True{} : Bool} -> {Prune.superseded(fs, y) == True{} : Bool}

def goes_sup(+kept: List<&2, Main.Full>, +f: Main.Full, +e: {Prune.goes(kept, f) == True{} : Bool}) -> {Prune.superseded(kept, Main.id_of(f)) == True{} : Bool}:
  and_l(Prune.superseded(kept, Main.id_of(f)), Bool.and(Bool.not(Prune.stood_on(kept, Main.id_of(f))), Bool.not(Prune.evidence(Prune.supersedes_of(f), Main.ids(kept)))), e)

def sup_which(q: Bool, +fs: List<&2, Main.Full>, +kept: List<&2, Main.Full>, +f: Main.Full, +y: String, +eq: {String.eq(Main.id_of(f), y) == q : Bool}, +e: {Prune.goes(kept, f) == True{} : Bool}, inv: Sup(fs, kept), +hf: {Rev.member(Main.ids(fs), y) == True{} : Bool}, +hk: {Rev.member(Main.ids(Prune.without(kept, Main.id_of(f))), y) == False{} : Bool}) -> {Prune.superseded(fs, y) == True{} : Bool}:
  match q:
    case True{}:
      %S.eq_true(Main.id_of(f), y, eq) : {Prune.superseded(fs, _) == True{} : Bool}
      inv(Main.id_of(f), or_lt(Prune.superseded(kept, Main.id_of(f)), Bool.and(Rev.member(Main.ids(fs), Main.id_of(f)), Bool.not(Rev.member(Main.ids(kept), Main.id_of(f)))), goes_sup(kept, f, e)))
    case False{}:
      inv(y, or_rt(Prune.superseded(kept, y), Bool.and(Rev.member(Main.ids(fs), y), Bool.not(Rev.member(Main.ids(kept), y))),
        B.and_tt(Rev.member(Main.ids(fs), y), Bool.not(Rev.member(Main.ids(kept), y)), hf, ArrangeL.not_ff(Rev.member(Main.ids(kept), y), member_without(kept, Main.id_of(f), y, eq, hk)))))

def sup_case(a: Bool, +fs: List<&2, Main.Full>, +kept: List<&2, Main.Full>, +f: Main.Full, +y: String, +ea: {Prune.superseded(Prune.without(kept, Main.id_of(f)), y) == a : Bool}, +e: {Prune.goes(kept, f) == True{} : Bool}, inv: Sup(fs, kept), +h: {Bool.or(a, Bool.and(Rev.member(Main.ids(fs), y), Bool.not(Rev.member(Main.ids(Prune.without(kept, Main.id_of(f))), y)))) == True{} : Bool}) -> {Prune.superseded(fs, y) == True{} : Bool}:
  match a:
    case True{}:
      inv(y, or_lt(Prune.superseded(kept, y), Bool.and(Rev.member(Main.ids(fs), y), Bool.not(Rev.member(Main.ids(kept), y))), sup_without(kept, Main.id_of(f), y, ea)))
    case False{}:
      sup_which(String.eq(Main.id_of(f), y), fs, kept, f, y, {==}, e, inv,
        ArrangeL.and_tl(Rev.member(Main.ids(fs), y), Bool.not(Rev.member(Main.ids(Prune.without(kept, Main.id_of(f))), y)), h),
        ArrangeL.not_tt(Rev.member(Main.ids(Prune.without(kept, Main.id_of(f))), y), ArrangeL.and_tr(Rev.member(Main.ids(fs), y), Bool.not(Rev.member(Main.ids(Prune.without(kept, Main.id_of(f))), y)), h)))

def sup_step(+fs: List<&2, Main.Full>, g: Bool, +kept: List<&2, Main.Full>, +f: Main.Full, +e: {Prune.goes(kept, f) == g : Bool}, inv: Sup(fs, kept)) -> Sup(fs, Prune.drop.if(g, kept, Main.id_of(f))):
  match g:
    case True{}:
      +y => h => sup_case(Prune.superseded(Prune.without(kept, Main.id_of(f)), y), fs, kept, f, y, {==}, e, inv, h)
    case False{}:
      inv

def pass_sup(snap: List<&2, Main.Full>, +fs: List<&2, Main.Full>, +kept: List<&2, Main.Full>, inv: Sup(fs, kept)) -> Sup(fs, Prune.pass(snap, kept)):
  match snap:
    case Nil{}:
      inv
    case +f <> rest:
      pass_sup(rest, fs, Prune.drop.if(Prune.goes(kept, f), kept, Main.id_of(f)), sup_step(fs, Prune.goes(kept, f), kept, f, {==}, inv))

def fix_sup(fuel: Nat, +fs: List<&2, Main.Full>, p: Prune.Passed, inv: Sup(fs, Prune.passed.kept(p))) -> Sup(fs, Prune.fix(fuel, p)):
  match fuel:
    case 0n:
      inv
    case 1n+more:
      match p:
        case Prune.Passed{+kept, shrank}:
          match shrank:
            case False{}:
              inv
            case True{}:
              fix_sup(more, fs, Prune.passed(kept, Prune.pass(kept, kept)), pass_sup(kept, fs, kept, inv))

def start_of(a: Bool, +fs: List<&2, Main.Full>, +y: String, +ea: {Prune.superseded(fs, y) == a : Bool}, +h: {Bool.or(a, Bool.and(Rev.member(Main.ids(fs), y), Bool.not(Rev.member(Main.ids(fs), y)))) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      +hm = ArrangeL.and_tl(Rev.member(Main.ids(fs), y), Bool.not(Rev.member(Main.ids(fs), y)), h)
      +hn = ArrangeL.not_tt(Rev.member(Main.ids(fs), y), ArrangeL.and_tr(Rev.member(Main.ids(fs), y), Bool.not(Rev.member(Main.ids(fs), y)), h))
      Empty.absurd({False{} == True{} : Bool}, S.true_false(Equal.trans(Bool, True{}, Rev.member(Main.ids(fs), y), False{}, Equal.sym(Bool, Rev.member(Main.ids(fs), y), True{}, hm), hn)))

def sup_start(+fs: List<&2, Main.Full>) -> Sup(fs, fs):
  +y => h => start_of(Prune.superseded(fs, y), fs, y, {==}, h)

# `prune` lets a revision of the store go only where a revision of the
# store supersedes it.
def superseded_gone(+fs: List<&2, Main.Full>, +id: String, +hf: {Rev.member(Main.ids(fs), id) == True{} : Bool}, +hk: {Rev.member(Main.ids(Prune.kept(fs)), id) == False{} : Bool}) -> {supersedes_any(fs, id) == True{} : Bool}:
  %superseded_is(fs, id) : {_ == True{} : Bool}
  fix_sup(List.length(&2, Main.Full, fs), fs, Prune.passed(fs, Prune.pass(fs, fs)), pass_sup(fs, fs, fs, sup_start(fs)))(id,
    or_rt(Prune.superseded(Prune.kept(fs), id), Bool.and(Rev.member(Main.ids(fs), id), Bool.not(Rev.member(Main.ids(Prune.kept(fs)), id))),
      B.and_tt(Rev.member(Main.ids(fs), id), Bool.not(Rev.member(Main.ids(Prune.kept(fs)), id)), hf, ArrangeL.not_ff(Rev.member(Main.ids(Prune.kept(fs)), id), hk))))

# What a run says
# ---------------

def files_dry(fs: List<&2, String>) -> {Prune.said.files(fs, "would remove") == T.map(~String, ~String, ~(f => "would remove history/" ++ f), fs) : List<&2, String>}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +rest:
      Equal.cong(List<&2, String>, List<&2, String>, l => ("would remove history/" ++ f) <> l, Prune.said.files(rest, "would remove"), T.map(~String, ~String, ~(f => "would remove history/" ++ f), rest), files_dry(rest))

def files_run(fs: List<&2, String>) -> {Prune.said.files(fs, "removed") == T.map(~String, ~String, ~(f => "removed history/" ++ f), fs) : List<&2, String>}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +rest:
      Equal.cong(List<&2, String>, List<&2, String>, l => ("removed history/" ++ f) <> l, Prune.said.files(rest, "removed"), T.map(~String, ~String, ~(f => "removed history/" ++ f), rest), files_run(rest))

def tail(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      t

def strip(n: Nat, s: String) -> String:
  match n:
    case 0n:
      s
    case 1n+k:
      strip(k, tail(s))

def first_char(s: String) -> Char:
  match s:
    case SNil{}:
      ' '
    case SCon{c, t}:
      c

# What follows a prefix is what is left once as many characters as the
# prefix has are taken off.
def strip_pre(pre: String, +z: String) -> {strip(String.length(pre), pre ++ z) == z : String}:
  match pre:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      strip_pre(t, z)

def eq_pre.no(q: Bool, +pre: String, +f: String, +x: String, +eq: {String.eq(pre ++ f, pre ++ x) == q : Bool}, ee: {String.eq(f, x) == False{} : Bool}) -> {q == False{} : Bool}:
  match q:
    case False{}:
      {==}
    case True{}:
      +same = Equal.trans(String, f, strip(String.length(pre), pre ++ f), x, Equal.sym(String, strip(String.length(pre), pre ++ f), f, strip_pre(pre, f)), Equal.trans(String, strip(String.length(pre), pre ++ f), strip(String.length(pre), pre ++ x), x, Equal.cong(String, String, z => strip(String.length(pre), z), pre ++ f, pre ++ x, S.eq_true(pre ++ f, pre ++ x, eq)), strip_pre(pre, x)))
      Empty.absurd({True{} == False{} : Bool}, S.true_false(Equal.trans(Bool, True{}, String.eq(f, x), False{}, Equal.sym(Bool, String.eq(f, x), True{}, (%same : {String.eq(f, _) == True{} : Bool}
        S.eq_refl(f))), ee)))

# Two lines of one prefix are the same line exactly where what follows the
# prefix is the same.
def eq_pre(e: Bool, +pre: String, +f: String, +x: String, ee: {String.eq(f, x) == e : Bool}) -> {String.eq(pre ++ f, pre ++ x) == e : Bool}:
  match e:
    case True{}:
      %Equal.sym(String, f, x, S.eq_true(f, x, ee)) : {String.eq(pre ++ _, pre ++ x) == True{} : Bool}
      S.eq_refl(pre ++ x)
    case False{}:
      eq_pre.no(String.eq(pre ++ f, pre ++ x), pre, f, x, {==}, ee)

# A line of a prefix is among lines of that prefix exactly where what
# follows it is among what follows theirs.
def member_pre(fs: List<&2, String>, +pre: String, +x: String) -> {Rev.member(T.map(~String, ~String, ~(f => pre ++ f), fs), pre ++ x) == Rev.member(fs, x) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +rest:
      %Equal.sym(Bool, String.eq(pre ++ f, pre ++ x), String.eq(f, x), eq_pre(String.eq(f, x), pre, f, x, {==})) : {Bool.or(_, Rev.member(T.map(~String, ~String, ~(f => pre ++ f), rest), pre ++ x)) == Rev.member(f <> rest, x) : Bool}
      Equal.cong(Bool, Bool, z => Bool.or(String.eq(f, x), z), Rev.member(T.map(~String, ~String, ~(f => pre ++ f), rest), pre ++ x), Rev.member(rest, x), member_pre(rest, pre, x))

def NOTHING() -> String:
  "nothing here is prunable: nothing superseded is unreferenced"

def msg_no(q: Bool, +pre: String, +x: String, +eq: {String.eq(NOTHING(), pre ++ x) == q : Bool}, hc: {Char.is_eq('n', first_char(pre ++ x)) == False{} : Bool}) -> {q == False{} : Bool}:
  match q:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, S.true_false(Equal.trans(Bool, True{}, Char.is_eq('n', first_char(pre ++ x)), False{},
        Equal.cong(String, Bool, z => Char.is_eq('n', first_char(z)), NOTHING(), pre ++ x, S.eq_true(NOTHING(), pre ++ x, eq)), hc)))

# What `prune` prints names a file, a line of the prefix each, exactly
# where the file is among those it removes; where it removes none, its
# one line names none.
def listed_pre(fs: List<&2, String>, +pre: String, +x: String, +hc: {Char.is_eq('n', first_char(pre ++ x)) == False{} : Bool}, +verb: String, +hv: {Prune.said.files(fs, verb) == T.map(~String, ~String, ~(f => pre ++ f), fs) : List<&2, String>}) -> {Rev.member(Prune.said.listed(fs, verb), pre ++ x) == Rev.member(fs, x) : Bool}:
  match fs:
    case Nil{}:
      %Equal.sym(Bool, String.eq(NOTHING(), pre ++ x), False{}, msg_no(String.eq(NOTHING(), pre ++ x), pre, x, {==}, hc)) : {Bool.or(_, False{}) == False{} : Bool}
      {==}
    case +f <> +rest:
      %Equal.sym(List<&2, String>, Prune.said.files(f <> rest, verb), T.map(~String, ~String, ~(f => pre ++ f), f <> rest), hv) : {Rev.member(_, pre ++ x) == Rev.member(f <> rest, x) : Bool}
      member_pre(f <> rest, pre, x)

# The dry run names a file exactly where the real run removes it, and the
# real run names it too.
def dry_run(p: Prune.Pruned, +x: String) -> {(Rev.member(Prune.act.says(Prune.act.of(True{}, False{}, p)), "would remove history/" ++ x), Rev.member(Prune.act.says(Prune.act.of(False{}, False{}, p)), "removed history/" ++ x)) == (Rev.member(Prune.act.removes(Prune.act.of(False{}, False{}, p)), x), Rev.member(Prune.act.removes(Prune.act.of(False{}, False{}, p)), x)) : Bool & Bool}:
  match p:
    case Prune.Pruned{+r, +o, +y, +fs}:
      %Equal.sym(Bool, Rev.member(Prune.said.listed(fs, "would remove"), "would remove history/" ++ x), Rev.member(fs, x), listed_pre(fs, "would remove history/", x, {==}, "would remove", files_dry(fs))) : {(_, Rev.member(Prune.said.listed(fs, "removed"), "removed history/" ++ x)) == (Rev.member(fs, x), Rev.member(fs, x)) : Bool & Bool}
      %Equal.sym(Bool, Rev.member(Prune.said.listed(fs, "removed"), "removed history/" ++ x), Rev.member(fs, x), listed_pre(fs, "removed history/", x, {==}, "removed", files_run(fs))) : {(Rev.member(fs, x), _) == (Rev.member(fs, x), Rev.member(fs, x)) : Bool & Bool}
      {==}

# What files may go
# -----------------

# Whether pruning lets a revision go: it is one of the store's (`fs`) and
# not one pruning keeps, a revision of the store says it supersedes it,
# and nothing pruning keeps names it as a parent.
def lets_go(+fs: List<&2, Main.Full>, +id: String) -> Bool:
  Bool.and(Rev.member(Main.ids(fs), id), Bool.and(Bool.not(Rev.member(Main.ids(Prune.kept(fs)), id)), Bool.and(supersedes_any(fs, id), Bool.not(Prune.stood_on(Prune.kept(fs), id)))))

# Whether a revision document among these, at `x`, holds a revision
# pruning lets go.
def rev_goes(revs: List<&2, T.Split>, +fs: List<&2, Main.Full>, +x: String) -> Bool:
  match revs:
    case Nil{}:
      False{}
    case T.Split{+p, +id} <> rest:
      Bool.or(Bool.and(String.eq(p, x), lets_go(fs, id)), rev_goes(rest, fs, x))

# Whether a file of content among these, at `x`, holds a digest no revision
# pruning keeps names by its own facts, and no forgetting document among
# `bs` standing in for content one of them names is filed under.
def content_goes(ds: List<&2, T.Split>, +fs: List<&2, Main.Full>, +bs: List<&2, Prune.Body>, +x: String) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case T.Split{+p, +id} <> rest:
      Bool.or(Bool.and(String.eq(p, x), Bool.not(Bool.or(named(Prune.kept(fs), id), stands_in(bs, Prune.kept(fs), id)))), content_goes(rest, fs, bs, x))

def hit(e: Bool, +a: Bool, -r: Bool, -m: Bool, +x: String, +p: String, ee: {String.eq(p, x) == e : Bool}, ha: {a == True{} : Bool}, h: {Bool.or(e, m) == True{} : Bool}, ih: {m == True{} : Bool} -> {r == True{} : Bool}) -> {Bool.or(Bool.and(e, a), r) == True{} : Bool}:
  match e:
    case True{}:
      or_lt(Bool.and(True{}, a), r, ha)
    case False{}:
      or_rt(Bool.and(False{}, a), r, ih(h))

def dead_goes(+fs: List<&2, Main.Full>, +id: String, h: {Arrange.has(Set.from_list(Rev.without(Main.ids(fs), Main.ids(Prune.kept(fs)))), id) == True{} : Bool}) -> {lets_go(fs, id) == True{} : Bool}:
  +mw = Equal.trans(Bool, Rev.member(Rev.without(Main.ids(fs), Main.ids(Prune.kept(fs))), id), Arrange.has(Set.from_list(Rev.without(Main.ids(fs), Main.ids(Prune.kept(fs)))), id), True{}, Equal.sym(Bool, Arrange.has(Set.from_list(Rev.without(Main.ids(fs), Main.ids(Prune.kept(fs)))), id), Rev.member(Rev.without(Main.ids(fs), Main.ids(Prune.kept(fs))), id), ArrangeL.has_list(Rev.without(Main.ids(fs), Main.ids(Prune.kept(fs))), id)), h)
  +hf = GL.without_sub(Main.ids(fs), Main.ids(Prune.kept(fs)), id, mw)
  +hk = SpanL.without_out(Main.ids(fs), Main.ids(Prune.kept(fs)), id, mw)
  +hs = B.and_tt(supersedes_any(fs, id), Bool.not(Prune.stood_on(Prune.kept(fs), id)), superseded_gone(fs, id, hf, hk), ArrangeL.not_ff(Prune.stood_on(Prune.kept(fs), id), stands(fs, id, hf, hk)))
  B.and_tt(Rev.member(Main.ids(fs), id), Bool.and(Bool.not(Rev.member(Main.ids(Prune.kept(fs)), id)), Bool.and(supersedes_any(fs, id), Bool.not(Prune.stood_on(Prune.kept(fs), id)))), hf,
    B.and_tt(Bool.not(Rev.member(Main.ids(Prune.kept(fs)), id)), Bool.and(supersedes_any(fs, id), Bool.not(Prune.stood_on(Prune.kept(fs), id))), ArrangeL.not_ff(Rev.member(Main.ids(Prune.kept(fs)), id), hk), hs))

def revs_step(c: Bool, +p: String, +id: String, +rest: List<&2, T.Split>, +fs: List<&2, Main.Full>, +x: String, +ec: {Arrange.has(Set.from_list(Rev.without(Main.ids(fs), Main.ids(Prune.kept(fs)))), id) == c : Bool}, h: {Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), Tree.keep(~T.Split, c, T.Split{p, id}, Prune.gone.revs(rest, Set.from_list(Rev.without(Main.ids(fs), Main.ids(Prune.kept(fs))))))), x) == True{} : Bool}, ih: {Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), Prune.gone.revs(rest, Set.from_list(Rev.without(Main.ids(fs), Main.ids(Prune.kept(fs)))))), x) == True{} : Bool} -> {rev_goes(rest, fs, x) == True{} : Bool}) -> {Bool.or(Bool.and(String.eq(p, x), lets_go(fs, id)), rev_goes(rest, fs, x)) == True{} : Bool}:
  match c:
    case True{}:
      hit(String.eq(p, x), lets_go(fs, id), rev_goes(rest, fs, x), Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), Prune.gone.revs(rest, Set.from_list(Rev.without(Main.ids(fs), Main.ids(Prune.kept(fs)))))), x), x, p, {==}, dead_goes(fs, id, ec), h, ih)
    case False{}:
      or_rt(Bool.and(String.eq(p, x), lets_go(fs, id)), rev_goes(rest, fs, x), ih(h))

# Every revision document `prune` removes holds a revision it lets go.
def revs_go(ds: List<&2, T.Split>, +fs: List<&2, Main.Full>, +x: String, h: {Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), Prune.gone.revs(ds, Set.from_list(Rev.without(Main.ids(fs), Main.ids(Prune.kept(fs)))))), x) == True{} : Bool}) -> {rev_goes(ds, fs, x) == True{} : Bool}:
  match ds:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(h))
    case T.Split{+p, +id} <> +rest:
      revs_step(Arrange.has(Set.from_list(Rev.without(Main.ids(fs), Main.ids(Prune.kept(fs)))), id), p, id, rest, fs, x, {==}, h, hr => revs_go(rest, fs, x, hr))

# A digest what is kept does not need is one no revision kept names and no
# forgetting document standing in for named content is filed under.
def unneeded_spec(+fs: List<&2, Main.Full>, +bs: List<&2, Prune.Body>, +d: String, h: {Arrange.has(Prune.referenced(Prune.kept(fs), bs), d) == False{} : Bool}) -> {Bool.or(named(Prune.kept(fs), d), stands_in(bs, Prune.kept(fs), d)) == False{} : Bool}:
  +nm = Prune.named_all(Prune.kept(fs))
  +forgot = Prune.forgetting(bs, Set.from_list(nm))
  +hl = ArrangeL.app_false(nm, forgot, d, ArrangeL.has_false(List.append(&2, String, nm, forgot), d, h))
  ArrangeL.or_ff(named(Prune.kept(fs), d), stands_in(bs, Prune.kept(fs), d),
    named_false(Prune.kept(fs), d, ArrangeL.or_ff_l(Rev.member(nm, d), Rev.member(forgot, d), hl)),
    stands_false(bs, Prune.kept(fs), d, ArrangeL.or_ff_r(Rev.member(nm, d), Rev.member(forgot, d), hl)))

def content_step(c: Bool, +p: String, +id: String, +rest: List<&2, T.Split>, +fs: List<&2, Main.Full>, +bs: List<&2, Prune.Body>, +x: String, +ec: {Bool.not(Arrange.has(Prune.referenced(Prune.kept(fs), bs), id)) == c : Bool}, h: {Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), Tree.keep(~T.Split, c, T.Split{p, id}, Prune.gone.of(rest, Prune.referenced(Prune.kept(fs), bs)))), x) == True{} : Bool}, ih: {Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), Prune.gone.of(rest, Prune.referenced(Prune.kept(fs), bs))), x) == True{} : Bool} -> {content_goes(rest, fs, bs, x) == True{} : Bool}) -> {Bool.or(Bool.and(String.eq(p, x), Bool.not(Bool.or(named(Prune.kept(fs), id), stands_in(bs, Prune.kept(fs), id)))), content_goes(rest, fs, bs, x)) == True{} : Bool}:
  match c:
    case True{}:
      hit(String.eq(p, x), Bool.not(Bool.or(named(Prune.kept(fs), id), stands_in(bs, Prune.kept(fs), id))), content_goes(rest, fs, bs, x), Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), Prune.gone.of(rest, Prune.referenced(Prune.kept(fs), bs))), x), x, p, {==},
        ArrangeL.not_ff(Bool.or(named(Prune.kept(fs), id), stands_in(bs, Prune.kept(fs), id)), unneeded_spec(fs, bs, id, ArrangeL.not_tt(Arrange.has(Prune.referenced(Prune.kept(fs), bs), id), ec))), h, ih)
    case False{}:
      or_rt(Bool.and(String.eq(p, x), Bool.not(Bool.or(named(Prune.kept(fs), id), stands_in(bs, Prune.kept(fs), id)))), content_goes(rest, fs, bs, x), ih(h))

# Every file of content `prune` removes holds a digest nothing kept needs.
def content_go(ds: List<&2, T.Split>, +fs: List<&2, Main.Full>, +bs: List<&2, Prune.Body>, +x: String, h: {Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), Prune.gone.of(ds, Prune.referenced(Prune.kept(fs), bs))), x) == True{} : Bool}) -> {content_goes(ds, fs, bs, x) == True{} : Bool}:
  match ds:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(h))
    case T.Split{+p, +id} <> +rest:
      content_step(Bool.not(Arrange.has(Prune.referenced(Prune.kept(fs), bs), id)), p, id, rest, fs, bs, x, {==}, h, hr => content_go(rest, fs, bs, x, hr))

def paths_app(xs: List<&2, T.Split>, +ys: List<&2, T.Split>) -> {T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), List.append(&2, T.Split, xs, ys)) == List.append(&2, String, T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), xs), T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), ys)) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case +q <> +rest:
      Equal.cong(List<&2, String>, List<&2, String>, l => Prune.split.path(q) <> l, T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), List.append(&2, T.Split, rest, ys)), List.append(&2, String, T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), rest), T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), ys)), paths_app(rest, ys))

def member_paths(+xs: List<&2, T.Split>, +ys: List<&2, T.Split>, +x: String) -> {Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), List.append(&2, T.Split, xs, ys)), x) == Bool.or(Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), xs), x), Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), ys), x)) : Bool}:
  %Equal.sym(List<&2, String>, T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), List.append(&2, T.Split, xs, ys)), List.append(&2, String, T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), xs), T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), ys)), paths_app(xs, ys)) : {Rev.member(_, x) == Bool.or(Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), xs), x), Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), ys), x)) : Bool}
  ArrangeL.member_app(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), xs), T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), ys), x)

def or3(a: Bool, b: Bool, -c: Bool, +A: Bool, +B2: Bool, -C: Bool, h: {Bool.or(a, Bool.or(b, c)) == True{} : Bool}, ha: {a == True{} : Bool} -> {A == True{} : Bool}, hb: {b == True{} : Bool} -> {B2 == True{} : Bool}, hc: {c == True{} : Bool} -> {C == True{} : Bool}) -> {Bool.or(A, Bool.or(B2, C)) == True{} : Bool}:
  match a:
    case True{}:
      or_lt(A, Bool.or(B2, C), ha({==}))
    case False{}:
      match b:
        case True{}:
          or_rt(A, Bool.or(B2, C), or_lt(B2, C, hb({==})))
        case False{}:
          or_rt(A, Bool.or(B2, C), or_rt(B2, C, hc(h)))

# Every file `prune` removes is one that may go: a revision document
# holding a revision it lets go, or a document or payload holding a digest
# nothing it keeps needs.
def may_go(+fs: List<&2, Main.Full>, +revs: List<&2, T.Split>, +bs: List<&2, Prune.Body>, +ps: List<&2, T.Split>, +x: String, h: {Rev.member(Prune.act.removes(Prune.act.of(False{}, False{}, Prune.plan(fs, revs, bs, ps))), x) == True{} : Bool}) -> {Bool.or(rev_goes(revs, fs, x), Bool.or(content_goes(T.map(~Prune.Body, ~T.Split, ~(b => Prune.body.split(b)), bs), fs, bs, x), content_goes(ps, fs, bs, x))) == True{} : Bool}:
  +R = Prune.gone.revs(revs, Set.from_list(Rev.without(Main.ids(fs), Main.ids(Prune.kept(fs)))))
  +O = Prune.gone.of(T.map(~Prune.Body, ~T.Split, ~(b => Prune.body.split(b)), bs), Prune.referenced(Prune.kept(fs), bs))
  +P = Prune.gone.of(ps, Prune.referenced(Prune.kept(fs), bs))
  +h2 = Equal.trans(Bool, Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), List.append(&2, T.Split, O, P)), x), Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), List.append(&2, T.Split, O, P)), x), Bool.or(Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), O), x), Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), P), x)), {==}, member_paths(O, P, x))
  +h1 = Equal.trans(Bool, Bool.or(Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), R), x), Bool.or(Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), O), x), Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), P), x))), Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), List.append(&2, T.Split, R, List.append(&2, T.Split, O, P))), x), True{},
    Equal.sym(Bool, Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), List.append(&2, T.Split, R, List.append(&2, T.Split, O, P))), x), Bool.or(Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), R), x), Bool.or(Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), O), x), Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), P), x))),
      (%h2 : {Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), List.append(&2, T.Split, R, List.append(&2, T.Split, O, P))), x) == Bool.or(Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), R), x), _) : Bool}
        member_paths(R, List.append(&2, T.Split, O, P), x))), h)
  or3(Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), R), x), Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), O), x), Rev.member(T.map(~T.Split, ~String, ~(q => Prune.split.path(q)), P), x), rev_goes(revs, fs, x), content_goes(T.map(~Prune.Body, ~T.Split, ~(b => Prune.body.split(b)), bs), fs, bs, x), content_goes(ps, fs, bs, x), h1,
    ha => revs_go(revs, fs, x, ha), hb => content_go(T.map(~Prune.Body, ~T.Split, ~(b => Prune.body.split(b)), bs), fs, bs, x, hb), hc => content_go(ps, fs, bs, x, hc))
