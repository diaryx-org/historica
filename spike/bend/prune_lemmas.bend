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
