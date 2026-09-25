# What `fetch` plans against this store, and what it says it took. It
# refuses a copy as unrelated exactly where decision 0052 says it must: no
# join asked, a revision on each side, and no revision the copy lists that
# this store holds or that a revision here names as a parent or as what it
# supersedes. It destroys only what a forgetting document of this store,
# or a line of the manifest, says is forgotten. And asked for `--fields`,
# it names each revision it took, once, in digest order.
import Base
import ./text.bend as T
import ./revision.bend as Rev
import ./tree.bend as Tree
import ./commands.bend as Main
import ./prune.bend as Prune
import ./receive.bend as Receive
import ./offer.bend as Offer
import ./fetch.bend as Fetch
import ./string_lemmas.bend as S
import ./anchor_lemmas.bend as AL
import ./composition_lemmas.bend as Comp
import ./receive_lemmas.bend as ReceiveL
import ./status_lemmas.bend as StatusL
import ./forget_lemmas.bend as ForgetL
import ./rewrite_lemmas.bend as RewriteL

# What the laws say
# -----------------

# The digests of the revisions a manifest lists: its `revision` lines'.
def theirs(os: List<&2, Offer.Offered>) -> List<&2, String>:
  T.map(~Offer.Offered, ~String, ~(o => Fetch.entry.digest(o)), List.filter(~Offer.Offered, ~(o => String.eq(Offer.offered.kind(o), "revision")), os))

# A revision, and every revision it names as a parent or as what it
# supersedes.
def named(+f: Main.Full) -> List<&2, String>:
  Main.id_of(f) <> List.append(&2, String, Main.parents_of(f), Prune.supersedes_of(f))

# Every revision this store holds, and every revision one of them names.
def ours(fs: List<&2, Main.Full>) -> List<&2, String>:
  List.concat(&2, String, T.map(~Main.Full, ~List<&2, String>, ~(f => named(f)), fs))

# Whether a line of the manifest says its file forgets `d`.
def forgot.listed(os: List<&2, Offer.Offered>, +d: String) -> Bool:
  match os:
    case Nil{}:
      False{}
    case Offer.Offered{k, g, f, p} <> rest:
      Bool.or(Receive.stands.for(f, d), forgot.listed(rest, d))

# Lists
# -----

def keep_put(b: Bool, +o: Offer.Offered, -r1: List<&2, Offer.Offered>, -r2: List<&2, Offer.Offered>, e: {r1 == r2 : List<&2, Offer.Offered>}) -> {Tree.keep(~Offer.Offered, b, o, r1) == List.filter.put(Offer.Offered, o, r2, b) : List<&2, Offer.Offered>}:
  match b:
    case True{}:
      Equal.cong(List<&2, Offer.Offered>, List<&2, Offer.Offered>, x => o <> x, r1, r2, e)
    case False{}:
      e

def of_kind_rev(os: List<&2, Offer.Offered>) -> {Fetch.of.kind(os, "revision") == List.filter(~Offer.Offered, ~(o => String.eq(Offer.offered.kind(o), "revision")), os) : List<&2, Offer.Offered>}:
  match os:
    case Nil{}:
      {==}
    case +o <> rest:
      keep_put(String.eq(Offer.offered.kind(o), "revision"), o, Fetch.of.kind(rest, "revision"), List.filter(~Offer.Offered, ~(o => String.eq(Offer.offered.kind(o), "revision")), rest), of_kind_rev(rest))

# What the plan reads as the copy's revisions is the manifest's `revision`
# lines' digests.
def theirs_eq(+os: List<&2, Offer.Offered>) -> {Fetch.digests.of(Fetch.of.kind(os, "revision")) == theirs(os) : List<&2, String>}:
  Equal.cong(List<&2, Offer.Offered>, List<&2, String>, x => Fetch.digests.of(x), Fetch.of.kind(os, "revision"), List.filter(~Offer.Offered, ~(o => String.eq(Offer.offered.kind(o), "revision")), os), of_kind_rev(os))

def mem_head(+x: String, +rest: List<&2, String>) -> {Rev.member(x <> rest, x) == True{} : Bool}:
  %Equal.sym(Bool, String.eq(x, x), True{}, S.eq_refl(x)) : {Bool.or(_, Rev.member(rest, x)) == True{} : Bool}
  {==}

def or_swap(a: Bool, b: Bool, c: Bool, -d: Bool) -> {Bool.or(Bool.or(a, b), Bool.or(c, d)) == Bool.or(Bool.or(a, c), Bool.or(b, d)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      match b:
        case False{}:
          {==}
        case True{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}

# A digest is among ours exactly where it is one of our revisions or a
# revision one of them names.
def ours_member(fs: List<&2, Main.Full>, +x: String) -> {Rev.member(ours(fs), x) == Bool.or(Rev.member(Main.ids(fs), x), Rev.member(Receive.edges(fs), x)) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +rest:
      Equal.trans(Bool,
        Rev.member(List.append(&2, String, Main.id_of(f) <> List.append(&2, String, Main.parents_of(f), Prune.supersedes_of(f)), ours(rest)), x),
        Bool.or(Bool.or(String.eq(Main.id_of(f), x), Rev.member(List.append(&2, String, Main.parents_of(f), Prune.supersedes_of(f)), x)), Bool.or(Rev.member(Main.ids(rest), x), Rev.member(Receive.edges(rest), x))),
        Bool.or(Rev.member(Main.id_of(f) <> Main.ids(rest), x), Rev.member(List.append(&2, String, List.append(&2, String, Main.parents_of(f), Prune.supersedes_of(f)), Receive.edges(rest)), x)),
        Equal.trans(Bool,
          Rev.member(List.append(&2, String, Main.id_of(f) <> List.append(&2, String, Main.parents_of(f), Prune.supersedes_of(f)), ours(rest)), x),
          Bool.or(Bool.or(String.eq(Main.id_of(f), x), Rev.member(List.append(&2, String, Main.parents_of(f), Prune.supersedes_of(f)), x)), Rev.member(ours(rest), x)),
          Bool.or(Bool.or(String.eq(Main.id_of(f), x), Rev.member(List.append(&2, String, Main.parents_of(f), Prune.supersedes_of(f)), x)), Bool.or(Rev.member(Main.ids(rest), x), Rev.member(Receive.edges(rest), x))),
          ReceiveL.member_app(Main.id_of(f) <> List.append(&2, String, Main.parents_of(f), Prune.supersedes_of(f)), ours(rest), x),
          Equal.cong(Bool, Bool, z => Bool.or(Bool.or(String.eq(Main.id_of(f), x), Rev.member(List.append(&2, String, Main.parents_of(f), Prune.supersedes_of(f)), x)), z), Rev.member(ours(rest), x), Bool.or(Rev.member(Main.ids(rest), x), Rev.member(Receive.edges(rest), x)), ours_member(rest, x))),
        Equal.trans(Bool,
          Bool.or(Bool.or(String.eq(Main.id_of(f), x), Rev.member(List.append(&2, String, Main.parents_of(f), Prune.supersedes_of(f)), x)), Bool.or(Rev.member(Main.ids(rest), x), Rev.member(Receive.edges(rest), x))),
          Bool.or(Bool.or(String.eq(Main.id_of(f), x), Rev.member(Main.ids(rest), x)), Bool.or(Rev.member(List.append(&2, String, Main.parents_of(f), Prune.supersedes_of(f)), x), Rev.member(Receive.edges(rest), x))),
          Bool.or(Rev.member(Main.id_of(f) <> Main.ids(rest), x), Rev.member(List.append(&2, String, List.append(&2, String, Main.parents_of(f), Prune.supersedes_of(f)), Receive.edges(rest)), x)),
          or_swap(String.eq(Main.id_of(f), x), Rev.member(List.append(&2, String, Main.parents_of(f), Prune.supersedes_of(f)), x), Rev.member(Main.ids(rest), x), Rev.member(Receive.edges(rest), x)),
          Equal.sym(Bool, Bool.or(Rev.member(Main.id_of(f) <> Main.ids(rest), x), Rev.member(List.append(&2, String, List.append(&2, String, Main.parents_of(f), Prune.supersedes_of(f)), Receive.edges(rest)), x)), Bool.or(Bool.or(String.eq(Main.id_of(f), x), Rev.member(Main.ids(rest), x)), Bool.or(Rev.member(List.append(&2, String, Main.parents_of(f), Prune.supersedes_of(f)), x), Rev.member(Receive.edges(rest), x))),
            Equal.cong(Bool, Bool, z => Bool.or(Bool.or(String.eq(Main.id_of(f), x), Rev.member(Main.ids(rest), x)), z), Rev.member(List.append(&2, String, List.append(&2, String, Main.parents_of(f), Prune.supersedes_of(f)), Receive.edges(rest)), x), Bool.or(Rev.member(List.append(&2, String, Main.parents_of(f), Prune.supersedes_of(f)), x), Rev.member(Receive.edges(rest), x)),
              ReceiveL.member_app(List.append(&2, String, Main.parents_of(f), Prune.supersedes_of(f)), Receive.edges(rest), x)))))

# `any.in`
# --------

def not_both.at(b: Bool, +x0: String, -rest: List<&2, String>, +ys: List<&2, String>, +x: String, eb: {String.eq(x0, x) == b : Bool}, h0: {Rev.member(ys, x0) == False{} : Bool}, ih: {Bool.and(Rev.member(ys, x), Rev.member(rest, x)) == False{} : Bool}) -> {Bool.and(Rev.member(ys, x), Bool.or(b, Rev.member(rest, x))) == False{} : Bool}:
  match b:
    case True{}:
      %S.eq_true(x0, x, eb) : {Bool.and(Rev.member(ys, _), True{}) == False{} : Bool}
      %Equal.sym(Bool, Rev.member(ys, x0), False{}, h0) : {Bool.and(_, True{}) == False{} : Bool}
      {==}
    case False{}:
      ih

# Where no string of `xs` is among `ys`, no string is among both.
def not_both(xs: List<&2, String>, +ys: List<&2, String>, +x: String, +h: {Fetch.any.in(xs, ys) == False{} : Bool}) -> {Bool.and(Rev.member(ys, x), Rev.member(xs, x)) == False{} : Bool}:
  match xs:
    case Nil{}:
      ReceiveL.and_false_r(Rev.member(ys, x))
    case +x0 <> +rest:
      not_both.at(String.eq(x0, x), x0, rest, ys, x, {==}, AL.or_false_l(Rev.member(ys, x0), Fetch.any.in(rest, ys), h), not_both(rest, ys, x, AL.or_false_r(Rev.member(ys, x0), Fetch.any.in(rest, ys), h)))

def any_none.at(b: Bool, +x0: String, +rest: List<&2, String>, +ys: List<&2, String>, eb: {Rev.member(ys, x0) == b : Bool}, h: @x: String -> {Rev.member(ys, x) == True{} : Bool} -> {Rev.member(x0 <> rest, x) == False{} : Bool}, ih: (@x: String -> {Rev.member(ys, x) == True{} : Bool} -> {Rev.member(rest, x) == False{} : Bool}) -> {Fetch.any.in(rest, ys) == False{} : Bool}) -> {Bool.or(b, Fetch.any.in(rest, ys)) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Bool.or(True{}, Fetch.any.in(rest, ys)) == False{} : Bool}, S.true_false(Equal.trans(Bool, True{}, Rev.member(x0 <> rest, x0), False{}, Equal.sym(Bool, Rev.member(x0 <> rest, x0), True{}, mem_head(x0, rest)), h(x0, eb))))
    case False{}:
      ih(+x => m => AL.or_false_r(String.eq(x0, x), Rev.member(rest, x), h(x, m)))

# Where nothing among `ys` is among `xs`, `any.in` finds nothing.
def any_none(xs: List<&2, String>, +ys: List<&2, String>, h: @x: String -> {Rev.member(ys, x) == True{} : Bool} -> {Rev.member(xs, x) == False{} : Bool}) -> {Fetch.any.in(xs, ys) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x0 <> +rest:
      any_none.at(Rev.member(ys, x0), x0, rest, ys, {==}, h, g => any_none(rest, ys, g))

def any_app(a: List<&2, String>, +b: List<&2, String>, +ys: List<&2, String>) -> {Fetch.any.in(List.append(&2, String, a, b), ys) == Bool.or(Fetch.any.in(a, ys), Fetch.any.in(b, ys)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, Fetch.any.in(List.append(&2, String, rest, b), ys), Bool.or(Fetch.any.in(rest, ys), Fetch.any.in(b, ys)), any_app(rest, b, ys)) : {Bool.or(Rev.member(ys, x), _) == Bool.or(Fetch.any.in(x <> rest, ys), Fetch.any.in(b, ys)) : Bool}
      ReceiveL.or_assoc(Rev.member(ys, x), Fetch.any.in(rest, ys), Fetch.any.in(b, ys))

def and_or_false(m: Bool, a: Bool, -b: Bool, h1: {Bool.and(m, a) == False{} : Bool}, h2: {Bool.and(m, b) == False{} : Bool}) -> {Bool.and(m, Bool.or(a, b)) == False{} : Bool}:
  match m:
    case False{}:
      {==}
    case True{}:
      AL.or_false(a, b, h1, h2)

# Relatedness
# -----------

def isdone(r: Result<&2, &2, Main.Refused, Fetch.FPlan>) -> Bool:
  match r:
    case Done{p}:
      True{}
    case Fail{e}:
      False{}

def pick_fail(c: Bool, -x: Fetch.FPlan, -y: Main.Refused, -r: Main.Refused, e: {Bool.pick(Result<&2, &2, Main.Refused, Fetch.FPlan>, c, Done{x}, Fail{y}) == Fail{r} : Result<&2, &2, Main.Refused, Fetch.FPlan>}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, S.true_false(Equal.cong(Result<&2, &2, Main.Refused, Fetch.FPlan>, Bool, z => isdone(z), Done{x}, Fail{r}, e)))
    case False{}:
      {==}

def unshared.go(+fs: List<&2, Main.Full>, +os: List<&2, Offer.Offered>, hn: @x: String -> {Rev.member(theirs(os), x) == True{} : Bool} -> {Rev.member(ours(fs), x) == False{} : Bool}) -> {Fetch.any.in(List.append(&2, String, Main.ids(fs), Receive.edges(fs)), Fetch.digests.of(Fetch.of.kind(os, "revision"))) == False{} : Bool}:
  any_none(List.append(&2, String, Main.ids(fs), Receive.edges(fs)), Fetch.digests.of(Fetch.of.kind(os, "revision")),
    +x => m => Equal.trans(Bool, Rev.member(List.append(&2, String, Main.ids(fs), Receive.edges(fs)), x), Bool.or(Rev.member(Main.ids(fs), x), Rev.member(Receive.edges(fs), x)), False{},
      ReceiveL.member_app(Main.ids(fs), Receive.edges(fs), x),
      Equal.trans(Bool, Bool.or(Rev.member(Main.ids(fs), x), Rev.member(Receive.edges(fs), x)), Rev.member(ours(fs), x), False{},
        Equal.sym(Bool, Rev.member(ours(fs), x), Bool.or(Rev.member(Main.ids(fs), x), Rev.member(Receive.edges(fs), x)), ours_member(fs, x)),
        hn(x, Equal.trans(Bool, Rev.member(theirs(os), x), Rev.member(Fetch.digests.of(Fetch.of.kind(os, "revision")), x), True{},
          Equal.cong(List<&2, String>, Bool, z => Rev.member(z, x), theirs(os), Fetch.digests.of(Fetch.of.kind(os, "revision")), Equal.sym(List<&2, String>, Fetch.digests.of(Fetch.of.kind(os, "revision")), theirs(os), theirs_eq(os))), m)))))

def unrelated.go(+fs: List<&2, Main.Full>, +os: List<&2, Offer.Offered>, hr: {List.is_empty(&2, Main.Full, fs) == False{} : Bool}, +ht: {List.is_empty(&2, String, theirs(os)) == False{} : Bool}, hn: @x: String -> {Rev.member(theirs(os), x) == True{} : Bool} -> {Rev.member(ours(fs), x) == False{} : Bool}) -> {Fetch.related(fs, Fetch.digests.of(Fetch.of.kind(os, "revision"))) == False{} : Bool}:
  AL.or_false(Bool.or(List.is_empty(&2, Main.Full, fs), List.is_empty(&2, String, Fetch.digests.of(Fetch.of.kind(os, "revision")))), Bool.or(Fetch.any.in(Main.ids(fs), Fetch.digests.of(Fetch.of.kind(os, "revision"))), Fetch.any.in(Receive.edges(fs), Fetch.digests.of(Fetch.of.kind(os, "revision")))),
    AL.or_false(List.is_empty(&2, Main.Full, fs), List.is_empty(&2, String, Fetch.digests.of(Fetch.of.kind(os, "revision"))), hr,
      (%Equal.sym(List<&2, String>, Fetch.digests.of(Fetch.of.kind(os, "revision")), theirs(os), theirs_eq(os)) : {List.is_empty(&2, String, _) == False{} : Bool}
        ht)),
    Equal.trans(Bool, Bool.or(Fetch.any.in(Main.ids(fs), Fetch.digests.of(Fetch.of.kind(os, "revision"))), Fetch.any.in(Receive.edges(fs), Fetch.digests.of(Fetch.of.kind(os, "revision")))), Fetch.any.in(List.append(&2, String, Main.ids(fs), Receive.edges(fs)), Fetch.digests.of(Fetch.of.kind(os, "revision"))), False{},
      Equal.sym(Bool, Fetch.any.in(List.append(&2, String, Main.ids(fs), Receive.edges(fs)), Fetch.digests.of(Fetch.of.kind(os, "revision"))), Bool.or(Fetch.any.in(Main.ids(fs), Fetch.digests.of(Fetch.of.kind(os, "revision"))), Fetch.any.in(Receive.edges(fs), Fetch.digests.of(Fetch.of.kind(os, "revision")))), any_app(Main.ids(fs), Receive.edges(fs), Fetch.digests.of(Fetch.of.kind(os, "revision")))),
      unshared.go(fs, os, hn)))

# Where no join is asked, each side holds a revision, and none the copy
# lists is one this store holds or names, the fetch is refused, in the Rust
# tool's words.
def refuses(+h: Fetch.Here, +os: List<&2, Offer.Offered>, hr: {List.is_empty(&2, Main.Full, Fetch.here.revs(h)) == False{} : Bool}, +ht: {List.is_empty(&2, String, theirs(os)) == False{} : Bool}, hn: @x: String -> {Rev.member(theirs(os), x) == True{} : Bool} -> {Rev.member(ours(Fetch.here.revs(h)), x) == False{} : Bool}) -> {Fetch.plan.r(h, os, False{}) == Fail{Main.Refused{1, Fetch.UNRELATED()}} : Result<&2, &2, Main.Refused, Fetch.FPlan>}:
  %Equal.sym(Bool, Fetch.related(Fetch.here.revs(h), Fetch.digests.of(Fetch.of.kind(os, "revision"))), False{}, unrelated.go(Fetch.here.revs(h), os, hr, ht, hn)) : {Bool.pick(Result<&2, &2, Main.Refused, Fetch.FPlan>, _, Done{Fetch.plan.of(h, os)}, Fail{Main.Refused{1, Fetch.UNRELATED()}}) == Fail{Main.Refused{1, Fetch.UNRELATED()}} : Result<&2, &2, Main.Refused, Fetch.FPlan>}
  {==}

def theirs_empty(+os: List<&2, Offer.Offered>, h: {List.is_empty(&2, String, Fetch.digests.of(Fetch.of.kind(os, "revision"))) == False{} : Bool}) -> {List.is_empty(&2, String, theirs(os)) == False{} : Bool}:
  %theirs_eq(os) : {List.is_empty(&2, String, _) == False{} : Bool}
  h

def shared_none(+os: List<&2, Offer.Offered>, +fs: List<&2, Main.Full>, +x: String, +h1: {Fetch.any.in(Main.ids(fs), Fetch.digests.of(Fetch.of.kind(os, "revision"))) == False{} : Bool}, +h2: {Fetch.any.in(Receive.edges(fs), Fetch.digests.of(Fetch.of.kind(os, "revision"))) == False{} : Bool}) -> {Bool.and(Rev.member(theirs(os), x), Rev.member(ours(fs), x)) == False{} : Bool}:
  %theirs_eq(os) : {Bool.and(Rev.member(_, x), Rev.member(ours(fs), x)) == False{} : Bool}
  %Equal.sym(Bool, Rev.member(ours(fs), x), Bool.or(Rev.member(Main.ids(fs), x), Rev.member(Receive.edges(fs), x)), ours_member(fs, x)) : {Bool.and(Rev.member(Fetch.digests.of(Fetch.of.kind(os, "revision")), x), _) == False{} : Bool}
  and_or_false(Rev.member(Fetch.digests.of(Fetch.of.kind(os, "revision")), x), Rev.member(Main.ids(fs), x), Rev.member(Receive.edges(fs), x),
    not_both(Main.ids(fs), Fetch.digests.of(Fetch.of.kind(os, "revision")), x, h1),
    not_both(Receive.edges(fs), Fetch.digests.of(Fetch.of.kind(os, "revision")), x, h2))

def refused.go(+fs: List<&2, Main.Full>, +os: List<&2, Offer.Offered>, +join: Bool, +x: String, hj: {join == False{} : Bool}, +hr: {Fetch.related(fs, Fetch.digests.of(Fetch.of.kind(os, "revision"))) == False{} : Bool}) -> {Bool.and(Bool.not(join), Bool.and(Bool.not(List.is_empty(&2, Main.Full, fs)), Bool.and(Bool.not(List.is_empty(&2, String, theirs(os))), Bool.not(Bool.and(Rev.member(theirs(os), x), Rev.member(ours(fs), x)))))) == True{} : Bool}:
  AL.and_intro(Bool.not(join), Bool.and(Bool.not(List.is_empty(&2, Main.Full, fs)), Bool.and(Bool.not(List.is_empty(&2, String, theirs(os))), Bool.not(Bool.and(Rev.member(theirs(os), x), Rev.member(ours(fs), x))))),
    AL.not_true(join, hj),
    AL.and_intro(Bool.not(List.is_empty(&2, Main.Full, fs)), Bool.and(Bool.not(List.is_empty(&2, String, theirs(os))), Bool.not(Bool.and(Rev.member(theirs(os), x), Rev.member(ours(fs), x)))),
      AL.not_true(List.is_empty(&2, Main.Full, fs), AL.or_false_l(List.is_empty(&2, Main.Full, fs), List.is_empty(&2, String, Fetch.digests.of(Fetch.of.kind(os, "revision"))), AL.or_false_l(Bool.or(List.is_empty(&2, Main.Full, fs), List.is_empty(&2, String, Fetch.digests.of(Fetch.of.kind(os, "revision")))), Bool.or(Fetch.any.in(Main.ids(fs), Fetch.digests.of(Fetch.of.kind(os, "revision"))), Fetch.any.in(Receive.edges(fs), Fetch.digests.of(Fetch.of.kind(os, "revision")))), hr))),
      AL.and_intro(Bool.not(List.is_empty(&2, String, theirs(os))), Bool.not(Bool.and(Rev.member(theirs(os), x), Rev.member(ours(fs), x))),
        AL.not_true(List.is_empty(&2, String, theirs(os)), theirs_empty(os, AL.or_false_r(List.is_empty(&2, Main.Full, fs), List.is_empty(&2, String, Fetch.digests.of(Fetch.of.kind(os, "revision"))), AL.or_false_l(Bool.or(List.is_empty(&2, Main.Full, fs), List.is_empty(&2, String, Fetch.digests.of(Fetch.of.kind(os, "revision")))), Bool.or(Fetch.any.in(Main.ids(fs), Fetch.digests.of(Fetch.of.kind(os, "revision"))), Fetch.any.in(Receive.edges(fs), Fetch.digests.of(Fetch.of.kind(os, "revision")))), hr)))),
        AL.not_true(Bool.and(Rev.member(theirs(os), x), Rev.member(ours(fs), x)), shared_none(os, fs, x,
          AL.or_false_l(Fetch.any.in(Main.ids(fs), Fetch.digests.of(Fetch.of.kind(os, "revision"))), Fetch.any.in(Receive.edges(fs), Fetch.digests.of(Fetch.of.kind(os, "revision"))), AL.or_false_r(Bool.or(List.is_empty(&2, Main.Full, fs), List.is_empty(&2, String, Fetch.digests.of(Fetch.of.kind(os, "revision")))), Bool.or(Fetch.any.in(Main.ids(fs), Fetch.digests.of(Fetch.of.kind(os, "revision"))), Fetch.any.in(Receive.edges(fs), Fetch.digests.of(Fetch.of.kind(os, "revision")))), hr)),
          AL.or_false_r(Fetch.any.in(Main.ids(fs), Fetch.digests.of(Fetch.of.kind(os, "revision"))), Fetch.any.in(Receive.edges(fs), Fetch.digests.of(Fetch.of.kind(os, "revision"))), AL.or_false_r(Bool.or(List.is_empty(&2, Main.Full, fs), List.is_empty(&2, String, Fetch.digests.of(Fetch.of.kind(os, "revision")))), Bool.or(Fetch.any.in(Main.ids(fs), Fetch.digests.of(Fetch.of.kind(os, "revision"))), Fetch.any.in(Receive.edges(fs), Fetch.digests.of(Fetch.of.kind(os, "revision")))), hr)))))))

# A refusal as unrelated is where decision 0052 puts it: no join asked, a
# revision on each side, and none of the copy's that this store holds or
# names.
def refused_only(+h: Fetch.Here, +os: List<&2, Offer.Offered>, +join: Bool, +x: String, -r: Main.Refused, +e: {Fetch.plan.r(h, os, join) == Fail{r} : Result<&2, &2, Main.Refused, Fetch.FPlan>}) -> {Bool.and(Bool.not(join), Bool.and(Bool.not(List.is_empty(&2, Main.Full, Fetch.here.revs(h))), Bool.and(Bool.not(List.is_empty(&2, String, theirs(os))), Bool.not(Bool.and(Rev.member(theirs(os), x), Rev.member(ours(Fetch.here.revs(h)), x)))))) == True{} : Bool}:
  refused.go(Fetch.here.revs(h), os, join, x,
    AL.or_false_l(join, Fetch.related(Fetch.here.revs(h), Fetch.digests.of(Fetch.of.kind(os, "revision"))), pick_fail(Bool.or(join, Fetch.related(Fetch.here.revs(h), Fetch.digests.of(Fetch.of.kind(os, "revision")))), Fetch.plan.of(h, os), Main.Refused{1, Fetch.UNRELATED()}, r, e)),
    AL.or_false_r(join, Fetch.related(Fetch.here.revs(h), Fetch.digests.of(Fetch.of.kind(os, "revision"))), pick_fail(Bool.or(join, Fetch.related(Fetch.here.revs(h), Fetch.digests.of(Fetch.of.kind(os, "revision")))), Fetch.plan.of(h, os), Main.Refused{1, Fetch.UNRELATED()}, r, e)))

# Forgetting
# ----------

def push_member(f: Maybe<&2, String>, +d: String, -rest: List<&2, String>, -r: Bool, ih: {Rev.member(rest, d) == r : Bool}) -> {Rev.member(Receive.forgets.push(f, rest), d) == Bool.or(Receive.stands.for(f, d), r) : Bool}:
  match f:
    case None{}:
      ih
    case Some{t}:
      Equal.cong(Bool, Bool, z => Bool.or(String.eq(t, d), z), Rev.member(rest, d), r, ih)

# A digest is among what the manifest's lines forget exactly where one of
# them says its file forgets it.
def listed_member(os: List<&2, Offer.Offered>, +d: String) -> {Rev.member(Fetch.entry.forgets(os), d) == forgot.listed(os, d) : Bool}:
  match os:
    case Nil{}:
      {==}
    case Offer.Offered{k, g, f, p} <> +rest:
      push_member(f, d, Fetch.entry.forgets(rest), forgot.listed(rest, d), listed_member(rest, d))

def among_held(xs: List<&2, String>, +ys: List<&2, String>, +ids: List<&2, String>, +h: {Main.all_held(ids, xs) == True{} : Bool}) -> {Main.all_held(ids, Fetch.among.list(xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      ReceiveL.keep_held(Rev.member(ys, x), x, Fetch.among.list(rest, ys), ids,
        Comp.and_left(Rev.member(ids, x), Main.all_held(ids, rest), h),
        among_held(rest, ys, ids, Comp.and_right(Rev.member(ids, x), Main.all_held(ids, rest), h)))

# What either side forgets, as the plan reads it: this store's forgetting
# documents, then the manifest's lines.
def forgotten.of(+s: Receive.Side, +os: List<&2, Offer.Offered>) -> List<&2, String>:
  List.append(&2, String, Receive.body.forgets(Receive.stored.bodies(Receive.stored.of(s))), Fetch.entry.forgets(os))

# The digests of this store's documents and payloads.
def held.of(+s: Receive.Side) -> List<&2, String>:
  List.append(&2, String, Receive.body.ids(Receive.stored.bodies(Receive.stored.of(s))), Receive.payload.ids(Receive.stored.payloads(Receive.stored.of(s))))

def destroys_held(+s: Receive.Side, +os: List<&2, Offer.Offered>) -> {Main.all_held(forgotten.of(s, os), Fetch.plan.destroys(Fetch.plan.of(Fetch.here.of(s), os))) == True{} : Bool}:
  StatusL.ah_distinct(forgotten.of(s, os), List.sort(~String, ~(a => b => String.is_le(a, b)), Fetch.among.list(forgotten.of(s, os), held.of(s))),
    StatusL.ah_sort(~(a => b => String.is_le(a, b)), forgotten.of(s, os), Fetch.among.list(forgotten.of(s, os), held.of(s)),
      among_held(forgotten.of(s, os), held.of(s), forgotten.of(s, os), ReceiveL.held_refl(forgotten.of(s, os)))))

# Every original a fetch destroys is one a forgetting document of this
# store stands in for, or one a line of the manifest says its file forgets.
def destroyed(+s: Receive.Side, +os: List<&2, Offer.Offered>, +d: String, h: {Rev.member(Fetch.plan.destroys(Fetch.plan.of(Fetch.here.of(s), os)), d) == True{} : Bool}) -> {Bool.or(Receive.forgot.by(Receive.stored.bodies(Receive.stored.of(s)), d), forgot.listed(os, d)) == True{} : Bool}:
  %ReceiveL.forgets_member(Receive.stored.bodies(Receive.stored.of(s)), d) : {Bool.or(_, forgot.listed(os, d)) == True{} : Bool}
  %listed_member(os, d) : {Bool.or(Rev.member(Receive.body.forgets(Receive.stored.bodies(Receive.stored.of(s))), d), _) == True{} : Bool}
  %ReceiveL.member_app(Receive.body.forgets(Receive.stored.bodies(Receive.stored.of(s))), Fetch.entry.forgets(os), d) : {_ == True{} : Bool}
  ForgetL.held_member(forgotten.of(s, os), Fetch.plan.destroys(Fetch.plan.of(Fetch.here.of(s), os)), d, destroys_held(s, os), h)

# What it says
# ------------

# Asked for `--fields`, what a fetch says names each revision it took,
# once, in digest order, and none it did not take.
def says_what_it_took(+rs: List<&2, String>, +ds: Nat, +ps: Nat, +rus: Nat, +res: Nat, +ns: List<&2, String>, +k: Nat, +dec: List<&2, Fetch.Declined>, +des: Nat, +re: Nat) -> {Main.fields.ok(rs, Fetch.said.done(True{}, Fetch.Tally{rs, ds, ps, rus, res, ns, k, dec, des, re})) == True{} : Bool}:
  RewriteL.abandon_fields(rs, ns)
