# What `offer` publishes of what is private. A manifest is what it would be
# if the store held no private bookmark, and what it would be if it held
# no private rule: neither leaves a line, so neither leaves the file name
# the key exists to keep back.
import Base
import ./offer.bend as Offer
import ./receive.bend as Receive
import ./prune.bend as Prune
import ./arrange.bend as Arrange
import ./bookmark.bend as Bm
import ./folder.bend as Folder
import ./text.bend as T
import ./tree.bend as Tree
import ./commands.bend as Main
import ./string_lemmas.bend as S
import ./prune_lemmas.bend as PruneL

# Bookmarks
# ---------

def names_shared(bs: List<&2, Bm.Bookmark>, +ids: List<&2, T.Split>, +prefix: String) -> {Offer.names.offered(bs, ids, prefix) == Offer.names.offered(Offer.shared(bs), ids, prefix) : List<&2, Offer.Offered>}:
  match bs:
    case Nil{}:
      {==}
    case Bm.Bookmark{+n, +t, +p} <> +rest:
      match p:
        case True{}:
          names_shared(rest, ids, prefix)
        case False{}:
          Equal.cong(List<&2, Offer.Offered>, List<&2, Offer.Offered>, x => Offer.offered.found(True{}, Arrange.lookup(ids, "names/" ++ n ++ ".txt"), "names/" ++ n ++ ".txt", "name", prefix, x),
            Offer.names.offered(rest, ids, prefix), Offer.names.offered(Offer.shared(rest), ids, prefix), names_shared(rest, ids, prefix))

# The manifest is the one a store with no private bookmark would have.
def bookmarks(+prefix: String, +s: Prune.Stored, +bs: List<&2, Bm.Bookmark>, +claims: List<&2, T.Split>, +rids: List<&2, T.Split>, +nids: List<&2, T.Split>) -> {Offer.manifest(prefix, s, bs, claims, rids, nids) == Offer.manifest(prefix, s, Offer.shared(bs), claims, rids, nids) : List<&2, String>}:
  Equal.cong(List<&2, Offer.Offered>, List<&2, String>, x => Offer.rendered(Offer.heads.of(s), Offer.manifest.of(Offer.files.of(prefix, s), Offer.rules.offered(Receive.ruled(Offer.rules.of(s)), rids, prefix), Offer.splits.offered(claims, "reserved", prefix), x)),
    Offer.names.offered(bs, nids, prefix), Offer.names.offered(Offer.shared(bs), nids, prefix), names_shared(bs, nids, prefix))

# Rules
# -----

def rule_kept(c: Bool, +path: String, +text: String, +file: String, +line: String, +label: String, +rest: List<&2, T.Split>, +ids: List<&2, T.Split>, +prefix: String, ec: {String.starts_with(line, "private") == c : Bool}, er: {Receive.ruled.of(Receive.skipped_file(path), text, Folder.rule_in(text)) == Some{Receive.Ruled{file, line, label}} : Maybe<&2, Receive.Ruled>}, ih: {Offer.rules.offered(Receive.ruled(rest), ids, prefix) == Offer.rules.offered(Receive.ruled(Offer.shared_files(rest)), ids, prefix) : List<&2, Offer.Offered>}) -> {Offer.offered.found(Bool.not(c), Arrange.lookup(ids, "skipped/" ++ file), "skipped/" ++ file, "rule", prefix, Offer.rules.offered(Receive.ruled(rest), ids, prefix)) == Offer.rules.offered(Receive.ruled(Tree.keep(~T.Split, Bool.not(c), T.Split{path, text}, Offer.shared_files(rest))), ids, prefix) : List<&2, Offer.Offered>}:
  match c:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Maybe<&2, Receive.Ruled>, Receive.ruled.of(Receive.skipped_file(path), text, Folder.rule_in(text)), Some{Receive.Ruled{file, line, label}}, er) : {Offer.offered.found(True{}, Arrange.lookup(ids, "skipped/" ++ file), "skipped/" ++ file, "rule", prefix, Offer.rules.offered(Receive.ruled(rest), ids, prefix)) == Offer.rules.offered(Receive.ruled.push(_, Receive.ruled(Offer.shared_files(rest))), ids, prefix) : List<&2, Offer.Offered>}
      %Equal.sym(Bool, String.starts_with(line, "private"), False{}, ec) : {Offer.offered.found(True{}, Arrange.lookup(ids, "skipped/" ++ file), "skipped/" ++ file, "rule", prefix, Offer.rules.offered(Receive.ruled(rest), ids, prefix)) == Offer.offered.found(Bool.not(_), Arrange.lookup(ids, "skipped/" ++ file), "skipped/" ++ file, "rule", prefix, Offer.rules.offered(Receive.ruled(Offer.shared_files(rest)), ids, prefix)) : List<&2, Offer.Offered>}
      Equal.cong(List<&2, Offer.Offered>, List<&2, Offer.Offered>, x => Offer.offered.found(True{}, Arrange.lookup(ids, "skipped/" ++ file), "skipped/" ++ file, "rule", prefix, x),
        Offer.rules.offered(Receive.ruled(rest), ids, prefix), Offer.rules.offered(Receive.ruled(Offer.shared_files(rest)), ids, prefix), ih)

def rule_step(r: Maybe<&2, Receive.Ruled>, +path: String, +text: String, +rest: List<&2, T.Split>, +ids: List<&2, T.Split>, +prefix: String, er: {Receive.ruled.of(Receive.skipped_file(path), text, Folder.rule_in(text)) == r : Maybe<&2, Receive.Ruled>}, ih: {Offer.rules.offered(Receive.ruled(rest), ids, prefix) == Offer.rules.offered(Receive.ruled(Offer.shared_files(rest)), ids, prefix) : List<&2, Offer.Offered>}) -> {Offer.rules.offered(Receive.ruled.push(r, Receive.ruled(rest)), ids, prefix) == Offer.rules.offered(Receive.ruled(Tree.keep(~T.Split, Bool.not(Offer.rule.private(r)), T.Split{path, text}, Offer.shared_files(rest))), ids, prefix) : List<&2, Offer.Offered>}:
  match r:
    case None{}:
      %Equal.sym(Maybe<&2, Receive.Ruled>, Receive.ruled.of(Receive.skipped_file(path), text, Folder.rule_in(text)), None{}, er) : {Offer.rules.offered(Receive.ruled(rest), ids, prefix) == Offer.rules.offered(Receive.ruled.push(_, Receive.ruled(Offer.shared_files(rest))), ids, prefix) : List<&2, Offer.Offered>}
      ih
    case Some{Receive.Ruled{+file, +line, +label}}:
      rule_kept(String.starts_with(line, "private"), path, text, file, line, label, rest, ids, prefix, {==}, er, ih)

def rules_shared(rs: List<&2, T.Split>, +ids: List<&2, T.Split>, +prefix: String) -> {Offer.rules.offered(Receive.ruled(rs), ids, prefix) == Offer.rules.offered(Receive.ruled(Offer.shared_files(rs)), ids, prefix) : List<&2, Offer.Offered>}:
  match rs:
    case Nil{}:
      {==}
    case T.Split{+path, +text} <> +rest:
      rule_step(Receive.ruled.of(Receive.skipped_file(path), text, Folder.rule_in(text)), path, text, rest, ids, prefix, {==}, rules_shared(rest, ids, prefix))

# The manifest is the one a store with no private rule would have.
def rules(+prefix: String, s: Prune.Stored, +bs: List<&2, Bm.Bookmark>, +claims: List<&2, T.Split>, +rids: List<&2, T.Split>, +nids: List<&2, T.Split>) -> {Offer.manifest(prefix, s, bs, claims, rids, nids) == Offer.manifest(prefix, Offer.shared_rules(s), bs, claims, rids, nids) : List<&2, String>}:
  match s:
    case Prune.Stored{+docs, +revs, +od, +bods, +ps, +names, +rs}:
      Equal.cong(List<&2, Offer.Offered>, List<&2, String>, x => Offer.rendered(Offer.heads.of(Prune.Stored{docs, revs, od, bods, ps, names, rs}), Offer.manifest.of(Offer.files.of(prefix, Prune.Stored{docs, revs, od, bods, ps, names, rs}), x, Offer.splits.offered(claims, "reserved", prefix), Offer.names.offered(bs, nids, prefix))),
        Offer.rules.offered(Receive.ruled(rs), rids, prefix), Offer.rules.offered(Receive.ruled(Offer.shared_files(rs)), rids, prefix), rules_shared(rs, rids, prefix))

# Digests
# -------

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

def some_inj(+a: String, -b: String, e: {Some{a} == Some{b} : Maybe<&2, String>}) -> {a == b : String}:
  Equal.cong(Maybe<&2, String>, String, m => Maybe.default(&2, String, m, a), Some{a}, Some{b}, e)

# What was listed stays listed with one more file in front.
def from_more(os: List<&2, Offer.Offered>, +x: T.Split, +rest: List<&2, T.Split>, +prefix: String, +h: {Offer.offered.from(os, rest, prefix) == True{} : Bool}) -> {Offer.offered.from(os, x <> rest, prefix) == True{} : Bool}:
  match os:
    case Nil{}:
      {==}
    case Offer.Offered{k, +d, f, +p} <> +more:
      match x:
        case T.Split{+l, +dd}:
          and_tt(Offer.listed(T.Split{l, dd} <> rest, prefix, p, d), Offer.offered.from(more, T.Split{l, dd} <> rest, prefix),
            or_r(Bool.and(String.eq(Offer.addressed(prefix, l), p), String.eq(dd, d)), Offer.listed(rest, prefix, p, d), PruneL.and_l(Offer.listed(rest, prefix, p, d), Offer.offered.from(more, rest, prefix), h)),
            from_more(more, T.Split{l, dd}, rest, prefix, PruneL.and_r(Offer.listed(rest, prefix, p, d), Offer.offered.from(more, rest, prefix), h)))

def self_listed(+l: String, +d: String, +rest: List<&2, T.Split>, +prefix: String) -> {Offer.listed(T.Split{l, d} <> rest, prefix, Offer.addressed(prefix, l), d) == True{} : Bool}:
  %Equal.sym(Bool, String.eq(Offer.addressed(prefix, l), Offer.addressed(prefix, l)), True{}, S.eq_refl(Offer.addressed(prefix, l))) : {Bool.or(Bool.and(_, String.eq(d, d)), Offer.listed(rest, prefix, Offer.addressed(prefix, l), d)) == True{} : Bool}
  %Equal.sym(Bool, String.eq(d, d), True{}, S.eq_refl(d)) : {Bool.or(Bool.and(True{}, _), Offer.listed(rest, prefix, Offer.addressed(prefix, l), d)) == True{} : Bool}
  {==}

def splits_from(ss: List<&2, T.Split>, +kind: String, +prefix: String) -> {Offer.offered.from(Offer.splits.offered(ss, kind, prefix), ss, prefix) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case T.Split{+p, +d} <> +rest:
      and_tt(Offer.listed(T.Split{p, d} <> rest, prefix, Offer.addressed(prefix, p), d), Offer.offered.from(Offer.splits.offered(rest, kind, prefix), T.Split{p, d} <> rest, prefix),
        self_listed(p, d, rest, prefix),
        from_more(Offer.splits.offered(rest, kind, prefix), T.Split{p, d}, rest, prefix, splits_from(rest, kind, prefix)))

def bodies_from(bs: List<&2, Prune.Body>, +prefix: String) -> {Offer.offered.from(Offer.bodies.offered(bs, prefix), Offer.body.splits(bs), prefix) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Prune.Body{+p, +d, ok, f} <> +rest:
      and_tt(Offer.listed(T.Split{p, d} <> Offer.body.splits(rest), prefix, Offer.addressed(prefix, p), d), Offer.offered.from(Offer.bodies.offered(rest, prefix), T.Split{p, d} <> Offer.body.splits(rest), prefix),
        self_listed(p, d, Offer.body.splits(rest), prefix),
        from_more(Offer.bodies.offered(rest, prefix), T.Split{p, d}, Offer.body.splits(rest), prefix, bodies_from(rest, prefix)))

def lookup_step(c: Bool, +k: String, +v: String, +rest: List<&2, T.Split>, +label: String, +d: String, +prefix: String, ec: {String.eq(k, label) == c : Bool}, e: {Bool.pick(Maybe<&2, String>, c, Some{v}, Arrange.lookup(rest, label)) == Some{d} : Maybe<&2, String>}, ih: {Arrange.lookup(rest, label) == Some{d} : Maybe<&2, String>} -> {Offer.listed(rest, prefix, Offer.addressed(prefix, label), d) == True{} : Bool}) -> {Offer.listed(T.Split{k, v} <> rest, prefix, Offer.addressed(prefix, label), d) == True{} : Bool}:
  match c:
    case True{}:
      %S.eq_true(k, label, ec) : {Offer.listed(T.Split{k, v} <> rest, prefix, Offer.addressed(prefix, _), d) == True{} : Bool}
      %some_inj(v, d, e) : {Offer.listed(T.Split{k, v} <> rest, prefix, Offer.addressed(prefix, k), _) == True{} : Bool}
      self_listed(k, v, rest, prefix)
    case False{}:
      or_r(Bool.and(String.eq(Offer.addressed(prefix, k), Offer.addressed(prefix, label)), String.eq(v, d)), Offer.listed(rest, prefix, Offer.addressed(prefix, label), d), ih(e))

def m_none(m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some(-x: String, e: {None{} == Some{x} : Maybe<&2, String>}) -> Empty:
  %e : {m_none(_) : Type}
  Unit{}

# A file found by its label is listed at that label, with that digest.
def lookup_listed(ids: List<&2, T.Split>, +label: String, +d: String, +prefix: String, e: {Arrange.lookup(ids, label) == Some{d} : Maybe<&2, String>}) -> {Offer.listed(ids, prefix, Offer.addressed(prefix, label), d) == True{} : Bool}:
  match ids:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, none_some(d, e))
    case T.Split{+k, +v} <> +rest:
      lookup_step(String.eq(k, label), k, v, rest, label, d, prefix, {==}, e, x => lookup_listed(rest, label, d, prefix, x))

def found_from(keep: Bool, found: Maybe<&2, String>, +label: String, +kind: String, +prefix: String, +rest: List<&2, Offer.Offered>, +ids: List<&2, T.Split>, ef: {Arrange.lookup(ids, label) == found : Maybe<&2, String>}, ih: {Offer.offered.from(rest, ids, prefix) == True{} : Bool}) -> {Offer.offered.from(Offer.offered.found(keep, found, label, kind, prefix, rest), ids, prefix) == True{} : Bool}:
  match keep:
    case True{}:
      match found:
        case Some{+d}:
          and_tt(Offer.listed(ids, prefix, Offer.addressed(prefix, label), d), Offer.offered.from(rest, ids, prefix), lookup_listed(ids, label, d, prefix, ef), ih)
        case None{}:
          ih
    case False{}:
      ih

def rules_from(rs: List<&2, Receive.Ruled>, +ids: List<&2, T.Split>, +prefix: String) -> {Offer.offered.from(Offer.rules.offered(rs, ids, prefix), ids, prefix) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Receive.Ruled{+file, +line, l} <> +rest:
      found_from(Bool.not(String.starts_with(line, "private")), Arrange.lookup(ids, "skipped/" ++ file), "skipped/" ++ file, "rule", prefix, Offer.rules.offered(rest, ids, prefix), ids, {==}, rules_from(rest, ids, prefix))

def names_from(bs: List<&2, Bm.Bookmark>, +ids: List<&2, T.Split>, +prefix: String) -> {Offer.offered.from(Offer.names.offered(bs, ids, prefix), ids, prefix) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Bm.Bookmark{+n, t, +p} <> +rest:
      found_from(Bool.not(p), Arrange.lookup(ids, "names/" ++ n ++ ".txt"), "names/" ++ n ++ ".txt", "name", prefix, Offer.names.offered(rest, ids, prefix), ids, {==}, names_from(rest, ids, prefix))

# Every line of a manifest names a file by the digest the store's listing
# gives it.
def digests(+prefix: String, s: Prune.Stored, +marks: List<&2, Bm.Bookmark>, +claims: List<&2, T.Split>, +rids: List<&2, T.Split>, +nids: List<&2, T.Split>) -> {Offer.manifest.from(prefix, s, marks, claims, rids, nids) == True{} : Bool}:
  match s:
    case Prune.Stored{docs, +revs, od, +bs, +ps, names, +rules}:
      and_tt(Offer.offered.from(Offer.splits.offered(ps, "payload", prefix), ps, prefix), Bool.and(Offer.offered.from(Offer.bodies.offered(bs, prefix), Offer.body.splits(bs), prefix), Bool.and(Offer.offered.from(Offer.splits.offered(revs, "revision", prefix), revs, prefix), Bool.and(Offer.offered.from(Offer.rules.offered(Receive.ruled(rules), rids, prefix), rids, prefix), Bool.and(Offer.offered.from(Offer.splits.offered(claims, "reserved", prefix), claims, prefix), Offer.offered.from(Offer.names.offered(marks, nids, prefix), nids, prefix))))),
        splits_from(ps, "payload", prefix),
        and_tt(Offer.offered.from(Offer.bodies.offered(bs, prefix), Offer.body.splits(bs), prefix), Bool.and(Offer.offered.from(Offer.splits.offered(revs, "revision", prefix), revs, prefix), Bool.and(Offer.offered.from(Offer.rules.offered(Receive.ruled(rules), rids, prefix), rids, prefix), Bool.and(Offer.offered.from(Offer.splits.offered(claims, "reserved", prefix), claims, prefix), Offer.offered.from(Offer.names.offered(marks, nids, prefix), nids, prefix)))),
          bodies_from(bs, prefix),
          and_tt(Offer.offered.from(Offer.splits.offered(revs, "revision", prefix), revs, prefix), Bool.and(Offer.offered.from(Offer.rules.offered(Receive.ruled(rules), rids, prefix), rids, prefix), Bool.and(Offer.offered.from(Offer.splits.offered(claims, "reserved", prefix), claims, prefix), Offer.offered.from(Offer.names.offered(marks, nids, prefix), nids, prefix))),
            splits_from(revs, "revision", prefix),
            and_tt(Offer.offered.from(Offer.rules.offered(Receive.ruled(rules), rids, prefix), rids, prefix), Bool.and(Offer.offered.from(Offer.splits.offered(claims, "reserved", prefix), claims, prefix), Offer.offered.from(Offer.names.offered(marks, nids, prefix), nids, prefix)),
              rules_from(Receive.ruled(rules), rids, prefix),
              and_tt(Offer.offered.from(Offer.splits.offered(claims, "reserved", prefix), claims, prefix), Offer.offered.from(Offer.names.offered(marks, nids, prefix), nids, prefix),
                splits_from(claims, "reserved", prefix),
                names_from(marks, nids, prefix))))))
